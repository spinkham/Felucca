/* SPDX-License-Identifier: GPL-3.0-only
 * Copyright (C) 2026 Leo Kuroshita (@kurogedelic), Hügelton Instruments */
/* Felucca update loader, the portable part (step 2 of the M-UPGRADE update
 * protocol).
 *
 * The host serves the package ("logical image") with cmd 0x30 reads (ota.c).
 * The loader:
 *   1. reads the UFW header and finds flash.bin;
 *   2. checks that the package's app area decrypts with THIS chip's key
 *      (taken from isd_config.ini in the device's own flash head), so a
 *      package for another key is refused before anything is erased;
 *   2b. reads the whole flash.bin once and checks it against the CRC16 of its
 *      UFW entry (the vendor tools' check), keeping each app sector's CRC16:
 *      a damaged or truncated package is refused before anything is erased;
 *   3. writes ONLY the app area [0x4000, 0x93000), sector by sector, skipping
 *      sectors that are already equal, and verifies each one; a sector that
 *      comes in different from the checked pass is read again, never written;
 *      the flash head (SPL, isd_config) is never written. The app area head
 *      (the first 32 bytes at 0x4000, which the SPL boots from) is the commit
 *      record: it is erased before the first change and programmed last, only
 *      after the CRC it carries matches the whole app area as read back from
 *      the flash, so a torn image is never bootable;
 *   4. asks 0xF0000000 ("success"), then invalidates the update record (RAM
 *      and flash: 4K boundary - 256 between 0x93000 and 0xFC000, outside
 *      Felucca's store, where only user data lives) so the SPL boots the new
 *      app, and resets.
 * Power loss during 3: the flash record is still there, the SPL runs the
 * loader again on the next power-on and the host can resume. A warm reset
 * during 3 (a crash, a long press): the RAM record is armed again from the
 * first change until the commit, so the SPL runs the loader, not a half-written
 * app, and ldr_boot() keeps it armed across further warm resets while the app
 * area head is erased. (Otherwise ldr_boot() clears the RAM record at start, so
 * a loader that fails before changing anything still falls back to the old app
 * on a warm reset.)
 *
 * Hooks from the platform (loader.c, ldr_test.c):
 *   ldr_fread(off, p, n)  ldr_erase(off)  ldr_prog(off, p, n)   flash, 0 = ok
 *   ldr_record_clear()    forget the RAM update record
 *   ldr_record_arm()      write a valid RAM update record (this loader again)
 *   ldr_progress(done, total)
 * plus the ota.c hooks (frames, time, idle). */
#define LDR_APP_LO 0x4000u
#define LDR_APP_HI 0x93000u
#define LDR_REC_LO 0x93000u                     /* update records live above the app ... */
#define LDR_REC_HI 0xFC000u                     /* ... and below Felucca's globals (Felucca's records: 0xE4F00, */
#define LDR_DATA_LO 0x97000u                    /* the stock firmware's: 0xE8F00), never in Felucca's store, whose */
#define LDR_DATA_HI 0xE0000u                    /* bytes (user samples) the host writes */
#define LDR_NSEC ((LDR_APP_HI - LDR_APP_LO) >> 12)
#define LDR_FL_MAX 0x100000u                    /* flash.bin: at most the 1 MiB part */

static int ldr_fread(uint32_t off, void *p, uint32_t n);
static int ldr_erase(uint32_t off);
static int ldr_prog(uint32_t off, const void *p, uint32_t n);
static void ldr_record_clear(void);
static void ldr_record_arm(void);
static void ldr_progress(uint32_t done, uint32_t total);

/* SFC cipher: per 32-byte block, key ^ (block offset >> 2) */
static void ldr_sfc(uint8_t *p, uint32_t n, uint32_t base_off, uint32_t key)
{
    uint32_t i, j;
    for (i = 0; i < n; i += 32u) {
        uint32_t k = key ^ ((base_off + i) >> 2);
        for (j = 0; j < 32u && i + j < n; j++) {
            p[i + j] ^= (uint8_t)k;
            k = ((k << 1) ^ (k & 0x8000u ? 0x1021u : 0u)) & 0xFFFFu;
        }
    }
}

/* chip key from the device's flash head: JLFS top entries (ENC 0xFFFF) -> isd_config.ini blob */
static int ldr_chip_key(uint32_t *key)
{
    uint8_t e[32], blob[34];
    uint32_t off, i, sum, k;
    for (off = 32; off < 0x400u; off += 32u) {
        if (ldr_fread(off, e, 32))
            return -1;
        ota_jl_enc(e, 32);
        if (ota_crc16(e + 2, 30, 0) != ota_rd16(e))
            return -2;
        if (!ota_memeq(e + 16, (const uint8_t *)"isd_config.ini", 15)) {
            if (ota_rd16(e + 14))
                return -3;                               /* last entry, not found */
            continue;
        }
        if (ldr_fread(ota_rd32(e + 4), blob, 34) || ota_crc16(blob, 32, 0) != ota_rd16(blob + 32))
            return -4;
        for (i = 0, sum = 0; i < 16u; i++)
            sum += blob[i];
        sum &= 0xFFu;
        sum = sum >= 0xE0u ? 0xAAu : sum <= 0x10u ? 0x55u : sum;
        for (i = 0, k = 0; i < 16u; i++)
            if ((uint32_t)(blob[16 + i] ^ blob[15 - i]) < sum)
                k |= 1u << i;
        *key = k;
        return 0;
    }
    return -3;
}

/* 2b. flash.bin [0, fl_size) from the host, before any erase: its CRC16 must be the UFW entry's (want); sc gets
 * the CRC16 of each app sector as it came in */
static int ldr_check(uint32_t fl_off, uint32_t fl_size, uint32_t want, uint16_t *sc, uint8_t *b)
{
    uint32_t i, n, crc = 0;
    for (i = 0; i < fl_size; i += n) {
        n = fl_size - i > 512u ? 512u : fl_size - i;
        if (ota_read(fl_off + i, b, n))
            return -7;
        crc = ota_crc16(b, n, crc);
        if (i >= LDR_APP_LO && i < LDR_APP_HI) {     /* (512-byte reads from 0: never across a sector) */
            uint32_t k = (i - LDR_APP_LO) >> 12;
            sc[k] = (uint16_t)ota_crc16(b, n, (i & 0xFFFu) ? sc[k] : 0u);
        }
    }
    return crc == want ? 0 : -12;
}

/* one sector: erase, program [from, 0x1000) from src, read back (cur); [0, from)
 * stays erased. Two tries. */
static int ldr_write_sector(uint32_t s, const uint8_t *src, uint32_t from, uint8_t *cur)
{
    uint32_t tries, k, n;
    for (tries = 0; tries < 2u; tries++) {
        if (ldr_erase(s))
            return -9;
        for (k = from; k < 0x1000u; k += n) {
            n = 256u - (k & 0xFFu);                      /* to the end of the page */
            if (ldr_prog(s + k, src + k, n))
                return -10;
        }
        if (ldr_fread(s, cur, 0x1000u))
            return -8;
        for (k = 0; k < from && cur[k] == 0xFFu; k++)
            ;
        if (k == from && ota_memeq(src + from, cur + from, 0x1000u - from))
            return 0;
    }
    return -11;                                          /* verify failed twice */
}

/* an app sector of the package, as checked in 2b, else read it again */
static int ldr_pkg_sector(uint32_t fl_off, uint32_t s, const uint16_t *sc, uint8_t *sec)
{
    uint32_t again, k;
    for (again = 0;; again++) {
        for (k = 0; k < 0x1000u; k += 512u)
            if (ota_read(fl_off + s + k, sec + k, 512))
                return -7;
        if (ota_crc16(sec, 0x1000u, 0) == sc[(s - LDR_APP_LO) >> 12])
            return 0;
        if (again == 2u)
            return -13;
    }
}

/* CRC16 of the app area [0x4000 + 32, 0x4000 + blk) as it is in the flash, decrypted */
static int ldr_app_crc(uint32_t blk, uint32_t key, uint8_t *buf, uint32_t *crc)
{
    uint32_t a, n;
    *crc = 0;
    for (a = 0; a < blk; a += n) {
        n = blk - a > 0x1000u ? 0x1000u : blk - a;
        if (ldr_fread(LDR_APP_LO + a, buf, n))
            return -8;
        ldr_sfc(buf, n, a, key);
        *crc = a ? ota_crc16(buf, n, *crc) : ota_crc16(buf + 32, n - 32u, *crc);
        ldr_progress(LDR_APP_HI - LDR_APP_LO, LDR_APP_HI - LDR_APP_LO);   /* watchdog, USB */
    }
    return 0;
}

/* loader start: forget the RAM record, so a loader that fails before changing
 * anything falls back to the old app on a warm reset; but with the app area
 * head erased (an update in progress, ldr_session) the app is not bootable:
 * keep the loader armed. */
static void ldr_boot(void)
{
    uint8_t h[32];
    uint32_t i;
    if (ldr_fread(LDR_APP_LO, h, 32) == 0) {
        for (i = 0; i < 32u && h[i] == 0xFFu; i++)
            ;
        if (i == 32u) {
            ldr_record_arm();
            return;
        }
    }
    ldr_record_clear();
}

static int ldr_session(void)
{
    static uint8_t hdr[0x400], first[0x1000], sec[0x1000], cur[0x1000];
    static uint16_t sc[LDR_NSEC];
    uint32_t i, fl_off, fl_size, ota_off, ota_len, key, s, blk, dcrc, crc, dirty, want = ~0u, done = 0;   /* (no CRC16: no flash.bin entry) */
    int rc;
    /* 1. UFW header + entry list (ota.c; it leaves the entries decoded in hdr) */
    if ((rc = ota_ufw(hdr, &fl_off, &fl_size, &ota_off, &ota_len)) != 0)
        return rc;
    if (!fl_off || fl_size < LDR_APP_HI || fl_size > LDR_FL_MAX)
        return -3;
    for (i = 0; i < ota_rd16(hdr + 8); i++)
        if (ota_rd16(hdr + 0x40 + i * 0x50u) == 0)
            want = ota_rd16(hdr + 0x40 + i * 0x50u + 4u);   /* flash.bin's data CRC16 */
    /* 2. the package's app area must decrypt with this chip's key */
    if ((rc = ldr_chip_key(&key)) != 0)
        return -40 + rc;
    if (ota_read(fl_off + LDR_APP_LO, sec, 32))
        return -5;
    ldr_sfc(sec, 32, 0, key);
    if (ota_crc16(sec + 2, 30, 0) != ota_rd16(sec))
        return -6;                                       /* package for another chip key */
    dcrc = ota_rd16(sec + 2);                            /* CRC of [32, blk) of the app area, plain */
    blk = ota_rd32(sec + 8);
    if (blk <= 32u || blk > LDR_APP_HI - LDR_APP_LO)
        return -15;
    /* 2b. the whole package first: nothing is erased for a damaged one */
    if ((rc = ldr_check(fl_off, fl_size, want, sc, sec)) != 0)
        return rc;
    /* 3. app area, sector by sector. The first change erases the head sector (and
     *    arms the RAM record); its body goes back at once, its head comes last. */
    if ((rc = ldr_pkg_sector(fl_off, LDR_APP_LO, sc, first)) != 0)
        return rc;
    if (ldr_fread(LDR_APP_LO, cur, 0x1000u))
        return -8;
    dirty = !ota_memeq(first, cur, 0x1000u);
    if (dirty) {
        ldr_record_arm();
        if ((rc = ldr_write_sector(LDR_APP_LO, first, 32, cur)) != 0)
            return rc;
    }
    for (s = LDR_APP_LO + 0x1000u; s < LDR_APP_HI; s += 0x1000u) {
        if ((rc = ldr_pkg_sector(fl_off, s, sc, sec)) != 0)
            return rc;
        if (ldr_fread(s, cur, 0x1000u))
            return -8;
        if (!ota_memeq(sec, cur, 0x1000u)) {
            if (!dirty) {                                /* the head sector was current: invalidate it first */
                dirty = 1;
                ldr_record_arm();
                if ((rc = ldr_write_sector(LDR_APP_LO, first, 32, cur)) != 0)
                    return rc;
            }
            if ((rc = ldr_write_sector(s, sec, 0, cur)) != 0)
                return rc;
        }
        done += 0x1000u;
        ldr_progress(done, LDR_APP_HI - LDR_APP_LO);
    }
    /* the whole app area as written must match the CRC in the package's head */
    if ((rc = ldr_app_crc(blk, key, cur, &crc)) != 0)
        return rc;
    if (crc != dcrc)
        return -16;                                      /* damaged app: stays unbootable, the record stays */
    if (dirty) {                                         /* commit: the app area head, last */
        if (ldr_prog(LDR_APP_LO, first, 32) || ldr_fread(LDR_APP_LO, cur, 32) || !ota_memeq(first, cur, 32))
            return -14;
    }
    /* 4. finish: the host confirms, the record goes, the SPL boots the app */
    for (i = 0; i < 4u; i++)
        if (!ota_read(0xF0000000u, sec, 8))
            break;
    ldr_record_clear();
    for (s = LDR_REC_HI; s > LDR_REC_LO; s -= 0x1000u) {   /* flash records: 4K boundary - 256 */
        uint8_t r[80];
        if (s - 0x1000u >= LDR_DATA_LO && s - 0x1000u < LDR_DATA_HI)
            continue;                                    /* Felucca's store: user data that may look like one */
        if (ldr_fread(s - 0x100u, r, 80))
            break;
        if (ota_rd16(r + 6) == 0x5441u && ota_rd16(r) && ota_rd16(r) == ota_crc16(r + 2, 78, 0))
            ldr_erase(s - 0x1000u);
    }
    return 0;
}

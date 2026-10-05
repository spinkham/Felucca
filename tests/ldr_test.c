/* SPDX-License-Identifier: GPL-3.0-only
 * Copyright (C) 2026 Leo Kuroshita (@kurogedelic), Hügelton Instruments */
/* Host test of the Felucca update loader (firmware/loader/ldr_core.c): a fake
 * host serves a package over the SysEx protocol, the "device" flash starts as
 * another package's flash.bin (as if that firmware were installed).
 *   ldr_test OLD.fwsc NEW.fwsc */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FELUCCA_ID "ota-FM-1_900"
#define FELUCCA_OTA_DRYRUN 0

static uint8_t nor[0x100000], *logical;
static size_t logical_len;
static uint8_t rx[1024];
static uint32_t rx_len, rx_full, now_ms, requests, erases, bad_range, record_cleared, f0_asked;
static uint32_t flip_addr = 0xFFFFFFFFu, flip_seen, flip_on;   /* serve addr's flip_on-th reply with a byte changed */
static uint32_t ram_record, armed, fail_at_erase, last_prog_off, last_prog_n;

static uint32_t pack7(const uint8_t *in, uint32_t n, uint8_t *out)
{
    uint32_t acc = 0, nb = 0, o = 0;
    while (n--) {
        acc |= (uint32_t)*in++ << nb;
        nb += 8;
        while (nb >= 7) { out[o++] = acc & 0x7F; acc >>= 7; nb -= 7; }
    }
    if (nb) out[o++] = acc & 0x7F;
    return o;
}
static uint32_t unpack7h(const uint8_t *in, uint32_t n, uint8_t *out)
{
    uint32_t acc = 0, nb = 0, o = 0;
    while (n--) {
        acc |= (uint32_t)*in++ << nb;
        nb += 7;
        if (nb >= 8) { out[o++] = (uint8_t)acc; acc >>= 8; nb -= 8; }
    }
    return o;
}

static int ota_wire_send(const uint8_t *p, uint32_t n)
{
    uint8_t u[64], m[600];
    uint32_t addr, len, i, s = 0;
    unpack7h(p + 1, n - 2, u);
    if (u[2] == 0x11) return 0;
    addr = u[7] | u[8] << 8 | u[9] << 16 | (uint32_t)u[10] << 24;
    len = u[11] | u[12] << 8 | u[13] << 16;
    requests++;
    memcpy(m, "\x00\x59\x30", 3);
    m[3] = (uint8_t)(len + 8); m[4] = (uint8_t)((len + 8) >> 8); m[5] = 0; m[6] = 0;
    memcpy(m + 7, &addr, 4);
    m[11] = (uint8_t)len; m[12] = (uint8_t)(len >> 8); m[13] = 0;
    if (addr >= 0xE0000000u) {
        f0_asked += addr == 0xF0000000u;
        memset(m + 14, 0, len);
        memcpy(m + 14, "success", 8);
    } else {
        if (addr + len > logical_len) { printf("read past the package %#x\n", addr); exit(1); }
        memcpy(m + 14, logical + addr, len);
        if (addr == flip_addr && ++flip_seen == flip_on)
            m[14 + len / 2u] ^= 0x10;                /* a transfer error the frame checksum does not see */
    }
    for (i = 6; i < 14 + len; i++) s += m[i];
    m[14 + len] = (uint8_t)~s;
    rx_len = pack7(m, 15 + len, rx);
    rx_full = 1;
    return 0;
}
static int ota_frame_get(const uint8_t **p, uint32_t *n) { if (!rx_full) return 0; *p = rx; *n = rx_len; return 1; }
static void ota_frame_done(void) { rx_full = 0; }
static uint32_t ota_now_ms(void) { return now_ms; }
static void ota_idle(void) { now_ms++; }
static int ota_erase(uint32_t off) { (void)off; return -1; }
static int ota_prog(uint32_t off, const void *p, uint32_t n) { (void)off; (void)p; (void)n; return -1; }
static int ota_fread(uint32_t off, void *p, uint32_t n) { memcpy(p, nor + off, n); return 0; }
static void ota_show(uint32_t step, int32_t code) { (void)step; (void)code; }
static void ota_commit(const uint8_t *parm) { (void)parm; }
#include "../firmware/src/ota.c"

static int ldr_fread(uint32_t off, void *p, uint32_t n) { memcpy(p, nor + off, n); return 0; }
static int ldr_erase(uint32_t off)
{
    if (off < 0x4000u || off >= 0xFC000u || (off & 0xFFFu) || (off >= 0x97000u && off < 0xE0000u)) bad_range++;
    if (off < 0x4000u) { printf("ERASE IN THE HEAD %#x\n", off); exit(1); }
    if (fail_at_erase && erases + 1u == fail_at_erase) return -1;    /* power loss / failing part */
    erases++;
    memset(nor + off, 0xFF, 0x1000);
    return 0;
}
static int ldr_prog(uint32_t off, const void *p, uint32_t n)
{
    const uint8_t *s = p;
    uint32_t i;
    if (off < 0x4000u || off + n > 0x93000u || ((off & 0xFFu) + n) > 256u) bad_range++;
    for (i = 0; i < n; i++) nor[off + i] &= s[i];
    last_prog_off = off;
    last_prog_n = n;
    return 0;
}
static void ldr_record_clear(void) { record_cleared++; ram_record = 0; }
static void ldr_record_arm(void) { armed++; ram_record = 1; }
static void ldr_progress(uint32_t done, uint32_t total) { (void)done; (void)total; }
#include "../firmware/loader/ldr_core.c"

static uint8_t *load_logical(const char *path, size_t *len)
{
    FILE *f = fopen(path, "rb");
    uint8_t *raw = malloc(0x200000), *lg;
    size_t n, i;
    if (!f) { perror(path); exit(2); }
    n = fread(raw, 1, 0x200000, f);
    fclose(f);
    if (n < 20 * 48 + 0x400) { printf("%s: too short for a package\n", path); exit(2); }
    lg = malloc(n);
    for (i = 0; i < 20; i++) memcpy(lg + i * 47, raw + i * 48, 47);
    memcpy(lg + 20 * 47, raw + 20 * 48, n - 20 * 48);
    *len = n - 20;
    free(raw);
    return lg;
}

static uint32_t flash_off(const uint8_t *lg)        /* flash.bin offset in the logical image */
{
    uint8_t h[0x400];
    uint32_t i, n;
    memcpy(h, lg, sizeof h);
    ota_jl_enc(h, 0x40);
    n = ota_rd16(h + 8);
    for (i = 0; i < n; i++) {
        uint8_t *e = h + 0x40 + i * 0x50u;
        ota_jl_enc(e, 0x50);
        if (ota_rd16(e) == 0) return ota_rd32(e + 8);
    }
    return 0;
}

static uint8_t *old;
static uint32_t ofo, nfo;

/* set the UFW entry's flash.bin CRC16 to the CRC of flash.bin as it is (a test package built inconsistent) */
static void flash_crc_fix(uint8_t *lg)
{
    uint8_t *h = lg;
    uint32_t i, n;
    ota_jl_enc(h, 0x40);                            /* (the cipher is an XOR stream: twice restores) */
    n = ota_rd16(h + 8);
    for (i = 0; i < n; i++) {
        uint8_t *e = h + 0x40 + i * 0x50u;
        ota_jl_enc(e, 0x50);
        if (ota_rd16(e) == 0)
            ota_wr16(e + 4, (uint16_t)ota_crc16(lg + ota_rd32(e + 8), ota_rd32(e + 12), 0));
        ota_jl_enc(e, 0x50);
    }
    ota_wr16(h + 2, (uint16_t)ota_crc16(h + 0x40, n * 0x50u, 0));
    ota_wr16(h, (uint16_t)ota_crc16(h + 2, 0x3E, 0));
    ota_jl_enc(h, 0x40);
}

/* device: OLD installed (or `img`), plus a valid update record at 0xE4F00 */
static void device(const uint8_t *img)
{
    uint8_t r[112] = {0};
    memset(nor, 0xFF, sizeof nor);
    memcpy(nor, img, 0x93000);
    r[2] = 0x0D; r[3] = 0x5A; r[4] = 0x01; r[5] = 0x5A; r[6] = 0x41; r[7] = 0x54;
    ota_wr16(r, ota_crc16(r + 2, 78, 0));
    memcpy(nor + 0xE4F00, r, sizeof r);
    erases = requests = f0_asked = record_cleared = armed = fail_at_erase = 0;
    ram_record = 0;                                /* loader.c clears it first thing */
}
static int head_blank(void)                         /* the app area head is erased: not bootable */
{
    uint32_t i;
    for (i = 0; i < 32u; i++) if (nor[0x4000 + i] != 0xFF) return 0;
    return 1;
}
static int app_is_new(void) { return !memcmp(nor + 0x4000, logical + nfo + 0x4000, 0x93000 - 0x4000); }
static int flash_record(void) { return nor[0xE4F06] == 0x41; }

static int check(const char *what, int ok) { printf("%-56s %s\n", what, ok ? "ok" : "FAIL"); return ok ? 0 : 1; }

int main(int argc, char **argv)
{
    size_t olen;
    static uint8_t user[0x1000];
    uint8_t head[0x4000];
    uint32_t i;
    int bad = 0, rc;
    if (argc < 3) { printf("usage: ldr_test OLD.fwsc NEW.fwsc\n"); return 2; }
    old = load_logical(argv[1], &olen);
    logical = load_logical(argv[2], &logical_len);
    ofo = flash_off(old);
    nfo = flash_off(logical);
    /* device: OLD installed, plus a valid update record at 0xE4F00 (Felucca's step 1) and 0xE8F00 (the stock
     * firmware's, a first install from it); user sample data in Felucca's store that looks like a record */
    device(old + ofo);
    memcpy(head, nor, sizeof head);
    {
        uint8_t r[112];
        memcpy(r, nor + 0xE4F00, sizeof r);
        memcpy(nor + 0xE8F00, r, sizeof r);
        for (i = 0; i < 0x1000u; i++) nor[0xA0000 + i] = (uint8_t)(i * 7u);
        memcpy(nor + 0xA0F00, r, sizeof r);
        memcpy(user, nor + 0xA0000, sizeof user);
    }
    /* a damaged package (one byte deep in the app area): refused before anything is erased */
    {
        size_t at = nfo + 0x50123u;
        logical[at] ^= 0x01;
        erases = 0;
        rc = ldr_session();
        bad += check("damaged package (flash.bin CRC) refused, nothing erased", rc == -12 && erases == 0 &&
                     !memcmp(nor + 0x4000, old + ofo + 0x4000, 0x93000 - 0x4000) && nor[0xE4F06] == 0x41 && !armed);
        logical[at] ^= 0x01;
        requests = 0;
    }
    /* a sector that comes in different the second time (a transfer error after the check) is read again */
    flip_addr = nfo + 0x20000u; flip_on = 2; flip_seen = 0;
    rc = ldr_session();
    printf("  rc %d, %u requests, %u sector erases\n", rc, requests, erases);
    bad += check("install completes", rc == 0);
    bad += check("a sector changed in transfer after the check is read again", flip_seen == 3);
    flip_addr = 0xFFFFFFFFu;
    bad += check("app area == the new package's flash.bin", !memcmp(nor + 0x4000, logical + nfo + 0x4000, 0x93000 - 0x4000));
    bad += check("flash head [0, 0x4000) untouched", !memcmp(nor, head, sizeof head));
    bad += check("finish asked (0xF0000000)", f0_asked >= 1);
    bad += check("update records cleared (RAM + flash 0xE4F00, the stock firmware's 0xE8F00)",
                 record_cleared && !ram_record && nor[0xE4F06] == 0xFF && nor[0xE8F06] == 0xFF);
    bad += check("user data in Felucca's store that looks like a record is kept", !memcmp(nor + 0xA0000, user, sizeof user));
    bad += check("RAM record armed while the app area was changing", armed >= 1);
    bad += check("app area head programmed last (the commit)", last_prog_off == 0x4000u && last_prog_n == 32u);
    bad += check("no write outside the allowed windows", bad_range == 0);
    /* same package again: nothing to erase */
    erases = 0; requests = 0; armed = 0;
    rc = ldr_session();
    bad += check("re-run with the same package erases nothing", rc == 0 && erases == 0 && armed == 0);
    /* power loss halfway: the app is not bootable, both records stay; the next session resumes */
    device(old + ofo);
    fail_at_erase = 40;
    rc = ldr_session();
    bad += check("interrupted install: app area head erased (not bootable)", rc != 0 && head_blank());
    bad += check("interrupted install: RAM + flash record kept", ram_record && flash_record() && !record_cleared);
    ram_record = 0;
    ldr_boot();
    bad += check("loader start with the app area head erased: stays armed", ram_record == 1);
    fail_at_erase = 0;
    rc = ldr_session();
    bad += check("interrupted install resumes to the new app", rc == 0 && app_is_new() && !ram_record &&
                 !memcmp(nor, head, sizeof head));
    ram_record = 1;
    ldr_boot();
    bad += check("loader start with a bootable app: record cleared", ram_record == 0);
    /* the new app installed but one later sector differs: the head goes first, comes back last */
    device(logical + nfo);
    nor[0x50123] ^= 0xFF;
    fail_at_erase = 2;                              /* the head sector erase passes, the next one fails */
    rc = ldr_session();
    bad += check("head current, later sector stale: head erased before it", rc != 0 && head_blank() && ram_record);
    fail_at_erase = 0;
    rc = ldr_session();
    bad += check("... and the next session completes", rc == 0 && app_is_new() && last_prog_off == 0x4000u);
    /* a package whose app does not match its own app area head CRC, but whose flash.bin CRC was made to
     * match (so 2b passes): written, never committed */
    {
        uint32_t at = nfo + 0x4000 + 0x30000;
        logical[at] ^= 0x01;
        flash_crc_fix(logical);
        device(old + ofo);
        rc = ldr_session();
        bad += check("inconsistent package: -16, head not committed, records kept",
                     rc == -16 && head_blank() && ram_record && flash_record() && !f0_asked);
        logical[at] ^= 0x01;
        flash_crc_fix(logical);
        rc = ldr_session();
        bad += check("... the good package then installs", rc == 0 && app_is_new());
    }
    /* a package for another chip key is refused before any erase */
    {
        uint8_t save = logical[nfo + 0x4000 + 5];
        logical[nfo + 0x4000 + 5] ^= 0x5A;           /* app area head no longer decrypts */
        device(old + ofo);
        rc = ldr_session();
        bad += check("foreign key / damaged app head refused, nothing erased", rc == -6 && erases == 0);
        logical[nfo + 0x4000 + 5] = save;
    }
    printf("%s\n", bad ? "LOADER TEST FAILED" : "loader test passed");
    return bad != 0;
}

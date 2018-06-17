#include <openssl/evp.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>

typedef unsigned __int128 uint128_t;

struct GfTbl {
  uint128_t data[256];
};

void gf_tbl_populate(struct GfTbl *tbl, uint64_t multiplier)
{
  int i, k;
  uint64_t a;
  for (i = 0; i < 256; i++)
  {
    tbl->data[i] = 0;
    a = i;
    for (k = 0; k < 8; k++)
    {
      if (a&1)
      {
        uint128_t val128;
        val128 = (((uint128_t)multiplier)<<64) >> (63-k);
        tbl->data[i] = tbl->data[i] ^ val128;
      }
      a >>= 1;
    }
  }
}

uint128_t clmul64(uint64_t a, struct GfTbl *b_tbl)
{
  uint128_t res = 0;
  int k;
  for (k = 0; k < 8; k++)
  {
    uint128_t tmpval = b_tbl->data[a&0xFF]<<(8*k);
    res ^= tmpval;
    a >>= 8;
  }
  return res;
}

void clmul128(uint128_t *rlo, uint128_t *rhi,
              uint128_t a, struct GfTbl *b_lo, struct GfTbl *b_hi)
{
  uint128_t v1 = clmul64(a&UINT64_MAX, b_lo);
  uint128_t v2 = clmul64(a&UINT64_MAX, b_hi);
  uint128_t v3 = clmul64(a>>64, b_lo);
  uint128_t v4 = clmul64(a>>64, b_hi);
  *rlo = v1 ^ (v2<<64) ^ (v3<<64);
  *rhi = (v2>>64) ^ (v3>>64) ^ v4;
}

uint128_t modpoly(uint128_t lo, uint128_t hi)
{
  uint128_t lo1, lo2, lo3, lo4, rm1, rm2, rm3, rm4, los, rms;
  while (hi != 0)
  {
    lo1 = hi>>7;
    lo2 = hi>>2;
    lo3 = hi>>1;
    lo4 = hi>>0;
    rm1 = ((hi<<64)>>7) & UINT64_MAX;
    rm2 = ((hi<<64)>>2) & UINT64_MAX;
    rm3 = ((hi<<64)>>1) & UINT64_MAX;
    rm4 = ((hi<<64)>>0) & UINT64_MAX;
    los = lo1^lo2^lo3^lo4;
    rms = rm1^rm2^rm3^rm4;
    lo = lo ^ los;
    hi = rms<<64;
  }
  return lo;
}

uint128_t clmodmul128(uint128_t a, struct GfTbl *b_lo, struct GfTbl *b_hi)
{
  uint128_t rlo, rhi;
  clmul128(&rlo, &rhi, a, b_lo, b_hi);
  return modpoly(rhi, rlo);
}

uint128_t clmul128slow(uint128_t *rlo, uint128_t *rhi, uint128_t a, uint128_t b)
{
  struct GfTbl b_lo, b_hi;
  gf_tbl_populate(&b_lo, b);
  gf_tbl_populate(&b_hi, b>>64);
  clmul128(rlo, rhi, a, &b_lo, &b_hi);
}

uint128_t clmodmul128slow(uint128_t a, uint128_t b)
{
  struct GfTbl b_lo, b_hi;
  gf_tbl_populate(&b_lo, b);
  gf_tbl_populate(&b_hi, b>>64);
  return clmodmul128(a, &b_lo, &b_hi);
}

void clmul_test()
{
  struct GfTbl tbl;
  uint128_t val1, val2;
  uint128_t u128;
  uint64_t lo, hi;
  uint128_t lo128, hi128;

  gf_tbl_populate(&tbl, 0x12345678);
  if (clmul64(0x87654321, &tbl) != 1352318730029507312LL)
  {
    printf("err1\n");
    abort();
  }
  if (clmul64(0x987654321LL, &tbl) & UINT64_MAX != 1578984220326634224L)
  {
    printf("err2\n");
    abort();
  }
  if (clmul64(0x987654321LL, &tbl) >> 64 != 1)
  {
    printf("err3\n");
    abort();
  }

  clmul128slow(&lo128, &hi128, 0x123456787654321, 0x876543212345678);

  lo = lo128 & UINT64_MAX;
  hi = lo128 >> 64;
  if (lo != 3476421074286289648LLU)
  {
    printf("errA\n");
    abort();
  }
  if (hi != 5282495036037788LLU)
  {
    printf("errB\n");
    abort();
  }

  lo = hi128 & UINT64_MAX;
  hi = hi128 >> 64;
  if (lo != 0)
  {
    printf("errC\n");
    abort();
  }
  if (hi != 0)
  {
    printf("errD\n");
    abort();
  }

  u128 = clmodmul128slow(0x123456787654321, 0x876543212345678);
  lo = u128 & UINT64_MAX;
  hi = u128 >> 64;
  if (lo != 2039624978001441649LLU)
  {
    printf("err4\n");
    abort();
  }
  if (hi != 12240558131881196608LLU)
  {
    printf("err5\n");
    abort();
  }

  val1 = 0x123456787654321;
  val1 <<= 64;
  val1 |= 0x123456787654321;

  val2 = 0x123456787654321;
  val2 <<= 64;
  val2 |= 0x123456787654321;

  u128 = clmodmul128slow(val1, val2);

  lo = u128 & UINT64_MAX;
  hi = u128 >> 64;
  if (lo != 13051372663720088081LLU)
  {
    printf("ErrErr1\n");
    abort();
  }
  if (hi != 16575922941164378703LLU)
  {
    printf("ErrErr2\n");
    abort();
  }

  printf("ok\n");
}

int main(int argc, char **argv)
{
  EVP_CIPHER_CTX *ctx;
  int ciphertext_len, len;
  char aad[] =
    "\xfe\xed\xfa\xce\xde\xad\xbe\xef"
    "\xfe\xed\xfa\xce\xde\xad\xbe\xef"
    "\xab\xad\xda\xd2";
  char iv[] = "\xca\xfe\xba\xbe\xfa\xce\xdb\xad\xde\xca\xf8\x88";
  char key[] =
    "\xfe\xff\xe9\x92\x86\x65\x73\x1c\x6d\x6a\x8f\x94\x67\x30\x83\x08";
  char ciphertext[1024] = {0};
  char plaintext[] = "\xd9\x31\x32\x25\xf8\x84\x06\xe5"
                     "\xa5\x59\x09\xc5\xaf\xf5\x26\x9a"
                     "\x86\xa7\xa9\x53\x15\x34\xf7\xda"
                     "\x2e\x4c\x30\x3d\x8a\x31\x8a\x72"
                     "\x1c\x3c\x0c\x95\x95\x68\x09\x53"
                     "\x2f\xcf\x0e\x24\x49\xa6\xb5\x25"
                     "\xb1\x6a\xed\xf5\xaa\x0d\xe6\x57"
                     "\xba\x63\x7b\x39";
  int plaintext_len = sizeof(plaintext) - 1;
  int aad_len = sizeof(aad) - 1;
  int iv_len = sizeof(iv) - 1;
  char tag[16] = {0};
  int i;
  char expected_tag[] = "\x5b\xc9\x4f\xbc\x32\x21\xa5\xdb\x94\xfa\xe9\x5a\xe7\x12\x1a\x47";
  char expected_ciphertext[] = 
                 "\x42\x83\x1e\xc2\x21\x77\x74\x24"
                 "\x4b\x72\x21\xb7\x84\xd0\xd4\x9c"
                 "\xe3\xaa\x21\x2f\x2c\x02\xa4\xe0"
                 "\x35\xc1\x7e\x23\x29\xac\xa1\x2e"
                 "\x21\xd5\x14\xb2\x54\x66\x93\x1c"
                 "\x7d\x8f\x6a\x5a\xac\x84\xaa\x05"
                 "\x1b\xa3\x0b\x39\x6a\x0a\xac\x97"
                 "\x3d\x58\xe0\x91";

  if(!(ctx = EVP_CIPHER_CTX_new())) abort();
  if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_128_gcm(), NULL, NULL, NULL)) abort();
  if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, iv_len, NULL)) abort();
  if(1 != EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv)) abort();
  if(1 != EVP_EncryptUpdate(ctx, NULL, &len, aad, aad_len)) abort();
  if(1 != EVP_EncryptUpdate(ctx, ciphertext, &len, plaintext, plaintext_len)) abort();
  ciphertext_len = len;
  if(1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len)) abort();
  ciphertext_len += len;
  if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag)) abort();
  printf("Ciphertext len: %d\n", ciphertext_len);
  for (i = 0; i < ciphertext_len; i++)
  {
    printf("%.2x ", (unsigned char)ciphertext[i]);
  }
  printf("\n");
  printf("Tag:\n");
  for (i = 0; i < 16; i++)
  {
    printf("%.2x ", (unsigned char)tag[i]);
  }
  printf("\n");
  if (memcmp(expected_ciphertext, ciphertext, ciphertext_len) != 0)
  {
    abort();
  }
  if (memcmp(expected_tag, tag, 16) != 0)
  {
    abort();
  }

  clmul_test();

  return 0;
}

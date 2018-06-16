import random
import time
import binascii
from Crypto.Cipher import AES

def clmul128(a,b):
  reslo = 0
  reshi = 0
  for k in xrange(128):
    if a&1:
      reslo ^= (b<<k) & ((1<<128)-1)
      reshi ^= (b<<k) >> 128
    a >>= 1
  return reslo, reshi

def clmul64(a,b):
  reslo = 0
  reshi = 0
  for k in xrange(64):
    if a&1:
      reslo ^= (b<<k) & ((1<<64)-1)
      reshi ^= (b<<k) >> 64
    a >>= 1
  return reslo, reshi

def clmul128inv(a,b):
  reslo = 0
  reshi = 0
  for k in xrange(128):
    if a&1:
      reslo ^= (b<<128)>>(127-k) >> 128
      reshi ^= (b<<128)>>(127-k) & ((1<<128)-1)
      #reslo ^= (b<<64)>>(k) >> 64
      #reshi ^= (b<<64)>>(k) & ((1<<64)-1)
    a >>= 1
  return reshi, reslo

def bitinv64(x):
  return sum(((x>>(63-k))&1)<<k for k in xrange(64))

def bitinv128(x):
  return sum(((x>>(127-k))&1)<<k for k in xrange(128))

def clmul64inv(a,b):
  reslo = 0
  reshi = 0
  for k in xrange(64):
    if a&1:
      tmpval = ((b<<64)>>(63-k))
      reslo ^= tmpval >> 64
      reshi ^= tmpval & ((1<<64)-1)
      #reslo ^= (b<<64)>>(k) >> 64
      #reshi ^= (b<<64)>>(k) & ((1<<64)-1)
    a >>= 1
  return reshi, reslo

class Num128(object):
  @staticmethod
  def rand():
    return Num128(random.randrange(1<<128))
  def __init__(self, lo, hi=0):
    hi += lo>>64
    hi &= ((1<<64)-1)
    lo &= ((1<<64)-1)
    self.hi = hi
    self.lo = lo
  def add(self, other):
    s1 = self.lo + other.lo
    new_lo = s1 & ((1<<64)-1)
    new_hi = ((self.hi + other.hi) + (s1>>64)) & ((1<<64)-1)
    return Num128(new_lo, new_hi), Num128(((self.hi + other.hi) + (s1>>64))>>64)
  def modadd(self, other):
    lo,hi = self.add(other)
    return lo.modpoly(hi)
  def mulcarry(self, other):
    p1 = self.lo * other.lo
    new_lo = p1 & ((1<<64) - 1)
    p2 = (p1 >> 64) + self.hi*other.lo + self.lo*other.hi
    new_hi = p2 & ((1<<64) - 1)
    p3 = (p2 >> 64) + self.hi*other.hi
    new2_lo = p3 & ((1<<64) - 1)
    p4 = p3 >> 64
    new2_hi = p4
    return Num128(new_lo, new_hi), Num128(new2_lo, new2_hi)
  def mul(self, other):
    a,b = self.mulcarry(other)
    return a
  def clmul(self, other):
    al,ah = clmul64(self.lo, other.lo)
    bl,bh = clmul64(self.lo, other.hi)
    cl,ch = clmul64(self.hi, other.lo)
    dl,dh = clmul64(self.hi, other.hi)
    return Num128(al, ah^bl^cl), Num128(bh^ch^dl, dh)
  #  8 0
  #  32 0
  #  16 0
  #  64 0
  def inv(self):
    return Num128(bitinv64(self.hi), bitinv64(self.lo))
  def clmulinv(self, other):
    ah,al = clmul64inv(self.lo, other.lo)
    bh,bl = clmul64inv(self.lo, other.hi)
    ch,cl = clmul64inv(self.hi, other.lo)
    dh,dl = clmul64inv(self.hi, other.hi)
    #print " ",ah,al
    #print " ",bh,bl
    #print " ",ch,cl
    #print " ",dh,dl
    #print "="
    #print "dh = " + hex(dh)
    #print "dl = " + hex(dl)
    #print "cl = " + hex(cl)
    #print "bl = " + hex(bl)
    #return Num128(al, ah^bl^cl), Num128(bh^ch^dl, dh)
    #return Num128(dh, dl^bh^ch), Num128(bl^cl^ah, al)
    lo,hi = Num128(ah, al^bh^ch), Num128(bl^cl^dh, dl)
    #lo2,hi2 = self.inv().clmul(other.inv())
    #print "?", hex(lo.to_long()), hex(hi.to_long())
    #print "?", hex(hi2.inv().to_long()), hex(lo2.inv().to_long())
    return lo,hi
    #x,y = clmul128inv(self.to_long(), other.to_long())
    #return Num128(x), Num128(y)
  def clmodmul(self, other):
    lo,hi = self.clmul(other)
    return lo.modpoly(hi)
  def clmodmulinv(self, other):
    lo,hi = self.clmulinv(other)
    return hi.modpolyinv(lo)
  def shlcarry(self, shift):
    assert shift == int(shift)
    assert shift >= 0
    assert shift <= 64
    reshi_lo = (self.hi<<shift)>>64
    reslo_hi = (self.hi<<shift) | ((self.lo<<shift)>>64)
    reslo_lo = (self.lo<<shift) & ((1<<64)-1)
    return Num128(reslo_lo, reslo_hi), Num128(reshi_lo, 0)
  def shrrm(self, shift):
    assert shift == int(shift)
    assert shift >= 0
    assert shift < 64
    reshi = self.hi >> shift
    reslo = (((self.hi << 64) >> shift) & ((1<<64) - 1)) | (self.lo >> shift)
    rm = ((self.lo << 64) >> shift) & ((1<<64) - 1)
    return Num128(reslo, reshi), Num128(rm)
  def xor(self, other):
    return Num128(self.lo ^ other.lo, self.hi ^ other.hi)
  def modpoly(self, other):
    lo = self
    hi = other
    while hi.lo != 0 or hi.hi != 0:
      lo1,hi1 = hi.shlcarry(7)
      lo2,hi2 = hi.shlcarry(2)
      lo3,hi3 = hi.shlcarry(1)
      lo4,hi4 = hi.shlcarry(0)
      hi = hi1.xor(hi2).xor(hi3).xor(hi4)
      lo = lo.xor(lo1).xor(lo2).xor(lo3).xor(lo4)
    return lo
  def modpolyinv(self, other):
    #return self.inv().modpoly(other.inv()).inv() # OK but slow!
    lo = self
    hi = other
    while hi.lo != 0 or hi.hi != 0:
      lo1,rm1 = hi.shrrm(7)
      lo2,rm2 = hi.shrrm(2)
      lo3,rm3 = hi.shrrm(1)
      lo4,rm4 = hi.shrrm(0)
      los = lo1.xor(lo2).xor(lo3).xor(lo4)
      rms = rm1.xor(rm2).xor(rm3).xor(rm4)
      lo = lo.xor(los)
      hi,xx = rms.shlcarry(64)
    #assert self.inv().modpoly(other.inv()) == lo.inv()
    return lo
  def __cmp__(self, other):
    r = cmp(self.hi, other.hi)
    if r != 0:
      return r
    return cmp(self.lo, other.lo)
  def to_long(self):
    return (self.hi<<64) | self.lo
  def __str__(self):
    return "Num128(" + str(self.to_long()) + ")"

def unit():
  x = random.randrange(1<<64)
  y = random.randrange(1<<64)
  lo,hi = clmul64(bitinv64(x),bitinv64(y))
  #print bitinv64(hi), bitinv64(lo)
  #print clmul64inv(x,y)
  assert clmul64inv(x,y) == (bitinv64(hi), bitinv64(lo))
  #
  a = (1<<62) + (1<<58) + (1<<56)
  b = (1<<62) + (1<<61) + (1<<59) + (1<<56)
  d,c = clmul64inv(a,b)
  assert c == (1<<(63-2)) + (1<<(63-3)) + (1<<(63-5)) + (1<<(63-6)) + (1<<(63-7)) + (1<<(63-11)) + (1<<(63-12)) + (1<<(63-14))
  assert d == 0
  #
  a = (1<<1) + (1<<5) + (1<<7)
  b = (1<<1) + (1<<2) + (1<<4) + (1<<7)
  c,d = clmul64(a,b)
  assert d == 0
  assert c == (1<<2) + (1<<3) + (1<<5) + (1<<6) + (1<<7) + (1<<11) + (1<<12) + (1<<14)
  #
  a <<= 55
  b <<= 55
  c,d = clmul64(a,b)
  x = (1<<2) + (1<<3) + (1<<5) + (1<<6) + (1<<7) + (1<<11) + (1<<12) + (1<<14)
  assert c == 0
  assert d == (x<<(55+55))>>64
  #
  r = random.randrange(1<<128)
  n = Num128(r)
  lo,rm = n.shrrm(5)
  assert lo.to_long() == r >> 5
  #
  #
  a,b = Num128(1).clmulinv(Num128(1))
  #print hex(b.modpolyinv(a).to_long())
  assert b.modpolyinv(a).to_long() == 0xe6080000000000000000000000000003L
  a,b = Num128(0x12345).clmulinv(Num128(0x54321))
  assert b.modpolyinv(a).to_long() == 0x1b280000000000000000000ccb362c4eL
  #raise SystemExit()
  #
  assert Num128(0x12345).clmodmulinv(Num128(0x54321)).to_long() == 0x1b280000000000000000000ccb362c4eL
  #raise SystemExit()
  #
  #
  #
  #
  #
  a = Num128(1,2) # (2<<64) | 1, x^127 + x^62
  b = Num128(4,8) # (8<<64) | 4, x^125 + x^60
  # a*b = x^122 + x^252
  # a*b = 32, 8
  l,h = a.clmulinv(b)
  assert h.to_long() == 32
  assert l.to_long() == 8
  #
  a = Num128(1,2) # (2<<64) | 1, x^127 + x^62
  b = Num128(4,16) # (16<<64) | 4, x^125 + x^59
  # a*b = x^121 + x^186 + x^187 + x^252
  # a*b = 32, 8
  l,h = a.clmulinv(b)
  #print hex(l.to_long()),hex(h.to_long())
  assert h.to_long() == 0x40
  assert l.to_long() == 0x300000000000000008
  #
  #
  x = Num128.rand()
  y = Num128.rand()
  rx,ry = x.clmul(y)
  rx2,ry2 = clmul128(x.to_long(), y.to_long())
  assert rx.to_long() == rx2
  assert ry.to_long() == ry2
  #
  #
  #
  x = Num128.rand()
  y = Num128.rand()
  xinv = x.inv()
  yinv = y.inv()
  rx,ry = x.clmulinv(y)
  #rx2,ry2 = clmul128inv(x.to_long(), y.to_long())
  rx2,ry2 = clmul128(xinv.to_long(), yinv.to_long())
  #
  assert ry.to_long() == bitinv128(rx2)
  assert rx.to_long() == bitinv128(ry2)
  #
  rx2,ry2 = clmul128inv(x.to_long(), y.to_long())
  #
  #print hex(rx.to_long()), hex(ry.to_long())
  #print hex(rx2), hex(ry2)
  assert rx.to_long() == rx2
  assert ry.to_long() == ry2
  #
  global poly
  poly = [1]+120*[0]+[1]+4*[0]+[1,1,1]
  hashkey = [random.randrange(2) for x in range(128)]
  #
  H = Num128(0b11101000000100110100010000111101111101100011011000011101011000001110001010010100111101111110011111000001101100000011000101101110)
  v = 3*8
  u = 3*8
  A = [Num128(bytesToLong("foo" + 13*"\x00"))]
  C = [Num128(bytesToLong("bar" + 13*"\x00"))]
  #print bin(A[0].to_long())
  #print bin(C[0].to_long())
  #print bin(fastghash(H, A, C, v, u).to_long())
  #print 'clmodmul', bin(A[0].clmodmul(C[0]).to_long())
  #print A[0].lo
  #print C[0].lo
  x,y = clmul64(A[0].lo, C[0].lo)
  #print x
  #
  #
  #
  As,v = packetize("foo")
  Cs,u = packetize("bar")
  #print '0b' + ''.join(str(x) for x in As[0])
  #print '0b' + ''.join(str(x) for x in Cs[0])
  Hs = [1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0]
  #print '0b' + ''.join(str(x) for x in ghash(Hs, As, Cs, v, u))
  #print 'modpoly,modmul', '0b' + ''.join(str(x) for x in modpoly(modmul(As[0],Cs[0]), poly))
  #
  #
  #val = [1] + 128*[0]
  #assert modpoly(val, poly) == 120*[0]+[1]+4*[0]+[1,1,1]
  #
  #val = [1] + 129*[0]
  #assert modpoly(val, poly) == 119*[0]+[1]+4*[0]+[1,1,1] + [0]
  #
  #val = [1,1] + 128*[0]
  #assert modpoly(val, poly) == 119*[0]+[1,1]+3*[0]+[1,0,0] + [1]
  #
  assert modmul([1,1,1], [1,1,1]) == [1,0,1,0,1]
  #
  lo = Num128(0)
  hi = Num128(1)
  assert lo.modpoly(hi) == Num128((1<<7) | (1<<2) | (1<<1) | (1<<0))
  #
  lo = Num128(0)
  hi = Num128(2)
  assert lo.modpoly(hi) == Num128((1<<8) | (1<<3) | (1<<2) | (1<<1))
  #
  lo = Num128(0)
  hi = Num128(3)
  assert lo.modpoly(hi) == Num128((1<<8) | (1<<7) | (1<<3) | (1<<0))
  #
  assert Num128(7).clmodmul(Num128(7)).to_long() == 21



    

def modadd(a, b):
  return [(n+m)%2 for n,m in zip(a,b)]

def modmul(a, b):
  res = (len(a)+len(b)-1)*[0]
  for n in range(len(a)):
    for m in range(len(b)):
      res[-1-n-m] = (res[-1-n-m] + a[-1-n] * b[-1-m]) % 2
  return res

def modpoly(value, poly):
  assert False # This function is erroneous
  assert len(poly) == 129
  val128 = value[-128:]
  for n in range(len(value)-128):
    if value[-128-n-1]:
      val128 = modadd(val128, poly[1+n:] + n*[0])
  return val128

def fastghash(H,A,C,v,u):
  X = Num128(0)
  for n in xrange(len(A)):
    X = X.xor(A[n])
    #print X
    #print H
    X = X.clmodmulinv(H)
    #print X
    #print "----"
  for n in xrange(len(C)):
    X = X.xor(C[n])
    X = X.clmodmulinv(H)
  lenA = 128*(len(A)-1)+v
  lenC = 128*(len(C)-1)+u
  lens = Num128(lenC, lenA)
  X = X.xor(lens)
  X = X.clmodmulinv(H)
  return X


def ghash(H,A,C,v,u):
  global poly
  X = 128*[0]
  for n in range(1, len(A)):
    X = modpoly(modmul(modadd(X, A[n-1]), H), poly)
  X = modpoly(modmul(modadd(X, A[-1]), H), poly)
  for n in range(1, len(C)):
    X = modpoly(modmul(modadd(X, C[n-1]), H), poly)
  X = modpoly(modmul(modadd(X, C[-1]), H), poly)
  lenA = 8*(len(A)-1)+v
  lenC = 8*(len(C)-1)+u
  lenAb = bin(lenA)[2:]
  lenCb = bin(lenC)[2:]
  lenAb = (64-len(lenAb))*'0'+lenAb
  lenCb = (64-len(lenCb))*'0'+lenCb
  lenAa = [x=='1' for x in lenAb]
  lenCa = [x=='1' for x in lenCb]
  lens = lenAa + lenCa
  assert len(lens) == 128
  X = modpoly(modmul(modadd(X, lens), H), poly)
  return X

def packetize128(s):
  w = (8*len(s)) % 128
  if w == 0:
    w = 128
  s += (16-(w/8))*"\x00"
  ps = []
  for b in range(0, len(s), 16):
    ps.append(Num128(bytesToLong(s[b:b+16])))
  return ps,w


def packetize(s):
  w = (8*len(s)) % 128
  if w == 0:
    w = 128
  p = []
  ps = []
  for n in range(8*len(s)):
    b = 7-(n%8)
    k = n/8
    bit = (ord(s[k]) >> b)&1
    p.append(bit)
  for n in range(128-w):
    p.append(0) # WAS: n, was buggy!
  for b in range(0, len(p), 128):
    ps.append(p[b:b+128])
  return ps,w

def longToBytes(val):
  w = long(val).bit_length()
  w = (w+7)//8 * 8
  formatString = '%%0%dx' % (w//4)
  return binascii.unhexlify(formatString % val)
def bytesToLong(val):
  return long(binascii.hexlify(val), 16)

"""
    Under this the license is the following:

    Copyright (C) 2013 Bo Zhu http://about.bozhu.me
    Copyright (C) 2018 Juha-Matti Tilli

    Permission is hereby granted, free of charge, to any person obtaining a
    copy of this software and associated documentation files (the "Software"),
    to deal in the Software without restriction, including without limitation
    the rights to use, copy, modify, merge, publish, distribute, sublicense,
    and/or sell copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
    THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
    FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
    DEALINGS IN THE SOFTWARE.
"""
if __name__ == '__main__':
    master_key = 0xfeffe9928665731c6d6a8f9467308308
    plaintext = b'\xd9\x31\x32\x25\xf8\x84\x06\xe5' + \
                b'\xa5\x59\x09\xc5\xaf\xf5\x26\x9a' + \
                b'\x86\xa7\xa9\x53\x15\x34\xf7\xda' + \
                b'\x2e\x4c\x30\x3d\x8a\x31\x8a\x72' + \
                b'\x1c\x3c\x0c\x95\x95\x68\x09\x53' + \
                b'\x2f\xcf\x0e\x24\x49\xa6\xb5\x25' + \
                b'\xb1\x6a\xed\xf5\xaa\x0d\xe6\x57' + \
                b'\xba\x63\x7b\x39'
    auth_data = b'\xfe\xed\xfa\xce\xde\xad\xbe\xef' + \
                b'\xfe\xed\xfa\xce\xde\xad\xbe\xef' + \
                b'\xab\xad\xda\xd2'
    init_value = 0xcafebabefacedbaddecaf888
    ciphertext = b'\x42\x83\x1e\xc2\x21\x77\x74\x24' + \
                 b'\x4b\x72\x21\xb7\x84\xd0\xd4\x9c' + \
                 b'\xe3\xaa\x21\x2f\x2c\x02\xa4\xe0' + \
                 b'\x35\xc1\x7e\x23\x29\xac\xa1\x2e' + \
                 b'\x21\xd5\x14\xb2\x54\x66\x93\x1c' + \
                 b'\x7d\x8f\x6a\x5a\xac\x84\xaa\x05' + \
                 b'\x1b\xa3\x0b\x39\x6a\x0a\xac\x97' + \
                 b'\x3d\x58\xe0\x91'
    auth_tag = 0x5bc94fbc3221a5db94fae95ae7121a47

    #print('plaintext:', hex(bytesToLong(plaintext)))

    t1 = time.time()

    ecb = AES.new(longToBytes(master_key), AES.MODE_ECB)

    ctr = (init_value << 32) + 1
    first = bytesToLong(ecb.encrypt(longToBytes((1<<128) + ctr)[1:]))
    auth_key = bytesToLong(ecb.encrypt(b'\x00' * 16))
    ctr += 1
    plainpackets,u = packetize128(plaintext)
    exp_cipherpackets,w = packetize128(ciphertext)
    authpackets,v = packetize128(auth_data)
    cipherpackets = []
    for plainpacket in plainpackets:
      lpp = plainpacket.to_long()
      lcp = lpp ^ bytesToLong(ecb.encrypt(longToBytes((1<<128) + ctr)[1:]))
      cipherpackets.append(Num128(lcp))
      ctr += 1
    if u != 128:
      lcp = cipherpackets[-1].to_long()
      cipherpackets[-1] = Num128(lcp & ~((1<<(128-u))-1))
    for plainpacket in plainpackets:
      lpp = plainpacket.to_long()
    for cipherpacket,exp_cipherpacket in zip(cipherpackets, exp_cipherpackets):
      lcp = cipherpacket.to_long()
      exp_lcp = exp_cipherpacket.to_long()
      #print ''.join(hex(ord(x))[2:] for x in longToBytes(lcp)),
      #print ''.join(hex(ord(x))[2:] for x in longToBytes(exp_lcp))
      assert lcp == exp_lcp
      #print "OK!"
    assert fastghash(Num128(auth_key), authpackets, cipherpackets, v, u).xor(Num128(first)).to_long() == auth_tag
    t2 = time.time()
    print "OK!"
    print (t2-t1)*1e3, "msec for encryption"
    t3 = time.time()
    unit()
    t4 = time.time()
    print (t4-t3)*1e3, "msec for unit test"

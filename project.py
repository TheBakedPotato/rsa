#!/usr/bin/python3

import random
import statistics

from time import time
from gmpy2 import gcdext, mpz, c_div
from Crypto import Random
from Crypto.Util import number, py3compat, strxor
from Crypto.Hash import SHA256
from Crypto.Signature.PKCS1_PSS import MGF1

BYTE_ORDER = "big"

def num_bytes(num):
    return c_div(num.bit_length(), 8)

def to_binary(num):
    return int(num).to_bytes(num_bytes(num), BYTE_ORDER)

def from_binary(num):
    return int.from_bytes(num, BYTE_ORDER)

def inverse(num, modulus):
    inverse = gcdext(num, modulus)[1]
    return inverse if inverse > 0 else inverse + modulus

def power(base, exp, modulus):
    val = 1
    bits = exp.bit_length()

    for i in range(bits - 1, -1, -1):
        val = (val * val) % modulus
        if exp.bit_test(i):
            val = (val * base) % modulus

    return val

class Key:
    """Key class"""
    def __init__(self, bitLength):
        p = mpz(number.getPrime(int(bitLength/2)))
        q = mpz(number.getPrime(int(bitLength/2)))
        while p == q or (not (p < q and q < 2*p) and not (q < p and p < 2*q)):
            q = mpz(number.getPrime(int(bitLength/2)))

        n = p * q
        phiN = (p - 1) * (q - 1)
        e = mpz(65537)

        d = inverse(e, phiN)

        d_p = d % (p - 1)
        d_q = d % (q - 1)
        q_inv = inverse(q, p)

        self.p = p
        self.q = q
        self.n = n
        self.e = e
        self.d = d
        self.d_p = d_p
        self.d_q = d_q
        self.q_inv = q_inv

def blinding_decrypt(cipherText, key, decrypt):
    r = number.getRandomNBitInteger(int(key.n.bit_length() / 2))
    cipherText = (cipherText * power(r, key.e, key.n)) % key.n
    return (decrypt(cipherText, key) * inverse(r, key.n)) % key.n

class Hasher:
    def __init__(self, delegate):
        self._delegate = delegate
        self.emptyHash = delegate.new("").digest()

    def length(self):
        return self._delegate.digest_size

    def mgf(self, seed, length):
        return MGF1(seed, int(length), self._delegate)

class Hashers:
    sha256 = Hasher(SHA256)

def oaep_encrypt(message, key, hasher):
    k = num_bytes(key.n)
    message = to_binary(message)
    m_len = len(message)
    h_len = hasher.length()
    lHash = hasher.emptyHash
    ps = py3compat.bchr(0x00) * (k - m_len - (2 * h_len) - 2)
    db = lHash + ps + py3compat.bchr(0x01) + message
    ros = Random.new().read(h_len)
    dbMask = hasher.mgf(ros, k - h_len - 1)
    maskedDb = strxor.strxor(db, dbMask)
    seedMask = hasher.mgf(maskedDb, h_len)
    maskedSeed = strxor.strxor(ros, seedMask)
    em = py3compat.bchr(0x00) + maskedSeed + maskedDb
    m = power(from_binary(em), key.e, key.n)
    return from_binary((py3compat.bchr(0x00) * (k - len(m))) + to_binary(m))

def oaep_decrypt(cipher, key, hasher):
    k = num_bytes(key.n)
    h_len = hasher.length()
    m = to_binary(cipher)
    em = (py3compat.bchr(0x00) * (k - len(m))) + m
    lHash = hasher.emptyHash
    y = em[0]
    maskedSeed = em[1:h_len + 1]
    maskedDb = em[h_len + 1:]
    seedMask = hasher.mgf(maskedDb, h_len)
    seed = strxor.strxor(maskedSeed, seedMask)
    dbMask = hasher.mgf(seed, (k - h_len - 1))
    db = strxor.strxor(maskedDb, dbMask)
    valid = 1
    one = db[h_len:].find(py3compat.bchr(0x01))
    lHash1 = db[:h_len]
    return from_binary(db[h_len + one + 1:])

def rand_num(bitLength):
    num = 0
    while num == 0:
        num = random.getrandbits(bitLength)
    return num

num_warm_ups = 5
num_tests = 50
msg_size = 256

keys = [ Key(2048), Key(3072) ]
message = mpz(rand_num(msg_size))

print("Message: " + str(message))
def test(encrypt, decrypt):
    for key in keys:
        print ("Key Length: " + str(key.n.bit_length()))
        for i in range(num_warm_ups):
            cipher = encrypt(message, key)
            plainText = decrypt(cipher, key)

        eTimes = []
        dTimes = []
        for i in range(num_tests):
            start = time()
            cipher = encrypt(message, key)
            stop = time()
            eTimes.append((stop - start) * 1000)
            start = time()
            plainText = decrypt(cipher, key)
            stop = time()
            dTimes.append((stop - start) * 1000)
            if plainText != message:
                print ("Trial " + str(i))
                print ("P: " + str(plainText))

        print(statistics.mean(eTimes))
        print(statistics.mean(dTimes))

def textbook_rsa_encrypt(plainText, key):
    return power(plainText, key.e, key.n)

def textbook_rsa_decrypt(cipherText, key):
    return power(cipherText, key.d, key.n)

print ("== Textbook RSA ==")
test(textbook_rsa_encrypt, textbook_rsa_decrypt)
print()

def blinding_rsa_encrypt(plainText, key):
    return power(plainText, key.e, key.n)

def blinding_rsa_decrypt(cipherText, key):
    def decrypt(cipherText, key):
        return power(cipherText, key.d, key.n)
    return blinding_decrypt(cipherText, key, decrypt)

print ("== Blinding RSA ==")
test(blinding_rsa_encrypt, blinding_rsa_decrypt)
print()

def cr_rsa_encrypt(plainText, key):
    return power(plainText, key.e, key.n)

def cr_rsa_decrypt(cipherText, key):
    m_1 = power(cipherText, key.d_p, key.p)
    m_2 = power(cipherText, key.d_q, key.q)
    h = (key.q_inv * (m_1 - m_2)) % key.p
    return (m_2 + (h * key.q)) % key.n

print ("== Chinese Remainder RSA ==")
test(cr_rsa_encrypt, cr_rsa_decrypt)
print()

def oaep_rsa_encrypt(plainText, key):
    return oaep_encrypt(plainText, key, Hashers.sha256)

def oaep_rsa_decrypt(cipherText, key):
    cipherText = power(cipherText, key.d, key.n)
    return oaep_decrypt(cipherText, key, Hashers.sha256)

print ("== OAEP RSA ==")
test(oaep_rsa_encrypt, oaep_rsa_decrypt)
print()

def rsa_encrypt(plainText, key):
    return oaep_encrypt(plainText, key, Hashers.sha256)

def rsa_decrypt(cipherText, key):
    cipherText = blinding_decrypt(cipherText, key, cr_rsa_decrypt)
    return oaep_decrypt(cipherText, key, Hashers.sha256)

print("== RSA ==")
test(rsa_encrypt, rsa_decrypt)
print()
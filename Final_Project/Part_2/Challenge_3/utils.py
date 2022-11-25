# +

import random
import math
import json
from base64 import b64encode, b64decode
from Crypto.Cipher import AES
from Crypto.Hash import HMAC, SHA256
from Crypto.Util.Padding import pad, unpad
from Crypto.Random import get_random_bytes

"""
Utility Functions
"""
def egcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)

def modularInverse(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    else:
        return x % m

def findSquareRoot(N,p):
    N = N % p
    
    if pow(N,(p-1)//2,p)==1:
        if (p%4) == 3:
            x1= pow(N,(p+1)//4, p)
            y1= p - x1
            return (x1,y1)
        else:
            for x in range(1,((p-1)//2)+1):
                if N == pow(x, 2, p):
                    return (x,p-x)
    return []



def extendedGCD(a,b):
    s_n1 = 1 # s_i-1
    s = 0 # s_i
    
    t_n1 = 0 #t_i-1
    t = 1 #t_1
    
    
    while b > 0:
        q = a // b

        s, s_n1 = s_n1 - q*s, s
        t, t_n1 = t_n1 - q*t, t
        
        a,b = b, a % b
    
    return (a, s_n1, t_n1)

egcd = extendedGCD

def millerRabinWitnessQ(a,n):
    q = n-1
    k = 0
    
    while q % 2 == 0:
        k+=1
        q //= 2
    
    i = 0
        
    b_i = pow(a, q, n)
    
    if b_i == 1 or b_i == (n-1):
        return False
    
    for i in range(k):
        if b_i == 1:
            return False
        
        b_i = pow(b_i, 2, n)

    return True

def probablyPrime(p):
    if p < 3:
        return True if (p == 1 or p == 2) else False
    
    for i in range(20):
        a = random.randrange(2, p) # randrange() returns [2, p) = [2, p-1]
        
        if millerRabinWitnessQ(a, p):
            return False
    return True

def findPrime(lBound, uBound): 
    p = random.randrange(lBound, uBound+1) 
    
    while not probablyPrime(p):
        p = random.randrange(lBound, uBound+1)
    
    return p

def int_to_bytes(x: int) -> bytes:
    return x.to_bytes((x.bit_length() + 7) // 8, 'big')

def hash_SHA256(M): # M is integer
    h = SHA256.new()
    h.update(bytes(int_to_bytes(M)))
    return int(h.hexdigest(), 16)

def getExpansion(n,m):
    arr = []
    
    while n > 0:
        r = n % m
        n //= m
        
        arr.append(r)
    
    return arr

def textToInt(s):
    total = 0
    
    for i in range(len(s)):
        total += ord(s[i])*(256**i)
    
    return total

def intToText(n):
    expansion = getExpansion(n, 256)
    
    finalStr = ""
    
    for i in range(len(expansion)):
        finalStr += chr(expansion[i])
        
    return finalStr


def bxor(b1, b2): # use xor for bytes
    result = bytearray()
    for b1, b2 in zip(b1, b2):
        result.append(b1 ^ b2)
    return result

def getRandomBytes(n):
    return get_random_bytes(n)

"""
Elliptic Curve Functions
"""

def evaluateP(x, E, p):
    evaled = ((pow(x, 3, p) + E[0]*x + E[1])%p)
    
    if evaled == 0:
        return [0]
    
    return findSquareRoot(evaled, p)

def pointOnCurve(P,E,p):
    assert isElliptic(E, p), "Invalid elliptic curve (has zero discriminant)"
    
    if P[0] == 'O':
        return True
    
    evaled = evaluateP(P[0], E, p)
    
    if len(evaled) == 0:
        return False
    
    return (evaled[0]%p == P[1]) or (evaled[1]%p == P[1])

def isElliptic(E, p):
    """
    Takes in curve E as [A, B] and modulo p. 
    Returns whether the discriminant of E is nonzero.
    """
    
    # Make sure to do this modulo p.
    discriminant = (4 * pow(E[0], 3, p) + 27 * pow(E[1], 2, p)) % p 
    
    return discriminant != 0 

def addPoints(P,Q,E,p):
    """
    Given points P,Q of the form (x,y), curve E of the form [A,B], and prime p, find P + Q.
    """
    
    assert isElliptic(E, p), "Invalid elliptic curve (has zero discriminant)"
    assert pointOnCurve(P, E, p), "Point P is not on the elliptic curve"
    assert pointOnCurve(Q, E, p), "Point Q is not on the elliptic curve"

    multi = 1 # Lambda

    if P == 'O': # If P is the point at infinity
        return Q 
    elif Q == 'O': # If Q is the point at infinity
        return P 
    elif P[0] == Q[0] and P[1] == (-Q[1] % p): # If P and Q are on a vertical line (share the same x-coord)
        return 'O' 
    elif P[0] == Q[0]: # If P = Q
        multi = ((3*pow(P[0], 2, p) + E[0])*modularInverse(2*P[1], p)) % p # Set lambda
    else: 
        multi = ((Q[1] - P[1])*modularInverse((Q[0] - P[0])%p, p))%p # Set lambda

    x_3 = (pow(multi, 2, p) - P[0] - Q[0]) % p 
    y_3 = (multi*(P[0] - x_3) - P[1]) % p 

    return (x_3, y_3)

def messageToPoint(m, E, p, K=100):
    """
    Koblitz's algorithm for finding a point for a given number (plaintext, m). Uses tolerance K=100 by default.
    
    Returns a point if found, otherwise None.
    """
    
    for j in range(K):
        square_roots = evaluateP(m*K + j, E, p)
        
        if square_roots == 0:
            return (m*K + j, 0)
        elif len(square_roots) == 2:
            return (m*K + j, square_roots[0])
        
    return None # Failure case

def pointToMessage(P, K=100):
    """
    Returns the message corresponding to point P.
    """
    
    return P[0]//K

def doubleAndAdd(P,n,E,p):
    assert isElliptic(E, p), "Invalid elliptic curve (has zero discriminant)"
    assert pointOnCurve(P, E, p), "Point P is not on the elliptic curve"
    
    point = P
    finalPoint = 'O'
        
    # What this while loop does is iteratively find the binary representation
    # starting from the least significant bit. It is faster than finding the representation first.
    while n > 0:
        r = n % 2
        n //= 2
        
        if r == 1: # Checks if this binary bit is 1
            # If the bit is one, add the current power of two point to the finalPoint
            finalPoint = addPoints(finalPoint, point, E, p) 
        
        # Double the current power of two point to the next power of two
        point = addPoints(point, point, E, p) 
    
    return finalPoint

def generateEllipticKeypair(P, q, E, p):
    assert pointOnCurve(P, E, p), "Generator point P is not on the given curve"
    
    secret = random.randrange(2,q)
    
    V = doubleAndAdd(P, secret, E, p)
    
    return secret, V

def generateECDH(generatorPoint, E, p, N):
    
    n = random.randrange(2, 50)

    nP = doubleAndAdd(generatorPoint, n, E, p)
    
    return nP, n

def combineECDH(publicPoint, k, E, p):
    """
    Takes in point publicPoint, secret k, the curve E, and prime p. 
    publicPoint can be either Bob's public or Alice's public key (aP, bP),
    and k is the opposite person's private key (n).
    Returns the shared secret (ab)P.
    """
    
    return doubleAndAdd(publicPoint, k, E, p)


"""
Hashing/MAC Functions
"""

def generateHMAC(key, data):
    if type(key) == int:
        key = key.to_bytes(32, byteorder='big')

    h = HMAC.new(key, digestmod=SHA256)

    h.update(data)

    return h.hexdigest()

def verifyHMAC(key, data, hmac):
    if type(key) == int:
        key = key.to_bytes(32, byteorder='big')

    h = HMAC.new(key, digestmod=SHA256)

    h.update(data)

    try:
        h.hexverify(hmac)
        return True
    except:
        return False

"""
Symmetric Encryption Functions
"""
def encryptAES(key, data):
    if type(key) == int:
        key = key.to_bytes(32, byteorder='big')
    
    assert len(key) == 16 or len(key) == 24 or len(key) == 32, "Invalid keysize"
    
    iv = get_random_bytes(16)
    
    paddedData = pad(data, AES.block_size)
    
    cipher = AES.new(key, AES.MODE_CBC, iv=iv)
    
    encrypted = cipher.encrypt(paddedData)

    iv = b64encode(cipher.iv).decode('utf-8')

    ct = b64encode(encrypted).decode('utf-8')

    return json.dumps({'iv':iv, 'ciphertext':ct})

def decryptAES(key, encrypted):
    if type(key) == int:
        key = key.to_bytes(32, byteorder='big')
    
    assert len(key) == 16 or len(key) == 24 or len(key) == 32, "Invalid keysize"
    
    try:
        b64 = json.loads(encrypted)
        iv = b64decode(b64['iv'])
        ct = b64decode(b64['ciphertext'])
        
        cipher = AES.new(key, AES.MODE_CBC, iv)

        return unpad(cipher.decrypt(ct), AES.block_size)
        
    except (ValueError, KeyError):
        raise AssertionError("Invalid ciphertext")
        

"""
Asymmetric Encryption Functions
"""

def generateRSAKeypair(b):
    p = findPrime(2, 2**(b//2) -1)
    q = findPrime(2, 2**(b//2) -1)
    
    while p == q:
        q = findPrime(2, 2**(b//2) -1) # ensure P!=q
    
    N = p*q
    
    e = 65537
    
    while math.gcd(e, (p-1)*(q-1)) != 1:
        e += 2 # Since e must be odd for gcd(e, p-1 * q-1) = 1, we start at 65537 and inc by 2 each time
    d = modularInverse(e, (p-1)*(q-1))
    
    return (e, N, d)

# Doesnt use padding
def encryptRSA(message, e, N):
    return pow(message, e, N)

def decryptRSA(encrypted, d, N):
    return pow(encrypted, d, N)

# Finds H(M)^d mod N.
def signRSA(d, M, N):
    assert type(d) == int, "Private key must be an integer"
    assert type(M) == int, "Message must be an integer"
    assert type(N) == int, "Modulus must be an integer"
    
    return pow(hash_SHA256(M%N)%N, d, N)

# Finds S^e mod N and compares it to H(M).
def verifyRSA(e, S, N, M):
    assert type(e) == int, "Public exponent must be an integer"
    assert type(S) == int, "Signature must be an integer"
    assert type(M) == int, "Message must be an integer"
    assert type(N) == int, "Modulus must be an integer"
    
    return pow(S, e, N) == (hash_SHA256(M%N))%N
    

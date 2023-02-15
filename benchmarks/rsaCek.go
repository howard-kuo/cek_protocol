package main

import (
	"crypto/rand"
	"errors"
	"fmt"
	"io"
	"time"
	"github.com/ncw/gmp"
)


func main() {
	fmt.Println("Start")

	privKey:= KeyGen(gmp.NewInt(2), gmp.NewInt(128))

	start := time.Now()

	for i := 0; i < 10; i++ {
		if i % 20 == 0 {
			fmt.Println(i)
		}
		privKey = kg2()
	}
	
	t := time.Now()
	eclapse := t.Sub(start)




	fmt.Println("keygen complete...", eclapse)
	fmt.Println("   ", privKey.p.BitLen())


/*
	// set initial ciphertext
	var result bool
	cZero := make([]*gmp.Int, 32)

	for i := 0; i < 32; i++ {
		cZero[i] = Encrypt(gmpZer, &privKey.PublicKey)
	}
*/

}
// *****************************************************************
// *                                                               *
// *                        DGK Comparison                         *
// *                                                               *
// *****************************************************************

func dgk2(valA, valB, bCount int, cZeros []*gmp.Int, privKey *PrivateKey) bool {
	
	var cA = make([]*gmp.Int, bCount) 
	var pubKey = &privKey.PublicKey

	
	// Alice computes [[a_i]]
	for i := 0; i < bCount; i++ {
		if valA>>uint64(i)&0x01 == 0 {
			cA[i] = PAdd(cZeros[i], gmpZer, pubKey) 

		} else {
			cA[i] = PAdd(cZeros[i], gmpOne, pubKey) 
		}
	}


	// compute xor array
	cXor := make([]*gmp.Int, bCount)
	cNegA := make([]*gmp.Int, bCount)

	for i := 0; i < bCount; i++ {
		cNegA[i] = Neg(cA[i], pubKey)

		if valB>>uint64(i)&0x01 == 0 {
			cXor[i] = cA[i]

		} else {
			cXor[i] = PAdd(cNegA[i], gmpOne, pubKey)
		}

	}

	//
	cResult := make([]*gmp.Int, bCount)
	upperNz := PAdd(cA[31], gmpZer, pubKey)
	for i := 0; i < bCount; i++ {
		cur := bCount - i - 1
		if valB>>uint64(cur)&0x01 == 0 {
			cResult[cur] = cNegA[cur]

		} else {
			cResult[cur] = PAdd(cNegA[cur], gmpOne, pubKey)
		}
		cResult[cur] = PAdd(cResult[cur], gmpOne, pubKey)

		cResult[cur] = Add(cResult[cur], upperNz, pubKey)

		rd, _ := randInt(rand.Reader, gmp.NewInt(96))
		rd.Add(rd, gmpOne)

		cResult[cur] = PMul(cResult[cur], rd, pubKey)

		tmp := PMul(cXor[cur], gmpThr, pubKey)
		upperNz = Add(upperNz, tmp, pubKey)
	}

	result := false
	for i := 0; i < bCount; i++ {
		plain := Decrypt(cResult[i], privKey)
		k := gmpOne.Cmp(plain)
		if k == 0 {
			result = true
		}
	}

	return result
}

// *****************************************************************
// *                                                               *
// *                             Struct                            *
// *                                                               *
// *****************************************************************

// Construction of CEK RSA scheme

// PrivateKey contains the factorization on multriplication of Z^*_n
type PrivateKey struct {
	PublicKey
	p				*gmp.Int
	q				*gmp.Int
	ps				*gmp.Int
	pt				*gmp.Int
	qs				*gmp.Int
	qt				*gmp.Int
	b				*gmp.Int
	d  				*gmp.Int
	od				*gmp.Int
}
// PublicKey contains modulus n, message generator g, and randomizer h
type PublicKey struct {
	G				*gmp.Int
	H				*gmp.Int
	N				*gmp.Int
	b				*gmp.Int
	d  				*gmp.Int
	od				*gmp.Int
}


// *****************************************************************
// *                                                               *
// *                              Key Gen                          *
// *                                                               *
// *****************************************************************
func kg2() (*PrivateKey) {
	p,_ := randPrime(rand.Reader, 1536)
	q,_ := randPrime(rand.Reader, 1536)
	return &PrivateKey{
		PublicKey: PublicKey{
			G:        	gmpOne,
			H:        	gmpOne,
			N:        	new(gmp.Int).Mul(p,q), 
			b:        	gmpOne,
			d:        	gmpOne,
			od:      	gmpOne,
		},
		p:			p,	
		q:			q,	
		ps:			gmpOne,	
		pt:			gmpOne,	
		qs:			gmpOne,	
		qt:			gmpOne,
		b:			gmpOne,	
		d:			gmpOne,  	
		od:			gmpOne,			
	}
}
// KeyGen return a private Key with plaintext space Z^*_b**d
func KeyGen(b, d *gmp.Int) (*PrivateKey) {
	od := new(gmp.Int).Exp(b, d, new(gmp.Int).SetUint64(^uint64(0)))
	ps, pt, p, _ := specialPrime(rand.Reader, 1536, od)
	qs, qt, q, _ := specialPrime(rand.Reader, 1536, od)
	g := MakeG(b, d, p, q)
	h := MakeH(ps, qs, p, q)
	n := new(gmp.Int).Mul(p,q)

	return &PrivateKey{
		PublicKey: PublicKey{
			G:        	g,
			H:        	h,
			N:        	n, 
			b:        	b,
			d:        	d,
			od:      	od,
		},
		p:			p,	
		q:			q,	
		ps:			ps,	
		pt:			pt,	
		qs:			qs,	
		qt:			qt,
		b:			b,	
		d:			d,  	
		od:			od,			
	}
}

// MakeG : Returns a gmp Int, say g, such that |gp|=|gq|=b**d for some prime b
func MakeG(b, d, p, q *gmp.Int) (*gmp.Int){
	pminusone := new(gmp.Int).Sub(p, gmpOne)
	qminusone := new(gmp.Int).Sub(q, gmpOne)

	pr := new(gmp.Int).Div(pminusone, b)

	qr := new(gmp.Int).Div(qminusone, b)
	gp := new(gmp.Int)
	gq := new(gmp.Int)

	for {
		x, _ := randInt(rand.Reader, pminusone)
		y := new(gmp.Int).Exp(x, pr, p)

		// if y = 1, then x^(c*b**(d-1)) = 1 is not desirable 
		if y.Cmp(gmpOne) != 0 {
			od := new(gmp.Int).Exp(b, d, p)
			pr.Div(pminusone, od)
			gp.Exp(x, pr, p)
			break
		}
	}

	for {
		x, _ := randInt(rand.Reader, pminusone)
		y := new(gmp.Int).Exp(x, qr, q)

		// if y = 1, then x^(c*b**(d-1)) = 1 is not desirable 
		if y.Cmp(gmpOne) != 0 {
			od := new(gmp.Int).Exp(b, d, q)
			qr.Div(qminusone, od)
			gq.Exp(x, qr, q)
			break
		}
	}

	g := crt(gp, gq, p, q)
	return g
}

// MakeH : Input(ps,qs,p,q) -> Returns a gmp Int, say h, such that |hp|=ps, |hq|=qs
func MakeH(ps, qs, p, q *gmp.Int) (*gmp.Int){
	pminusone := new(gmp.Int).Sub(p, gmpOne)
	qminusone := new(gmp.Int).Sub(q, gmpOne)
	
	pr := new(gmp.Int).Div(pminusone, ps)


	qr := new(gmp.Int).Div(qminusone, qs)



	hp := new(gmp.Int)
	hq := new(gmp.Int)

	for {
		x, _ := randInt(rand.Reader, pminusone)
		x.Exp(x,pr,p)
		if x.Cmp(gmpOne) != 0 {
			hp = x
			break
		}
	}

	for {
		x, _ := randInt(rand.Reader, qminusone)
		x.Exp(x,qr,q)
		if x.Cmp(gmpOne) != 0 {
			hq = x
			break
		}
	}

	h := crt(hp, hq, p, q)
	return h
}


// *****************************************************************
// *                                                               *
// *                   Encryption and Decryption                   *
// *                                                               *
// *****************************************************************

// Encrypt : Input (message, public key) -> Return (c = g**m * h**r)
func Encrypt(m *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	// bb =2^256
	bb := make([]byte, 33)
	bb[0] |= 1
	r, _ := randInt(rand.Reader, new(gmp.Int).SetBytes(bb))
	r.Exp(pubKey.H, r, pubKey.N)
	gm := new(gmp.Int).Exp(pubKey.G, m, pubKey.N)
	return gm
}

// Decrypt : Input (encrypted, private key) -> Return (m = c^ps mod p)
func Decrypt(c *gmp.Int, privKey *PrivateKey) (*gmp.Int) {
	m := new(gmp.Int).Exp(c, privKey.ps, privKey.p)
	return m
}

// DLog : Input : (message, PrivateKey) -> Return (i) s.t. g**(i*ps) = message. Perform super slow discrete log to decode a message
func DLog(m *gmp.Int, privKey *PrivateKey) (int) {
	var t = gmp.NewInt(1)
	var v = int(new(gmp.Int).ModInverse(privKey.ps, privKey.od).Uint64())
	for i := 0; i < 257; i++{
		if m.Cmp(t) == 0 {
			return (i * v) % int(privKey.od.Uint64())
		}
		t.Mul(t, privKey.PublicKey.G)
		t.Mod(t, privKey.p)
	}
	return -1
}

// *****************************************************************
// *                                                               *
// *                           Evaluations                         *
// *                                                               *
// *****************************************************************


// PMul : Input (c, p, pubKey) -> Return (c**p)
func PMul(c, p *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	return new(gmp.Int).Exp(c, p, pubKey.N)
}

// PAdd : Input (c, p, pubKey) -> Return (c*(g**p))
func PAdd(c, p *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	ge := new(gmp.Int).Exp(pubKey.G, p, pubKey.N)
	return ge.Mul(c,ge)
}

// Add : Input (c1, c2, pubKey) -> Return (c1*c2)
func Add(c1, c2 *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	cmul := new(gmp.Int).Mul(c1,c2)
	return cmul.Mod(cmul, pubKey.N)
}

// Flip : return Enc(1 - m)
func Flip(c *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	f := Neg(c, pubKey)
	f = PAdd(f, gmpOne, pubKey)
	return f
}

// Neg : return a ciphertext which is a encrypted of m inverse
func Neg(c *gmp.Int, pubKey *PublicKey) (*gmp.Int) {
	cinv :=  new(gmp.Int).ModInverse(c, pubKey.N)
	return cinv
}

// *****************************************************************
// *                                                               *
// *                             Global                            *
// *                                                               *
// *****************************************************************


var gmpZer = gmp.NewInt(0)
var gmpOne = gmp.NewInt(1)
var gmpTwo = gmp.NewInt(2)
var gmpThr = gmp.NewInt(3)


// *****************************************************************
// *                                                               *
// *                             RANDOM                            *
// *                                                               *
// *****************************************************************

// smallPrimes is a list of small, prime numbers that allows us to rapidly

// exclude some fraction of composite candidates when searching for a random

// prime. This list is truncated at the point where smallPrimesProduct exceeds

// a uint64. It does not include two because we ensure that the candidates are

// odd by construction.

var smallPrimes = []uint8{

	3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
}

// smallPrimesProduct is the product of the values in smallPrimes and allows us

// to reduce a candidate prime by this number and then determine whether it's

// coprime to all the elements of smallPrimes without further big.Int

// operations.

var smallPrimesProduct = new(gmp.Int).SetUint64(16294579238595022365)

// Prime returns a number, p, of the given size, such that p is prime

// with high probability.

// Prime will return error for any error returned by rand.Read or if bits < 2.
func randPrime(rand io.Reader, bits int) (p *gmp.Int, err error) {

	if bits < 2 {

		err = errors.New("crypto/rand: prime size must be at least 2-bit")

		return

	}

	b := uint(bits % 8)

	if b == 0 {

		b = 8

	}

	bytes := make([]byte, (bits+7)/8)

	p = new(gmp.Int)

	bigMod := new(gmp.Int)

	for {

		_, err = io.ReadFull(rand, bytes)

		if err != nil {

			return nil, err

		}

		// Clear bits in the first byte to make sure the candidate has a size <= bits.

		bytes[0] &= uint8(int(1<<b) - 1)

		// Don't let the value be too small, i.e, set the most significant two bits.

		// Setting the top two bits, rather than just the top bit,

		// means that when two of these values are multiplied together,

		// the result isn't ever one bit short.

		if b >= 2 {

			bytes[0] |= 3 << (b - 2)

		} else {

			// Here b==1, because b cannot be zero.

			bytes[0] |= 1

			if len(bytes) > 1 {

				bytes[1] |= 0x80

			}

		}

		// Make the value odd since an even number this large certainly isn't prime.

		bytes[len(bytes)-1] |= 1

		p.SetBytes(bytes)

		// Calculate the value mod the product of smallPrimes. If it's

		// a multiple of any of these primes we add two until it isn't.

		// The probability of overflowing is minimal and can be ignored

		// because we still perform Miller-Rabin tests on the result.

		bigMod.Mod(p, smallPrimesProduct)

		mod := bigMod.Uint64()

	NextDelta:

		for delta := uint64(0); delta < 1<<20; delta += 2 {

			m := mod + delta

			for _, prime := range smallPrimes {

				if m%uint64(prime) == 0 && (bits > 6 || m != uint64(prime)) {

					continue NextDelta

				}

			}

			if delta > 0 {

				bigMod.SetUint64(delta)

				p.Add(p, bigMod)

			}

			break

		}

		// There is a tiny possibility that, by adding delta, we caused

		// the number to be one bit too long. Thus we check BitLen

		// here.
		if p.ProbablyPrime(20) && p.BitLen() == bits {

			return

		}

	}
}

// p = 2 * q * ps * pt + 1
// specialPrime will return error for any error returned by rand.Read or if bits < 2.
func specialPrime(rand io.Reader, bits int, q *gmp.Int) (ps *gmp.Int, pt *gmp.Int,  p *gmp.Int, err error) {

	pt, err = randPrime(rand, bits - 256 - q.BitLen())

	qd2 := new(gmp.Int).Mul(q, gmp.NewInt(2))

	for i := 0; i < 2<<20; i++ {
		ps, err := randPrime(rand, 256)

		if err != nil {

			return nil, nil, nil, err

		}

		if err != nil {

			return nil, nil, nil, err

		}

		p := new(gmp.Int).Mul(ps, pt)
		p.Mul(p, qd2)
		p.Add(p, gmpOne)

		//a := new(gmp.Int).Rem(p, gmp.NewInt(2))
		//fmt.Println(a.Bytes())

		if p.ProbablyPrime(20) {

			return ps, pt, p, nil

		}
	}

	return nil, nil, nil, err
}

// Int returns a uniform random value in [0, max). It panics if max <= 0.
func randInt(rand io.Reader, max *gmp.Int) (n *gmp.Int, err error) {

	if max.Sign() <= 0 {

		panic("crypto/rand: argument to Int is <= 0")

	}

	n = new(gmp.Int)

	n.Sub(max, n.SetUint64(1))

	// bitLen is the maximum bit length needed to encode a value < max.

	bitLen := n.BitLen()

	if bitLen == 0 {

		// the only valid result is 0

		return

	}

	// k is the maximum byte length needed to encode a value < max.

	k := (bitLen + 7) / 8

	// b is the number of bits in the most significant byte of max-1.

	b := uint(bitLen % 8)

	if b == 0 {

		b = 8

	}

	bytes := make([]byte, k)

	for {

		_, err = io.ReadFull(rand, bytes)

		if err != nil {

			return nil, err

		}

		// Clear bits in the first byte to increase the probability

		// that the candidate is < max.

		bytes[0] &= uint8(int(1<<b) - 1)

		n.SetBytes(bytes)

		if n.Cmp(max) < 0 {

			return

		}

	}

}


// *****************************************************************
// *                                                               *
// *                              BASIC                            *
// *                                                               *
// *****************************************************************

func crt(mp, mq, p, q *gmp.Int) *gmp.Int {
	n := new(gmp.Int).Mul(p, q)
	pinvq := new(gmp.Int).ModInverse(p, q)
	u := new(gmp.Int).Mod(new(gmp.Int).Mul(new(gmp.Int).Sub(mq, mp), pinvq), q)
	m := new(gmp.Int).Add(mp, new(gmp.Int).Mul(u, p))
	return new(gmp.Int).Mod(m, n)
}
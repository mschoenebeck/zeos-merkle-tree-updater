#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <cstring>

#include <emscripten.h>
#include <sinsemilla_s.h>


#include <emscripten/bind.h>
#include <emscripten/val.h>
using namespace emscripten;

typedef __int128 int128_t;
typedef unsigned __int128 uint128_t;

// helper from zeos-bellman/inc/groth16/bls12_381/util.hpp needed by Scalar
// also used for halo2 fp operations
/// Compute a + b + carry, returning the result and the new carry over.
tuple<uint64_t, uint64_t> adc(uint64_t a, uint64_t b, uint64_t carry)
{
    uint128_t ret = (uint128_t)a + (uint128_t)b + (uint128_t)carry;
    return tuple<uint64_t, uint64_t>{(uint64_t)ret, (uint64_t)(ret >> 64)};
}
/// Compute a - (b + borrow), returning the result and the new borrow.
tuple<uint64_t, uint64_t> sbb(uint64_t a, uint64_t b, uint64_t borrow)
{
    uint128_t ret = (uint128_t)a - ((uint128_t)b + (uint128_t)(borrow >> 63));
    return tuple<uint64_t, uint64_t>{(uint64_t)ret, (uint64_t)(ret >> 64)};
}
/// Compute a + (b * c) + carry, returning the result and the new carry over.
tuple<uint64_t, uint64_t> mac(uint64_t a, uint64_t b, uint64_t c, uint64_t carry)
{
    uint128_t ret = (uint128_t)a + ((uint128_t)b * (uint128_t)c) + (uint128_t)carry;
    return tuple<uint64_t, uint64_t>{(uint64_t)ret, (uint64_t)(ret >> 64)};
}

class Fp
{
    public:

    /// INV = -(p^{-1} mod 2^64) mod 2^64
    static const uint64_t INV;
    /// p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
    static const Fp MODULUS;
    /// R = 2^256 mod p
    static const Fp R;
    /// R^2 = 2^512 mod p
    static const Fp R2;

    // members
    array<uint64_t, 4UL> data;

    Fp() : data({0, 0, 0, 0})
    {
    }
    Fp(const array<uint64_t, 4UL>& data) : data(data)
    {
    }

    static Fp zero()
    {
        return Fp({0, 0, 0, 0});
    }
    static Fp one()
    {
        return R;
    }

    static Fp from_raw(const array<uint64_t, 4UL>& v)
    {
        return Fp(v).mul(R2);
    }
    static Fp from_raw(const uint64_t& d0, const uint64_t& d1, const uint64_t& d2, const uint64_t& d3)
    {
        return Fp({d0, d1, d2, d3}).mul(R2);
    }
    static Fp from_bool(const bool& bit)
    {
        return bit ? Fp::one() : Fp::zero();
    }
    static Fp from_u64(const uint64_t& val)
    {
        return Fp({val, 0, 0, 0}) * R2;
    }

    Fp square() const
    {
        uint64_t _, r0, r1, r2, r3, r4, r5, r6, r7, carry;
        tie(r1, carry) = mac(0, this->data[0], this->data[1], 0);
        tie(r2, carry) = mac(0, this->data[0], this->data[2], carry);
        tie(r3, r4)    = mac(0, this->data[0], this->data[3], carry);

        tie(r3, carry) = mac(r3, this->data[1], this->data[2], 0);
        tie(r4, r5)    = mac(r4, this->data[1], this->data[3], carry);

        tie(r5, r6)    = mac(r5, this->data[2], this->data[3], 0);

        r7 = r6 >> 63;
        r6 = (r6 << 1) | (r5 >> 63);
        r5 = (r5 << 1) | (r4 >> 63);
        r4 = (r4 << 1) | (r3 >> 63);
        r3 = (r3 << 1) | (r2 >> 63);
        r2 = (r2 << 1) | (r1 >> 63);
        r1 = r1 << 1;

        tie(r0, carry) = mac(0, this->data[0], this->data[0], 0);
        tie(r1, carry) = adc(0, r1, carry);
        tie(r2, carry) = mac(r2, this->data[1], this->data[1], carry);
        tie(r3, carry) = adc(0, r3, carry);
        tie(r4, carry) = mac(r4, this->data[2], this->data[2], carry);
        tie(r5, carry) = adc(0, r5, carry);
        tie(r6, carry) = mac(r6, this->data[3], this->data[3], carry);
        tie(r7, _)     = adc(0, r7, carry);

        return montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7);
    }
    Fp add(const Fp& rhs) const
    {
        uint64_t _, d0, d1, d2, d3, borrow, carry;
        tie(d0, carry) = adc(this->data[0], rhs.data[0], 0);
        tie(d1, carry) = adc(this->data[1], rhs.data[1], carry);
        tie(d2, carry) = adc(this->data[2], rhs.data[2], carry);
        tie(d3, _)     = adc(this->data[3], rhs.data[3], carry);

        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        return Fp({d0, d1, d2, d3}).sub(MODULUS);
    }
    Fp sub(const Fp& rhs) const
    {
        uint64_t _, d0, d1, d2, d3, borrow, carry;
        tie(d0, borrow) = sbb(this->data[0], rhs.data[0], 0);
        tie(d1, borrow) = sbb(this->data[1], rhs.data[1], borrow);
        tie(d2, borrow) = sbb(this->data[2], rhs.data[2], borrow);
        tie(d3, borrow) = sbb(this->data[3], rhs.data[3], borrow);

        // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
        // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
        tie(d0, carry) = adc(d0, MODULUS.data[0] & borrow, 0);
        tie(d1, carry) = adc(d1, MODULUS.data[1] & borrow, carry);
        tie(d2, carry) = adc(d2, MODULUS.data[2] & borrow, carry);
        tie(d3, _)     = adc(d3, MODULUS.data[3] & borrow, carry);

        return Fp({d0, d1, d2, d3});
    }
    Fp mul(const Fp& rhs) const
    {
        // Schoolbook multiplication
        uint64_t r0, r1, r2, r3, r4, r5, r6, r7, carry;
        tie(r0, carry) = mac(0, this->data[0], rhs.data[0], 0);
        tie(r1, carry) = mac(0, this->data[0], rhs.data[1], carry);
        tie(r2, carry) = mac(0, this->data[0], rhs.data[2], carry);
        tie(r3, r4)    = mac(0, this->data[0], rhs.data[3], carry);

        tie(r1, carry) = mac(r1, this->data[1], rhs.data[0], 0);
        tie(r2, carry) = mac(r2, this->data[1], rhs.data[1], carry);
        tie(r3, carry) = mac(r3, this->data[1], rhs.data[2], carry);
        tie(r4, r5)    = mac(r4, this->data[1], rhs.data[3], carry);

        tie(r2, carry) = mac(r2, this->data[2], rhs.data[0], 0);
        tie(r3, carry) = mac(r3, this->data[2], rhs.data[1], carry);
        tie(r4, carry) = mac(r4, this->data[2], rhs.data[2], carry);
        tie(r5, r6)    = mac(r5, this->data[2], rhs.data[3], carry);

        tie(r3, carry) = mac(r3, this->data[3], rhs.data[0], 0);
        tie(r4, carry) = mac(r4, this->data[3], rhs.data[1], carry);
        tie(r5, carry) = mac(r5, this->data[3], rhs.data[2], carry);
        tie(r6, r7)    = mac(r6, this->data[3], rhs.data[3], carry);

        return Fp::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7);
    }
    Fp montgomery_reduce(const uint64_t& r0,
                         const uint64_t& r1,
                         const uint64_t& r2,
                         const uint64_t& r3,
                         const uint64_t& r4,
                         const uint64_t& r5,
                         const uint64_t& r6,
                         const uint64_t& r7) const
    {
        // The Montgomery reduction here is based on Algorithm 14.32 in
        // Handbook of Applied Cryptography
        // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

        uint64_t _, rr0 = r0, rr1 = r1, rr2 = r2, rr3 = r3, rr4 = r4, rr5 = r5, rr6 = r6, rr7 = r7, carry, carry2;
        uint64_t k = rr0 * INV;
        tie(_,   carry) = mac(rr0, k, MODULUS.data[0], 0);
        tie(rr1, carry) = mac(rr1, k, MODULUS.data[1], carry);
        tie(rr2, carry) = mac(rr2, k, MODULUS.data[2], carry);
        tie(rr3, carry) = mac(rr3, k, MODULUS.data[3], carry);
        tie(rr4, carry2) = adc(rr4, 0, carry);

        k = rr1 * INV;
        tie(_,   carry) = mac(rr1, k, MODULUS.data[0], 0);
        tie(rr2, carry) = mac(rr2, k, MODULUS.data[1], carry);
        tie(rr3, carry) = mac(rr3, k, MODULUS.data[2], carry);
        tie(rr4, carry) = mac(rr4, k, MODULUS.data[3], carry);
        tie(rr5, carry2) = adc(rr5, carry2, carry);

        k = rr2 * INV;
        tie(_,   carry) = mac(rr2, k, MODULUS.data[0], 0);
        tie(rr3, carry) = mac(rr3, k, MODULUS.data[1], carry);
        tie(rr4, carry) = mac(rr4, k, MODULUS.data[2], carry);
        tie(rr5, carry) = mac(rr5, k, MODULUS.data[3], carry);
        tie(rr6, carry2) = adc(rr6, carry2, carry);

        k = rr3 * INV;
        tie(_,   carry) = mac(rr3, k, MODULUS.data[0], 0);
        tie(rr4, carry) = mac(rr4, k, MODULUS.data[1], carry);
        tie(rr5, carry) = mac(rr5, k, MODULUS.data[2], carry);
        tie(rr6, carry) = mac(rr6, k, MODULUS.data[3], carry);
        tie(rr7, _) = adc(rr7, carry2, carry);

        // Result may be within MODULUS of the correct value
        return (Fp({rr4, rr5, rr6, rr7})).sub(MODULUS);
    };

    Fp operator + (const Fp& rhs) const
    {
        return this->add(rhs);
    }
    Fp operator - (const Fp& rhs) const
    {
        return this->sub(rhs);
    }
    Fp operator * (const Fp& rhs) const
    {
        return this->mul(rhs);
    }
    bool operator== (const Fp &rhs) const
    {
        return this->data[0] == rhs.data[0] &&
               this->data[1] == rhs.data[1] &&
               this->data[2] == rhs.data[2] &&
               this->data[3] == rhs.data[3];
    }
    bool is_zero() const
    {
        return *this == Fp::zero();
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    Fp invert() const
    {
        return this->pow_vartime<4>({
            0x992d30ecffffffff,
            0x224698fc094cf91b,
            0x0,
            0x4000000000000000,
        });
    }

    template<size_t n> Fp pow_vartime(const array<uint64_t, n> exp) const
    {
        Fp res = Fp::one();
        bool found_one = false;
        for(int e = n-1; e >= 0; e--)
        {
            for(int i = 63; i >= 0; i--)
            {
                if(found_one)
                {
                    res = res.square();
                }

                if(((exp[e] >> i) & 1) == 1)
                {
                    found_one = true;
                    res = res * *this;
                }
            }
        }
        return res;
    }
};

/// INV = -(p^{-1} mod 2^64) mod 2^64
const uint64_t Fp::INV = 0x992d30ecffffffff;
// R = 2^256 mod p
const Fp Fp::R = Fp({
    0x34786d38fffffffd,
    0x992c350be41914ad,
    0xffffffffffffffff,
    0x3fffffffffffffff,
});
// R2 = R^2 = 2^512 mod p
const Fp Fp::R2 = Fp({
    0x8c78ecb30000000f,
    0xd7d30dbd8b0de0e7,
    0x7797a99bc3c95d18,
    0x096d41af7b9cb714,
});
// p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
const Fp Fp::MODULUS = Fp({
    0x992d30ed00000001,
    0x224698fc094cf91b,
    0x0000000000000000,
    0x4000000000000000,
});

class Ep;

class EpAffine
{
    public:

    Fp x;
    Fp y;

    EpAffine() : x(Fp::zero()), y(Fp::zero())
    {
    }

    EpAffine(const Fp& x, const Fp& y) : x(x), y(y)
    {
    }

    static EpAffine identity()
    {
        return EpAffine();
    }

    bool is_identity() const
    {
        return this->x.is_zero() && this->y.is_zero();
    }

    Ep to_curve() const;
};

class Ep
{
    public:

    /// HashDomain Q for Sinsemilla hash function. This constant is created from the
    /// initializer string halo2_gadgets::sinsemilla::primitives::Q_PERSONALIZATION = "z.cash:SinsemillaQ"
    /// see primitives.rs: line 129
    static const Ep Q;

    Fp x;
    Fp y;
    Fp z;

    Ep() : x(Fp::zero()), y(Fp::zero()), z(Fp::zero())
    {
    }

    Ep(const Fp& x, const Fp& y, const Fp& z) : x(x), y(y), z(z)
    {
    }

    static Ep identity()
    {
        return Ep();
    }

    bool is_identity() const
    {
        return this->z.is_zero();
    }

    // rename 'double()' to 'dbl()' to avoid name conflict with primitive c++ type
    Ep dbl() const
    {
        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        //
        // There are no points of order 2.

        if(this->is_identity())
        {
            return Ep::identity();
        }

        Fp a = this->x.square();
        Fp b = this->y.square();
        Fp c = b.square();
        Fp d = this->x + b;
           d = d.square();
           d = d - a - c;
           d = d + d;
        Fp e = a + a + a;
        Fp f = e.square();
        Fp z3 = this->z * this->y;
           z3 = z3 + z3;
        Fp x3 = f - (d + d);
           c = c + c;
           c = c + c;
           c = c + c;
        Fp y3 = e * (d - x3) - c;

        return Ep(x3, y3, z3);
    }
    Ep add(const Ep& rhs) const
    {
        if(this->is_identity())
        {
            return rhs;
        }
        else if(rhs.is_identity())
        {
            return *this;
        }
        else
        {
            Fp z1z1 = this->z.square();
            Fp z2z2 = rhs.z.square();
            Fp u1 = this->x * z2z2;
            Fp u2 = rhs.x * z1z1;
            Fp s1 = this->y * z2z2 * rhs.z;
            Fp s2 = rhs.y * z1z1 * this->z;

            if(u1 == u2)
            {
                if(s1 == s2)
                {
                    return this->dbl();
                }
                else
                {
                    return Ep::identity();
                }
            }
            else
            {
                Fp h = u2 - u1;
                Fp i = (h + h).square();
                Fp j = h * i;
                Fp r = s2 - s1;
                   r = r + r;
                Fp v = u1 * i;
                Fp x3 = r.square() - j - v - v;
                   s1 = s1 * j;
                   s1 = s1 + s1;
                Fp y3 = r * (v - x3) - s1;
                Fp z3 = (this->z + rhs.z).square() - z1z1 - z2z2;
                   z3 = z3 * h;

                return Ep(x3, y3, z3);
            }
        }
    }
    Ep add(const EpAffine& rhs) const
    {
        if(this->is_identity())
        {
            return rhs.to_curve();
        }
        else if(rhs.is_identity())
        {
            return *this;
        }
        else
        {
            Fp z1z1 = this->z.square();
            Fp u2 = rhs.x * z1z1;
            Fp s2 = rhs.y * z1z1 * this->z;

            if(this->x == u2)
            {
                if(this->y == s2)
                {
                    return this->dbl();
                }
                else
                {
                    return Ep::identity();
                }
            }
            else
            {
                Fp h = u2 - this->x;
                Fp hh = h.square();
                Fp i = hh + hh;
                   i = i + i;
                Fp j = h * i;
                Fp r = s2 - this->y;
                   r = r + r;
                Fp v = this->x * i;
                Fp x3 = r.square() - j - v - v;
                   j = this->y * j;
                   j = j + j;
                Fp y3 = r * (v - x3) - j;
                Fp z3 = (this->z + h).square() - z1z1 - hh;

                return Ep(x3, y3, z3);
            }
        }
    }

    Ep operator + (const Ep& rhs) const
    {
        return this->add(rhs);
    }
    Ep operator + (const EpAffine& rhs) const
    {
        return this->add(rhs);
    }

    EpAffine to_affine() const
    {
        Fp zinv = this->z.invert();
        Fp zinv2 = zinv.square();
        Fp x = this->x * zinv2;
        Fp zinv3 = zinv2 * zinv;
        Fp y = this->y * zinv3;

        if(zinv.is_zero())
        {
            return EpAffine::identity();
        }
        else
        {
            return EpAffine(x, y);
        }
    }
};

Ep EpAffine::to_curve() const
{
    return Ep(
        this->x,
        this->y,
        this->is_identity() ? Fp::zero() : Fp::one()
    );
}


/// HashDomain Q for Sinsemilla hash function. This constant is created from the
/// initializer string halo2_gadgets::sinsemilla::primitives::Q_PERSONALIZATION = "z.cash:SinsemillaQ"
/// see primitives.rs: line 129
const Ep Ep::Q = Ep(
    Fp({0x67B76299266CB8D4, 0xD0D128C329E581C0, 0x6244657A3F4F6094, 0x0D43CFCDAE22562B}),
    Fp({0xBE93D15A29027311, 0xBDC9E25C08B4AB5B, 0xC0FBDB629781BA9A, 0x284D126C4C96B56C}),
    Fp({0xF24E7313E8A108F1, 0x3A1046C9E8EF2B9A, 0x49956F05DFCA8041, 0x0B57E97EF8C4E060})
);

// helper macro to update state of sinsemilla hash function
#define MERKLE_HASH_UPDATE(i) \
    tie(S_x, S_y) = zeosio::halo2::sinsemilla_base(i); \
    S_chunk = EpAffine(Fp::from_raw(S_x), Fp::from_raw(S_y)); \
    acc = (acc + S_chunk) + acc;

/// Implements `MerkleCRH^Orchard` as defined in
/// <https://zips.z.cash/protocol/protocol.pdf#orchardmerklecrh>
///
/// The layer with 2^n nodes is called "layer n":
///      - leaves are at layer MERKLE_DEPTH_ORCHARD = 32;
///      - the root is at layer 0.
/// `l` is MERKLE_DEPTH_ORCHARD - layer - 1.
///      - when hashing two leaves, we produce a node on the layer above the leaves, i.e.
///        layer = 31, l = 0
///      - when hashing to the final root, we produce the anchor with layer = 0, l = 31.
Fp sinsemilla_combine(const uint64_t& altitude, const Fp& left, const Fp& right)
{
    Fp l = left.montgomery_reduce(left.data[0], left.data[1], left.data[2], left.data[3], 0, 0, 0, 0);
    Fp r = left.montgomery_reduce(right.data[0], right.data[1], right.data[2], right.data[3], 0, 0, 0, 0);

    Ep acc = Ep::Q;
    array<uint64_t, 4> S_x, S_y;
    EpAffine S_chunk;

    MERKLE_HASH_UPDATE(altitude & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >>  0 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >> 10 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >> 20 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >> 30 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >> 40 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[0] >> 50 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[1] <<  4 & 0x3F0 | l.data[0] >> 60 & 0xF)
    MERKLE_HASH_UPDATE(l.data[1] >>  6 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[1] >> 16 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[1] >> 26 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[1] >> 36 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[1] >> 46 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] <<  8 & 0x300 | l.data[1] >> 56 & 0xFF)
    MERKLE_HASH_UPDATE(l.data[2] >>  2 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] >> 12 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] >> 22 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] >> 32 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] >> 42 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[2] >> 52 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[3] <<  2 & 0x3FC | l.data[2] >> 62 & 0x003)
    MERKLE_HASH_UPDATE(l.data[3] >>  8 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[3] >> 18 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[3] >> 28 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[3] >> 38 & 0x3FF)
    MERKLE_HASH_UPDATE(l.data[3] >> 48 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[0] <<  5 & 0x3E0 | l.data[3] >> 58 & 0x01F)   // cut off bit 256 of 'l'
    MERKLE_HASH_UPDATE(r.data[0] >>  5 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[0] >> 15 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[0] >> 25 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[0] >> 35 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[0] >> 45 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] <<  9 & 0x200 | r.data[0] >> 55 & 0x1FF)
    MERKLE_HASH_UPDATE(r.data[1] >>  1 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] >> 11 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] >> 21 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] >> 31 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] >> 41 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[1] >> 51 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[2] <<  3 & 0x3F8 | r.data[1] >> 61 & 0x007)
    MERKLE_HASH_UPDATE(r.data[2] >>  7 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[2] >> 17 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[2] >> 27 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[2] >> 37 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[2] >> 47 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] <<  7 & 0x380 | r.data[2] >> 57 & 0x07F)
    MERKLE_HASH_UPDATE(r.data[3] >>  3 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] >> 13 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] >> 23 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] >> 33 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] >> 43 & 0x3FF)
    MERKLE_HASH_UPDATE(r.data[3] >> 53 & 0x3FF)
    // MERKLE_HASH_UPDATE(r.data[3] >> 63 & 0x001) not needed because bit 256 of 'r' is cut off

    return acc.to_affine().x;
}

// empty roots up to depth 32
// d=0 => EMPTY_LEAF,
// d=1 => sinsemilla_combine(0, EMPTY_LEAF, EMPTY_LEAF)
const Fp EMPTY_ROOT[] = {
    Fp({0xcfc3a984fffffff9, 0x1011d11bbee5303e, 0xffffffffffffffff, 0x3fffffffffffffff}),
    Fp({0x07a9009e0a581029, 0x09e7b91f81e378fc, 0x1a82a264f22bea0a, 0x0c82031f50309c9f}),
    Fp({0xc9ecfc3a09178d32, 0x0b4c9ff2201994bf, 0x22cb9c0a6e41bd2a, 0x1c3b7eb79eeaf10a}),
    Fp({0x39bf490b9c63a6b3, 0x6b047793eebd2ad7, 0x8b6a56cc1bb1d2e6, 0x0e5ada44b5ac900b}),
    Fp({0xdaab63818557da0d, 0x21bb27e5ff238824, 0xbf65270b467ddf84, 0x339da128deb77752}),
    Fp({0xef0f55ff1a7862c0, 0xd3791e6211299a1c, 0x7d9b4c74da669560, 0x23c5bbf35b04091d}),
    Fp({0x95ef1287d7b44f08, 0x2b896f33a8733787, 0x103446c2f6129e50, 0x3948396852c405ed}),
    Fp({0x650cbea2da366868, 0xb4cf379f57fb95ff, 0xb8f866e7fbe3a165, 0x14341745aa0a32e1}),
    Fp({0x30a2f7c76000d014, 0x582926eae7647de9, 0x897539a776ee3c7c, 0x3ec97effbfdc357a}),
    Fp({0x5a3e1d2dfeb2f3f5, 0x508c680f28b566a7, 0xc637225236726af1, 0x318ff0f1acb17d2a}),
    Fp({0x982c92d2a442f828, 0x21f3b869d3b41fd5, 0xefc315441486318c, 0x317b7c06862887d1}),
    Fp({0x8bb91e504ff6674a, 0x4dfdc4b7c448d625, 0x34526da1897fb804, 0x193258690b34d94d}),
    Fp({0x742ec7b7098d5bff, 0xb56ec4a072832980, 0x69a6ea9032682613, 0x1a78651a8a6b5ba7}),
    Fp({0xa8982dcb00e85cc2, 0xd518389f0e87cb1d, 0x5c52f8e62fa88076, 0x14d9efe65120c572}),
    Fp({0x87e0bdcd42993761, 0xdb9343f10eeea647, 0xf4856994b3b2a0b4, 0x0fb917dc0f856b13}),
    Fp({0xd662ffd211e7f368, 0xfc069740671423a8, 0x2bfa72c6a613489d, 0x1f8c47597f4cff15}),
    Fp({0x2b80f62dc6d863ab, 0x6c5045667d2c8119, 0xd910b640fdf0e263, 0x1b64d31d56b12539}),
    Fp({0xd8dbcb104faa6a75, 0x8f1af94d6735e09c, 0x86fbf312a62ccf41, 0x267ed8285dcc11f5}),
    Fp({0xd76f4dabcd4c72ce, 0xa7f38b447eb41365, 0x771bda01c66290bd, 0x30d681f214d6573e}),
    Fp({0x3c7cf91c27440783, 0x0a09276c5efcd6e4, 0x6d712293c41b473f, 0x1fba7925b82b1993}),
    Fp({0xb0e99d8b68f82bab, 0x25b6f82dee24d331, 0xe84b455aab403234, 0x237352d7b9b5eaea}),
    Fp({0x7df9a36a040c75b4, 0xb66bc076da8e8636, 0x4575bcc51669bb77, 0x3214d00ce4062f44}),
    Fp({0x4494961af85b12e3, 0xced65f75e340ec69, 0xbcd1ad06f0d2dd0f, 0x21debbbef0c3f9b7}),
    Fp({0xacf2a3c599dac9d7, 0x7b45cfb6710feabe, 0x72ad422116d1f1c5, 0x39874c815db36323}),
    Fp({0xe9640012b7154a1f, 0x5f0ce18b91343ecc, 0xdcd87930bbe9c0fd, 0x037ce5b5657b1733}),
    Fp({0x64cce7f2a3cf17ec, 0xd1ff3c6376899f7d, 0x760edce8a9e779b2, 0x088d63087580ae23}),
    Fp({0xf79dbf3510ef2b84, 0xbcc919060d4f063c, 0x2e40a265292f3935, 0x274f5f826a3c118c}),
    Fp({0x41720afbfc0df919, 0xbfd210d9d5b68976, 0xe7826aebcb27128f, 0x2ae08e5ce2536718}),
    Fp({0x51cd6de53b41d7b5, 0x04526eb96ccbce4f, 0xc7a4373b4c51947a, 0x1da4928d22c7d20b}),
    Fp({0xaabcde1182e7c715, 0xd1cbb4a7dd212705, 0x0923feb28a9c387c, 0x253f940e57829ebd}),
    Fp({0xe0a73ed971f07cc4, 0x527c02d03a58ed2a, 0x4335ceb77aa63432, 0x0b84f68d78bd7ec8}),
    Fp({0x4f9a61965c06c1bc, 0xd3eed8b6685d6ff7, 0xe44224d7fcb0721c, 0x3e9d3ee01e5ea615}),
};

struct merkle_node
{
    char state;
    Fp val;
};

// merkle tree structure:
// 
//              (0)                 [d = 0] (root)
//         /            \
//       (1)            (2)         [d = 1]
//     /    \        /      \
//   (3)    (4)    (5)      (6)     [d = 2]
//   / \    / \    /  \    /  \
// (7) (8)(9)(10)(11)(12)(13)(14)   [d = 3]
//
#define MT_ARR_LEAF_ROW_OFFSET(d) ((1ULL<<(d)) - 1)
#define MT_ARR_FULL_TREE_OFFSET(d) ((1ULL<<((d)+1)) - 1)
#define MT_NUM_LEAVES(d) (1ULL<<(d))
void insert_into_merkle_tree(map<uint64_t, merkle_node>& tree, uint64_t& leaf_count, const uint64_t& depth, const Fp& leaf)
{
    // calculate array index of next free leaf in >local< tree
    uint64_t idx = MT_ARR_LEAF_ROW_OFFSET(depth-1) + leaf_count % MT_NUM_LEAVES(depth-1);
    // calculate tree offset to translate array indices of >local< tree to global array indices
    uint64_t tos = leaf_count / MT_NUM_LEAVES(depth-1) /*=tree_idx*/ * MT_ARR_FULL_TREE_OFFSET(depth-1);

    // insert leaf into tree
    tree[tos + idx] = {'N', leaf};

    // calculate merkle path up to root
    for(int d = 0; d < depth-1; d++)
    {
        // if array index of node is uneven it is always the left child
        bool is_left_child = 1 == idx % 2;

        // determine sister node
        uint64_t sis_idx = is_left_child ? idx + 1 : idx - 1;

        // get values of both nodes
        //                            (n)          |            (n)
        //                          /     \        |         /      \
        //                       (idx)     (0)     |     (sis_idx)  (idx)
        Fp l = is_left_child ? tree[tos + idx].val : tree[tos + sis_idx].val;
        Fp r = is_left_child ? EMPTY_ROOT[d]       : tree[tos + idx].val;

        // calculate sinsemilla merkle hash of parent node
        Fp parent_val = sinsemilla_combine(d, l, r);

        // set idx to parent node index:
        // left child's array index divided by two (integer division) equals array index of parent node
        idx = is_left_child ? idx / 2 : sis_idx / 2;

        // check if parent node is new: this is the case if the left child (=idx*2+1) of this parent is new
        char s = tree[tos + idx*2+1].state == 'N' ? 'N' : 'U';
        tree[tos + idx] = {s, parent_val};
    }
    
    // update global state
    ++leaf_count;
}

// main function to update merkle tree
// all note_commitments are being added to the tree
// final_nodes must include all left children
// required to calculate merkle path 
// callable from JavaScript (only 32 bit values)
val update_merkle_tree(unsigned int leaf_count_l,
                       unsigned int leaf_count_h,
                       unsigned int tree_depth, 
                       uintptr_t final_nodes, 
                       unsigned int final_nodes_num, 
                       uintptr_t note_commitments, 
                       unsigned int note_commitments_num)
{
    map<uint64_t, merkle_node> tree;
    uint64_t* fn = reinterpret_cast<uint64_t*>(final_nodes);
    uint64_t* nc = reinterpret_cast<uint64_t*>(note_commitments);
    uint64_t lc = static_cast<unsigned long long>(leaf_count_h) << 32 | leaf_count_l;
    
    // read final nodes and add to tree
    for(unsigned int i = 0; i < final_nodes_num; i++)
    {
        // 5 x uint64_t: index (1) and value (4)
        tree[fn[i*5+0]] = {'F', Fp({fn[i*5+1], fn[i*5+2], fn[i*5+3], fn[i*5+4]})};
    }
    
    // add note commitments as new leaves to tree
    for(unsigned int i = 0; i < note_commitments_num; i++)
    {
        Fp leaf({nc[i*4+0], nc[i*4+1], nc[i*4+2], nc[i*4+3]});
        insert_into_merkle_tree(tree, lc, tree_depth, leaf);
    }
    
    // collect updated ('U') and new ('N') nodes
    vector<uint64_t> nu_nodes;
    for(auto it = tree.begin(); it != tree.end(); ++it)
    {
        if(it->second.state == 'F')
            continue;
        
        nu_nodes.push_back(it->first | (it->second.state == 'U' ? 1ULL << 63 : 0));
        nu_nodes.push_back(it->second.val.data[0]);
        nu_nodes.push_back(it->second.val.data[1]);
        nu_nodes.push_back(it->second.val.data[2]);
        nu_nodes.push_back(it->second.val.data[3]);
    }

    return val(typed_memory_view(nu_nodes.size() * sizeof(uint64_t), reinterpret_cast<uint8_t*>(nu_nodes.data())));
}

EMSCRIPTEN_BINDINGS(x)
{
    emscripten::function("update_merkle_tree", &update_merkle_tree);
}
-- Prove2me | Definitions.Def_Yukon_f26f320d63e3d31767086ad3
-- name    : Yukon_f26f320d63e3d31767086ad3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:05:13.02645+00:00
-- url     : https://prove2.me/theorems/eb7a9afa-3e3c-48cc-82a3-8239de504903
-- title:
--   YukonModule.CompPoly.Univariate.Raw.Division.part0
-- statement:
--   Source module CompPoly.Univariate.Raw.Division.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Univariate/Raw/Division.lean
--
--   yukon-proof-operation:cdf9dc2cb05431da5fa8ae2932c19d9b3b84441248047bc884bf49001fb81cb1
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Y2RmOWRjMmNiMDU0MzFkYTVmYThhZTI5MzJjMTlkOWIzYjg0NDQxMjQ4MDQ3YmM4ODRiZjQ5MDAxZmI4MWNiMSIsImhhc2giOiI3OGRhZTM4YjBjZjU2N2IyYzU4YzJiMWYyNWViMDliMWRiMzc0YzU4MTZkN2MwOWZlMmE1M2RmYWJkMmYzMTU3Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9mMjZmMzIwZDYzZTNkMzE3NjcwODZhZDMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles, Valerii Huhnin
-/
module

import all Definitions.Def_Yukon_2b2cffaf7915639b497d3e9d

public import Definitions.Def_Yukon_2b2cffaf7915639b497d3e9d



public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Cases
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.GroupWithZero.Nat
public import Init
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Tropical.Basic
meta import Definitions.Def_Yukon_2b2cffaf7915639b497d3e9d
set_option backward.isDefEq.respectTransparency.types false
/-!
# Raw Univariate Polynomial Division

Division algorithms for raw computable univariate polynomials.
-/

public section

namespace CompPoly

namespace CPolynomial.Raw

variable {R : Type*}

section Division

variable [BEq R]

/-- Division with remainder by a monic polynomial using polynomial long division. -/
@[expose]
def divModByMonicAux [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R × CPolynomial.Raw R :=
  go p.size p q
where
  go : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R × CPolynomial.Raw R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      if p.size < q.size then
        ⟨0, p⟩
      else
        let k := p.size - q.size
        let q' := C p.leadingCoeff * (q * X.pow k)
        let p' := (p - q').trim
        let (e, f) := go n p' q
        ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def divByMonic [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def modByMonic [CommRing R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  (divModByMonicAux p q).2

/-- Subtract `scale * q * X^shift` from `p` without using general polynomial multiplication. -/
@[inline, specialize]
def subScaledShift [Field R] (p q : CPolynomial.Raw R) (scale : R) (shift : Nat) :
    CPolynomial.Raw R :=
  let coeffs := Array.ofFn (n := p.size) fun j : Fin p.size ↦
    let i := j.val - shift
    let subtractCoeff := if shift ≤ j.val ∧ i < q.size then scale * q.coeff i else 0
    p.coeff j.val - subtractCoeff
  (CPolynomial.Raw.mk coeffs).trim

/-- Remainder-only long division by a monic polynomial.

Unlike `modByMonic`, this does not compute the quotient and avoids the general
polynomial multiplications used by each cancellation step. It is intended as an
executable implementation for the canonical `modByMonic` specification.
-/
@[expose, inline, specialize]
def modByMonicRemainderOnly [Field R] (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) :
    CPolynomial.Raw R :=
  go p.size p q
where
  go : Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  | 0, p, _ => p
  | n + 1, p, q =>
      if p.size < q.size then
        p
      else
        let k := p.size - q.size
        let p' := subScaledShift p q p.leadingCoeff k
        go n p' q

/-- Inverse modulo `X^k`, using Newton iteration and the supplied low-product backend. -/
@[expose, inline, specialize]
def inverseModX [Field R] [LawfulBEq R] (M : MulLowContext R) (k : Nat)
    (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if k = 0 then
    #[]
  else
    go (k + 1) 1 (C (p.coeff 0)⁻¹)
where
  go : Nat → Nat → CPolynomial.Raw R → CPolynomial.Raw R
  | 0, _, g => truncate k g
  | fuel + 1, n, g =>
      if k ≤ n then
        truncate k g
      else
        let next := Nat.min k (2 * n)
        let fg := M.mulLow next p g
        let correction := C (2 : R) - fg
        let g' := M.mulLow next g correction
        go fuel next g'

/--
Remainder by a monic polynomial through reversal and truncated products.

For canonical monic inputs this computes the quotient from the reversed divisor
inverse modulo `X^k`, then subtracts only the low coefficients needed for the
remainder. Inputs outside the fast-path guard use the simple monic-remainder
implementation.
-/
@[inline, specialize]
def modByMonicByReversal [Field R] [LawfulBEq R] (M : MulLowContext R)
    (p : CPolynomial.Raw R) (q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  if p.trim == p && q.trim == q && q.leadingCoeff == 1 then
    if p.size < q.size then
      p
    else
      let k := p.size - q.size + 1
      let remainderLen := q.size - 1
      let revP := reverse p.size p
      let revQ := reverse q.size q
      let invRevQ := inverseModX M k revQ
      let quotientRev := M.mulLow k revP invRevQ
      let quotient := reverse k quotientRev
      let productLow := M.mulLow remainderLen q quotient
      truncate remainderLen p - productLow
  else
    modByMonicRemainderOnly p q

/-- Division of two `CPolynomial.Raw`s. -/
def div [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial.Raw`s. -/
def mod [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance  _root_.CompPoly.CPolynomial.Raw.instDivOfField [Field R] : Div (CPolynomial.Raw R) := ⟨div⟩
instance  _root_.CompPoly.CPolynomial.Raw.instModOfField [Field R] : Mod (CPolynomial.Raw R) := ⟨mod⟩

/-- Normalize a nonzero raw polynomial to monic form. The zero polynomial stays zero. -/
def monicNormalize [Field R] (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let p := p.trim
  if p == 0 then
    0
  else
    p.leadingCoeff⁻¹ • p

/-- Raw Euclidean gcd with explicit fuel, normalized to a monic result. -/
def gcdMonicWithFuel [Field R] :
    Nat → CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  | 0, p, _ => monicNormalize p
  | fuel + 1, p, q =>
      let p := p.trim
      let q := q.trim
      if q == 0 then
        monicNormalize p
      else
        gcdMonicWithFuel fuel q (p % q)

/-- Raw monic Euclidean gcd. -/
def gcdMonic [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  gcdMonicWithFuel (p.size + q.size + 1) p q

end Division

end CPolynomial.Raw

end CompPoly



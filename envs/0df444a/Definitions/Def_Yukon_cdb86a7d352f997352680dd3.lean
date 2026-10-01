-- Prove2me | Definitions.Def_Yukon_cdb86a7d352f997352680dd3
-- name    : Yukon_cdb86a7d352f997352680dd3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:16:52.138422+00:00
-- url     : https://prove2.me/theorems/33ad8773-aae7-4a1f-a89b-cf5ec50a0dd6
-- title:
--   YukonModule.CompPoly.Univariate.NTT.Domain.part0
-- statement:
--   Source module CompPoly.Univariate.NTT.Domain.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Univariate/NTT/Domain.lean
--
--   yukon-proof-operation:57995779c68dfe6156ea349068c13ad1b4e45e4ce1aa131169818adaab123edc
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NTc5OTU3NzljNjhkZmU2MTU2ZWEzNDkwNjhjMTNhZDFiNGU0NWU0Y2UxYWExMzExNjk4MThhZGFhYjEyM2VkYyIsImhhc2giOiJjZjgwMTgzYWM3MTliMWFlNzBmNjcwOGIxNDVjOGYwNjYzMWQwNDU1MDRhMzU0ZDE0YzY5ZDIzNmZiMTI2NTI4Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jZGI4NmE3ZDM1MmY5OTczNTI2ODBkZDMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu, Valerii Huhnin
-/
module


public import Init.Data.Vector.OfFn
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots


public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Cases
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.GroupWithZero.Nat
public import Init
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Definitions.Def_Yukon_8b420bde4918adb5e45d1b8c
public import Definitions.Def_Yukon_f26f320d63e3d31767086ad3
public import Definitions.Def_Yukon_2b2cffaf7915639b497d3e9d
public import Definitions.Def_Yukon_3d8244498ed1310db5b4a14e
meta import Definitions.Def_Yukon_8b420bde4918adb5e45d1b8c
meta import Definitions.Def_Yukon_f26f320d63e3d31767086ad3
meta import Definitions.Def_Yukon_2b2cffaf7915639b497d3e9d
meta import Definitions.Def_Yukon_3d8244498ed1310db5b4a14e
set_option backward.isDefEq.respectTransparency.types false
/-!
# NTT Domain

This file defines the radix-2 NTT domain parameters and basic raw-polynomial
shape helpers used by forward/inverse NTT.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

/-- Parameters for a radix-2 NTT domain of size `2 ^ logN`. -/
structure Domain (R : Type*) [Field R] where
  logN : Nat
  omega : R
  primitive : IsPrimitiveRoot omega (2 ^ logN)

namespace Domain

/-- Domain size. -/
@[simp] def n (D : Domain R) : Nat := 2 ^ D.logN

/-- Index type for vectors over the domain. -/
abbrev Idx (D : Domain R) := Fin D.n

/-- The `i`-th evaluation node `omega^i`. -/
@[inline] def node (D : Domain R) (i : D.Idx) : R := D.omega ^ (i : Nat)

/-- Inverse root of unity. -/
@[inline] def omegaInv (D : Domain R) : R := D.omega⁻¹

/-- The domain with the inverse root, used by inverse NTT butterflies. -/
def inverse (D : Domain R) : Domain R where
  logN := D.logN
  omega := D.omegaInv
  primitive := by
    simpa [omegaInv] using D.primitive.inv

/-- Multiplicative inverse of the domain size in `R`. -/
@[inline] def nInv (D : Domain R) : R := ((D.n : Nat) : R)⁻¹

@[simp] lemma n_pos (D : Domain R) : 0 < D.n := by
  simp [n]

@[simp] lemma n_ne_zero (D : Domain R) : D.n ≠ 0 := by
  exact Nat.ne_of_gt D.n_pos

/-- The size of an NTT domain is nonzero in its coefficient field. -/
theorem natCast_ne_zero (D : Domain R) : ((D.n : Nat) : R) ≠ 0 := by
  letI : NeZero D.n := ⟨D.n_ne_zero⟩
  exact D.primitive.neZero'.out

section RawHelpers

variable [BEq R]

/-- Required convolution length for multiplying `p` and `q`. -/
def requiredLength (p q : CPolynomial.Raw R) : Nat :=
  if p.trim.size = 0 ∨ q.trim.size = 0 then
    0
  else
    p.trim.size + q.trim.size - 1

theorem requiredLength_eq_zero_of_left_trim_size_zero
    (p q : CPolynomial.Raw R) (hp : p.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hp]

theorem requiredLength_eq_zero_of_right_trim_size_zero
    (p q : CPolynomial.Raw R) (hq : q.trim.size = 0) :
    requiredLength p q = 0 := by
  simp [requiredLength, hq]

theorem requiredLength_eq_of_trim_size_pos
    (p q : CPolynomial.Raw R) (hp : 0 < p.trim.size) (hq : 0 < q.trim.size) :
    requiredLength p q = p.trim.size + q.trim.size - 1 := by
  have hp0 : p.trim.size ≠ 0 := Nat.ne_of_gt hp
  have hq0 : q.trim.size ≠ 0 := Nat.ne_of_gt hq
  simp [requiredLength, hp0, hq0]

/-- Whether domain `D` is large enough for multiplying `p` and `q`. -/
def fits (D : Domain R) (p q : CPolynomial.Raw R) : Prop :=
  requiredLength p q ≤ D.n

/-- Truncate a polynomial to at most `m` coefficients. -/
def truncate (m : Nat) (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.extract 0 m

end RawHelpers
end Domain

/-- The smallest radix-2 exponent that can cover a requested convolution length. -/
def bestLogN (requiredLen : Nat) : Nat :=
  Nat.clog 2 requiredLen

/-- Load an array in natural order and pad it to a domain-sized array. -/
@[inline] def loadNaturalArray (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0)

@[simp] theorem size_loadNaturalArray (D : Domain R) (a : Array R) :
    (loadNaturalArray D a).size = D.n := by
  simp [loadNaturalArray]

@[simp] theorem getElem_loadNaturalArray (D : Domain R) (a : Array R) (i : Nat)
    (hi : i < (loadNaturalArray D a).size) :
    (loadNaturalArray D a)[i] = a.getD i 0 := by
  simp [loadNaturalArray]

/-- Load an array in natural order and pad it to a domain-sized vector. -/
@[inline] def loadNaturalVector (D : Domain R) (a : Array R) : Vector R D.n :=
  Vector.ofFn (fun i : D.Idx => a.getD i.1 0)

/-- An NTT domain bundled with proof that it covers the requested convolution length. -/
abbrev FittingDomain (R : Type*) [Field R] (requiredLen : Nat) :=
  { D : Domain R // requiredLen ≤ D.n }

/--
Generic adapter from field-specific radix-2 domain tables to a best-fitting domain lookup.

The adapter chooses `logN = Nat.clog 2 requiredLen`, then returns `none` if that exponent
is outside the supported table.
-/
def bestDomainForLength?
    (maxLogN : Nat) (domainOfLogN : (logN : Nat) → logN ≤ maxLogN → Domain R)
    (domainOfLogN_logN : ∀ logN hlogN, (domainOfLogN logN hlogN).logN = logN)
    (requiredLen : Nat) : Option (FittingDomain R requiredLen) :=
  let logN := bestLogN requiredLen
  if hlogN : logN ≤ maxLogN then
    some ⟨domainOfLogN logN hlogN, by
      have hfit : requiredLen ≤ 2 ^ logN := by
        simpa [logN, bestLogN] using Nat.le_pow_clog (by decide : 1 < 2) requiredLen
      simpa [Domain.n, domainOfLogN_logN logN hlogN] using hfit⟩
  else
    none

end NTT
end CPolynomial
end CompPoly



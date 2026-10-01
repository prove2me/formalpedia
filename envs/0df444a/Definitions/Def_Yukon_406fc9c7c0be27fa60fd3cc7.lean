-- Prove2me | Definitions.Def_Yukon_406fc9c7c0be27fa60fd3cc7
-- name    : Yukon_406fc9c7c0be27fa60fd3cc7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:27.571162+00:00
-- url     : https://prove2.me/theorems/2fc1239f-dc40-423c-ab3f-876a836a5aee
-- title:
--   YukonModule.CompPoly.Fields.Montgomery.Basic.part0
-- statement:
--   Source module CompPoly.Fields.Montgomery.Basic.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/Montgomery/Basic.lean
--
--   provider-v8:7fb554a17cb7e2391cf58fdaf3091a43f62898d4e2d6f2b116bd0f3c1b76651d
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODo3ZmI1NTRhMTdjYjdlMjM5MWNmNThmZGFmMzA5MWE0M2Y2Mjg5OGQ0ZTJkNmYyYjExNmJkMGYzYzFiNzY2NTFkIiwiaGFzaCI6IjU0MmIzMzdmYjcyYzQ2OGRlMjBiNTUwMGRhNzlkMzkxNDFiN2MxMjhmNzdlNjcyMTcyNTdhNWRlZDIyOWI2ZmIiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzQwNmZjOWM3YzBiZTI3ZmE2MGZkM2NjNyIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Montgomery Reduction

Radix-generic specification and correctness lemmas for single-word Montgomery reduction.
Word-specific implementations refine these results in sibling modules.
-/

@[expose] public section

namespace Montgomery

/-- Natural-number Montgomery reduction used to specify the native-word reducer. -/
def reduceNat (R p negInv x : ℕ) : ℕ :=
  let m := (x % R * negInv) % R
  let u := (x + m * p) / R
  if u < p then u else u - p

/-- The quotient before the final conditional subtraction in Montgomery reduction. -/
def reduceNatQuotient (R p negInv x : ℕ) : ℕ :=
  let m := (x % R * negInv) % R
  (x + m * p) / R

/-- The pre-subtraction quotient is below twice the modulus. -/
theorem reduceNatQuotient_lt_two_mul (R p negInv x : ℕ)
    (hR : 0 < R) (hp : 0 < p) (hx : x < p * R) :
    reduceNatQuotient R p negInv x < 2 * p := by
  let m := x % R * negInv % R
  have hm_lt : m < R := Nat.mod_lt _ hR
  change (x + m * p) / R < 2 * p
  rw [Nat.div_lt_iff_lt_mul]
  · have hprod_lt : m * p < R * p := Nat.mul_lt_mul_of_pos_right hm_lt hp
    have hprod_lt' : m * p < p * R := by
      simpa only [Nat.mul_comm] using hprod_lt
    calc
      x + m * p < p * R + p * R := Nat.add_lt_add hx hprod_lt'
      _ = 2 * p * R := by ring
  · exact hR

/-- Montgomery reduction returns a canonical representative. -/
theorem reduceNat_lt (R p negInv x : ℕ)
    (hR : 0 < R) (hp : 0 < p) (hx : x < p * R) :
    reduceNat R p negInv x < p := by
  change (if reduceNatQuotient R p negInv x < p then
    reduceNatQuotient R p negInv x else reduceNatQuotient R p negInv x - p) < p
  have hu := reduceNatQuotient_lt_two_mul R p negInv x hR hp hx
  by_cases h : reduceNatQuotient R p negInv x < p
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    omega

/-- The Montgomery divisibility identity: if `(negInv * p) % R = R - 1` (i.e.
`negInv = -p⁻¹ mod R`), then `R ∣ x + ((x mod R)·negInv mod R)·p` for every `x`. -/
theorem dvd_add (R p negInv : ℕ) (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (x : ℕ) :
    R ∣ x + ((x % R * negInv) % R) * p := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod, Nat.mod_mul_mod (x % R * negInv) p R, Nat.mul_assoc]
  rw [← Nat.mul_mod_mod, hnegInv, Nat.add_mod_mod, add_comm, ← Nat.mul_add_one]
  rw [show R - 1 + 1 = R by omega, Nat.mul_mod_left]

/-- The pre-subtraction quotient represents multiplication by `R⁻¹` in `ZMod p`. -/
theorem reduceNatQuotient_cast (R p negInv : ℕ) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (hRne : (R : ZMod p) ≠ 0) (x : ℕ) :
    (reduceNatQuotient R p negInv x : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  change (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹
  have hdiv : R ∣ x + m * p := by
    simpa [m] using dvd_add R p negInv hR hnegInv x
  have hu_mul : u * R = x + m * p := Nat.div_mul_cancel hdiv
  have hcast_mul : (u : ZMod p) * (R : ZMod p) = (x : ZMod p) := by
    rw [← Nat.cast_mul, hu_mul, Nat.cast_add, Nat.cast_mul]
    simp
  rw [← hcast_mul]
  exact (mul_inv_cancel_right₀ hRne (u : ZMod p)).symm

/-- Montgomery reduction represents multiplication by `R⁻¹` in `ZMod p`. -/
theorem reduceNat_cast (R p negInv : ℕ) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (hRne : (R : ZMod p) ≠ 0) (x : ℕ) :
    (reduceNat R p negInv x : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  have hu_cast : (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
    simpa only [reduceNatQuotient, m, u] using
      reduceNatQuotient_cast R p negInv hR hnegInv hRne x
  change ((if u < p then u else u - p : ℕ) : ZMod p) =
    (x : ZMod p) * (R : ZMod p)⁻¹
  by_cases hu : u < p
  · rw [if_pos hu]
    exact hu_cast
  · have hfield : ((u - p : ℕ) : ZMod p) = (u : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    rw [if_neg hu]
    rw [hfield]
    exact hu_cast

/-- Two naturals below `p` are equal once their `ZMod p` casts agree. -/
theorem natCast_inj_of_lt {p a b : ℕ} (h : (a : ZMod p) = (b : ZMod p))
    (ha : a < p) (hb : b < p) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

end Montgomery



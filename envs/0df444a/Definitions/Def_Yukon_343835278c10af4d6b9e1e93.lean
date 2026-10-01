-- Prove2me | Definitions.Def_Yukon_343835278c10af4d6b9e1e93
-- name    : Yukon_343835278c10af4d6b9e1e93
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:55:10.602284+00:00
-- url     : https://prove2.me/theorems/3c5a6965-e31e-44d5-9a6a-398259438ad5
-- title:
--   YukonModule.CompPoly.Fields.Montgomery.Native32.part0
-- statement:
--   Source module CompPoly.Fields.Montgomery.Native32.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/Montgomery/Native32.lean
--
--   yukon-proof-operation:6f3d289e2269e3d7d609c2e9205f7d49ad0a0b85405ce2177015bc431e0c8eb2
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NmYzZDI4OWUyMjY5ZTNkN2Q2MDljMmU5MjA1ZjdkNDlhZDBhMGI4NTQwNWNlMjE3NzAxNWJjNDMxZTBjOGViMiIsImhhc2giOiJhMjkxNTA4OWZlNzA3MTZkYzAzY2FiZDhmYWVmNjk0Mzk1OWU3NjA2OWYyZmU3MTk4OTRlYjRkNTdkZTZmMDI2Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8zNDM4MzUyNzhjMTBhZjRkNmI5ZTFlOTMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
module

public import Definitions.Def_Yukon_406fc9c7c0be27fa60fd3cc7



public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.ModEq
public import Init
meta import Definitions.Def_Yukon_406fc9c7c0be27fa60fd3cc7
set_option backward.isDefEq.respectTransparency.types false
/-!
# Native 32-bit Montgomery Reduction

Raw word operations for Montgomery reduction with radix `2 ^ 32`.
-/

@[expose] public section

namespace Montgomery
namespace Native32

/-- Montgomery reduction. -/
@[inline]
def reduceRaw (p32 : UInt32) (p64 : UInt64) (negInv : UInt32) (x : UInt64) : UInt32 :=
  let m := (x.toUInt32 * negInv).toUInt64
  let u := ((x + m * p64) >>> 32).toUInt32
  if u < p32 then u else u - p32

/-- The native pre-subtraction quotient in 32-bit Montgomery reduction. -/
def reduceQuotient (negInv : UInt32) (p x : UInt64) : UInt32 :=
  ((x + (x.toUInt32 * negInv).toUInt64 * p) >>> 32).toUInt32

/-- Conditional subtraction of the modulus in 32-bit Montgomery reduction. -/
def conditionalSubtract (p32 : UInt32) (u : UInt32) : UInt32 :=
  if u < p32 then u else u - p32

variable {modulus : ℕ} {p32 negInv u : UInt32} {p64 x : UInt64}

theorem reduceRaw_eq_conditionalSubtract :
    reduceRaw p32 p64 negInv x =
      conditionalSubtract p32 (reduceQuotient negInv p64 x) := rfl

/-- The native quotient agrees with the `Nat`-level Montgomery quotient. -/
theorem reduceQuotient_toNat (hp_pos : 0 < p64.toNat) (hbound : p64.toNat < 2 ^ 31)
    (h : x.toNat < p64.toNat * 2 ^ 32) :
    (reduceQuotient negInv p64 x).toNat =
      reduceNatQuotient (2 ^ 32) p64.toNat negInv.toNat x.toNat := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    reduceQuotient, reduceNatQuotient, Nat.shiftRight_eq_div_pow]
  let mNat := x.toNat * negInv.toNat % 2 ^ 32
  have hm_lt : mNat < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * p64.toNat < 2 ^ 64 := by
    have hprod_lt : mNat * p64.toNat < p64.toNat * 2 ^ 32 := by
      have := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
      simpa [Nat.mul_comm] using this
    calc
      x.toNat + mNat * p64.toNat <
          p64.toNat * 2 ^ 32 + p64.toNat * 2 ^ 32 := Nat.add_lt_add h hprod_lt
      _ = 2 * p64.toNat * 2 ^ 32 := by ring
      _ < 2 ^ 64 := by omega
  norm_num [UInt32.size]
  change ((x.toNat + mNat * p64.toNat) % 2 ^ 64 / 2 ^ 32) % 2 ^ 32 =
      (x.toNat + mNat * p64.toNat) / 2 ^ 32
  rw [Nat.mod_eq_of_lt hsum_lt, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

theorem conditionalSubtract_toNat :
    (conditionalSubtract p32 u).toNat =
      if u.toNat < p32.toNat then u.toNat else u.toNat - p32.toNat := by
  simp only [conditionalSubtract, UInt32.lt_iff_toNat_lt]
  by_cases hx : u.toNat < p32.toNat
  · simp only [if_pos hx]
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      omega
    simp only [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]

/-- Native Montgomery reduction agrees with the natural-number specification. -/
theorem reduceRaw_toNat (hp32 : p32.toNat = modulus) (hp64 : p64.toNat = modulus)
    (hp_pos : 0 < modulus) (hp_bound : modulus < 2 ^ 31)
    (h : x.toNat < modulus * 2 ^ 32) :
    (reduceRaw p32 p64 negInv x).toNat =
      reduceNat (2 ^ 32) modulus negInv.toNat x.toNat := by
  rw [reduceRaw_eq_conditionalSubtract, conditionalSubtract_toNat]
  rw [reduceQuotient_toNat
    (by simpa only [hp64] using hp_pos)
    (by simpa only [hp64] using hp_bound)
    (by simpa only [hp64] using h)]
  rw [hp32, hp64]
  rfl

theorem conditionalSubtract_lt (h : u.toNat < 2 * p32.toNat) :
    (conditionalSubtract p32 u).toNat < p32.toNat := by
  simp only [conditionalSubtract, UInt32.lt_iff_toNat_lt]
  by_cases hx : u.toNat < p32.toNat
  · rw [if_pos hx]
    exact hx
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      omega
    rw [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]
    omega

theorem conditionalSubtract_cast :
    ((conditionalSubtract p32 u).toNat : ZMod p32.toNat) =
      (u.toNat : ZMod p32.toNat) := by
  simp only [conditionalSubtract]
  by_cases hx : u < p32
  · rw [if_pos hx]
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      rw [UInt32.lt_iff_toNat_lt] at hx
      exact Nat.le_of_not_gt hx
    rw [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hp_le_x
      exact hp_le_x)]
    simp

theorem reduceRaw_lt (hp : p32.toNat = p64.toNat) (hp_pos : 0 < p64.toNat)
    (hp_bound : p64.toNat < 2 ^ 31)
    (h : x.toNat < p64.toNat * 2 ^ 32) :
    (reduceRaw p32 p64 negInv x).toNat < p32.toNat := by
  rw [reduceRaw_toNat hp rfl hp_pos hp_bound h, hp]
  exact reduceNat_lt (2 ^ 32) p64.toNat negInv.toNat x.toNat
    (by decide) hp_pos h

theorem reduceRaw_cast [Fact (Nat.Prime modulus)]
    (hp32 : p32.toNat = modulus) (hp64 : p64.toNat = modulus)
    (hp_pos : 0 < modulus) (hp_bound : modulus < 2 ^ 31)
    (hnegInv : negInv.toNat * modulus % 2 ^ 32 = 2 ^ 32 - 1)
    (hRne : ((2 ^ 32 : ℕ) : ZMod modulus) ≠ 0)
    (h : x.toNat < modulus * 2 ^ 32) :
    ((reduceRaw p32 p64 negInv x).toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  rw [reduceRaw_toNat hp32 hp64 hp_pos hp_bound h]
  exact reduceNat_cast (2 ^ 32) modulus negInv.toNat
    (by decide) hnegInv hRne x.toNat

end Native32
end Montgomery



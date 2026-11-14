-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalIntegers
-- name    : InfoLossLAR_Native_AFT_BinaryRationalIntegers
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:18:00.768688+00:00
-- url     : https://prove2.me/theorems/23c62311-fe3e-4004-9908-86ed362181e7
-- title:
--   Constructing rational encodings from existing integer digits
-- statement:
--   The integer and natural constructors normalize a supplied magnitude digit list and use denominator one. For sign bit $s$ and magnitude string $a$,
--
--   $$\operatorname{decode}(\operatorname{ofInt}(s,a))=(-1)^s v(a),\qquad\operatorname{decode}(\operatorname{ofNat}(a))=v(a).$$
--
--   These constructors read existing digit strings and retain their native operation charges.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalIntegers.lean; migrated native SHA256 4c8b0a7d1aa0bede9d0bc28f46295ea429445a404455c9ba4e0196853b61d5de; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalData
import Mathlib


/-! Integer-to-rational constructors read an existing signed binary input.
They never convert an opaque arbitrary-precision natural in one step. -/
namespace AFT.BinaryArithmetic.RationalBits

def ofInt (negative : Bool) (digits : List Bool) : RationalResult :=
  let normalized := normalize digits
  ⟨{negative := negative,numerator := normalized.digits,denominator := [true]
    numerator_normal := by dsimp only [normalized];rw [normalize_length,normalize_value]
    denominator_normal := by decide
    denominator_positive := by decide
    coprime := by simp [value]},normalized.work+3⟩

def ofNat (digits : List Bool) : RationalResult := ofInt false digits

theorem ofInt_value (negative : Bool) (digits : List Bool) :
    (ofInt negative digits).data.decode=(signedValue negative digits : ℚ) := by
  rw [decode_fraction]
  simp only [ofInt,signedValue,normalize_value,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,
    Nat.cast_one,div_one]

theorem ofNat_value (digits : List Bool) : (ofNat digits).data.decode=(value digits : ℚ) := by
  simp [ofNat,ofInt_value,signedValue]





end AFT.BinaryArithmetic.RationalBits



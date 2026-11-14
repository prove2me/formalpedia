-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalOperations
-- name    : InfoLossLAR_Native_AFT_BinaryRationalOperations
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:19:31.293268+00:00
-- url     : https://prove2.me/theorems/daaac342-8d5f-4fcf-9d6d-e9fd5b3937ec
-- title:
--   Exact arithmetic on canonical rational encodings
-- statement:
--   The operations on canonical rational encodings are zero, sign negation, inversion, multiplication, and addition. They preserve their ordinary rational meanings:
--
--   $$\operatorname{decode}(\operatorname{op}(e_1,e_2))=\operatorname{op}(\operatorname{decode}(e_1),\operatorname{decode}(e_2)).$$
--
--   The corresponding unary identities hold for negation and inversion, with $0^{-1}=0$. Arithmetic results retain native operation charges; a fixed cubic charge budget is supplied for later estimates.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalOperations.lean; migrated native SHA256 0db8b36eb41999d6f3fc79b0e9e230d23eb80cf15197efcc267f505c42f36177; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinarySignedAddition
import Mathlib


/-! Executable arithmetic on canonical rational bit strings. -/
set_option backward.isDefEq.respectTransparency false

namespace AFT.BinaryArithmetic
namespace RationalBits

def zero : RationalBits := ⟨false,[],[true],by decide,by decide,by decide,by decide⟩

def negate (input : RationalBits) : RationalResult :=
  ⟨{input with negative := !input.negative},2⟩

def inverse (input : RationalBits) : RationalResult :=
  if hz : input.numerator=[] then ⟨zero,2⟩ else
    ⟨{negative := input.negative,numerator := input.denominator,denominator := input.numerator
      numerator_normal := input.denominator_normal,denominator_normal := input.numerator_normal
      denominator_positive := by
        by_contra hn
        have hh : value input.numerator=0 := by omega
        have hl := input.numerator_normal
        rw [hh,Nat.size_zero] at hl
        exact hz (List.length_eq_zero_iff.mp hl)
      coprime := input.coprime.symm},2⟩

def multiply (first second : RationalBits) : RationalResult :=
  let top := BinaryArithmetic.multiply first.numerator second.numerator
  let bottom := BinaryArithmetic.multiply first.denominator second.denominator
  let result := reduce (first.negative ^^ second.negative) top.digits bottom.digits (by
    rw [BinaryArithmetic.multiply_value]
    exact Nat.mul_pos first.denominator_positive second.denominator_positive)
  ⟨result.data,top.work+bottom.work+result.work+3⟩

def add (first second : RationalBits) : RationalResult :=
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  let top := signedAdd first.negative second.negative left.digits right.digits
  let bottom := BinaryArithmetic.multiply first.denominator second.denominator
  let result := reduce top.negative top.digits bottom.digits (by
    rw [BinaryArithmetic.multiply_value]
    exact Nat.mul_pos first.denominator_positive second.denominator_positive)
  ⟨result.data,left.work+right.work+top.work+bottom.work+result.work+4⟩

@[simp] theorem zero_value : zero.decode=0 := by decide

theorem negate_value (input : RationalBits) : (negate input).data.decode= -input.decode := by
  rw [decode_fraction,decode_fraction]
  simp only [negate,signedValue]
  by_cases hsign : input.negative = true <;> simp_all [neg_div]

theorem inverse_value (input : RationalBits) : (inverse input).data.decode=input.decode⁻¹ := by
  simp only [inverse]
  split <;> rename_i hz
  · have hn : input.decode=0 := by rw [decode_fraction];simp [signedValue,hz,value]
    simp [hn]
  · rw [decode_fraction,decode_fraction]
    simp only [signedValue]
    cases input.negative <;> simp [inv_div,neg_div]

theorem multiply_value (first second : RationalBits) :
    (multiply first second).data.decode=first.decode*second.decode := by
  simp only [multiply,reduce_value,signedValue,BinaryArithmetic.multiply_value]
  rw [decode_fraction,decode_fraction]
  cases first.negative <;> cases second.negative <;>
    simp [signedValue,Nat.cast_mul,Int.cast_mul,div_mul_div_comm]

theorem add_value (first second : RationalBits) : (add first second).data.decode=first.decode+second.decode := by
  simp only [add,reduce_value,signedAdd_value,Int.cast_add]
  rw [decode_fraction,decode_fraction]
  simp only [signedValue,BinaryArithmetic.multiply_value,Nat.cast_mul]
  have hd1 : (value first.denominator : ℚ) ≠ 0 := by exact_mod_cast first.denominator_positive.ne'
  have hd2 : (value second.denominator : ℚ) ≠ 0 := by exact_mod_cast second.denominator_positive.ne'
  cases first.negative <;> cases second.negative <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Int.cast_natCast,Int.cast_neg,Int.cast_mul] <;> field_simp

def primitiveWorkBound (bits : ℕ) : ℕ := 10000000*(bits+2)^3









end RationalBits
end AFT.BinaryArithmetic



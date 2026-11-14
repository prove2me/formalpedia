-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalControl
-- name    : InfoLossLAR_Native_AFT_BinaryRationalControl
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:20:20.573742+00:00
-- url     : https://prove2.me/theorems/11388a16-88ef-4ea0-b4d5-fd70a45b37c3
-- title:
--   Positive part and natural ceiling for rational encodings
-- statement:
--   The positive-part operation and natural-ceiling operation act on a canonical signed rational encoding of $x$. Their decoded outputs satisfy
--
--   $$\operatorname{positivePart}(x)=\max\{x,0\},\qquad\operatorname{ceil}_{\mathbb N}(x)=\max\{0,\lceil x\rceil\}.$$
--
--   The ceiling uses binary quotient and remainder computations, with a single increment when the nonnegative fraction has nonzero remainder. Each result records the native charge of its arithmetic.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalControl.lean; migrated native SHA256 80fed0c6478c32e7968e894f35cb20f85bed8f9bfedd1ecb118c27781f835d56; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalOperations
import Mathlib


/-! # Actual binary clipping and natural ceiling

The ceiling uses binary long division, high-zero trimming, and one ripple
increment when the remainder is nonzero. Tests inspect the stored sign or
list constructor, never the decoded rational value.
-/
namespace AFT.BinaryArithmetic
namespace RationalBits

def maxZero (input : RationalBits) : RationalResult :=
  if input.negative then ⟨zero,2⟩ else ⟨input,2⟩

theorem maxZero_value (input : RationalBits) : (maxZero input).data.decode=max input.decode 0 := by
  have hd : (0 : ℚ) < value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | false =>
      have hp : 0≤ input.decode := by rw [decode_fraction];simp only [signedValue,hs,ite_false,Bool.false_eq_true];positivity
      simp only [maxZero,hs,ite_false,Bool.false_eq_true,max_eq_left hp]
  | true =>
      have hn : input.decode≤ 0 := by rw [decode_fraction];simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast];exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [maxZero,hs,ite_true,zero_value,max_eq_right hn]



 theorem ceil_fraction (num den : ℕ) (hd : 0 < den) :
    ⌈(num : ℚ)/(den : ℚ)⌉₊=if num%den=0 then num/den else num/den+1 := by
  have hdq : (0 : ℚ)<den := by exact_mod_cast hd
  have hb : num/den*den+num%den=num := by nlinarith [Nat.div_add_mod num den]
  have hr := Nat.mod_lt num hd
  split <;> rename_i hz
  · have he : (num : ℚ)/(den : ℚ)=(num/den : ℕ) := by
      apply (div_eq_iff hdq.ne').mpr
      have hn : num=num/den*den := by omega
      exact_mod_cast hn
    rw [he,Nat.ceil_natCast]
  · apply (Nat.ceil_eq_iff (Nat.succ_ne_zero (num/den))).mpr
    constructor
    · apply (lt_div_iff₀ hdq).mpr
      have hn : num/den*den<num := by omega
      exact_mod_cast hn
    · apply (div_le_iff₀ hdq).mpr
      have hn : num≤ (num/den+1)*den := by nlinarith
      exact_mod_cast hn

/-- Both output and all arithmetic intermediates are Boolean lists. -/
def ceilNatural (input : RationalBits) : Result :=
  if input.negative then ⟨[],2⟩ else
    let division := divide input.numerator input.denominator
    let remainder := normalize division.remainder
    let rounded : Result := if remainder.digits.isEmpty then
        ⟨division.quotient,1⟩
      else
        let increment := BinaryArithmetic.add false division.quotient [true]
        ⟨increment.digits,increment.work+1⟩
    let normalized := normalize rounded.digits
    ⟨normalized.digits,division.work+remainder.work+rounded.work+normalized.work+4⟩

theorem ceilNatural_value (input : RationalBits) : value (ceilNatural input).digits=⌈input.decode⌉₊ := by
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [ceilNatural,hs,ite_true,value,Nat.ceil_eq_zero.mpr hn]
  | false =>
      have hq := divide_value input.numerator input.denominator input.denominator_positive
      have he : (normalize (divide input.numerator input.denominator).remainder).digits=[] ↔
          value input.numerator%value input.denominator=0 := by rw [normalize_nil_iff,hq.2]
      rw [decode_fraction]
      simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      rw [ceil_fraction _ _ input.denominator_positive]
      simp only [ceilNatural,hs,ite_false,Bool.false_eq_true,normalize_value]
      by_cases hz : value input.numerator%value input.denominator=0
      · simp only [he.mpr hz,List.isEmpty_nil,ite_true,hq.1,hz]
      · have hne : (normalize (divide input.numerator input.denominator).remainder).digits≠[] :=
          fun hh => hz (he.mp hh)
        have hb : (normalize (divide input.numerator input.denominator).remainder).digits.isEmpty=false := by
          simpa only [List.isEmpty_eq_false_iff] using hne
        simp only [hb,ite_false,Bool.false_eq_true,BinaryArithmetic.add_value,value,Bool.toNat_true,Bool.toNat_false,hq.1,hz,
          Nat.mul_zero,Nat.add_zero]











end RationalBits
end AFT.BinaryArithmetic



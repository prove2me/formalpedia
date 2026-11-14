-- Prove2me | solution 1 for AFT.BinaryArithmetic.RationalBits.ceilNatural_le_numerator
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:21:49.357951+00:00
-- url     : https://prove2.me/submissions/4cd4b01f-2fad-4d16-af83-b6bbb053cb30

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalControl
import Mathlib


/-! # Actual binary clipping and natural ceiling

The ceiling uses binary long division, high-zero trimming, and one ripple
increment when the remainder is nonzero. Tests inspect the stored sign or
list constructor, never the decoded rational value.
-/
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
section AFT
section BinaryArithmetic
open AFT
open AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
section RationalBits
open AFT
open AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits















theorem solution (input : RationalBits) :
    ⌈input.decode⌉₊≤ value input.numerator := by
  apply Nat.ceil_le.mpr
  rw [decode_fraction]
  have hd : (1 : ℚ)≤ value input.denominator := by exact_mod_cast input.denominator_positive
  have hp : (0 : ℚ)≤ value input.numerator := by positivity
  cases hs : input.negative with
  | false =>
      simp only [signedValue,ite_false,Bool.false_eq_true,Int.cast_natCast]
      exact div_le_self hp hd
  | true =>
      simp only [signedValue,ite_true,Int.cast_neg,Int.cast_natCast]
      exact (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) (le_trans (by norm_num) hd)).trans hp







end RationalBits
end BinaryArithmetic
end AFT

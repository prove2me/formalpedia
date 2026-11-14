-- Prove2me | solution 1 for AFT.BinaryArithmetic.RationalBits.ceilNatural_work
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:21:35.128782+00:00
-- url     : https://prove2.me/submissions/cc1614f8-9bcb-4a37-a830-93bf5fd43ae6

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
    (ceilNatural input).work≤ 100*(input.numerator.length+input.denominator.length+1)^2 := by
  have hw := divide_work input.numerator input.denominator
  have hq := divide_quotient_length input.numerator input.denominator
  have hr := divide_remainder_length input.numerator input.denominator
  have hl := add_length (divide input.numerator input.denominator).quotient [true] false
  have hm : max (divide input.numerator input.denominator).quotient.length 1≤ input.numerator.length+1 := by omega
  have hp : 1≤ input.numerator.length+input.denominator.length+1 := by omega
  unfold ceilNatural
  split
  · change 2≤ _
    have hh := Nat.one_le_pow 2 _ hp
    omega
  · dsimp only
    split
    · simp only [normalize_work,hq]
      nlinarith [Nat.mul_le_mul_left (input.numerator.length+input.denominator.length+1) hp]
    · simp only [normalize_work,BinaryArithmetic.add_work,List.length_cons,List.length_nil,Nat.zero_add]
      simp only [List.length_cons,List.length_nil,Nat.zero_add] at hl
      nlinarith [Nat.mul_le_mul_left (input.numerator.length+input.denominator.length+1) hp]



end RationalBits
end BinaryArithmetic
end AFT

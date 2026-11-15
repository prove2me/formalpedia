-- Prove2me | solution 1 for AFT.BinaryArithmetic.reduce_work
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T06:15:29.878429+00:00
-- url     : https://prove2.me/submissions/bd7e3e12-f88c-447c-9a4e-29af91e8e2b9

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalData
import Mathlib
import Theorems.Thm_AFT_BinaryArithmetic_gcd_resources
section



/-! Canonical rational data stored as Boolean lists. Proof fields are erased;
semantic reduced height controls the actual operand representation length. -/
namespace AFT.BinaryArithmetic







namespace RationalBits











end RationalBits











set_option maxRecDepth 8192
theorem _root_.AFT.BinaryArithmetic.__p2m_proof_24891d405ab8147719c4 (negative : Bool) (num den : List Bool) (hden : 0 < _root_.AFT.BinaryArithmetic.value den) :
    (_root_.AFT.BinaryArithmetic.reduce negative num den hden).work ≤ 2000*(num.length+den.length+1)^3 := by
  have hg := _root_.AFT.BinaryArithmetic.gcd_resources num den
  have ht := _root_.AFT.BinaryArithmetic.divide_work num (_root_.AFT.BinaryArithmetic.gcd num den).digits
  have hd := _root_.AFT.BinaryArithmetic.divide_work den (_root_.AFT.BinaryArithmetic.gcd num den).digits
  have htl := _root_.AFT.BinaryArithmetic.divide_quotient_length num (_root_.AFT.BinaryArithmetic.gcd num den).digits
  have hdl := _root_.AFT.BinaryArithmetic.divide_quotient_length den (_root_.AFT.BinaryArithmetic.gcd num den).digits
  simp only [_root_.AFT.BinaryArithmetic.reduce,_root_.AFT.BinaryArithmetic.normalize_work]
  rw [htl,hdl]
  have htop : num.length+(_root_.AFT.BinaryArithmetic.gcd num den).digits.length+1 ≤ 2*(num.length+den.length+1) := by omega
  have hbot : den.length+(_root_.AFT.BinaryArithmetic.gcd num den).digits.length+1 ≤ 2*(num.length+den.length+1) := by omega
  have hone : 1 ≤ num.length+den.length+1 := by omega
  nlinarith [hg.2,Nat.pow_le_pow_left htop 2,Nat.pow_le_pow_left hbot 2,
    Nat.mul_le_mul_left ((num.length+den.length+1)^2) hone]

end AFT.BinaryArithmetic

end


set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.AFT.BinaryArithmetic.__p2m_proof_24891d405ab8147719c4) := @_root_.AFT.BinaryArithmetic.__p2m_proof_24891d405ab8147719c4

-- Prove2me | solution 1 for AFT.BinaryArithmetic.gcd_resources
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:18:09.615358+00:00
-- url     : https://prove2.me/submissions/b73e4266-d290-4084-9f1f-585ccc78a7e3

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryEuclid
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryNormalization
import Mathlib


/-! Linear-time removal of high zero digits. -/
namespace AFT.BinaryArithmetic







theorem normalize_length_le (digits : List Bool) : (normalize digits).digits.length ≤ digits.length := by
  rw [normalize_length]
  exact Nat.size_le.mpr (value_lt digits)





end AFT.BinaryArithmetic




/-! A binary implementation of Euclid with an explicit linear-in-bitlength
iteration bound. Each iteration performs two long divisions, which halves
the second nonzero operand. -/
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
section AFT
section BinaryArithmetic
open AFT
open AFT.BinaryArithmetic





theorem _root_.AFT.BinaryArithmetic.remainder_normal (as bs : List Bool) :
    (remainder as bs).digits.length=(value (remainder as bs).digits).size := by
  exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm

theorem _root_.AFT.BinaryArithmetic.remainder_length (as bs : List Bool) (hb : 0 < value bs) :
    (remainder as bs).digits.length ≤ bs.length := by
  change (normalize (divide as bs).remainder).digits.length ≤ _
  rw [normalize_length,(divide_value as bs hb).2]
  exact (Nat.size_le_size (Nat.mod_lt _ hb).le).trans (Nat.size_le.mpr (value_lt bs))

theorem _root_.AFT.BinaryArithmetic.remainder_work (as bs : List Bool) :
    (remainder as bs).work ≤ 30*(as.length+bs.length+1)^2 := by
  have hd := divide_work as bs
  have hl := divide_remainder_length as bs
  simp only [remainder,normalize_work]
  nlinarith







theorem _root_.AFT.BinaryArithmetic.gcdAux_resources (fuel : ℕ) (as bs : List Bool)
    (hbn : bs.length=(value bs).size) (bound : ℕ)
    (ha : as.length ≤ bound) (hb : bs.length ≤ bound) :
    (gcdAux fuel as bs).digits.length ≤ bound ∧
      (gcdAux fuel as bs).work ≤ fuel*(300*(bound+1)^2)+2 := by
  induction fuel generalizing as bs with
  | zero => simpa only [gcdAux,Nat.zero_mul,Nat.zero_add,le_refl,and_true] using ha
  | succ fuel ih =>
    cases bs with
    | nil => simp only [gcdAux];constructor;exact ha;omega
    | cons b tail =>
      have hbpos : 0 < value (b::tail) := by
        by_contra hn
        have hz : value (b::tail)=0 := by omega
        simp [hz] at hbn
      have hfl := remainder_length as (b::tail) hbpos
      have hfw := remainder_work as (b::tail)
      have hfw' : (remainder as (b::tail)).work ≤ 120*(bound+1)^2 := by
        have hm : as.length+(b::tail).length+1 ≤ 2*(bound+1) := by omega
        nlinarith [Nat.pow_le_pow_left hm 2]
      simp only [gcdAux]
      split <;> rename_i he
      · constructor;exact hb
        have hone : 1 ≤ (bound+1)^2 := Nat.one_le_pow _ _ (by omega)
        nlinarith
      · have hfpos : 0 < value (remainder as (b::tail)).digits := by
          have hfn := remainder_normal as (b::tail)
          by_contra hn
          have hz : value (remainder as (b::tail)).digits=0 := by omega
          rw [hz,Nat.size_zero,he] at hfn
          simp at hfn
        have hsl := remainder_length (b::tail) (remainder as (b::tail)).digits hfpos
        have hsw := remainder_work (b::tail) (remainder as (b::tail)).digits
        have hsw' : (remainder (b::tail) (remainder as (b::tail)).digits).work ≤ 120*(bound+1)^2 := by
          have hm : (b::tail).length+(remainder as (b::tail)).digits.length+1 ≤ 2*(bound+1) := by omega
          nlinarith [Nat.pow_le_pow_left hm 2]
        have hr := ih (remainder as (b::tail)).digits
          (remainder (b::tail) (remainder as (b::tail)).digits).digits
          (remainder_normal _ _) (hfl.trans hb) (hsl.trans (hfl.trans hb))
        constructor
        · exact hr.1
        · have hone : 1 ≤ (bound+1)^2 := Nat.one_le_pow _ _ (by omega)
          nlinarith [hr.2]





theorem solution (as bs : List Bool) :
    (_root_.AFT.BinaryArithmetic.gcd as bs).digits.length ≤ max as.length bs.length ∧
      (_root_.AFT.BinaryArithmetic.gcd as bs).work ≤ 1000*(as.length+bs.length+1)^3 := by
  have hn : (normalize bs).digits.length=(value (normalize bs).digits).size := by
    rw [normalize_length,normalize_value]
  have hr := gcdAux_resources (bs.length+1) (normalize as).digits (normalize bs).digits hn
    (as.length+bs.length) ((normalize_length_le as).trans (by omega)) ((normalize_length_le bs).trans (by omega))
  have hl := gcdAux_resources (bs.length+1) (normalize as).digits (normalize bs).digits hn
    (max as.length bs.length) ((normalize_length_le as).trans (Nat.le_max_left ..))
    ((normalize_length_le bs).trans (Nat.le_max_right ..))
  constructor
  · exact hl.1
  · simp only [_root_.AFT.BinaryArithmetic.gcd,normalize_work]
    have hh := hr.2
    have hone : 1 ≤ as.length+bs.length+1 := by omega
    nlinarith [Nat.mul_le_mul_right (300*(as.length+bs.length+1)^2) (show bs.length+1 ≤ as.length+bs.length+1 by omega)]

end BinaryArithmetic
end AFT

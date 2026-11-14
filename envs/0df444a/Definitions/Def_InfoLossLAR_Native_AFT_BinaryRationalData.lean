-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalData
-- name    : InfoLossLAR_Native_AFT_BinaryRationalData
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:10:22.030511+00:00
-- url     : https://prove2.me/theorems/987ae448-3143-4bdd-9126-e9e1b297d468
-- title:
--   Canonical signed binary rational data
-- statement:
--   A rational encoding consists of a sign bit $s$, canonical numerator and denominator digit lists representing $u,v\in\mathbb N$, and conditions $v>0$ and $\gcd(u,v)=1$. Its decoded value is
--
--   $$\operatorname{decode}(s,u,v)=(-1)^s\frac{u}{v}.$$
--
--   The reduction routine uses the binary gcd, division, and normalization operations to produce this representation from supplied numerator and positive-denominator strings. Results pair the rational data with a native operation charge.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalData.lean; migrated native SHA256 3b61e90cabedb20ce7a4ad82b6d23f7fc21b0903ba2f6e470c21ea4c0f3addc0; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryEuclid
import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Mathlib



/-! Canonical rational data stored as Boolean lists. Proof fields are erased;
semantic reduced height controls the actual operand representation length. -/
namespace AFT.BinaryArithmetic

def signedValue (negative : Bool) (digits : List Bool) : ℤ :=
  if negative then -(value digits : ℤ) else (value digits : ℤ)

@[simp] theorem signedValue_natAbs (negative : Bool) (digits : List Bool) :
    (signedValue negative digits).natAbs=value digits := by
  cases negative <;> simp [signedValue]

structure RationalBits where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  numerator_normal : numerator.length=(value numerator).size
  denominator_normal : denominator.length=(value denominator).size
  denominator_positive : 0 < value denominator
  coprime : (value numerator).Coprime (value denominator)

namespace RationalBits

def decode (input : RationalBits) : ℚ :=
  Rat.mk' (signedValue input.negative input.numerator) (value input.denominator)
    input.denominator_positive.ne' (by simpa only [signedValue_natAbs] using input.coprime)

theorem decode_num (input : RationalBits) :
    input.decode.num=signedValue input.negative input.numerator := rfl



theorem decode_fraction (input : RationalBits) :
    input.decode=(signedValue input.negative input.numerator : ℚ)/(value input.denominator : ℚ) := by
  rw [← Rat.num_div_den input.decode]
  rfl



end RationalBits

structure RationalResult where
  data : RationalBits
  work : ℕ

/-- Actual Euclid, two actual binary divisions, then high-zero trimming. -/
def reduce (negative : Bool) (num den : List Bool) (hden : 0 < value den) : RationalResult :=
  let common := gcd num den
  let top := divide num common.digits
  let bottom := divide den common.digits
  let nt := normalize top.quotient
  let nd := normalize bottom.quotient
  have hc : 0 < value common.digits := by
    simpa only [common,gcd_value] using Nat.gcd_pos_of_pos_right (value num) hden
  have ht : value nt.digits=value num/Nat.gcd (value num) (value den) := by
    simpa only [nt,normalize_value,top,common,gcd_value] using (divide_value num common.digits hc).1
  have hd : value nd.digits=value den/Nat.gcd (value num) (value den) := by
    simpa only [nd,normalize_value,bottom,common,gcd_value] using (divide_value den common.digits hc).1
  ⟨{negative := negative,numerator := nt.digits,denominator := nd.digits
    numerator_normal := by dsimp only [nt];rw [normalize_length,normalize_value]
    denominator_normal := by dsimp only [nd];rw [normalize_length,normalize_value]
    denominator_positive := by rw [hd];exact Nat.div_gcd_pos_of_pos_right _ hden
    coprime := by rw [ht,hd];exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hden)},
    common.work+top.work+bottom.work+nt.work+nd.work+8⟩

theorem reduce_numerator (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    value (reduce negative num den hden).data.numerator=value num/Nat.gcd (value num) (value den) := by
  have hc : 0 < value (gcd num den).digits := by rw [gcd_value];exact Nat.gcd_pos_of_pos_right _ hden
  simp only [reduce,normalize_value,(divide_value num (gcd num den).digits hc).1,gcd_value]

theorem reduce_denominator (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    value (reduce negative num den hden).data.denominator=value den/Nat.gcd (value num) (value den) := by
  have hc : 0 < value (gcd num den).digits := by rw [gcd_value];exact Nat.gcd_pos_of_pos_right _ hden
  simp only [reduce,normalize_value,(divide_value den (gcd num den).digits hc).1,gcd_value]

theorem reduce_value (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    (reduce negative num den hden).data.decode=(signedValue negative num : ℚ)/(value den : ℚ) := by
  rw [RationalBits.decode_fraction]
  have hneg : (reduce negative num den hden).data.negative=negative := rfl
  simp only [signedValue,hneg]
  rw [reduce_numerator,reduce_denominator]
  have hc : (Nat.gcd (value num) (value den) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right _ hden).ne'
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,Int.cast_neg,Int.cast_natCast]
  all_goals rw [Nat.cast_div (Nat.gcd_dvd_left ..),Nat.cast_div (Nat.gcd_dvd_right ..)]
  all_goals first | exact hc | field_simp [hc]



end AFT.BinaryArithmetic



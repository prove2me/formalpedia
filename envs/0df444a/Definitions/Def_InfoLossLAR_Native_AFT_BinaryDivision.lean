-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryDivision
-- name    : InfoLossLAR_Native_AFT_BinaryDivision
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:07:48.173547+00:00
-- url     : https://prove2.me/theorems/4a84c274-60c3-4783-b738-9386dd7c0240
-- title:
--   Long division with explicit quotient and remainder
-- statement:
--   Binary long division returns digit lists for a quotient $q$ and remainder $r$, together with the native operation charge. For a positive decoded divisor $v(b)>0$,
--
--   $$v(a)=v(q)v(b)+v(r),\qquad0\le v(r)<v(b).$$
--
--   The algorithm is total on all input strings; the displayed quotient-remainder specification requires a positive divisor. The included estimates track output lengths and the charge of the digit operations.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryDivision.lean; migrated native SHA256 fa47ce69dd7f2cd80cd8e6fb730374cf2aadc791d26a04b9062d02eaa213af57; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinarySubtraction
import Mathlib


/-! Binary long division. Each input digit performs one borrow subtraction.
The divisor is positive in the correctness theorem; the executable algorithm
itself is total, including zero divisors. -/
namespace AFT.BinaryArithmetic

structure QuotientRemainder where
  quotient : List Bool
  remainder : List Bool
  work : ℕ

def divide : List Bool → List Bool → QuotientRemainder
  | [],_ => ⟨[],[],2⟩
  | bit::tail,divisor =>
    let previous := divide tail divisor
    let next := bit::previous.remainder
    let difference := subtract false next divisor
    if difference.borrow then
      ⟨false::previous.quotient,next,previous.work+difference.work+4⟩
    else ⟨true::previous.quotient,difference.digits,previous.work+difference.work+4⟩

theorem divide_balance (as bs : List Bool) (hb : 0 < value bs) :
    value as=value (divide as bs).quotient*value bs+value (divide as bs).remainder ∧
      value (divide as bs).remainder < value bs := by
  induction as with
  | nil => simp [divide,value,hb]
  | cons bit tail ih =>
    have hbit : bit.toNat ≤ 1 := by cases bit <;> decide
    have hnext : value (bit::(divide tail bs).remainder) < 2*value bs := by
      simp only [value];omega
    have hborrow := subtract_borrow (bit::(divide tail bs).remainder) bs
    cases hd : (subtract false (bit::(divide tail bs).remainder) bs).borrow with
    | true =>
      have hsmall := hborrow.mp hd
      simp only [divide,hd,ite_true,value,Bool.toNat_false,Nat.zero_add]
      constructor
      · nlinarith [ih.1]
      · exact hsmall
    | false =>
      have hge : value bs ≤ value (bit::(divide tail bs).remainder) := by
        simp only [hd,Bool.false_eq_true,false_iff] at hborrow
        omega
      have hdiff := subtract_value (bit::(divide tail bs).remainder) bs hge
      simp only [divide,hd,Bool.false_eq_true,ite_false,value,Bool.toNat_true,hdiff]
      simp only [value] at hdiff hge hnext
      constructor
      · nlinarith [ih.1,Nat.sub_add_cancel hge]
      · omega

theorem divide_value (as bs : List Bool) (hb : 0 < value bs) :
    value (divide as bs).quotient=value as/value bs ∧
      value (divide as bs).remainder=value as%value bs := by
  obtain ⟨he,hr⟩ := divide_balance as bs hb
  constructor
  · rw [he,Nat.mul_comm (value (divide as bs).quotient),Nat.mul_add_div hb,Nat.div_eq_of_lt hr,Nat.add_zero]
  · rw [he,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hr]

theorem divide_quotient_length (as bs : List Bool) :
    (divide as bs).quotient.length=as.length := by
  induction as with
  | nil => rfl
  | cons bit tail ih =>
    simp only [divide]
    split <;> simp only [List.length_cons,ih]

theorem divide_remainder_length (as bs : List Bool) :
    (divide as bs).remainder.length ≤ as.length+bs.length := by
  induction as with
  | nil => simp [divide]
  | cons bit tail ih =>
    simp only [divide]
    split
    · simp only [List.length_cons];omega
    · simp only [subtract_length,List.length_cons];omega

theorem divide_work (as bs : List Bool) :
    (divide as bs).work ≤ 20*(as.length+bs.length+1)^2 := by
  induction as with
  | nil =>
    simp only [divide,List.length_nil,Nat.zero_add]
    have hh : 1 ≤ (bs.length+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  | cons bit tail ih =>
    have hl := divide_remainder_length tail bs
    have hm : max ((divide tail bs).remainder.length+1) bs.length ≤ tail.length+bs.length+1 := by omega
    simp only [divide]
    split <;> simp only [subtract_work,List.length_cons] <;> nlinarith

end AFT.BinaryArithmetic



-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryArithmeticProgram
-- name    : InfoLossLAR_Native_AFT_BinaryArithmeticProgram
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:06:10.814186+00:00
-- url     : https://prove2.me/theorems/4153c358-ae9e-4398-941c-70dafe2ce4e2
-- title:
--   Binary digit values, ripple addition, and multiplication
-- statement:
--   Boolean lists represent nonnegative integers with the least significant bit first:
--
--   $$v([])=0,\qquad v(b::s)=b+2v(s),\quad b\in\{0,1\}.$$
--
--   The result type stores an output digit list and a native operation charge. Ripple-carry addition and schoolbook multiplication operate on the supplied digits; addition includes an optional incoming carry. Their accompanying identities identify the decoded values and the addition length and charge.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryArithmeticProgram.lean; migrated native SHA256 7dc99509c98c7eb94777db35443786765be85cf2a3e7eec81c7271850affd225; retained source units selected by Lean oracle.

import Mathlib


/-! # Explicit Boolean-list addition and schoolbook multiplication

The runtime representation is little endian, with harmless high zero bits.
Every arithmetic step below inspects individual Boolean digits. `work` counts
Boolean gates, list constructors, and case tests; no natural-number addition
or multiplication is used to compute the represented result.
-/
namespace AFT.BinaryArithmetic

def value : List Bool → ℕ
  | [] => 0
  | bit::tail => bit.toNat+2*value tail

structure Result where
  digits : List Bool
  work : ℕ

def sumBit (a b carry : Bool) : Bool := (a ^^ b) ^^ carry
def carryBit (a b carry : Bool) : Bool := (a && b) || (carry && (a ^^ b))

theorem fullAdder (a b carry : Bool) :
    (sumBit a b carry).toNat+2*(carryBit a b carry).toNat=a.toNat+b.toNat+carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

/-- Ripple-carry addition. One recursive call is made per input digit. -/
def add (carry : Bool) : List Bool → List Bool → Result
  | [],[] => ⟨if carry then [true] else [],2⟩
  | a::as,[] =>
    let next := add (carryBit a false carry) as []
    ⟨sumBit a false carry::next.digits,next.work+10⟩
  | [],b::bs =>
    let next := add (carryBit false b carry) [] bs
    ⟨sumBit false b carry::next.digits,next.work+10⟩
  | a::as,b::bs =>
    let next := add (carryBit a b carry) as bs
    ⟨sumBit a b carry::next.digits,next.work+10⟩

theorem add_value (as bs : List Bool) (carry : Bool) :
    value (add carry as bs).digits=value as+value bs+carry.toNat := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [add,value]
    | cons b bs ih =>
      have hf := fullAdder false b carry
      simp only [add,value,ih,Bool.toNat_false] at *
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have hf := fullAdder a false carry
      simp only [add,value,ih,Bool.toNat_false] at *
      omega
    | cons b bs =>
      have hf := fullAdder a b carry
      simp only [add,value,ih] at *
      omega

theorem add_length (as bs : List Bool) (carry : Bool) :
    (add carry as bs).digits.length ≤ max as.length bs.length+1 := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [add]
    | cons b bs ih =>
      have hh := ih (carryBit false b carry)
      simp only [add,List.length_cons,List.length_nil] at *
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have hh := ih [] (carryBit a false carry)
      simp only [add,List.length_cons,List.length_nil] at *
      omega
    | cons b bs =>
      have hh := ih bs (carryBit a b carry)
      simp only [add,List.length_cons] at *
      omega

theorem add_work (as bs : List Bool) (carry : Bool) :
    (add carry as bs).work=10*max as.length bs.length+2 := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp [add]
    | cons b bs ih =>
      simp only [add,ih,List.length_cons,List.length_nil,Nat.zero_max]
      omega
  | cons a as ih =>
    cases bs with
    | nil => simp [add,ih];omega
    | cons b bs =>
      simp only [add,ih,List.length_cons]
      omega

/-- Schoolbook multiplication, implemented only by shifts and the ripple
adder above. No whole-integer primitive occurs in the digit computation. -/
def multiply : List Bool → List Bool → Result
  | [],_ => ⟨[],2⟩
  | bit::tail,other =>
    let previous := multiply tail other
    if bit then
      let next := add false other (false::previous.digits)
      ⟨next.digits,previous.work+next.work+3⟩
    else ⟨false::previous.digits,previous.work+3⟩

theorem multiply_value (as bs : List Bool) :
    value (multiply as bs).digits=value as*value bs := by
  induction as with
  | nil => simp [multiply,value]
  | cons a as ih =>
    cases a <;> simp only [multiply,Bool.false_eq_true,ite_false,ite_true,value,
      Bool.toNat_false,Bool.toNat_true,add_value,ih] <;> ring





end AFT.BinaryArithmetic



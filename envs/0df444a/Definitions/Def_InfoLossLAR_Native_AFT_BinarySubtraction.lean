-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinarySubtraction
-- name    : InfoLossLAR_Native_AFT_BinarySubtraction
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:06:54.716828+00:00
-- url     : https://prove2.me/theorems/c0c68ba5-d7ad-4522-a4f4-af711e91f43d
-- title:
--   Borrow subtraction on binary lists
-- statement:
--   Binary subtraction returns a digit list $r$, a final borrow bit $\beta$, and a native operation charge. For input strings $a,b$, incoming borrow $c\in\{0,1\}$, and $m=\max\{|a|,|b|\}$, the arithmetic balance is
--
--   $$v(r)+v(b)+c=v(a)+2^m\beta.$$
--
--   The routine processes individual digits. Its final borrow also records the comparison needed by division and signed arithmetic.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinarySubtraction.lean; migrated native SHA256 3b3901f2c3e1e412c1501cc06899fc7efa890644c7d586368427e7d4e048644c; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryArithmeticProgram
import Mathlib


/-! Explicit borrow subtraction and comparison, with no integer primitive. -/
namespace AFT.BinaryArithmetic

structure Difference where
  digits : List Bool
  borrow : Bool
  work : ℕ

def borrowBit (a b carry : Bool) : Bool := (!a && (b || carry)) || (b && carry)

theorem fullSubtractor (a b carry : Bool) :
    (sumBit a b carry).toNat+b.toNat+carry.toNat = a.toNat+2*(borrowBit a b carry).toNat := by
  cases a <;> cases b <;> cases carry <;> decide

def subtract (carry : Bool) : List Bool → List Bool → Difference
  | [],[] => ⟨[],carry,2⟩
  | a::as,[] =>
    let next := subtract (borrowBit a false carry) as []
    ⟨sumBit a false carry::next.digits,next.borrow,next.work+10⟩
  | [],b::bs =>
    let next := subtract (borrowBit false b carry) [] bs
    ⟨sumBit false b carry::next.digits,next.borrow,next.work+10⟩
  | a::as,b::bs =>
    let next := subtract (borrowBit a b carry) as bs
    ⟨sumBit a b carry::next.digits,next.borrow,next.work+10⟩

theorem subtract_length (as bs : List Bool) (carry : Bool) :
    (subtract carry as bs).digits.length = max as.length bs.length := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp [subtract]
    | cons b bs ih => simp [subtract,ih]
  | cons a as ih =>
    cases bs with
    | nil => simp [subtract,ih]
    | cons b bs => simp [subtract,ih,Nat.succ_max_succ]

theorem subtract_work (as bs : List Bool) (carry : Bool) :
    (subtract carry as bs).work=10*max as.length bs.length+2 := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp [subtract]
    | cons b bs ih => simp [subtract,ih];omega
  | cons a as ih =>
    cases bs with
    | nil => simp [subtract,ih];omega
    | cons b bs => simp [subtract,ih,Nat.succ_max_succ];omega

theorem subtract_balance (as bs : List Bool) (carry : Bool) :
    value (subtract carry as bs).digits+value bs+carry.toNat =
      value as+(subtract carry as bs).borrow.toNat*2^(max as.length bs.length) := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp [subtract,value]
    | cons b bs ih =>
      have hh := ih (borrowBit false b carry)
      have hf := fullSubtractor false b carry
      simp only [subtract,value,List.length_cons,List.length_nil,Nat.zero_max,Bool.toNat_false] at *
      rw [pow_succ]
      nlinarith
  | cons a as ih =>
    cases bs with
    | nil =>
      have hh := ih [] (borrowBit a false carry)
      have hf := fullSubtractor a false carry
      simp only [subtract,value,List.length_cons,List.length_nil,Nat.max_zero,Bool.toNat_false] at *
      rw [pow_succ]
      nlinarith
    | cons b bs =>
      have hh := ih bs (borrowBit a b carry)
      have hf := fullSubtractor a b carry
      simp only [subtract,value,List.length_cons,Nat.succ_max_succ] at *
      rw [pow_succ]
      nlinarith

theorem value_lt (digits : List Bool) : value digits < 2^digits.length := by
  induction digits with
  | nil => simp [value]
  | cons b tail ih =>
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [value,List.length_cons,pow_succ]
    omega

theorem subtract_borrow (as bs : List Bool) :
    (subtract false as bs).borrow = true ↔ value as < value bs := by
  have hh := subtract_balance as bs false
  have hv := value_lt (subtract false as bs).digits
  rw [subtract_length] at hv
  simp only [Bool.toNat_false,Nat.add_zero] at hh
  cases hb : (subtract false as bs).borrow <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,zero_mul,one_mul] at hh
  · simp only [Bool.false_eq_true,false_iff];omega
  · simp only [true_iff];omega

theorem subtract_value (as bs : List Bool) (h : value bs ≤ value as) :
    value (subtract false as bs).digits=value as-value bs := by
  have hn : (subtract false as bs).borrow=false := by
    cases hb : (subtract false as bs).borrow
    · rfl
    · exact False.elim ((subtract_borrow as bs).mp hb |>.not_ge h)
  have hh := subtract_balance as bs false
  simp only [hn,Bool.toNat_false,zero_mul,Nat.add_zero] at hh
  omega

end AFT.BinaryArithmetic



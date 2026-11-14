-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryNormalization
-- name    : InfoLossLAR_Native_AFT_BinaryNormalization
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:07:38.964679+00:00
-- url     : https://prove2.me/theorems/4b8d1e51-7f42-47bd-873c-08065f6b5f94
-- title:
--   Removing redundant high zero digits
-- statement:
--   The normalization procedure removes redundant high zero digits from a list written with the least significant bit first. Its result $N(s)$ satisfies
--
--   $$v(N(s))=v(s),\qquad |N(s)|=\operatorname{bitsize}(v(s)).$$
--
--   Zero is represented by the empty list. The result also carries the native charge for this digit traversal.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryNormalization.lean; migrated native SHA256 8e1a8bf2d8c6536a2dd6b55b7e200310d86c0008b555def035b82504c76de78f; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinarySubtraction
import Mathlib


/-! Linear-time removal of high zero digits. -/
namespace AFT.BinaryArithmetic

def normalize : List Bool → Result
  | [] => ⟨[],2⟩
  | bit::tail =>
    let previous := normalize tail
    match previous.digits with
    | [] => ⟨if bit then [true] else [],previous.work+4⟩
    | next::rest => ⟨bit::next::rest,previous.work+4⟩

theorem normalize_value (digits : List Bool) : value (normalize digits).digits=value digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
    simp only [normalize]
    split <;> rename_i he
    · rw [he] at ih
      cases bit <;> simp only [ite_false,ite_true,Bool.false_eq_true,value,Bool.toNat_false,Bool.toNat_true] at * <;> omega
    · simp only [value]
      rw [← ih,he]
      rfl

theorem normalize_length (digits : List Bool) :
    (normalize digits).digits.length=(value digits).size := by
  induction digits with
  | nil => simp [normalize,value]
  | cons bit tail ih =>
    have hv := normalize_value tail
    simp only [normalize]
    split <;> rename_i he
    · rw [he] at ih hv
      simp only [value] at hv
      cases bit <;> simp [value,hv.symm]
    · have ht : value tail ≠ 0 := by
        intro ht
        rw [ht,Nat.size_zero,he] at ih
        simp at ih
      have hn : Nat.bit bit (value tail) ≠ 0 := by
        rw [Nat.bit_val]
        have hbit : bit.toNat ≤ 1 := by cases bit <;> decide
        omega
      have hs := Nat.size_bit hn
      rw [he] at ih
      simp only [List.length_cons] at ih
      simp only [List.length_cons,value]
      rw [Nat.bit_val] at hs
      have hvEq : bit.toNat+2*value tail=2*value tail+bit.toNat := by omega
      rw [hvEq,hs]
      omega



theorem normalize_nil_iff (digits : List Bool) : (normalize digits).digits=[] ↔ value digits=0 := by
  rw [← List.length_eq_zero_iff,normalize_length]
  exact Nat.size_eq_zero

theorem normalize_work (digits : List Bool) : (normalize digits).work=4*digits.length+2 := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
    simp only [normalize]
    split <;> simp only [List.length_cons] <;> omega

end AFT.BinaryArithmetic



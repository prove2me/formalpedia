-- Prove2me | Definitions.Def_LeanPool_Champernowne_CountExtras
-- name    : LeanPool_Champernowne_CountExtras
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:36:18.524005+00:00
-- url     : https://prove2.me/theorems/837ae081-cf72-4c8b-8c0f-a419c822b83c
-- title:
--   Count Extras
-- statement:
--   Definitions and structural lemmas for Count Extras, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Theorems.Thm_Champernowne_length_bigDigits_eq

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
theorem lt_of_mem_bigDigits {b n d : ℕ} (hb : 1 < b)
    (hd : d ∈ bigDigits b n) : d < b :=
  Nat.digits_lt_base hb (List.mem_reverse.mp hd)
theorem head_bigDigits_ne_zero {b n : ℕ} (hn : n ≠ 0) :
    (bigDigits b n).head? ≠ some 0 := by
  have hnil : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  change (Nat.digits b n).reverse.head? ≠ some 0
  rw [← List.getLast?_eq_head?_reverse, List.getLast?_eq_getLast_of_ne_nil hnil]
  simpa using Nat.getLast_digit_ne_zero b hn
theorem ofDigits_reverse_bigDigits (b n : ℕ) :
    Nat.ofDigits b (bigDigits b n).reverse = n := by
  simp [bigDigits, Nat.ofDigits_digits]
theorem digits_ofDigits_reverse {b : ℕ} (hb : 1 < b) {l : List ℕ}
    (hlt : ∀ d ∈ l, d < b) (hhead : l.head? ≠ some 0) :
    Nat.digits b (Nat.ofDigits b l.reverse) = l.reverse := by
  refine Nat.digits_ofDigits b hb l.reverse
    (fun d hd => hlt d (List.mem_reverse.mp hd)) ?_
  intro h hgl0
  apply hhead
  have h? : l.reverse.getLast? = l.head? := by
    rw [List.getLast?_eq_head?_reverse, List.reverse_reverse]
  rw [← h?, List.getLast?_eq_getLast_of_ne_nil h, hgl0]
theorem bigDigits_ofDigits_reverse {b : ℕ} (hb : 1 < b) {l : List ℕ}
    (hlt : ∀ d ∈ l, d < b) (hhead : l.head? ≠ some 0) :
    bigDigits b (Nat.ofDigits b l.reverse) = l := by
  simp only [bigDigits, digits_ofDigits_reverse hb hlt hhead,
    List.reverse_reverse]
theorem ofDigits_reverse_mem_Ico {b m : ℕ} (hb : 1 < b) (hm : 0 < m)
    {l : List ℕ} (hlen : l.length = m) (hlt : ∀ d ∈ l, d < b)
    (hhead : l.head? ≠ some 0) :
    Nat.ofDigits b l.reverse ∈ Finset.Ico (b ^ (m - 1)) (b ^ m) := by
  have hlength : (Nat.digits b (Nat.ofDigits b l.reverse)).length = m := by
    rw [digits_ofDigits_reverse hb hlt hhead, List.length_reverse, hlen]
  rw [Finset.mem_Ico]
  exact ⟨(Nat.lt_digits_length_iff hb _).mp (by omega),
    (Nat.digits_length_le_iff hb _).mp (by omega)⟩
def digitEquiv {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    Finset.Ico (b ^ (m - 1)) (b ^ m) ≃
    {l : List ℕ // l.length = m ∧ (∀ d ∈ l, d < b) ∧ l.head? ≠ some 0} where
  toFun n :=
    have hn := Finset.mem_Ico.mp n.2
    ⟨bigDigits b n, length_bigDigits_eq hb hn.1 hn.2,
      fun _ hd => lt_of_mem_bigDigits hb hd,
      head_bigDigits_ne_zero (by
        have hP : 0 < b ^ (m - 1) := pow_pos (by omega) _
        have h1 := hn.1
        omega)⟩
  invFun l := ⟨Nat.ofDigits b l.1.reverse,
    ofDigits_reverse_mem_Ico hb hm l.2.1 l.2.2.1 l.2.2.2⟩
  left_inv n := Subtype.ext (ofDigits_reverse_bigDigits b n)
  right_inv l := Subtype.ext (bigDigits_ofDigits_reverse hb l.2.2.1 l.2.2.2)
end Champernowne



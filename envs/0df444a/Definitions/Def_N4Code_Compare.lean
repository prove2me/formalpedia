-- Prove2me | Definitions.Def_N4Code_Compare
-- name    : N4Code_Compare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:02:46.532068+00:00
-- url     : https://prove2.me/theorems/f8c57bf0-b22c-5653-86cc-ae4d3e709d02
-- title:
--   Compare
-- statement:
--   Definitions and structural lemmas for Compare, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_N4Code_dRow_eq_indicator_sum

set_option autoImplicit true
namespace N4Code
lemma flipBit_involutive {n : ℕ} (t : Fin n) (y : Word n) : flipBit t (flipBit t y) = y := by
  funext u
  by_cases h : u = t <;> simp [flipBit, h]
lemma sum_split_at {n : ℕ} (f : Fin n → ℕ) (t : Fin n) :
    (∑ u : Fin n, f u) = (∑ u ∈ (Finset.univ.erase t), f u) + f t := by
  exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ t)).symm
lemma dRow_flip_le_add_one {n : ℕ} (C : Code n) (i : Fin 4) (t : Fin n) (y : Word n) :
    dRow C i (flipBit t y) ≤ dRow C i y + 1 ∧ dRow C i y ≤ dRow C i (flipBit t y) + 1 := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  have hsplit_new := sum_split_at
    (fun u : Fin n => if colBit i (C u) ≠ flipBit t y u then 1 else 0) t
  have hsplit_old := sum_split_at
    (fun u : Fin n => if colBit i (C u) ≠ y u then 1 else 0) t
  have hS : (∑ u ∈ (Finset.univ.erase t), if colBit i (C u) ≠ flipBit t y u then 1 else 0) =
      ∑ u ∈ (Finset.univ.erase t), if colBit i (C u) ≠ y u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have ht : u ≠ t := (Finset.mem_erase.mp hu).1
    simp [flipBit, ht]
  have hnewt : (if colBit i (C t) ≠ flipBit t y t then 1 else 0) ≤
      (if colBit i (C t) ≠ y t then 1 else 0) + 1 := by
    by_cases h : colBit i (C t) = y t <;> by_cases h2 : colBit i (C t) ≠ flipBit t y t <;>
      simp [flipBit, h]
  have holdt : (if colBit i (C t) ≠ y t then 1 else 0) ≤
      (if colBit i (C t) ≠ flipBit t y t then 1 else 0) + 1 := by
    by_cases h : colBit i (C t) = flipBit t y t <;> by_cases h2 : colBit i (C t) ≠ y t <;>
      simp [flipBit, h, h2]
  constructor
  · rw [hsplit_new, hsplit_old, hS]
    omega
  · rw [hsplit_old, hsplit_new, hS]
    omega
lemma min3_add_one (a b c : ℕ) : min (a + 1) (min (b + 1) (c + 1)) = min a (min b c) + 1 := by
  omega
lemma min3_le_add_one {a b c a' b' c' : ℕ} (h1 : a' ≤ a + 1) (h2 : b' ≤ b + 1)
    (h3 : c' ≤ c + 1) : min a' (min b' c') ≤ min a (min b c) + 1 := by
  calc
    min a' (min b' c') ≤ min (a + 1) (min (b + 1) (c + 1)) := by
      apply le_min
      · exact le_trans (Nat.min_le_left _ _) h1
      · apply le_min
        · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_left _ _) h2)
        · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) h3)
    _ = min a (min b c) + 1 := min3_add_one a b c
lemma dO_le_dOp_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dO C y ≤ dOp C t y + 1 := by
  unfold dOp dO
  apply min3_le_add_one
  · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).2
  · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).2
  · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).2
lemma dP_le_dPp_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dP C y ≤ dPp C t y + 1 := by
  unfold dPp dP
  exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).2
lemma Y13_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y1 C t (flipBit t y) ∨ Y3 C t (flipBit t y)) → (Y1 C t y ∨ Y3 C t y) := by
  intro hy
  rcases hy with hy | hy
  · rcases hy with hy | hy
    · -- Y1 (F1 y), first disjunct: dOp y ≤ dPp y ∧ dPp y < dP y
      have hOp_le_Pp : dOp C t y ≤ dPp C t y := by
        simpa [dOp, dPp] using hy.1
      have hPp_lt_P : dPp C t y < dP C y := by
        simpa [dPp, flipBit_involutive] using hy.2
      have hdO_le : dO C y ≤ dOp C t y + 1 := dO_le_dOp_add_one C t y
      have hdP_le : dP C y ≤ dPp C t y + 1 := dP_le_dPp_add_one C t y
      by_cases h1 : dO C y ≤ dPp C t y
      · exact Or.inl (Or.inr ⟨h1, le_of_lt hPp_lt_P, hOp_le_Pp⟩)
      · have hOp_eq_Pp : dOp C t y = dPp C t y := by omega
        have hP_eq_dO : dP C y = dO C y := by omega
        exact Or.inr ⟨hOp_eq_Pp.symm, hPp_lt_P, hP_eq_dO⟩
    · -- Y1 (F1 y), second disjunct: dOp y ≤ dP y ∧ dP y ≤ dPp y ∧ dO y ≤ dP y
      have hOp_le_P : dOp C t y ≤ dP C y := by
        simpa [dOp, dPp, flipBit_involutive] using hy.1
      have hP_le_Pp : dP C y ≤ dPp C t y := by
        simpa [dPp, flipBit_involutive] using hy.2.1
      have hO_le_P : dO C y ≤ dP C y := by
        simpa [dOp, dPp, flipBit_involutive] using hy.2.2
      by_cases h2 : dP C y < dPp C t y
      · exact Or.inl (Or.inl ⟨hO_le_P, h2⟩)
      · have hP_eq_Pp : dP C y = dPp C t y := le_antisymm hP_le_Pp (le_of_not_gt h2)
        exact Or.inl (Or.inr ⟨by rw [← hP_eq_Pp]; exact hO_le_P, by rw [hP_eq_Pp],
          by rw [← hP_eq_Pp]; exact hOp_le_P⟩)
  · -- Y3 (F1 y): dP y = dO y ∧ dP y < dPp y ∧ dPp y = dOp y
    rcases hy with ⟨h1, h2, h3⟩
    have hP_eq_O : dP C y = dO C y := by
      simpa [dOp, dPp, flipBit_involutive] using h1
    have hP_lt_Pp : dP C y < dPp C t y := by
      simpa [dPp, flipBit_involutive] using h2
    have hPp_eq_Op : dPp C t y = dOp C t y := by
      simpa [dOp, dPp, flipBit_involutive] using h3
    exact Or.inl (Or.inl ⟨by rw [hP_eq_O], hP_lt_Pp⟩)
lemma Y13_complement_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∨ Y3 C t y) → ¬ (Y1 C t (flipBit t y) ∨ Y3 C t (flipBit t y)) := by
  intro hnot h
  exact hnot (Y13_closed C t y h)
theorem g1_bijective {n : ℕ} (C _C' : Code n) (t : Fin n) :
    Function.Bijective (g1 C t) := by
  let h : Word n → Word n := fun z => if Y1 C t z ∨ Y3 C t z then z else flipBit t z
  have hleft : ∀ y : Word n, h (g1 C t y) = y := by
    intro y
    by_cases hy : Y1 C t y ∨ Y3 C t y
    · simp [g1, h, hy]
    · have hcl := Y13_complement_closed C t y hy
      simp [g1, h, hy, hcl, flipBit_involutive t y]
  have hright : ∀ z : Word n, g1 C t (h z) = z := by
    intro z
    by_cases hz : Y1 C t z ∨ Y3 C t z
    · simp [g1, h, hz]
    · have hcl := Y13_complement_closed C t z hz
      simp [g1, h, hz, hcl, flipBit_involutive t z]
  refine ⟨?inj, ?surj⟩
  · intro a b hab
    rw [← hleft a, ← hleft b, hab]
  · intro z
    exact ⟨h z, hleft z⟩
noncomputable def g1Equiv {n : ℕ} (C : Code n) (t : Fin n) : Word n ≃ Word n :=
  Equiv.ofBijective (g1 C t) (g1_bijective C C t)
end N4Code



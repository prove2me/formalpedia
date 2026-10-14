-- Prove2me | solution 1 for Apery.inner_table_84_89
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:05:19.641816+00:00
-- url     : https://prove2.me/submissions/1893759d-c277-4568-9ce7-35f4bb986ca6

/-
# Inner table pieces 84-89 (source `Apery/Growth/InnerTable.lean`)

The generated piece lemmas `inPiece_84`...`inPiece_89` and the block assembly,
reproduced verbatim from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0
(split into size-limited blocks for the platform compile budget); the nine continuous
interval counts come from the platform theorem `Apery.ccount_cc` and the window
expansion from `Apery.Ein_expand`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_ccount_cc
import Theorems.Thm_Apery_Ein_expand

set_option autoImplicit false

section Port0
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

namespace Apery

lemma sum_range_tri (t : ℚ) (L : ℕ) :
    ∑ i ∈ range L, ((t - 2 * i) / 2) = (L : ℚ) * (t - L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma psiR_eq (k β : ℤ) : psiR k β = (lrow k β : ℚ) * (((k - β : ℤ) : ℚ) - lrow k β + 1) / 2 := by
  unfold psiR
  rw [← sum_range_tri]
  refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring

/-! ### Closed forms of the interval counts -/

theorem toNat_cast_q (a : ℤ) : ((a.toNat : ℕ) : ℚ) = max (a : ℚ) 0 := by
  have := Int.toNat_eq_max a
  have h2 : (((a.toNat : ℕ) : ℤ) : ℚ) = ((max a 0 : ℤ) : ℚ) := by rw [this]
  push_cast at h2; exact h2

lemma cc00 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 0 = 1 / 2 := (ccount_cc hf0 hf1 hg0 hg1).1
lemma cc01 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 1 = min g (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.1
lemma cc02 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 2 = max 0 (g - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.1
lemma cc10 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 0 = min f (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.1
lemma cc20 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 0 = max 0 (f - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.1
lemma cc11 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 1 = min (min f g) (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.1
lemma cc12 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.1
lemma cc21 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.2.1
lemma cc22 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 2 = max 0 (min f g - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.2.2

theorem inPiece_84 (x : ℝ) (h1 : ((330) / 23 : ℝ) ≤ x) (h2 : x < ((29) / 2 : ℝ)) :
    Ein x (33) = ((723) / 40 : ℝ) * x + ((-417) / 2 : ℝ) := by
  rw [Ein_expand (33) (q := 14) (q' := 1) (μ := 26) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((14 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((14 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-14) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_85 (x : ℝ) (h1 : ((29) / 2 : ℝ) ≤ x) (h2 : x < ((540) / 37 : ℝ)) :
    Ein x (33) = ((763) / 40 : ℝ) * x + ((-223) : ℝ) := by
  rw [Ein_expand (33) (q := 14) (q' := 1) (μ := 26) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((14 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((14 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-29) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_86 (x : ℝ) (h1 : ((540) / 37 : ℝ) ≤ x) (h2 : x < ((340) / 23 : ℝ)) :
    Ein x (33) = ((837) / 40 : ℝ) * x + ((-250) : ℝ) := by
  rw [Ein_expand (33) (q := 14) (q' := 1) (μ := 27) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((14 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((14 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-29) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_87 (x : ℝ) (h1 : ((340) / 23 : ℝ) ≤ x) (h2 : x < ((640) / 43 : ℝ)) :
    Ein x (34) = ((791) / 40 : ℝ) * x + ((-233) : ℝ) := by
  rw [Ein_expand (34) (q := 14) (q' := 1) (μ := 27) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((14 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((14 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-29) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_88 (x : ℝ) (h1 : ((640) / 43 : ℝ) ≤ x) (h2 : x < (15 : ℝ)) :
    Ein x (34) = ((331) / 20 : ℝ) * x + ((-185) : ℝ) := by
  rw [Ein_expand (34) (q := 14) (q' := 1) (μ := 27) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((14 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((14 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-29) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = (((43) / 40 : ℝ) * x + ((-16) : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((14 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_89 (x : ℝ) (h1 : (15 : ℝ) ≤ x) (h2 : x < ((560) / 37 : ℝ)) :
    Ein x (34) = ((157) / 10 : ℝ) * x + ((-200) : ℝ) := by
  rw [Ein_expand (34) (q := 15) (q' := 1) (μ := 27) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((15 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((15 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-15) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = ((1 : ℝ) * x + ((-15) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((15 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring

theorem inner_table_84_89 : ∀ i, 84 ≤ i → i < 90 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i _ hi x hx
  interval_cases i
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_84 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_85 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_86 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_87 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_88 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_89 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith

end Apery
end Port0


open Finset in
/-- The platform target `Apery.inner_table_84_89`, restated at top level as `solution`. -/
theorem solution : ∀ i, 84 ≤ i → i < 90 → ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    Apery.Ein x (Apery.kIn i) = Apery.gIn i x :=
  Apery.inner_table_84_89

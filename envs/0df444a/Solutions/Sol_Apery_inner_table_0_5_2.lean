-- Prove2me | solution 2 for Apery.inner_table_0_5
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:07:54.704117+00:00
-- url     : https://prove2.me/submissions/75e166cb-e7af-4a70-ab45-1a98ed8adfe2

/-
# Inner table pieces 0-5 (source `Apery/Growth/InnerTable.lean`)

The generated piece lemmas `inPiece_0`...`inPiece_5` and the block assembly,
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

theorem inPiece_0 (x : ℝ) (h1 : (3 : ℝ) ≤ x) (h2 : x < ((70) / 23 : ℝ)) :
    Ein x (2) = ((18) / 5 : ℝ) * x + ((-6) : ℝ) := by
  rw [Ein_expand (2) (q := 3) (q' := 0) (μ := 5) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_1 (x : ℝ) (h1 : ((70) / 23 : ℝ) ≤ x) (h2 : x < ((120) / 37 : ℝ)) :
    Ein x (3) = ((49) / 20 : ℝ) * x + ((-5) / 2 : ℝ) := by
  rw [Ein_expand (3) (q := 3) (q' := 0) (μ := 5) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_2 (x : ℝ) (h1 : ((120) / 37 : ℝ) ≤ x) (h2 : x < ((10) / 3 : ℝ)) :
    Ein x (3) = ((283) / 40 : ℝ) * x + ((-35) / 2 : ℝ) := by
  rw [Ein_expand (3) (q := 3) (q' := 0) (μ := 6) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_3 (x : ℝ) (h1 : ((10) / 3 : ℝ) ≤ x) (h2 : x < ((80) / 23 : ℝ)) :
    Ein x (4) = ((277) / 40 : ℝ) * x + ((-17) : ℝ) := by
  rw [Ein_expand (4) (q := 3) (q' := 0) (μ := 6) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_4 (x : ℝ) (h1 : ((80) / 23 : ℝ) ≤ x) (h2 : x < ((7) / 2 : ℝ)) :
    Ein x (5) = ((231) / 40 : ℝ) * x + ((-13) : ℝ) := by
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 6) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-3) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_5 (x : ℝ) (h1 : ((7) / 2 : ℝ) ≤ x) (h2 : x < ((160) / 43 : ℝ)) :
    Ein x (5) = ((271) / 40 : ℝ) * x + ((-33) / 2 : ℝ) := by
  rw [Ein_expand (5) (q := 3) (q' := 0) (μ := 6) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((3 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((3 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-7) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((3 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring

theorem inner_table_0_5 : ∀ i, 0 ≤ i → i < 6 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i _ hi x hx
  interval_cases i
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_0 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_1 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_2 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_3 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_4 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_5 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith

end Apery
end Port0


open Finset in
/-- The platform target `Apery.inner_table_0_5`, restated at top level as `solution`. -/
theorem solution : ∀ i, 0 ≤ i → i < 6 → ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    Apery.Ein x (Apery.kIn i) = Apery.gIn i x :=
  Apery.inner_table_0_5

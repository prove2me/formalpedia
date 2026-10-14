-- Prove2me | solution 1 for Apery.inner_table_120_124
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T23:09:38.055075+00:00
-- url     : https://prove2.me/submissions/35c3c1cd-5c88-4afc-81ee-5dbcee3309da

/-
# Inner table pieces 120-124 (source `Apery/Growth/Innertable.lean`)

The generated piece lemmas `inPiece_120`...`inPiece_124` and the block assembly, reproduced
verbatim from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0 (blocks of 8 pieces,
sized for the platform compile budget); the nine continuous interval counts come from
`Apery.ccount_cc` and the window expansion from `Apery.Ein_expand`.
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

theorem inPiece_120 (x : ℝ) (h1 : ((440) / 23 : ℝ) ≤ x) (h2 : x < ((720) / 37 : ℝ)) :
    Ein x (45) = ((353) / 20 : ℝ) * x + ((-354) : ℝ) := by
  rw [Ein_expand (45) (q := 19) (q' := 1) (μ := 35) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((19 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((19 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-19) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = ((1 : ℝ) * x + ((-19) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_121 (x : ℝ) (h1 : ((720) / 37 : ℝ) ≤ x) (h2 : x < ((39) / 2 : ℝ)) :
    Ein x (45) = ((891) / 40 : ℝ) * x + ((-444) : ℝ) := by
  rw [Ein_expand (45) (q := 19) (q' := 1) (μ := 36) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((19 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((19 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-19) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_122 (x : ℝ) (h1 : ((39) / 2 : ℝ) ≤ x) (h2 : x < ((840) / 43 : ℝ)) :
    Ein x (45) = ((931) / 40 : ℝ) * x + ((-927) / 2 : ℝ) := by
  rw [Ein_expand (45) (q := 19) (q' := 1) (μ := 36) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((19 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((19 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-39) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_123 (x : ℝ) (h1 : ((840) / 43 : ℝ) ≤ x) (h2 : x < ((450) / 23 : ℝ)) :
    Ein x (45) = ((401) / 20 : ℝ) * x + ((-801) / 2 : ℝ) := by
  rw [Ein_expand (45) (q := 19) (q' := 1) (μ := 36) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((19 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((19 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-39) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = (((43) / 40 : ℝ) * x + ((-21) : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring
theorem inPiece_124 (x : ℝ) (h1 : ((450) / 23 : ℝ) ≤ x) (h2 : x < (20 : ℝ)) :
    Ein x (46) = ((189) / 10 : ℝ) * x + ((-378) : ℝ) := by
  rw [Ein_expand (46) (q := 19) (q' := 1) (μ := 36) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((19 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((19 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-39) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + ((-1) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 1 = (((43) / 40 : ℝ) * x + ((-21) : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((19 : ℕ) : ℝ)) (3 / 40 * x - ((1 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  simp only [bIn, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, psiR_eq, lrow, toNat_cast_q]
  push_cast
  norm_num
  ring

theorem inner_table_120_124 : ∀ i, 120 ≤ i → i < 125 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  intro i _ hi x hx
  interval_cases i
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_120 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_121 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_122 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_123 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tIn, tInL, kIn, kInL, gIn, aInL, bInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := inPiece_124 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith

end Apery
end Port0


open Finset in
/-- The platform target `Apery.inner_table_120_124`, restated at top level as `solution`. -/
theorem solution : ∀ i, 120 ≤ i → i < 125 → ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    Apery.Ein x (Apery.kIn i) = Apery.gIn i x :=
  Apery.inner_table_120_124

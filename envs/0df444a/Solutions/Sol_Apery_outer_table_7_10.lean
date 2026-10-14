-- Prove2me | solution 1 for Apery.outer_table_7_10
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T17:30:37.603644+00:00
-- url     : https://prove2.me/submissions/8130ab5f-dc21-40ab-86e0-a012dba52c44

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The outer table, pieces 7-10 (source `Apery/Growth/OuterTable.lean`)

This file proves the platform theorem `Apery.outer_table_7_10`: on the next four pieces of the grid $(2, 80/37, 5/2, 100/37)$ the
continuous outer profile agrees with the affine table. The generated pieces
`outPiece_7`...`outPiece_10` and the block assembly are reproduced verbatim from
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth/OuterTable.lean`
(the table is split into small blocks for submission size); the nine continuous interval
counts come from the platform theorem `Apery.ccount_cc` and the window expansion from
`Apery.Eout_expand`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_ccount_cc
import Theorems.Thm_Apery_Eout_expand

set_option autoImplicit false

section Port0
/-!
# Outer table pieces 7-10 (source `Apery/Growth/OuterTable.lean`)

The generated piece lemmas `outPiece_7`...`outPiece_10` and the block assembly,
reproduced verbatim from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0 (split for
submission size; the nine continuous interval counts come from the platform theorem
`Apery.ccount_cc`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

namespace Apery

lemma cc00 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 0 = 1 / 2 := (ccount_cc hf0 hf1 hg0 hg1).1
lemma cc01 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 1 = min g (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.1
lemma cc02 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 0 2 = max 0 (g - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.1
lemma cc10 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 0 = min f (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.1
lemma cc20 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 0 = max 0 (f - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.1
lemma cc11 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 1 = min (min f g) (1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.1
lemma cc12 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.1
lemma cc21 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.2.1
lemma cc22 {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) : ccount f g 2 2 = max 0 (min f g - 1 / 2) := (ccount_cc hf0 hf1 hg0 hg1).2.2.2.2.2.2.2.2

theorem outPiece_7 (x : ℝ) (h1 : ((80) / 43 : ℝ) ≤ x) (h2 : x < (2 : ℝ)) :
    Eout x = ((51) / 10 : ℝ) * x + ((-3) : ℝ) := by
  rw [Eout_expand (q := 1) (q' := 0) (μ := 3) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((1 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((1 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-3) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = (((43) / 40 : ℝ) * x + ((-2) : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((1 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have em : max 0 (13 / 10 * x - 2) = (((13) / 10 : ℝ) * x + ((-2) : ℝ)) := by
    (try simp only [max_def]); (try split_ifs) <;> linarith
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, em]
  simp only [bGO, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, GO, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring_nf
theorem outPiece_8 (x : ℝ) (h1 : (2 : ℝ) ≤ x) (h2 : x < ((80) / 37 : ℝ)) :
    Eout x = ((17) / 4 : ℝ) * x + ((-5) : ℝ) := by
  rw [Eout_expand (q := 2) (q' := 0) (μ := 3) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((2 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((2 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-2) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = ((1 : ℝ) * x + ((-2) : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have em : max 0 (13 / 10 * x - 2) = (((13) / 10 : ℝ) * x + ((-2) : ℝ)) := by
    (try simp only [max_def]); (try split_ifs) <;> linarith
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, em]
  simp only [bGO, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, GO, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring_nf
theorem outPiece_9 (x : ℝ) (h1 : ((80) / 37 : ℝ) ≤ x) (h2 : x < ((5) / 2 : ℝ)) :
    Eout x = ((429) / 40 : ℝ) * x + ((-19) : ℝ) := by
  rw [Eout_expand (q := 2) (q' := 0) (μ := 4) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((2 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((2 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((1 : ℝ) * x + ((-2) : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have em : max 0 (13 / 10 * x - 2) = (((13) / 10 : ℝ) * x + ((-2) : ℝ)) := by
    (try simp only [max_def]); (try split_ifs) <;> linarith
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, em]
  simp only [bGO, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, GO, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring_nf
theorem outPiece_10 (x : ℝ) (h1 : ((5) / 2 : ℝ) ≤ x) (h2 : x < ((100) / 37 : ℝ)) :
    Eout x = ((429) / 40 : ℝ) * x + ((-19) : ℝ) := by
  rw [Eout_expand (q := 2) (q' := 0) (μ := 4) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by linarith)]
  have hf0 : (0 : ℝ) ≤ x - ((2 : ℕ) : ℝ) := by norm_num; linarith
  have hf1 : x - ((2 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have hg0 : (0 : ℝ) ≤ 3 / 40 * x - ((0 : ℕ) : ℝ) := by norm_num; linarith
  have hg1 : 3 / 40 * x - ((0 : ℕ) : ℝ) < 1 := by norm_num; linarith
  have e00 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc00 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e01 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc01 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e02 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 0 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc02 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e10 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 0 = ((0 : ℝ) * x + ((1) / 2 : ℝ)) := by
    rw [cc10 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e11 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 1 = (((3) / 40 : ℝ) * x + (0 : ℝ)) := by
    rw [cc11 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e12 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 1 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc12 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e20 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 0 = ((1 : ℝ) * x + ((-5) / 2 : ℝ)) := by
    rw [cc20 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e21 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc21 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have e22 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 2 = ((0 : ℝ) * x + (0 : ℝ)) := by
    rw [cc22 hf0 hf1 hg0 hg1]; (try simp only [min_def, max_def]); (try split_ifs) <;> (push_cast at *; linarith)
  have em : max 0 (13 / 10 * x - 2) = (((13) / 10 : ℝ) * x + ((-2) : ℝ)) := by
    (try simp only [max_def]); (try split_ifs) <;> linarith
  simp only [Fin.sum_univ_three]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, em]
  simp only [bGO, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, GO, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring_nf

theorem outer_table_7_10 : ∀ i, 7 ≤ i → i < 11 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  intro i _ hi x hx
  interval_cases i
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_7 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_8 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_9 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_10 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith

end Apery
end Port0


open Finset in
/-- The platform target `Apery.outer_table_7_10`, restated at top level as `solution`. -/
theorem solution : ∀ i, 7 ≤ i → i < 11 → ∀ x ∈ Set.Ico (Apery.tOut i) (Apery.tOut (i + 1)),
    Apery.Eout x = Apery.gOut i x :=
  Apery.outer_table_7_10

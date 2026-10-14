-- Prove2me | solution 1 for Apery.outer_table_hi
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T16:50:26.392076+00:00
-- url     : https://prove2.me/submissions/1f54f947-cf8a-499a-973e-b96f817b0c33

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The last six pieces of the outer table (source `Apery/Growth/OuterTable.lean`)

A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, module
`Apery/Growth/OuterTable.lean` (the generated table of $E_{\mathrm{out}}$ on $[20/37, 3]$,
split in two for submission size).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables
import Theorems.Thm_Apery_Eout_expand


set_option autoImplicit false

section Port0
/-!
# The outer table, pieces 7-12 (source `Apery/Growth/OuterTable.lean`)

This file proves the platform theorem `Apery.outer_table_hi`. The generated piece lemmas and the
assembly are reproduced verbatim from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
module `Apery/Growth/OuterTable.lean` (split in two for submission size); the continuous
interval counts `cc00`..`cc22` are included locally since imported theorems expose only their
own statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

namespace Apery

section
variable {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)

include hf0 hf1 hg0 hg1 in
lemma cc00 : ccount f g 0 0 = 1 / 2 := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc01 : ccount f g 0 1 = min g (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc02 : ccount f g 0 2 = max 0 (g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc10 : ccount f g 1 0 = min f (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc20 : ccount f g 2 0 = max 0 (f - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc11 : ccount f g 1 1 = min (min f g) (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc12 : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc21 : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc22 : ccount f g 2 2 = max 0 (min f g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

end

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

theorem outPiece_11 (x : ℝ) (h1 : ((100) / 37 : ℝ) ≤ x) (h2 : x < ((120) / 43 : ℝ)) :
    Eout x = ((503) / 40 : ℝ) * x + ((-24) : ℝ) := by
  rw [Eout_expand (q := 2) (q' := 0) (μ := 5) (by norm_num; linarith) (by norm_num; linarith)
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

theorem outPiece_12 (x : ℝ) (h1 : ((120) / 43 : ℝ) ≤ x) (h2 : x < (3 : ℝ)) :
    Eout x = ((36) / 5 : ℝ) * x + ((-9) : ℝ) := by
  rw [Eout_expand (q := 2) (q' := 0) (μ := 5) (by norm_num; linarith) (by norm_num; linarith)
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
  have e21 : ccount (x - ((2 : ℕ) : ℝ)) (3 / 40 * x - ((0 : ℕ) : ℝ)) 2 1 = (((43) / 40 : ℝ) * x + ((-3) : ℝ)) := by
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


lemma outer_table_hi : ∀ i, 7 ≤ i → i < 13 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  intro i hi7 hi13 x hx
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
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_11 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  · simp only [tOut, tOutL, gOut, aOutL, bOutL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx ⊢
    have := outPiece_12 x (by linarith [hx.1]) (by linarith [hx.2])
    linarith

end Apery
end Port0


open Finset in
/-- The platform target `Apery.outer_table_hi`, restated at top level as `solution`. -/
theorem solution : ∀ i, 7 ≤ i → i < 13 → ∀ x ∈ Set.Ico (Apery.tOut i) (Apery.tOut (i + 1)),
    Apery.Eout x = Apery.gOut i x :=
  Apery.outer_table_hi

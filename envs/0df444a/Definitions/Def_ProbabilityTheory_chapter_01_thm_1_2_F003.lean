-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F003
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:52:49.917608+00:00
-- url     : https://prove2.me/theorems/b4c9d753-e7c7-479f-83e7-1125b6d62d1a
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `abs_const_mul_error_lt_core`, `image_const_mul_subinterval_eq_smul_core`, `upperStep_const_mul_nonneg_core`, `upperSum_const_mul_nonneg_core`, `lowerStep_const_mul_nonneg_core`, and 5 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma abs_const_mul_error_lt_core {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps := by
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rw [abs_mul]
  have hmul₁ : |c| * |old - L| ≤ |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt (by simpa [C] using hold)) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

lemma image_const_mul_subinterval_eq_smul_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) :
    (fun x => c * f x) '' Partition.subinterval P i = c • (f '' Partition.subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

lemma upperStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul_core]

  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' Partition.subinterval P i)

theorem upperSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg_core P f i hc]
  ring

lemma lowerStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]

  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' Partition.subinterval P i)

theorem lowerSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg_core P f i hc]
  ring

lemma upperStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]

  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' Partition.subinterval P i)
theorem upperSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos_core P f i hc]
  ring

lemma lowerStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul_core]

  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' Partition.subinterval P i)

theorem lowerSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos_core P f i hc]
  ring

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result



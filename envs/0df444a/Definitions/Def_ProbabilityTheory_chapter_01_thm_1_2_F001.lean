-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:24:50.563384+00:00
-- url     : https://prove2.me/theorems/7d932300-c14f-4659-b303-b667ed7d257c
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `image_const_mul_Icc_eq_smul_core`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma image_const_mul_Icc_eq_smul_core {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result



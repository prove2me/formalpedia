-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:54:34.927547+00:00
-- url     : https://prove2.me/theorems/7977aefd-19a0-4373-9598-23a3bac8752b
-- title:
--   Chapter 1, thm_1_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_4`: `strict_interval_of_rsIntegrable`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1

end Thm_1_4



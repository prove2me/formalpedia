-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:51:48.917229+00:00
-- url     : https://prove2.me/theorems/6097302e-2369-43a2-b022-53e1d31e2fa4
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_oscillation_basic`: `continuousAt_abs_sub_lt`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

lemma continuousAt_abs_sub_lt {g : ℝ → ℝ} {c eps : ℝ}
    (hg : ContinuousAt g c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x : ℝ, |x - c| < delta → |g x - g c| < eps := by
  rcases (Metric.continuousAt_iff.mp hg eps heps) with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x hx
  have hx' : dist x c < delta := by
    simpa [Real.dist_eq] using hx
  have h := Hdelta hx'
  simpa [Real.dist_eq] using h
end Thm11SourceRoute



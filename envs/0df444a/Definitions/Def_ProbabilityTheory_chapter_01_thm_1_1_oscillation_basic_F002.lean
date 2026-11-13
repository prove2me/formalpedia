-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F002
-- name    : ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:25:08.510019+00:00
-- url     : https://prove2.me/theorems/d38e7763-c92c-4275-b837-8fbdc93212a8
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_oscillation_basic`: `continuousAt_alpha_local_increment`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F001
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

lemma continuousAt_alpha_local_increment {α : ℝ → ℝ} {c eps : ℝ}
    (hα : ContinuousAt α c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x y : ℝ,
        |x - c| < delta → |y - c| < delta → α y - α x < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_abs_sub_lt hα hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x y hx hy
  have hx' := abs_lt.mp (Hdelta x hx)
  have hy' := abs_lt.mp (Hdelta y hy)
  linarith
end Thm11SourceRoute



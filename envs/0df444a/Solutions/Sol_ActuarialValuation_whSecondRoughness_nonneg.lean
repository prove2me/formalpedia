-- Prove2me | solution 1 for ActuarialValuation.whSecondRoughness_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:25:00.966017+00:00
-- url     : https://prove2.me/submissions/05a32945-9e41-4440-9704-a9d528f03540

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness
open ActuarialValuation

theorem solution(g : ℕ → ℝ) (n : ℕ) : 0 ≤ whSecondRoughness g n := by
  unfold whSecondRoughness
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

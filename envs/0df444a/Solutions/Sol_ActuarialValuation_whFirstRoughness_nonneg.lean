-- Prove2me | solution 1 for ActuarialValuation.whFirstRoughness_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:04:52.48082+00:00
-- url     : https://prove2.me/submissions/3b3987a0-f556-42bf-b800-357e00459918

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstRoughness
open ActuarialValuation

theorem solution(g : ℕ → ℝ) (n : ℕ) : 0 ≤ whFirstRoughness g n := by
  unfold whFirstRoughness
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

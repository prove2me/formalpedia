-- Prove2me | solution 1 for ActuarialValuation.ratWeightedExposure_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:05:53.485429+00:00
-- url     : https://prove2.me/submissions/be5eba6a-dee8-4db1-ab08-75caeb05bf35

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratWeightedExposure
open ActuarialValuation

theorem solution(e r : ℕ → ℝ) : ratWeightedExposure e r 0 = 0 := by
  simp [ratWeightedExposure]

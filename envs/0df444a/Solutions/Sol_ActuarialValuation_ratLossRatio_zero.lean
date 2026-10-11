-- Prove2me | solution 1 for ActuarialValuation.ratLossRatio_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:55:30.53359+00:00
-- url     : https://prove2.me/submissions/510b90fd-c424-48af-8afa-822b65febc16

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratLossRatio
open ActuarialValuation

theorem solution(premium : ℝ) : ratLossRatio 0 premium = 0 := by
  simp [ratLossRatio]

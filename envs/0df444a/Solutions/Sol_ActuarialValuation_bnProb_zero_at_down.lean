-- Prove2me | solution 1 for ActuarialValuation.bnProb_zero_at_down
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:37:24.244891+00:00
-- url     : https://prove2.me/submissions/f2846bc2-458d-4b4c-8f2b-acb0e7418f7b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb
open ActuarialValuation

theorem solution(u d : ℝ) (hud : u ≠ d) : bnRiskNeutralProb u d d = 0 := by
  simp [bnRiskNeutralProb]

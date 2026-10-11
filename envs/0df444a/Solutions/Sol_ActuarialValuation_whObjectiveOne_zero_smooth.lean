-- Prove2me | solution 1 for ActuarialValuation.whObjectiveOne_zero_smooth
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:30:48.371821+00:00
-- url     : https://prove2.me/submissions/799b75d3-6c3d-4ef2-b1d0-3c96c6022f7f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveOne
open ActuarialValuation

theorem solution(fit lambda : ℝ) : whObjectiveOne fit 0 lambda = fit := by
  simp [whObjectiveOne]

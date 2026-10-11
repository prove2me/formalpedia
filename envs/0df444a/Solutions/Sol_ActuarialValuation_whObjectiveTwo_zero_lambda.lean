-- Prove2me | solution 1 for ActuarialValuation.whObjectiveTwo_zero_lambda
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:29:31.131408+00:00
-- url     : https://prove2.me/submissions/03cdfebb-0d39-44e9-ab37-f76b7fcafe08

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveTwo
open ActuarialValuation

theorem solution(fit smooth : ℝ) : whObjectiveTwo fit smooth 0 = fit := by
  simp [whObjectiveTwo]

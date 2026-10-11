-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalFactor_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:52:06.485053+00:00
-- url     : https://prove2.me/submissions/a314b481-1803-468c-b6b4-c46f0f6bb060

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor
open ActuarialValuation

theorem solution(d : ℝ) (hd : d ≠ 0) : kmSurvivalFactor d d = 0 := by
  simp [kmSurvivalFactor, kmDeathHazard, hd]

-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalFactor_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:13:09.653351+00:00
-- url     : https://prove2.me/submissions/6346f96f-8056-4bea-a32d-17df1c6d4211

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor
open ActuarialValuation

theorem solution(r : ℝ) : kmSurvivalFactor 0 r = 1 := by
  simp [kmSurvivalFactor, kmDeathHazard]

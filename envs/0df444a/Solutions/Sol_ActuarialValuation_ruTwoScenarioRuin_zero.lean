-- Prove2me | solution 1 for ActuarialValuation.ruTwoScenarioRuin_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:21:51.572722+00:00
-- url     : https://prove2.me/submissions/421b121e-704c-448f-8b5a-c6270cf72e35

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruTwoScenarioRuin
open ActuarialValuation

theorem solution(p q : ℝ) : ruTwoScenarioRuin p q false false = 0 := by
  simp [ruTwoScenarioRuin]

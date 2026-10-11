-- Prove2me | solution 1 for ActuarialValuation.ulSurrenderValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:38:35.600056+00:00
-- url     : https://prove2.me/submissions/47e8a829-0d21-4d36-9df7-e51ed17027f7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulSurrenderValue
open ActuarialValuation

theorem solution(fund charge : ℝ) : 0≤ulSurrenderValue fund charge := by
  unfold ulSurrenderValue
  exact le_max_left _ _

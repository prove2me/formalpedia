-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalFactor_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:48:13.53841+00:00
-- url     : https://prove2.me/submissions/cc7ca231-3829-4dd7-9c19-4d26fdedd0f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d r : ℝ) (hd : 0 ≤ d) (hr : 0 < r) : kmSurvivalFactor d r ≤ 1 := by
  unfold kmSurvivalFactor kmDeathHazard
  exact sub_le_self 1 (div_nonneg hd hr.le)

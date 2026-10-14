-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:50:23.836913+00:00
-- url     : https://prove2.me/submissions/0217ca97-916b-40a5-9502-386d4e7c5bfa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d r : ℝ) (h : d ≤ r) (hr : 0 < r) : 0 ≤ kmSurvivalFactor d r := by
  unfold kmSurvivalFactor kmDeathHazard
  rw [sub_nonneg]
  exact (div_le_one₀ hr).2 h

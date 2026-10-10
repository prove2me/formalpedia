-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveFloor_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:42.4606+00:00
-- url     : https://prove2.me/submissions/6839f183-e34a-4fef-9337-d25569450953

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℝ) (hg : 0 < g) (h : s*R ≤ c) : cm1ZeroReserveFloor c s g R = 0 := by
  unfold cm1ZeroReserveFloor
  apply max_eq_left
  apply (div_le_iff₀ hg).2
  nlinarith [h]

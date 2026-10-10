-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:22:02.159889+00:00
-- url     : https://prove2.me/submissions/c97d6e6c-765e-4d7e-b9c7-691ed15c97ec

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℕ → ℝ) (N : ℕ) (h : cm1ZeroReserveCondition c s g R N) : R N = 0 := by
  exact h.1

-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:35.750879+00:00
-- url     : https://prove2.me/submissions/ffc24e42-71f5-49a1-a445-8fb5df6dd47a

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (i : ℝ) : cm1CashflowPV c 0 i = 0 := by
  simp [cm1CashflowPV]

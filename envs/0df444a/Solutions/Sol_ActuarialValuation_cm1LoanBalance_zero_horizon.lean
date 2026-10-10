-- Prove2me | solution 1 for ActuarialValuation.cm1LoanBalance_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:51.766912+00:00
-- url     : https://prove2.me/submissions/17ca9b21-8f9b-4cbe-b970-48448393ad14

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1LoanBalance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (t : ℕ) (i : ℝ) : cm1LoanBalance c 0 t i = 0 := by
  simp [cm1LoanBalance]

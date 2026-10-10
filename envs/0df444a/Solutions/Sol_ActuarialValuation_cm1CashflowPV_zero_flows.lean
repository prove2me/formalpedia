-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_zero_flows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:41.902353+00:00
-- url     : https://prove2.me/submissions/d699a4c0-9c0d-42b0-859b-d9062e7eef05

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (n : ℕ) (i : ℝ) : cm1CashflowPV (fun _ => 0) n i = 0 := by
  simp [cm1CashflowPV]

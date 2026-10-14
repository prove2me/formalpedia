-- Prove2me | solution 1 for ActuarialValuation.panjerStopLoss_zero_weights
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:29.947666+00:00
-- url     : https://prove2.me/submissions/ff913a85-f4e0-4fee-8c04-6e92aed4d676

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (n : ℕ) (d : ℝ) : panjerStopLoss (fun _ => (0 : ℝ)) n d = 0 := by
  simp [panjerStopLoss]

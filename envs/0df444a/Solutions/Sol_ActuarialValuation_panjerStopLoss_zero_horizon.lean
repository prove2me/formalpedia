-- Prove2me | solution 1 for ActuarialValuation.panjerStopLoss_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:26:07.326255+00:00
-- url     : https://prove2.me/submissions/a16e02a7-4da5-4f4e-a86a-af4ee20896d1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d) : panjerStopLoss g 0 d = 0 := by
  unfold panjerStopLoss
  have hdneg : -d ≤ (0 : ℝ) := neg_nonpos.mpr hd
  simp [hdneg]

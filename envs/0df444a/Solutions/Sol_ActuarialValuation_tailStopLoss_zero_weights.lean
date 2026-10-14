-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_zero_weights
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.840111+00:00
-- url     : https://prove2.me/submissions/87571d95-1abb-4214-95d6-74592f1f1d55

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (n : ℕ) (t : ℝ) :
    tailStopLoss (fun _ => (0 : ℝ)) n t = 0 := by
  first
  | (unfold tailStopLoss; simp)
  | (simp [tailStopLoss])

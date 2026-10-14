-- Prove2me | solution 1 for ActuarialValuation.whFitPenalty_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:37:06.066368+00:00
-- url     : https://prove2.me/submissions/29dcd08d-9481-4e06-a163-601bdf86795f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit
import Definitions.Def_actuarial_whFitPenalty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w g q : ℕ → ℝ) (n : ℕ) : whFitPenalty w g q (n+1) = whFitPenalty w g q n + whWeightedFit (w n) (g n) (q n) := by
  simp [whFitPenalty, Finset.sum_range_succ]

-- Prove2me | solution 1 for ActuarialValuation.tailLossMean_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:56.600479+00:00
-- url     : https://prove2.me/submissions/a7ff5d5d-54ae-4c4e-9de4-cc73f6a67526

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailLossMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) :
    tailLossMean p (n+1) = tailLossMean p n + ((n+1 : ℕ) : ℝ) * p (n+1) := by
  unfold tailLossMean
  exact Finset.sum_range_succ _ _

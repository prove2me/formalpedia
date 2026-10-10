-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:00:39.231981+00:00
-- url     : https://prove2.me/submissions/ffb4fb6d-a2e2-44be-a81d-3b2c4b71a9fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM : ℝ) (hE : 0 < EPV) :
  exposureCredibilityWeight EPV VHM 0 = 0 := by
  simp [exposureCredibilityWeight]

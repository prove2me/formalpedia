-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:01:11.455196+00:00
-- url     : https://prove2.me/submissions/52096600-8a8d-476b-8c47-1ecf8759f388

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM experience collective : ℝ) (hE : 0 < EPV) :
  exposureCredibilityPremium EPV VHM 0 experience collective = collective := by
  simp [exposureCredibilityPremium, exposureCredibilityWeight]

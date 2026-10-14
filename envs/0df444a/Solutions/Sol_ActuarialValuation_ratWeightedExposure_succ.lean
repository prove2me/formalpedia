-- Prove2me | solution 1 for ActuarialValuation.ratWeightedExposure_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:26.365874+00:00
-- url     : https://prove2.me/submissions/bf5de876-ca52-4bc3-9384-fd6064f59871

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratWeightedExposure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e r : ℕ → ℝ) (n : ℕ) : ratWeightedExposure e r (n+1) = ratWeightedExposure e r n + e n * r n := by
  simp [ratWeightedExposure, Finset.sum_range_succ]

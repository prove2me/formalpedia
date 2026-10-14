-- Prove2me | solution 1 for ActuarialValuation.ratExposureSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:18.762217+00:00
-- url     : https://prove2.me/submissions/db525d83-1c0f-4ebc-97ec-bc07b0b5e82b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratExposureSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e : ℕ → ℝ) (n : ℕ) : ratExposureSum e (n+1) = ratExposureSum e n + e n := by
  simp [ratExposureSum, Finset.sum_range_succ]

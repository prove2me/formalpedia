-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonPanjerStep_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:09:14.65224+00:00
-- url     : https://prove2.me/submissions/976f9f4e-8c44-49e9-ac66-aea6f39ee038

import Mathlib
import Definitions.Def_actuarial_compoundPoissonPanjerStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (rate : ℝ) (f g : ℕ → ℝ) :
  compoundPoissonPanjerStep rate f g 1 = rate * f 1 * g 0 := by
  simp [compoundPoissonPanjerStep, Finset.sum_range_succ, mul_assoc]

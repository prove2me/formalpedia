-- Prove2me | solution 1 for ActuarialValuation.pensionLateTotalMultiplier_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:12:29.250983+00:00
-- url     : https://prove2.me/submissions/8bebd71b-c4df-4456-8bb0-4b633b02ebb7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLateTotalMultiplier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (m f : ℝ)
  (hm : 0 ≤ m) (hf : 0 ≤ f) :
  0 ≤ pensionLateTotalMultiplier m f := by
  change 0 ≤ m * f
  exact mul_nonneg hm hf

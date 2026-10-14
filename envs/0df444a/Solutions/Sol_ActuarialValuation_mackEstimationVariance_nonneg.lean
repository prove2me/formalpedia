-- Prove2me | solution 1 for ActuarialValuation.mackEstimationVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:59.196549+00:00
-- url     : https://prove2.me/submissions/48870fdd-974e-45eb-b171-48a64bcd35ec

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackEstimationVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s c d : ℝ) (hs : 0 ≤ s) (hd : 0 < d) : 0 ≤ mackEstimationVariance s c d := by
  unfold mackEstimationVariance
  exact div_nonneg (mul_nonneg hs (sq_nonneg c)) (le_of_lt hd)

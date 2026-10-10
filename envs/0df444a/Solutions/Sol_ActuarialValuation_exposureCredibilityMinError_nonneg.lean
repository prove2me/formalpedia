-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityMinError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:01:41.337079+00:00
-- url     : https://prove2.me/submissions/174e3d65-ed1e-4b48-8872-358d444567a9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityMinError

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  0 ≤ exposureCredibilityMinError EPV VHM P := by
  change 0 ≤ EPV * VHM / (P * VHM + EPV)
  exact div_nonneg (mul_nonneg (le_of_lt hE) hV)
    (le_of_lt (add_pos_of_nonneg_of_pos (mul_nonneg hP hV) hE))

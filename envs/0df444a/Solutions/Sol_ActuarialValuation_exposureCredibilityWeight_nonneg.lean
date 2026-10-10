-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:00:48.167919+00:00
-- url     : https://prove2.me/submissions/9edd03fe-1db1-4f48-adf9-d95e9f12d16b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  0 ≤ exposureCredibilityWeight EPV VHM P := by
  change 0 ≤ P * VHM / (P * VHM + EPV)
  exact div_nonneg (mul_nonneg hP hV)
    (le_of_lt (add_pos_of_nonneg_of_pos (mul_nonneg hP hV) hE))

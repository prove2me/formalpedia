-- Prove2me | solution 1 for ActuarialValuation.pensionEarlyFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:31.784551+00:00
-- url     : https://prove2.me/submissions/6dec529b-8067-4d36-992d-7c95183f1a99

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D A : ℝ)
  (hD : 0 ≤ D) (hA : 0 < A) : 0 ≤ pensionEarlyFactor D A := by
  change 0 ≤ D / A
  exact div_nonneg hD (le_of_lt hA)

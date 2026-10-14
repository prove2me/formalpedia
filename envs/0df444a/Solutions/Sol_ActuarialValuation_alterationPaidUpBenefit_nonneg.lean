-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:20.375645+00:00
-- url     : https://prove2.me/submissions/fd776f4b-7ecc-457c-b3b4-9cd4d6292d1c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V A : ℝ) (hV : 0 ≤ V) (hA : 0 < A) : 0 ≤ alterationPaidUpBenefit V A := by
  unfold alterationPaidUpBenefit
  exact div_nonneg hV (le_of_lt hA)

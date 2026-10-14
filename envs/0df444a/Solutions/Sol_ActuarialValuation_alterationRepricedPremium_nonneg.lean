-- Prove2me | solution 1 for ActuarialValuation.alterationRepricedPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:17.333291+00:00
-- url     : https://prove2.me/submissions/2c59c63f-e0ca-4190-b9de-029f1ed4763c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRepricedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A : ℝ) (hB : 0 ≤ B) (hA : 0 < A) : 0 ≤ alterationRepricedPremium B A := by
  unfold alterationRepricedPremium
  exact div_nonneg hB (le_of_lt hA)

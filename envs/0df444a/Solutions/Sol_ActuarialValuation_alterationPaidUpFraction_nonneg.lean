-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpFraction_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:32.372984+00:00
-- url     : https://prove2.me/submissions/32ea28d1-7b56-48a4-86b1-96c736a049ba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpFraction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V B : ℝ) (hV : 0 ≤ V) (hB : 0 < B) : 0 ≤ alterationPaidUpFraction V B := by
  unfold alterationPaidUpFraction
  exact div_nonneg hV (le_of_lt hB)

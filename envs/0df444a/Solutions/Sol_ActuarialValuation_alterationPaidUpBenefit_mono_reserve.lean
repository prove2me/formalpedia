-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpBenefit_mono_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:20.513042+00:00
-- url     : https://prove2.me/submissions/2a78238c-e2f7-4bd4-abb4-0014fafbe0b1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V1 V2 A : ℝ) (hA : 0 < A) (h : V1 ≤ V2) : alterationPaidUpBenefit V1 A ≤ alterationPaidUpBenefit V2 A := by
  unfold alterationPaidUpBenefit
  exact div_le_div_of_nonneg_right h (le_of_lt hA)

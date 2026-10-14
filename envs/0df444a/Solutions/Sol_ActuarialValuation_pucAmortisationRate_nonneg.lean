-- Prove2me | solution 1 for ActuarialValuation.pucAmortisationRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:21:03.469578+00:00
-- url     : https://prove2.me/submissions/e5b46391-e459-44a3-afa2-c958850b4ba0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAmortisationRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u base : ℝ) (hu : 0 ≤ u) (hb : 0 < base) : 0 ≤ pucAmortisationRate u base := by
  unfold pucAmortisationRate
  exact div_nonneg hu (le_of_lt hb)

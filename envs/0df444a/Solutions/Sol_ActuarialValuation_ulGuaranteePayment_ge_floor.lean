-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePayment_ge_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:50.575731+00:00
-- url     : https://prove2.me/submissions/2b6c6c8a-454f-4208-aab7-58d21883e263

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) : floor ≤ ulGuaranteePayment account floor := by
  change floor ≤ max account floor
  exact le_max_right _ _

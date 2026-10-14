-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePayment_ge_account
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:38.273131+00:00
-- url     : https://prove2.me/submissions/c702d0c4-37da-40a2-8d1d-547ca0f056a1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) : account ≤ ulGuaranteePayment account floor := by
  change account ≤ max account floor
  exact le_max_left _ _

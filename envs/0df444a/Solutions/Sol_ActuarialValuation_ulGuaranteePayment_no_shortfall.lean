-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePayment_no_shortfall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:02.557+00:00
-- url     : https://prove2.me/submissions/b29bcce5-7e39-4e22-88f1-34b573f9a786

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) (h : floor≤account) : ulGuaranteePayment account floor = account := by
  change max account floor = account
  exact max_eq_left h

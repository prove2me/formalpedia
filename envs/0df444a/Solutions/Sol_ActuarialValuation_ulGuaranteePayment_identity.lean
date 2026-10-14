-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteePayment_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:23:31.222132+00:00
-- url     : https://prove2.me/submissions/e9e551ca-a023-4632-a06f-ea8783df5db4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment
import Definitions.Def_actuarial_ulGuaranteeShortfall
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) : ulGuaranteePayment account floor = account + ulGuaranteeShortfall account floor := by
  change max account floor = account + max (floor - account) 0
  rcases le_total floor account with h | h
  · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

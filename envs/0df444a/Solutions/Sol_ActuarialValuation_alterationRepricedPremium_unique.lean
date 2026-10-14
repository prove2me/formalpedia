-- Prove2me | solution 1 for ActuarialValuation.alterationRepricedPremium_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:29.473927+00:00
-- url     : https://prove2.me/submissions/3e8809ba-8460-477b-bd11-cada5ce5024a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRepricedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P : ℝ) (hA : A ≠ 0) (hP : P*A=B) : P = alterationRepricedPremium B A := by
  unfold alterationRepricedPremium
  exact (eq_div_iff hA).2 hP

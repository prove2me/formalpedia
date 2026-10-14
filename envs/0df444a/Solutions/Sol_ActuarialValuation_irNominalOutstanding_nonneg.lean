-- Prove2me | solution 1 for ActuarialValuation.irNominalOutstanding_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:04:34.955194+00:00
-- url     : https://prove2.me/submissions/42793cd1-8cfc-488e-930f-fcfd49059da8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irNominalOutstanding

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (real future base : ℝ) (hr : 0≤real) (hf : 0≤future) (hb : 0<base) : 0≤irNominalOutstanding real future base := by
  unfold irNominalOutstanding irReinflate
  exact div_nonneg (mul_nonneg hr hf) (le_of_lt hb)

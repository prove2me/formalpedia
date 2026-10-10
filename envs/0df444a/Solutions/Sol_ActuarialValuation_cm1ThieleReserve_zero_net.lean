-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleReserve_zero_net
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:08:45.026787+00:00
-- url     : https://prove2.me/submissions/7bbdf929-82fa-48ec-aba4-fcfc95777511

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ThieleReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T t : ℝ) (h : P=μ*B) : cm1ThieleReserve δ μ B P T t = 0 := by
  subst P
  simp [cm1ThieleReserve, cm1ForceNetOutgo]

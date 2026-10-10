-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleReserve_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:08:05.948914+00:00
-- url     : https://prove2.me/submissions/b122d8fd-b92b-44e0-8c01-198a6bec2663

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ThieleReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T : ℝ) : cm1ThieleReserve δ μ B P T T = 0 := by
  simp only [cm1ThieleReserve, cm1ForceTermFactor, sub_self, mul_zero,
    neg_zero, Real.exp_zero, sub_self, zero_div, mul_zero]

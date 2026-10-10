-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleRHS_expand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:46:50.00524+00:00
-- url     : https://prove2.me/submissions/ec944a28-ff9f-473d-90a5-7c9a5919483f

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ThieleRHS
import Definitions.Def_actuarial_cm1ForceNetOutgo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P V : ℝ) :
    cm1ThieleRHS δ μ B P V =
      (δ+μ)*V - cm1ForceNetOutgo μ B P := by
  simp only [cm1ThieleRHS, cm1ForceNetOutgo]
  ring

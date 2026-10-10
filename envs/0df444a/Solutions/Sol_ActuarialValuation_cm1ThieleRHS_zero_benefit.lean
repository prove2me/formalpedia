-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleRHS_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:34:01.242999+00:00
-- url     : https://prove2.me/submissions/328636d5-1c20-41ba-b96c-dcb441980ffc

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ThieleRHS


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ P V : ℝ) : cm1ThieleRHS δ μ 0 P V = (δ+μ)*V + P := by
  simp only [cm1ThieleRHS]
  ring

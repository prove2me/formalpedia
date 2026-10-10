-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleReserve_issue_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:47.890364+00:00
-- url     : https://prove2.me/submissions/6d4afe09-2995-4a00-819f-e1069a52fdb1

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ForceBenefitPV
import Definitions.Def_actuarial_cm1ForcePremiumPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T : ℝ) :
    cm1ThieleReserve δ μ B P T 0 =
      cm1ForceBenefitPV δ μ B T - cm1ForcePremiumPV δ μ P T := by
  simp only [cm1ThieleReserve, cm1ForceNetOutgo,
    cm1ForceBenefitPV, cm1ForcePremiumPV]
  ring

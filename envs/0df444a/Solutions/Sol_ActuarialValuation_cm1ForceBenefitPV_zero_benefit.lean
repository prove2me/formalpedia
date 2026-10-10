-- Prove2me | solution 1 for ActuarialValuation.cm1ForceBenefitPV_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:08:50.919143+00:00
-- url     : https://prove2.me/submissions/ad97a5b6-e296-4496-855c-7eab4ffa7c47

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ForceBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ T : ℝ) : cm1ForceBenefitPV δ μ 0 T = 0 := by
  change μ * 0 * cm1ForceTermFactor δ μ T 0 = 0
  ring

-- Prove2me | solution 1 for ActuarialValuation.cm1ForceBenefitPV_zero_mortality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:08:56.500979+00:00
-- url     : https://prove2.me/submissions/782e4e97-9666-40ed-88a0-bdc738219c86

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ForceBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ B T : ℝ) : cm1ForceBenefitPV δ 0 B T = 0 := by
  change (0 : ℝ) * B * cm1ForceTermFactor δ 0 T 0 = 0
  ring

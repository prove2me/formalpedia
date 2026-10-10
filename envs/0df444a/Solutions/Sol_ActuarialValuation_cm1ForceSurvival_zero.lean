-- Prove2me | solution 1 for ActuarialValuation.cm1ForceSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:35.268138+00:00
-- url     : https://prove2.me/submissions/432a7aab-883b-4fec-969b-95b3df0ee639

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ : ℝ) : cm1ForceSurvival μ 0 = 1 := by
  simp [cm1ForceSurvival]

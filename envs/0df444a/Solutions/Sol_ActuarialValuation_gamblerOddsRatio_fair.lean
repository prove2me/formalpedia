-- Prove2me | solution 1 for ActuarialValuation.gamblerOddsRatio_fair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:46.223107+00:00
-- url     : https://prove2.me/submissions/179a582c-4ffb-470f-a900-d6a15a957e07

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerOddsRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution :
    gamblerOddsRatio (1 / 2 : ℝ) = 1 := by
  norm_num [gamblerOddsRatio]

-- Prove2me | solution 1 for ActuarialValuation.gamblerBiasedSuccess_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:01.68338+00:00
-- url     : https://prove2.me/submissions/9fe0ad82-b314-4d35-a854-3e4df77fdaf4

import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerOddsRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N : ℕ) (p : ℝ)
    (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
    gamblerBiasedSuccess N N p = 1 := by
  simp [gamblerBiasedSuccess, hden]

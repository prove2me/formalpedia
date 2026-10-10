-- Prove2me | solution 1 for ActuarialValuation.credibilityScaledMSE_square_completion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:32.522631+00:00
-- url     : https://prove2.me/submissions/a6936797-4207-4ae1-aad3-4cfb921562e1

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm z : ℝ) (hd : p * vhm + epv ≠ 0) :
  credibilityScaledMSE p epv vhm z =
    (p * vhm * epv) / (p * vhm + epv) +
    (p * vhm + epv) *
      (z - credibilityOptimalWeight p epv vhm) ^ 2 := by
  unfold credibilityScaledMSE credibilityOptimalWeight
  field_simp [hd]
  ring

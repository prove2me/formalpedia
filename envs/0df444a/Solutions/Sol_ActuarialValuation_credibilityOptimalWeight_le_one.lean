-- Prove2me | solution 1 for ActuarialValuation.credibilityOptimalWeight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:52.260078+00:00
-- url     : https://prove2.me/submissions/8d47a28f-a6df-490b-afcd-2d7d676c68d9

import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm : ℝ) (hp : 0 ≤ p) (he : 0 ≤ epv)
  (hv : 0 ≤ vhm) (hd : 0 < p * vhm + epv) :
  credibilityOptimalWeight p epv vhm ≤ 1 := by
  unfold credibilityOptimalWeight
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg hp hv]

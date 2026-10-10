-- Prove2me | solution 1 for ActuarialValuation.credibilityOptimalWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:45.170702+00:00
-- url     : https://prove2.me/submissions/20451fc5-01ef-4f81-ad61-3a5aac005bcf

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm : ℝ) (hp : 0 ≤ p) (he : 0 ≤ epv)
  (hv : 0 ≤ vhm) (hd : 0 < p * vhm + epv) :
  0 ≤ credibilityOptimalWeight p epv vhm := by
  unfold credibilityOptimalWeight
  exact div_nonneg (mul_nonneg hp hv) hd.le

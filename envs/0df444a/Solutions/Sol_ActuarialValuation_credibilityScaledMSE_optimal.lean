-- Prove2me | solution 1 for ActuarialValuation.credibilityScaledMSE_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:58.207669+00:00
-- url     : https://prove2.me/submissions/170c1091-0b4d-4a65-b043-52d0e4007742

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm z : ℝ)
  (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm)
  (hd : 0 < p * vhm + epv) :
  credibilityScaledMSE p epv vhm
      (credibilityOptimalWeight p epv vhm) ≤
    credibilityScaledMSE p epv vhm z := by
  have hdne : p * vhm + epv ≠ 0 := ne_of_gt hd
  have hcomp (t : ℝ) :
      credibilityScaledMSE p epv vhm t =
        (p * vhm * epv) / (p * vhm + epv) +
          (p * vhm + epv) *
            (t - credibilityOptimalWeight p epv vhm) ^ 2 := by
    unfold credibilityScaledMSE credibilityOptimalWeight
    field_simp [hdne]
    ring
  let Z := credibilityOptimalWeight p epv vhm
  calc
    credibilityScaledMSE p epv vhm Z =
        (p * vhm * epv) / (p * vhm + epv) := by
          rw [hcomp]
          ring
    _ ≤ (p * vhm * epv) / (p * vhm + epv) +
          (p * vhm + epv) * (z - Z) ^ 2 := by
          have hn := mul_nonneg hd.le (sq_nonneg (z - Z))
          linarith
    _ = credibilityScaledMSE p epv vhm z :=
      (hcomp z).symm

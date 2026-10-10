-- Prove2me | solution 1 for ActuarialValuation.credibilityScaledMSE_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:43:04.710877+00:00
-- url     : https://prove2.me/submissions/3351427a-2a8b-4f92-b024-ea36111a6a78

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm z : ℝ) (hd : 0 < p * vhm + epv)
  (hEq : credibilityScaledMSE p epv vhm z =
    credibilityScaledMSE p epv vhm
      (credibilityOptimalWeight p epv vhm)) :
  z = credibilityOptimalWeight p epv vhm := by
  have hdne : p * vhm + epv ≠ 0 := ne_of_gt hd
  have hcomp (t : ℝ) :
      credibilityScaledMSE p epv vhm t =
        (p * vhm * epv) / (p * vhm + epv) +
          (p * vhm + epv) *
            (t - credibilityOptimalWeight p epv vhm) ^ 2 := by
    unfold credibilityScaledMSE credibilityOptimalWeight
    field_simp [hdne]
    ring
  have hzero : (p * vhm + epv) *
      (z - credibilityOptimalWeight p epv vhm) ^ 2 = 0 := by
    rw [hcomp z, hcomp (credibilityOptimalWeight p epv vhm)] at hEq
    nlinarith
  have hs : (z - credibilityOptimalWeight p epv vhm) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hdne
  nlinarith [sq_nonneg (z - credibilityOptimalWeight p epv vhm)]

-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonSeverityPower_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:12:17.397935+00:00
-- url     : https://prove2.me/submissions/19b355f2-cd56-43f7-bab8-8660853655ba

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower
import Definitions.Def_actuarial_compoundPoissonConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonSeverityPower f 1 s = f s := by
  classical
  change (∑ j ∈ Finset.range (s + 1),
    f j * (if s - j = 0 then (1 : ℝ) else 0)) = f s
  rw [Finset.sum_eq_single s]
  · simp
  · intro j hj hjs
    have hjlt : j < s := by
      have hb : j < s + 1 := Finset.mem_range.mp hj
      omega
    have hne : s - j ≠ 0 := by omega
    simp [hne]
  · simp

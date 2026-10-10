-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonSeverityPower_outside
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:12:24.516996+00:00
-- url     : https://prove2.me/submissions/9927c9ec-acdf-46d3-87b2-dc0e022abb37

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (f : ℕ → ℝ) (m s : ℕ) (hzero : f 0 = 0) (h : s < m) :
  compoundPoissonSeverityPower f m s = 0 := by
  induction m generalizing s with
  | zero =>
      omega
  | succ m ih =>
      change (∑ j ∈ Finset.range (s + 1),
        f j * compoundPoissonSeverityPower f m (s - j)) = 0
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [hzero]
      · have hjle : j ≤ s := by
          have hb : j < s + 1 := Finset.mem_range.mp hj
          omega
        have hsmall : s - j < m := by omega
        simp [ih (s - j) hsmall]

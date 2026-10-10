-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonAggregatePMF_rate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:22:43.92784+00:00
-- url     : https://prove2.me/submissions/24a93fa5-8f96-4c99-8963-1dcccff1ae14

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonAggregatePMF 0 f s = (if s = 0 then 1 else 0) := by
  classical
  unfold compoundPoissonAggregatePMF
  rw [Finset.sum_eq_single 0]
  · simp [compoundPoissonCountWeight, compoundPoissonSeverityPower]
  · intro m hm hmzero
    have hpos : 0 < m := Nat.pos_of_ne_zero hmzero
    simp [compoundPoissonCountWeight, hpos, hmzero]
  · simp

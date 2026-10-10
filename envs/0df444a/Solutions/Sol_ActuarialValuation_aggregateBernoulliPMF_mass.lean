-- Prove2me | solution 1 for ActuarialValuation.aggregateBernoulliPMF_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:12:17.135414+00:00
-- url     : https://prove2.me/submissions/937ce115-bf47-4cd2-b941-d572d37e6123

import Mathlib
import Definitions.Def_actuarial_aggregateFiniteMass
import Definitions.Def_actuarial_aggregateBernoulliPMF
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℝ) (b : ℕ) :
    aggregateFiniteMass (aggregateBernoulliPMF p b) b = 1 := by
  unfold aggregateFiniteMass aggregateBernoulliPMF
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  simp

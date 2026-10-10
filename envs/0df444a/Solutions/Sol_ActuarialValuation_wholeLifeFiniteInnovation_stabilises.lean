-- Prove2me | solution 1 for ActuarialValuation.wholeLifeFiniteInnovation_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:32.405803+00:00
-- url     : https://prove2.me/submissions/6d3cdc62-17fb-442a-851a-9c347499f1aa

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeCompleteInnovation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w rho : ℕ → ℝ) (n k : ℕ)
  (h : k < n) :
  wholeLifeFiniteInnovation w rho n k =
    wholeLifeCompleteInnovation w rho k := by
  have hn : k + 1 ≤ n := by omega
  have hsplit : n = (k + 1) + (n - (k + 1)) := by omega
  change (∑ t ∈ Finset.range n, rho t * wholeLifeYearInnovation w t k) =
    ∑ t ∈ Finset.range (k + 1), rho t * wholeLifeYearInnovation w t k
  rw [hsplit, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (n - (k + 1)),
      rho (k + 1 + i) * wholeLifeYearInnovation w (k + 1 + i) k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hik : k < k + 1 + i := by omega
    have hneq : k ≠ k + 1 + i := ne_of_lt hik
    have hnot : ¬ k + 1 + i ≤ k := not_le.mpr hik
    simp [wholeLifeYearInnovation, hneq, hnot]
  simpa [hz]

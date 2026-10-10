-- Prove2me | solution 1 for ActuarialValuation.separateTrancheFactors_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:05:21.936986+00:00
-- url     : https://prove2.me/submissions/175ce2eb-e4e7-4723-9441-9ba895821c0e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_trancheAdjustedPV
import Definitions.Def_actuarial_trancheSchemeAdjustedPV
import Definitions.Def_actuarial_trancheSchemeComparatorPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (n : ℕ)
  (hA : ∀ i ∈ Finset.range n, A i ≠ 0) :
  (∀ i ∈ Finset.range n, trancheAdjustedPV P A D i = P i * D i) ∧
  (trancheSchemeAdjustedPV P A D n = trancheSchemeComparatorPV P D n) := by
  have heq : ∀ i ∈ Finset.range n,
      trancheAdjustedPV P A D i = P i * D i := by
    intro i hi
    dsimp [trancheAdjustedPV, trancheAdjustedPension, trancheIndividualFactor]
    field_simp [hA i hi] <;> ring
  refine ⟨heq, ?_⟩
  unfold trancheSchemeAdjustedPV trancheSchemeComparatorPV
  apply Finset.sum_congr rfl
  intro i hi
  exact heq i hi

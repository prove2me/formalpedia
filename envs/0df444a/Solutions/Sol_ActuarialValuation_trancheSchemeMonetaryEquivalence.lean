-- Prove2me | solution 1 for ActuarialValuation.trancheSchemeMonetaryEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:05:15.258233+00:00
-- url     : https://prove2.me/submissions/2a90d0fc-dbf5-48b2-9cc5-88b43c3d48f6

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_trancheSchemeAdjustedPV
import Definitions.Def_actuarial_trancheSchemeComparatorPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (n : ℕ)
  (hA : ∀ i ∈ Finset.range n, A i ≠ 0) :
  trancheSchemeAdjustedPV P A D n = trancheSchemeComparatorPV P D n := by
  unfold trancheSchemeAdjustedPV trancheSchemeComparatorPV
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [trancheAdjustedPV, trancheAdjustedPension, trancheIndividualFactor]
  field_simp [hA i hi] <;> ring

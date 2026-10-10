-- Prove2me | solution 1 for ActuarialValuation.xlRiskAdjustedRetention_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:20:29.11999+00:00
-- url     : https://prove2.me/submissions/a104f700-d618-40b1-bb67-18fbc591b1e1

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_actuarial_xlFiniteOptimalRetentionCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (retention : A → ℝ) (θ kap : ℝ)
  :
  ((∀ a : A, xlFiniteOptimalRetentionCost w z retention θ kap ≤
      xlRiskAdjustedRetentionCost w z θ kap (retention a))
  ∧ (∃ a : A, xlFiniteOptimalRetentionCost w z retention θ kap =
      xlRiskAdjustedRetentionCost w z θ kap (retention a))) := by
  classical
  constructor
  · intro a
    unfold xlFiniteOptimalRetentionCost
    exact Finset.inf'_le
      (fun x : A => xlRiskAdjustedRetentionCost w z θ kap (retention x))
      (Finset.mem_univ a)
  · unfold xlFiniteOptimalRetentionCost
    obtain ⟨a, ha, heq⟩ :=
      Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset A))
        (Finset.univ_nonempty) (fun a : A =>
          xlRiskAdjustedRetentionCost w z θ kap (retention a))
    exact ⟨a, heq⟩

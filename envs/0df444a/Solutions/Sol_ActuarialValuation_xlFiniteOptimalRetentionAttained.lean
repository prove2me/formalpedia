-- Prove2me | solution 1 for ActuarialValuation.xlFiniteOptimalRetentionAttained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:09:24.717989+00:00
-- url     : https://prove2.me/submissions/16dbafd5-1e40-4d9a-8920-f969cf3a550f

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
  ∃ a : A, xlFiniteOptimalRetentionCost w z retention θ kap =
   xlRiskAdjustedRetentionCost w z θ kap (retention a) := by
  classical
  unfold xlFiniteOptimalRetentionCost
  obtain ⟨a, ha, heq⟩ :=
    Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset A))
      (Finset.univ_nonempty) (fun a : A =>
        xlRiskAdjustedRetentionCost w z θ kap (retention a))
  exact ⟨a, heq⟩

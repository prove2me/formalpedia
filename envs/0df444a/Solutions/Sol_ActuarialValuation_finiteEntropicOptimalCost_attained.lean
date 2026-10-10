-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicOptimalCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:29:29.81559+00:00
-- url     : https://prove2.me/submissions/30addc94-2707-486b-9035-efc689275166

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_actuarial_finiteEntropicOptimalCost
import Definitions.Def_actuarial_finiteEntropicRetentionCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω A : Type*} [Fintype Ω] [Fintype A]
    [Nonempty A] (w z : Ω → ℝ)
    (reinsurancePremium : ℝ → ℝ)
    (retention : A → ℝ) (gamma : ℝ) :
    ∃ a : A, finiteEntropicOptimalCost w z reinsurancePremium retention gamma =
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a) := by
  unfold finiteEntropicOptimalCost
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset A))
    Finset.univ_nonempty
    (fun a : A =>
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))
  exact ⟨a, ha⟩

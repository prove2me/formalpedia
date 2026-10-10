-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicOptimalCost_le_action
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:29:25.166715+00:00
-- url     : https://prove2.me/submissions/f9cc56bf-632c-40ff-acc9-554701368073

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
    (retention : A → ℝ) (gamma : ℝ) (a : A) :
    finiteEntropicOptimalCost w z reinsurancePremium retention gamma ≤
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a) := by
  unfold finiteEntropicOptimalCost
  exact Finset.inf'_le
    (fun a : A =>
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))
    (Finset.mem_univ a)

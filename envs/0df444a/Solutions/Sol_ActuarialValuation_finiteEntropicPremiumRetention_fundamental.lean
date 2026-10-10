-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPremiumRetention_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:33:38.585289+00:00
-- url     : https://prove2.me/submissions/58f89ef9-148f-41c8-a6a7-d3bd3f00d09e

import Mathlib
import Definitions.Def_actuarial_finiteEntropicOptimalCost
import Definitions.Def_actuarial_finiteEntropicRetentionCost
import Theorems.Thm_ActuarialValuation_finiteEntropicOptimalCost_le_action
import Theorems.Thm_ActuarialValuation_finiteEntropicOptimalCost_attained
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω A : Type*} [Fintype Ω] [Fintype A]
    [Nonempty A] (w z : Ω → ℝ)
    (reinsurancePremium : ℝ → ℝ)
    (retention : A → ℝ) (gamma : ℝ) :
    ((∀ a : A, finiteEntropicOptimalCost w z reinsurancePremium retention gamma ≤
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))
    ∧ (∃ a : A, finiteEntropicOptimalCost w z reinsurancePremium retention gamma =
      finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))) := by
  constructor
  · intro a
    exact finiteEntropicOptimalCost_le_action w z reinsurancePremium retention gamma a
  · exact finiteEntropicOptimalCost_attained w z reinsurancePremium retention gamma

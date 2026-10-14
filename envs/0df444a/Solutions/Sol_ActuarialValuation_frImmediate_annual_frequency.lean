-- Prove2me | solution 1 for ActuarialValuation.frImmediate_annual_frequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T11:44:59.738774+00:00
-- url     : https://prove2.me/submissions/11e21ae9-f49d-460e-b41a-16d986ce9942

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue
import Definitions.Def_actuarial_frAnnualImmediateValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ) (hp : ∀ k ∈ Finset.range n, p (k+1) = p k * (1-q k)) : frImmediateValue c discount p q n 1 = frAnnualImmediateValue c discount p n := by
  unfold frImmediateValue frAnnualImmediateValue
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.sum_range_one]
  simp [frImmediateTerm, frTime, frUddSurvival, hp k hk] <;> ring

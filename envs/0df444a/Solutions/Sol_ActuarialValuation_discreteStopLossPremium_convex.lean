-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_convex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:29:02.53602+00:00
-- url     : https://prove2.me/submissions/2867b556-c6e3-4632-b89a-5ccfead28ea6

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  discreteStopLossPremium w bound deductible +
    discreteStopLossPremium w bound (deductible + 2) ≥
      2 * discreteStopLossPremium w bound (deductible + 1) := by
  unfold discreteStopLossPremium
  have hp :
      2 * (∑ s ∈ Finset.range (bound + 1),
        (discreteStopLossPayment s (deductible + 1) : ℝ) * w s) ≤
        ∑ s ∈ Finset.range (bound + 1),
          ((discreteStopLossPayment s deductible : ℝ) * w s +
          (discreteStopLossPayment s (deductible + 2) : ℝ) * w s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hnat :
        2 * (s - (deductible + 1)) ≤
          (s - deductible) + (s - (deductible + 2)) := by
      omega
    have hreal :
        (2 : ℝ) * (s - (deductible + 1) : ℕ) ≤
          (s - deductible : ℕ) + (s - (deductible + 2) : ℕ) := by
      exact_mod_cast hnat
    have hweighted := mul_le_mul_of_nonneg_right hreal (hw s)
    dsimp [discreteStopLossPayment]
    nlinarith
  rw [Finset.sum_add_distrib] at hp
  linarith

-- Prove2me | solution 1 for ActuarialValuation.ruStoppedIncrement_after_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:37:24.119988+00:00
-- url     : https://prove2.me/submissions/42d61453-5d85-4758-97e6-3055411b0b32

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruStoppedIncrementMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ)
    (N k : ℕ) (hτ : ∀ ω, τ ω ≤ N) (hk : N ≤ k) :
    ruStoppedIncrementMean p X τ k = 0 := by
  unfold ruStoppedIncrementMean
  apply Finset.sum_eq_zero
  intro ω hω
  have hτω : τ ω ≤ N := hτ ω
  have h1 : τ ω ≤ k + 1 := by omega
  have h2 : τ ω ≤ k := le_trans hτω hk
  have e1 : ruStopped X τ (k+1) ω = X (τ ω) ω := by
    first
    | (unfold ruStopped; simp [h1])
    | (simp [ruStopped, h1])
  have e2 : ruStopped X τ k ω = X (τ ω) ω := by
    first
    | (unfold ruStopped; simp [h2])
    | (simp [ruStopped, h2])
  rw [e1, e2, sub_self, mul_zero]

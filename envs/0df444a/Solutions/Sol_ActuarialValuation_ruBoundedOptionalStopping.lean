-- Prove2me | solution 1 for ActuarialValuation.ruBoundedOptionalStopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:09:25.099414+00:00
-- url     : https://prove2.me/submissions/56f09dbf-237f-49b4-bea4-e7824a38be1b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruExpectedStopped
import Definitions.Def_actuarial_ruStoppedIncrementMean
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ)
    (N : ℕ) (hinc : ∀ k ∈ Finset.range N, ruStoppedIncrementMean p X τ k = 0) :
    ruExpectedStopped p X τ N = ruMean p (X 0) := by
  have htel : ∀ N : ℕ, ruExpectedStopped p X τ N
      = ruExpectedStopped p X τ 0
        + ∑ k ∈ Finset.range N, ruStoppedIncrementMean p X τ k := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      have hbal : ruExpectedStopped p X τ (n+1)
          = ruExpectedStopped p X τ n + ruStoppedIncrementMean p X τ n := by
        unfold ruExpectedStopped ruStoppedIncrementMean ruMean
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      rw [hbal, ih, Finset.sum_range_succ]
      ring
  have h0 : ruExpectedStopped p X τ 0 = ruMean p (X 0) := by
    unfold ruExpectedStopped ruMean
    apply Finset.sum_congr rfl
    intro ω hω
    congr 1
    try (simp [ruStopped])
  have hsum : ∑ k ∈ Finset.range N, ruStoppedIncrementMean p X τ k = 0 :=
    Finset.sum_eq_zero (fun k hk => hinc k hk)
  rw [htel N, h0, hsum, add_zero]

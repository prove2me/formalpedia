-- Prove2me | solution 1 for ActuarialValuation.ruExpectedStopped_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:33:18.134848+00:00
-- url     : https://prove2.me/submissions/58aa5fba-ca36-40f8-b4d4-17d02bd5a722

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruExpectedStopped
import Definitions.Def_actuarial_ruStoppedIncrementMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ)
    (N : ℕ) :
    ruExpectedStopped p X τ N
      = ruExpectedStopped p X τ 0
        + ∑ k ∈ Finset.range N, ruStoppedIncrementMean p X τ k := by
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

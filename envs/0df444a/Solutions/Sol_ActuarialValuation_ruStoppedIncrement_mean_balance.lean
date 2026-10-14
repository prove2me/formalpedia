-- Prove2me | solution 1 for ActuarialValuation.ruStoppedIncrement_mean_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:28:09.071108+00:00
-- url     : https://prove2.me/submissions/81f5be72-e593-43a1-af5c-23d10291742e

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
    (k : ℕ) :
    ruExpectedStopped p X τ (k+1)
      = ruExpectedStopped p X τ k + ruStoppedIncrementMean p X τ k := by
  unfold ruExpectedStopped ruStoppedIncrementMean ruMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

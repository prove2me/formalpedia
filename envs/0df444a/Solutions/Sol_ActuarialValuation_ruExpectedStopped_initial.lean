-- Prove2me | solution 1 for ActuarialValuation.ruExpectedStopped_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:24:38.403358+00:00
-- url     : https://prove2.me/submissions/d0ceaab8-0567-4546-b37d-c36c9f3d0943

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExpectedStopped
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) :
    ruExpectedStopped p X τ 0 = ruMean p (X 0) := by
  unfold ruExpectedStopped ruMean
  apply Finset.sum_congr rfl
  intro ω hω
  congr 1
  try (simp [ruStopped])

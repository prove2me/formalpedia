-- Prove2me | solution 1 for ActuarialValuation.ruStopped_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:08:31.427481+00:00
-- url     : https://prove2.me/submissions/3fe2f54c-3eac-4e01-8f4c-0c7f9268f200

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruStopped

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ)
    (ω : Fin m) :
    ruStopped X τ 0 ω = X 0 ω := by
  first
  | (unfold ruStopped; rw [Nat.zero_min])
  | (unfold ruStopped; simp)
  | (simp [ruStopped])

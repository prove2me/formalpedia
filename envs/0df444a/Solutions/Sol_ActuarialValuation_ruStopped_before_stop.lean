-- Prove2me | solution 1 for ActuarialValuation.ruStopped_before_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:09:23.190463+00:00
-- url     : https://prove2.me/submissions/863f4cf5-ed38-4c9d-997b-4b24b0f14e45

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
    (k : ℕ) (ω : Fin m) (hτ : k ≤ τ ω) :
    ruStopped X τ k ω = X k ω := by
  first
  | (unfold ruStopped; exact min_eq_right hτ)
  | (unfold ruStopped; simp [hτ])
  | (simp [ruStopped, hτ])

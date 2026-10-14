-- Prove2me | solution 1 for ActuarialValuation.ruStopped_past_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:11:13.54993+00:00
-- url     : https://prove2.me/submissions/39a6d1ee-0a89-41ef-aed1-7ac64499dd8c

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
    (k : ℕ) (ω : Fin m) (hτ : τ ω ≤ k) :
    ruStopped X τ k ω = X (τ ω) ω := by
  first
  | (unfold ruStopped; exact min_eq_left hτ)
  | (unfold ruStopped; simp [hτ])
  | (simp [ruStopped, hτ])

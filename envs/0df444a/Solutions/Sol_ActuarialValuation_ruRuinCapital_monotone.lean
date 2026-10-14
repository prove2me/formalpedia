-- Prove2me | solution 1 for ActuarialValuation.ruRuinCapital_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:04:47.450975+00:00
-- url     : https://prove2.me/submissions/ca116be0-7931-4bc1-9ec8-1d423072471f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruRuinAtHorizon
import Definitions.Def_actuarial_ruSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u v : ℝ) (G : ℕ → Fin m → ℝ) (N : ℕ) (huv : u ≤ v)
    (ω : Fin m) :
    ruRuinAtHorizon v G N ω → ruRuinAtHorizon u G N ω := by
  intro h
  unfold ruRuinAtHorizon at h ⊢
  unfold ruSurplus at h ⊢
  obtain ⟨k, hkmem, hlt⟩ := h
  exact ⟨k, hkmem, by linarith⟩

-- Prove2me | solution 1 for ActuarialValuation.ruRuinAtHorizon_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:18:03.719386+00:00
-- url     : https://prove2.me/submissions/1ee2f4a6-45e0-4d4d-9425-7681ad75b7f8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinAtHorizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (N K : ℕ) (hNK : N ≤ K)
    (ω : Fin m) :
    ruRuinAtHorizon u G N ω → ruRuinAtHorizon u G K ω := by
  intro h
  unfold ruRuinAtHorizon at h ⊢
  obtain ⟨k, hkmem, hlt⟩ := h
  refine ⟨k, ?_, hlt⟩
  first
  | (rw [Finset.mem_range] at hkmem ⊢; omega)
  | (simp only [Finset.mem_range] at hkmem ⊢; omega)

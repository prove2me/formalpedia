-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_positive_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:04:38.763964+00:00
-- url     : https://prove2.me/submissions/4d173ef5-e575-4d13-bdb1-c51ee9bcbc76

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStateZeroBond

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount : Fin m → ℝ) (hp : ∀ ω,0≤p ω) (hd : ∀ ω,0<discount ω) (hpos : ∃ ω, 0<p ω) : 0<bdStateZeroBond p discount := by
  unfold bdStateZeroBond bdStatePV
  simp only [mul_one]
  apply Finset.sum_pos'
  · intro ω hω
    exact mul_nonneg (hp ω) (le_of_lt (hd ω))
  · obtain ⟨ω, hω⟩ := hpos
    exact ⟨ω, Finset.mem_univ _, mul_pos hω (hd ω)⟩

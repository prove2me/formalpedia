-- Prove2me | solution 1 for Arxiv2012_05254.closure_phase_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:55:51.119303+00:00
-- url     : https://prove2.me/submissions/db2a14bf-b09f-408a-a585-6371579bcd28

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

open Arxiv2012_05254 in
theorem solution (x : Fin 3 → Plane) (ψ : Fin 3 → ℝ) (s₀ : Plane) :
    (∀ a, npc (spacing x a) (recentredPhase (spacing x a) (ψ a) s₀) =
      (fun s => s - s₀) '' npc (spacing x a) (ψ a)) ∧
    closurePhase (fun a => recentredPhase (spacing x a) (ψ a) s₀) = closurePhase ψ := by
  constructor
  · intro a
    ext s
    simp only [npc, recentredPhase, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨s + s₀, ?_, by simp⟩
      rw [inner_add_right]; linarith
    · rintro ⟨t, ht, rfl⟩
      rw [inner_sub_right]; linarith
  · simp only [closurePhase, recentredPhase, Fin.sum_univ_three, spacing]
    have : ⟪x (0 + 1) - x 0, s₀⟫ + ⟪x (1 + 1) - x 1, s₀⟫ + ⟪x (2 + 1) - x 2, s₀⟫ = 0 := by
      rw [← inner_add_left, ← inner_add_left]
      have : x (0 + 1) - x 0 + (x (1 + 1) - x 1) + (x (2 + 1) - x 2) = 0 := by
        have h1 : (0 + 1 : Fin 3) = 1 := rfl
        have h2 : (1 + 1 : Fin 3) = 2 := rfl
        have h3 : (2 + 1 : Fin 3) = 0 := rfl
        rw [h1, h2, h3]; abel
      rw [this, inner_zero_left]
    linear_combination 2 * Real.pi * this

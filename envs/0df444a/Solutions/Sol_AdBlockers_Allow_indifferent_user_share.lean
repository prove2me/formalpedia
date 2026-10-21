-- Prove2me | solution 1 for AdBlockers.Allow.indifferent_user_share
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:50:45.712054+00:00
-- url     : https://prove2.me/submissions/8c7618e4-cf24-4348-adcd-e4515d3898a9

import Mathlib
import Definitions.Def_AdBlockers_Allow_Duopoly

set_option autoImplicit false
open MeasureTheory AdBlockers.Allow

theorem solution (m d₁ d₂ : ℝ) :
    volume {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ m + x - d₂ < m + (1 - x) - d₁} =
      ENNReal.ofReal (hotellingShare d₁ d₂) := by
  set c : ℝ := (1 + d₂ - d₁) / 2 with hc
  have hS : {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ m + x - d₂ < m + (1 - x) - d₁}
      = Set.Icc (0 : ℝ) 1 ∩ Set.Iio c := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iio, hc]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith
  rw [hS]
  have hsh : hotellingShare d₁ d₂ = max 0 (min 1 c) := rfl
  rw [hsh]
  rcases le_or_gt c 0 with h0 | h0
  · have : Set.Icc (0 : ℝ) 1 ∩ Set.Iio c = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_empty_iff_false,
        iff_false, not_and, not_lt]
      intro h; linarith [h.1]
    rw [this, min_eq_right (by linarith : c ≤ 1), max_eq_left h0]
    simp
  rcases le_or_gt c 1 with h1 | h1
  · have : Set.Icc (0 : ℝ) 1 ∩ Set.Iio c = Set.Ico 0 c := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, by linarith⟩, b⟩
    rw [this, min_eq_right h1, max_eq_right h0.le, Real.volume_Ico]
    simp
  · have : Set.Icc (0 : ℝ) 1 ∩ Set.Iio c = Set.Icc 0 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio]
      constructor
      · rintro ⟨a, _⟩; exact a
      · rintro ⟨a, b⟩; exact ⟨⟨a, b⟩, by linarith⟩
    rw [this, min_eq_left h1.le, max_eq_right zero_le_one, Real.volume_Icc]
    simp

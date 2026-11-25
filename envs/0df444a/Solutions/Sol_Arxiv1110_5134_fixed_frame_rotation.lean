-- Prove2me | solution 1 for Arxiv1110_5134.fixed_frame_rotation
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T07:59:08.933509+00:00
-- url     : https://prove2.me/submissions/dc6717a0-fc63-42c3-ae45-262d399dd23f

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

private lemma stokesRot_neg_mul (ψ : ℝ) : stokesRot (-ψ) * stokesRot ψ = 1 := by
  have hcs := Real.sin_sq_add_cos_sq (2 * ψ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stokesRot, Matrix.mul_apply, Fin.sum_univ_four, mul_neg, Real.cos_neg, Real.sin_neg] <;>
    nlinarith [hcs]

theorem solution (σ φ : ℝ) :
    stokesRot (-φ) * stokesRot φ = 1 ∧
    (0 < σ → modRot σ φ = stokesRot φ) ∧
    (σ < 0 → modRot σ φ = stokesRot (-φ)) ∧
    (σ ≠ 0 → modRot σ (-φ) * modRot σ φ = 1 ∧ modRot σ φ * modRot σ (-φ) = 1) ∧
    (σ ≠ 0 → ∀ I IG : Stokes, IG = modRot σ φ *ᵥ I ↔ I = modRot σ (-φ) *ᵥ IG) := by
  have hpos : ∀ ψ, 0 < σ → modRot σ ψ = stokesRot ψ := by
    intro ψ hσ
    ext i j
    simp [modRot, Real.sign_of_pos hσ]
    ring
  have hneg : ∀ ψ, σ < 0 → modRot σ ψ = stokesRot (-ψ) := by
    intro ψ hσ
    ext i j
    simp [modRot, Real.sign_of_neg hσ]
    ring
  have hinv : σ ≠ 0 → modRot σ (-φ) * modRot σ φ = 1 ∧ modRot σ φ * modRot σ (-φ) = 1 := by
    intro hσ
    rcases lt_or_gt_of_ne hσ with h | h
    · rw [hneg (-φ) h, hneg φ h, neg_neg]
      exact ⟨by simpa [neg_neg] using stokesRot_neg_mul (-φ), stokesRot_neg_mul φ⟩
    · rw [hpos (-φ) h, hpos φ h]
      exact ⟨stokesRot_neg_mul φ, by simpa [neg_neg] using stokesRot_neg_mul (-φ)⟩
  refine ⟨stokesRot_neg_mul φ, hpos φ, hneg φ, hinv, ?_⟩
  intro hσ I IG
  obtain ⟨hL, hR⟩ := hinv hσ
  constructor
  · rintro rfl
    rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

-- Prove2me | solution 1 for ALADIN.LocalStab.bound_from_partial_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:41:12.592201+00:00
-- url     : https://prove2.me/submissions/3d1bf0fe-659e-4c34-aac3-bb63ca644433

import Mathlib

open Filter Topology

theorem solution {X Λ Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ξ : X × Λ → Y) (ξ' : X × Λ →L[ℝ] Y) (xs : X) (lamS : Λ)
    (hξ : HasFDerivAt ξ ξ' (xs, lamS)) (χ₁ χ₂ : ℝ)
    (h₁ : ‖ξ'.comp (ContinuousLinearMap.inl ℝ X Λ)‖ < χ₁)
    (h₂ : ‖ξ'.comp (ContinuousLinearMap.inr ℝ X Λ)‖ < χ₂) :
    ∀ᶠ p in 𝓝 (xs, lamS), ‖ξ p - ξ (xs, lamS)‖ ≤ χ₁ * ‖p.1 - xs‖ + χ₂ * ‖p.2 - lamS‖ := by
  set a := ‖ξ'.comp (ContinuousLinearMap.inl ℝ X Λ)‖ with ha
  set b := ‖ξ'.comp (ContinuousLinearMap.inr ℝ X Λ)‖ with hb
  set ε := min (χ₁ - a) (χ₂ - b) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ χ₁ - a := min_le_left _ _
  have hε2 : ε ≤ χ₂ - b := min_le_right _ _
  filter_upwards [hξ.isLittleO.def hεpos] with p hp
  set s : X × Λ := (xs, lamS)
  have hsplit : p - s = (ContinuousLinearMap.inl ℝ X Λ) (p.1 - xs)
      + (ContinuousLinearMap.inr ℝ X Λ) (p.2 - lamS) := by
    ext <;> simp [s]
  have hlin : ‖ξ' (p - s)‖ ≤ a * ‖p.1 - xs‖ + b * ‖p.2 - lamS‖ := by
    rw [hsplit, map_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (ξ'.comp (ContinuousLinearMap.inl ℝ X Λ)).le_opNorm (p.1 - xs)
    · exact (ξ'.comp (ContinuousLinearMap.inr ℝ X Λ)).le_opNorm (p.2 - lamS)
  have hnorm : ‖p - s‖ ≤ ‖p.1 - xs‖ + ‖p.2 - lamS‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have htri : ‖ξ p - ξ s‖ ≤ ‖ξ p - ξ s - ξ' (p - s)‖ + ‖ξ' (p - s)‖ := by
    have := norm_add_le (ξ p - ξ s - ξ' (p - s)) (ξ' (p - s))
    simpa using this
  have hn1 := norm_nonneg (p.1 - xs)
  have hn2 := norm_nonneg (p.2 - lamS)
  have : ε * ‖p - s‖ ≤ ε * (‖p.1 - xs‖ + ‖p.2 - lamS‖) :=
    mul_le_mul_of_nonneg_left hnorm hεpos.le
  nlinarith

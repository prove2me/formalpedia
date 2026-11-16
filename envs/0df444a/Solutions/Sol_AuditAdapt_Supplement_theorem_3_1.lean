-- Prove2me | solution 1 for AuditAdapt.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:05:28.524484+00:00
-- url     : https://prove2.me/submissions/b64006ce-efd4-4cbf-af86-2df6d41c831a

import Mathlib

theorem solution {n T : ℕ} (Z : Set (Fin n → ℝ)) (hZconv : Convex ℝ Z) (hZcpt : IsCompact Z)
    (c z : Fin T → Fin n → ℝ) (hz : ∀ t, z t ∈ Z) (zstar : Fin n → ℝ) (hzstar : zstar ∈ Z)
    (hmin : ∀ y ∈ Z, ((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ zstar ≤ ((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ y) :
    (∑ t, c t ⬝ᵥ z t) - sInf ((fun y => ∑ t, c t ⬝ᵥ y) '' Z) =
        (∑ t, (c t - (T : ℝ)⁻¹ • ∑ t', c t') ⬝ᵥ (z t - (T : ℝ)⁻¹ • ∑ t', z t')) +
          (T : ℝ) * (((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ ((T : ℝ)⁻¹ • ∑ t, z t - zstar)) ∧
      0 ≤ (T : ℝ) * (((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ ((T : ℝ)⁻¹ • ∑ t, z t - zstar)) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have hne : Z.Nonempty := ⟨zstar, hzstar⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero,
      le_refl, and_true]
    rw [hne.image_const, csInf_singleton]
    simp
  · have hτ : (T : ℝ) ≠ 0 := by positivity
    have hτpos : (0 : ℝ) < T := by positivity
    set C := ∑ t, c t with hC
    set W := ∑ t, z t with hW
    have hsum : ∀ y, (∑ t, c t ⬝ᵥ y) = C ⬝ᵥ y := by
      intro y; rw [hC, sum_dotProduct]
    have hscale : ∀ y, C ⬝ᵥ y = (T : ℝ) * (((T : ℝ)⁻¹ • C) ⬝ᵥ y) := by
      intro y; rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hτ, one_mul]
    have hinf : sInf ((fun y => ∑ t, c t ⬝ᵥ y) '' Z) = C ⬝ᵥ zstar := by
      apply IsLeast.csInf_eq
      refine ⟨⟨zstar, hzstar, hsum zstar⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      simp only
      rw [hsum y, hscale y, hscale zstar]
      exact mul_le_mul_of_nonneg_left (hmin y hy) hτpos.le
    have hbar : (T : ℝ)⁻¹ • W ∈ Z := by
      have := hZconv.sum_mem (t := Finset.univ) (w := fun _ => (T : ℝ)⁻¹) (z := z)
        (fun _ _ => by positivity) (by simp [Finset.card_univ, Fintype.card_fin, hτ])
        (fun i _ => hz i)
      simpa [hW, Finset.smul_sum] using this
    constructor
    · rw [hinf]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, Finset.sum_sub_distrib, smul_eq_mul]
      have e1 : ∑ x, (T : ℝ)⁻¹ * C ⬝ᵥ z x = (T : ℝ)⁻¹ * C ⬝ᵥ W := by
        rw [← Finset.mul_sum, ← dotProduct_sum, ← hW]
      have e2 : ∑ x, (T : ℝ)⁻¹ * (c x ⬝ᵥ W - (T : ℝ)⁻¹ * C ⬝ᵥ W) =
          (T : ℝ)⁻¹ * (C ⬝ᵥ W - (T : ℝ) * ((T : ℝ)⁻¹ * C ⬝ᵥ W)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← sum_dotProduct, ← hC]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [e1, e2]
      field_simp
      ring
    · apply mul_nonneg hτpos.le
      rw [dotProduct_sub, sub_nonneg]
      exact hmin _ hbar

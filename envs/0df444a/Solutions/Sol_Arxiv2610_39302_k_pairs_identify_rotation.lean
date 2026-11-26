-- Prove2me | solution 1 for Arxiv2610_39302.k_pairs_identify_rotation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T07:35:54.916224+00:00
-- url     : https://prove2.me/submissions/9a2000f3-064a-40a1-9f78-089eab7b2b38

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open Matrix

noncomputable section
namespace KPX
open Arxiv2610_39302

lemma sqNorm_nonneg {k : ℕ} (a : Fin k → ℝ) : 0 ≤ sqNorm a :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (a i))

lemma sqNorm_eq_zero {k : ℕ} (a : Fin k → ℝ) (h : sqNorm a = 0) : a = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i))).1 h i
    (Finset.mem_univ i)
  simpa using this

lemma whiten_rot {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (h : Z → Fin k → ℝ)
    (hh : IsWhitened p h) (R : Matrix.orthogonalGroup (Fin k) ℝ) :
    IsWhitened p (fun z => rot R (h z)) := by
  obtain ⟨h1, h2⟩ := hh
  set M : Matrix (Fin k) (Fin k) ℝ := (R : Matrix (Fin k) (Fin k) ℝ)
  have hR : M * Mᵀ = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).1 R.2
    simpa [M] using this
  constructor
  · intro i
    simp only [rot, Matrix.mulVec, dotProduct]
    have : ∑ x, p x * ∑ j, M i j * h x j = ∑ j, M i j * ∑ x, p x * h x j := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro x _; ring
    rw [this]; simp [h1]
  · intro i j
    simp only [rot, Matrix.mulVec, dotProduct]
    have : ∑ x, p x * (∑ a, M i a * h x a) * (∑ b, M j b * h x b)
        = ∑ a, ∑ b, M i b * M j a * ∑ x, p x * h x b * h x a := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro x _; ring
    rw [this]
    simp only [h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := congrFun (congrFun hR i) j
    rw [Matrix.mul_apply] at this
    simp only [Matrix.transpose_apply] at this
    rw [this, Matrix.one_apply]

end KPX
end

open KPX Arxiv2610_39302 in
theorem solution {Z X₁ X₂ : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z)
    (hgap : k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k)
    (g₁ : Z → X₁) (g₂ : Z → X₂) (hg₁ : Function.Injective g₁) (hg₂ : Function.Injective g₂)
    (f₁ : X₁ → Fin k → ℝ) (f₂ : X₂ → Fin k → ℝ)
    (hf₁ : ∀ f : X₁ → Fin k → ℝ, modalityLoss p π sqDist whiteningReg g₁ f₁ ≤ modalityLoss p π sqDist whiteningReg g₁ f)
    (hf₂ : ∀ f : X₂ → Fin k → ℝ, modalityLoss p π sqDist whiteningReg g₂ f₂ ≤ modalityLoss p π sqDist whiteningReg g₂ f) :
    (∀ h : Z → Fin k → ℝ, IsWhitened p h →
      ∀ R : Matrix.orthogonalGroup (Fin k) ℝ, IsWhitened p (fun z => rot R (h z))) ∧
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ, (∀ z, f₁ (g₁ z) = rot Q (f₂ (g₂ z))) →
      ∀ (n : ℕ) (zs : Fin n → Z), k ≤ n →
        Submodule.span ℝ (Set.range fun i => f₂ (g₂ (zs i))) = ⊤ →
        (∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot Q (f₂ (g₂ (zs i)))) ≤
            ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i))))) ∧
        ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          (∀ R' : Matrix.orthogonalGroup (Fin k) ℝ,
            ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i)))) ≤
              ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R' (f₂ (g₂ (zs i))))) → R = Q) := by
  refine ⟨fun h hh R => whiten_rot p h hh R, fun Q hQ n zs _ hspan => ?_⟩
  have h0 : ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot Q (f₂ (g₂ (zs i)))) = 0 := by
    simp [hQ, sqNorm]
  refine ⟨fun R => by rw [h0]; exact Finset.sum_nonneg (fun i _ => sqNorm_nonneg _), fun R hR => ?_⟩
  have hle := hR Q
  rw [h0] at hle
  have hz : ∀ i, sqNorm (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i)))) = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sqNorm_nonneg
      (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i)))))).1
      (le_antisymm hle (Finset.sum_nonneg (fun i _ => sqNorm_nonneg _))) i (Finset.mem_univ i)
    exact this
  have heq : ∀ i, (R : Matrix (Fin k) (Fin k) ℝ) *ᵥ f₂ (g₂ (zs i)) =
      (Q : Matrix (Fin k) (Fin k) ℝ) *ᵥ f₂ (g₂ (zs i)) := by
    intro i
    have := sub_eq_zero.1 (sqNorm_eq_zero _ (hz i))
    rw [hQ] at this
    exact this.symm
  have hlin : Matrix.toLin' (R : Matrix (Fin k) (Fin k) ℝ) = Matrix.toLin' (Q : Matrix (Fin k) (Fin k) ℝ) :=
    LinearMap.ext_on_range hspan (fun i => by simpa [Matrix.toLin'_apply] using heq i)
  exact Subtype.ext (Matrix.toLin'.injective hlin)

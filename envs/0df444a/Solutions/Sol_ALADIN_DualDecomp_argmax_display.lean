-- Prove2me | solution 1 for ALADIN.DualDecomp.argmax_display
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:57:14.835978+00:00
-- url     : https://prove2.me/submissions/89e44767-318b-4304-9f83-0ddfe80baa2a

import Mathlib

open Matrix

private theorem negative_shift {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : (-M).PosSemidef) (μ : ℝ) (hμ : 0 < μ) :
    (-(M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))).PosDef := by
  have hp : (μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (inv_pos.mpr hμ)
  have he : -(M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) = μ⁻¹ • 1 + -M := by abel
  rw [he]
  exact hp.add_posSemidef hM

theorem solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : (-M).PosSemidef)
    (μ : ℝ) (hμ : 0 < μ) (lam g : Fin m → ℝ) :
    let φ : (Fin m → ℝ) → ℝ := fun ν =>
      1 / 2 * ((ν - lam) ⬝ᵥ (M *ᵥ (ν - lam))) + ν ⬝ᵥ g - 1 / (2 * μ) * ((ν - lam) ⬝ᵥ (ν - lam))
    let νstar := lam - (M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ g
    IsUnit (M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).det ∧
    IsMaxOn φ Set.univ νstar ∧
    ∀ ν, φ ν = φ νstar → ν = νstar := by
  let A := M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)
  let νstar := lam - A⁻¹ *ᵥ g
  let φ : (Fin m → ℝ) → ℝ := fun ν =>
    1 / 2 * ((ν - lam) ⬝ᵥ (M *ᵥ (ν - lam))) + ν ⬝ᵥ g -
      1 / (2 * μ) * ((ν - lam) ⬝ᵥ (ν - lam))
  change IsUnit A.det ∧ IsMaxOn φ Set.univ νstar ∧ ∀ ν, φ ν = φ νstar → ν = νstar
  have hA : (-A).PosDef := negative_shift M hM μ hμ
  have hu : IsUnit A := by simpa using hA.isUnit
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hsym : Aᵀ = A := by
    have ht := hA.isHermitian.eq
    simpa using ht
  have symm (u v : Fin m → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hz : A *ᵥ (νstar - lam) = -g := by
    have he : νstar - lam = -(A⁻¹ *ᵥ g) := by dsimp [νstar]; abel
    rw [he, Matrix.mulVec_neg, Matrix.mulVec_mulVec, A.mul_nonsing_inv hd, Matrix.one_mulVec]
  have he (ν : Fin m → ℝ) : φ ν =
      1 / 2 * ((ν - lam) ⬝ᵥ (A *ᵥ (ν - lam))) + ν ⬝ᵥ g := by
    dsimp [φ, A]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    <;> ring
  have identity (ν : Fin m → ℝ) :
      φ ν - φ νstar = 1 / 2 * ((ν - νstar) ⬝ᵥ (A *ᵥ (ν - νstar))) := by
    rw [he ν, he νstar]
    have he1 : ν - lam = (ν - νstar) + (νstar - lam) := by abel
    rw [he1]
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    rw [symm (νstar - lam) (ν - νstar), hz, dotProduct_neg, dotProduct_neg]
    simp only [sub_dotProduct]
    ring
  refine ⟨hd, ?_, ?_⟩
  · intro ν _
    change φ ν ≤ φ νstar
    have hn := hA.posSemidef.dotProduct_mulVec_nonneg (ν - νstar)
    simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] at hn
    have hi := identity ν
    linarith
  · intro ν hν
    by_contra hne
    have hn := hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] at hn
    have hi := identity ν
    rw [hν, sub_self] at hi
    linarith

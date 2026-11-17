-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_bezoutCertificates_of_iso_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:41.173423+00:00
-- url     : https://prove2.me/submissions/c54dc1a3-7dca-4331-97af-7b1ac5e7f202

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_MvPolynomial_exists_homogeneous_bezout_mod_ideal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append_homogeneousIdeal

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem _root_.solution {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ (D₁ D₂ : ℕ)
      (q₁ : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) × Fin (N₁ + 1) → MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)
      (q₂ : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) × Fin (N₂ + 1) → MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K),
      (∀ a, (q₁ a).IsHomogeneous D₁) ∧ (∀ a, (q₂ a).IsHomogeneous D₂) ∧
      ∀ x : Scheme.KPoint f, ∃ (z : Fin (N₁ + 1) ⊕ Fin (N₂ + 1) → K)
          (h₁ : z ∘ Sum.inl ≠ 0) (h₂ : z ∘ Sum.inr ≠ 0),
        P₁.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inl) h₁ ∧
        P₂.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inr) h₂ ∧
        (∀ k, ∑ i, (q₁ (k, i)).eval z * z (Sum.inl i) = z k ^ (D₁ + 1)) ∧
        (∀ k, ∑ j, (q₂ (k, j)).eval z * z (Sum.inr j) = z k ^ (D₂ + 1))  := by
  classical
  obtain ⟨I, hzero₁, hzero₂, hpoint⟩ :=
    exists_append_homogeneousIdeal P₁ P₂ e hfin
  obtain ⟨D₁, q₁, hq₁, hmem₁⟩ :=
    MvPolynomial.exists_homogeneous_bezout_mod_ideal I.toIdeal I.isHomogeneous Sum.inl hzero₁
  obtain ⟨D₂, q₂, hq₂, hmem₂⟩ :=
    MvPolynomial.exists_homogeneous_bezout_mod_ideal I.toIdeal I.isHomogeneous Sum.inr hzero₂
  refine ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, ?_⟩
  intro x
  obtain ⟨z, h₁, h₂, hp₁, hp₂, hvanish⟩ := hpoint x
  refine ⟨z, h₁, h₂, hp₁, hp₂, ?_, ?_⟩
  · intro k
    have h := hvanish _ (hmem₁ k)
    have heq := h
    simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.eval_X] at heq
    exact (sub_eq_zero.mp heq).symm
  · intro k
    have h := hvanish _ (hmem₂ k)
    have heq := h
    simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.eval_X] at heq
    exact (sub_eq_zero.mp heq).symm

end AlgebraicGeometry.Scheme.Modules.ProjPresentation

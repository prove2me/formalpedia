-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:41.7726+00:00
-- url     : https://prove2.me/submissions/83f7dfe1-0efe-4418-a2dd-0d78a2ae7b33

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_Height_exists_logHeight_le_restrict_add_of_bezout
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append_bezoutCertificates_of_iso_of_isFinite

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem _root_.solution {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Scheme.KPoint f, |P₁.pointLogHeight x - P₂.pointLogHeight x| ≤ C := by
  obtain ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, hcert⟩ :=
    exists_append_bezoutCertificates_of_iso_of_isFinite P₁ P₂ e hfin
  obtain ⟨C₁, hC₁, hbound₁⟩ :=
    Height.exists_logHeight_le_restrict_add_of_bezout Sum.inl q₁ hq₁
  obtain ⟨C₂, hC₂, hbound₂⟩ :=
    Height.exists_logHeight_le_restrict_add_of_bezout Sum.inr q₂ hq₂
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), ?_⟩
  intro x
  obtain ⟨z, hz₁, hz₂, hp₁, hp₂, hbez₁, hbez₂⟩ := hcert x
  change |Projectivization.logHeight (P₁.pointProjectivization x) -
    Projectivization.logHeight (P₂.pointProjectivization x)| ≤ max C₁ C₂
  rw [hp₁, hp₂, Projectivization.logHeight_mk, Projectivization.logHeight_mk]
  have hfull₁ := hbound₁ z hbez₁
  have hfull₂ := hbound₂ z hbez₂
  have hrestrict₁ := Height.logHeight_comp_le Sum.inl z
  have hrestrict₂ := Height.logHeight_comp_le Sum.inr z
  have hmax₁ : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hmax₂ : C₂ ≤ max C₁ C₂ := le_max_right _ _
  apply abs_le.mpr
  constructor <;> linarith

end AlgebraicGeometry.Scheme.Modules.ProjPresentation

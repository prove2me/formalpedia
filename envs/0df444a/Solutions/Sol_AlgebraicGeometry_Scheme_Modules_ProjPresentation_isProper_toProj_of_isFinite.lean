-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.isProper_toProj_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:56.6689+00:00
-- url     : https://prove2.me/submissions/6d2e1aaf-8df5-4fcb-8d41-604b19f5fa95

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- One finite presentation makes every presentation of the same scheme proper. -/
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (hfin : IsFinite P₁.toProj) : IsProper P₂.toProj := by
  letI : IsFinite P₁.toProj := hfin
  haveI : IsProper f := by rw [← P₁.toProj_π]; infer_instance
  haveI : IsProper (P₂.toProj ≫ ProjSpace.π K N₂) := by rw [P₂.toProj_π]; infer_instance
  exact IsProper.of_comp P₂.toProj (ProjSpace.π K N₂)

end AlgebraicGeometry.Scheme.Modules.ProjPresentation

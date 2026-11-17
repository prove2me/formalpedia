-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_pullback_pointLogHeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:55.454614+00:00
-- url     : https://prove2.me/submissions/a25d7019-8685-4923-9458-a8e3d3658116

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- The canonical pullback frame preserves the projective height after composition. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K]
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    (p : Y ⟶ X) {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) :
    ∃ P' : ((Scheme.Modules.pullback p).obj M).ProjPresentation (p ≫ f) N,
      (∀ i, P'.σ i =
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤)
          (P.σ i)) ∧
      P'.toProj = p ≫ P.toProj ∧
      ∀ y : Scheme.KPoint (p ≫ f),
        P'.pointLogHeight y =
          P.pointLogHeight
            ⟨y.1 ≫ p, by rw [Category.assoc, y.2]⟩  := by
  obtain ⟨P', hσ, hp⟩ := P.exists_projPresentation_pullback_sigma_eq_toProj_eq p
  refine ⟨P', hσ, hp, ?_⟩
  intro y
  unfold pointLogHeight pointProjectivization
  congr 2
  apply Subtype.ext
  dsimp
  rw [hp, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.ProjPresentation

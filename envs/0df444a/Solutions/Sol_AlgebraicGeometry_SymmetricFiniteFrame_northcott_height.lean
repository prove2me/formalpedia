-- Prove2me | solution 1 for AlgebraicGeometry.SymmetricFiniteFrame.northcott_height
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:00.106248+00:00
-- url     : https://prove2.me/submissions/eb2a9763-bce2-413c-ad72-1a316b48ebf9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_northcott_pointLogHeight_of_isFinite
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SymmetricFiniteFrame

/-- Rational points of bounded frame height form a finite set. -/
theorem _root_.solution {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) : ∀ B : ℝ, {x : Scheme.KPoint f | F.height x ≤ B}.Finite := by
  exact F.presentation.northcott_pointLogHeight_of_isFinite F.presentation_finite

end AlgebraicGeometry.SymmetricFiniteFrame

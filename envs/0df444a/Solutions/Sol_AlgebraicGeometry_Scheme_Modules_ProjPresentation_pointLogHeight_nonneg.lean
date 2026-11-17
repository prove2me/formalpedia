-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointLogHeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:08.874968+00:00
-- url     : https://prove2.me/submissions/204b1e35-f0d6-4bac-b074-40b8ee243ae0

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Projective logarithmic height is nonnegative with the number-field normalization. -/
theorem _root_.solution {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (x : Scheme.KPoint f) : 0 ≤ P.pointLogHeight x := by
  exact Projectivization.logHeight_nonneg (P.pointProjectivization x)

end AlgebraicGeometry.Scheme.Modules.ProjPresentation

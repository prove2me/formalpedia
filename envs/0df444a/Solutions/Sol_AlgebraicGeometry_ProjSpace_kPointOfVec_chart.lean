-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_chart
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:47.001622+00:00
-- url     : https://prove2.me/submissions/a493df83-e76f-412c-a64c-67a076fda683

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry

/-- The scheme point associated with a vector has the usual homogeneous
coordinate ratios on each standard affine chart. -/
theorem _root_.solution (K : Type) [Field K] (N : ℕ) (v : Fin (N + 1) → K) (hv : v ≠ 0)
    (i : Fin (N + 1)) (hi : v i ≠ 0) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K,
      (∀ j, φ (ProjSpace.ratio K N i j) = v j / v i) ∧
      (ProjSpace.kPointOfVec K N v hv).1 = Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
          (ProjSpace.X_mem_one K N i) one_pos := by
  exact ProjSpace.kPointOfVec_has_charts K N v hv i hi

end AlgebraicGeometry

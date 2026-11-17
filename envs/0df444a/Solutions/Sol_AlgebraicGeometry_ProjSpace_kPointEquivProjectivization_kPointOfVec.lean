-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointEquivProjectivization_kPointOfVec
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:37.472252+00:00
-- url     : https://prove2.me/submissions/746f9af8-969a-4a9a-ba1b-00faa2b9664e

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry

theorem _root_.solution (K : Type) [Field K] (N : ℕ)
    (v) (hv : v ≠ 0) :
    ProjSpace.kPointEquivProjectivization K N (ProjSpace.kPointOfVec K N v hv) =
      Projectivization.mk K v hv := by
  apply (ProjSpace.kPointEquivProjectivization K N).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

end AlgebraicGeometry

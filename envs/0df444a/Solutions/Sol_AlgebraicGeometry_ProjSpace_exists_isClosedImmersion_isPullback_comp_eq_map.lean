-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2483c79f-d5f7-50c8-af4a-f39c64448a81

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (B : Type u) [CommRing B] [Algebra A B] :
    ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
      (_ : IsClosedImmersion ι') (e : Z' ⟶ Z),
      IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      e ≫ ι = ι' ≫ ProjSpace.map A B n := by
  refine ⟨pullback ι (ProjSpace.map A B n), pullback.snd ι (ProjSpace.map A B n), inferInstance,
    pullback.fst ι (ProjSpace.map A B n), ?_, pullback.condition⟩
  exact (IsPullback.of_hasPullback ι (ProjSpace.map A B n)).paste_vert (ProjSpace.isPullback_map A B n)

end S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map (solution)

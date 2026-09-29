-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointSubBasepoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8d1831c0-0756-5fcf-894d-2d4202bd8a67

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointSubBasepointModule (a := a) P ε) :
    IsAlgEquivZero a L :=
  IsAlgEquivZero.of_fst_pullback_iso e (isAlgEquivZero_pointSubBasepoint P ε)

end S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint (solution)

-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f4db219a-5e06-5d52-b478-cceaddc7c212

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))
    {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) :
    IsAlgEquivZero a L :=
  by
  have key : ∀ Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointsSubBasepointModule (a := a) ε Qs)) := by
    intro Qs
    induction Qs with
    | nil =>
      exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorUnitObjIso _).symm (IsAlgEquivZero.tensorUnit a)
    | cons P Ps ih =>
      exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorObjIso _ _ _).symm
        ((isAlgEquivZero_pointSubBasepoint P ε).tensor ih)
  exact IsAlgEquivZero.of_fst_pullback_iso e (key Ps)

end S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint (solution)

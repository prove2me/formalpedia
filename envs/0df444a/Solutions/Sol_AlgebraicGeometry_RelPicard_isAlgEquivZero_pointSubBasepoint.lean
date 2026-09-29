-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b19ccb61-bb8d-5e8e-afc4-967706c73ef2

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointSubBasepointModule (a := a) P ε)) :=
  by
  refine ⟨A, a, inferInstance, inferInstance, ajFamily (a := a) ε, isInvertible_ajFamily (a := a) ε, ε, P, ?_, ?_⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε ε
    obtain ⟨p⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
      (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a ε.1 ε.2))
    exact ⟨i ≪≫ p⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε P
    exact ⟨i ≪≫ (fstPullbackToProdSpecPullbackIso a _).symm⟩

end S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint (solution)

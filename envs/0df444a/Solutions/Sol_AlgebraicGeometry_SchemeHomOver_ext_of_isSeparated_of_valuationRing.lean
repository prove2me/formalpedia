-- Prove2me | solution 1 for AlgebraicGeometry.SchemeHomOver.ext_of_isSeparated_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/30e0ed34-cf39-54b7-b939-8079744436cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing

open CategoryTheory AlgebraicGeometry NeronModelInfra

universe u

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
         Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by

  have hw : (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [Category.assoc, x.2]
  let sq : ValuativeCommSq f :=
    { R := A, K := K,
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap R A)),
      commSq := ⟨hw⟩ }
  have hsub : Subsingleton sq.commSq.LiftStruct := IsSeparated.valuativeCriterion f sq
  let lx : sq.commSq.LiftStruct := ⟨x.1, rfl, x.2⟩
  let ly : sq.commSq.LiftStruct := ⟨y.1, h.symm, y.2⟩
  have hlxy : lx = ly := hsub.elim lx ly
  have hxy1 : x.1 = y.1 := congrArg CommSq.LiftStruct.l hlxy
  exact Subtype.ext hxy1

end S_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing (solution)

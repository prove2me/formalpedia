-- Prove2me | solution 1 for AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c25ab90f-8f21-5207-a2ee-209d4dc6f7f5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq

open CategoryTheory AlgebraicGeometry NeronModelInfra

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
    (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
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

end S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq (solution)

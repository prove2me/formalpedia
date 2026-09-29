-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/538e6fa7-2155-587d-bdad-ead88afe600f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      AlgebraicGeometry.IsIntegral (pullback f s)) :
    GeometricallyIntegral f := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro K _ y Z fst snd hZ
  suffices hI : AlgebraicGeometry.IsIntegral (pullback f y) by
    haveI := hI
    exact AlgebraicGeometry.IsIntegral.of_isIso hZ.isoPullback.inv
  let Kb := AlgebraicClosure K
  let t : Spec (CommRingCat.of Kb) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  haveI : AlgebraicGeometry.IsIntegral (pullback (pullback.snd f y) t) := by
    have hP := (IsPullback.of_hasPullback (pullback.snd f y) t).paste_horiz (IsPullback.of_hasPullback f y)
    haveI := hgeo Kb (t ≫ y)
    exact AlgebraicGeometry.IsIntegral.of_isIso hP.isoPullback.inv
  haveI : GeometricallyIntegral (pullback.snd (pullback.snd f y) t) := geometricallyIntegral_of_isAlgClosed _
  haveI : GeometricallyIntegral (pullback.snd f y) :=
    GeometricallyIntegral.of_isPullback_of_geometricallyIntegral (pullback.snd f y)
      (pullback.snd (pullback.snd f y) t) (pullback.fst (pullback.snd f y) t) (IsPullback.of_hasPullback _ _)
  exact self_of_isIntegral_of_geometrically (f := pullback.snd f y) GeometricallyIntegral.geometrically_isIntegral

end S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback (solution)

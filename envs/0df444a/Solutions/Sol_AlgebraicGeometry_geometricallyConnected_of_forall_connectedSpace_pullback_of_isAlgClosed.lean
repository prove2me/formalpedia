-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/460d00da-2a5e-5806-8087-d8cc5e1517c4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : R →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
    GeometricallyConnected f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 fun K _ _ => ?_⟩

  let k := AlgebraicClosure K
  let x : R →+* k := (algebraMap K k).comp (algebraMap R K)
  let a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K k))
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hx : Spec.map (CommRingCat.ofHom x) = a ≫ b := by
    simp only [x, a, b, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI hk : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) := h k x

  let p : pullback f (Spec.map (CommRingCat.ofHom x)) ⟶ pullback f b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by rw [pullback.condition, hx, Category.assoc])
  have hp : IsPullback p (pullback.snd f (Spec.map (CommRingCat.ofHom x))) (pullback.snd f b) a := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f b)
    rw [pullback.lift_fst, ← hx]
    exact IsPullback.of_hasPullback f _
  haveI : Surjective a := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    infer_instance
  haveI : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance

  rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr p.surjective]
  exact isConnected_range p.continuous

end S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed (solution)

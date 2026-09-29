-- Prove2me | solution 1 for Algebra.Etale.isReduced_of_isReduced_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/15fd681f-e6db-53c6-a3cc-982b4bcac8e1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleReducedAux

theorem geometricallyReduced_specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  constructor
  intro K _ y Z fst snd hP
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
  letI : Algebra R K := φ.hom.toAlgebra
  have hP' : IsPullback fst snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := hP
  haveI : _root_.IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  haveI : _root_.IsReduced (S ⊗[R] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R S K).toRingHom (Algebra.TensorProduct.comm R S K).injective
  haveI : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (S ⊗[R] K))) := (affine_isReduced_iff _).mpr ‹_›
  exact isReduced_of_isOpenImmersion (hP'.isoPullback ≪≫ pullbackSpecIso R S K).hom

end EtaleReducedAux

theorem solution
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [_root_.IsReduced R] [Algebra.Etale R S] :
    _root_.IsReduced S := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI := EtaleReducedAux.geometricallyReduced_specMap R S
  have h := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp h

end S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing
end P2MW
export P2MW.S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing (solution)

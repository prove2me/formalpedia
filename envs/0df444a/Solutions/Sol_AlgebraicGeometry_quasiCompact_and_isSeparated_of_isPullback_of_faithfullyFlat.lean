-- Prove2me | solution 1 for AlgebraicGeometry.quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e26b30a9-16a6-54ce-ae49-66317e08dc85

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    [QuasiCompact f'] [IsSeparated f'] :
    QuasiCompact f ∧ IsSeparated f := by

  have hff : (CommRingCat.ofHom (algebraMap S S')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap S S'))).mpr hff
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
    ⟨⟨hsurj, hflat⟩, inferInstance⟩
  refine ⟨?_, ?_⟩
  ·
    haveI : Surjective c := MorphismProperty.of_isPullback (P := @Surjective) hc.flip hsurj
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    have hs : Function.Surjective c.base := c.surjective
    haveI : CompactSpace X := ⟨by rw [← hs.range_eq]; exact isCompact_range c.continuous⟩
    exact (quasiCompact_iff_compactSpace f).mpr inferInstance
  ·
    have hP : (MorphismProperty.diagonal @UniversallyClosed : MorphismProperty Scheme.{u}) f' := by
      show UniversallyClosed (pullback.diagonal f')
      infer_instance
    haveI hU : UniversallyClosed (pullback.diagonal f) :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip hQ hP
    exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩

end S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat (solution)

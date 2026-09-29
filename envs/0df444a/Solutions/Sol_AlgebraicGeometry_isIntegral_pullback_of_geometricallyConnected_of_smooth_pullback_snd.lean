-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/80120022-873a-5a48-9c27-d0e7783dacb2

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R K L : Type u} [CommRing R] [Field K] [Field L] (i : R →+* K) (j : K →+* L)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom i)))]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom i)))] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by
  haveI hS : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) :=
    AlgebraicGeometry.pullback_snd_specMap_comp_of_isStableUnderBaseChange @Smooth i j f ‹_›
  haveI hG : GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) :=
    AlgebraicGeometry.pullback_snd_specMap_comp_of_isStableUnderBaseChange @GeometricallyConnected i j f ‹_›
  haveI : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (j.comp i)))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i))))
  exact AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
    (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i))))

end S_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd (solution)

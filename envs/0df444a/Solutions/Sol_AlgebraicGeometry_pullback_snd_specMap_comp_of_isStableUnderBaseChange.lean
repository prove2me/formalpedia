-- Prove2me | solution 1 for AlgebraicGeometry.pullback_snd_specMap_comp_of_isStableUnderBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1b358d94-abb9-56da-b4af-4e787c027d5e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (i : R →+* S) (j : S →+* T)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : P (pullback.snd f (Spec.map (CommRingCat.ofHom i)))) :
    P (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by
  have hcomp : Spec.map (CommRingCat.ofHom (j.comp i)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hcomp, ← pullbackLeftPullbackSndIso_inv_snd_snd f (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom j))]
  rw [P.cancel_left_of_respectsIso]
  exact P.pullback_snd _ _ h

end S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange
end P2MW
export P2MW.S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange (solution)

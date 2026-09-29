-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyReduced_of_isReduced_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ef290a22-bb49-54d4-aad9-34768571d2b9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type) [Field k] [CharZero k] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [IsReduced X] :
    GeometricallyReduced g := by

  have h := AlgebraicGeometry.geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero k k X g

  have hι : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
    rw [show algebraMap k k = RingHom.id k from rfl, CommRingCat.ofHom_id]; exact Spec.map_id _
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by rw [hι]; infer_instance

  have hcond := pullback.condition (f := g) (g := Spec.map (CommRingCat.ofHom (algebraMap k k)))
  have h1 : GeometricallyReduced (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [GeometricallyReduced.eq_geometrically] at h ⊢
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).2 h
  rw [← hcond] at h1
  rw [GeometricallyReduced.eq_geometrically] at h1 ⊢
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 h1

end S_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero (solution)

-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b4f7b5f9-94c5-5a51-be83-8b8d332cdc37

import Mathlib
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyConnected f := by
  set g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K k)) with hg
  haveI hirr : GeometricallyIrreducible (pullback.snd f g) :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed (pullback.snd f g)
  have hconn : GeometricallyConnected (pullback.snd f g) :=
    AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected (pullback.snd f g)
  have hsurj : Surjective g := ⟨fun x => ⟨(⊥ : PrimeSpectrum k), Subsingleton.elim _ _⟩⟩
  haveI : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @GeometricallyConnected) (Q := @Surjective) hsurj hconn

end S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed (solution)

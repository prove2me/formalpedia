-- Prove2me | solution 1 for AlgebraicGeometry.surjective_and_generalizingMap_pullback_fst_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b08357cd-607d-5c11-a06d-24ce23469de3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] :
    Surjective (pullback.fst f g) ∧ GeneralizingMap (pullback.fst f g).base ∧
      ∀ η : ↥(pullback f g), (∀ η' : ↥(pullback f g), η' ⤳ η → η' = η) →
        ∀ y : ↥X, y ⤳ (pullback.fst f g).base η → y = (pullback.fst f g).base η := by
  have hs : Surjective (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  have hf : Flat (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  have hg : GeneralizingMap (pullback.fst f g).base := Flat.generalizingMap _
  refine ⟨hs, hg, fun η hη y hy => ?_⟩
  obtain ⟨η', hη', rfl⟩ := hg hy
  rw [hη η' hη']

end S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat (solution)

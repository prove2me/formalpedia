-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_isPullback_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0f9701ca-7af1-559d-bca3-264e4a9dff3d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Y' X' : Scheme.{u}} (ψ : X ⟶ Y) (g : Y' ⟶ Y) [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
    (ψ' : X' ⟶ Y') (π : X' ⟶ X) (h : IsPullback π ψ' ψ g) [Flat ψ'] : Flat ψ := by

  have hcod : RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
    apply RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso
    introv h H
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    rw [RingHom.flat_algebraMap_iff] at H ⊢
    exact Module.Flat.of_flat_tensorProduct R T S
  haveI : MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat hcod
  haveI : MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) h.flip
    ⟨⟨‹Surjective g›, ‹Flat g›⟩, ‹LocallyOfFinitePresentation g›⟩ ‹Flat ψ'›

end S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_isPullback_of_flat_of_surjective (solution)

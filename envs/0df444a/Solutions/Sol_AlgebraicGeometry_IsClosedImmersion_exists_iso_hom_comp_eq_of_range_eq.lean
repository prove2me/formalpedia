-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a4925fc4-e147-5c56-8a22-1e59424b3434

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced A] [IsReduced B] (h : Set.range f.base = Set.range g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by

  haveI : Surjective (pullback.fst f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, ← h, Set.preimage_range]⟩
  haveI : Surjective (pullback.snd f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, h, Set.preimage_range]⟩
  haveI : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.snd f g) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨(asIso (pullback.fst f g)).symm ≪≫ asIso (pullback.snd f g), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
  rw [IsIso.inv_comp_eq, pullback.condition]

end S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq (solution)

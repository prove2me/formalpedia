-- Prove2me | solution 1 for AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0256a6f2-f1e1-50ef-9929-8666420159d4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CLOPENSECT

theorem hasOfPostcompProperty_isOpenImmersion_unramified :
    MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ f hf ↦ by
      obtain ⟨h₁, h₂⟩ := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))

theorem main {S T : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by
  haveI : IsOpenImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact ⟨hasOfPostcompProperty_isOpenImmersion_unramified.of_postcomp s g ⟨‹_›, ‹_›⟩ ‹_›,
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) s g ‹_› ‹_›⟩

end CLOPENSECT

theorem solution
    {S T : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  CLOPENSECT.main g s hs

end S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
end P2MW
export P2MW.S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id (solution)

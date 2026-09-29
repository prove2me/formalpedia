-- Prove2me | solution 1 for AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/07e5e005-ba6b-5c4f-92f2-92cce3044f88

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsClosedImmersion i] [Etale g]
    [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
    IsOpenImmersion i ∧ Etale (i ≫ g) := by

  have hmono : Mono i := inferInstance
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal i) := inferInstance
  have hi : FormallyUnramified i := inferInstance
  have hg : FormallyUnramified g := inferInstance
  have hig : FormallyUnramified (i ≫ g) := MorphismProperty.comp_mem _ i g hi hg
  have het : Etale (i ≫ g) := Etale.of_formallyUnramified_of_flat (f := i ≫ g)
  have heti : Etale i := Etale.of_comp i g
  have hflat : Flat i := (Etale.iff_flat_and_formallyUnramified.mp heti).1
  have hlfp : LocallyOfFinitePresentation i := (Etale.iff_flat_and_formallyUnramified.mp heti).2.2
  exact ⟨IsOpenImmersion.of_flat_of_mono i, het⟩

end S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
end P2MW
export P2MW.S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale (solution)

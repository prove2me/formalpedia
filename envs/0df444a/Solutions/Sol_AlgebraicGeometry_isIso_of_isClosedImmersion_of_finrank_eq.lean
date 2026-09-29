-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/99924049-4092-5ef4-b078-e3719f0d8804

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (fX : X ⟶ Z) (fY : Y ⟶ Z) (i : X ⟶ Y) (hi : i ≫ fY = fX)
    [IsClosedImmersion i]
    [IsFinite fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsFinite fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (hrank : ∀ z : Z, fX.finrank z = fY.finrank z) :
    IsIso i := by
  exact AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i fY fX hi hrank

end S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq (solution)

-- Prove2me | solution 1 for AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3a50621f-217b-5bb5-bd4a-e82e45796d4e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian

set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory

universe u

theorem solution
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation h := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : LocallyOfFiniteType (h ≫ g) := by rw [w]; infer_instance
  haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h g
  infer_instance

end S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
end P2MW
export P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian (solution)

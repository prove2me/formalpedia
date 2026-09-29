-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4a74b902-dc5e-5f10-8e6c-129f39c3a2af

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace REDsol

theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.isReduced_of_smooth_of_field snd

end REDsol

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by
  haveI := REDsol.geometricallyReduced_of_smooth f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian (solution)

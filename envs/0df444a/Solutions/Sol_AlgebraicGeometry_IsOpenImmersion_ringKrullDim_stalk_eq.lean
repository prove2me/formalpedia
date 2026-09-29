-- Prove2me | solution 1 for AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b0a8db6d-7004-56d7-b5c7-a836060c0ac9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (X.presheaf.stalk (i.base u)) :=
  (ringKrullDim_eq_of_ringEquiv (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv).symm

end S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq (solution)

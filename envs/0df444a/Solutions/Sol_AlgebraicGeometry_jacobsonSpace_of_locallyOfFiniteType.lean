-- Prove2me | solution 1 for AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c92dde94-df91-55b3-95dc-9cf0a62f3ccf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] :
    JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace t

end S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType (solution)

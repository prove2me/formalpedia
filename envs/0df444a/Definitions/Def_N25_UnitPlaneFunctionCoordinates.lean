-- Prove2me | Definitions.Def_N25_UnitPlaneFunctionCoordinates
-- name    : N25_UnitPlaneFunctionCoordinates
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:10.979777+00:00
-- url     : https://prove2.me/theorems/48ce8400-3ae7-4337-b675-0853fa07d23a
-- title:
--   Universal unit-plane coordinates in the function field
-- statement:
--   For the unit-plane coordinate ring $A=ℚ[U,V]/(R)$ and its function field $K(A)$, the file defines the two coordinate functions $$U_A∈K(A),\qquad V_A∈K(A)$$ as the images of the universal affine coordinates. They are the distinguished generators used in the birational comparison with the modular function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionField
noncomputable section
namespace N25

/-- The first coordinate as an element of the actual plane function field. -/
def unitPlaneFunctionU25 : UnitPlaneFF25 := algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneU

/-- The second coordinate as an element of the actual plane function field. -/
def unitPlaneFunctionV25 : UnitPlaneFF25 := algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneV

end N25



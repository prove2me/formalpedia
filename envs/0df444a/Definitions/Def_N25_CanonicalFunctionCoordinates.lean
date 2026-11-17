-- Prove2me | Definitions.Def_N25_CanonicalFunctionCoordinates
-- name    : N25_CanonicalFunctionCoordinates
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:36.807844+00:00
-- url     : https://prove2.me/theorems/85d6165f-e1ab-40db-828a-a41479ea0b59
-- title:
--   Plane and homogeneous coordinates in the canonical function field
-- statement:
--   The file transports the two unit-plane generators to canonical rational functions $u,v∈K(C)$ and defines each normalized homogeneous coordinate as an element of the canonical total fraction ring. These named functions connect the birational plane model, the projective coordinates, and the modular units in later order and place computations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionField
import Definitions.Def_N25_UnitPlaneFunctionCoordinates
/-! The two plane generators transported to the canonical function field. -/
noncomputable section
namespace N25

/-- The first plane coordinate as a canonical rational function. -/
def canonicalFunctionU25 : CanonicalFF25 ℚ :=
  canonicalUnitPlaneAlgEquiv25 unitPlaneFunctionU25

/-- The second plane coordinate as a canonical rational function. -/
def canonicalFunctionV25 : CanonicalFF25 ℚ :=
  canonicalUnitPlaneAlgEquiv25 unitPlaneFunctionV25

end N25

namespace N25.Endgame

/-- A normalized homogeneous coordinate in the canonical total fraction ring. -/
def canonicalFFCoordinate25
    (K : Type*) [CommRing K] (i : Fin 4) :
    N25.CanonicalFF25 K :=
  algebraMap (N25.CanonicalOpenChartRing25 K)
    (N25.CanonicalFF25 K)
    (algebraMap (N25.CanonicalAChartRing25 K)
      (N25.CanonicalOpenChartRing25 K)
      (N25.canonicalAChartCoordinate25 K i))

end N25.Endgame



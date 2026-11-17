-- Prove2me | Definitions.Def_N25_canonicalFunctionFieldAlgEquiv25
-- name    : N25_canonicalFunctionFieldAlgEquiv25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:27.691204+00:00
-- url     : https://prove2.me/theorems/747f827e-7af8-4293-9e66-d623e946b8f1
-- title:
--   A coefficient-preserving equivalence of canonical function fields
-- statement:
--   Upgrades the ring equivalence between the scheme function field and the literal fraction field to a $K$-algebra equivalence, characterized by its agreement with the whole principal-open algebra. This is the coefficient-sensitive dictionary used to transport places and finite-field calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial
import Theorems.Thm_N25_canonicalConeToTower25_coordinate
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalConeTowerEquiv
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Mathlib.AlgebraicGeometry.Properties
import Definitions.Def_N25_CanonicalProjectiveGenericPoint
import Theorems.Thm_N25_canonicalFunctionFieldRingEquiv25_on_open
import Theorems.Thm_N25_canonicalOpenToSchemeFFRingHom25_commutes
import Definitions.Def_N25_canonicalFunctionFieldRingEquiv25

noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]
variable [IsIntegral (CanonicalProjectiveCurve25 K)]

/-- The selected scheme field equivalence preserves the structural coefficients. -/
def canonicalFunctionFieldAlgEquiv25 : CanonicalSchemeFF25 K ≃ₐ[K] CanonicalFF25 K where
  __ := canonicalFunctionFieldRingEquiv25 K
  commutes' a := by
    exact (congrArg (canonicalFunctionFieldRingEquiv25 K)
      (canonicalOpenToSchemeFFRingHom25_commutes K a).symm).trans
      ((canonicalFunctionFieldRingEquiv25_on_open K
        (algebraMap K (CanonicalOpenChartRing25 K) a)).trans
        (IsScalarTower.algebraMap_apply K (CanonicalOpenChartRing25 K) (CanonicalFF25 K) a).symm)

end N25
end



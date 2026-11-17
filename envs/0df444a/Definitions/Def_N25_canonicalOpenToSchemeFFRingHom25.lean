-- Prove2me | Definitions.Def_N25_canonicalOpenToSchemeFFRingHom25
-- name    : N25_canonicalOpenToSchemeFFRingHom25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:59.736061+00:00
-- url     : https://prove2.me/theorems/9d151e0c-4106-497d-94b6-f5197a8fb449
-- title:
--   The principal-open germ in the scheme function field
-- statement:
--   Defines the ring homomorphism from the literal principal-open algebra to the scheme function field by identifying elements with sections on $U$ and then taking their germ at the generic point. This is the concrete open-to-function-field map before imposing the coefficient-field law.
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
import Theorems.Thm_N25_canonicalProjPrincipalOpen25_nonempty
import Definitions.Def_N25_canonicalOpenSectionsRingEquiv25

noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]
variable [IsIntegral (CanonicalProjectiveCurve25 K)]

/-- The exact principal-open germ, before adding its structural coefficient law. -/
def canonicalOpenToSchemeFFRingHom25 :
    CanonicalOpenChartRing25 K →+* CanonicalSchemeFF25 K := by
  letI := canonicalProjPrincipalOpen25_nonempty K
  exact ((CanonicalProjectiveCurve25 K).germToFunctionField
    (canonicalProjPrincipalOpen25 K)).hom.comp (canonicalOpenSectionsRingEquiv25 K).toRingHom

end N25
end



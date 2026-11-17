-- Prove2me | Definitions.Def_N25_canonicalFunctionFieldAlgEquivGood25
-- name    : N25_canonicalFunctionFieldAlgEquivGood25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:54.966779+00:00
-- url     : https://prove2.me/theorems/7d0a590f-0f5d-4719-87fc-d79257921ad2
-- title:
--   The canonical function-field equivalence at the good primes
-- statement:
--   For characteristic $2$ or $3$, defines the $K$-algebra equivalence between the scheme-theoretic canonical function field and its explicit fraction-field model, induced by the entire prescribed principal open. This is the good-prime identification through which place counts and reduction data are transferred.
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
import Theorems.Thm_N25_canonicalProjectiveCurve25_isIntegral_good
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
import Definitions.Def_N25_canonicalFunctionFieldAlgEquiv25

noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory

/-- The exact signed good-prime field equivalence is induced by the whole literal open. -/
def canonicalFunctionFieldAlgEquivGood25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type u) [Field K] [CharP K p] :
    letI : IsIntegral (CanonicalProjectiveCurve25 K) := canonicalProjectiveCurve25_isIntegral_good p hp K
    CanonicalSchemeFF25 K ≃ₐ[K] CanonicalFF25 K := by
  letI := canonicalProjectiveCurve25_isIntegral_good p hp K
  exact canonicalFunctionFieldAlgEquiv25 K

end N25
end



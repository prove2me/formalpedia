-- Prove2me | Definitions.Def_N25_canonicalFunctionFieldRingEquiv25
-- name    : N25_canonicalFunctionFieldRingEquiv25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:58.309929+00:00
-- url     : https://prove2.me/theorems/d8c51510-a757-48c5-add4-f8abe960702b
-- title:
--   The scheme function field as a literal fraction field
-- statement:
--   Defines a ring equivalence between the scheme-theoretic function field of the canonical projective curve and the fraction field of its explicit principal-open coordinate ring. The equivalence is selected by fraction-field uniqueness and the actual nonempty affine open, thereby identifying the abstract scheme field with the computational model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain
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

/-- Fraction-field uniqueness, using the actual nonempty principal-open germ. -/
def canonicalFunctionFieldRingEquiv25 : CanonicalSchemeFF25 K ≃+* CanonicalFF25 K := by
  letI := canonicalProjPrincipalOpen25_nonempty K
  letI := canonicalOpenChartRing25C_isDomain (K := K)
  letI : IsFractionRing
      Γ(CanonicalProjectiveCurve25 K, canonicalProjPrincipalOpen25 K) (CanonicalSchemeFF25 K) :=
    functionField_isFractionRing_of_isAffineOpen (CanonicalProjectiveCurve25 K)
      (canonicalProjPrincipalOpen25 K)
      (Proj.isAffineOpen_basicOpen (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
        (canonicalConePrincipalElement25_mem K) (by decide : 0 < (5 : ℕ)))
  exact IsFractionRing.ringEquivOfRingEquiv (K := CanonicalSchemeFF25 K) (L := CanonicalFF25 K)
    (canonicalOpenSectionsRingEquiv25 K).symm

end N25
end



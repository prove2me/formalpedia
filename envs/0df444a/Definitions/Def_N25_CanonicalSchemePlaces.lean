-- Prove2me | Definitions.Def_N25_CanonicalSchemePlaces
-- name    : N25_CanonicalSchemePlaces
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:08:01.712632+00:00
-- url     : https://prove2.me/theorems/9c1e338c-198a-4ad3-899f-9b1034e581ee
-- title:
--   Scheme sections as degree-one places of the canonical function field
-- statement:
--   Let $p∈\{2,3\}$ and let $K$ be a perfect field of characteristic $p$. The file defines an equivalence between sections of the proper smooth canonical curve $X_K→\operatorname{Spec}K$ and degree-one places of the prescribed canonical function field, using the generic-stalk function field and the proved field equivalence. This supplies the scheme-theoretic point/place correspondence used to convert finite point counts into place counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalSchemePoints
import Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
import Definitions.Def_AlgebraicCurve_SchemePointPlaces
import Definitions.Def_N25_canonicalFunctionFieldAlgEquivGood25
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25
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
import Theorems.Thm_N25_canonicalProjectiveCurveToSpec25_smoothDimensionOne_good
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_canonicalProjectiveCurveToSpec25_isProper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
/-! Full scheme-point/place correspondence for the literal canonical model at the good primes. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace N25.Endgame
open N25 AlgebraicGeometry

/-- Every scheme section of the full proper canonical curve corresponds to
one degree-one place of the prescribed canonical function field. -/
def canonicalSchemePointPlaceEquivGood25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type u) [Field K] [PerfectField K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    CanonicalSchemePoint25 K ≃
      {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} := by
  letI : IsDomain (CanonicalOpenChartRing25 K) :=
    canonicalOpenChartRing_isDomain_good25 p hp K
  letI : IsIntegral (CanonicalProjectiveCurve25 K) :=
    canonicalProjectiveCurve25_isIntegral_good p hp K
  letI : IsProper (canonicalProjectiveCurveToSpec25 K) :=
    canonicalProjectiveCurveToSpec25_isProper K
  letI : SmoothOfRelativeDimension 1 (canonicalProjectiveCurveToSpec25 K) :=
    canonicalProjectiveCurveToSpec25_smoothDimensionOne_good p hp K
  let E : CanonicalSchemePoint25 K ≃
      {P : AlgebraicCurve.Place K (CanonicalSchemeFF25 K) // P.deg = 1} :=
    AlgebraicCurve.schemeSectionPlaceEquiv (canonicalProjectiveCurveToSpec25 K)
  exact E.trans (AlgebraicCurve.Place.degreeOneAlgEquiv
    (canonicalFunctionFieldAlgEquivGood25 p hp K))

end N25.Endgame



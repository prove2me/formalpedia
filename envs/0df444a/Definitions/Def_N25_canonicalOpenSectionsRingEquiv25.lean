-- Prove2me | Definitions.Def_N25_canonicalOpenSectionsRingEquiv25
-- name    : N25_canonicalOpenSectionsRingEquiv25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:18.884971+00:00
-- url     : https://prove2.me/theorems/5efa6894-4d87-4fe9-ad5a-0e6023d68bab
-- title:
--   Sections on the selected canonical affine open
-- statement:
--   Defines a ring equivalence between the literal coordinate algebra of the selected canonical principal open and the ring of regular sections $Γ(C,U)$ on the corresponding affine open of the projective curve. It is the first bridge from the explicit quotient-and-localization model to the scheme-theoretic function field.
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

noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]

/-- The selected literal open algebra is exactly the ring of sections on that affine scheme open. -/
def canonicalOpenSectionsRingEquiv25 :
    CanonicalOpenChartRing25 K ≃+*
      Γ(CanonicalProjectiveCurve25 K, canonicalProjPrincipalOpen25 K) :=
  (canonicalPrincipalOpenAlgEquiv25 K).toRingEquiv.trans
    (Proj.basicOpenIsoAway (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
      (canonicalConePrincipalElement25_mem K) (by decide : 0 < (5 : ℕ))).commRingCatIsoToRingEquiv

end N25
end



-- Prove2me | Definitions.Def_N25_CanonicalProjectiveCharts
-- name    : N25_CanonicalProjectiveCharts
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:44.406141+00:00
-- url     : https://prove2.me/theorems/99e796f0-ea97-41d4-a509-d5f13667e179
-- title:
--   The four standard affine charts of the canonical projective curve
-- statement:
--   Let $A$ be the graded homogeneous coordinate ring of the canonical curve and let $x_0,x_1,x_2,x_3∈A_1$ be its coordinate classes. For each $i∈\{0,1,2,3\}$, the file defines the degree-zero localization $A_{(x_i)}$, its coordinate ratios $x_j/x_i$, and the corresponding basic open $D_+(x_i)⊂\operatorname{Proj}(A)$. These objects provide the four literal affine charts used for smoothness, point normalization, and gluing.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCone
import Definitions.Def_N25_CanonicalAffineCharts
/-! The four degree-zero localizations and their literal coordinate ratios. -/
noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]

abbrev CanonicalProjChartRing25 (i : Fin 4) :=
  HomogeneousLocalization.Away (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)

noncomputable instance canonicalProjChartRing25_algebra (i : Fin 4) :
    Algebra K (CanonicalProjChartRing25 K i) :=
  ((HomogeneousLocalization.fromZeroRingHom (canonicalConePiece25 K)
    (Submonoid.powers (canonicalConeCoordinate25 K i))).comp
      (algebraMap K (canonicalConePiece25 K 0))).toAlgebra

def canonicalProjChartCoordinate25 (i j : Fin 4) : CanonicalProjChartRing25 K i :=
  HomogeneousLocalization.Away.mk (canonicalConePiece25 K)
    (canonicalConeCoordinate25_mem K i) 1 (canonicalConeCoordinate25 K j)
    (by simpa using canonicalConeCoordinate25_mem K j)

def canonicalProjChartOpen25 (i : Fin 4) : (CanonicalProjectiveCurve25 K).Opens :=
  Proj.basicOpen (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)

end N25



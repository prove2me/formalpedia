-- Prove2me | Definitions.Def_N25_CanonicalProjectivePrincipalOpen
-- name    : N25_CanonicalProjectivePrincipalOpen
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:23.003429+00:00
-- url     : https://prove2.me/theorems/c7706757-07f5-4f25-8c67-1527dbb1c280
-- title:
--   The common principal open for the canonical–plane birational map
-- statement:
--   Writing $x,y,z,w$ for the canonical cone coordinates, the file defines $A=y+z-w$, $B=xz+zA+xA$, and the homogeneous degree-five element $$f=A\,x\,z\,B.$$ It also defines the degree-five numerators $x_jxzB$, their degree-zero fractions, the localization $A_{(f)}$, and the basic open $D_+(f)$. This is the common principal open on which the canonical and unit-plane birational formulas are regular.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalOpenChart
/-! The degree-five homogeneous element selecting the canonical principal open. -/
noncomputable section
universe u
namespace N25
open AlgebraicGeometry
variable (K : Type u) [Field K]

def canonicalConeA25 : CanonicalConeRing25 K :=
  canonicalConeCoordinate25 K 1 + canonicalConeCoordinate25 K 2 - canonicalConeCoordinate25 K 3

def canonicalConeB25 : CanonicalConeRing25 K :=
  canonicalConeCoordinate25 K 0 * canonicalConeCoordinate25 K 2 +
    canonicalConeCoordinate25 K 2 * canonicalConeA25 K +
    canonicalConeCoordinate25 K 0 * canonicalConeA25 K

def canonicalConePrincipalElement25 : CanonicalConeRing25 K :=
  canonicalConeA25 K * canonicalConeCoordinate25 K 0 *
    canonicalConeCoordinate25 K 2 * canonicalConeB25 K

def canonicalConePrincipalNumerator25 (j : Fin 4) : CanonicalConeRing25 K :=
  canonicalConeCoordinate25 K j * canonicalConeCoordinate25 K 0 *
    canonicalConeCoordinate25 K 2 * canonicalConeB25 K

theorem canonicalConeA25_mem : canonicalConeA25 K ∈ canonicalConePiece25 K 1 :=
  (canonicalConePiece25 K 1).sub_mem ((canonicalConePiece25 K 1).add_mem
    (canonicalConeCoordinate25_mem K 1) (canonicalConeCoordinate25_mem K 2))
    (canonicalConeCoordinate25_mem K 3)

theorem canonicalConeB25_mem : canonicalConeB25 K ∈ canonicalConePiece25 K 2 :=
  (canonicalConePiece25 K 2).add_mem ((canonicalConePiece25 K 2).add_mem
    (SetLike.mul_mem_graded (canonicalConeCoordinate25_mem K 0) (canonicalConeCoordinate25_mem K 2))
    (SetLike.mul_mem_graded (canonicalConeCoordinate25_mem K 2) (canonicalConeA25_mem K)))
    (SetLike.mul_mem_graded (canonicalConeCoordinate25_mem K 0) (canonicalConeA25_mem K))

theorem canonicalConePrincipalElement25_mem :
    canonicalConePrincipalElement25 K ∈ canonicalConePiece25 K 5 :=
  SetLike.mul_mem_graded (SetLike.mul_mem_graded (SetLike.mul_mem_graded
    (canonicalConeA25_mem K) (canonicalConeCoordinate25_mem K 0))
    (canonicalConeCoordinate25_mem K 2)) (canonicalConeB25_mem K)

theorem canonicalConePrincipalNumerator25_mem (j : Fin 4) :
    canonicalConePrincipalNumerator25 K j ∈ canonicalConePiece25 K 5 :=
  SetLike.mul_mem_graded (SetLike.mul_mem_graded (SetLike.mul_mem_graded
    (canonicalConeCoordinate25_mem K j) (canonicalConeCoordinate25_mem K 0))
    (canonicalConeCoordinate25_mem K 2)) (canonicalConeB25_mem K)

abbrev CanonicalProjPrincipalRing25 :=
  HomogeneousLocalization.Away (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)

noncomputable instance canonicalProjPrincipalRing25_algebra : Algebra K (CanonicalProjPrincipalRing25 K) :=
  ((HomogeneousLocalization.fromZeroRingHom (canonicalConePiece25 K)
    (Submonoid.powers (canonicalConePrincipalElement25 K))).comp
      (algebraMap K (canonicalConePiece25 K 0))).toAlgebra

def canonicalProjPrincipalCoordinate25 (j : Fin 4) : CanonicalProjPrincipalRing25 K :=
  HomogeneousLocalization.Away.mk (canonicalConePiece25 K) (canonicalConePrincipalElement25_mem K)
    1 (canonicalConePrincipalNumerator25 K j) (by simpa using canonicalConePrincipalNumerator25_mem K j)

def canonicalProjPrincipalOpen25 : (CanonicalProjectiveCurve25 K).Opens :=
  Proj.basicOpen (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)

end N25



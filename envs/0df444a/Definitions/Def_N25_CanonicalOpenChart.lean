-- Prove2me | Definitions.Def_N25_CanonicalOpenChart
-- name    : N25_CanonicalOpenChart
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:01.338329+00:00
-- url     : https://prove2.me/theorems/bd160499-2612-435c-9f44-27c2bc0c223a
-- title:
--   The principal birational open of the canonical affine chart
-- statement:
--   Let $A=y+z-w$. The file defines the affine chart cut out by $(Q,C,A-1)$, its four coordinate functions, and the open element $$x z B,   B=xz+zA+xA.$$ It then defines the localization in which this element is invertible and installs its coefficient-algebra structure. This is the literal canonical principal open on which both directions of the birational map are regular.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! The principal open of the canonical curve where A = y+z-w is normalized to one
and x, z and B = xz+zA+xA are invertible. -/
noncomputable section
namespace N25
open MvPolynomial

/-- The homogeneous coordinates with the affine equation A=1. -/
abbrev CanonicalAChartPolynomial25 (k : Type*) [CommRing k] := MvPolynomial (Fin 4) k

/-- The literal complete-intersection ideal together with the affine-chart equation. -/
def canonicalAChartIdeal25 (k : Type*) [CommRing k] : Ideal (CanonicalAChartPolynomial25 k) :=
  Ideal.span {canonicalQuadric (X 0) (X 1) (X 2) (X 3),
    canonicalCubic (X 0) (X 1) (X 2) (X 3),
    canonicalDenominator (X 1) (X 2) (X 3) - 1}

/-- The affine chart A=1, before localization. -/
abbrev CanonicalAChartRing25 (k : Type*) [CommRing k] :=
  CanonicalAChartPolynomial25 k ⧸ canonicalAChartIdeal25 k

/-- The coordinate functions on the affine chart. -/
def canonicalAChartCoordinate25 (k : Type*) [CommRing k] (i : Fin 4) : CanonicalAChartRing25 k :=
  Ideal.Quotient.mk _ (X i)

/-- The principal open on which the integral reverse composition is nonzero. -/
def canonicalAChartOpenElement25 (k : Type*) [CommRing k] : CanonicalAChartRing25 k :=
  canonicalAChartCoordinate25 k 0 * canonicalAChartCoordinate25 k 2 *
    canonicalMultiplier (canonicalAChartCoordinate25 k 0) (canonicalAChartCoordinate25 k 1)
      (canonicalAChartCoordinate25 k 2) (canonicalAChartCoordinate25 k 3)

/-- A genuine localization of the literal canonical affine-coordinate ring. -/
abbrev CanonicalOpenChartRing25 (k : Type*) [CommRing k] :=
  Localization.Away (canonicalAChartOpenElement25 k)

/-- The semiring structure of the literal canonical principal open. -/
instance canonicalOpenChartSemiring25 (k : Type*) [CommRing k] :
    Semiring (CanonicalOpenChartRing25 k) := inferInstance

/-- The commutative semiring structure of the canonical principal open. -/
instance canonicalOpenChartCommSemiring25 (k : Type*) [CommRing k] :
    CommSemiring (CanonicalOpenChartRing25 k) := inferInstance

/-- Named ring structure on the literal canonical principal open. -/
instance canonicalOpenChartCommRing25 (k : Type*) [CommRing k] :
    CommRing (CanonicalOpenChartRing25 k) := inferInstance

/-- The principal open retains its coefficient algebra structure. -/
instance canonicalOpenChartAlgebra25 (k : Type*) [CommRing k] :
    Algebra k (CanonicalOpenChartRing25 k) := inferInstance

end N25



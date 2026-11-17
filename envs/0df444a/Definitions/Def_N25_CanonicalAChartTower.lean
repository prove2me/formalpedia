-- Prove2me | Definitions.Def_N25_CanonicalAChartTower
-- name    : N25_CanonicalAChartTower
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:02.120676+00:00
-- url     : https://prove2.me/theorems/0f3d7d2a-c970-46b0-9f7f-526bf594a3dd
-- title:
--   A monic quadratic tower for the normalized canonical chart
-- statement:
--   Over a field $K$, the file uses base variables $x,z$, the multiplier $m=xz+x+z$, and adjoins a root $y$ of $$q(y)=y^2+(2z-x)y+z^2-2xz+x-z.$$ It then quotients by the linear remainder $$m y+z(z-1-x^2).$$ This tower presentation replaces the four-variable chart by a monic quadratic extension followed by one relation, enabling regularity and domain arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! A monic quadratic presentation of the canonical A=1 chart. -/
noncomputable section
namespace N25
open Polynomial
variable (K : Type*) [Field K]

abbrev CanonicalAChartBase25 := Polynomial (Polynomial K)
def canonicalAChartBaseX25 : CanonicalAChartBase25 K := X
def canonicalAChartBaseZ25 : CanonicalAChartBase25 K := C X

def canonicalAChartBaseMultiplier25 : CanonicalAChartBase25 K :=
  canonicalAChartBaseX25 K * canonicalAChartBaseZ25 K +
    canonicalAChartBaseX25 K + canonicalAChartBaseZ25 K

def canonicalAChartQuadratic25 : Polynomial (CanonicalAChartBase25 K) :=
  let x := canonicalAChartBaseX25 K
  let z := canonicalAChartBaseZ25 K
  X^2+C (2*z-x)*X+C (z^2-2*x*z+x-z)

abbrev CanonicalAChartQuadricRoot25 := AdjoinRoot (canonicalAChartQuadratic25 K)

def canonicalAChartLinearRemainder25 : Polynomial (CanonicalAChartBase25 K) :=
  let x := canonicalAChartBaseX25 K
  let z := canonicalAChartBaseZ25 K
  C (canonicalAChartBaseMultiplier25 K)*X+C (z*(z-1-x^2))

abbrev CanonicalAChartTowerRing25 := CanonicalAChartQuadricRoot25 K ⧸
  Ideal.span ({AdjoinRoot.mk (canonicalAChartQuadratic25 K)
    (canonicalAChartLinearRemainder25 K)} : Set (CanonicalAChartQuadricRoot25 K))

end N25



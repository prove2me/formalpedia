-- Prove2me | Definitions.Def_N25_UnitPlaneDerivative
-- name    : N25_UnitPlaneDerivative
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:29.653468+00:00
-- url     : https://prove2.me/theorems/05490511-60bb-411f-81c5-dea08c3a13a5
-- title:
--   Derivative and Bézout data for the plane projection
-- statement:
--   Defines $∂F/∂v$, the cubic branch factor $u^3+u^2+2u+1$, and explicit Bézout coefficients relating the plane equation to its $v$-derivative. These formulas locate the branch locus and control regularity of the projection to the $u$-line.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
import Definitions.Def_N25_PlaneBranchPolynomial
/-! The derivative and integral Euclidean certificate for the plane quartic. -/
namespace N25
variable {k : Type*} [CommRing k]

/-- Partial derivative of the plane relation with respect to its second coordinate. -/
def planeDerivativeV (u v : k) : k :=
  4*v^3-3*u^3*v^2+2*(u-u^3-2*u^4)*v-(u^3+u^4+2*u^5)

/-- The cubic factor in the branch locus of the plane projection. -/
def planeCubicBranchValue (u : k) : k := u^3+u^2+2*u+1

/-- First Euclidean coefficient for the relation and its derivative. -/
def planeDerivativeBezoutLeft (u v : k) : k :=
  (u*(27*u^15 + 28*u^14 + 300*u^13 + 449*u^12 + 1193*u^11 + 1380*u^10 + 1631*u^9 + 1083*u^8 + 188*u^7 - 320*u^6 - 568*u^5 - 220*u^4 + 32*u^3 + 64*u^2 - 16)) +
  (2*u^2*(6*u^12 - 3*u^11 + 70*u^10 - 4*u^9 + 214*u^8 + 44*u^7 + 241*u^6 + 44*u^5 + 44*u^4 + 12*u^3 + 4*u - 8))*v +
  (-8*(2*u^11 + 5*u^10 + 26*u^9 + 44*u^8 + 108*u^7 + 102*u^6 + 107*u^5 + 34*u^4 - 6*u^3 - 12*u^2 + 4))*v^2

/-- Second Euclidean coefficient for the relation and its derivative. -/
def planeDerivativeBezoutRight (u v : k) : k :=
  (-u^3*(6*u^14 + 11*u^13 + 66*u^12 + 158*u^11 + 310*u^10 + 495*u^9 + 556*u^8 + 554*u^7 + 358*u^6 + 170*u^5 + 27*u^4 - 9*u^3 - 4*u^2 + 4*u + 4)) +
  (-u*(9*u^15 + 12*u^14 + 104*u^13 + 183*u^12 + 443*u^11 + 610*u^10 + 701*u^9 + 535*u^8 + 108*u^7 - 160*u^6 - 278*u^5 - 100*u^4 + 22*u^3 + 32*u^2 - 8))*v +
  (-u^2*(4*u^12 + u^11 + 48*u^10 + 20*u^9 + 161*u^8 + 73*u^7 + 174*u^6 + 39*u^5 + 19*u^4 + 4*u - 4))*v^2 +
  (2*(2*u^11 + 5*u^10 + 26*u^9 + 44*u^8 + 108*u^7 + 102*u^6 + 107*u^5 + 34*u^4 - 6*u^3 - 12*u^2 + 4))*v^3

end N25



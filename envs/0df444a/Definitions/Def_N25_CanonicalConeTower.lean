-- Prove2me | Definitions.Def_N25_CanonicalConeTower
-- name    : N25_CanonicalConeTower
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:05.14212+00:00
-- url     : https://prove2.me/theorems/e087f3b5-8616-465c-815f-cdefb3c20988
-- title:
--   A monic quadratic tower presentation of the canonical cone
-- statement:
--   Using coefficient variables $A,x,z$, the file adjoins $y$ through $$q(y)=y^2+(2z-x)y+z^2-2xz+A(x-z)$$ and then imposes the linear cubic remainder $$(Ax+Az+xz)y+Az^2-A^2z-x^2z.$$ The resulting quotient is an explicit tower model of the homogeneous canonical cone. It is used to prove regularity of a boundary element and hence integrality of the cone and projective curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! A monic quadratic presentation of the canonical cone, with A as a coefficient variable. -/
noncomputable section
namespace N25
open Polynomial
variable (K : Type*) [Field K]

abbrev CanonicalConeBase25 := Polynomial (Polynomial (Polynomial K))

@[reducible] instance canonicalConeBaseSemiring25 : Semiring (CanonicalConeBase25 K) :=
  (inferInstance : CommRing (CanonicalConeBase25 K)).toSemiring
def canonicalConeBaseA25 : CanonicalConeBase25 K := X
def canonicalConeBaseX25 : CanonicalConeBase25 K := C X
def canonicalConeBaseZ25 : CanonicalConeBase25 K := C (C X)

def canonicalConeQuadricPolynomial25 : Polynomial (CanonicalConeBase25 K) :=
  let a := canonicalConeBaseA25 K
  let x := canonicalConeBaseX25 K
  let z := canonicalConeBaseZ25 K
  X^2+C (2*z-x)*X+C (z^2-2*x*z+a*(x-z))

def canonicalConeCubicRemainder25 : Polynomial (CanonicalConeBase25 K) :=
  let a := canonicalConeBaseA25 K
  let x := canonicalConeBaseX25 K
  let z := canonicalConeBaseZ25 K
  C (a*x+a*z+x*z)*X+C (a*z^2-a^2*z-x^2*z)

abbrev CanonicalConeQuadricRoot25 := AdjoinRoot (canonicalConeQuadricPolynomial25 K)

abbrev CanonicalConeTowerRing25 := CanonicalConeQuadricRoot25 K ⧸
  Ideal.span ({AdjoinRoot.mk (canonicalConeQuadricPolynomial25 K)
    (canonicalConeCubicRemainder25 K)} : Set (CanonicalConeQuadricRoot25 K))

end N25



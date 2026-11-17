-- Prove2me | Definitions.Def_N25_CanonicalUnitPlane
-- name    : N25_CanonicalUnitPlane
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:13.43931+00:00
-- url     : https://prove2.me/theorems/b6399267-f1f0-4863-8538-7b2747332fa1
-- title:
--   Integral birational formulas for the canonical and unit-plane models
-- statement:
--   Over a commutative ring, the file defines the plane equation $$R(u,v)=v^4-u^3v^3+(u-u^3-2u^4)v^2-(u^3+u^4+2u^5)v+u^7,$$ the canonical quadric $Q=-xz-xw+y^2+yz+zw$, and the canonical cubic $C=x^2w+xyz-xyw-xzw+yzw+z^2w-zw^2$. It also defines the forward coordinates from $(u,v)$, the denominators and multiplier, and the four cleared reverse numerators. These polynomial data are the denominator-free core of the birational equivalence between the plane and canonical models.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-! Polynomial models and integral birational formulas for the order-25 canonical curve. -/
namespace N25

variable {k : Type*} [CommRing k]

/-- The relation of the two plane coordinates. -/
def planeRelation (u v : k) : k :=
  v ^ 4 - u ^ 3 * v ^ 3 + (u - u ^ 3 - 2 * u ^ 4) * v ^ 2 -
    (u ^ 3 + u ^ 4 + 2 * u ^ 5) * v + u ^ 7

/-- The quadric equation of the canonical model. -/
def canonicalQuadric (x y z w : k) : k := -x*z-x*w+y^2+y*z+z*w

/-- The cubic equation of the canonical model. -/
def canonicalCubic (x y z w : k) : k :=
  x^2*w+x*y*z-x*y*w-x*z*w+y*z*w+z^2*w-z*w^2

def planeDenominator (u v : k) : k := u^2+u+v
def planeX (u v : k) : k := u*v*planeDenominator u v
def planeY (u v : k) : k := u*(u^2*v-u^2+v)
def planeZ (u v : k) : k := u^2*planeDenominator u v
def planeW (u v : k) : k := u^4+u^3*v-v^2

def canonicalDenominator (y z w : k) : k := y+z-w
def canonicalMultiplier (x y z w : k) : k :=
  x*z+z*canonicalDenominator y z w+x*canonicalDenominator y z w

def reverseX (x y z w : k) : k := x*canonicalMultiplier x y z w
def reverseY (x y z w : k) : k :=
  z*(x^2-z*canonicalDenominator y z w+(canonicalDenominator y z w)^2)
def reverseZ (x y z w : k) : k := z*canonicalMultiplier x y z w
def reverseW (x y z w : k) : k :=
  x*(z^2+x*z-(canonicalDenominator y z w)^2)

end N25



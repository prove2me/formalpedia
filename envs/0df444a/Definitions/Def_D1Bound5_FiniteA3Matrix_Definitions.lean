-- Prove2me | Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
-- name    : D1Bound5_FiniteA3Matrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:29.738334+00:00
-- url     : https://prove2.me/theorems/01fad6ba-181c-46dd-ad4f-b68fb1543cff
-- title:
--   Finite A3Matrix
-- statement:
--   Definitions for finite a3matrix in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA3Constant`, `finiteA3Left`, `finiteA3Right`, `finiteA3DividedMatrix`, `finiteA3Matrix`, `finiteA3RowFactor`.
-- source:
--   D1Bound5/FiniteA3Matrix.lean, lines 9-10, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23; D1Bound5/FiniteA3Matrix.lean, lines 12-13, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23; D1Bound5/FiniteA3Matrix.lean, lines 15-16, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23; D1Bound5/FiniteA3Matrix.lean, lines 18-19, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23; D1Bound5/FiniteA3Matrix.lean, lines 21-22, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23; D1Bound5/FiniteA3Matrix.lean, lines 24-24, SHA-256 e2e655ee4e57d8710dc3aa3f891fc956ce3421ebfedb3c1976c3b656531c2d23. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

section
namespace D1Bound5
variable {R : Type*} [CommRing R]

def finiteA3Constant (x y c : R) : Fin 3 → R :=
  ![(x-y)^5*c^1*(96*x^2*c^2 + 144*x*y*c^2 + 168*x*c + 96*y^2*c^2 + 168*y*c + 70),(x-y)^6*c^2*(-64*x*c - 48*y*c - 56),(x-y)^6*c^2*(-48*x*c - 64*y*c - 56)]

def finiteA3Left (x y c : R) : Fin 3 → R :=
  ![-96*x^6*c^3 + 336*x^5*y*c^3 - 120*x^5*c^2 - 336*x^4*y^2*c^3 + 504*x^4*y*c^2 - 22*x^4*c - 672*x^3*y^2*c^2 + 140*x^3*y*c + 2*x^3 - 406*x^2*y^2*c - 28*x^2*y - 70*x*y^2,64*x^6*c^3 - 336*x^5*y*c^3 + 24*x^5*c^2 + 672*x^4*y^2*c^3 - 168*x^4*y*c^2 - 4*x^4*c - 560*x^3*y^3*c^3 + 504*x^3*y^2*c^2 + 42*x^3*y*c + x^3 - 840*x^2*y^3*c^2 - 168*x^2*y^2*c - 21*x^2*y - 350*x*y^3*c - 105*x*y^2 - 35*y^3,48*x^6*c^3 - 224*x^5*y*c^3 + 32*x^5*c^2 + 336*x^4*y^2*c^3 - 224*x^4*y*c^2 - 10*x^4*c + 672*x^3*y^2*c^2 + 84*x^3*y*c + 6*x^3 + 406*x^2*y^2*c + 84*x^2*y + 70*x*y^2]

def finiteA3Right (x y c : R) : Fin 3 → R :=
  ![336*x^2*y^4*c^3 + 672*x^2*y^3*c^2 + 406*x^2*y^2*c + 70*x^2*y - 336*x*y^5*c^3 - 504*x*y^4*c^2 - 140*x*y^3*c + 28*x*y^2 + 96*y^6*c^3 + 120*y^5*c^2 + 22*y^4*c - 2*y^3,336*x^2*y^4*c^3 + 672*x^2*y^3*c^2 + 406*x^2*y^2*c + 70*x^2*y - 224*x*y^5*c^3 - 224*x*y^4*c^2 + 84*x*y^3*c + 84*x*y^2 + 48*y^6*c^3 + 32*y^5*c^2 - 10*y^4*c + 6*y^3,-560*x^3*y^3*c^3 - 840*x^3*y^2*c^2 - 350*x^3*y*c - 35*x^3 + 672*x^2*y^4*c^3 + 504*x^2*y^3*c^2 - 168*x^2*y^2*c - 105*x^2*y - 336*x*y^5*c^3 - 168*x*y^4*c^2 + 42*x*y^3*c - 21*x*y^2 + 64*y^6*c^3 + 24*y^5*c^2 - 4*y^4*c + y^3]

def finiteA3DividedMatrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => ![finiteA3Constant x y c i,finiteA3Left x y c i,finiteA3Right x y c i] j

def finiteA3Matrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  finiteA3DividedMatrix x y c * Matrix.diagonal ![1,x,y]

def finiteA3RowFactor (x y : R) : Fin 3 → R := ![x-y,x,y]











end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
-- name    : D1Bound5_FiniteN2Matrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:27:20.516958+00:00
-- url     : https://prove2.me/theorems/606ac619-f63d-4fab-b3be-cb96186768c2
-- title:
--   Finite N2Matrix
-- statement:
--   The three constant columns in the manuscript's N2 family, after the row divisions and the common factor2 have been removed. The named objects in this bundle include `finiteN2Constant`, `finiteN2Left`, `finiteN2Right`, `finiteN2DividedMatrix`, `finiteN2Matrix`, `finiteN2RowFactor`.
-- source:
--   D1Bound5/FiniteN2Matrix.lean, lines 12-17, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa; D1Bound5/FiniteN2Matrix.lean, lines 19-24, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa; D1Bound5/FiniteN2Matrix.lean, lines 26-31, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa; D1Bound5/FiniteN2Matrix.lean, lines 33-37, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa; D1Bound5/FiniteN2Matrix.lean, lines 39-41, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa; D1Bound5/FiniteN2Matrix.lean, lines 43-43, SHA-256 1f3f076e9bd3b39bd1afb85c25ff777354cf04b5db2ff603d1bf7550fbf8c4aa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {R : Type*} [CommRing R]

/-- The three constant columns in the manuscript's N2 family, after the
row divisions and the common factor2 have been removed. -/
def finiteN2Constant (x y c : R) : Fin 3 → R :=
  ![(x-y)^3*(15+40*(x+y)*c+8*(3*x^2+4*x*y+3*y^2)*c^2),
    -4*c*(x-y)^4*(5+(6*x+4*y)*c),
    -4*c*(x-y)^4*(5+(4*x+6*y)*c)]

/-- Divided x-column; every displayed coefficient is an integer. -/
def finiteN2Left (x y c : R) : Fin 3 → R :=
  ![-4*x^2+20*x*y+(-28*x^3+60*x^2*y)*c+(-24*x^4+40*x^3*y)*c^2,
    -x^2+10*x*y+15*y^2+(8*x^3-40*x^2*y+80*x*y^2)*c+
      (24*x^4-80*x^3*y+80*x^2*y^2)*c^2,
    -4*x^2-20*x*y+(12*x^3-60*x^2*y)*c+(16*x^4-40*x^3*y)*c^2]

/-- Divided y-column in the same row order. -/
def finiteN2Right (x y c : R) : Fin 3 → R :=
  ![-20*x*y+4*y^2+(-60*x*y^2+28*y^3)*c+(-40*x*y^3+24*y^4)*c^2,
    -20*x*y-4*y^2+(-60*x*y^2+12*y^3)*c+(-40*x*y^3+16*y^4)*c^2,
    15*x^2+10*x*y-y^2+(80*x^2*y-40*x*y^2+8*y^3)*c+
      (80*x^2*y^2-80*x*y^3+24*y^4)*c^2]

/-- The polynomial matrix with its exact anchor factors removed. This is
the matrix acting on the integral vector of signed root products. -/
def finiteN2DividedMatrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of (fun i j => ![finiteN2Constant x y c i,
    finiteN2Left x y c i, finiteN2Right x y c i] j)

/-- The original root coefficient matrix, with its exact anchor factors. -/
def finiteN2Matrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  finiteN2DividedMatrix x y c * Matrix.diagonal ![1,x,y]

def finiteN2RowFactor (x y : R) : Fin 3 → R := ![x-y,x,y]













end D1Bound5
end



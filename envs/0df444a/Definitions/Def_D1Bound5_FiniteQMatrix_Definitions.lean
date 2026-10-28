-- Prove2me | Definitions.Def_D1Bound5_FiniteQMatrix_Definitions
-- name    : D1Bound5_FiniteQMatrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:41.697577+00:00
-- url     : https://prove2.me/theorems/5515958d-67d2-41ca-8d57-e02d5f394f74
-- title:
--   Finite QMatrix
-- statement:
--   Left divided coefficient in the manuscript's finite Q pair row. The named objects in this bundle include `finiteQLeft`, `finiteQRight`, `finiteQConstant`, `finiteQDividedMatrix`.
-- source:
--   D1Bound5/FiniteQMatrix.lean, lines 64-66, SHA-256 3ee6c257a35cbef87e7863b9221f558f30f7e22b373aafe1a2ee836183738093; D1Bound5/FiniteQMatrix.lean, lines 68-70, SHA-256 3ee6c257a35cbef87e7863b9221f558f30f7e22b373aafe1a2ee836183738093; D1Bound5/FiniteQMatrix.lean, lines 72-74, SHA-256 3ee6c257a35cbef87e7863b9221f558f30f7e22b373aafe1a2ee836183738093; D1Bound5/FiniteQMatrix.lean, lines 76-83, SHA-256 3ee6c257a35cbef87e7863b9221f558f30f7e22b373aafe1a2ee836183738093. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {R : Type*} [CommRing R]



/-- Left divided coefficient in the manuscript's finite Q pair row. -/
def finiteQLeft (u v c : R) : R :=
  u^2-5*u*v+(4*u^3-8*u^2*v)*c

/-- Right divided coefficient in the manuscript's finite Q pair row. -/
def finiteQRight (u v c : R) : R :=
  5*u*v-v^2+(8*u*v^2-4*v^3)*c

/-- Constant coefficient in the same actual pair row. -/
def finiteQConstant (u v c : R) : R :=
  -(u-v)^3*(3+4*(u+v)*c)

/-- The five rows ab,as,bs,at,bt, with the anchor factor divided out of
each nonconstant column. All coefficients are integer polynomials. -/
def finiteQDividedMatrix (a b s t c : R) : Matrix (Fin 5) (Fin 5) R :=
  !![finiteQConstant a b c, finiteQLeft a b c, finiteQRight a b c, 0, 0;
     finiteQConstant a s c, finiteQLeft a s c, 0, finiteQRight a s c, 0;
     finiteQConstant b s c, 0, finiteQLeft b s c, finiteQRight b s c, 0;
     finiteQConstant a t c, finiteQLeft a t c, 0, 0, finiteQRight a t c;
     finiteQConstant b t c, 0, finiteQLeft b t c, 0, finiteQRight b t c]









end D1Bound5
end



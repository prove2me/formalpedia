-- Prove2me | Definitions.Def_D1Bound5_MatrixOperatorNorm_Definitions
-- name    : D1Bound5_MatrixOperatorNorm_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T03:35:37.234032+00:00
-- url     : https://prove2.me/theorems/0b6e2b22-b7a3-4763-a3ee-1342f5cd586b
-- title:
--   Matrix Operator Norm
-- statement:
--   Definitions for matrix operator norm in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `swap01_23`, `swap02_13`, `swap03_12`.
-- source:
--   D1Bound5/MatrixOperatorNorm.lean, lines 11-11, SHA-256 e3a215e2d0f7fe9174e19270dccf5ae1e487d675d84922a6f8a84e2966da5d96; D1Bound5/MatrixOperatorNorm.lean, lines 12-12, SHA-256 e3a215e2d0f7fe9174e19270dccf5ae1e487d675d84922a6f8a84e2966da5d96; D1Bound5/MatrixOperatorNorm.lean, lines 13-13, SHA-256 e3a215e2d0f7fe9174e19270dccf5ae1e487d675d84922a6f8a84e2966da5d96. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

 def swap01_23 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
 def swap02_13 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
 def swap03_12 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2











end D1Bound5

namespace D1Bound5









end D1Bound5
end



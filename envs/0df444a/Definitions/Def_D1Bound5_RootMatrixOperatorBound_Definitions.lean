-- Prove2me | Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
-- name    : D1Bound5_RootMatrixOperatorBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:05:47.995781+00:00
-- url     : https://prove2.me/theorems/a8203886-de16-495d-980a-b7233806650a
-- title:
--   Root Matrix Operator Bound
-- statement:
--   The reference matrix (J_4-I_4)/2 in the determinant estimates. The named objects in this bundle include `halfOffDiagonal`.
-- source:
--   D1Bound5/RootMatrixOperatorBound.lean, lines 8-10, SHA-256 bebb47341f2dbce50938d93401ea24ad5d189f7f69df4fffbfa01c87f611352c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

namespace D1Bound5

/-- The reference matrix (J_4-I_4)/2 in the determinant estimates. -/
noncomputable def halfOffDiagonal : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if i = j then 0 else (1/2 : ℂ)





end D1Bound5
end



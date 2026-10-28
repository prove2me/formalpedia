-- Prove2me | Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
-- name    : D1Bound5_ReferenceMatrixSpectral_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:39.41518+00:00
-- url     : https://prove2.me/theorems/b8b53bce-23c8-458f-aa9c-dbc844b84e7d
-- title:
--   Reference Matrix Spectral
-- statement:
--   An explicit inverse of the reference matrix `(J₄-I₄)/2`. The named objects in this bundle include `halfOffDiagonalInverse`, `negativeOnes`, `positiveOnes`.
-- source:
--   D1Bound5/ReferenceMatrixSpectral.lean, lines 11-13, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001; D1Bound5/ReferenceMatrixSpectral.lean, lines 38-38, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001; D1Bound5/ReferenceMatrixSpectral.lean, lines 39-39, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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

/-- An explicit inverse of the reference matrix `(J₄-I₄)/2`. -/
noncomputable def halfOffDiagonalInverse : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if i = j then (-4/3 : ℂ) else (2/3 : ℂ)







 def negativeOnes : Fin 4 → ℂ := fun _ => -1
 def positiveOnes : Fin 4 → ℂ := fun _ => 1







end D1Bound5
end



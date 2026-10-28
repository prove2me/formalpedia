-- Prove2me | Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
-- name    : D1Bound5_ProductFiveRankTwo_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:45.186868+00:00
-- url     : https://prove2.me/theorems/ce40374f-e25d-4a71-8f8b-a6c792e029ee
-- title:
--   Product Five Rank Two
-- statement:
--   Two columns encoding the two low-rank directions of the fifth-entry Schur complement. The named objects in this bundle include `productFiveColumns`, `productFiveRows`, `productFiveSchur`.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 45-49, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902; D1Bound5/ProductFiveRankTwo.lean, lines 51-54, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902; D1Bound5/ProductFiveRankTwo.lean, lines 161-168, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5





/-- Two columns encoding the two low-rank directions of the fifth-entry
Schur complement. -/
def productFiveColumns (f w : Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 2) ℂ :=
  fun i k => if k = 0 then f i else w i

/-- Rows encoding the exact non-Hermitian low-rank perturbation. -/
noncomputable def productFiveRows (f w : Fin 4 → ℂ) (d : ℂ) :
    Matrix (Fin 2) (Fin 4) ℂ :=
  fun k i => if k = 0 then -(w i / d + f i / d^2) else -(f i / d)











/-- The four-by-four Schur complement from (integrated-3), written
entrywise so it does not depend on any matrix-divide conventions. -/
noncomputable def productFiveSchur
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => F i j - (w i * f j + f i * w j) / d -
    f i * f j / d^2





end D1Bound5
end



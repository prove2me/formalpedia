-- Prove2me | Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
-- name    : D1Bound5_ProductFiveArithmeticClosure_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:16.625376+00:00
-- url     : https://prove2.me/theorems/44aa8b35-ecdb-42ce-83bc-6f43953d45fa
-- title:
--   Product Five Arithmetic Closure
-- statement:
--   The four-by-four Schur complement of a normalized five-entry root matrix. The named objects in this bundle include `fiveNormalizedSchur`.
-- source:
--   D1Bound5/ProductFiveArithmeticClosure.lean, lines 10-17, SHA-256 0da19bb1f7a607bd1cb647f269c6c5f92cae2602755ad9eddbe0deb76e5a496d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5

/-- The four-by-four Schur complement of a normalized five-entry root matrix. -/
noncomputable def fiveNormalizedSchur
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  productFiveSchur
    (fivePrefixError (normalizedRootError t u M))
    (fiveLastError (normalizedRootError t u M))
    (fivePrefixValues t) (fiveLastValue t)









end D1Bound5
end



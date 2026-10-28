-- Prove2me | Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
-- name    : D1Bound5_ProductFiveMatrixBridge_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:05:45.966253+00:00
-- url     : https://prove2.me/theorems/d0d5c518-bd50-4d04-b793-38dea83ce59f
-- title:
--   Product Five Matrix Bridge
-- statement:
--   The four-entry prefix, using the canonical inclusion into five indices. The named objects in this bundle include `fivePrefixError`, `fiveLastError`, `fivePrefixValues`, `fiveLastValue`.
-- source:
--   D1Bound5/ProductFiveMatrixBridge.lean, lines 8-11, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc; D1Bound5/ProductFiveMatrixBridge.lean, lines 13-15, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc; D1Bound5/ProductFiveMatrixBridge.lean, lines 17-19, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc; D1Bound5/ProductFiveMatrixBridge.lean, lines 21-23, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc. Project: https://github.com/tomislav-math/d1-bound5-lean

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

/-- The four-entry prefix, using the canonical inclusion into five indices. -/
def fivePrefixError (E : Matrix (Fin 5) (Fin 5) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => E (Fin.castAdd 1 i) (Fin.castAdd 1 j)

/-- The last column of a five-entry correction matrix. -/
def fiveLastError (E : Matrix (Fin 5) (Fin 5) ℂ) : Fin 4 → ℂ :=
  fun i => E (Fin.castAdd 1 i) (Fin.natAdd 4 (0 : Fin 1))

/-- The first four tuple elements. -/
def fivePrefixValues (t : Fin 5 → ℂ) : Fin 4 → ℂ :=
  fun i => t (Fin.castAdd 1 i)

/-- The last tuple element, without introducing square roots or division. -/
def fiveLastValue (t : Fin 5 → ℂ) : ℂ :=
  t (Fin.natAdd 4 (0 : Fin 1))







end D1Bound5
end



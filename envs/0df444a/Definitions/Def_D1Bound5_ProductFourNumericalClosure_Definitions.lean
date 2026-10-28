-- Prove2me | Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
-- name    : D1Bound5_ProductFourNumericalClosure_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:13.440412+00:00
-- url     : https://prove2.me/theorems/f92a82c4-e6d6-4b63-9f30-014964a80707
-- title:
--   Product Four Numerical Closure
-- statement:
--   The exact rational parameters in the large-entry branch of `lem:product-four`, with e = 128/8649. The named objects in this bundle include `productFourS`, `productFourH`.
-- source:
--   D1Bound5/ProductFourNumericalClosure.lean, lines 9-11, SHA-256 fb992c197fe0f50a9f89f189349d42efc0b35d9ebec71e17006e6846eae15712; D1Bound5/ProductFourNumericalClosure.lean, lines 13-13, SHA-256 fb992c197fe0f50a9f89f189349d42efc0b35d9ebec71e17006e6846eae15712. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- The exact rational parameters in the large-entry branch of
`lem:product-four`, with e = 128/8649. -/
noncomputable def productFourS : ℝ := 3139 / 5766

noncomputable def productFourH : ℝ := 8905 / 5766







end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_MixedProductFourGrowth_Definitions
-- name    : D1Bound5_MixedProductFourGrowth_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:37.559792+00:00
-- url     : https://prove2.me/theorems/a03be539-5ebb-43a1-8310-988bf03ce236
-- title:
--   Mixed Product Four Growth
-- statement:
--   Exact parameters in the A >= 1, B >= 3 case of product-four. The named objects in this bundle include `productFourMixedS`, `productFourMixedH`.
-- source:
--   D1Bound5/MixedProductFourGrowth.lean, lines 44-45, SHA-256 6405700c83d4efaa313716abc06975c43c8dd7320d44c6d848be130386d5f504; D1Bound5/MixedProductFourGrowth.lean, lines 46-46, SHA-256 6405700c83d4efaa313716abc06975c43c8dd7320d44c6d848be130386d5f504. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5



/-- Exact parameters in the A >= 1, B >= 3 case of product-four. -/
noncomputable def productFourMixedS : ℝ := 59 / 96
noncomputable def productFourMixedH : ℝ := 155 / 96












end D1Bound5
end



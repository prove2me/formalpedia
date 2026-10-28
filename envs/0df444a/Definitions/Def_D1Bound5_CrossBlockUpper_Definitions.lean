-- Prove2me | Definitions.Def_D1Bound5_CrossBlockUpper_Definitions
-- name    : D1Bound5_CrossBlockUpper_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:42:19.303983+00:00
-- url     : https://prove2.me/theorems/8cf6d5cd-1096-44ac-86e8-88cdbbb20f5e
-- title:
--   Cross Block Upper
-- statement:
--   The thirteen terms of a product that survive alternating over columns in the determinant of a quadratic rank-one matrix, a linear rank-one matrix, and an error matrix. The named objects in this bundle include `crossBlock_keptProduct`.
-- source:
--   D1Bound5/CrossBlockUpper.lean, lines 19-27, SHA-256 751cfc90c8157cd148f1ea291c9c2514ef722d3e7ded4f856850dac4856d5706. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5



/-- The thirteen terms of a product that survive alternating over columns
in the determinant of a quadratic rank-one matrix, a linear rank-one
matrix, and an error matrix. -/
 noncomputable def crossBlock_keptProduct (x e : Fin 3 → ℂ) : ℂ :=
  e 0*e 1*e 2 +
  (x 0^2*e 1*e 2+x 1^2*e 0*e 2+x 2^2*e 0*e 1) +
  (1/2 : ℂ)*(x 0*e 1*e 2+x 1*e 0*e 2+x 2*e 0*e 1) +
  (1/2 : ℂ)*(x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2+
    x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0)





end D1Bound5
end



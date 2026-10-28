-- Prove2me | Definitions.Def_D1Bound5_FiniteA5IntegralRows_Definitions
-- name    : D1Bound5_FiniteA5IntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:35:32.456979+00:00
-- url     : https://prove2.me/theorems/56210b22-14ea-47c8-a71f-d0a84be7b61e
-- title:
--   Finite A5Integral Rows
-- statement:
--   The actual integral A5 form, using source-ring signed root products. The named objects in this bundle include `finiteA5RowForm`.
-- source:
--   D1Bound5/FiniteA5IntegralRows.lean, lines 29-31, SHA-256 135a11e7f96cd3ffa5b3aba636da84c37adec2ecbaa3d92a22ae8fb4a3140799. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral A5 form, using source-ring signed root products. -/
def finiteA5RowForm (x y c z sX sY : R) (i : Fin 3) : R :=
  (finiteA5DividedMatrix x y c).mulVec ![z,sX,sY] i







end D1Bound5
end



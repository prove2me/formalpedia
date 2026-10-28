-- Prove2me | Definitions.Def_D1Bound5_FiniteA4IntegralRows_Definitions
-- name    : D1Bound5_FiniteA4IntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:34:44.982996+00:00
-- url     : https://prove2.me/theorems/f7e27f1c-fba9-481e-8ef8-c324c9ded0a5
-- title:
--   Finite A4Integral Rows
-- statement:
--   The actual integral A4 form, using source-ring signed root products. The named objects in this bundle include `finiteA4RowForm`.
-- source:
--   D1Bound5/FiniteA4IntegralRows.lean, lines 29-31, SHA-256 b56979ac7f4b1c57a6032fbeb1344d28af0ac543b385ae16ed83d797b116c686. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral A4 form, using source-ring signed root products. -/
def finiteA4RowForm (x y c z sX sY : R) (i : Fin 3) : R :=
  (finiteA4DividedMatrix x y c).mulVec ![z,sX,sY] i







end D1Bound5
end



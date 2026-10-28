-- Prove2me | Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions
-- name    : D1Bound5_FiniteN2IntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:08.955988+00:00
-- url     : https://prove2.me/theorems/46a80baf-7d80-4043-bc53-248344534edc
-- title:
--   Finite N2Integral Rows
-- statement:
--   The actual integral N2 form, using source-ring signed root products. The named objects in this bundle include `finiteN2RowForm`.
-- source:
--   D1Bound5/FiniteN2IntegralRows.lean, lines 29-31, SHA-256 24e7bcc1d136549034d85c5aaaf506ddde891a0489583b3f2c16180cc599e2b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral N2 form, using source-ring signed root products. -/
def finiteN2RowForm (x y c z sX sY : R) (i : Fin 3) : R :=
  (finiteN2DividedMatrix x y c).mulVec ![z,sX,sY] i







end D1Bound5
end



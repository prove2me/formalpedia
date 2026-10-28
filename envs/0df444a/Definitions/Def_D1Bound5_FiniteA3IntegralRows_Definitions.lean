-- Prove2me | Definitions.Def_D1Bound5_FiniteA3IntegralRows_Definitions
-- name    : D1Bound5_FiniteA3IntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:34:23.016585+00:00
-- url     : https://prove2.me/theorems/73b0880d-3257-4c6d-af3c-1e30e34ddcce
-- title:
--   Finite A3Integral Rows
-- statement:
--   The actual integral A3 form, using source-ring signed root products. The named objects in this bundle include `finiteA3RowForm`.
-- source:
--   D1Bound5/FiniteA3IntegralRows.lean, lines 29-31, SHA-256 42033bb8bd85c414b4848eee578bd650370e19045d35bbad0e464de2a0fcbbf2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral A3 form, using source-ring signed root products. -/
def finiteA3RowForm (x y c z sX sY : R) (i : Fin 3) : R :=
  (finiteA3DividedMatrix x y c).mulVec ![z,sX,sY] i







end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_FiniteN3IntegralRows_Definitions
-- name    : D1Bound5_FiniteN3IntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:24:45.360761+00:00
-- url     : https://prove2.me/theorems/2e127ca1-53ee-4ad4-ab62-6bd2428ac7d0
-- title:
--   Finite N3Integral Rows
-- statement:
--   The actual integral N3 form, using source-ring signed root products. The named objects in this bundle include `finiteN3RowForm`.
-- source:
--   D1Bound5/FiniteN3IntegralRows.lean, lines 29-31, SHA-256 c3427020ac3dfeb2a74c0f0beb97b619fe1be1a02fad1755f9a8e51d90f6d4bc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral N3 form, using source-ring signed root products. -/
def finiteN3RowForm (x y c z sX sY : R) (i : Fin 3) : R :=
  (finiteN3DividedMatrix x y c).mulVec ![z,sX,sY] i







end D1Bound5
end



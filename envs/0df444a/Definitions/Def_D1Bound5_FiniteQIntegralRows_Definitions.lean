-- Prove2me | Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
-- name    : D1Bound5_FiniteQIntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:27:25.883861+00:00
-- url     : https://prove2.me/theorems/2337faf1-9266-4b57-822c-1f2f4fdb6553
-- title:
--   Finite QIntegral Rows
-- statement:
--   The actual integral form supplied by each row of the finite Q family. The root products are inputs in the original ring, so integrality is preserved without division by anchors. The named objects in this bundle include `finiteQRowForm`.
-- source:
--   D1Bound5/FiniteQIntegralRows.lean, lines 30-34, SHA-256 13dbc71d3f13cc35a26b1a62808a9ec3ba2232668209833fc8f21e0bdba9f6ad. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]









/-- The actual integral form supplied by each row of the finite Q family.
The root products are inputs in the original ring, so integrality is
preserved without division by anchors. -/
def finiteQRowForm (a b s t c z rA rB rS rT : R) (i : Fin 5) : R :=
  (finiteQDividedMatrix a b s t c).mulVec ![z, rA, rB, rS, rT] i







end D1Bound5
end



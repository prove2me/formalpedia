-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
-- name    : D1Bound5_SmallPairGraphSymmetry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:16:14.451154+00:00
-- url     : https://prove2.me/theorems/1f8d5b98-9d3c-4019-9f69-b59cc5f1cf60
-- title:
--   Small Pair Graph Symmetry
-- statement:
--   No compatible triple of distinct proper common extensions lies in the closed annulus with radii 3 and 10^550. The named objects in this bundle include `SmallPairGraphProperty`.
-- source:
--   D1Bound5/SmallPairGraphSymmetry.lean, lines 10-16, SHA-256 fe95f828c789959447eda784c0aa5f4516dacd522e3da889399545aa071a7bef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- No compatible triple of distinct proper common extensions lies in the
closed annulus with radii 3 and 10^550. -/
def SmallPairGraphProperty {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) : Prop :=
  ∀ t : Fin 3 → QuadInt tau nu, IsD1Tuple t →
    (∀ i, ProperCommonExtension A (t i)) →
    (∀ i, 9 ≤ (t i).norm) → (∀ i, (t i).norm ≤ 10^1100) → False









end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_SmallPairClassification_Definitions
-- name    : D1Bound5_SmallPairClassification_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:52:37.420159+00:00
-- url     : https://prove2.me/theorems/34a27989-1404-48df-965f-798ee3d5b28c
-- title:
--   Small Pair Classification
-- statement:
--   The eleven full-ring models represented by the48nondegenerate pair rows. The named objects in this bundle include `smallPairModels`.
-- source:
--   D1Bound5/SmallPairClassification.lean, lines 11-14, SHA-256 a32a3e7b2d5dfed4754fd2fe6af26c9e86156fe171110d66d6c2f3d17661c981. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- The eleven full-ring models represented by the48nondegenerate pair rows. -/
def smallPairModels : Finset (ℤ × ℤ) :=
  {(0,1), (0,2), (0,5), (0,6),
   (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,8)}





end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_DegeneratePairClassification_Definitions
-- name    : D1Bound5_DegeneratePairClassification_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:05.902461+00:00
-- url     : https://prove2.me/theorems/87271e23-6a58-4df3-9fc6-44f615e307c0
-- title:
--   Degenerate Pair Classification
-- statement:
--   The ordered rational unit pair, with either orientation allowed. The named objects in this bundle include `RationalUnitPair`, `EisensteinCanonicalPair`.
-- source:
--   D1Bound5/DegeneratePairClassification.lean, lines 6-8, SHA-256 61da8c7aa871a81d9d56989ed28825c79c1cef687d7de61a56038260054cdd37; D1Bound5/DegeneratePairClassification.lean, lines 90-92, SHA-256 61da8c7aa871a81d9d56989ed28825c79c1cef687d7de61a56038260054cdd37. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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
namespace D1Bound5
open QuadInt

/-- The ordered rational unit pair, with either orientation allowed. -/
def RationalUnitPair {R : Type*} [Ring R] (a b : R) : Prop :=
  (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1)









/-- Both orientations of the exceptional Eisenstein pair. -/
def EisensteinCanonicalPair (a b : QuadInt 1 1) : Prop :=
  (a=⟨0,-1⟩ ∧ b=⟨1,-1⟩) ∨ (a=⟨1,-1⟩ ∧ b=⟨0,-1⟩)





end D1Bound5
end



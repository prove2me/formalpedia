-- Prove2me | Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions
-- name    : D1Bound5_FullRingUnitPairPell_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:30:34.27611+00:00
-- url     : https://prove2.me/theorems/8f7bdf2f-d4cd-4e4c-bbec-7b89a211ea01
-- title:
--   Full Ring Unit Pair Pell
-- statement:
--   The actual norm-two real and norm-one imaginary Pell alternatives. The signed integer v is required to be nonzero. The named objects in this bundle include `UnitPairPellDescription`.
-- source:
--   D1Bound5/FullRingUnitPairPell.lean, lines 8-13, SHA-256 2e87573896d81e7a78ce82726dbf3857615c804b12c146f1724403786fcb9e55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField QuadraticAlgebra
open Module

namespace D1Bound5

/-- The actual norm-two real and norm-one imaginary Pell alternatives.
The signed integer v is required to be nonzero. -/
def UnitPairPellDescription {R : Type*} [Ring R] (d : ℤ) (w z : R) : Prop :=
  (∃ u v : ℤ, v ≠ 0 ∧ u^2-d*v^2 = 2 ∧
    (z = ((d*v^2+1 : ℤ) : R) ∨ z = -((d*v^2+1 : ℤ) : R))) ∨
  (∃ u v : ℤ, v ≠ 0 ∧ u^2-d*v^2 = 1 ∧ z = ((2*u*v : ℤ) : R)*w)



end D1Bound5
end



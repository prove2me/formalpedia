-- Prove2me | Definitions.Def_D1Bound5_OneThreeNegative_Definitions
-- name    : D1Bound5_OneThreeNegative_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:15.886405+00:00
-- url     : https://prove2.me/theorems/2a7ecfa6-dd1a-4757-a285-c6e0b4828871
-- title:
--   One Three Negative
-- statement:
--   The same field parameter represents every nonpositive integer square; zero square roots are included. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/OneThreeNegative.lean, lines 10-17, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08; D1Bound5/OneThreeNegative.lean, lines 19-24, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The same field parameter represents every nonpositive integer square;
zero square roots are included. -/
theorem nonpositive_integer_square_trace_zero {d m : ℤ} (hm : m ≤ 0)
    (hr : ∃ r : QuadInt 0 d, r*r = (m : QuadInt 0 d)) :
    ∃ y : ℤ, m = -d*y^2 := by
  rcases eq_or_lt_of_le hm with h | h
  · exact ⟨0, by simp [h]⟩
  · exact negative_integer_square_trace_zero h hr

theorem nonpositive_integer_square_trace_one {nu m : ℤ} (hm : m ≤ 0)
    (hr : ∃ r : QuadInt 1 nu, r*r = (m : QuadInt 1 nu)) :
    ∃ y : ℤ, m = -(4*nu-1)*y^2 := by
  rcases eq_or_lt_of_le hm with h | h
  · exact ⟨0, by simp [h]⟩
  · exact negative_integer_square_trace_one h hr



























end D1Bound5
end



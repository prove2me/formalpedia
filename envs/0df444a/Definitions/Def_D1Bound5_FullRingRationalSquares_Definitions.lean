-- Prove2me | Definitions.Def_D1Bound5_FullRingRationalSquares_Definitions
-- name    : D1Bound5_FullRingRationalSquares_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:34.082078+00:00
-- url     : https://prove2.me/theorems/2d1da580-0913-4dba-b426-e7de5e3ec3fa
-- title:
--   Full Ring Rational Squares
-- statement:
--   Square-root existence is transported through any ring equivalence, including roots equal to zero. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/FullRingRationalSquares.lean, lines 9-17, SHA-256 5e6a9ffe5db3306b6d3f7e27d41771f8b8cc8d19bc56609362cb3ac1f5ebd2ab. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Square-root existence is transported through any ring equivalence,
including roots equal to zero. -/
theorem integer_square_under_ring_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (m : ℤ)
    (h : ∃ r : S, r*r = (m : S)) :
    ∃ r : R, r*r = (m : R) := by
  obtain ⟨r,hr⟩ := h
  refine ⟨e.symm r, ?_⟩
  simpa only [map_mul, map_intCast] using congrArg e.symm hr





end D1Bound5
end



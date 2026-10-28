-- Prove2me | Definitions.Def_D1Bound5_FiniteTail_Definitions
-- name    : D1Bound5_FiniteTail_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:29:04.606409+00:00
-- url     : https://prove2.me/theorems/2def6367-307b-425a-be03-9e04c5f65bb3
-- title:
--   Finite Tail
-- statement:
--   Finite exhaustive check for the small-tail case of lem:tail-irregular. The disk and square-test procedures have independent completeness proofs. The named objects in this bundle include `SmallTailCheck`.
-- source:
--   D1Bound5/FiniteTail.lean, lines 35-47, SHA-256 4a84a3e4ca3b7d43920e93e12f04cbea329f4d21bc5572c8337e09d252793110. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5

open QuadInt





/-- Finite exhaustive check for the small-tail case of lem:tail-irregular.
The disk and square-test procedures have independent completeness proofs. -/
def SmallTailCheck (tau nu : ℤ) : Prop :=
  ∀ b ∈ disk tau nu 15, ∀ c ∈ disk tau nu 15,
    9 ≤ b.norm → b.norm ≤ c.norm → b ≠ c →
    hasSquareRoot (b*c+1) = true →
      ∀ d ∈ ({b+c+2*rootCandidate (b*c+1),b+c-2*rootCandidate (b*c+1)} :
          Finset (QuadInt tau nu)),
        d ≠ 0 → d ≠ b → d ≠ c → c.norm ≤ d.norm →
        ∀ a ∈ disk tau nu 15,
          a ≠ 0 → a ≠ b → a ≠ c → a ≠ d → a.norm ≤ b.norm →
          hasSquareRoot (a*b+1) = true → hasSquareRoot (a*c+1) = true →
          hasSquareRoot (a*d+1) = false








end D1Bound5
end



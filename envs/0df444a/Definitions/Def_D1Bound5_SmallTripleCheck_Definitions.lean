-- Prove2me | Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
-- name    : D1Bound5_SmallTripleCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:38.188202+00:00
-- url     : https://prove2.me/theorems/af20f072-83bd-4cbb-b455-eed006907c17
-- title:
--   Small Triple Check
-- statement:
--   Unordered coordinate set of an indexed triple. The named objects in this bundle include `tripleCoordinates`, `smallTripleClassifiedBool`.
-- source:
--   D1Bound5/SmallTripleCheck.lean, lines 6-8, SHA-256 1f75bcdaa9e326145897ef273ea3989447fff478e71849b1db21c3aa9abd5c19; D1Bound5/SmallTripleCheck.lean, lines 10-27, SHA-256 1f75bcdaa9e326145897ef273ea3989447fff478e71849b1db21c3aa9abd5c19. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

/-- Unordered coordinate set of an indexed triple. -/
def tripleCoordinates {tau nu : ℤ} (a b c : QuadInt tau nu) : Finset (ℤ × ℤ) :=
  {(a.re, a.im), (b.re, b.im), (c.re, c.im)}

/-- Every three-clique in the input disk must occur in the supplied table.
The checker does not impose an ordering on its three input vertices. -/
def smallTripleClassifiedBool {tau nu : ℤ} (xs : List (QuadInt tau nu))
    (rows : List (Finset (ℤ × ℤ))) : Bool :=
  xs.all fun a =>
    if decide (a ≠ 0) then
      xs.all fun b =>
        if decide (b ≠ 0 ∧ a ≠ b) then
          if hasSquareRoot (a*b+1) then
            xs.all fun c =>
              if decide (c ≠ 0 ∧ a ≠ c ∧ b ≠ c) then
                if hasSquareRoot (a*c+1) && hasSquareRoot (b*c+1) then
                  decide (tripleCoordinates a b c ∈ rows)
                else true
              else true
          else true
        else true
    else true



end D1Bound5
end



-- Prove2me | Definitions.Def_D1Bound5_SmallTailExplicit_Definitions
-- name    : D1Bound5_SmallTailExplicit_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:50:57.12583+00:00
-- url     : https://prove2.me/theorems/14bdb244-912d-4cae-bd42-74ebdde4fbcf
-- title:
--   Small Tail Explicit
-- statement:
--   Check the two regular completions against every candidate first entry. The list may contain zero and anchor coincidences; the guards handle them. The named objects in this bundle include `tailPairBool`, `tailListBool`.
-- source:
--   D1Bound5/SmallTailExplicit.lean, lines 6-19, SHA-256 1276e7682da7a886b79eccc5e7267d374a94b67c65efc71b70ac09c8660526af; D1Bound5/SmallTailExplicit.lean, lines 21-26, SHA-256 1276e7682da7a886b79eccc5e7267d374a94b67c65efc71b70ac09c8660526af. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

/-- Check the two regular completions against every candidate first entry.
The list may contain zero and anchor coincidences; the guards handle them. -/
def tailPairBool {tau nu : ℤ} (xs : List (QuadInt tau nu))
    (b c : QuadInt tau nu) : Bool :=
  let r := rootCandidate (b*c+1)
  [b+c+2*r,b+c-2*r].all fun d =>
    if decide (d ≠ 0 ∧ d ≠ b ∧ d ≠ c ∧ c.norm ≤ d.norm) then
      xs.all fun a =>
        if decide (a ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a.norm ≤ b.norm) then
          if hasSquareRoot (a*b+1) && hasSquareRoot (a*c+1) then
            !(hasSquareRoot (a*d+1))
          else true
        else true
    else true

/-- A fully explicit list checker, avoiding noncomputable list conversion. -/
def tailListBool {tau nu : ℤ} (xs : List (QuadInt tau nu)) : Bool :=
  xs.all fun b => xs.all fun c =>
    if decide (9 ≤ b.norm ∧ b.norm ≤ c.norm ∧ b ≠ c) then
      if hasSquareRoot (b*c+1) then tailPairBool xs b c else true
    else true



end D1Bound5
end



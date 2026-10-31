-- Prove2me | Definitions.Def_Tatamibari_NPC_ClauseSemantics
-- name    : Tatamibari_NPC_ClauseSemantics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:23.432787+00:00
-- url     : https://prove2.me/theorems/0b0c67b3-b7c0-40d5-b079-fe010dea959c
-- title:
--   Wire values and geometric enforcement-line crossing
-- statement:
--   A variable has one value when all nine square clues in each of its arbitrarily many branches use the same vertical shift. Safe placement of its constituent wires is stated independently. The enforcement clues have coordinates (9,13), (15+a,9), and (21+a+b,5) before reflection, where a and b are the clause extension parameters. An enforcement rectangle crosses to the verification wire when it contains both its own clue and the cell in column 5 at that clue's row. Reflection changes the row coordinate for a negative clause. This crossing predicate refers to actual rectangles, not to membership in a Boolean truth table.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 12, Sections 1–3 (definitions and figures)

import Definitions.Def_Tatamibari_NPC_Reduction

set_option autoImplicit false

namespace Tatamibari.NPC

def variableWiresSafe (b : Board) (offset : Cell) (n : Nat) : Prop :=
  ∀ i < n, safelyPlaced b (offset.1+6*i+1, offset.2) 9

def variableHasValue (offset : Cell) (n : Nat) (rs : List Rectangle) (down : Bool) : Prop :=
  ∀ i < n, ∀ j < 9,
    squarePosition (translateCell offset (6*i+2,2*j+2)) down ∈ rs

def reflectPoint (h : Nat) (p : Cell) : Cell := (p.1,h-1-p.2)
def enforcementClue (a b : Nat) (negative : Bool) (port : Nat) : Cell :=
  let p := if port = 0 then (9,13) else if port = 1 then (15+a,9) else (21+a+b,5)
  if negative then reflectPoint 22 p else p

/-- Reaching the clause-verification wire means containing its left column
at the enforcement line's row. It is not defined by the port's Boolean value. -/
def enforcementCrosses (a b : Nat) (negative : Bool) (port : Nat)
    (r : Rectangle) : Bool :=
  r.contains (enforcementClue a b negative port) &&
  r.contains (5,(enforcementClue a b negative port).2)

end Tatamibari.NPC



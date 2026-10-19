-- Prove2me | Definitions.Def_AngelDevil_SquareBoundary
-- name    : AngelDevil_SquareBoundary
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:52:27.129242+00:00
-- url     : https://prove2.me/theorems/4391822a-6fe3-4195-bbb4-f998a5562061
-- title:
--   Side-connected integer squares and their unit boundary
-- statement:
--   Squares are indexed by integer pairs. The four side neighbors differ by one in exactly one coordinate. A finite set is connected when it is nonempty and any two members can be joined by a finite sequence of side-neighbor steps within the set. Each exposed side is a direction from an occupied square to an unoccupied neighbor. The perimeter counts all such sides, including hole boundaries. The wall set records the occupied square and side direction.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript p. 6, Definition 4.1 and Claim 4.2.

import Definitions.Def_AngelDevil_Game
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

namespace AngelDevil

/-- Four oriented sides of an integer unit square. -/
abbrev SquareSide := Bool × Bool

def sideNeighbor (v : Point) (d : SquareSide) : Point :=
  if d.1 then (v.1, v.2 + if d.2 then -1 else 1)
  else (v.1 + if d.2 then -1 else 1, v.2)

def oppositeSide (d : SquareSide) : SquareSide := (d.1, !d.2)

def SquareAdjacent (u v : Point) : Prop := ∃ d, sideNeighbor u d = v

def exposedSides (s : Finset Point) (v : Point) : Finset SquareSide :=
  Finset.univ.filter (fun d => sideNeighbor v d ∉ s)

/-- Number of unit boundary sides, including sides surrounding holes. -/
def squarePerimeter (s : Finset Point) : Nat :=
  ∑ v ∈ s, (exposedSides s v).card

def SquaresConnected (s : Finset Point) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s,
    Relation.ReflTransGen (fun u v => u ∈ s ∧ v ∈ s ∧ SquareAdjacent u v) a b

/-- A wall records its occupied square and the direction of its empty neighbor. -/
def boundaryWalls (s : Finset Point) : Finset (Point × SquareSide) :=
  s.biUnion (fun v => (exposedSides s v).image (fun d => (v, d)))

end AngelDevil



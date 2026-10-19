-- Prove2me | Definitions.Def_AngelDevil_WallWalk
-- name    : AngelDevil_WallWalk
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:12:52.670777+00:00
-- url     : https://prove2.me/theorems/778bd072-6fcb-407d-85d0-a013477fb67c
-- title:
--   Octagonal boundary walk and the power-two wall strategy
-- statement:
--   A directed wall is an occupied integer square with an outward side direction. The tangent points counterclockwise from the outward normal. To advance, first test the occupied square's tangent neighbor: if empty, turn around the same square, even when the diagonal square is occupied. Otherwise test the diagonal square: if empty, continue straight; if occupied, turn around the concave corner. Obstacles consist of all squares with negative first coordinate together with the recorded Devil choices. Starting with the east side of square (-1,0), the strategy performs exactly two wall transitions after each Devil move and lands in the outside square. Its state is reconstructed from the chronological burn history. The wall trace records individual transitions, using the same obstacle set for both transitions of a round.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303; author manuscript pp. 6-8, octagonal wall-following rule, Claim 3.1 analogue, Proposition 4.3 and Theorem 4.5. Two wall transitions per turn give an admissible power-two implementation; no-return is the remaining geometric obligation.

import Definitions.Def_AngelDevil_SquareBoundary

namespace AngelDevil

abbrev Wall := Point × SquareSide

/-- Counterclockwise rotation of the outward normal: occupied squares are left. -/
def tangentSide (d : SquareSide) : SquareSide :=
  (!d.1, if d.1 then !d.2 else d.2)

def wallOutside (w : Wall) : Point := sideNeighbor w.1 w.2

def IsBoundaryWall (B : Set Point) (w : Wall) : Prop :=
  w.1 ∈ B ∧ wallOutside w ∉ B

/-- The corner rule for shrunken blocks. An empty side-neighbor takes
priority over a diagonally touching block, so the walker passes through the gap. -/
noncomputable def nextWall (B : Set Point) (w : Wall) : Wall := by
  classical
  let t := tangentSide w.2
  let a := sideNeighbor w.1 t
  let b := sideNeighbor a w.2
  exact if a ∉ B then (w.1, t)
    else if b ∉ B then (a, w.2)
    else (b, oppositeSide t)

noncomputable def previousWall (B : Set Point) (w : Wall) : Wall := by
  classical
  let t := oppositeSide (tangentSide w.2)
  let a := sideNeighbor w.1 t
  let b := sideNeighbor a w.2
  exact if a ∉ B then (w.1, t)
    else if b ∉ B then (a, w.2)
    else (b, oppositeSide t)

def initialWall : Wall := ((-1, 0), (false, false))

def wallObstacles (burned : List (Option Point)) : Set Point :=
  {v | v.1 < 0 ∨ some v ∈ burned}

/-- Two wall transitions per turn fit inside the power-two movement box. -/
noncomputable def wallHistory (burned : List (Option Point)) : Wall :=
  if _h : burned = [] then initialWall else
  let w := wallHistory burned.dropLast
  nextWall (wallObstacles burned) (nextWall (wallObstacles burned) w)
termination_by burned.length
decreasing_by
  have hp := List.length_pos_iff.mpr _h
  simp only [List.length_dropLast]
  omega

noncomputable def wallAngel : AngelStrategy :=
  fun _ burned => wallOutside (wallHistory burned)

def traceObstacles (D : DevilStrategy) (i : Nat) : Set Point :=
  wallObstacles (play wallAngel D (i / 2 + 1)).burned

noncomputable def wallTrace (D : DevilStrategy) : Nat → Wall
  | 0 => initialWall
  | i+1 => nextWall (traceObstacles D i) (wallTrace D i)

end AngelDevil



-- Prove2me | Definitions.Def_SquarePeg_shapes
-- name    : SquarePeg_shapes
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T23:18:32.494739+00:00
-- url     : https://prove2.me/theorems/c2bac18a-df63-41d5-b421-673c3f2d2323
-- title:
--   Squares, rectangles, and similarity (square peg problem)
-- statement:
--   Predicates on four points of the Euclidean plane, in cyclic order. $\mathrm{IsRectangle}(p_1,p_2,p_3,p_4)$ holds when the diagonals bisect each other ($p_1+p_3=p_2+p_4$) and have equal length, with adjacent vertices distinct; this is exactly a non-degenerate rectangle. $\mathrm{IsSquare}$ adds that two adjacent sides have equal length, giving a non-degenerate square. $\mathrm{SameShape}$ says two quadrilaterals have all six pairwise distances in one common positive ratio (similarity, possibly reflected); $\mathrm{SimilarTriangle}$ is the analogous relation for triangles. Non-degeneracy is built in, so four coincident points never form a square.
-- source:
--   Standard Euclidean geometry. The equal-side/equal-diagonal test-map description and the degenerate components follow Matschke, A survey on the square peg problem, Notices AMS 61(4) (2014), 346-352, p. 348 (equation (1)) and p. 346 (Figure 2).

import Mathlib
import Definitions.Def_SchoenfliesPlaneCore

open Schoenflies

namespace SquarePeg

/-- Four points forming a non-degenerate rectangle, listed in cyclic order:
the diagonals bisect each other and have equal length, and adjacent vertices differ. -/
def IsRectangle (p1 p2 p3 p4 : Plane) : Prop :=
  p1 + p3 = p2 + p4 ∧ dist p1 p3 = dist p2 p4 ∧ p1 ≠ p2 ∧ p2 ≠ p3

/-- Four points forming a non-degenerate square, listed in cyclic order:
a rectangle with two adjacent sides of equal length. -/
def IsSquare (p1 p2 p3 p4 : Plane) : Prop :=
  IsRectangle p1 p2 p3 p4 ∧ dist p1 p2 = dist p2 p3

/-- Two quadrilaterals whose six pairwise distances are in one common positive ratio
(similar, possibly reflected). -/
def SameShape (p1 p2 p3 p4 q1 q2 q3 q4 : Plane) : Prop :=
  ∃ s : ℝ, 0 < s ∧
    dist p1 p2 = s * dist q1 q2 ∧ dist p2 p3 = s * dist q2 q3 ∧
    dist p3 p4 = s * dist q3 q4 ∧ dist p4 p1 = s * dist q4 q1 ∧
    dist p1 p3 = s * dist q1 q3 ∧ dist p2 p4 = s * dist q2 q4

/-- Two triangles whose corresponding side lengths are in one common positive ratio
(similar, possibly reflected). -/
def SimilarTriangle (p1 p2 p3 t1 t2 t3 : Plane) : Prop :=
  ∃ s : ℝ, 0 < s ∧
    dist p1 p2 = s * dist t1 t2 ∧ dist p2 p3 = s * dist t2 t3 ∧
    dist p3 p1 = s * dist t3 t1

end SquarePeg



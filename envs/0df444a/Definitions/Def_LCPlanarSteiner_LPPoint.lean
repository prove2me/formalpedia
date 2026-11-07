-- Prove2me | Definitions.Def_LCPlanarSteiner_LPPoint
-- name    : LCPlanarSteiner_LPPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:25.642687+00:00
-- url     : https://prove2.me/theorems/516ba532-16e4-4060-8922-d54b31c3de0d
-- title:
--   LP points as finite data
-- statement:
--   An **LP point** lists the graph, the pairs, the root $v$, $\varepsilon$, $h$, the purchases $x_e$, the demands $y_i$ and flow records $(i, \text{kind}, e, j, \text{value})$ giving the flow of pair $i$ on each staged arc. The flow of a pair on a staged arc is the sum of its records there (zero if none).
--
--   This is the input format of the junction search of Lemma 4.6.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.6, p.15; §4.4, p.14

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **A root trial of the density LP together with a candidate point, as finite data.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.6, p.15: "A feasible point of value X yields, in polynomial time, a nonempty original
junction"; §4.4, p.14 (the LP (14)–(15)).

An LP point lists the graph `net`, the pairs `dem`, the root `root`, the accuracy `ε`, the length
bound `h`, the purchases `x` (entry `e` is `x_e`), the demands `y` (entry `i` is `y_i`), and the flow
records `(i, kind, e, j, value)`: the flow of pair `i` on the staged arc `(kind, e, j)`.

`fx`, `fy`, `ff` read these as functions; `ff P i a` is the sum of the values of the records of pair
`i` on the staged arc `a` (no record: `0`).

**Formalization Note.** Records with the same arc add up; a point is checked against `LPFeasible`
through these functions. -/
structure LPPoint where
  /-- the graph -/
  net : Net
  /-- the residual pairs -/
  dem : List (ℕ × ℕ)
  /-- the root `v` of the trial -/
  root : ℕ
  /-- the accuracy `ε` -/
  ε : ℚ
  /-- the length bound `h` -/
  h : ℚ
  /-- purchases `x_e` -/
  x : List ℚ
  /-- demands `y_i` -/
  y : List ℚ
  /-- flow records `(i, kind, e, j, value)` -/
  flows : List (ℕ × ℕ × ℕ × ℕ × ℚ)

/-- Purchases as a function. -/
def LPPoint.fx (P : LPPoint) (e : ℕ) : ℚ := P.x.getD e 0

/-- Demands as a function. -/
def LPPoint.fy (P : LPPoint) (i : ℕ) : ℚ := P.y.getD i 0

/-- Flows as a function of the pair and the staged arc. -/
def LPPoint.ff (P : LPPoint) (i : ℕ) (a : ℕ × ℕ × ℕ) : ℚ :=
  ((P.flows.filter fun rc => decide (rc.1 = i ∧ (rc.2.1, rc.2.2.1, rc.2.2.2.1) = a)).map
    fun rc => rc.2.2.2.2).sum

end LCPlanarSteiner



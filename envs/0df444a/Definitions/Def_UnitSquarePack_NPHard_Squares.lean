-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_Squares
-- name    : UnitSquarePack_NPHard_Squares
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:18:53.258919+00:00
-- url     : https://prove2.me/theorems/d8474c23-6069-491d-aad0-9b1b2f3861b5
-- title:
--   Axis-aligned 2×2 squares, packings in a set, and unions of unit grid cells
-- statement:
--   For $c = (a, b) \in \mathbb R^2$ let $Q(c) = [a, a+2] \times [b, b+2]$ be the closed axis-aligned $2 \times 2$ square with lower-left corner $c$.
--
--   A **packing** of $k$ squares in a set $P \subseteq \mathbb R^2$ is a list of corners $c_0, \dots, c_{k-1} \in \mathbb R^2$ such that every $Q(c_i) \subseteq P$ and distinct squares have disjoint interiors:
--   $$\operatorname{int} Q(c_i) \cap \operatorname{int} Q(c_j) = \emptyset \qquad (i \ne j).$$
--   $P$ **has room for $k$ squares** if such a packing exists. Positions are arbitrary real numbers; squares are only translated, never rotated. Squares may touch each other and the boundary of $P$.
--
--   A **unit grid cell** is $[i, i+1] \times [j, j+1]$ with $(i, j) \in \mathbb Z^2$. A set is a **finite union of unit grid cells** if it equals the union of finitely many of them. The closed region of a grid polygon, with or without holes, is such a union.
--
--   These are the objects of the decision problem 2 × 2-Square-Packing: given a polygon $P$ and an integer $k$, decide whether $P$ has room for $k$ axis-aligned $2 \times 2$ squares.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 1, §1 (2 × 2-Square-Packing); p. 6, Lemma 6

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_GridPolygon

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Set

/-- The closed axis-aligned `2 × 2` square `[a, a + 2] × [b, b + 2]` with lower-left corner
`c = (a, b) ∈ ℝ²`. -/
def square2 (c : ℝ × ℝ) : Set (ℝ × ℝ) := Icc c.1 (c.1 + 2) ×ˢ Icc c.2 (c.2 + 2)

/-- `c 0, …, c (k-1)` are the lower-left corners of a packing of `k` axis-aligned `2 × 2`
squares in `P`: every square lies in `P` and distinct squares have disjoint interiors.
Positions are arbitrary real numbers; squares are translated, never rotated. -/
def IsPackingIn (P : Set (ℝ × ℝ)) {k : ℕ} (c : Fin k → ℝ × ℝ) : Prop :=
  (∀ i, square2 (c i) ⊆ P) ∧
  ∀ i j, i ≠ j → Disjoint (interior (square2 (c i))) (interior (square2 (c j)))

/-- `P` has room for `k` axis-aligned `2 × 2` squares. -/
def HasRoomFor (P : Set (ℝ × ℝ)) (k : ℕ) : Prop :=
  ∃ c : Fin k → ℝ × ℝ, IsPackingIn P c

/-- The closed unit grid cell `[i, i + 1] × [j, j + 1]` for `(i, j) ∈ ℤ²`. -/
def unitCell (c : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Icc (c.1 : ℝ) (c.1 + 1) ×ˢ Icc (c.2 : ℝ) (c.2 + 1)

/-- `P` is the union of finitely many closed unit grid cells. The closed region of every grid
polygon, with or without holes, is such a union. -/
def IsGridCellUnion (P : Set (ℝ × ℝ)) : Prop :=
  ∃ S : Finset (ℤ × ℤ), P = ⋃ c ∈ S, unitCell c

end UnitSquarePack.NPHard



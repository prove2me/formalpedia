-- Prove2me | Definitions.Def_ClickomaniaNPC_ThreeColor_Grid
-- name    : ClickomaniaNPC_ThreeColor_Grid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T03:26:35.419206+00:00
-- url     : https://prove2.me/theorems/7771063f-416d-47e1-806d-abdd992cc724
-- title:
--   Clickomania grids, edge adjacency and maximal monochromatic groups
-- statement:
--   A board is a finite ordered list of columns of natural-number color labels, read left to right and bottom to top. Columns may have unequal heights during play. A cell has zero-based coordinates (column, height). Its color is defined only when both indices are in range; missing cells have no color. Two coordinates share an edge exactly when one coordinate agrees and the other differs by one. The monochromatic edge relation additionally requires two present cells with the same color.
--
--   A full rectangle of width w, height h and palette size k has exactly w columns, every column has exactly h cells, and every color label is less than k. Labels need not all occur. Zero width, height or palette is permitted when these conditions are satisfied.
--
--   A group G at a selected cell p consists of exactly all cells reachable from p by a finite sequence of monochromatic edges, including the length-zero path, and p must be present. Thus G is the entire maximal monochromatic component, not a chosen connected subset. This definition includes singleton groups; legality of a click is specified separately.
--
--   The definition uses Mathlib's reflexive transitive closure for finite paths. The general finite colored grid is separate from the game's move rules and from computational complexity.
-- source:
--   Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, The Complexity of Clickomania, arXiv:cs/0107031v1 (21 July 2001), section 1, p. 1; section 4, Theorem 15, p. 11. https://arxiv.org/abs/cs/0107031v1

import Mathlib

namespace ClickomaniaNPC.ThreeColor

/-- A finite colored grid stored as columns, left to right, each bottom to top.
Unequal heights are allowed for intermediate positions. -/
abbrev Board := List (List ℕ)

/-- Zero-based column and height coordinates. -/
abbrev Cell := ℕ × ℕ

/-- Missing cells have no color; they never acquire a default color. -/
def colorAt (B : Board) (p : Cell) : Option ℕ :=
  (B[p.1]?).bind fun col => col[p.2]?

def Present (B : Board) (p : Cell) : Prop := ∃ c, colorAt B p = some c

/-- Edge adjacency in the current coordinate system; diagonal contact is excluded. -/
def EdgeAdjacent (p q : Cell) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

/-- The monochromatic edge relation includes only present cells. -/
def MonoEdge (B : Board) (p q : Cell) : Prop :=
  EdgeAdjacent p q ∧ ∃ c, colorAt B p = some c ∧ colorAt B q = some c

/-- A full rectangle of width w and height h, colored from k available labels. -/
def Rectangle (B : Board) (w h k : ℕ) : Prop :=
  B.length = w ∧ ∀ col ∈ B, col.length = h ∧ ∀ c ∈ col, c < k

/-- Every cell in the maximal monochromatic component of the selected cell,
including the selected cell itself via a path of length zero. -/
def IsGroup (B : Board) (p : Cell) (G : Finset Cell) : Prop :=
  Present B p ∧ ∀ q, q ∈ G ↔ Relation.ReflTransGen (MonoEdge B) p q

end ClickomaniaNPC.ThreeColor



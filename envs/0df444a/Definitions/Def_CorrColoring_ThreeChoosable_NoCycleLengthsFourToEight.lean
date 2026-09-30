-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
-- name    : CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:59:14.016994+00:00
-- url     : https://prove2.me/theorems/5f660ae1-710a-42ec-baf3-278615e12ac5
-- title:
--   Graphs without cycles of lengths 4 to 8
-- statement:
--   A graph $G$ has **no cycles of lengths 4 to 8** if every cycle $K$ of $G$ has length
--
--   $$|K| \le 3 \quad\text{or}\quad |K| \ge 9 .$$
--
--   Triangles are allowed, as are cycles of length 9 or more; this is the hypothesis of the main theorem of Dvořák and Postle, and it is not a girth condition.
--
--   **Formalization Note** A cycle is a closed walk `c : G.Walk v v` with `c.IsCycle` (Mathlib), and its length is the number of edges; the condition is $|c| < 4$ or $8 < |c|$.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 3, Theorem 1 (hypothesis 'without cycles of lengths 4 to 8')

import Mathlib

namespace CorrColoring.ThreeChoosable

/-- `G` has no cycle of length 4, 5, 6, 7 or 8. Triangles and cycles of length at least 9
are allowed. -/
def NoCycleLengthsFourToEight {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length < 4 ∨ 8 < c.length

end CorrColoring.ThreeChoosable



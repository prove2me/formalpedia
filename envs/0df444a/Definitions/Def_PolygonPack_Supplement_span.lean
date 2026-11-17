-- Prove2me | Definitions.Def_PolygonPack_Supplement_span
-- name    : PolygonPack_Supplement_span
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:14:31.809017+00:00
-- url     : https://prove2.me/theorems/d6e9845d-a5f9-4495-aebf-83b39c855b1f
-- title:
--   Width and height of a polygon; individual fit by translation; a margin of $\delta$ in one coordinate
-- statement:
--   For a polygon $P$ given as the convex hull of a finite list of rational points, its **width** is the largest minus the smallest $x$-coordinate of its vertices, and its **height** is the same for the $y$-coordinates; these are the coordinate spans of $P$.
--
--   $P$ **fits by translation** if some translate $P+t$, $t\in\mathbb R^2$, lies in the unit square $[0,1]^2$; for a nonempty polygon this means $\mathrm{width}(P)\le1$ and $\mathrm{height}(P)\le1$. For $\delta\in\mathbb R$, $P$ has a **margin $\delta$ in one coordinate** if
--   $$\mathrm{width}(P)\le1-\delta\quad\text{or}\quad\mathrm{height}(P)\le1-\delta .$$
--   The coordinate with the margin may differ from polygon to polygon, and the other span may equal one.
--
--   These are the hypotheses of Theorem H.4 and of the bin-packing part of Theorem 1.3.
--
--   **Formalization Note** Spans are computed over the vertex list, which needs no cyclic order. The empty list has width and height $0$.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. H, p.74 (PDF p.75) (margin; individual feasibility as coordinate spans at most one); Theorem H.4, p.77

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Supplement_TPacks

namespace PolygonPack.Supplement

open PolygonPack

/-- **Width, height, individual fit and margin.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. H, p.74 (PDF p.75): "each polygon has width or height at most 1 − δ. The coordinate in which this margin occurs may differ from polygon to polygon, and the other span may equal one", and "individual feasibility in a unit square means that both coordinate spans are at most one"; Theorem H.4, p.77.

`width v` is the largest minus the smallest x-coordinate of the vertices of `v`, `height v` likewise for the
y-coordinates; both are the coordinate spans of the polygon `hull v`. `FitsT v`: some translate of the polygon
lies in the unit square. `HasMargin δ v`: the width or the height of the polygon is at most `1 − δ`.

**Formalization Note.** Spans are computed over the vertex list, which needs no cyclic order; the span of the
convex hull equals the span of its vertices. For the empty list both are `0` (the empty polygon fits and has
every margin, and constrains nothing). -/
def width (v : List (ℚ × ℚ)) : ℚ := ((v.map Prod.fst).max?.getD 0) - ((v.map Prod.fst).min?.getD 0)

/-- The vertical span of the polygon. -/
def height (v : List (ℚ × ℚ)) : ℚ := ((v.map Prod.snd).max?.getD 0) - ((v.map Prod.snd).min?.getD 0)

/-- Some translate of the polygon lies in the unit square. -/
def FitsT (v : List (ℚ × ℚ)) : Prop := ∃ t : ℝ × ℝ, translate v t ⊆ unitSq

/-- The width or the height of the polygon is at most `1 − δ`. -/
def HasMargin (δ : ℝ) (v : List (ℚ × ℚ)) : Prop := ((width v : ℚ) : ℝ) ≤ 1 - δ ∨ ((height v : ℚ) : ℝ) ≤ 1 - δ

end PolygonPack.Supplement



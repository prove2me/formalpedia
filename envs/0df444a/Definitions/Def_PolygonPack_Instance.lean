-- Prove2me | Definitions.Def_PolygonPack_Instance
-- name    : PolygonPack_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:24.946455+00:00
-- url     : https://prove2.me/theorems/b867e2f0-196b-4a3b-8c8a-116fb40fb96a
-- title:
--   Knapsack instance: polygons as vertex lists with rational profits
-- statement:
--   An **instance** of weighted convex-polygon knapsack is a finite list of pairs $(v,\pi)$, where $v$ is a finite list of points with rational coordinates and $\pi$ is a rational number. The polygon of the pair is the convex hull of the points of $v$ in the plane $\mathbb R^2$, and $\pi$ is its profit.
--
--   This definition fixes how the input of the knapsack problem is presented. It is the object every statement of this mission speaks about.
--
--   **Formalization Note** The vertex list may be in any order and may contain points that are not extreme, since the polygon is its convex hull. Positive area, individual fit and nonnegative profit are the separate predicate `Instance.Valid`.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1 (the input)

import Mathlib

namespace PolygonPack

/-- **Knapsack instance.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1: "The input consists of convex polygons P1, . . . , Pn
with rational vertex coordinates [...] each polygon Pi has a nonnegative rational profit πi".

An instance is a list of pairs (vertex list, profit). `castPt` casts a rational point to `ℝ × ℝ`,
`hull v` is the polygon spanned by a vertex list, and `I.n`, `I.verts i`, `I.prof i` read an instance.

**Formalization Note.** The polygon is the convex hull of its vertex list, so the vertices need not
be in convex position or in cyclic order. This covers the paper's input and is what a machine would
compute first. Positive area, individual fit and nonnegative profit are `Instance.Valid`, not part
of this type. -/
abbrev Instance : Type := List (List (ℚ × ℚ) × ℚ)

/-- A rational point, as a point of the plane. -/
def castPt (z : ℚ × ℚ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

/-- The convex polygon spanned by a vertex list. -/
def hull (v : List (ℚ × ℚ)) : Set (ℝ × ℝ) := convexHull ℝ {p | ∃ z ∈ v, castPt z = p}

/-- The number of polygons. -/
abbrev Instance.n (I : Instance) : ℕ := I.length

/-- The vertex list of polygon `i`. -/
def Instance.verts (I : Instance) (i : Fin I.n) : List (ℚ × ℚ) := (I.get i).1

/-- The profit of polygon `i`. -/
def Instance.prof (I : Instance) (i : Fin I.n) : ℚ := (I.get i).2

/-- A list of polygons as an instance with zero profits (the input of Lemma E.1). -/
def Instance.ofPolys (l : List (List (ℚ × ℚ))) : Instance := l.map (fun v => (v, 0))

end PolygonPack



-- Prove2me | Definitions.Def_DelaunayStretch_face
-- name    : DelaunayStretch_face
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:59.914932+00:00
-- url     : https://prove2.me/theorems/96cbf0ec-96b1-4674-bc23-6c11e49464ff
-- title:
--   Faces $F_T$ of the Delaunay subdivision, their vertices and edges
-- statement:
--   Let $S\subset\mathbb R^2$ be finite and $D$ a Delaunay triangulation of $S$. For a triangle $T\in D$, let $O_T$ be its closed circumdisk; the **face** of $T$ is
--
--   $$
--   F_T=\mathrm{conv}\,(S\cap\partial O_T).
--   $$
--
--   A **vertex** of a face is an extreme point; an **edge** of a face $F$ is a segment $[x,y]$ between two distinct vertices of $F$ that lies on the boundary of $F$; an **edge of $D$** is a side of a triangle of $D$.
--
--   The faces handle cocircular points in the reduction from triangulations to disk chains (Appendix A).
--
--   **Formalization Note** $\partial O_T$ is written as the set of points at distance $r$ from $o$ for some $(o,r)$ with all three vertices of $T$ at distance $r$; for a non-collinear triangle exactly one such pair exists. For a convex polygon with nonempty interior, as every face is, the segments between vertices that lie on the boundary are exactly its sides.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Appendix A, p.48

import Mathlib
import Definitions.Def_DelaunayStretch_IsDelaunayTriangulation

namespace DelaunayStretch

/-- The circumcircle `∂O_T` of a triangle `T` (the set of its three vertices): the circle
`{p : ‖p − o‖ = r}` through the vertices of `T`.

**Formalization Note** Written as `{p | ∃ o r, (∀ q ∈ T, ‖q − o‖ = r) ∧ ‖p − o‖ = r}`; for a
non-collinear triple exactly one `(o, r)` qualifies, so this is that circle. -/
def circumcircle (T : Finset ℂ) : Set ℂ :=
  {p | ∃ (o : ℂ) (r : ℝ), (∀ q ∈ T, dist q o = r) ∧ dist p o = r}

/-- The **face** `F_T` of a triangle `T`: the convex hull of `S ∩ ∂O_T` (Appendix A, p.48).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Appendix A,
p.48. -/
def face (S : Finset ℂ) (T : Finset ℂ) : Set ℂ := convexHull ℝ ((S : Set ℂ) ∩ circumcircle T)

/-- `F` is a face of the Delaunay triangulation `D` of `S`: `F = F_T` for some `T ∈ D`. -/
def IsFace (S : Finset ℂ) (D : Finset (Finset ℂ)) (F : Set ℂ) : Prop := ∃ T ∈ D, F = face S T

/-- `[x, y]` is an **edge of the convex polygon** `F`: `x ≠ y` are vertices (extreme points) of
`F` and the segment `[x, y]` lies on the boundary of `F`.

**Formalization Note** For a convex polygon with nonempty interior, as every face is, the
segments between two vertices that lie on the boundary are exactly the sides, the segments
between cyclically consecutive vertices. -/
def IsFaceEdge (F : Set ℂ) (x y : ℂ) : Prop :=
  x ∈ Set.extremePoints ℝ F ∧ y ∈ Set.extremePoints ℝ F ∧ x ≠ y ∧ segment ℝ x y ⊆ frontier F

/-- `[x, y]` is an **edge of `D`**: a side of a triangle of `D`. -/
def IsEdgeOf (D : Finset (Finset ℂ)) (x y : ℂ) : Prop := x ≠ y ∧ ∃ T ∈ D, x ∈ T ∧ y ∈ T

end DelaunayStretch



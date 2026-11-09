-- Prove2me | Definitions.Def_DelaunayStretch_IsDelaunayTriangulation
-- name    : DelaunayStretch_IsDelaunayTriangulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:21.660385+00:00
-- url     : https://prove2.me/theorems/95b7f5bb-39e5-4533-9d03-5174b951dd58
-- title:
--   Delaunay triangulations of a finite planar point set (formal definition)
-- statement:
--   Let $S\subset\mathbb R^2$ be finite. A **Delaunay triangulation** of $S$ is a set $D$ of triangles with vertices in $S$ such that
--
--   1. the triangles cover the convex hull of $S$;
--   2. every point of $S$ is a vertex of some triangle;
--   3. any two triangles are disjoint, or meet in a common vertex, or meet in a common edge;
--   4. the open circumdisk of every triangle contains no point of $S$.
--
--   This is the object of the main theorem. Points of $S$ on a circumcircle are allowed, and no general-position assumption is made.
--
--   **Formalization Note** The plane is $\mathbb C$. A triangle is the set $T$ of its three vertices, with $T$ not collinear (equivalently, affinely independent); the closed triangle is $\mathrm{conv}\,T$. Condition 3 is $\mathrm{conv}\,T\cap\mathrm{conv}\,T'=\mathrm{conv}(T\cap T')$ for $T\ne T'$, which, since $|T\cap T'|\in\{0,1,2\}$, is exactly "disjoint, a common vertex, or a common edge". Condition 4 is: there are $o$ and $r$ with $\|p-o\|=r$ for the three vertices $p$ and $r\le\|q-o\|$ for all $q\in S$; the circle through three non-collinear points is unique.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Appendix A, formal definition, p.48 (informal version §1, p.3)

import Mathlib

namespace DelaunayStretch

/-- **Delaunay triangulation** (Appendix A, formal definition, p.48). For a finite set
`S ⊂ ℝ²`, a Delaunay triangulation of `S` is a set `D` of triangles with vertices in `S` that
cover the convex hull of `S`, such that every point of `S` is a vertex of some triangle, any two
triangles are disjoint or meet in a common vertex or a common edge, and the open circumdisk of
every triangle contains no point of `S`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Appendix A,
p.48 (informal version: §1, p.3).

**Formalization Note** The plane is `ℂ`. A triangle is the `Finset` `T` of its three vertices,
not collinear (`T.card = 3` and `¬ Collinear ℝ T`, i.e. affinely independent); the closed
triangle is `convexHull ℝ T`. "Disjoint, or meet in a common vertex or a common edge" is
`conv T ∩ conv T′ = conv (T ∩ T′)` for `T ≠ T′`: with `|T ∩ T′| ∈ {0, 1, 2}` this is exactly
the three cases (and conversely each case forces this equality). The circumcircle of `T` is a
circle `{p : ‖p − o‖ = r}` through the three vertices (unique for a non-collinear triple,
`EuclideanGeometry.Sphere`/`AffineIndependent.existsUnique_dist_eq`); "its open disk contains
no point of `S`" is `r ≤ ‖q − o‖` for all `q ∈ S`, so points of `S` on the circle are allowed.
No general-position assumption is made. -/
def IsDelaunayTriangulation (S : Finset ℂ) (D : Finset (Finset ℂ)) : Prop :=
  (∀ T ∈ D, T.card = 3 ∧ ¬ Collinear ℝ (T : Set ℂ) ∧ T ⊆ S) ∧
  (⋃ T ∈ D, convexHull ℝ (T : Set ℂ)) = convexHull ℝ (S : Set ℂ) ∧
  (∀ p ∈ S, ∃ T ∈ D, p ∈ T) ∧
  (∀ T ∈ D, ∀ T' ∈ D, T ≠ T' →
    convexHull ℝ (T : Set ℂ) ∩ convexHull ℝ (T' : Set ℂ) = convexHull ℝ ((T : Set ℂ) ∩ T')) ∧
  (∀ T ∈ D, ∃ (o : ℂ) (r : ℝ), (∀ p ∈ T, dist p o = r) ∧ ∀ q ∈ S, r ≤ dist q o)

end DelaunayStretch



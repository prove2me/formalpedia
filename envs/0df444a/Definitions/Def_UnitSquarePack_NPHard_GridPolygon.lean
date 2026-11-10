-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_GridPolygon
-- name    : UnitSquarePack_NPHard_GridPolygon
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:18:15.897231+00:00
-- url     : https://prove2.me/theorems/613492cd-3c0b-4659-9c5b-176e611ffa06
-- title:
--   Grid polygons given by their integer vertices, their closed region, and orthogonal convexity
-- statement:
--   A **grid polygon** is given by a list of integer points $v_0, v_1, \dots, v_{N-1} \in \mathbb Z^2$, its vertices. Its **edges** are the closed segments $[v_i, v_{i+1}]$ for $0 \le i < N$, indices taken modulo $N$ (so the last edge joins $v_{N-1}$ back to $v_0$); their union is the **boundary curve** $\partial P$. The list is a grid polygon when
--
--   - $N \ge 3$;
--   - every edge is a nondegenerate horizontal or vertical segment: $v_i \ne v_{i+1}$ and $v_i, v_{i+1}$ share their $x$- or their $y$-coordinate;
--   - the closed chain is simple: consecutive edges $[v_i, v_{i+1}]$ and $[v_{i+1}, v_{i+2}]$ meet exactly in $\{v_{i+1}\}$, and non-consecutive edges are disjoint.
--
--   The **closed region** $P$ of the chain is the boundary curve together with every bounded connected component of its complement:
--   $$P \;=\; \partial P \,\cup\, \{\,p \notin \partial P : \text{the connected component of } \mathbb R^2 \setminus \partial P \text{ containing } p \text{ is bounded}\,\}.$$
--   For a grid polygon, $\partial P$ is a simple closed curve, so $P$ is the curve together with its interior: the polygon as a closed set.
--
--   A set $P \subseteq \mathbb R^2$ is **orthogonally convex** if, for every horizontal line and every vertical line $\ell$, the intersection $P \cap \ell$ is connected; the empty intersection counts as connected.
--
--   The packing problem of the paper takes a grid polygon as input, and its main result is about grid polygons whose closed region is orthogonally convex. An orthogonally convex polygon is necessarily simple.
--
--   **Formalization Note.** Points are `ℝ × ℝ`; `toPlane` casts an integer point to the plane. `vertex vs i` is $v_{i \bmod N}$. Connectedness is `IsPreconnected` (the empty set is preconnected). Collinear consecutive edges are allowed, as a vertex list may contain a straight-angle vertex.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 1, §1 (grid polygons, orthogonal convexity)

import Mathlib

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Set

/-- An integer point `(a, b) ∈ ℤ²`, viewed as a point of the real plane `ℝ²`. -/
def toPlane (v : ℤ × ℤ) : ℝ × ℝ := ((v.1 : ℝ), (v.2 : ℝ))

/-- The `i`-th vertex `v_{i mod N}` of the closed chain `v_0 v_1 … v_{N-1} v_0` given by the
vertex list `vs` (`N = vs.length`; indices are taken modulo `N`). -/
def vertex (vs : List (ℤ × ℤ)) (i : ℕ) : ℤ × ℤ := vs.getD (i % vs.length) (0, 0)

/-- The `i`-th edge of the closed chain: the closed segment from `v_i` to `v_{i+1}` (indices
modulo `N`, so edge `N - 1` joins `v_{N-1}` back to `v_0`). -/
def edge (vs : List (ℤ × ℤ)) (i : ℕ) : Set (ℝ × ℝ) :=
  segment ℝ (toPlane (vertex vs i)) (toPlane (vertex vs (i + 1)))

/-- The boundary curve: the union of the `N` edges of the closed chain. -/
def boundary (vs : List (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  ⋃ i ∈ Finset.range vs.length, edge vs i

/-- `vs` is a *grid polygon*: the closed chain `v_0 v_1 … v_{N-1} v_0` through the integer
points `vs` has at least three vertices, every edge is a nondegenerate horizontal or vertical
segment, and the chain is simple: consecutive edges meet only in their common vertex and
non-consecutive edges are disjoint. -/
def IsGridPolygon (vs : List (ℤ × ℤ)) : Prop :=
  3 ≤ vs.length ∧
  (∀ i < vs.length, vertex vs i ≠ vertex vs (i + 1) ∧
      ((vertex vs i).1 = (vertex vs (i + 1)).1 ∨ (vertex vs i).2 = (vertex vs (i + 1)).2)) ∧
  (∀ i < vs.length, edge vs i ∩ edge vs (i + 1) = {toPlane (vertex vs (i + 1))}) ∧
  (∀ i < vs.length, ∀ j < vs.length, i ≠ j → j ≠ (i + 1) % vs.length →
      i ≠ (j + 1) % vs.length → Disjoint (edge vs i) (edge vs j))

/-- The closed region bounded by the chain: the boundary curve together with every bounded
connected component of its complement. For a grid polygon (a simple closed curve) this is the
curve together with its interior, i.e. the closed polygon `P`. -/
def region (vs : List (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  boundary vs ∪
    {p | p ∉ boundary vs ∧ Bornology.IsBounded (connectedComponentIn (boundary vs)ᶜ p)}

/-- A set `P ⊆ ℝ²` is *orthogonally convex* if its intersection with every horizontal line and
with every vertical line is connected (the empty set counts as connected). -/
def IsOrthogonallyConvex (P : Set (ℝ × ℝ)) : Prop :=
  (∀ c : ℝ, IsPreconnected (P ∩ {p : ℝ × ℝ | p.2 = c})) ∧
  (∀ c : ℝ, IsPreconnected (P ∩ {p : ℝ × ℝ | p.1 = c}))

end UnitSquarePack.NPHard



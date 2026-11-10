-- Prove2me | Definitions.Def_StackingStars_Main_StarPolygon
-- name    : StackingStars_Main_StarPolygon
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:42:59.797635+00:00
-- url     : https://prove2.me/theorems/f1708daa-e491-47f3-9bcb-50f7598d51e3
-- title:
--   Simple polygons given by real vertex lists, their closed regions, kernels, and star-shapedness
-- statement:
--   A polygon is given by its vertex list $V=[v_0,\dots,v_{m-1}]$ of points of $\mathbb R^2$ with real coordinates and any number $m\ge3$ of vertices; its edges are the segments $v_iv_{i+1}$, indices modulo $m$.
--
--   * `IsSimple V`: $m\ge3$, consecutive vertices are distinct, and two distinct edges meet only in their common vertex when they are consecutive, and not at all otherwise. So the boundary is a simple closed polygonal chain.
--   * `boundary V` is the union of the edges, and `region V` is the closed region of the polygon: the boundary together with every point off it whose connected component in the complement of the boundary is bounded (the bounded face of the polygonal Jordan curve theorem).
--   * `kernel S` $=\{q\in S:\ qp\subseteq S\text{ for every }p\in S\}$, the points of $S$ that see all of $S$.
--   * `IsStarPolygon V`: $V$ is simple and the kernel of its region is nonempty. This is a star (star-shaped polygon).
--   * `IsConvexPolygon V`: $V$ is simple and its region is convex. These are the inputs of Theorem 5.
--
--   **Formalization Note.** The inputs are simple polygons, so every star has a nonempty connected interior. The zero-area "plus" and "L" shapes of §2 are illustrations, not inputs. No convexity, rationality, general position or bound on the number of vertices is imposed.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2, §1 (star-shaped polygon, kernel)

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry

namespace StackingStars.Main

/-!
# Simple polygons, their closed regions, and star-shapedness

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2
(PDF 4): "a polygon P is said to be star-shaped if there is a point q ∈ P that sees all of P, i.e.,
for every point p ∈ P, we have qp ⊆ P. The set of points for which this holds is called the kernel
of P."

A polygon is given by its vertex list `V = [v₀, …, v_{m−1}]` (real coordinates, any `m ≥ 3`); its
edges are the segments `v_i v_{i+1}` (indices mod `m`). It is *simple* when consecutive vertices
differ and two distinct edges meet only in the vertex they share when they are consecutive, and
not at all otherwise. Its closed region is the boundary together with every point off the boundary
whose connected component in the complement of the boundary is bounded (the bounded face, by the
polygonal Jordan curve theorem). A star polygon is a simple polygon whose closed region has a
nonempty kernel.
-/

/-- Vertex `i` of `V`, indices taken modulo the number of vertices. -/
noncomputable def vtx (V : List Pt) (i : ℕ) : Pt := V.getD (i % V.length) 0

/-- Edge `i` of `V`: the segment from vertex `i` to vertex `i + 1` (mod `m`). -/
def edge (V : List Pt) (i : ℕ) : Set Pt := segment ℝ (vtx V i) (vtx V (i + 1))

/-- The boundary: the union of the `m` edges. -/
def boundary (V : List Pt) : Set Pt := ⋃ i ∈ Finset.range V.length, edge V i

/-- `V` is a simple polygon: at least three vertices, consecutive vertices distinct, and two
distinct edges `i ≠ j` meet only in their shared vertex when consecutive (`j = i + 1` or
`i = j + 1` mod `m`), and not at all otherwise. -/
def IsSimple (V : List Pt) : Prop :=
  3 ≤ V.length ∧ (∀ i < V.length, vtx V i ≠ vtx V (i + 1)) ∧
    ∀ i < V.length, ∀ j < V.length, i ≠ j → ∀ z ∈ edge V i ∩ edge V j,
      (j = (i + 1) % V.length ∧ z = vtx V j) ∨ (i = (j + 1) % V.length ∧ z = vtx V i)

/-- The closed region of the polygon: the boundary and the points off it whose connected
component in the complement of the boundary is bounded. -/
def region (V : List Pt) : Set Pt :=
  boundary V ∪ {z | z ∉ boundary V ∧ Bornology.IsBounded (connectedComponentIn (boundary V)ᶜ z)}

/-- The kernel of a set `S`: the points `q ∈ S` such that `qp ⊆ S` for every `p ∈ S`. -/
def kernel (S : Set Pt) : Set Pt := {q | q ∈ S ∧ ∀ p ∈ S, segment ℝ q p ⊆ S}

/-- A star (star-shaped polygon): a simple polygon whose closed region has a nonempty kernel. -/
def IsStarPolygon (V : List Pt) : Prop := IsSimple V ∧ (kernel (region V)).Nonempty

/-- A convex polygon: a simple polygon whose closed region is convex. -/
def IsConvexPolygon (V : List Pt) : Prop := IsSimple V ∧ Convex ℝ (region V)

end StackingStars.Main



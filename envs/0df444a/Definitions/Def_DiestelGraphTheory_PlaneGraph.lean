-- Prove2me | Definitions.Def_DiestelGraphTheory_PlaneGraph
-- name    : DiestelGraphTheory_PlaneGraph
-- status  : Definition
-- author  : @tiago duque marques
-- created : 2026-11-18T11:33:19.798014+00:00
-- url     : https://prove2.me/theorems/637fdb73-ccd8-44b1-b29d-f720074fed27
-- title:
--   Plane graphs, faces, triangulations and planar graphs (Diestel §4.2, §4.4)
-- statement:
--   Plane and planar graphs, following Diestel, Sections 4.2 and 4.4. Arcs, polygons and regions are as in `DiestelGraphTheory_PolygonalArc`.
--
--   A **plane graph** is a pair $G=(V,E)$ of finite sets such that
--
--   1. $V\subseteq\mathbb R^2$;
--   2. every edge $e\in E$ is an arc between two vertices;
--   3. different edges have different sets of endpoints;
--   4. the interior $\mathring e$ of an edge (the arc minus its endpoints) contains no vertex and no point of any other edge.
--
--   Two vertices $x\ne y$ are **adjacent** if some edge is an arc between them; this defines the abstract graph of $G$. Writing $G$ also for the point set $V\cup\bigcup E$, the **faces** of $G$ are the regions of $\mathbb R^2\setminus G$.
--
--   A face $f$ is **bounded by a triangle** if there are vertices $a,b,c$ and edges $e_{ab},e_{bc},e_{ca}$ of $G$, arcs between $a,b$, between $b,c$ and between $c,a$, whose union is exactly the frontier of $f$. $G$ is a **plane triangulation** if every face (including the outer face) is bounded by a triangle.
--
--   An abstract graph is **planar** if it is isomorphic to the abstract graph of some plane graph.
--
--   These are the objects of Euler's formula and of the Four and Five Colour Theorems.
--
--   **Formalization Note** The abstract graph is built with `SimpleGraph.fromRel` on the vertex set; $|V|$, $|E|$ and the number of faces are measured with `Nat.card`.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Section 4.2, p. 96 (plane graph, faces), p. 100 (plane triangulation); Section 4.4, p. 106 (planar).

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc

/-!
Plane graphs, their faces, plane triangulations, and planar graphs, following
R. Diestel, *Graph Theory*, 6th ed. (Springer GTM 173, 2025), Sections 4.2 and 4.4.
-/

namespace DiestelGraphTheory

open Set

/-- The *endpoints* of an arc `e`: the points `z` such that `e` is an arc between
`z` and some point, or between some point and `z`. -/
def arcEnds (e : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | ∃ w : ℝ × ℝ, IsArcBetween e z w ∨ IsArcBetween e w z}

/-- The *interior* `e̊ = e \ {x, y}` of an arc `e` between `x` and `y`. -/
def arcInterior (e : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := e \ arcEnds e

/-- A *plane graph* `(V, E)` (Diestel, §4.2): finite sets `V ⊆ ℝ²` of vertices and
`E` of edges such that
1. every edge is an arc between two vertices;
2. different edges have different sets of endpoints;
3. the interior of an edge contains no vertex and no point of any other edge. -/
structure PlaneGraph where
  /-- The vertices: points of the plane. -/
  V : Set (ℝ × ℝ)
  /-- The edges: subsets of the plane. -/
  E : Set (Set (ℝ × ℝ))
  V_finite : V.Finite
  E_finite : E.Finite
  edge_isArc : ∀ e ∈ E, ∃ x ∈ V, ∃ y ∈ V, IsArcBetween e x y
  ends_injective : ∀ e ∈ E, ∀ e' ∈ E, arcEnds e = arcEnds e' → e = e'
  interior_disjoint_vertices : ∀ e ∈ E, Disjoint (arcInterior e) V
  interior_disjoint_edges : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (arcInterior e) e'

namespace PlaneGraph

/-- The point set `V ∪ ⋃ E` of a plane graph. -/
def pointSet (H : PlaneGraph) : Set (ℝ × ℝ) := H.V ∪ ⋃₀ H.E

/-- The abstract graph defined by a plane graph: two distinct vertices `x, y` are
adjacent iff some edge is an arc between them. -/
def toSimpleGraph (H : PlaneGraph) : SimpleGraph H.V :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ H.E, IsArcBetween e (x : ℝ × ℝ) (y : ℝ × ℝ)

/-- The *faces* of a plane graph `G`: the regions of `ℝ² \ G` (Diestel, §4.2). -/
def faces (H : PlaneGraph) : Set (Set (ℝ × ℝ)) := regions (H.pointSet)ᶜ

/-- A face `f` is *bounded by a triangle* of `H`: there are three vertices `a, b, c`
and edges `e_ab, e_bc, e_ca` of `H` (arcs between `a,b`, `b,c`, `c,a`) whose union
is exactly the frontier of `f`. -/
def IsBoundedByTriangle (H : PlaneGraph) (f : Set (ℝ × ℝ)) : Prop :=
  ∃ a ∈ H.V, ∃ b ∈ H.V, ∃ c ∈ H.V,
    ∃ eab ∈ H.E, ∃ ebc ∈ H.E, ∃ eca ∈ H.E,
      IsArcBetween eab a b ∧ IsArcBetween ebc b c ∧ IsArcBetween eca c a ∧
      frontier f = eab ∪ ebc ∪ eca

/-- A *plane triangulation*: every face (including the outer face) is bounded by a
triangle (Diestel, §4.2). -/
def IsTriangulation (H : PlaneGraph) : Prop :=
  ∀ f ∈ H.faces, H.IsBoundedByTriangle f

end PlaneGraph

/-- A graph is *planar* if it is isomorphic to (the abstract graph of) a plane graph
(Diestel, §4.4). -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : PlaneGraph, Nonempty (G ≃g H.toSimpleGraph)

end DiestelGraphTheory



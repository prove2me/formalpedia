-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing
-- name    : CorrColoring_ThreeChoosable_StraightLineDrawing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:59:57.785637+00:00
-- url     : https://prove2.me/theorems/c1aca3dc-24c7-455a-ab36-46d2725c0586
-- title:
--   Straight-line plane drawings, planarity, faces and face incidence
-- statement:
--   A **straight-line plane drawing** $D$ of a simple graph $G$ assigns to each vertex $v$ a point $p(v) \in \mathbb{R}^2$ such that
--
--   1. distinct vertices get distinct points;
--   2. for every edge $ab$ and every vertex $v \notin \{a, b\}$, the point $p(v)$ does not lie on the closed segment $[p(a), p(b)]$;
--   3. for any two edges $ab$ and $cd$ with no common end, the segments $[p(a), p(b)]$ and $[p(c), p(d)]$ are disjoint.
--
--   A graph is **planar** if it has such a drawing. For a drawing $D$, let $|D| \subseteq \mathbb{R}^2$ be the union of all vertex points and all edge segments. A **face** of $D$ is a connected component of $\mathbb{R}^2 \setminus |D|$; a vertex $v$ is **incident** with a face $f$ if
--
--   $$p(v) \in \overline{f},$$
--
--   the closure of $f$. The **outer face** is the unbounded face, and a vertex is incident with the outer face if it is incident with an unbounded face.
--
--   These are the notions of plane graph and planar graph used in Theorems 1, 6 and 8 of Dvořák and Postle.
--
--   **Formalization Note** The paper does not define planarity; it uses the standard notion. For finite simple graphs, having a straight-line drawing is equivalent to planarity by Fáry's theorem, and every plane embedding can be replaced by a straight-line one with the same faces, so the straight-line model covers exactly the planar graphs. The drawing clauses are identical to those of the platform's `OPG401.IsPlanar`, restated here with Mathlib's `segment ℝ`. The plane is `ℝ × ℝ` with its product topology and bornology (the same connected components and bounded sets as the Euclidean plane).
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 3 Theorem 1 ('planar graph'), p. 11 Theorem 8 ('plane graph', 'vertices incident with a face', 'outer face'); standard notions, not defined in the paper

import Mathlib

namespace CorrColoring.ThreeChoosable

/-- A straight-line plane drawing of a simple graph `G`: vertices go to distinct points of
`ℝ × ℝ`, every edge `ab` is drawn as the closed segment from `pos a` to `pos b`, no vertex other
than `a, b` lies on that segment, and the segments of two edges with no common end are
disjoint. (Same clauses as `OPG401.IsPlanar`.) -/
structure StraightLineDrawing {V : Type*} (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pos : V → ℝ × ℝ
  inj : Function.Injective pos
  avoid : ∀ ⦃a b v : V⦄, G.Adj a b → v ≠ a → v ≠ b → pos v ∉ segment ℝ (pos a) (pos b)
  disjoint : ∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    Disjoint (segment ℝ (pos a) (pos b)) (segment ℝ (pos c) (pos d))

/-- `G` is planar: it has a straight-line plane drawing (equivalent to planarity for finite
simple graphs by Fáry's theorem). -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (StraightLineDrawing G)

namespace StraightLineDrawing

variable {V : Type*} {G : SimpleGraph V}

/-- The point set of the drawing: all vertex points and all edge segments. -/
def image (D : StraightLineDrawing G) : Set (ℝ × ℝ) :=
  Set.range D.pos ∪ ⋃ (a : V) (b : V) (_ : G.Adj a b), segment ℝ (D.pos a) (D.pos b)

/-- A face of the drawing: a connected component of the complement of its point set. -/
def IsFace (D : StraightLineDrawing G) (f : Set (ℝ × ℝ)) : Prop :=
  ∃ x, x ∉ D.image ∧ f = connectedComponentIn D.imageᶜ x

/-- Vertex `v` is incident with the region `f` when its point lies in the closure of `f`. -/
def IsIncident (D : StraightLineDrawing G) (v : V) (f : Set (ℝ × ℝ)) : Prop :=
  D.pos v ∈ closure f

/-- The outer face: the (unique, for a finite graph) unbounded face. -/
def IsOuterFace (D : StraightLineDrawing G) (f : Set (ℝ × ℝ)) : Prop :=
  D.IsFace f ∧ ¬ Bornology.IsBounded f

/-- Vertex `v` is incident with the outer face. -/
def IncidentOuter (D : StraightLineDrawing G) (v : V) : Prop :=
  ∃ f, D.IsOuterFace f ∧ D.IsIncident v f

end StraightLineDrawing

end CorrColoring.ThreeChoosable



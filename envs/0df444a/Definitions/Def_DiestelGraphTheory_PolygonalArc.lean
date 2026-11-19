-- Prove2me | Definitions.Def_DiestelGraphTheory_PolygonalArc
-- name    : DiestelGraphTheory_PolygonalArc
-- status  : Definition
-- author  : @tiago duque marques
-- created : 2026-11-18T11:32:44.994541+00:00
-- url     : https://prove2.me/theorems/ca0e53a7-c085-4f09-87ff-1c5cb2c5b25b
-- title:
--   Polygonal arcs, polygons and regions in $\mathbb R^2$ (Diestel §4.1)
-- statement:
--   Topological prerequisites for plane graphs, following Diestel, Section 4.1. The plane $\mathbb R^2$ carries its Euclidean topology, and every subset carries the subspace topology.
--
--   1. A **straight line segment** is a set $\{p+\lambda(q-p) : 0\le\lambda\le1\}$ for two distinct points $p\ne q$ of $\mathbb R^2$.
--   2. A **polygon** is a subset of $\mathbb R^2$ that is the union of finitely many straight line segments and is homeomorphic to the unit circle $S^1=\{z\in\mathbb R^2 : z_1^2+z_2^2=1\}$.
--   3. A **(polygonal) arc between $x$ and $y$** is a subset $P\subseteq\mathbb R^2$ that is the union of finitely many straight line segments and admits a homeomorphism $\varphi:[0,1]\to P$ with $\varphi(0)=x$ and $\varphi(1)=y$; the points $x,y$ are its endpoints.
--   4. For $O\subseteq\mathbb R^2$, two points $a,b$ are **linked by an arc in $O$** if $a=b$ or some arc between $a$ and $b$ is contained in $O$.
--   5. The **regions** of $O$ are the classes $\{b\in O : b \text{ linked to } a \text{ in } O\}$ for $a\in O$. For open $O$ (the only case used) these are the equivalence classes of the linking relation.
--
--   These notions underlie the definition of plane graphs and their faces, and the Jordan Curve Theorem for polygons.
--
--   **Formalization Note** $\mathbb R^2$ is `ℝ × ℝ`, whose product topology is the Euclidean one; because Mathlib's metric on `ℝ × ℝ` is the sup metric, the unit circle is written by its Euclidean equation. A homeomorphism $[0,1]\cong P$ is encoded as a topological embedding of `unitInterval` with range $P$.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Section 4.1, p. 94 (definitions of straight line segment, polygon, polygonal arc, regions).

import Mathlib

/-!
Topological prerequisites for plane graphs, following
R. Diestel, *Graph Theory*, 6th ed. (Springer GTM 173, 2025), Section 4.1.

The Euclidean plane `ℝ²` is modelled as `ℝ × ℝ` with its product topology
(which is the Euclidean topology). Every subset carries the subspace topology.
-/

namespace DiestelGraphTheory

open Set

/-- A *straight line segment*: a set of the form `{p + λ (q - p) | 0 ≤ λ ≤ 1}`
for two distinct points `p ≠ q` of the plane (Diestel, §4.1). -/
def IsStraightSegment (S : Set (ℝ × ℝ)) : Prop :=
  ∃ p q : ℝ × ℝ, p ≠ q ∧
    S = {z : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = p + t • (q - p)}

/-- `P` is the union of finitely many straight line segments. -/
def IsFiniteUnionOfSegments (P : Set (ℝ × ℝ)) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Set (ℝ × ℝ)), (∀ i, IsStraightSegment (S i)) ∧ P = ⋃ i, S i

/-- The unit circle `S¹ = {z ∈ ℝ² | ‖z‖₂ = 1}` (Euclidean norm, not the sup norm
that `ℝ × ℝ` carries in Mathlib). -/
def unitCircle : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = 1}

/-- A *polygon*: a finite union of straight line segments homeomorphic to the
unit circle `S¹` (Diestel, §4.1). -/
def IsPolygon (P : Set (ℝ × ℝ)) : Prop :=
  IsFiniteUnionOfSegments P ∧ Nonempty (P ≃ₜ unitCircle)

/-- `P` is a *(polygonal) arc between `x` and `y`*: a finite union of straight line
segments that is homeomorphic to `[0,1]` via a homeomorphism sending `0 ↦ x` and
`1 ↦ y` (Diestel, §4.1). A topological embedding `[0,1] → ℝ²` with range `P` is
exactly a homeomorphism `[0,1] ≅ P`. -/
def IsArcBetween (P : Set (ℝ × ℝ)) (x y : ℝ × ℝ) : Prop :=
  IsFiniteUnionOfSegments P ∧
    ∃ φ : unitInterval → ℝ × ℝ,
      Topology.IsEmbedding φ ∧ range φ = P ∧ φ 0 = x ∧ φ 1 = y

/-- Two points `a, b` of an open set `O` are *linked by an arc in `O`*: they are
equal, or some arc between `a` and `b` lies inside `O` (Diestel, §4.1). -/
def LinkedIn (O : Set (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  a = b ∨ ∃ P : Set (ℝ × ℝ), IsArcBetween P a b ∧ P ⊆ O

/-- The *regions* of `O ⊆ ℝ²`: the equivalence classes of points of `O` under
"being linked by an arc in `O`" (Diestel, §4.1). -/
def regions (O : Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {R | ∃ a ∈ O, R = {b : ℝ × ℝ | b ∈ O ∧ LinkedIn O a b}}

end DiestelGraphTheory



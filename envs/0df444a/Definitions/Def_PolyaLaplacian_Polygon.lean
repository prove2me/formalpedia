-- Prove2me | Definitions.Def_PolyaLaplacian_Polygon
-- name    : PolyaLaplacian_Polygon
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-17T02:25:23.513858+00:00
-- url     : https://prove2.me/theorems/74f84906-f2c9-4745-b2f2-546f3156ce49
-- title:
--   Rational polygonal domains with holes
-- statement:
--   This file defines the class of **rational polygonal domains** that the counterexample is required to belong to.
--
--   A polygon is given by a list of vertices in $\mathbb Q^2$, embedded into the real plane. The predicate `IsSimplePolygon` requires at least three distinct vertices, that consecutive edges meet exactly at their shared vertex, and that non-adjacent edges are disjoint — i.e. the boundary is a simple closed polygonal curve. The **interior** of a polygon is the union of the bounded connected components of the complement of its boundary curve (for a simple polygon, the bounded Jordan interior); the **closed polygon** is the interior together with the boundary.
--
--   A `RationalPolygonalDomain` bundles an outer simple polygon and a list of polygonal **holes**, together with the conditions that every hole is simple, that each closed hole lies strictly inside the outer polygon's interior, and that the holes are pairwise disjoint. Its underlying open set is the outer interior minus the closed holes, so the domain may be multiply connected.
--
--   **Formalization Note.** Vertices are exact rationals; edges are real segments between the embedded vertices. The interior is defined via connected components rather than a ray-crossing parity, so no Jordan-curve theorem is needed to state the definition (its properties are proved by solvers).
-- source:
--   https://epoch.ai/frontiermath/open-problems/polya-laplacian-spectrum (Task: bounded polygonal domain with rational vertices, outer simple polygon with polygonal holes).

import Mathlib

noncomputable section

namespace PolyaLaplacian

open Set TopologicalSpace

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Embed a rational point into the plane. -/
def ratPoint (p : ℚ × ℚ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![↑p.1, ↑p.2]

/-- Auxiliary: the `i`-th element of a list of rational points, or `(0,0)` if out of range. -/
def vertexAux : List (ℚ × ℚ) → ℕ → ℚ × ℚ
  | [], _ => (0, 0)
  | a :: _, 0 => a
  | _ :: as, i + 1 => vertexAux as i

/-- The `i`-th vertex of a polygon, cyclically indexed; returns `(0,0)` out of range. -/
def vertexAt (verts : List (ℚ × ℚ)) (i : ℕ) : ℚ × ℚ :=
  vertexAux verts (i % verts.length)

/-- The `i`-th closed edge of a polygon, as a set of real points. -/
def edge (verts : List (ℚ × ℚ)) (i : ℕ) : Set Plane :=
  segment ℝ (ratPoint (vertexAt verts i)) (ratPoint (vertexAt verts (i + 1)))

/-- A list of rational vertices forms a simple polygon: at least three distinct vertices,
consecutive edges meet exactly at their shared vertex, and non-adjacent edges are disjoint. -/
def IsSimplePolygon (verts : List (ℚ × ℚ)) : Prop :=
  3 ≤ verts.length ∧ verts.Nodup ∧
  (∀ i ∈ Finset.range verts.length,
    edge verts i ∩ edge verts ((i + 1) % verts.length) = {ratPoint (vertexAt verts (i + 1))}) ∧
  (∀ i ∈ Finset.range verts.length, ∀ j ∈ Finset.range verts.length,
    i ≠ j → (i + 1) % verts.length ≠ j → (j + 1) % verts.length ≠ i →
    Disjoint (edge verts i) (edge verts j))

/-- The polygonal curve: the union of the edges. -/
def polygonCurve (verts : List (ℚ × ℚ)) : Set Plane :=
  ⋃ i ∈ Finset.range verts.length, edge verts i

/-- The interior of a polygon: the union of the bounded connected components of the complement of
its polygonal curve. For a simple polygon this is the bounded Jordan interior. -/
def polygonInterior (verts : List (ℚ × ℚ)) : Set Plane :=
  ⋃₀ {C : Set Plane | Bornology.IsBounded C ∧
    ∃ x : Plane, C = connectedComponentIn (polygonCurve verts)ᶜ x}

/-- The closed polygon: its interior together with its boundary curve. -/
def polygonClosure (verts : List (ℚ × ℚ)) : Set Plane :=
  polygonInterior verts ∪ polygonCurve verts

/-- A bounded polygonal domain with rational vertices: an outer simple polygon with zero or more
polygonal holes removed. Each hole is simple, lies strictly inside the outer polygon, and the holes
are pairwise disjoint. -/
structure RationalPolygonalDomain where
  outer : List (ℚ × ℚ)
  holes : List (List (ℚ × ℚ))
  outer_simple : IsSimplePolygon outer
  holes_simple : ∀ h ∈ holes, IsSimplePolygon h
  holes_inside : ∀ h ∈ holes, polygonClosure h ⊆ polygonInterior outer
  holes_disjoint : ∀ h₁ ∈ holes, ∀ h₂ ∈ holes, h₁ ≠ h₂ →
    Disjoint (polygonClosure h₁) (polygonClosure h₂)

/-- The open domain: the outer polygon's interior minus the closed holes. -/
def RationalPolygonalDomain.toSet (P : RationalPolygonalDomain) : Set Plane :=
  polygonInterior P.outer \ ⋃ h ∈ P.holes, polygonClosure h

end PolyaLaplacian



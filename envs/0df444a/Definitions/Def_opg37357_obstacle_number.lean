-- Prove2me | Definitions.Def_opg37357_obstacle_number
-- name    : opg37357_obstacle_number
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-08T05:05:55.801581+00:00
-- url     : https://prove2.me/theorems/ce91eb01-bc59-4db7-a2b8-9cca50516afa
-- title:
--   Polygonal obstacle drawings and ordinary obstacle number
-- statement:
--   This module defines an ordinary obstacle drawing of a finite simple graph. Vertices are placed injectively in $\mathbb R^2$. Each obstacle is a closed connected polygonal region represented by a nonempty finite union of filled closed triangles; distinct obstacle regions are disjoint and contain no graph vertex.
--
--   Two distinct vertices are adjacent exactly when their closed joining segment is disjoint from every obstacle. `ObstacleNumberAtMost G k` means that such a drawing exists with $k$ indexed obstacles. Straight-line planarity of the abstract graph is defined independently and does not require the obstacle drawing itself to be crossing-free.
--
--   Segment contact with an obstacle boundary counts as blocked visibility. Degenerate triangle pieces are not excluded, while the whole obstacle region must be preconnected.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-37357, https://www.unsolvedmath.com/problems/OPG-37357; conventions compared with Gimbel--Ossona de Mendez--Valtr, arXiv:1706.06992v3, Section 1

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Constructions.SumProd

namespace OPG37357

universe u

abbrev Point := ℝ × ℝ

def affine2 (a b : Point) (t : ℝ) : Point :=
  ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)

def closedSegment (a b : Point) : Set Point :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = affine2 a b t}

def closedTriangle (a b c : Point) : Set Point :=
  {x | ∃ α β γ : ℝ,
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    x = (α * a.1 + β * b.1 + γ * c.1,
         α * a.2 + β * b.2 + γ * c.2)}

/-- A closed connected polygonal obstacle, represented by a nonempty finite
union of filled closed triangles. -/
structure PolygonalObstacle where
  pieces : List (Point × Point × Point)
  pieces_nonempty : pieces ≠ []
  region_connected : IsPreconnected
    {x | ∃ t ∈ pieces, x ∈ closedTriangle t.1 t.2.1 t.2.2}

/-- The closed region occupied by a polygonal obstacle. -/
def PolygonalObstacle.region (O : PolygonalObstacle) : Set Point :=
  {x | ∃ t ∈ O.pieces, x ∈ closedTriangle t.1 t.2.1 t.2.2}

/-- A drawing by `k` pairwise disjoint polygonal obstacles. Vertices avoid all
obstacles, and two distinct vertices are adjacent exactly when their closed
joining segment avoids every obstacle. -/
structure ObstacleDrawing {V : Type u} (G : SimpleGraph V) (k : ℕ) where
  position : V → Point
  position_injective : Function.Injective position
  obstacle : Fin k → PolygonalObstacle
  obstacles_disjoint : ∀ ⦃i j : Fin k⦄, i ≠ j →
    Disjoint (obstacle i).region (obstacle j).region
  vertices_free : ∀ (v : V) (i : Fin k), position v ∉ (obstacle i).region
  realizes : ∀ ⦃u v : V⦄, u ≠ v →
    (G.Adj u v ↔ ∀ i : Fin k,
      Disjoint (closedSegment (position u) (position v)) (obstacle i).region)

/-- The ordinary obstacle number of `G` is at most `k`. -/
def ObstacleNumberAtMost {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (ObstacleDrawing G k)

/-- Straight-line planarity, used only to state that the abstract graph is
planar; it does not constrain the obstacle drawing. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ p : V → Point,
    Function.Injective p ∧
    (∀ ⦃a b v : V⦄, G.Adj a b → v ≠ a → v ≠ b → p v ∉ closedSegment (p a) (p b)) ∧
    (∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d →
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Disjoint (closedSegment (p a) (p b)) (closedSegment (p c) (p d)))

end OPG37357



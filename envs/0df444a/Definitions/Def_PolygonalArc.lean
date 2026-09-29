-- Prove2me | Definitions.Def_PolygonalArc
-- name    : PolygonalArc
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T18:37:26.055966+00:00
-- url     : https://prove2.me/theorems/fe1fb030-8b94-4477-aa8b-5860d64d85a0
-- title:
--   Polygonal arc
-- statement:
--   A polygonal arc is a simple finite polygonal chain in the Euclidean plane with at least two vertices. Its designated source and target are the first and last vertices; its carrier is the union of consecutive segments, and its relative interior removes those endpoints. The definition also records the prescribed intersection and vertex-avoidance conditions for the chain.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArc.lean#L1-L34

-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- [TABLET NODE: PolygonalArc]
structure PolygonalArc where
-- BODY
  vertices : List (EuclideanSpace ℝ (Fin 2))
  length_ge_two : 2 ≤ vertices.length
  source : EuclideanSpace ℝ (Fin 2)
  target : EuclideanSpace ℝ (Fin 2)
  source_eq_head : vertices.head? = some source
  target_eq_last : vertices.getLast? = some target
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  relativeInterior : Set (EuclideanSpace ℝ (Fin 2))
  carrier_eq :
    carrier =
      {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
        p ∈ segment ℝ vertices[i] vertices[i + 1]}
  relativeInterior_eq : relativeInterior = carrier \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))
  simple_vertices : vertices.Nodup
  segment_intersections :
    ∀ ⦃i j : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hj : j + 1 < vertices.length) →
      i < j →
      (segment ℝ vertices[i] vertices[i + 1] ∩
          segment ℝ vertices[j] vertices[j + 1]) =
        if j = i + 1 then {vertices[j]} else ∅
  vertices_avoid_nonincident_interiors :
    ∀ ⦃i k : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hk : k < vertices.length) →
      k ≠ i →
      k ≠ i + 1 →
      vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1]



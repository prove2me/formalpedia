-- Prove2me | Definitions.Def_FinitePolygonalSet
-- name    : FinitePolygonalSet
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T19:54:07.810354+00:00
-- url     : https://prove2.me/theorems/7c201a2c-4fc1-4e6d-afac-26ca1547c1aa
-- title:
--   Finite polygonal set
-- statement:
--   A finite polygonal set records a planar carrier together with a finite list of marked points and a finite list of nondegenerate segments. Every segment endpoint is among the marked points, every intersection point of two distinct listed segments is also marked, and the carrier is exactly the union of the marked points and all listed segments. This packages the finite geometric data used to control polygonal-path intersections and perturbations.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePolygonalSet.lean#L1-L23

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- [TABLET NODE: FinitePolygonalSet]
structure FinitePolygonalSet where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  points : Finset (EuclideanSpace ℝ (Fin 2))
  segments : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  segment_nondegenerate :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → s.1 ≠ s.2
  segment_endpoints_listed :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → s.1 ∈ points ∧ s.2 ∈ points
  segment_intersections_listed :
    ∀ s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → t ∈ segments → s ≠ t →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ segment ℝ s.1 s.2 → p ∈ segment ℝ t.1 t.2 → p ∈ points
  carrier_eq :
    carrier =
      (points : Set (EuclideanSpace ℝ (Fin 2))) ∪
        ⋃ s : {s // s ∈ segments}, segment ℝ s.1.1 s.1.2



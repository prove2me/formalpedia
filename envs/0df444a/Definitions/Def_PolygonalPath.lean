-- Prove2me | Definitions.Def_PolygonalPath
-- name    : PolygonalPath
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T22:20:28.539885+00:00
-- url     : https://prove2.me/theorems/85d476e2-e4f0-4be2-8ab1-c454af8730ef
-- title:
--   Polygonal paths in the plane
-- statement:
--   A polygonal path is a finite nonempty list of points in the plane together with designated source and target endpoints. Its carrier is exactly the union of those endpoints and the line segments joining consecutive vertices. This is the basic path object used to express polygonal connectivity of planar complements.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPath.lean#L1-L17

-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- [TABLET NODE: PolygonalPath]
structure PolygonalPath where
-- BODY
  vertices : List (EuclideanSpace ℝ (Fin 2))
  vertices_nonempty : vertices ≠ []
  source : EuclideanSpace ℝ (Fin 2)
  target : EuclideanSpace ℝ (Fin 2)
  source_eq_head : vertices.head? = some source
  target_eq_last : vertices.getLast? = some target
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  carrier_eq :
    carrier =
      ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
          p ∈ segment ℝ vertices[i] vertices[i + 1]}



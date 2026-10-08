-- Prove2me | Definitions.Def_FinitePolygonalSetElementaryComplex
-- name    : FinitePolygonalSetElementaryComplex
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T20:24:18.262066+00:00
-- url     : https://prove2.me/theorems/7d0dd3d7-5563-421d-a635-af8ce893113f
-- title:
--   Finite Polygonal Set Elementary Complex
-- statement:
--   Let $K$ be a finite polygonal set in the plane.  An elementary complex
--   refinement of $K$ consists of a finite vertex set $V$ and a finite edge
--   set $E$ of non-degenerate closed straight segments with the following
--   properties.  The vertex set is exactly the listed point set of $K$.  The
--   endpoints of every edge of $E$ lie in $V$.  Every edge of $E$ is a
--   consecutive subsegment of some raw listed segment of $K$, where that raw
--   segment is cut at parameters $0$, $1$, and at every parameter whose image
--   is a listed point of $K$.  Each elementary edge is contained in its raw
--   listed segment.  No vertex of $V$ lies in the relative interior of an
--   elementary edge.  Distinct elementary edges have disjoint relative interiors.
--   Finally,
--   $$
--     K = V\cup\bigcup_{e\in E} e .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FinitePolygonalSetElementaryComplex`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePolygonalSetElementaryComplex.lean#L1-L62

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Sort
import Definitions.Def_FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetElementaryComplex]
structure FinitePolygonalSetElementaryComplex (K : FinitePolygonalSet) where
-- BODY
  vertices : Finset (EuclideanSpace ℝ (Fin 2))
  edges : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  vertices_eq_points : vertices = K.points
  edge_source_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ∈ vertices
  edge_target_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.2 ∈ vertices
  edge_nondegenerate :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ≠ e.2
  edge_consecutive_cut :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧
            ∃ L : List ℝ,
              L.Nodup ∧
                L.SortedLT ∧
                  (∀ t : ℝ, t ∈ L ↔
                    t = 0 ∨ t = 1 ∨
                      (0 ≤ t ∧ t ≤ 1 ∧
                        AffineMap.lineMap s.1 s.2 t ∈ K.points)) ∧
                    (0 : ℝ) ∈ L ∧
                      (1 : ℝ) ∈ L ∧
                        (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                          (∀ n (hn : n + 1 < L.length), L[n] < L[n + 1]) ∧
                            (∀ n (hn : n + 1 < L.length) t,
                              0 ≤ t → t ≤ 1 →
                                AffineMap.lineMap s.1 s.2 t ∈ K.points →
                                  ¬ (L[n] < t ∧ t < L[n + 1])) ∧
                              ∃ k, ∃ hk : k + 1 < L.length,
                                e.1 = AffineMap.lineMap s.1 s.2 L[k] ∧
                                  e.2 = AffineMap.lineMap s.1 s.2 L[k + 1]
  edge_subset_raw :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧ segment ℝ e.1 e.2 ⊆ segment ℝ s.1 s.2
  no_vertex_in_edge_interior :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ vertices → v ∉ openSegment ℝ e.1 e.2
  edge_open_interiors_disjoint :
    ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → f ∈ edges → e ≠ f →
        Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2)
  carrier_eq :
    K.carrier =
      (vertices : Set (EuclideanSpace ℝ (Fin 2))) ∪
        ⋃ e : {e // e ∈ edges}, segment ℝ e.1.1 e.1.2



-- Prove2me | Definitions.Def_OrdinaryDrawingImageWithoutEdge
-- name    : OrdinaryDrawingImageWithoutEdge
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T20:24:27.852605+00:00
-- url     : https://prove2.me/theorems/7eec8f29-d6d4-417d-bb41-858dd9766ad5
-- title:
--   Ordinary Drawing Image Without Edge
-- statement:
--   For an ordinary polygonal drawing $D$ of a graph $G$ and an edge $e$,
--   $\mathrm{OrdinaryDrawingImageWithoutEdge}(G,D,e)$ is the union of all vertex
--   placements of $D$ and the carriers of all drawn edge arcs except the carrier
--   of $e$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OrdinaryDrawingImageWithoutEdge`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OrdinaryDrawingImageWithoutEdge.lean#L1-L13

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImageWithoutEdge]
def OrdinaryDrawingImageWithoutEdge {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  Set.range D.vertexPlacement ∪
    ⋃ f : {f : G.edgeFinset // f ≠ e}, (D.edgeArc f.1).carrier



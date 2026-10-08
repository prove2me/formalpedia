-- Prove2me | Definitions.Def_PlaneDrawingDartSectorWitnessData
-- name    : PlaneDrawingDartSectorWitnessData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:40:25.1021+00:00
-- url     : https://prove2.me/theorems/5463bf05-3c99-4cfd-ad77-63fc299906a5
-- title:
--   Plane Drawing Dart Sector Witness Data
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, and suppose oriented dart-arc data, vertex-star data, and compatible
--   side-strip data have been fixed.  Sector-witness data consists of the two
--   local sector certificates needed at vertices.
--
--   First, for each dart $d=(u,v)$, it gives an open connected sector contained
--   in the local ball around $D(v)$, contained in the complement of the drawing
--   image, and disjoint from every radial germ at $v$.  This sector meets,
--   inside that same local ball, both the left side strip of $d$ and the left
--   side strip of the successor dart $\phi(d)$.
--
--   Second, it gives vertex-sector coverage.  If a vertex $v$ is the head of at
--   least one dart, then every nonvertex point of the local ball around $D(v)$
--   which lies in the drawing complement belongs to one of these open connected
--   sectors for some incoming dart $d$ with head $v$, and the sector has the
--   same complement containment, side-strip intersection, and radial-germ
--   disjointness properties.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSectorWitnessData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSectorWitnessData.lean#L1-L52

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexStarData
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSectorWitnessData]
structure PlaneDrawingDartSectorWitnessData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (B : PlaneDrawingDartVertexStarData G D A)
    (S : PlaneDrawingDartSideStripData G D A B) where
-- BODY
  successor_clockwise_sector :
    ∀ d : G.Dart,
      ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen sector ∧ IsConnected sector ∧
          sector ⊆ Metric.ball (D.vertexPlacement d.toProd.2)
            (B.localDiskRadius d.toProd.2) ∧
          sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
          (sector ∩ S.leftSideStrip d ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (B.localDiskRadius d.toProd.2)).Nonempty ∧
          (sector ∩ S.leftSideStrip (B.successor d) ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (B.localDiskRadius d.toProd.2)).Nonempty ∧
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2},
            Disjoint sector (B.radialGerm d.toProd.2 e))
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (B.localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart,
                d.toProd.2 = v ∧
                  ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
                    y ∈ sector ∧ IsOpen sector ∧ IsConnected sector ∧
                      sector ⊆ Metric.ball (D.vertexPlacement v)
                        (B.localDiskRadius v) ∧
                      sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                      (sector ∩ S.leftSideStrip d ∩
                        Metric.ball (D.vertexPlacement v)
                          (B.localDiskRadius v)).Nonempty ∧
                      (sector ∩ S.leftSideStrip (B.successor d) ∩
                        Metric.ball (D.vertexPlacement v)
                          (B.localDiskRadius v)).Nonempty ∧
                      (∀ e : {e : G.Dart // e.toProd.1 = v},
                        Disjoint sector (B.radialGerm v e))



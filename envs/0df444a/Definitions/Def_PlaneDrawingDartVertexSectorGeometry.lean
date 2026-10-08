-- Prove2me | Definitions.Def_PlaneDrawingDartVertexSectorGeometry
-- name    : PlaneDrawingDartVertexSectorGeometry
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:21:28.125983+00:00
-- url     : https://prove2.me/theorems/d519741a-89e5-488b-a868-aedb996b2601
-- title:
--   Plane Drawing Dart Vertex Sector Geometry
-- statement:
--   For an ordinary polygonal drawing with dart-arc data, a
--   *dart vertex-sector geometry package* consists of vertex-star data
--   `PlaneDrawingDartVertexStarData`, and for every dart $d=(u,v)$
--   an open connected set $\Sigma_d$.  The set $\Sigma_d$ lies in the local
--   disk about $D(v)$, is contained in the complement of the drawing image
--   `OrdinaryDrawingImage`, and is disjoint from every radial germ at
--   $v$.  It also has terminal left endpoint access for $d$ and initial left
--   endpoint access for the successor dart: for some positive radius and aperture
--   the terminal left endpoint cone
--   `PolygonalArcTerminalEndpointLeftCone` of $d$, respectively the
--   initial left endpoint cone `PolygonalArcInitialEndpointLeftCone`
--   of the successor, is contained in $\Sigma_d$.  Finally, at every vertex that
--   is the head of some dart, the sectors cover the punctured local complement:
--   every nonvertex point of the local disk that is not in the drawing image lies
--   in one of the sectors whose dart has that vertex as head.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartVertexSectorGeometry`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartVertexSectorGeometry.lean#L1-L43

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexStarData
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexSectorGeometry]
structure PlaneDrawingDartVertexSectorGeometry {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D) where
-- BODY
  star : PlaneDrawingDartVertexStarData G D A
  successorSector : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  successorSector_isOpen : ∀ d : G.Dart, IsOpen (successorSector d)
  successorSector_isConnected : ∀ d : G.Dart, IsConnected (successorSector d)
  successorSector_subset_localDisk :
    ∀ d : G.Dart,
      successorSector d ⊆
        Metric.ball (D.vertexPlacement d.toProd.2) (star.localDiskRadius d.toProd.2)
  successorSector_subset_complement :
    ∀ d : G.Dart, successorSector d ⊆ (OrdinaryDrawingImage G D)ᶜ
  successorSector_disjoint_radialGerm :
    ∀ (d : G.Dart) (e : {e : G.Dart // e.toProd.1 = d.toProd.2}),
      Disjoint (successorSector d) (star.radialGerm d.toProd.2 e)
  terminal_left_endpoint_sector_access :
    ∀ d : G.Dart,
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        PolygonalArcTerminalEndpointLeftCone (A.dartArc d) r K ⊆ successorSector d
  successor_initial_left_endpoint_sector_access :
    ∀ d : G.Dart,
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        PolygonalArcInitialEndpointLeftCone (A.dartArc (star.successor d)) r K ⊆
          successorSector d
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (star.localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart, d.toProd.2 = v ∧ y ∈ successorSector d



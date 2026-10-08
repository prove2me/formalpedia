-- Prove2me | Definitions.Def_PlaneDrawingDartCollarChoiceData
-- name    : PlaneDrawingDartCollarChoiceData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:40:25.953351+00:00
-- url     : https://prove2.me/theorems/4a98ed6c-8eed-49e5-a151-86f6eea34b1d
-- title:
--   Plane Drawing Dart Collar Choice Data
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, let $A$ be dart-arc data, and let
--   $C$ be a dart vertex-sector geometry package.  A
--   *dart collar-choice package* for $A$ and $C$ consists, for every dart
--   $d$, of the following retained choices and compatibility facts.
--
--   First, it contains source and target endpoint radii $r_0(d)$ and $r_1(d)$
--   which satisfy the endpoint-isolation predicate
--   `PolygonalArcEndpointIsolation` for $A.dartArc(d)$, with
--   $r_0(d)$ smaller than the local vertex-star disk at $d.toProd.1$ and
--   $r_1(d)$ smaller than the local vertex-star disk at $d.toProd.2$.
--
--   Second, it contains positive source and target left-cone apertures
--   $K_0(d)>0$ and $K_1(d)>0$.  It also contains the terminal
--   sector-access radius and aperture $R_T(d),K_T(d)>0$ with
--   $$
--     PolygonalArcTerminalEndpointLeftCone(A.dartArc(d),R_T(d),K_T(d))
--       \subseteq C.successorSector(d),
--   $$
--   and the successor-initial sector-access radius and aperture
--   $R_I(d),K_I(d)>0$ with
--   $$
--     PolygonalArcInitialEndpointLeftCone(A.dartArc(C.star.successor(d)),
--       R_I(d),K_I(d))\subseteq C.successorSector(d).
--   $$
--   The target radius and aperture of $d$ are below $R_T(d)$ and $K_T(d)$,
--   and the source radius and aperture of $C.star.successor(d)$ are below
--   $R_I(d)$ and $K_I(d)$.
--
--   Third, it contains a positive collar scale $\eta(d)$, smaller than the two
--   endpoint radii, and a positive away-from-endpoints separation.  The separation
--   is larger than $\eta(d)$ and bounds the distance from every point of
--   `OrdinaryDrawingImageWithoutEdge` outside the two endpoint balls
--   to every point of the carrier of $A.dartArc(d)$.
--
--   Fourth, it contains control radii, middle-segment data, forbidden margins, and
--   compatible oriented tube data for $A.dartArc(d)$.  The source and target
--   control radii are respectively smaller than $r_0(d)$ and $r_1(d)$, all
--   non-source control balls are disjoint from the source endpoint ball, and all
--   non-target control balls are disjoint from the target endpoint ball.  The
--   initial tube cone bound is smaller than $K_0(d)$, and the terminal tube cone
--   bound on the last segment is smaller than $K_1(d)$.  In addition, every
--   non-first tube is disjoint from the source endpoint ball, every non-last tube
--   is disjoint from the target endpoint ball, the part of the first left
--   half-tube inside the source endpoint ball is contained in the initial endpoint
--   left cone with parameters $r_0(d),K_0(d)$, and the part of the last left
--   half-tube inside the target endpoint ball is contained in the terminal
--   endpoint left cone with parameters $r_1(d),K_1(d)$.
--
--   Fifth, it contains vertex-local pieces and local-side data for the same
--   oriented collar.  The local source left side piece is contained in
--   $$
--     PolygonalArcInitialEndpointLeftCone(A.dartArc(d),r_0(d),K_0(d)),
--   $$
--   and the local target left side piece is contained in
--   $$
--     PolygonalArcTerminalEndpointLeftCone(A.dartArc(d),r_1(d),K_1(d)).
--   $$
--
--   Finally, it contains polygonal side strips for $A.dartArc(d)$, in the sense
--   of `PolygonalSideStrips`.  The exported left strip is nonempty and
--   is contained in the complement of the whole drawing image
--   `OrdinaryDrawingImage`.  Near every point of the relative interior
--   of $A.dartArc(d)$, the drawing complement inside a sufficiently small open
--   neighborhood is contained in the union of the exported left strip of $d$ and
--   the exported left strip of the reverse dart $\bar d$.  The side labels are
--   coherent under reversal: the exported right strip of $d$ is the exported
--   left strip of $\bar d$.
--
--   The package also records the two endpoint access facts actually used in the
--   successor-sector argument.  For every dart $d$, the sector
--   $C.successorSector(d)$, the exported left strip of $d$, and the local
--   disk at the head of $d$ have nonempty triple intersection.  The same sector,
--   the exported left strip of the successor dart $C.star.successor(d)$, and
--   that local disk also have nonempty triple intersection.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartCollarChoiceData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartCollarChoiceData.lean#L1-L195

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OrdinaryDrawingImageWithoutEdge
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarLocalSideData
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData
import Definitions.Def_PolygonalArcCollarVertexLocalPieceData
import Definitions.Def_PolygonalArcEndpointIsolation
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartCollarChoiceData]
structure PlaneDrawingDartCollarChoiceData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) where
-- BODY
  sourceRadius : G.Dart → ℝ
  targetRadius : G.Dart → ℝ
  endpointIsolation :
    ∀ d : G.Dart, PolygonalArcEndpointIsolation (A.dartArc d)
      (sourceRadius d) (targetRadius d)
  sourceRadius_lt_localDisk :
    ∀ d : G.Dart, sourceRadius d < C.star.localDiskRadius d.toProd.1
  targetRadius_lt_localDisk :
    ∀ d : G.Dart, targetRadius d < C.star.localDiskRadius d.toProd.2
  sourceAperture : G.Dart → ℝ
  targetAperture : G.Dart → ℝ
  sourceAperture_pos : ∀ d : G.Dart, 0 < sourceAperture d
  targetAperture_pos : ∀ d : G.Dart, 0 < targetAperture d
  terminalSectorRadius : G.Dart → ℝ
  terminalSectorAperture : G.Dart → ℝ
  terminalSectorRadius_pos : ∀ d : G.Dart, 0 < terminalSectorRadius d
  terminalSectorAperture_pos : ∀ d : G.Dart, 0 < terminalSectorAperture d
  terminalSector_subset_successorSector :
    ∀ d : G.Dart,
      PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
        (terminalSectorRadius d) (terminalSectorAperture d) ⊆
          C.successorSector d
  successorInitialSectorRadius : G.Dart → ℝ
  successorInitialSectorAperture : G.Dart → ℝ
  successorInitialSectorRadius_pos :
    ∀ d : G.Dart, 0 < successorInitialSectorRadius d
  successorInitialSectorAperture_pos :
    ∀ d : G.Dart, 0 < successorInitialSectorAperture d
  successorInitialSector_subset_successorSector :
    ∀ d : G.Dart,
      PolygonalArcInitialEndpointLeftCone (A.dartArc (C.star.successor d))
        (successorInitialSectorRadius d) (successorInitialSectorAperture d) ⊆
          C.successorSector d
  targetRadius_lt_terminalSectorRadius :
    ∀ d : G.Dart, targetRadius d < terminalSectorRadius d
  targetAperture_lt_terminalSectorAperture :
    ∀ d : G.Dart, targetAperture d < terminalSectorAperture d
  successor_sourceRadius_lt_initialSectorRadius :
    ∀ d : G.Dart, sourceRadius (C.star.successor d) <
      successorInitialSectorRadius d
  successor_sourceAperture_lt_initialSectorAperture :
    ∀ d : G.Dart, sourceAperture (C.star.successor d) <
      successorInitialSectorAperture d
  eta : G.Dart → ℝ
  eta_pos : ∀ d : G.Dart, 0 < eta d
  eta_lt_sourceRadius : ∀ d : G.Dart, eta d < sourceRadius d
  eta_lt_targetRadius : ∀ d : G.Dart, eta d < targetRadius d
  awaySeparation : G.Dart → ℝ
  awaySeparation_pos : ∀ d : G.Dart, 0 < awaySeparation d
  eta_lt_awaySeparation : ∀ d : G.Dart, eta d < awaySeparation d
  awaySeparation_le_dist :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
        x ∉ Metric.ball (A.dartArc d).source (sourceRadius d) ∪
          Metric.ball (A.dartArc d).target (targetRadius d) →
          ∀ p : EuclideanSpace ℝ (Fin 2),
            p ∈ (A.dartArc d).carrier →
              awaySeparation d ≤ dist x p
  controlRadii :
    ∀ d : G.Dart, PolygonalArcCollarControlRadii (A.dartArc d) (eta d)
  source_controlRadius_lt :
    ∀ (d : G.Dart) (hsource : 0 < (A.dartArc d).vertices.length),
      (controlRadii d).radius ⟨0, hsource⟩ < sourceRadius d
  target_controlRadius_lt :
    ∀ (d : G.Dart)
      (htarget : (A.dartArc d).vertices.length - 1 <
        (A.dartArc d).vertices.length),
      (controlRadii d).radius
        ⟨(A.dartArc d).vertices.length - 1, htarget⟩ < targetRadius d
  source_controlBall_disjoint :
    ∀ (d : G.Dart) (i : Fin (A.dartArc d).vertices.length),
      i.1 ≠ 0 →
        Disjoint
          (Metric.ball (A.dartArc d).vertices[i.1] ((controlRadii d).radius i))
          (Metric.ball (A.dartArc d).source (sourceRadius d))
  target_controlBall_disjoint :
    ∀ (d : G.Dart) (i : Fin (A.dartArc d).vertices.length),
      i.1 + 1 ≠ (A.dartArc d).vertices.length →
        Disjoint
          (Metric.ball (A.dartArc d).vertices[i.1] ((controlRadii d).radius i))
          (Metric.ball (A.dartArc d).target (targetRadius d))
  middleSegments :
    ∀ d : G.Dart,
      PolygonalArcCollarMiddleSegmentData (A.dartArc d) (controlRadii d)
  forbiddenMargins :
    ∀ d : G.Dart,
      PolygonalArcCollarMiddleForbiddenMargins (A.dartArc d) (controlRadii d)
        (middleSegments d)
  compatibleTubes :
    ∀ d : G.Dart,
      PolygonalArcCollarCompatibleOrientedTubeData (A.dartArc d)
        (controlRadii d) (middleSegments d) (forbiddenMargins d)
  initialConeBound_lt_sourceAperture :
    ∀ (d : G.Dart) (hfirst : 0 + 1 < (A.dartArc d).vertices.length),
      (compatibleTubes d).initialConeBound 0 hfirst < sourceAperture d
  terminalConeBound_lt_targetAperture :
    ∀ (d : G.Dart)
      (hlast : ((A.dartArc d).vertices.length - 2) + 1 <
        (A.dartArc d).vertices.length),
      (compatibleTubes d).terminalConeBound ((A.dartArc d).vertices.length - 2)
        hlast < targetAperture d
  nonfirst_tube_disjoint_sourceBall :
    ∀ (d : G.Dart) (j : ℕ) (hj : j + 1 < (A.dartArc d).vertices.length),
      j ≠ 0 →
        Disjoint ((compatibleTubes d).orientedTubes.tube j hj)
          (Metric.ball (A.dartArc d).source (sourceRadius d))
  nonlast_tube_disjoint_targetBall :
    ∀ (d : G.Dart) (j : ℕ) (hj : j + 1 < (A.dartArc d).vertices.length),
      (j + 1) + 1 ≠ (A.dartArc d).vertices.length →
        Disjoint ((compatibleTubes d).orientedTubes.tube j hj)
          (Metric.ball (A.dartArc d).target (targetRadius d))
  first_leftHalf_sourceBall_subset_initialCone :
    ∀ (d : G.Dart) (hfirst : 0 + 1 < (A.dartArc d).vertices.length),
      (compatibleTubes d).orientedTubes.leftHalf 0 hfirst ∩
          Metric.ball (A.dartArc d).source (sourceRadius d) ⊆
        PolygonalArcInitialEndpointLeftCone (A.dartArc d)
          (sourceRadius d) (sourceAperture d)
  last_leftHalf_targetBall_subset_terminalCone :
    ∀ (d : G.Dart)
      (hlast : ((A.dartArc d).vertices.length - 2) + 1 <
        (A.dartArc d).vertices.length),
      (compatibleTubes d).orientedTubes.leftHalf
          ((A.dartArc d).vertices.length - 2) hlast ∩
          Metric.ball (A.dartArc d).target (targetRadius d) ⊆
        PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
          (targetRadius d) (targetAperture d)
  vertexLocalPieces :
    ∀ d : G.Dart,
      PolygonalArcCollarVertexLocalPieceData (A.dartArc d) (controlRadii d)
        (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d).orientedTubes.toPolygonalArcCollarSeparatedTubeData
  localSideData :
    ∀ d : G.Dart,
      PolygonalArcCollarLocalSideData (A.dartArc d) (controlRadii d)
        (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d).orientedTubes (vertexLocalPieces d)
  source_leftSidePiece_subset_initialCone :
    ∀ (d : G.Dart) (hsource : 0 < (A.dartArc d).vertices.length),
      (localSideData d).leftSidePiece ⟨0, hsource⟩ ⊆
        PolygonalArcInitialEndpointLeftCone (A.dartArc d)
          (sourceRadius d) (sourceAperture d)
  target_leftSidePiece_subset_terminalCone :
    ∀ (d : G.Dart)
      (htarget : (A.dartArc d).vertices.length - 1 <
        (A.dartArc d).vertices.length),
      (localSideData d).leftSidePiece
        ⟨(A.dartArc d).vertices.length - 1, htarget⟩ ⊆
          PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
            (targetRadius d) (targetAperture d)
  sideStrips : ∀ d : G.Dart, PolygonalSideStrips (A.dartArc d)
  leftStrip_nonempty :
    ∀ d : G.Dart, ((sideStrips d).leftStrip).Nonempty
  leftStrip_subset_complement :
    ∀ d : G.Dart,
      (sideStrips d).leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (A.dartArc d).relativeInterior →
        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ x ∈ U ∧
            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
              (sideStrips d).leftStrip ∪ (sideStrips d.symm).leftStrip
  rightStrip_eq_leftStrip_symm :
    ∀ d : G.Dart, (sideStrips d).rightStrip = (sideStrips d.symm).leftStrip
  successorSector_meets_leftStrip :
    ∀ d : G.Dart,
      (C.successorSector d ∩ (sideStrips d).leftStrip ∩
        Metric.ball (D.vertexPlacement d.toProd.2)
          (C.star.localDiskRadius d.toProd.2)).Nonempty
  successorSector_meets_successor_leftStrip :
    ∀ d : G.Dart,
      (C.successorSector d ∩ (sideStrips (C.star.successor d)).leftStrip ∩
        Metric.ball (D.vertexPlacement d.toProd.2)
          (C.star.localDiskRadius d.toProd.2)).Nonempty



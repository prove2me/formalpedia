-- Prove2me | Definitions.Def_PlaneFaceData
-- name    : PlaneFaceData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T21:33:56.167856+00:00
-- url     : https://prove2.me/theorems/b80c6ed0-f3df-4dcc-9899-ad031131b5c9
-- title:
--   Plane face data for a crossing-free ordinary polygonal drawing
-- statement:
--   A finite combinatorial and geometric record describing the faces, darts, side strips, local vertex sectors, and cyclic successor structure associated with a crossing-free ordinary polygonal drawing of a finite simple graph.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneFaceData.lean#L1-L145

import Definitions.Def_OrdinaryPolygonalDrawing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

-- Source-only support declarations, kept local to this definition module.
def ComplementComponent (K F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  F.Nonempty ∧ F ⊆ Kᶜ ∧ IsConnected F ∧
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      C.Nonempty → C ⊆ Kᶜ → IsConnected C → F ⊆ C → C ⊆ F

def OrdinaryDrawingImage {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Set.range D.vertexPlacement ∪ ⋃ e : G.edgeFinset, (D.edgeArc e).carrier

def DrawingFaceComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ComplementComponent (OrdinaryDrawingImage G D) F

structure PolygonalSideStrips (γ : PolygonalArc) where
  collar : Set (EuclideanSpace ℝ (Fin 2))
  leftStrip : Set (EuclideanSpace ℝ (Fin 2))
  rightStrip : Set (EuclideanSpace ℝ (Fin 2))
  collar_open : IsOpen collar
  left_open : IsOpen leftStrip
  right_open : IsOpen rightStrip
  relativeInterior_subset_collar : γ.relativeInterior ⊆ collar
  left_subset_collar : leftStrip ⊆ collar
  right_subset_collar : rightStrip ⊆ collar
  left_connected : IsConnected leftStrip
  right_connected : IsConnected rightStrip
  left_disjoint_arc : Disjoint leftStrip γ.carrier
  right_disjoint_arc : Disjoint rightStrip γ.carrier
  side_strips_disjoint : Disjoint leftStrip rightStrip
  relativeInterior_subset_closure_left :
    γ.relativeInterior ⊆ closure leftStrip
  relativeInterior_subset_closure_right :
    γ.relativeInterior ⊆ closure rightStrip
  collar_without_arc :
    collar \ γ.relativeInterior = leftStrip ∪ rightStrip

open Classical
noncomputable section

-- [TABLET NODE: PlaneFaceData]
structure PlaneFaceData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G) where
-- BODY
  isPlane : D.crossingSet.card = 0
  Face : Type*
  [faceFintype : Fintype Face]
  faceSet : Face → Set (EuclideanSpace ℝ (Fin 2))
  face_component : ∀ F : Face, DrawingFaceComponent G D (faceSet F)
  faces_complete :
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent G D C → ∃! F : Face, faceSet F = C
  complement_point_face :
    ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ (OrdinaryDrawingImage G D)ᶜ → ∃! F : Face, p ∈ faceSet F
  dartEdge : G.Dart → G.edgeFinset
  dartEdge_eq : ∀ d : G.Dart, (dartEdge d).1 = d.edge
  dartArc : G.Dart → PolygonalArc
  dartArc_carrier :
    ∀ d : G.Dart, (dartArc d).carrier = (D.edgeArc (dartEdge d)).carrier
  dartArc_source :
    ∀ d : G.Dart, (dartArc d).source = D.vertexPlacement d.toProd.1
  dartArc_target :
    ∀ d : G.Dart, (dartArc d).target = D.vertexPlacement d.toProd.2
  leftSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  rightSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  sideStripData :
    ∀ d : G.Dart, ∃ S : PolygonalSideStrips (dartArc d),
      leftSideStrip d = S.leftStrip ∧ rightSideStrip d = S.rightStrip
  rightSideStrip_eq_leftSideStrip_symm :
    ∀ d : G.Dart, rightSideStrip d = leftSideStrip d.symm
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (dartArc d).relativeInterior →
        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ x ∈ U ∧
            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
              leftSideStrip d ∪ leftSideStrip d.symm
  leftFace : G.Dart → Face
  leftFace_contains :
    ∀ d : G.Dart, leftSideStrip d ⊆ faceSet (leftFace d)
  localDiskRadius : V → ℝ
  localDiskRadius_pos : ∀ v : V, 0 < localDiskRadius v
  germDirection :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2)
  germDirection_ne_zero :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}), germDirection v d ≠ 0
  radialGerm :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
      Set (EuclideanSpace ℝ (Fin 2))
  radialGerm_eq_openSegment :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      ∃ r : ℝ, 0 < r ∧ r ≤ localDiskRadius v ∧
        radialGerm v d =
          openSegment ℝ (D.vertexPlacement v)
            (D.vertexPlacement v + r • germDirection v d)
  radialGerm_subset_dartArc :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      radialGerm v d ⊆ (D.edgeArc (dartEdge d.1)).carrier
  localDisk_meets_drawing_only_incident_germs :
    ∀ v : V,
      Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
          OrdinaryDrawingImage G D =
        {D.vertexPlacement v} ∪
          ⋃ d : {d : G.Dart // d.toProd.1 = v}, radialGerm v d
  clockwiseNext :
    ∀ v : V, Equiv.Perm {d : G.Dart // d.toProd.1 = v}
  fullClockwiseTurn : V → ℝ
  fullClockwiseTurn_pos : ∀ v : V, 0 < fullClockwiseTurn v
  clockwiseTurn :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
      {d : G.Dart // d.toProd.1 = v} → ℝ
  clockwiseTurn_pos :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}), 0 < clockwiseTurn v d e
  clockwiseTurn_le_full :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      clockwiseTurn v d e ≤ fullClockwiseTurn v
  clockwiseTurn_full_iff_same :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      clockwiseTurn v d e = fullClockwiseTurn v ↔ e = d
  clockwiseNext_first_after :
    ∀ (v : V) (d e : {d : G.Dart // d.toProd.1 = v}),
      e ≠ d → clockwiseTurn v d (clockwiseNext v d) ≤ clockwiseTurn v d e
  clockwiseNext_eq_self_iff_isolated :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      clockwiseNext v d = d ↔ ∀ e : {d : G.Dart // d.toProd.1 = v}, e = d
  successor : Equiv.Perm G.Dart
  successor_tail : ∀ d : G.Dart, (successor d).toProd.1 = d.toProd.2
  successor_eq_clockwiseNext :
    ∀ d : G.Dart,
      successor d =
        (clockwiseNext d.toProd.2
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).1
  successor_single_incident :
    ∀ d : G.Dart,
      (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e.1 = d.symm) →
        successor d = d.symm
  successor_clockwise_sector :
    ∀ d : G.Dart,
      ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen sector ∧ IsConnected sector ∧
          sector ⊆ Metric.ball (D.vertexPlacement d.toProd.2)
            (localDiskRadius d.toProd.2) ∧
          sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
          (sector ∩ leftSideStrip d ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (localDiskRadius d.toProd.2)).Nonempty ∧
          (sector ∩ leftSideStrip (successor d) ∩
            Metric.ball (D.vertexPlacement d.toProd.2)
              (localDiskRadius d.toProd.2)).Nonempty ∧
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2},
            Disjoint sector (radialGerm d.toProd.2 e))
  vertex_sector_coverage :
    ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      (∃ d : G.Dart, d.toProd.2 = v) →
        y ∈ Metric.ball (D.vertexPlacement v) (localDiskRadius v) →
          y ≠ D.vertexPlacement v →
            y ∈ (OrdinaryDrawingImage G D)ᶜ →
              ∃ d : G.Dart,
                d.toProd.2 = v ∧
                  ∃ sector : Set (EuclideanSpace ℝ (Fin 2)),
                    y ∈ sector ∧ IsOpen sector ∧ IsConnected sector ∧
                      sector ⊆ Metric.ball (D.vertexPlacement v)
                        (localDiskRadius v) ∧
                      sector ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                      (sector ∩ leftSideStrip d ∩
                        Metric.ball (D.vertexPlacement v)
                          (localDiskRadius v)).Nonempty ∧
                      (sector ∩ leftSideStrip (successor d) ∩
                        Metric.ball (D.vertexPlacement v)
                          (localDiskRadius v)).Nonempty ∧
                      (∀ e : {e : G.Dart // e.toProd.1 = v},
                        Disjoint sector (radialGerm v e))
  faceDegree : Face → ℕ
  faceDegree_eq :
    ∀ F : Face, faceDegree F = Fintype.card {d : G.Dart // leftFace d = F}



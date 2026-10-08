-- Prove2me | Definitions.Def_PlaneDrawingDartSectorData
-- name    : PlaneDrawingDartSectorData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T20:24:38.266297+00:00
-- url     : https://prove2.me/theorems/ece7aed3-798d-421a-87a5-62571dc01ae9
-- title:
--   Plane Drawing Dart Sector Data
-- statement:
--   Let $G$ be a finite simple graph and let $D$ be an ordinary polygonal
--   drawing of $G$.  Write $K=|D|$ for its drawing image.  Local dart-sector
--   data for $D$ consists of the part of the face-data construction that is
--   local to edge sides and vertex stars, but not the finite indexing of faces.
--
--   For each dart $d$, the data chooses the underlying edge, an oriented
--   polygonal arc with the same carrier as the drawn edge and with source and
--   target equal to the placed tail and head of $d$, and left and right side
--   strips for that oriented arc.  Each chosen left side strip and each chosen
--   right side strip lies in a unique complement face component of
--   $\mathbb R^2\setminus K$.  The side labels are coherent under reversing the
--   dart: the right side strip of $d$ is the left side strip of the reverse dart
--   $\bar d$.
--
--   The side strips also own the local complement along the dart.  For every dart
--   $d$ and every point $x$ of the relative interior of the oriented dart arc,
--   there is an open neighborhood $U_x$ of $x$ such that
--   $$
--     U_x\cap(\mathbb R^2\setminus K)
--     \subseteq
--     \operatorname{leftSideStrip}(d)\cup
--     \operatorname{leftSideStrip}(\bar d).
--   $$
--   Thus, near any non-endpoint point of a drawn edge, the old drawing complement
--   is locally contained in the two side strips assigned to the two orientations
--   of that edge.
--
--   For each vertex $v$, the data chooses a positive radius $\rho_v$.  In the
--   ball $B(D(v),\rho_v)$, the drawing is exactly the vertex point $D(v)$
--   together with the radial germs of the darts whose tail is $v$.  Each germ is
--   an open segment from $D(v)$ in a nonzero direction, with length at most
--   $\rho_v$, and is contained in the corresponding edge-arc carrier.  The
--   outgoing darts at $v$ are equipped with a local clockwise-next permutation
--   and with positive clockwise-turn values.  These turns are bounded by one
--   positive full turn, a full turn occurs exactly from a dart to itself, and the
--   clockwise-next dart is the first dart encountered after a positive clockwise
--   turn.  If a dart is the only outgoing dart at $v$, the clockwise-next map
--   sends it to itself, and this is the only fixed-point case.
--
--   The global successor $\phi$ sends a dart $d=(u,v)$ to the dart obtained at
--   $v$ by applying the local clockwise-next map to the reverse germ
--   $\bar d=(v,u)$.  Thus $\phi(d)$ has tail $v$, agrees with the local
--   clockwise-next construction, and equals $\bar d$ when $\bar d$ is the only
--   incident germ at $v$.
--
--   Finally, the data includes two existential sector certificates.  First, for
--   each dart $d=(u,v)$, there exists a successor-clockwise sector $S$.  The
--   set $S$ is open and connected, is contained in
--   $B(D(v),\rho_v)\cap K^c$, is disjoint from every radial germ whose tail is
--   $v$, and has nonempty intersection, inside $B(D(v),\rho_v)$, with both
--   the left side strip of $d$ and the left side strip of $\phi(d)$.
--
--   Second, if a vertex $v$ is the head of at least one dart, then every point
--   $$
--     y\in B(D(v),\rho_v)\cap K^c,\qquad y\ne D(v),
--   $$
--   lies in some sector of the same kind: there are a dart $d$ with head $v$
--   and an open connected set $S$ containing $y$, contained in
--   $B(D(v),\rho_v)\cap K^c$, disjoint from every radial germ whose tail is
--   $v$, and meeting inside $B(D(v),\rho_v)$ both the left side strip of
--   $d$ and the left side strip of $\phi(d)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSectorData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSectorData.lean#L1-L134

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSectorData]
structure PlaneDrawingDartSectorData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G) where
-- BODY
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
  leftSide_unique_face_component :
    ∀ d : G.Dart, ∃! L : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent G D L ∧ leftSideStrip d ⊆ L
  rightSide_unique_face_component :
    ∀ d : G.Dart, ∃! R : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent G D R ∧ rightSideStrip d ⊆ R
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



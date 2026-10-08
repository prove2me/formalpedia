-- Prove2me | Definitions.Def_PlaneDrawingDartVertexStarData
-- name    : PlaneDrawingDartVertexStarData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:03:27.433987+00:00
-- url     : https://prove2.me/theorems/aee379e7-9d72-4258-ac98-466980c478bb
-- title:
--   Plane Drawing Dart Vertex Star Data
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, and suppose oriented dart-arc data has been fixed.  Vertex-star data
--   consists of the local information around each placed vertex.  For every vertex
--   $v$, it chooses a positive radius $\rho_v$, and for every outgoing dart at
--   $v$, it chooses a nonzero direction vector and a radial germ.  The direction
--   vector is required to be the normalized first segment vector of the
--   corresponding dart arc:
--   $$
--     u_{v,d}
--     =
--     \|(A.dartArc(d)).vertices_1-D(v)\|^{-1}
--     \bigl((A.dartArc(d)).vertices_1-D(v)\bigr).
--   $$
--   The radial germ is an open segment from $D(v)$ in that direction, of length
--   at most $\rho_v$, and is contained in the corresponding drawn edge carrier.
--   In the ball
--   $B(D(v),\rho_v)$, the drawing image is exactly the vertex point together
--   with these outgoing radial germs.
--
--   The same data orders the outgoing germs cyclically.  It chooses a positive
--   full clockwise turn, positive clockwise-turn values between outgoing darts,
--   and a clockwise-next permutation.  Full turn occurs exactly from a dart to
--   itself, all turns are bounded by the full turn, and the clockwise-next dart is
--   the first outgoing dart encountered after a positive clockwise turn.  The
--   clockwise-next map fixes a dart exactly in the one-incident-germ case.  Finally,
--   the data chooses the global successor permutation on all darts by reversing an
--   incoming dart at its head and applying the local clockwise-next map there.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartVertexStarData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartVertexStarData.lean#L1-L75

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexStarData]
structure PlaneDrawingDartVertexStarData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D) where
-- BODY
  localDiskRadius : V → ℝ
  localDiskRadius_pos : ∀ v : V, 0 < localDiskRadius v
  germDirection :
    ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2)
  germDirection_ne_zero :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}), germDirection v d ≠ 0
  germDirection_eq_normalized_firstSegment :
    ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      germDirection v d =
        (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
          ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)
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
      radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier
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



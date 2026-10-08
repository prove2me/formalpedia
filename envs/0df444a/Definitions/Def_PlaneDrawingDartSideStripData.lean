-- Prove2me | Definitions.Def_PlaneDrawingDartSideStripData
-- name    : PlaneDrawingDartSideStripData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:21:45.911404+00:00
-- url     : https://prove2.me/theorems/a6369ca7-543f-4db4-877f-448599ff5e28
-- title:
--   Plane Drawing Dart Side Strip Data
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing
--   of $G$, and suppose oriented dart-arc data and vertex-star data have been
--   fixed.  Compatible side-strip data chooses, for every dart $d$, a left side
--   strip and a right side strip for the oriented dart arc of $d$.  These strips
--   are realized by polygonal side-strip data in the sense of
--   `PolygonalSideStrips`, and the labels are coherent under reversal:
--   the right side strip of $d$ is the left side strip of $\bar d$.
--
--   Both side strips are required to lie in the complement of the whole drawing
--   image.  They also own the local complement along the dart: for every point of
--   the relative interior of the dart arc, some open neighborhood meets the drawing
--   complement only inside the union of the two left side strips assigned to the
--   two orientations of the same edge.  Finally, each left side strip and each
--   right side strip lies in a unique drawing face component.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartSideStripData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartSideStripData.lean#L1-L40

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexStarData
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripData]
structure PlaneDrawingDartSideStripData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (B : PlaneDrawingDartVertexStarData G D A) where
-- BODY
  leftSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  rightSideStrip : G.Dart → Set (EuclideanSpace ℝ (Fin 2))
  sideStripData :
    ∀ d : G.Dart, ∃ S : PolygonalSideStrips (A.dartArc d),
      leftSideStrip d = S.leftStrip ∧ rightSideStrip d = S.rightStrip
  rightSideStrip_eq_leftSideStrip_symm :
    ∀ d : G.Dart, rightSideStrip d = leftSideStrip d.symm
  leftSideStrip_subset_complement :
    ∀ d : G.Dart, leftSideStrip d ⊆ (OrdinaryDrawingImage G D)ᶜ
  rightSideStrip_subset_complement :
    ∀ d : G.Dart, rightSideStrip d ⊆ (OrdinaryDrawingImage G D)ᶜ
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (A.dartArc d).relativeInterior →
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



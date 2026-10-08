-- Prove2me | Definitions.Def_PlaneDrawingDartArcData
-- name    : PlaneDrawingDartArcData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T20:24:30.284195+00:00
-- url     : https://prove2.me/theorems/d4326c61-7666-410a-ab00-a46faa0e91a6
-- title:
--   Plane Drawing Dart Arc Data
-- statement:
--   Let $G$ be a finite simple graph and let $D$ be an ordinary polygonal
--   drawing of $G$.  Oriented dart-arc data for $D$ consists of the following
--   choices.  For each dart $d$, it chooses the underlying edge of $d$, with
--   the assertion that this edge has unordered endpoint pair equal to the edge of
--   $d$.  It also chooses an oriented polygonal arc $\gamma_d$ whose carrier is
--   the carrier of the drawn edge of $d$, whose source is the placement of the
--   tail of $d$, and whose target is the placement of the head of $d$.
--   Moreover, this oriented arc is publicly identified with the stored edge arc
--   in the dart orientation: for each dart $d=(u,v)$, either
--   $\gamma_d$ is exactly the stored arc $D(e_d)$ and the stored source is
--   $D(u)$, or $\gamma_d$ is exactly
--   $\operatorname{PolygonalArcReverse}(D(e_d))$ and the stored target is
--   $D(u)$.  Thus the first segment of $\gamma_d$ can be rewritten as the
--   stored first segment of $D(e_d)$ in the first case, and as the reversed
--   stored last segment of $D(e_d)$ in the second case.
--   Finally the two orientations of the same drawn edge are required to be
--   coherent: for every dart $d$,
--   $$
--     \gamma_{\bar d}=\operatorname{PolygonalArcReverse}(\gamma_d).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartArcData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartArcData.lean#L1-L28

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcReverse

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartArcData]
structure PlaneDrawingDartArcData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G) where
-- BODY
  dartEdge : G.Dart → G.edgeFinset
  dartEdge_eq : ∀ d : G.Dart, (dartEdge d).1 = d.edge
  dartArc : G.Dart → PolygonalArc
  dartArc_orientation :
    ∀ d : G.Dart,
      (dartArc d = D.edgeArc (dartEdge d) ∧
        (D.edgeArc (dartEdge d)).source = D.vertexPlacement d.toProd.1) ∨
      (dartArc d = PolygonalArcReverse (D.edgeArc (dartEdge d)) ∧
        (D.edgeArc (dartEdge d)).target = D.vertexPlacement d.toProd.1)
  dartArc_carrier :
    ∀ d : G.Dart, (dartArc d).carrier = (D.edgeArc (dartEdge d)).carrier
  dartArc_source :
    ∀ d : G.Dart, (dartArc d).source = D.vertexPlacement d.toProd.1
  dartArc_target :
    ∀ d : G.Dart, (dartArc d).target = D.vertexPlacement d.toProd.2
  dartArc_symm_eq_reverse :
    ∀ d : G.Dart, dartArc d.symm = PolygonalArcReverse (dartArc d)



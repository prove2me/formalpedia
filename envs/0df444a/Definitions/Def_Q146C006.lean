-- Prove2me | Definitions.Def_Q146C006
-- name    : Q146C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:11:43.499902+00:00
-- url     : https://prove2.me/theorems/ed01c8f7-5472-4518-846d-97ab90788cad
-- title:
--   Definitions bundle Q146C006 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 427 declarations of OpenAI's Lean: 23 definitions, 4 inductive types or structures, 2 instances and 398 theorems. The definitions and types are `Graph.IsPlaneChain`, `Schoenflies.ArcCollar.ptL`, `Schoenflies.ArcCollar.ptR`, `Schoenflies.CellStructure.Realization.faceBoundary`, `Schoenflies.CellStructure.SplitData.IsCrosscutSplit`, `Schoenflies.CellStructure.SplitData.IsRefinement`, `Schoenflies.CellStructure.SplitData.earNewCells`, `Schoenflies.CellStructure.SplitData.parent`, `Schoenflies.CellStructure.subcells`, `Schoenflies.HasArcCollars`, `Schoenflies.IsPieceChain`, `Schoenflies.IsPolyArcCarrier`, `Schoenflies.PolyArc.trimmed`, `Schoenflies.PreArc.carrier`, `Schoenflies.SquaresTwoConnected`, `Schoenflies.familyChain`, `Schoenflies.familyOverlay`, `Schoenflies.familyPieces`, `Schoenflies.familyPoints`, `Schoenflies.familySquare`, `Schoenflies.insideEdges`, `Schoenflies.sideEdges`, `Schoenflies.sqCoord`, `Schoenflies.squareEdges`, `Schoenflies.squareGraph`, `Schoenflies.squarePieces`, `Schoenflies.subarcCell`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `AccessibleJoin`, `ArcCollars`, `ArcComplement`, `ArcComplementPrep`, `BoundaryCycles`, `BoundaryCyclesGenerated`, `CellulationInvariants`, `CombinatorialInvariance`, `CrosscutAtMostTwo`, `CrosscutEncloses`, `CrosscutExists`, `FaceCycles`, `FaceCyclesLand`, `FaceCyclesProof`, `FiniteTransfer`, `GeneralCrosscut`, `GeneratedStructure`, `Graph_Component`, `Graph_Drawing`, `Graph_OuterFace`, `Graph_PathGraph`, `Graph_Relabel`, `Graph_RelativeEar`, `Graph_Tree`, `Graph_TwoConnected`, `Jordan`, `JordanClosed`, `JordanSeparates`, `LocallyPolygonal`, `MatchedSplit`, `OuterChain`, `OuterChainClosed`, `OverlayGraph`, `PolyArcRealize`, `PolyPath`, `RealizeSplit`, `RefinementStars`, `SimpleArc`, `SquareCycle`, `SquareMover`, `TwoArcs`.
--
--   **Imports.** It imports the bundles `Q146C003` and `Q146C004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C009` and `Q146C010`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_Q146C003
import Definitions.Def_Q146C004

section
-- module Solutions.Q146_CD.PolyPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.poly_pair _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

/-! ### The carrier of a vertex list -/

/-! ### Polygonal connectedness -/

/-- Lemma 1.1 (polygonal connectedness), existence half. Any two points of a region are
joined in it by a polygonal path.

The blueprint goes on to make the path *simple*, by subdividing at self-intersections and
taking a simple path in the resulting finite graph; that half is deferred to the graph
module, where the subdivision procedure is available. -/
theorem exists_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  -- `R` is the set of points reachable from `x` by a polygonal path inside `Ω`.
  set R : Set Plane :=
    {w ∈ Ω | ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  -- Extending a path by a segment inside a convex subset of `Ω` keeps it inside `Ω`. Applied
  -- to a ball this makes `R` open, and applied in the other direction makes `Ω \ R` open.
  have key : ∀ C : Set Plane, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    -- A path to `z` runs back to `w` through the same ball, so `w ∈ R` after all.
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  -- `R` is nonempty, open and closed in the preconnected `Ω`, so `R = Ω`.
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

end Schoenflies
end

section
-- module Solutions.Q146_CD.LocallyPolygonal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.poly_pair _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The plane minus finitely many open squares is locally polygonally connected

This is brick B5 of the polygonal-redrawing argument. The redrawing cuts an open axis-parallel
square out of the plane around each vertex of the graph; what the rest of the argument needs of
the leftover set `M` is that it is *locally polygonally connected* — every point of `M` has a
relatively open neighbourhood all of whose points are joined to each other by polygonal paths
running inside `M`. That is what feeds the clopen argument one level up (brick B6), where the
basic open piece is no longer a ball.

The informal description of the three basic shapes — a disk away from every square, a half-disk
against one side, a three-quarter disk at a corner — suggests an angular case analysis. There is
none here. Both the squares and the basic neighbourhoods are axis-parallel, so each shape is an
intersection of a small square with the complement of an open square, and

* the complement of an open square is the union of the four closed coordinate half-planes that
  bound it (`Plane.compl_openSquare_subset_iUnion`);
* intersecting with a small square gives four *rectangles*, each convex;
* if the small square is small enough, each of those rectangles is either empty or contains the
  centre `p` (`Plane.exists_radius_sides`).

A union of convex sets with a common point is polygonally connected by two segments through that
point, which is `isLocallyPolyConnAt_of_star`. The three shapes are then just the three ways the
list of nonempty pieces can come out (one, two adjacent, or two adjacent again with `p` on the
corner) and none of them has to be named.

The passage from one square to finitely many is a shrinking step: since the closed squares are
pairwise disjoint, a point lies in at most one of them, and a small enough neighbourhood of any
point misses all the others outright, so `M` looks locally exactly like the one-square case.

## Blueprint

* `PolyConnIn` — "joined by a polygonal path inside `S`"; the relation Lemma 1.1 produces.
* `IsLocallyPolyConn` — the local form of polygonal connectedness, brick B5's conclusion.
* `polyConnIn_of_convex`, `polyConnIn_union_of_convex` — a rectangle, and two rectangles that
  meet, are polygonally connected.
* `Plane.sideHalfPlane`, `Plane.sideGap` — the four half-planes bounding a square and the room
  between a point and each of them.
* `isLocallyPolyConnAt_compl_openSquare` — the one-square case: the complement of any open
  square is locally polygonally connected, at every point of the plane.
* `isLocallyPolyConn_compl_biUnion` — brick B5: the plane minus finitely many open squares with
  pairwise disjoint closures is locally polygonally connected.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T : Set Plane} {x y z : Plane}

/-! ### Two list lemmas about `poly`

`PolyPath.lean` has `poly_concat`, which extends a vertex list by a single vertex. Transitivity
and symmetry of polygonal connectedness need the two-list versions; both are general facts about
`poly` and belong beside `poly_concat` rather than here. -/

/-- Reversing a vertex list does not move its carrier. -/
theorem poly_reverse : ∀ vs : List Plane, poly vs.reverse = poly vs
  | [] => by simp
  | [v] => by simp
  | u :: v :: tl => by
    rw [List.reverse_cons, poly_concat (by simp) u, poly_reverse (v :: tl),
      List.getLast_reverse (by simp), List.head_cons, poly_cons_cons, segment_symm]
    exact union_comm _ _

/-! ### Polygonal connectedness inside a set -/

/-! ### The local statement -/

/-! ### The four sides of a square -/

/-! ### Choosing one radius for finitely many constraints -/

/-! ### The one-square case -/

/-! ### Finitely many squares -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Drawing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open Metric Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

namespace IsDrawing

/-- Away from the vertices, a point of the drawing lies on exactly one edge. This is the form
the polygonal overlay wants. -/
theorem unique_edge_at (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    {p : Plane} (hpV : p ∉ V(G)) (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    e = f := by
  by_contra hef
  exact hpV (h.arcs_meet_at_vertex he hf hef hpe hpf)

end IsDrawing

/-! ### What a plane graph occupies -/

theorem isConnected_face (h : base ∈ exterior G drawing) :
    IsConnected (face G drawing base) :=
  ⟨⟨base, mem_face h⟩, isPreconnected_connectedComponentIn⟩

end Graph
end

section
-- module Solutions.Q146_CD.OverlayGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-! ### The canonical orientation of a piece -/

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

/-! ### The graph -/

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-- **The overlay graph is a plane graph.** -/
theorem overlayGraph_isDrawing (pieces : List Piece) (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) :
    Graph.IsDrawing (overlayGraph pieces points) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · -- An edge is a nondegenerate segment, and `segmentDrawing` IS its parametrization.
    intro P hP
    have hne : P.Nondeg := overlayPieces_nondeg points hnd P (by simpa using hP)
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact ⟨by simpa using hP, Or.inl ⟨rfl, rfl⟩⟩
  · -- A vertex is an end of some edge, hence a cut point, hence interior to nothing; and a
    -- point of a segment that is not interior to it is one of its ends.
    rintro P a b w ⟨hP, h⟩ hw hwarc
    rw [edgeArc_segmentDrawing] at hwarc
    obtain ⟨R, hR, hwR⟩ := hw
    have hwint : w ∉ P.interior :=
      overlayPieces_avoids hnd w (overlayPieces_ends_cut hEnds R hR w hwR) P hP
    have hend : w = P.1 ∨ w = P.2 := by
      by_contra hcon
      push Not at hcon
      exact hwint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hwarc)
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · -- A common point is an end of both edges: if it were an end of neither it would be
    -- interior to both, and if it were an end of just one it would be a cut point, hence not
    -- interior to the other.
    rintro P Q hP hQ hPQ p hpP hpQ
    rw [overlayGraph_mem_edgeSet] at hP hQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    have key : ∀ A B : Piece, A ∈ overlayPieces pieces points →
        B ∈ overlayPieces pieces points → A ≠ B → p ∈ A.seg → p ∈ B.seg →
        (p = A.1 ∨ p = A.2) := by
      intro A B hA hB hAB hpA hpB
      by_contra hcon
      push Not at hcon
      have hintA : p ∈ A.interior :=
        mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpA
      by_cases hendB : p = B.1 ∨ p = B.2
      · exact overlayPieces_avoids hnd p (overlayPieces_ends_cut hEnds B hB p hendB) A hA hintA
      · push Not at hendB
        have hintB : p ∈ B.interior :=
          mem_openSegment_of_ne_left_right (Ne.symm hendB.1) (Ne.symm hendB.2) hpB
        exact overlayPieces_disjoint_interiors hnd hEnds hMeets hA hB hAB hintA hintB
    have hendP := key P Q hP hQ hPQ hpP hpQ
    have hendQ := key Q P hQ hP (Ne.symm hPQ) hpQ hpP
    exact ⟨⟨P, hP, hendP⟩, overlayGraph_inc hP hendP, overlayGraph_inc hQ hendQ⟩

/-- What the graph occupies is what its edges occupy: every vertex is an end of an edge, so
the vertices add nothing. -/
theorem overlayGraph_pointSet (pieces : List Piece) (points : List Plane) :
    Graph.pointSet (overlayGraph pieces points) segmentDrawing = cover pieces := by
  rw [← overlayPieces_cover pieces points]
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, overlayGraph_vertexSet,
    endSet, mem_setOf_eq, overlayGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SimpleArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.mem_vertexSet_induce_component _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-- A cut point on the union is a vertex: it lies on some edge, and a cut point is interior to
no edge, so it is one of that edge's two ends. -/
theorem overlayGraph_mem_vertexSet_of_mem_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hxp : x ∈ points) (hx : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hx
  simp only [cover, mem_iUnion, exists_prop] at hx
  obtain ⟨P, hP, hxP⟩ := hx
  have hint : x ∉ P.interior := overlayPieces_avoids hnd x hxp P hP
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-- **The overlay graph of a connected union is connected**, in the form the construction
needs: any vertex reaches any other.

The proof is a clopen argument in the plane. Split the edges into those whose ends the walk
relation reaches from `a` and those it does not; each class carries a compact set, the two
carried sets cover the union, and they are disjoint — a common point would, by the drawing
condition, be a vertex incident with an edge of each class, and incidence is reachability.
Preconnectedness then leaves the second class carrying nothing. -/
theorem overlayGraph_reaches (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    (hap : a ∈ points) (hbp : b ∈ points) (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    (overlayGraph pieces points).Reaches a b := by
  classical
  have hdraw : Graph.IsDrawing (overlayGraph pieces points) segmentDrawing :=
    overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have haV : a ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hap ha
  have hbV : b ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hbp hb
  -- Every edge carries a link between its two ends; this is the only fact about the graph
  -- used below beyond the drawing condition.
  have hlink : ∀ P ∈ overlayPieces pieces points,
      (overlayGraph pieces points).IsLink P P.1 P.2 := fun P hP =>
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  -- The two classes of edges, and the point sets they carry.
  set S : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      (overlayGraph pieces points).Reaches a P.1}, P.seg with hS
  set T : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      ¬ (overlayGraph pieces points).Reaches a P.1}, P.seg with hT
  have hSclosed : IsClosed S :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  have hTclosed : IsClosed T :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  -- The two classes carry the whole union between them.
  have hunion : ∀ z ∈ cover pieces, z ∈ S ∨ z ∈ T := by
    intro z hz
    rw [← overlayPieces_cover pieces points] at hz
    simp only [cover, mem_iUnion, exists_prop] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    by_cases hr : (overlayGraph pieces points).Reaches a P.1
    · exact Or.inl (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
    · exact Or.inr (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
  -- And they carry disjoint sets: a common point is a vertex incident with an edge of each.
  have hdisj : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    simp only [hS, hT, mem_iUnion, mem_setOf_eq, exists_prop] at hzS hzT
    obtain ⟨P, ⟨hP, hPr⟩, hzP⟩ := hzS
    obtain ⟨Q, ⟨hQ, hQr⟩, hzQ⟩ := hzT
    have hPQ : P ≠ Q := by rintro rfl; exact hQr hPr
    obtain ⟨-, hincP, hincQ⟩ := hdraw.edge_inter (overlayGraph_mem_edgeSet.2 hP)
      (overlayGraph_mem_edgeSet.2 hQ) hPQ
      (by rwa [edgeArc_segmentDrawing]) (by rwa [edgeArc_segmentDrawing])
    have hzendP : z = P.1 ∨ z = P.2 := hincP.eq_or_eq_of_isLink (hlink P hP)
    have hzendQ : z = Q.1 ∨ z = Q.2 := hincQ.eq_or_eq_of_isLink (hlink Q hQ)
    exact hQr ((overlayGraph_reaches_end hQ hzendQ).2
      ((overlayGraph_reaches_end hP hzendP).1 hPr))
  -- `a` is carried by the reachable class, so that class is nonempty.
  have haS : a ∈ S := by
    obtain ⟨P, hP, hend⟩ := id haV
    refine mem_biUnion (show P ∈ _ from
      ⟨hP, (overlayGraph_reaches_end hP hend).2 (Graph.Reaches.refl haV)⟩) ?_
    rcases hend with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  -- Preconnectedness: the far class carries nothing that the union contains.
  have hbS : b ∈ S := by
    by_contra hbnot
    have hbT : b ∈ T := (hunion b hb).resolve_left hbnot
    have hsub : cover pieces ⊆ Tᶜ ∪ Sᶜ := by
      intro w hw
      rcases hunion w hw with h | h
      · exact Or.inl fun h' => hdisj w h h'
      · exact Or.inr fun h' => hdisj w h' h
    obtain ⟨z, hzc, hzT, hzS⟩ := hconn Tᶜ Sᶜ hTclosed.isOpen_compl hSclosed.isOpen_compl
      hsub ⟨a, ha, fun h => hdisj a haS h⟩ ⟨b, hb, fun h => hdisj b h hbT⟩
    exact (hunion z hzc).elim hzS hzT
  -- `b` is a vertex on an edge of the reachable class, hence an end of it.
  simp only [hS, mem_iUnion, mem_setOf_eq, exists_prop] at hbS
  obtain ⟨P, ⟨hP, hPr⟩, hbP⟩ := hbS
  have hbend : b = P.1 ∨ b = P.2 :=
    hdraw.vertex_mem_edgeArc (hlink P hP) hbV (by rwa [edgeArc_segmentDrawing])
  exact (overlayGraph_reaches_end hP hbend).1 hPr

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-- **Lemma 1.2 (finite polygonal unions).** If a finite union of nondegenerate segments is
connected, any two distinct points of it are joined inside it by a *simple* polygonal arc.

The arc is returned as a vertex list, not merely as a set: the consumers that overlay it with
another polygonal object need its vertices, and an existential over sets would not give them
back. -/
theorem exists_simple_poly_of_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces)) (hab : a ≠ b)
    (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      poly vs ⊆ cover pieces ∧ IsArcBetween (poly vs) a b := by
  classical
  -- Put the two endpoints on the cut list, so that they become vertices of the overlay. The
  -- two cut conditions ask only that certain points occur in the list, so this is free.
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points pieces
  set pts : List Plane := a :: b :: pts₀ with hpts
  have hEnds : EndsAreCut pieces pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut pieces pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨u, v, huv, by simp [hpts, hu], by simp [hpts, hv]⟩
  have hdraw : Graph.IsDrawing (overlayGraph pieces pts) segmentDrawing :=
    overlayGraph_isDrawing pieces pts hnd hEnds hMeets
  -- A walk from `a` to `b`, thinned to a path.
  have hreach : (overlayGraph pieces pts).Reaches a b :=
    overlayGraph_reaches hnd hconn hEnds hMeets (by simp [hpts]) (by simp [hpts]) ha hb
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hab hpath.isWalk.eq_of_nil
  -- Its realisation is an arc, and it is the carrier of a vertex list.
  have harc : IsArcBetween (Graph.edgesCover segmentDrawing W) a b :=
    hdraw.path_isArcBetween hpath hWne
  obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := exists_poly_eq_edgesCover hpath.isWalk hWne
  refine ⟨vs, hvs, hhead, hlast, ?_, ?_⟩
  · rw [hpoly, ← overlayGraph_pointSet pieces pts]
    exact Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he
  · rw [hpoly]; exact harc

/-- **Lemma 1.2**, for a set presented as a polygonal chain. -/
theorem exists_simple_poly_of_poly {vs : List Plane} (hconn : IsPreconnected (poly vs))
    (hab : a ≠ b) (ha : a ∈ poly vs) (hb : b ∈ poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ poly vs ∧ IsArcBetween (poly ws) a b := by
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  have := exists_simple_poly_of_cover (segsOf_nondeg vs) (hcov ▸ hconn) hab
    (hcov ▸ ha) (hcov ▸ hb)
  rwa [hcov] at this

/-- **Lemma 1.2**, for a set given only as polygonal. -/
theorem exists_simple_poly_of_isPolygonal {A : Set Plane} (hA : IsPolygonal A)
    (hconn : IsPreconnected A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ A ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨vs, rfl⟩ := hA
  exact exists_simple_poly_of_poly hconn hab ha hb

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

/-- **Lemma 1.2 (finite polygonal unions).** A connected finite union of polygonal chains joins
any two of its distinct points by a simple polygonal arc inside it. -/
theorem exists_simple_poly_of_biUnion {L : List (List Plane)}
    (hconn : IsPreconnected (⋃ vs ∈ L, poly vs)) (hab : a ≠ b)
    (ha : a ∈ ⋃ vs ∈ L, poly vs) (hb : b ∈ ⋃ vs ∈ L, poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ vs ∈ L, poly vs) ∧ IsArcBetween (poly ws) a b := by
  classical
  have hnd : ∀ P ∈ L.flatMap segsOf, P.Nondeg := by
    intro P hP
    obtain ⟨vs, -, hPvs⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg vs P hPvs
  have hcovsub : ∀ vs : List Plane, cover (segsOf vs) ⊆ poly vs := by
    intro vs
    rcases cover_segsOf vs with h | ⟨h, -⟩
    · exact h.subset
    · rw [h, cover_nil]; exact empty_subset _
  have hflat : cover (L.flatMap segsOf) = ⋃ vs ∈ L, cover (segsOf vs) :=
    cover_flatMap_list segsOf L
  have hsub : cover (L.flatMap segsOf) ⊆ ⋃ vs ∈ L, poly vs := by
    rw [hflat]
    exact iUnion₂_mono fun vs _ => hcovsub vs
  -- What the segments miss is finitely many collapsed members.
  have hdiff : ((⋃ vs ∈ L, poly vs) \ cover (L.flatMap segsOf)).Finite := by
    have hsmall : ∀ vs : List Plane, (poly vs \ cover (segsOf vs)).Subsingleton := by
      intro vs
      rcases cover_segsOf vs with h | ⟨-, h⟩
      · rw [h]; simp
      · exact h.anti Set.sdiff_subset
    refine (Set.Finite.biUnion L.finite_toSet
      fun vs _ => (hsmall vs).finite).subset ?_
    rintro z ⟨hzU, hzC⟩
    simp only [mem_iUnion, exists_prop] at hzU
    obtain ⟨vs, hvs, hz⟩ := hzU
    refine mem_biUnion hvs ⟨hz, fun hmem => hzC ?_⟩
    rw [hflat]
    exact mem_biUnion hvs hmem
  have hclosed : IsClosed (cover (L.flatMap segsOf)) :=
    Set.Finite.isClosed_biUnion (L.flatMap segsOf).finite_toSet fun P _ =>
      (isCompact_segment P.1 P.2).isClosed
  have heq : cover (L.flatMap segsOf) = ⋃ vs ∈ L, poly vs :=
    subset_antisymm hsub (subset_of_finite_diff hconn hclosed hdiff ha hb hab)
  have := exists_simple_poly_of_cover hnd (heq ▸ hconn) hab (heq ▸ ha) (heq ▸ hb)
  rwa [heq] at this

/-- **Lemma 1.1 (polygonal connectedness), in full.** Any two distinct points of a region are
joined in it by a *simple* polygonal arc.

`Schoenflies.exists_poly_of_isPreconnected` supplies a polygonal path; Lemma 1.2 extracts a
simple arc from its carrier. -/
theorem exists_simple_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = x ∧ vs.getLast h = y ∧
      poly vs ⊆ Ω ∧ IsArcBetween (poly vs) x y := by
  obtain ⟨us, hus, hsub, hhead, hlast⟩ := exists_poly_of_isPreconnected hΩ hconn hx hy
  have hxu : x ∈ poly us := hhead ▸ head_mem_poly hus
  have hyu : y ∈ poly us := hlast ▸ getLast_mem_poly hus
  obtain ⟨vs, hvs, h1, h2, h3, h4⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hus).2 hxy hxu hyu
  exact ⟨vs, hvs, h1, h2, h3.trans hsub, h4⟩

/-- **Lemma 1.1**, in set form: a simple polygonal arc inside the region between any two of
its points. -/
theorem exists_simple_arc_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ A ⊆ Ω, IsPolygonal A ∧ IsArcBetween A x y := by
  obtain ⟨vs, -, -, -, hsub, harc⟩ := exists_simple_poly_of_isPreconnected hΩ hconn hx hy hxy
  exact ⟨poly vs, hsub, ⟨vs, rfl⟩, harc⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.AccessibleJoin
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Joining accessible boundary points

Two boundary points of a region that are each reachable by a polygonal arc from inside can be
joined by a *single* simple polygonal arc whose interior stays inside the region. This is
`lem:accessible-endpoints`, and the same extraction — applied to a finite polygonal skeleton
rather than to a pair of access arcs — is `lem:skeleton-crosscuts`.

## The predicate

`Schoenflies.PolyAccessible Ω a` says that `a` admits a *polygonal access arc* from `Ω`: a
vertex list starting at `a`, ending inside `Ω`, all of whose points other than `a` lie in `Ω`.

The definition deliberately does **not** ask the access arc to be simple. A consumer that has
only a self-crossing approach path can still supply the hypothesis, and nothing is lost: the
extraction below re-runs `lem:finite-polygonal-union` on the whole union anyway, so simplicity
of the input is never used. `PolyAccessible.exists_simple` recovers the blueprint's literal
phrasing (*a simple polygonal arc from `a` to a point of `Ω`*) for a point off `Ω`, so the two
readings agree where the blueprint uses them.

Note also that neither the definition nor the theorems below mention `frontier Ω`. The
blueprint states `lem:accessible-endpoints` for `a, b ∈ ∂Ω`, but boundary membership plays no
role in the proof — only `a ≠ b` does — so the statements here are the stronger ones with the
hypothesis dropped. A consumer holding `a, b ∈ ∂Ω` simply does not pass it.

## The method, and where the difficulty actually is

Take an access arc from `a` and one from `b`, join their far ends inside `Ω` by
`lem:polygonal-connected` (`Schoenflies.exists_poly_of_isPreconnected`), and extract a simple
arc from the resulting three-piece polygonal union by `lem:finite-polygonal-union`
(`Schoenflies.exists_simple_poly_of_union`).

The whole content is that the extraction must keep the two endpoints and must keep everything
else inside `Ω`. Both are free from the interface actually on `main`:
`Schoenflies.exists_simple_poly_of_union` already returns a vertex list whose `head` is `a` and
whose `getLast` is `b`, together with `IsArcBetween _ a b`, so the endpoints are pinned; and it
returns the arc as a *subset of the union it was extracted from*, so `poly ws \ {a, b} ⊆ Ω`
follows from the same inclusion for the union. No endpoint-pinning lemma had to be added.

What *was* missing is a version of the extraction indexed by an arbitrary finite family rather
than by a `List (Set Plane)`: a skeleton arrives as a finite set of edges, and turning it into a
list at the call site is noise. `Schoenflies.exists_simple_poly_of_biUnion_finite` is that
version and belongs beside `Schoenflies.exists_simple_poly_of_union` in
`Schoenflies/SimpleArc.lean`.

## Blueprint

* `Schoenflies.PolyAccessible` — "admitting a polygonal access arc from `Ω`", the hypothesis of
  `lem:accessible-endpoints`.
* `Schoenflies.PolyAccessible.of_openSegment`, `Schoenflies.StronglyAccessible.polyAccessible`,
  `Schoenflies.polyAccessible_of_poly`, `Schoenflies.polyAccessible_of_poly'` — the ways the
  construction produces the hypothesis: a straight access segment, Definition 8.1 (strong
  accessibility), and a chain already known to run into `Ω` from either of its ends.
* `Schoenflies.PolyAccessible.exists_simple` — the blueprint's literal reading of the
  hypothesis, for a point off `Ω`.
* `Schoenflies.exists_simple_poly_of_biUnion_finite`,
  `Schoenflies.exists_simple_arc_of_biUnion_finite`, `Schoenflies.exists_simple_poly_pinned`,
  `Schoenflies.exists_simple_poly_of_isPolygonal_pinned` — `lem:finite-polygonal-union` over a
  finite family, and with the "off the endpoints, stay in the region" clause attached. These
  four belong in `Schoenflies/SimpleArc.lean`.
* `Graph.pointSet_eq_biUnion`, `Graph.exists_simple_poly_of_pointSet` — the same extraction on
  the point set of a finite plane graph with polygonal edges, which is the shape a skeleton
  stage arrives in. Root `Graph` namespace, per the convention of `Schoenflies/Graph/*`.
* `Schoenflies.exists_simple_poly_of_polyAccessible`,
  `Schoenflies.exists_simple_arc_of_polyAccessible` — `lem:accessible-endpoints`.
* `Schoenflies.exists_crosscut_of_polyAccessible` — `lem:accessible-endpoints` in crosscut form:
  when `Ω` misses a set `C` carrying `a` and `b`, the arc meets `C` exactly at its endpoints.
* `Schoenflies.exists_crosscut_of_biUnion_finite`,
  `Schoenflies.exists_crosscut_arc_of_biUnion_finite` — `lem:skeleton-crosscuts`, the extraction
  step: a connected finite polygonal union meeting `C` in exactly two points carries a simple
  polygonal crosscut between them.

`lem:skeleton-crosscuts` has two further halves that are **not** here, because the objects they
speak about are not yet in Lean: the construction of the connected union `Y = e_a ∪ |Λ| ∪ e_b`
from a finite stage of the skeleton, and the transport of the crosscut through the finite
skeleton homeomorphism. Both need the stage/anchor machinery of §"Continuity at the Jordan
curve"; the extraction between them is what this module supplies.
-/

open Metric Set

namespace Schoenflies

variable {Ω C D S : Set Plane} {a b z : Plane}

/-! ### Polygonal accessibility -/

/-- **The constructor a consumer holding an arc should use.** A chain that starts at `a`, ends
somewhere else, and has all of its other points in `Ω` is an access arc.

This is the converse direction of `lem:accessible-endpoints`: the arc that lemma produces makes
both of its endpoints accessible again, which is what an induction that extends a partial
construction one crosscut at a time needs. -/
theorem polyAccessible_of_poly {vs : List Plane} (h : vs ≠ []) (hhead : vs.head h = a)
    (hlast : vs.getLast h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a :=
  ⟨vs, h, hhead, hsub ⟨getLast_mem_poly h, hlast⟩, hsub⟩

/-- `Schoenflies.polyAccessible_of_poly` read from the far end: reversing the chain moves the
distinguished endpoint from the head to the last vertex. -/
theorem polyAccessible_of_poly' {vs : List Plane} (h : vs ≠ []) (hlast : vs.getLast h = a)
    (hhead : vs.head h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a := by
  have hrev : vs.reverse ≠ [] := by simpa using h
  refine polyAccessible_of_poly hrev ?_ ?_ ?_
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhead
  · rw [poly_reverse]; exact hsub

/-! ### `lem:finite-polygonal-union` over a finite family

`Schoenflies.exists_simple_poly_of_union` takes the union as a `List (Set Plane)`. A skeleton
arrives as a finite *set* of edges, so the list is pure friction at the call site. This
paragraph removes it; it belongs in `Schoenflies/SimpleArc.lean`. -/

/-- `Schoenflies.exists_simple_poly_pinned` for a union presented as one polygonal set. -/
theorem exists_simple_poly_of_isPolygonal_pinned {Y E : Set Plane} (hY : IsPolygonal Y)
    (hconn : IsPreconnected Y) (hab : a ≠ b) (ha : a ∈ Y) (hb : b ∈ Y) (hS : Y \ E ⊆ S) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ Y ∧ poly ws \ E ⊆ S ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_isPolygonal hY hconn hab ha hb
  exact ⟨ws, hws, hhead, hlast, hsub, fun x hx => hS ⟨hsub hx.1, hx.2⟩, harc⟩

/-! ### `lem:skeleton-crosscuts`: the extraction step

The blueprint's proof of `lem:skeleton-crosscuts` builds, from a finite stage of the skeleton, a
connected finite union `Y = e_a ∪ |Λ| ∪ e_b` of polygonal arcs with `Y ∩ C = {a, b}`, and then
says: *subdivide `Y` at its finitely many vertices; the resulting finite graph is connected, so
it contains a simple graph path `P` from `a` to `b`, as in the proof of
`lem:finite-polygonal-union`; this path meets `C` only at its endpoints and is therefore a
polygonal crosscut.* That last step is what this paragraph is. The construction of `Y` from the
skeleton needs the stage machinery and is not here. -/

/-! ### `lem:accessible-endpoints` -/

/-- **`lem:accessible-endpoints`: accessible endpoints can be joined.** Let `Ω` be a region and
`a ≠ b` two points each admitting a polygonal access arc from `Ω`. Then there is a simple
polygonal arc from `a` to `b` whose remaining points lie in `Ω`.

The arc is returned as a vertex list with its two ends displayed, matching
`Schoenflies.exists_simple_poly_of_union`: the consumers that overlay this arc with another
polygonal object need the vertices, not merely the set.

`a` and `b` are *not* required to lie on `frontier Ω`; the proof never uses it. -/
theorem exists_simple_poly_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨as, has, hahead, halast, haint⟩ := ha
  obtain ⟨bs, hbs, hbhead, hblast, hbint⟩ := hb
  -- Join the two far ends inside the region.
  obtain ⟨ms, hms, hmsub, hmhead, hmlast⟩ :=
    exists_poly_of_isPreconnected hΩ hconn halast hblast
  -- The three chains form a connected union: consecutive ones share a far end.
  set U : Set Plane := poly as ∪ (poly ms ∪ poly bs) with hU
  have hlist : (⋃ vs ∈ [as, ms, bs], poly vs) = U := by
    rw [biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs), hU]
    simp
  have hconnU : IsPreconnected U := by
    refine (IsConnected.union ?_ (isConnected_poly has) (IsConnected.union ?_
      (isConnected_poly hms) (isConnected_poly hbs))).2
    · exact ⟨as.getLast has, getLast_mem_poly has,
        Or.inl (hmhead ▸ head_mem_poly hms)⟩
    · exact ⟨ms.getLast hms, getLast_mem_poly hms, hmlast ▸ getLast_mem_poly hbs⟩
  -- Off `{a, b}` the union is inside `Ω`, one piece at a time.
  have hUΩ : U \ {a, b} ⊆ Ω := by
    rintro x ⟨hx, hxab⟩
    rcases hx with hx | hx | hx
    · exact haint ⟨hx, fun hxa => hxab (Or.inl (hahead ▸ hxa))⟩
    · exact hmsub hx
    · exact hbint ⟨hx, fun hxb => hxab (Or.inr (hbhead ▸ hxb))⟩
  have haU : a ∈ U := Or.inl (hahead ▸ head_mem_poly has)
  have hbU : b ∈ U := Or.inr (Or.inr (hbhead ▸ head_mem_poly hbs))
  obtain ⟨ws, hws, hwhead, hwlast, hwsub, hwarc⟩ :=
    exists_simple_poly_of_biUnion (L := [as, ms, bs]) (hlist ▸ hconnU) hab
      (hlist ▸ haU) (hlist ▸ hbU)
  rw [hlist] at hwsub
  exact ⟨ws, hws, hwhead, hwlast, fun x hx => hUΩ ⟨hwsub hx.1, hx.2⟩, hwarc⟩

/-- **`lem:accessible-endpoints` in crosscut form.** If the region `Ω` misses a set `C` that
carries the two accessible points, the joining arc meets `C` exactly at its endpoints. With `C`
a Jordan curve and `Ω` its interior this says the arc is a polygonal crosscut. -/
theorem exists_crosscut_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hdisj : Disjoint Ω C) (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b ∧ poly ws ∩ C = {a, b} := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  refine ⟨ws, hws, hhead, hlast, hsub, harc, subset_antisymm ?_ ?_⟩
  · -- A point of the arc off `{a, b}` lies in `Ω`, which misses `C`.
    rintro x ⟨hxw, hxC⟩
    by_contra hxab
    exact (hdisj.ne_of_mem (hsub ⟨hxw, hxab⟩) hxC) rfl
  · rintro x (rfl | rfl)
    exacts [⟨hhead ▸ head_mem_poly hws, haC⟩, ⟨hlast ▸ getLast_mem_poly hws, hbC⟩]

end Schoenflies

/-! ### The extraction on the point set of a finite polygonal plane graph

A skeleton stage arrives as a plane graph, and what the crosscut is extracted from is its point
set. Splitting that into "one singleton per vertex, one arc per edge" is the only step between
`Schoenflies.exists_simple_poly_of_biUnion_finite` and the graph, so it is done once here.

Following the convention of `Schoenflies/Graph/*`, these live in the root `Graph` namespace. -/
end

section
-- module Solutions.Q146_CD.CrosscutAtMostTwo
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A crosscut cuts a region into at most two pieces

Lemma "At most two sides": if `D` is a region and `P` is a simple polygonal arc whose endpoints
lie *outside* `D` and whose remaining points lie in `D`, then `D ∖ P` has at most two
components. This is the missing half of the crosscut theorem — the crosscut-cells lemma
(`Schoenflies.crosscut_cells`) already exhibits two components, and this says there are no
others.

## "At most two" as a covering statement

Nothing here talks about the *set* of components. What is proved, and what the crosscut theorem
consumes, is the constructive form: two points `z_L, z_R` of `D ∖ P` such that every point of
`D ∖ P` lies in the component of one of them (`crosscut_at_most_two`). Handed two components
that are known to be distinct — which is exactly what the crosscut-cells lemma supplies — that
turns into "every point lies in one of *those* two" (`crosscut_components_exhaust`), which is
the sentence the crosscut theorem actually needs.

## The proof is a clopen argument, not the blueprint's path argument

The blueprint traces a polygonal arc `γ` from an arbitrary `x ∈ D ∖ P` to a reference point
`z₀ ∈ P`, takes the first point `z` of `γ` on `P`, and pushes `x` into a track of a strip around
the subarc of `P` from `z` to `z₀`. The first-hitting-point step is only there to *find* a point
of `D ∖ P` next to `P`; once one knows that a whole neighbourhood of every point of `P ∩ D` is
covered by the two components, the statement is a connectedness argument and no path is needed:

* `T`, the set of points of `D ∖ P` in neither of the two components, is open, because a
  component of an open subset of the plane is open and two components are equal or disjoint
  (`isOpen_notMem_two_components`);
* `U`, the union of the two components with every open piece of `D` whose complement of `P` is
  covered, is open and contains all of `P ∩ D`;
* `U` and `T` are disjoint, cover `D`, and `U` meets `D`; so `T = ∅` because `D` is connected.

That is `covered_by_two_of_local`, and it is where "at most two" really comes from. The arc, the
polygonality and the endpoint hypotheses enter only through the collar.

## The collar is a hypothesis: `Schoenflies/Strip.lean` is stated for a closed curve

The local input the argument needs is blueprint Lemma 1.8 (b) — a two-sided collar of a compact
subarc of `P ∖ ∂P`. `Schoenflies/Strip.lean`, `Schoenflies/StripLocal.lean` and
`Schoenflies/Compose.lean` build the collar of a `ClosedPolygon`, a *closed* curve, and the note
at the end of `StripLocal.lean` says in as many words that the arc case "is not formalised".
There is no way to get it from the closed case: the two tracks of a closed collar are connected
because they run all the way round the curve, and intersecting them with `D` destroys exactly
that.

So `HasArcCollars D P` is an explicit hypothesis of every theorem below. It is blueprint
Lemma 1.8 (b) with the prescribed open set taken to be `D`, together with the "local sides"
clause of that lemma in the form `StripLocal.lean` already proves in the closed case
(`StripData.carrier_subset_closure_sideL`): every point of the subarc is in the closure of both
tracks. `ArcCollar` is the bundled datum, so a discharger returns a construction rather than an
existential.

## Blueprint

* `Schoenflies.ArcCollar`, `Schoenflies.HasArcCollars` — Lemma 1.8 (b) (two-sided polygonal
  strips, the arc case) as an interface: the collar of one compact subarc as data, and the
  hypothesis that every compact subarc has one.
* `Schoenflies.isOpen_notMem_two_components`, `Schoenflies.covered_by_two_of_local` — the clopen
  step, which is the whole of the lemma once the collar is available.
* `Schoenflies.crosscut_at_most_two` — Lemma "At most two sides".
* `Schoenflies.crosscut_components_exhaust` — the same, applied to two components already known
  to be distinct; this is the form Theorem "Crosscut theorem" cites.
* `Schoenflies.Plane.mem_segment_iff_coord`, `Schoenflies.hasArcCollars_segment` — Lemma 1.8 (b)
  for a straight crosscut, which is the blueprint's edge block and nothing else. With it,
  `Schoenflies.segment_crosscut_at_most_two` is Lemma "At most two sides" for a straight
  crosscut with no hypothesis left standing, and certifies that `HasArcCollars` is satisfiable.
-/

open Metric Set unitInterval

namespace Schoenflies

variable {D P K K' : Set Plane}

/-! ### The collar of a compact subarc, as data

Blueprint Lemma 1.8 (b). `nbhd` is the neighbourhood `N`, `left` and `right` are the two tracks
`N_L, N_R`. The prescribed open set of the blueprint is `D`, which is all this development ever
prescribes.

Two clauses of the blueprint are dropped because nothing here uses them: that the tracks are
open and that they are disjoint. Two are kept and are essential: that each track is *connected*
— that is the whole point of a collar, and it is what ties the local picture at one point of the
arc to the local picture at another — and that every point of the subarc is in the closure of
both tracks, which is the blueprint's "the two sets `N_L, N_R` are the two local sides of the
curve" in the form `StripLocal.lean` proves it for a closed polygon. -/

/-- **Blueprint Lemma 1.8 (b) as a hypothesis.** Every nondegenerate compact connected piece of
`P` lying inside `D` has a two-sided collar inside `D`.

A compact connected subset of an arc is a compact subarc, so this is the blueprint's "if `P` is
an arc and `K` is a compact subarc of `P ∖ ∂P`" — the condition `K ⊆ D ∩ P` is what "`K` avoids
the endpoints" amounts to here, since the endpoints of a crosscut are outside `D`.

Nondegeneracy is asked for because the blueprint's proof builds the collar out of edge blocks
and vertex disks along `K`, which needs `K` to contain an edge; a consumer that has a genuine
subarc always has it. -/
def HasArcCollars (D P : Set Plane) : Prop :=
  ∀ K : Set Plane, K ⊆ D ∩ P → IsCompact K → IsPreconnected K → K.Nontrivial →
    Nonempty (ArcCollar D P K)

namespace ArcCollar

theorem left_subset_nbhd_diff (C : ArcCollar D P K) : C.left ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_left

theorem right_subset_nbhd_diff (C : ArcCollar D P K) : C.right ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_right

theorem nbhd_diff_subset_diff (C : ArcCollar D P K) : C.nbhd \ P ⊆ D \ P :=
  fun _ hy => ⟨C.nbhd_subset hy.1, hy.2⟩

theorem left_subset_diff (C : ArcCollar D P K) : C.left ⊆ D \ P :=
  C.left_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

theorem right_subset_diff (C : ArcCollar D P K) : C.right ⊆ D \ P :=
  C.right_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

/-- The reference point on the left of the arc. Exported as a function of the collar rather
than produced by an existential, so that a consumer holding a collar holds the point. -/
noncomputable def ptL (C : ArcCollar D P K) : Plane := C.isConnected_left.nonempty.some

/-- The reference point on the right of the arc. -/
noncomputable def ptR (C : ArcCollar D P K) : Plane := C.isConnected_right.nonempty.some

theorem ptL_mem (C : ArcCollar D P K) : C.ptL ∈ C.left := C.isConnected_left.nonempty.some_mem

theorem ptR_mem (C : ArcCollar D P K) : C.ptR ∈ C.right := C.isConnected_right.nonempty.some_mem

theorem ptL_mem_diff (C : ArcCollar D P K) : C.ptL ∈ D \ P := C.left_subset_diff C.ptL_mem

theorem ptR_mem_diff (C : ArcCollar D P K) : C.ptR ∈ D \ P := C.right_subset_diff C.ptR_mem

/-- A connected piece of `D ∖ P` that meets the neighbourhood of a collar lies in one of the
two components that collar's reference points name.

The piece meets `nbhd` in a point off `P`, which is therefore in one of the two tracks; the
piece and that track together are connected inside `D ∖ P` and contain the corresponding
reference point. -/
theorem meeting_subset_components (C₀ : ArcCollar D P K') {S : Set Plane}
    (hS : IsPreconnected S) (hSsub : S ⊆ D \ P) (hmeet : (C₀.nbhd ∩ S).Nonempty) :
    S ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  obtain ⟨y, hy₀, hyS⟩ := hmeet
  have hy : y ∈ C₀.left ∪ C₀.right := by
    rw [← C₀.nbhd_diff]; exact ⟨hy₀, (hSsub hyS).2⟩
  rcases hy with hy | hy
  · refine subset_union_of_subset_left ?_ _
    have hconn : IsPreconnected (S ∪ C₀.left) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_left.2
    have hsub : S ∪ C₀.left ⊆ D \ P := union_subset hSsub C₀.left_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptL_mem) hsub (Or.inl hz)
  · refine subset_union_of_subset_right ?_ _
    have hconn : IsPreconnected (S ∪ C₀.right) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_right.2
    have hsub : S ∪ C₀.right ⊆ D \ P := union_subset hSsub C₀.right_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptR_mem) hsub (Or.inl hz)

/-- **The whole of a second collar is covered by the two components named by the first**, as
soon as the two subarcs share a point.

Both tracks of `C` approach the shared point `z`, and `C₀.nbhd` is an open neighbourhood of it,
so each track of `C` meets `C₀.nbhd`; `meeting_subset_components` then places each of them in
one of the two components. This is the blueprint's "one track meets `B_L` and the other meets
`B_R`", with the two half-disks replaced by the fixed collar. -/
theorem nbhd_diff_subset_components (C₀ : ArcCollar D P K') (C : ArcCollar D P K)
    {z : Plane} (hz' : z ∈ K') (hz : z ∈ K) :
    C.nbhd \ P ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  have hmeetL : (C₀.nbhd ∩ C.left).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_left hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  have hmeetR : (C₀.nbhd ∩ C.right).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_right hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  rw [C.nbhd_diff]
  exact union_subset
    (C₀.meeting_subset_components C.isConnected_left.2 C.left_subset_diff hmeetL)
    (C₀.meeting_subset_components C.isConnected_right.2 C.right_subset_diff hmeetR)

end ArcCollar

/-! ### The clopen step -/

/-! ### Lemma "At most two sides" -/

/-- **Lemma "At most two sides".** Let `D` be a region and `P` a simple polygonal arc whose
endpoints `a, b` lie outside `D` and whose remaining points lie in `D`. Then there are two
points `z_L, z_R` of `D ∖ P` such that every point of `D ∖ P` lies in the component of one of
them — that is, `D ∖ P` has at most two components.

`IsPolygonal P` is carried because the blueprint statement carries it, and because it is what
makes `HasArcCollars` discharge­able; this proof does not use it, since all the geometry is
inside the collar.

The reference points are the two reference points of the collar of the middle third of the arc:
`K₀ = f '' [1/4, 3/4]` for a parametrisation `f` of `P`. Any other nondegenerate compact subarc
would do, and `ArcCollar.nbhd_diff_subset_components` is stated so that a consumer that has a
collar of its own can use *its* reference points instead. -/
theorem crosscut_at_most_two {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (_hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  have hPclosed : IsClosed P := hP.isArc.isClosed
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := hP
  -- The part of the arc inside the region is exactly its interior, because its two endpoints
  -- are outside `D` and everything else is inside.
  have hDPeq : D ∩ P = f '' Ioo 0 1 := by
    have hdiff : P \ {a, b} = f '' Ioo 0 1 := by
      rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
      rfl
    rw [← hdiff]
    ext y
    simp only [mem_inter_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hyD, hyP⟩ => ⟨hyP, ?_⟩, fun ⟨hyP, hy⟩ => ⟨hPD ⟨hyP, by simpa using hy⟩, hyP⟩⟩
    rintro (rfl | rfl)
    exacts [ha hyD, hb hyD]
  -- Every nondegenerate closed parameter interval inside `(0, 1)` names an admissible subarc.
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 → Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ I := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
    refine hcollars _ (by rw [hDPeq]; exact image_mono hsubIoo)
      (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s, mem_image_of_mem f hsI, f t, mem_image_of_mem f htI, fun h => ?_⟩
    exact absurd (hi (hsubI hsI) (hsubI htI) h) (ne_of_lt hst)
  -- The fixed collar, around the middle half of the arc.
  obtain ⟨C₀⟩ := hsubarc (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1 / 2) ∈ f '' Icc (1 / 4 : ℝ) (3 / 4) :=
    mem_image_of_mem f ⟨by norm_num, by norm_num⟩
  refine ⟨C₀.ptL, C₀.ptL_mem_diff, C₀.ptR, C₀.ptR_mem_diff, fun x hx => ?_⟩
  refine covered_by_two_of_local hDopen hDconn hPclosed C₀.ptL_mem_diff (fun w hw => ?_) hx
  -- For a point `w` of the arc inside `D`, take the subarc that joins it to the middle half:
  -- its collar is a neighbourhood of `w` and shares the point `f (1/2)` with the fixed one.
  rw [hDPeq] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨C⟩ := hsubarc (min u (1 / 4)) (max u (3 / 4))
    (lt_min hu.1 (by norm_num)) (by have := min_le_right u (1 / 4 : ℝ)
                                    have := le_max_right u (3 / 4 : ℝ)
                                    linarith)
    (max_lt hu.2 (by norm_num))
  refine ⟨C.nbhd, C.isOpen_nbhd,
    C.subset_nbhd (mem_image_of_mem f ⟨min_le_left _ _, le_max_left _ _⟩), C.nbhd_subset, ?_⟩
  exact C₀.nbhd_diff_subset_components C hz₀
    (mem_image_of_mem f ⟨le_trans (min_le_right _ _) (by norm_num),
      le_trans (by norm_num) (le_max_right _ _)⟩)

/-! ### The collar hypothesis is not vacuous: a straight crosscut

The collar of a *straight* crosscut is a rectangle, and the free-standing frame toolkit of
`Schoenflies/Strip.lean` — `coordAlong`, `coordAcross`, `strip`, `isOpen_strip`, `convex_strip`,
`dist_foot`, `frame_decomp` — builds it directly, with no cyclic vertex family in sight. So
`HasArcCollars` is discharged outright in the simplest crosscut configuration, and
`segment_crosscut_at_most_two` below is a hypothesis-free instance of the lemma.

This is the shape a general discharger has to reproduce along a chain of edges: it is exactly
the blueprint's edge block, and what is missing is the vertex disks between consecutive blocks
and the end cross-sections. -/

/-- **Lemma "At most two sides", in the form the crosscut theorem consumes.** Two distinct
components of `D ∖ P` exhaust it. -/
theorem crosscut_components_exhaust {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ := by
  obtain ⟨zL, -, zR, -, hcov⟩ :=
    crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD hcollars
  exact covered_by_two_components_of_ne hcov h₁ h₂ hne

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two-sided collars along a simple polygonal arc

`Schoenflies/CrosscutAtMostTwo.lean` proves Lemma "At most two sides" assuming
`Schoenflies.HasArcCollars`: every compact piece of `D ∩ P` has a two-sided collar inside `D`.
This module discharges that hypothesis for a polygonal arc presented by its vertex list.

## The route: a linear chain, not a cyclic one

`Schoenflies/Strip.lean` builds the collar of blueprint Lemma 1.8 for a `ClosedPolygon`, whose
vertex family is indexed by `ZMod (m + 3)`. The apparatus is redone here on a *linear* index —
route (A) of the three the blueprint's arc case admits. Closing the arc into a polygon (route
(B)) was rejected: it needs a return path from one end of the arc back to the other meeting the
arc only at its ends, and producing one is the two-sided collar of the arc all over again.

Two things change from the cyclic case, and both make the arc case *easier*.

* **There are no sectors at the two extreme vertices.** An edge block already stops short of
  both of its endpoints by the trim `lam`, so the collar of the whole chain of blocks is an open
  neighbourhood of the arc minus two small end caps — which is all that is wanted, because the
  compact piece `K` sits at positive distance from the two endpoints of a crosscut (they are
  outside `D` and `K` is inside).
* **The neighbourhood is open by construction.** The collar of a closed polygon has to contain
  the curve, so `StripData.nbhd` is a union of open sets *plus the carrier*, and
  `StripData.nbhd_eq` is needed to see that it is open. Here `nbhd` is defined outright as the
  union of the vertex balls and the edge tubes; it contains the arc only away from its two ends,
  and there is nothing to prove.

What does **not** change is the germ argument at a corner: `Plane.germs_split'` is applied
exactly as in the cyclic case, with the incoming ray at vertex `i + 1` written `A.back i` and
the outgoing one `A.tang (i + 1)`.

## The one thing left open

`PolyArc` is a *presentation*: a simple polygonal arc given by its vertex list, exactly as
`ClosedPolygon` presents a simple closed polygonal curve. Everything is proved for a `PolyArc`,
and `Schoenflies.polyArc_crosscut_at_most_two` is Lemma "At most two sides" for one with no
hypothesis left standing at all. What is *not* proved is the converse presentation statement:
that a set which happens to be a simple polygonal arc is the carrier of some `PolyArc`. That is
the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve; it is normalisation, not geometry.
`Schoenflies.hasArcCollars` therefore carries it as the hypothesis
`Schoenflies.IsPolyArcCarrier`. See the note at the end of the file for the route.

The presentation is checked in both other directions, so neither the structure nor the
hypothesis is vacuous or accidentally false: `Schoenflies.PolyArc.isArcBetween_carrier` and
`Schoenflies.PolyArc.isPolygonal_carrier` say the carrier of a `PolyArc` *is* a simple polygonal
arc, and `Schoenflies.isPolyArcCarrier_segment` exhibits one.

## Blueprint

* `Schoenflies.PolyArc` — a simple polygonal arc presented by its vertex list; the arc analogue
  of `Schoenflies.ClosedPolygon`.
* `Schoenflies.ArcStrip` — the constants of blueprint Lemma 1.8 (b), as a structure: the cone
  radius `R`, the trim `lam`, the half-width `rho`, and the separations they satisfy. The arc
  analogue of `Schoenflies.StripData`, with the two clauses that make the collar fit inside the
  prescribed region and clear of the two endpoints.
* `Schoenflies.ArcStrip.nbhd`, `.sideL`, `.sideR` — the collar `N` and its two tracks `N_L`,
  `N_R` of Lemma 1.8 (b).
* `Schoenflies.ArcStrip.nbhd_diff_carrier`, `.isConnected_sideL`, `.isConnected_sideR`,
  `.sideL_disjoint_sideR`, `.subset_closure_sideL`, `.subset_closure_sideR` — the clauses of
  Lemma 1.8 (b).
* `Schoenflies.exists_arcStrip` — the constants exist. The arc analogue of
  `Schoenflies.exists_stripData_subset`.
* `Schoenflies.ArcStrip.collar`, `Schoenflies.PolyArc.exists_arcCollar`,
  `Schoenflies.PolyArc.hasArcCollars` — Lemma 1.8 (b) itself, as the interface
  `Schoenflies.ArcCollar` that `Schoenflies/CrosscutAtMostTwo.lean` consumes.
* `Schoenflies.PolyArc.isArcBetween_carrier`, `Schoenflies.PolyArc.isPolygonal_carrier` — the
  carrier of a `PolyArc` is a simple polygonal arc between its two extreme vertices.
* `Schoenflies.polyArc_crosscut_at_most_two`,
  `Schoenflies.polyArc_crosscut_components_exhaust` — Lemma "At most two sides" for a polygonal
  arc presented by a vertex list, with no further assumptions.
* `Schoenflies.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_polyArc`,
  `Schoenflies.crosscut_components_exhaust_of_polyArc` — the same for a *set* `P` presented by
  `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.segmentPolyArc`, `Schoenflies.isPolyArcCarrier_segment` — a straight crosscut as
  a `PolyArc`, which recovers `Schoenflies.hasArcCollars_segment` as a special case.
-/

open Metric Set

namespace Schoenflies

open Plane

/-! ## Simple polygonal arcs

A polygonal arc is presented by its vertex list `v 0, …, v (n + 1)`; its edges are the `n + 1`
segments `edge i = [v i, v (i + 1)]` for `i ≤ n`, and its *interior* vertices — the ones that
carry a corner, and hence a sector of the collar — are `v 1, …, v n`.

The vertex function is indexed by all of `ℕ` and asked to be injective outright, rather than
injective on `{0, …, n + 1}`. Nothing past `v (n + 1)` is ever looked at except through
`A.tang i` and `A.len i`, which are only well behaved when `v i ≠ v (i + 1)`; asking for global
injectivity buys that for free and removes an `i ≤ n` side condition from every lemma about the
edge frame. It costs a discharger nothing: a finite vertex list is padded to an injective
sequence by any tail of fresh points. -/

/-! ### The turned vector of a reversed direction -/

namespace PolyArc

variable {n : ℕ} (A : PolyArc n) (i j : ℕ) (c t s : ℝ)

variable {A i j c t s}

/-! ### The edge frame -/

/-! ### Edges as sets -/

theorem vertex_succ_mem_edge : A.vertex (i + 1) ∈ A.edge i := by
  rw [← pt_len]; exact pt_mem_edge ⟨len_pos.le, le_refl _⟩

theorem isCompact_edge : IsCompact (A.edge i) := isCompact_segment _ _

theorem continuous_pt (A : PolyArc n) (i : ℕ) : Continuous (A.pt i) := by
  have h : A.pt i = fun c : ℝ => A.vertex i + c • A.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives -/

/-- **Simplicity, first form.** A vertex lies on no edge but the (at most two) edges incident
to it. -/
theorem vertex_notMem_edge (hi : i ≤ n + 1) (hj : j ≤ n) (h1 : i ≠ j) (h2 : i ≠ j + 1) :
    A.vertex i ∉ A.edge j := by
  intro hx
  rcases Nat.lt_or_ge i (n + 1) with hlt | hge
  · -- `vertex i` is also the initial vertex of edge `i`, which exists.
    have hi' : i ≤ n := by omega
    have hmem : A.vertex i ∈ A.edge j ∩ A.edge i := ⟨hx, vertex_mem_edge⟩
    have hsub := A.edges_meet j hj i hi' (Ne.symm h1) hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    rcases hsub with h | h
    · exact h1 (A.vertex_inj h)
    · exact h2 (A.vertex_inj h)
  · -- `vertex (n + 1)` is the terminal vertex of edge `n`.
    have hin : i = n + 1 := by omega
    subst hin
    have hjn : j ≠ n := fun h => h2 (by omega)
    have hmem : A.vertex (n + 1) ∈ A.edge j ∩ A.edge n := ⟨hx, vertex_succ_mem_edge⟩
    have hsub := A.edges_meet j hj n (le_refl n) hjn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    rcases hsub with h | h
    · exact h1 (A.vertex_inj h)
    · exact h2 (A.vertex_inj h)

/-- The trimmed core of edge `i`: the points at distance at least `lam` from both endpoints. -/
def trimmed (A : PolyArc n) (i : ℕ) (lam : ℝ) : Set Plane :=
  A.pt i '' Set.Icc lam (A.len i - lam)

theorem pt_mem_trimmed {lam : ℝ} (hc : c ∈ Set.Icc lam (A.len i - lam)) :
    A.pt i c ∈ A.trimmed i lam := ⟨c, hc, rfl⟩

theorem isCompact_trimmed {lam : ℝ} : IsCompact (A.trimmed i lam) :=
  isCompact_Icc.image (A.continuous_pt i)

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge: the two
common points `edges_meet` allows are the endpoints, and the trim removes them. -/
theorem trimmed_disjoint_edge {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n) (hj : j ≤ n) (hij : j ≠ i) :
    Disjoint (A.trimmed i lam) (A.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ A.len i := le_trans hc.2 (by linarith)
  have hmem : A.pt i c ∈ A.edge i ∩ A.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := A.edges_meet i hi j hj (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · have h0 : |c| = 0 := by rw [← dist_pt_vertex (A := A) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · have h0 : |c - A.len i| = 0 := by
      rw [← dist_pt_vertex_succ (A := A) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonpos (by linarith)] at h0
    linarith [hc.2]

/-! ### The four germs at an interior vertex

`Plane.germs_split'` applied at the interior vertex `v (i + 1)`, whose incoming ray is
`A.back i` and whose outgoing ray is `A.tang (i + 1)`. The smallness of the offset is left as a
hypothesis; the block versions supply it from the `germ` field of an `ArcStrip`. -/

end PolyArc

/-! ## The constants

`ArcStrip` is the arc analogue of `Schoenflies.StripData`: the blueprint's "choose the blocks so
that consecutive ones overlap and nonadjacent closures are disjoint", with every constant named.
Three fields have no counterpart in the closed case, and they are what makes the collar a collar
*of `K` inside `D`*: `ball_subset` and `tube_subset` put every piece inside the prescribed open
set, and `sep_ends` keeps `K` clear of the two ends of the arc, where the collar has no pieces.

`sep_ends` is not a restriction in the intended application: the two endpoints of a crosscut lie
outside `D` and `K` lies inside, so the distance from `K` to either endpoint is positive and `R`
is chosen below it. -/

/-! ### Two shapes of bounded union

Both tracks and the collar are unions over an initial segment of `ℕ`. These two rewrites are the
only interface to that indexing. -/

/-! ## Chaining a linear family

The union of the left pieces is connected because consecutive pieces overlap. Unlike the cyclic
case there is no closing overlap to discard: the chain `0, 1, …, N` is exactly the spanning tree
of the overlap graph. -/

/-! ## Choosing the constants

The blueprint's own recipe, in the blueprint's order, with the two clauses about the prescribed
open set folded in at the step where they can be met.

1. `R` from the edge lengths, the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, the openness of `D` at each interior vertex, and the distance from `K`
   to the two endpoints of the arc.
2. `lam := R / 5`, which gives `2 lam < R` and, through `R ≤ len i`, also `4 lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, from the germ threshold
   at every interior vertex, and from the compact separation of each trimmed edge from the
   complement of `D`. Step 3 is where "the collar is inside `D`" is really paid for: a trimmed
   core is a compact subset of `D`, because the only points of the arc outside `D` are its two
   endpoints and the trim removes them. -/

namespace PolyArc

variable {n : ℕ} {A : PolyArc n} {i : ℕ} {c : ℝ}

/-- A point of a trimmed core is not the first vertex of the arc: on the first edge the trim
keeps it away, and on any other edge simplicity does. -/
theorem pt_ne_vertex_zero {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n)
    (hc : c ∈ Set.Icc lam (A.len i - lam)) : A.pt i c ≠ A.vertex 0 := by
  have hmem : A.pt i c ∈ A.edge i :=
    pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · intro h
    have hd : dist (A.pt 0 c) (A.vertex 0) = |c| := dist_pt_vertex
    rw [h, dist_self, abs_of_nonneg (le_trans hlam.le hc.1)] at hd
    linarith [hc.1]
  · intro h
    exact vertex_notMem_edge (A := A) (i := 0) (j := i) (by omega) hi (by omega) (by omega)
      (h ▸ hmem)

/-- …nor the last vertex of the arc. -/
theorem pt_ne_vertex_last {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n)
    (hc : c ∈ Set.Icc lam (A.len i - lam)) : A.pt i c ≠ A.vertex (n + 1) := by
  have hmem : A.pt i c ∈ A.edge i :=
    pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩
  rcases Nat.lt_or_ge i n with hilt | hige
  · intro h
    exact vertex_notMem_edge (A := A) (i := n + 1) (j := i) (le_refl _) hi (by omega) (by omega)
      (h ▸ hmem)
  · have hin : i = n := by omega
    intro h
    have hd : dist (A.pt i c) (A.vertex (i + 1)) = |c - A.len i| := dist_pt_vertex_succ
    have heq : A.vertex (i + 1) = A.vertex (n + 1) := by rw [hin]
    rw [heq, h, dist_self, abs_of_nonpos (by linarith [hc.2, hlam] : c - A.len i ≤ 0)] at hd
    linarith [hc.2]

/-- **Step 1: the cone radius.** -/
theorem exists_cone_radius (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (hKcompact : IsCompact K) (hKD : K ⊆ D) (hint : ∀ j, 1 ≤ j → j ≤ n → A.vertex j ∈ D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D) :
    ∃ R > 0, (∀ i ≤ n, R ≤ A.len i) ∧
      (∀ i ≤ n + 1, ∀ j ≤ n + 1, i ≠ j → 2 * R ≤ dist (A.vertex i) (A.vertex j)) ∧
      (∀ i ≤ n + 1, ∀ j ≤ n, i ≠ j → i ≠ j + 1 → ∀ y ∈ A.edge j, 2 * R ≤ dist (A.vertex i) y) ∧
      (∀ i < n, ball (A.vertex (i + 1)) R ⊆ D) ∧
      (∀ x ∈ K, R ≤ dist x (A.vertex 0) ∧ R ≤ dist x (A.vertex (n + 1))) := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_le_nat n) (f := fun i => A.len i) fun _ _ => len_pos
  -- (2) the pairwise vertex separations
  have h₂ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n + 1} ×ˢ {i | i ≤ n + 1}) →
      (p.1 ≠ p.2 → ε ≤ dist (A.vertex p.1) (A.vertex p.2)) := by
    refine exists_pos_forall_of_finite
      ((Set.finite_le_nat (n + 1)).prod (Set.finite_le_nat (n + 1))) ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (A.vertex i) (A.vertex j), dist_pos.2 fun h => hij (A.vertex_inj h),
          fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to
  have h₃ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n + 1} ×ˢ {i | i ≤ n}) →
      (p.1 ≠ p.2 → p.1 ≠ p.2 + 1 → ∀ y ∈ A.edge p.2, ε ≤ dist (A.vertex p.1) y) := by
    refine exists_pos_forall_of_finite
      ((Set.finite_le_nat (n + 1)).prod (Set.finite_le_nat n)) ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ hp
      by_cases h1 : i = j
      · exact ⟨1, one_pos, fun h => absurd h1 h⟩
      by_cases h2 : i = j + 1
      · exact ⟨1, one_pos, fun _ h => absurd h2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hp.1 hp.2 h1 h2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set, at the interior vertices
  have h₄ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i < n} → ball (A.vertex (i + 1)) ε ⊆ D := by
    refine exists_pos_forall_of_finite (Set.finite_lt_nat n) ?_ ?_
    · intro _ δ ε _ hδε h
      exact subset_trans (ball_subset_ball hδε) h
    · intro i hi
      have hi' : i < n := hi
      exact Metric.isOpen_iff.1 hD _ (hint (i + 1) (by omega) (by omega))
  -- (5) the two endpoints of the arc, which are off `K`
  obtain ⟨e₅, he₅, hK0⟩ := Plane.exists_dist_pos hKcompact isCompact_singleton
    (Set.disjoint_singleton_right.2 fun h => ha (hKD h))
  obtain ⟨e₆, he₆, hK1⟩ := Plane.exists_dist_pos hKcompact isCompact_singleton
    (Set.disjoint_singleton_right.2 fun h => hb (hKD h))
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  obtain ⟨e₄, he₄, hball⟩ := h₄
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) (lt_min he₄ (lt_min he₅ he₆))),
    fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi j hj h1 h2 y hy => ?_,
    fun i hi => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i hi)
  · have h := hvv (i, j) (Set.mk_mem_prod hi hj) hij
    have hm : min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · have h := hve (i, j) (Set.mk_mem_prod hi hj) h1 h2 y hy
    have hm : min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans (ball_subset_ball
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) (hball i hi)
  · exact le_trans (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
      (hK0 x hx _ rfl)
  · exact le_trans (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      (hK1 x hx _ rfl)

/-- **Step 3: the half-width.** -/
theorem exists_half_width (A : PolyArc n) {D : Set Plane} {lam : ℝ} (hD : IsOpen D)
    (hlam : 0 < lam) (hcore : ∀ i ≤ n, A.trimmed i lam ⊆ D) :
    ∃ rho > 0, rho < lam ∧
      (∀ i ≤ n, ∀ j ≤ n, j ≠ i → ∀ c ∈ Set.Icc lam (A.len i - lam), ∀ y ∈ A.edge j,
        2 * rho ≤ dist (A.pt i c) y) ∧
      (∀ i < n, rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
        lam * |det (A.back i) (A.tang (i + 1))|) ∧
      (∀ i ≤ n, ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) rho ⊆ D) := by
  -- (1) each trimmed edge against every other edge
  have h₁ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n} ×ˢ {i | i ≤ n}) →
      (p.2 ≠ p.1 → ∀ x ∈ A.trimmed p.1 lam, ∀ y ∈ A.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite ((Set.finite_le_nat n).prod (Set.finite_le_nat n)) ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ hp
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hp.1 hp.2 hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every interior vertex
  have h₂ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i < n} →
      ε * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
        lam * |det (A.back i) (A.tang (i + 1))| := by
    refine exists_pos_forall_of_finite (Set.finite_lt_nat n) ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
      nlinarith
    · intro i hi
      have hi' : i < n := hi
      have hbd : 0 < |det (A.back i) (A.tang (i + 1))| := abs_pos.2 (det_rays_ne_zero hi')
      have hac : (0 : ℝ) < 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
      exact ⟨lam * |det (A.back i) (A.tang (i + 1))| /
          (1 + |inner ℝ (A.back i) (A.tang (i + 1))|),
        div_pos (mul_pos hlam hbd) hac, le_of_eq (by field_simp)⟩
  -- (3) the prescribed open set, along every trimmed core
  have h₃ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i ≤ n} →
      ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) ε ⊆ D := by
    refine exists_pos_forall_of_finite (Set.finite_le_nat n) ?_ ?_
    · intro _ δ ε _ hδε h c hc
      exact subset_trans (ball_subset_ball hδε) (h c hc)
    · intro i hi
      have hi' : i ≤ n := hi
      obtain ⟨ρ, hρ, hsub⟩ :=
        Plane.exists_thickening_subset isCompact_trimmed hD (hcore i hi')
      exact ⟨ρ, hρ, fun c hc y hy => hsub (mem_thickening_iff.2 ⟨A.pt i c, pt_mem_trimmed hc, hy⟩)⟩
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  obtain ⟨ε₃, hε₃, hballs⟩ := h₃
  refine ⟨min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)),
    lt_min (lt_min (by linarith) hε₂) (lt_min hε₃ (by linarith)), ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  · intro i hi j hj hij c hc y hy
    have h := htrim (i, j) (Set.mk_mem_prod hi hj) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i hi
    have h := hgerm i hi
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
    have hm : min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  · intro i hi c hc
    exact subset_trans (ball_subset_ball
      (le_trans (min_le_right _ _) (min_le_left _ _))) (hballs i hi c hc)

end PolyArc

/-- **Lemma 1.8 (b), the constants.** A simple polygonal arc whose two endpoints lie outside the
region `D` and whose remaining points lie inside it carries an `ArcStrip` for every compact
piece `K` of `D ∩ P`. -/
theorem exists_arcStrip {n : ℕ} (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D)
    (hKcompact : IsCompact K) (hKsub : K ⊆ D ∩ A.carrier) :
    Nonempty (ArcStrip A D K) := by
  -- Every interior vertex is inside the region, being on the arc and distinct from its ends.
  have hint : ∀ j, 1 ≤ j → j ≤ n → A.vertex j ∈ D := by
    intro j h1 h2
    refine hPD ⟨PolyArc.vertex_mem_carrier h2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact absurd (A.vertex_inj h) (by omega)
    · exact absurd (A.vertex_inj h) (by omega)
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRball, hRends⟩ :=
    A.exists_cone_radius hD hKcompact (fun _ hz => (hKsub hz).1) hint ha hb
  have hlam : (0 : ℝ) < R / 5 := by linarith
  -- Every trimmed core is a compact subset of the region: the trim removes the two endpoints.
  have hcore : ∀ i ≤ n, A.trimmed i (R / 5) ⊆ D := by
    rintro i hi _ ⟨c, hc, rfl⟩
    refine hPD ⟨PolyArc.edge_subset_carrier hi (PolyArc.pt_mem_edge
      ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩), ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact PolyArc.pt_ne_vertex_zero hlam hi hc h
    · exact PolyArc.pt_ne_vertex_last hlam hi hc h
  obtain ⟨rho, hrho, hrl, htrim, hgerm, hballs⟩ := A.exists_half_width hD hlam hcore
  exact ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, fun i hi => by have := hRlen i hi; linarith,
    hRlen, hRvv, hRve, htrim, hgerm, hRball, hballs, fun _ hz => (hKsub hz).2, hRends⟩⟩

/-! ## Lemma 1.8 (b), and `HasArcCollars` -/

namespace PolyArc

/-- **Two-sided polygonal strips, the arc case.** Every compact piece of the arc lying inside
the region has a two-sided collar there. The collar is `ArcStrip.collar`, a construction, not an
existential: `Schoenflies.exists_arcStrip` produces the constants and every part of the collar is
a definition with an API. -/
theorem exists_arcCollar {n : ℕ} (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D)
    (hKcompact : IsCompact K) (hKsub : K ⊆ D ∩ A.carrier) :
    Nonempty (ArcCollar D A.carrier K) := by
  obtain ⟨S⟩ := exists_arcStrip A hD ha hb hPD hKcompact hKsub
  exact ⟨S.collar⟩

/-- **`HasArcCollars` for a polygonal arc.** This is the hypothesis of
`Schoenflies.crosscut_at_most_two`, discharged.

Note that neither connectedness nor nontriviality of `K` is used: the collar exists for *every*
compact subset of `D ∩ P`. -/
theorem hasArcCollars {n : ℕ} (A : PolyArc n) {D : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D) :
    HasArcCollars D A.carrier :=
  fun _ hKsub hKcompact _ _ => A.exists_arcCollar hD ha hb hPD hKcompact hKsub

end PolyArc

/-- **`P` is a simple polygonal arc from `a` to `b`, presented by a vertex list.** This is the
arc analogue of what `Schoenflies.exists_closedPolygon` proves for a Jordan curve, and it is the
one thing this module does not prove; see the note at the end of the file. -/
def IsPolyArcCarrier (P : Set Plane) (a b : Plane) : Prop :=
  ∃ (n : ℕ) (A : PolyArc n), A.carrier = P ∧ A.vertex 0 = a ∧ A.vertex (n + 1) = b

/-- **`HasArcCollars` for a set presented as the carrier of a `PolyArc`.** The conclusion is
literally the `Schoenflies.HasArcCollars` that `Schoenflies/CrosscutAtMostTwo.lean` carries as a
hypothesis, and the hypotheses are those of `Schoenflies.crosscut_at_most_two` together with the
presentation of `P` by a vertex list. -/
theorem hasArcCollars {D P : Set Plane} {a b : Plane} (hD : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) (hchain : IsPolyArcCarrier P a b) :
    HasArcCollars D P := by
  obtain ⟨n, A, rfl, rfl, rfl⟩ := hchain
  exact A.hasArcCollars hD ha hb hPD

/-! ## The presentation is faithful: the carrier is a simple polygonal arc

`PolyArc` is a *presentation*, so the interface owes a check in the other direction: that the
carrier of a `PolyArc` really is a simple polygonal arc between its two extreme vertices. Both
halves are an induction along the chain of edges, and the only input is simplicity: consecutive
edges meet exactly at the vertex they share, and nonconsecutive ones not at all.

With them, Lemma "At most two sides" for an arc presented by a vertex list has **no hypothesis
left standing** — `Schoenflies.polyArc_crosscut_at_most_two`. -/

/-! ## The presentation is not vacuous: a straight crosscut

A nondegenerate segment is a `PolyArc 0`: one edge, no interior vertex, so both `edges_meet` and
`corner` are vacuous. The vertex function is padded past the segment by walking on in the same
direction, which keeps it injective — this is the padding convention the structure's docstring
describes, in its simplest instance. With it, `Schoenflies.hasArcCollars_segment` of
`Schoenflies/CrosscutAtMostTwo.lean` is a special case of `Schoenflies.hasArcCollars`, which
certifies that `Schoenflies.IsPolyArcCarrier` is satisfiable and that the whole apparatus above
is not vacuous. -/

/-!
## What is still missing

Exactly one thing: `Schoenflies.IsPolyArcCarrier`. Everything above is proved for an arc
*presented by its vertex list*, and `Schoenflies.hasArcCollars` therefore carries that
presentation as a hypothesis in place of the blueprint's set-level "`P` is a simple polygonal
arc" (`IsArcBetween P a b` together with `IsPolygonal P`).

The missing theorem is

```
theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) (hab : a ≠ b) : IsPolyArcCarrier P a b
```

the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve. It is a *normalisation* statement, not geometry: it says a set that
happens to be both an arc and a finite union of segments can be cut into a chain. The route is
the one `Schoenflies/Realization.lean` takes in the closed case, and its three steps are:

1. `Schoenflies.IsArcBetween.exists_poly_eq` already gives a vertex list `vs` with
   `poly vs = P`, `vs.head = a`, `vs.getLast = b`. That list may backtrack: nothing yet says its
   vertices occur in order along `P`.
2. Order them. Each segment `[vs i, vs (i+1)]` is contained in `P` and is an arc between its
   ends, so by `Schoenflies.IsArcBetween.eq_of_subset` it *is* the subarc of `P` between the two
   parameters. The parameters of the `vs i`, sorted and deduplicated, therefore cut `[0, 1]` into
   intervals each of which is covered by one of those segments, and the subarc over each is a
   segment. That is the chain, with `vertex_inj` and `edges_meet` immediate from injectivity of
   the parametrisation.
3. Delete redundant vertices, i.e. merge two consecutive collinear edges into one. This is the
   blueprint's own first sentence ("Delete redundant vertices at which two consecutive edges are
   collinear") and is what `corner` needs; the closed-curve analogue is
   `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.

None of the three is formalised for an arc. The remaining results require no such interface.
-/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_OuterFace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The outer face

Exactly one face of a finite plane graph is unbounded.

The plane fact this needs is not "the exterior of a large disk is connected" but the exterior
of a *square*, and that one is elementary — `Plane.isConnected_beyondSquare`, four convex
half-planes with consecutive ones sharing a corner. The disk version is what would have
needed a traversal of the circle, which a trigonometry-free development withholds.

No face is produced as data: a face is named by a point of it, as `Graph.face` always has
been, so "the outer face" is "the face through any point far enough out".

## Blueprint

* `exists_unbounded_face` — some face is unbounded.
* `unbounded_face_unique` — any two unbounded faces coincide.
* `beyondSquare_subset_face` — an unbounded face swallows the whole outside of any square
  containing the drawing. This is the working form: it is how one proves a given point lies in
  the outer face.
-/

open Metric Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- Any two unbounded faces coincide: an unbounded face escapes every containing square, so it
swallows the whole outside and is named by any point of it. -/
theorem unbounded_face_unique [G.Finite] (h : IsDrawing G drawing) {b c : Plane}
    (hbu : ¬ Bornology.IsBounded (face G drawing b))
    (hcu : ¬ Bornology.IsBounded (face G drawing c)) :
    face G drawing b = face G drawing c := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  -- An unbounded face is not contained in the square, so it meets the outside.
  have escape : ∀ z : Plane, ¬ Bornology.IsBounded (face G drawing z) →
      ∃ w, w ∈ face G drawing z ∧ w ∈ Schoenflies.Plane.beyondSquare r := by
    intro z hz
    by_contra hcon
    push Not at hcon
    refine hz ((isBounded_closedSquare r).subset fun w hw => ?_)
    have hw' : w ∉ Schoenflies.Plane.beyondSquare r := hcon w hw
    rw [Schoenflies.Plane.beyondSquare_eq_compl] at hw'
    simpa using hw'
  obtain ⟨w, hwb, hwout⟩ := escape b hbu
  obtain ⟨v, hvc, hvout⟩ := escape c hcu
  -- Each face therefore swallows the whole outside, so the two share a point.
  have hbeyond_b : Schoenflies.Plane.beyondSquare r ⊆ face G drawing b := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hwout
    have hwe : face G drawing w = face G drawing b := (connectedComponentIn_eq hwb).symm
    rwa [hwe] at hsub
  have hbeyond_c : Schoenflies.Plane.beyondSquare r ⊆ face G drawing c := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hvout
    have hve : face G drawing v = face G drawing c := (connectedComponentIn_eq hvc).symm
    rwa [hve] at hsub
  obtain ⟨z, hz⟩ := (Schoenflies.Plane.isConnected_beyondSquare r).nonempty
  have e1 : face G drawing b = face G drawing z := connectedComponentIn_eq (hbeyond_b hz)
  have e2 : face G drawing c = face G drawing z := connectedComponentIn_eq (hbeyond_c hz)
  rw [e1, e2]

end Graph
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Moving an interior point of the square

The pointed form of the bounded theorem needs a self-homeomorphism of the closed square that
fixes the boundary pointwise and carries one prescribed interior point to another. The
blueprint builds it by coning: the four triangles `conv {x, vᵢ, vᵢ₊₁}` triangulate the square,
and the affine map of each onto `conv {y, vᵢ, vᵢ₊₁}` fixing the two corners pastes with its
neighbours along the radial edges.

The construction here is the same map in different coordinates, and it is written so that no
pasting of four affine pieces is needed. It is the composite of two *shears*. A shear bends
one coordinate by the piecewise-linear self-map of `[-r, r]` that fixes the two endpoints and
moves a chosen breakpoint (`bend`), with a displacement that is scaled by a tent function of
the *other* coordinate (`tent`), so that it dies away to zero on the two transverse sides of
the square. The first shear moves the first coordinate of `x` to that of `y`, the second moves
the second coordinate.

Two features make this cheap. Writing the tent as a minimum of two affine functions makes it
continuous with no case split at all. And the family of shears is closed under inversion: the
shear with displacement parameters `k, k'` is undone by the shear with parameters `k + k',
-k'`, so bijectivity and the continuity of the inverse come from one composition identity
(`bend_bend`) instead of from a compactness argument, and no map has to be inverted by hand.

## Blueprint

* `Plane.exists_squareMover` — Lemma (Moving an interior point of the square): for interior
  points `x`, `y` of the square there are mutually inverse boundary-fixing self-maps `M`, `N`
  of the closed square with `M x = y`. `Plane.IsSquareMover` bundles the properties that make
  `M` a homeomorphism of the square onto itself, `Plane.IsSquareMover.homeomorph` repackages
  it as a `Homeomorph`, and `Plane.IsSquareMover.eqOn_frontier` states the boundary condition
  against the topological frontier, which `Plane.frontier_closedSquare` identifies with the
  blueprint's boundary square `S`.
* `Plane.iInter_eq_singleton_of_mem_tail` — the point-set kernel of Proposition (Skeleton
  agreement). The proposition itself is not statable in the present development; see the
  section comment at that lemma for exactly what is and is not proved.

Supporting material, of independent use: `Plane.tent` and `Plane.bend` with their algebra,
`Plane.continuousOn_bend`, the coordinate lemmas `Plane.abs_sub_le_supDist`,
`Plane.supDist_le_of_forall`, `Plane.exists_abs_sub_eq_of_supDist_eq`,
and `Plane.interior_closedSquare`.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### The tent function -/

variable {r p q u : ℝ}

/-! ### Bending an interval -/

/-! ### Coordinates of the square -/

/-- Each coordinate difference is bounded by the sup distance. -/
theorem abs_sub_le_supDist (z c : Plane) (l : Fin 2) : |z l - c l| ≤ supDist z c := by
  fin_cases l
  · exact abs_sub_zero_le_supDist z c
  · exact abs_sub_one_le_supDist z c

/-! ### Shearing the square along one coordinate -/

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

/-! ### Movers of the square -/

/-! ### Moving an interior point -/

/-! ### The boundary of the square -/

/-- The interior of the closed square is the open square: a point with a coordinate at
distance exactly `r` from the centre can be pushed further out along that coordinate. -/
theorem interior_closedSquare (c : Plane) (r : ℝ) :
    interior (closedSquare c r) = openSquare c r := by
  have hsub : openSquare c r ⊆ closedSquare c r := fun z hz => show supDist z c ≤ r from hz.le
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal hsub (isOpen_openSquare c r))
  by_contra hzo
  have hzc : z ∈ closedSquare c r := interior_subset hz
  have heq : supDist z c = r := le_antisymm hzc (not_lt.1 hzo)
  obtain ⟨l, hl⟩ := exists_abs_sub_eq_of_supDist_eq heq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hr : 0 ≤ r := hl ▸ abs_nonneg _
  have key : ∀ t : ℝ, |t| < ε → |(z l - c l) + t| ≤ r := by
    intro t ht
    have hmem : z + t • EuclideanSpace.single l (1 : ℝ) ∈ closedSquare c r :=
      interior_subset (hball (by rw [Metric.mem_ball, dist_add_smul_single]; exact ht))
    have := le_trans (abs_sub_le_supDist (z + t • EuclideanSpace.single l (1 : ℝ)) c l) hmem
    rwa [add_smul_single_apply, show z l + t - c l = z l - c l + t by ring] at this
  rcases (abs_eq hr).1 hl with he | he
  · have := (abs_le.1 (key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))).2
    rw [he] at this
    linarith
  · have := (abs_le.1 (key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))).1
    rw [he] at this
    linarith

/-- The boundary of the closed square is the sup-distance sphere: the blueprint's `S`. -/
theorem frontier_closedSquare (c : Plane) (r : ℝ) :
    frontier (closedSquare c r) = {z | supDist z c = r} := by
  rw [(isClosed_closedSquare c r).frontier_eq, interior_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.1 h2)
  · intro h
    exact ⟨le_of_eq h, by rw [openSquare, mem_setOf_eq, h]; exact lt_irrefl r⟩

/-! ### The mover as a homeomorphism -/

/-! ### The point-set kernel of skeleton agreement

The blueprint's Proposition (Skeleton agreement) says that the limit map `F`, defined at `x`
as the unique point of the nested intersection `⋂ n, T n x` of closed target stars, agrees
with every finite skeleton map: if `x ∈ G_N ∩ D` then `F x = g_N x`. Its proof is one line of
point-set topology once the combinatorics is in place — the value `g_N x` lies in `T n x` for
every `n ≥ N`, hence in the intersection, hence is *the* point of the intersection.

That one line is what follows. The proposition itself cannot be stated in this development
yet: matched cell structures, carriers, stars, the skeleton homeomorphisms `g_n` and the limit
map `F` do not exist here. What is proved is exactly the implication the proposition rests on,
with the nested stars as an abstract antitone sequence of shrinking compacta and `g_N x` as an
abstract point of all late terms. -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.ArcComplementPrep
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Scaffolding for the arc-complement theorem

`thm:arc-complement` — a simple arc does not separate the plane — is proved by covering the
arc with a chain of small axis-parallel squares, overlaying their boundaries into one plane
graph `G`, and showing that the two given points lie in the outer face of `G`, which is then
disjoint from the arc. This module builds everything in that proof that does **not** need the
outer-chain lemma (`lem:outer-chain`), so that the theorem itself becomes a short assembly.

## What is here

1. *The square boundary as a polygon.* `Schoenflies.squarePolygon c hr : ClosedPolygon 1` is
   the axis-parallel square of `ℓ^∞`-radius `r` about `c`, presented the way the parity and
   overlay machinery consume a polygon — as a `ClosedPolygon`, not as a set. Its carrier is
   `frontier (Plane.closedSquare c r)` (`carrier_squarePolygon`), and the polygonal Jordan
   curve theorem then hands over that this frontier is a Jordan curve, is polygonal, and is
   separating, with `inside` the open square and `outside` the complement of the closed one.

   `Schoenflies.modelCurve` is the case `c = 0`, `r = 1` as a *set*; nothing there is a
   `ClosedPolygon`, so nothing there could be fed to the overlay.

2. *Two nearby congruent squares meet twice.* The route taken is the coordinate one, not the
   blueprint's topological one, because the meeting points can be written down: a vertical
   side of one square crosses a horizontal side of the other, transversally, in a single
   point. That "single point" is exactly what `Schoenflies.MeetsAreCut` needs to turn a
   meeting point into a *vertex* of the overlay graph, which is what
   `Graph.IsTwoConnected.union` consumes. See `exists_two_common_vertices` and the discussion
   before it.

3. *The uniform-continuity partition.* `Schoenflies.sample n i = i / n` is the even partition
   of `[0,1]`; `exists_mesh` says that for `n` large enough — and `n` may be asked to be a
   multiple of any prescribed `k`, which is what makes the fine partition refine the coarse
   one — every point of `α '' [t i, t (i+1)]` is within `ε` of `α (t i)`.

4. *Nonadjacent subarcs are at positive distance.* `exists_pos_dist_nonadjacent`.

5. *The covering clause.* `image_subset_iUnion_closedSquare`: the closed squares of radius `ε`
   about the samples cover the arc.

## Blueprint

* `squarePolygon`, `carrier_squarePolygon` — the square boundary of the proof of
  `thm:arc-complement` ("around every sample draw the boundary of the axis-parallel square of
  `ℓ^∞`-radius `δ/4`"), as a polygon.
* `isJordanCurve_frontier_closedSquare`, `isPolygonal_frontier_closedSquare`,
  `isSeparating_frontier_closedSquare`, `inside_frontier_closedSquare`,
  `outside_frontier_closedSquare` — `thm:polygonal-jordan` specialised to the square.
* `exists_two_meets`, `exists_two_frontier_inter` — "their boundary cycles therefore meet in
  at least two points", `thm:arc-complement`; `exists_two_meets` is the sharp form, in which
  each meeting point is a transversal crossing of two sides.
* `exists_two_common_vertices`, `exists_two_cut_points`, `exists_overlayPiece_end_subset` —
  the bridge from "two common points" to the two common **vertices** that
  `lem:union-two-connected` (`Graph.IsTwoConnected.union`) consumes.
* `sample`, `exists_mesh` — "By uniform continuity, choose a partition …", used twice in
  `thm:arc-complement` and again in `prop:anchored-square-mesh`.
* `exists_pos_dist_nonadjacent` — "Nonadjacent compact subarcs are disjoint, hence at positive
  distance by `lem:compact-separation`(b)".
* `image_subset_iUnion_closedSquare` — "Every point of `A` lies in or on one of the small
  squares".
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## Part 1: the boundary of a square, as a polygon

Everything is done in coordinates. The four corners are named, the four sides are the four
segments between consecutive corners, and the two lemmas `Plane.mem_seg_horiz` and
`Plane.mem_seg_vert` of `Schoenflies/ModelCurve.lean` reduce membership of a side to a pair of
scalar conditions. -/

namespace Plane

variable {c z : Plane} {r : ℝ}

/-- The sup distance in coordinates. -/
theorem supDist_eq_max (z c : Plane) : supDist z c = max |z 0 - c 0| |z 1 - c 1| := rfl

theorem mem_frontier_closedSquare :
    z ∈ frontier (closedSquare c r) ↔ max |z 0 - c 0| |z 1 - c 1| = r := by
  rw [frontier_closedSquare]
  exact Iff.rfl

/-- **The boundary of a square is the union of its four sides.** -/
theorem mem_frontier_closedSquare_iff_sides (hr : 0 ≤ r) :
    z ∈ frontier (closedSquare c r) ↔
      z ∈ segment ℝ (sqNE c r) (sqNW c r) ∨ z ∈ segment ℝ (sqNW c r) (sqSW c r) ∨
      z ∈ segment ℝ (sqSW c r) (sqSE c r) ∨ z ∈ segment ℝ (sqSE c r) (sqNE c r) := by
  rw [mem_seg_top hr, mem_seg_left hr, mem_seg_bottom hr, mem_seg_right hr,
    mem_frontier_closedSquare]
  constructor
  · intro h
    have h0 : |z 0 - c 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |z 1 - c 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, h1⟩))
      · exact Or.inr (Or.inl ⟨by linarith, h1⟩)
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inl ⟨by linarith, h0⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h0⟩))
  · rintro (⟨h1, h0⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h0, h1⟩)
    · have hz : |z 1 - c 1| = r := by rw [h1, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by
        rw [h0, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]
    · have hz : |z 1 - c 1| = r := by
        rw [h1, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by rw [h0, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]

end Plane

open Plane

/-! ### The square as a `ClosedPolygon`

Four corners in counterclockwise order. `edges_meet` splits into the four adjacent pairs,
where `segment_inter_shared` applies because consecutive sides are perpendicular, and the two
opposite pairs, which are disjoint because opposite sides are pinned to different values of
one coordinate. -/

variable {c : Plane} {r : ℝ}

/-! ### What the polygonal Jordan curve theorem says about a square

All four clauses come from `main`; only the identification of the two regions is new, and it
is `Plane.connectedComponentIn_eq_of_frontier_disjoint` twice: once for the open square and
once for its complement. -/

namespace Plane

/-- A closed square is bounded — the statement for an arbitrary centre.
`Graph.isBounded_closedSquare` is the same fact for the centre `0` only. -/
theorem isBounded_closedSquare (c : Plane) (r : ℝ) :
    Bornology.IsBounded (closedSquare c r) := by
  refine (Metric.isBounded_closedBall (x := c) (r := Real.sqrt 2 * r)).subset fun z hz => ?_
  have hsup : supNorm (z - c) ≤ r := hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact le_trans (norm_le_sqrt_two_mul_supNorm _)
    (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))

/-- The outside of a square about `c` contains the outside of a large square about the
origin, hence is unbounded. -/
theorem beyondSquare_subset_compl_closedSquare (c : Plane) (r : ℝ) :
    beyondSquare (r + supNorm c) ⊆ (closedSquare c r)ᶜ := by
  intro x hx
  rw [beyondSquare_eq_compl] at hx
  have hx' : ¬ supNorm x ≤ r + supNorm c := by
    simpa [closedSquare] using hx
  intro hmem
  have hmem' : supDist x c ≤ r := hmem
  -- The triangle inequality against the centre, with `supDist · 0 = supNorm ·`.
  have h1 : supNorm x ≤ supDist x c + supNorm c := by simpa using supDist_triangle x c 0
  exact hx' (by linarith)

theorem not_isBounded_compl_closedSquare (c : Plane) (r : ℝ) :
    ¬ Bornology.IsBounded (closedSquare c r)ᶜ := fun h =>
  Graph.not_isBounded_beyondSquare (r + supNorm c)
    (h.subset (beyondSquare_subset_compl_closedSquare c r))

/-- Membership in the outside of a square, as membership in a translate of `beyondSquare`. -/
theorem mem_compl_closedSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ (closedSquare c r)ᶜ ↔ x - c ∈ beyondSquare r := by
  rw [beyondSquare_eq_compl]
  simp only [mem_compl_iff, closedSquare, mem_setOf_eq, supDist_zero]
  exact Iff.rfl

theorem compl_closedSquare_eq_image (c : Plane) (r : ℝ) :
    (closedSquare c r)ᶜ = (fun x => x + c) '' beyondSquare r := by
  ext z
  rw [mem_compl_closedSquare_iff]
  constructor
  · intro hz
    exact ⟨z - c, hz, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

/-- The plane outside a closed square is connected: a translate of `beyondSquare`. -/
theorem isConnected_compl_closedSquare (c : Plane) (r : ℝ) :
    IsConnected (closedSquare c r)ᶜ := by
  rw [compl_closedSquare_eq_image]
  exact (isConnected_beyondSquare r).image _ (by fun_prop)

/-- The complement of the boundary is the open square together with the outside. -/
theorem compl_frontier_closedSquare (c : Plane) (r : ℝ) :
    (frontier (closedSquare c r))ᶜ = openSquare c r ∪ (closedSquare c r)ᶜ := by
  ext z
  rw [frontier_closedSquare]
  simp only [mem_compl_iff, mem_setOf_eq, mem_union, openSquare, closedSquare, not_le]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h

/-- `Plane.openSquare_subset_closedSquare` already exists on `main`, but in
`Schoenflies/Graph/Redrawing.lean`, which is far above this module in the import order (its
home should be `Schoenflies/Square.lean`).  Kept `private` here so that the two never collide;
delete it once the public one is moved down. -/
theorem openSquare_subset_closedSquare' (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r :=
  fun z hz => show supDist z c ≤ r from le_of_lt hz

/-- The frontier of the *open* square lies in the frontier of the closed one. That inclusion
is all `lem:recognizing-a-component` needs. -/
theorem frontier_openSquare_subset (c : Plane) (r : ℝ) :
    frontier (openSquare c r) ⊆ frontier (closedSquare c r) := by
  rw [(isOpen_openSquare c r).frontier_eq, frontier_closedSquare]
  rintro z ⟨hz1, hz2⟩
  have h1 : supDist z c ≤ r :=
    (isClosed_closedSquare c r).closure_subset_iff.2 (openSquare_subset_closedSquare' c r) hz1
  exact le_antisymm h1 (not_lt.1 hz2)

end Plane


/-! ## Part 2: two nearby congruent squares meet twice

The blueprint (`thm:arc-complement`) argues topologically: neither congruent square contains
the other, so each boundary has nonempty relatively open parts inside the other open square and
outside the other closed square, and a single intersection point could not disconnect a
connected boundary curve.

**The route taken here is the coordinate one**, and it proves more than the blueprint asks.
Write the two centres as `c₁` and `c₂ = c₁ + (a, b)` with `|a|, |b| < r`. Then

* the vertical side of `S₁` on the side of `c₂` crosses the horizontal side of `S₂` away from
  `c₁`, in the single point `(c₁₀ ± r, c₂₁ ∓ r)`;
* the horizontal side of `S₁` away from `c₂` crosses the vertical side of `S₂` on the side of
  `c₁`, in the single point `(c₂₀ ∓ r, c₁₁ ± r)`;

and the two points differ because their first coordinates differ by `2r - |a| ≠ 0`. Each is a
*transversal* crossing — the meet of the two sides is a singleton, not a segment — which is
exactly what `MeetsAreCut` turns into a cut point and hence into a **vertex** of the overlay
graph. Two common points would not be enough for `Graph.IsTwoConnected.union`, which wants two
common vertices; see `exists_two_common_vertices`. -/

/-- The four sides of the square of `ℓ^∞`-radius `r` about `c`, as `Piece`s, in the same cyclic
order as `squarePolygon`. -/
def squarePieces (c : Plane) (r : ℝ) : List Piece :=
  [(sqNE c r, sqNW c r), (sqNW c r, sqSW c r), (sqSW c r, sqSE c r), (sqSE c r, sqNE c r)]

theorem cover_squarePieces (c : Plane) (hr : 0 ≤ r) :
    cover (squarePieces c r) = frontier (closedSquare c r) := by
  ext z
  rw [Plane.mem_frontier_closedSquare_iff_sides hr]
  simp only [squarePieces, cover_cons, cover_nil, Piece.seg, mem_union, mem_empty_iff_false,
    or_false]

theorem squarePieces_nondeg (c : Plane) (hr : 0 < r) :
    ∀ P ∈ squarePieces c r, P.Nondeg := by
  have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
  have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
  intro P hP
  simp only [squarePieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact hfst _ _ (by simp <;> linarith)
  · exact hsnd _ _ (by simp <;> linarith)
  · exact hfst _ _ (by simp <;> linarith)
  · exact hsnd _ _ (by simp <;> linarith)

/-! ### A vertical side crosses a horizontal side in one point -/

/-- **A vertical segment and a horizontal segment that reach each other meet in exactly one
point.** Both coordinates are pinned, one by each segment. -/
theorem meetOf_vert_horiz {x₀ y₀ u v s t : ℝ}
    (hy : y₀ ∈ segment ℝ u v) (hx : x₀ ∈ segment ℝ s t) :
    meetOf (Plane.mk x₀ u, Plane.mk x₀ v) (Plane.mk s y₀, Plane.mk t y₀) =
      {Plane.mk x₀ y₀} := by
  ext z
  simp only [meetOf, Piece.seg, mem_inter_iff, mem_singleton_iff]
  rw [mem_segment_vert, mem_segment_horiz]
  constructor
  · rintro ⟨⟨hz0, -⟩, ⟨hz1, -⟩⟩
    ext i
    fin_cases i
    · simpa using hz0
    · simpa using hz1
  · rintro rfl
    exact ⟨⟨rfl, hy⟩, ⟨rfl, hx⟩⟩

/-- The same crossing with the two pieces in the other order. -/
theorem meetOf_horiz_vert {x₀ y₀ u v s t : ℝ}
    (hx : x₀ ∈ segment ℝ s t) (hy : y₀ ∈ segment ℝ u v) :
    meetOf (Plane.mk s y₀, Plane.mk t y₀) (Plane.mk x₀ u, Plane.mk x₀ v) =
      {Plane.mk x₀ y₀} := by
  rw [meetOf_comm]
  exact meetOf_vert_horiz hy hx

/-- **Two congruent axis-parallel squares whose centres are less than one radius apart have
boundaries meeting in at least two points**, and each meeting point is a *transversal*
crossing: the two sides that produce it meet in a singleton.

The two centres are not required to be distinct — for equal centres the two squares coincide
and the two points produced are two of the four corners, which is what the blueprint's "or
coincide" allows. -/
theorem exists_two_meets {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r)
    (hd : Plane.supDist c₁ c₂ < r) :
    ∃ p q : Plane, p ≠ q ∧
      (∃ P ∈ squarePieces c₁ r, ∃ Q ∈ squarePieces c₂ r, meetOf P Q = {p}) ∧
      (∃ P ∈ squarePieces c₁ r, ∃ Q ∈ squarePieces c₂ r, meetOf P Q = {q}) := by
  rw [Plane.supDist_eq_max, max_lt_iff, abs_lt, abs_lt] at hd
  obtain ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩ := hd
  -- `ha₁ : -r < c₁ 0 - c₂ 0`, `ha₂ : c₁ 0 - c₂ 0 < r`, and likewise for the second
  -- coordinate.  The four cases are the four sign patterns of `c₂ - c₁`.
  have hfst : ∀ (x y u v : ℝ), x ≠ y → Plane.mk x u ≠ Plane.mk y v := by
    intro x y u v hxy hcon
    exact hxy (by simpa using congrArg (fun p : Plane => p 0) hcon)
  rcases le_or_gt (c₁ 0) (c₂ 0) with hA | hA <;> rcases le_or_gt (c₁ 1) (c₂ 1) with hB | hB
  · -- `c₂` is to the north-east: the right side of `S₁` meets the bottom side of `S₂`, and the
    -- top side of `S₁` meets the left side of `S₂`.
    refine ⟨Plane.mk (c₁ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 - r) (c₁ 1 + r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
  · -- `c₂` is to the south-east.
    refine ⟨Plane.mk (c₁ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₁ 1 - r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
  · -- `c₂` is to the north-west.
    refine ⟨Plane.mk (c₁ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₁ 1 + r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
  · -- `c₂` is to the south-west.
    refine ⟨Plane.mk (c₁ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 + r) (c₁ 1 - r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))

/-! ### From a meeting point to a vertex of the overlay

`Graph.IsTwoConnected.union` needs two common **vertices**, not two common points.  The
overlay's cut-point condition `MeetsAreCut` says that both ends of the meet of two source
pieces are cut points; when the meet is a *singleton* both ends are that one point, so the
crossing point is a cut point, and `overlayGraph_mem_vertexSet_of_mem_cover` promotes a cut
point on the union to a vertex.  This is the whole bridge, and it is why `exists_two_meets` is
stated with singleton meets rather than with mere common points. -/

/-- The crossing point lies on both square boundaries. -/
theorem mem_frontier_of_meetOf_eq_singleton {c₁ c₂ : Plane} {r : ℝ} (hr : 0 ≤ r)
    {P Q : Piece} {p : Plane} (hP : P ∈ squarePieces c₁ r) (hQ : Q ∈ squarePieces c₂ r)
    (h : meetOf P Q = {p}) :
    p ∈ frontier (closedSquare c₁ r) ∧ p ∈ frontier (closedSquare c₂ r) := by
  have hp : p ∈ meetOf P Q := by rw [h]; exact rfl
  constructor
  · rw [← cover_squarePieces c₁ hr]
    exact Set.mem_iUnion₂.2 ⟨P, hP, hp.1⟩
  · rw [← cover_squarePieces c₂ hr]
    exact Set.mem_iUnion₂.2 ⟨Q, hQ, hp.2⟩

/-! ### Localizing a cut point to one source piece

`overlayGraph_mem_vertexSet_of_mem_cover` says a cut point on the union is a vertex, but it
says nothing about *which* edge it is an end of.  The next wave has to place the two common
points of two neighbouring squares in the vertex sets of the two graphs being unioned, and for
that the edge must be pinned inside the boundary it came from.  The three lemmas below do that;
the first two are general facts about `subdivide` whose home is `Schoenflies/Subdivide.lean`. -/

/-- Subdividing is monotone in the piece list. -/
theorem subdivide_mono : ∀ (points : List Plane) {l pieces : List Piece},
    (∀ P ∈ l, P ∈ pieces) → ∀ Q ∈ subdivide l points, Q ∈ subdivide pieces points := by
  intro points
  induction points with
  | nil => intro l pieces h Q hQ; exact h Q hQ
  | cons p ps ih =>
    intro l pieces h Q hQ
    rw [subdivide_cons] at hQ ⊢
    refine ih ?_ Q hQ
    intro R hR
    simp only [splitAllAt, List.mem_flatMap] at hR ⊢
    obtain ⟨P, hP, hRP⟩ := hR
    exact ⟨P, h P hP, hRP⟩

/-- **A cut point on a source piece is an end of an overlay edge inside that source piece.**
This is `overlayGraph_mem_vertexSet_of_mem_cover` with the witnessing edge named and pinned:
the edge lies inside the prescribed source segment, so a subgraph spanned by the edges inside
that segment has the point among its vertices. -/
theorem exists_overlayPiece_end_subset {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hxp : x ∈ points)
    {P₀ : Piece} (hP₀ : P₀ ∈ pieces) (hx : x ∈ P₀.seg) :
    ∃ Q ∈ overlayPieces pieces points, (x = Q.1 ∨ x = Q.2) ∧ Q.seg ⊆ P₀.seg := by
  -- The pieces of the subdivision of `[P₀]` alone already cover `P₀.seg`.
  have hcov : x ∈ cover (subdivide [P₀] points) := by
    rw [subdivide_cover, cover_cons, cover_nil, union_empty]
    exact hx
  simp only [cover, mem_iUnion, exists_prop] at hcov
  obtain ⟨Q, hQ, hxQ⟩ := hcov
  have hQpieces : Q ∈ subdivide pieces points :=
    subdivide_mono points (by simpa using hP₀) Q hQ
  have hQsub : Q.seg ⊆ P₀.seg := by
    obtain ⟨R, hR, hseg, -⟩ := subdivide_subset [P₀] points Q hQ
    rw [List.mem_singleton] at hR
    exact hR ▸ hseg
  have hint : x ∉ Q.interior := subdivide_avoids points hnd x hxp Q hQpieces
  have hend : x = Q.1 ∨ x = Q.2 := by
    by_contra hcon
    push Not at hcon
    exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxQ)
  refine ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQpieces, rfl⟩, ?_, ?_⟩
  · exact (orientPiece_ends Q x).2 hend
  · rw [orientPiece_seg]
    exact hQsub

/-- The localizable form: two distinct **cut points**, each lying on both square boundaries.
Feed a cut point together with "it lies on the union carried by `Γ`" to
`overlayGraph_mem_vertexSet_of_mem_cover` to get a vertex of `Γ`. -/
theorem exists_two_cut_points {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r) (hd : Plane.supDist c₁ c₂ < r)
    (h₁ : ∀ P ∈ squarePieces c₁ r, P ∈ pieces) (h₂ : ∀ P ∈ squarePieces c₂ r, P ∈ pieces) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ points ∧ q ∈ points ∧
      p ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) ∧
      q ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) := by
  -- The cut-point half is `MeetsAreCut` at a singleton meet, exactly as in the vertex lemma.
  have key : ∀ {P Q : Piece} {z : Plane}, P ∈ pieces → Q ∈ pieces → meetOf P Q = {z} →
      z ∈ points := by
    intro P Q z hP hQ hmeet
    have hp : z ∈ meetOf P Q := by rw [hmeet]; exact rfl
    have hPQ : P ≠ Q := by
      rintro rfl
      have hseg : P.seg = {z} := by rw [← hmeet]; exact (Set.inter_self _).symm
      have h1 : P.1 ∈ P.seg := left_mem_segment ℝ _ _
      have h2 : P.2 ∈ P.seg := right_mem_segment ℝ _ _
      rw [hseg, mem_singleton_iff] at h1 h2
      exact hnd P hP (h1.trans h2.symm)
    obtain ⟨u, v, huv, hu, -⟩ := hMeets P hP Q hQ hPQ ⟨z, hp⟩
    have hmem : u ∈ segment ℝ u v := left_mem_segment ℝ _ _
    rw [← huv, hmeet, mem_singleton_iff] at hmem
    exact hmem ▸ hu
  obtain ⟨p, q, hpq, ⟨P, hP, Q, hQ, hp⟩, ⟨P', hP', Q', hQ', hq⟩⟩ := exists_two_meets hr hd
  exact ⟨p, q, hpq, key (h₁ P hP) (h₂ Q hQ) hp, key (h₁ P' hP') (h₂ Q' hQ') hq,
    mem_frontier_of_meetOf_eq_singleton hr.le hP hQ hp,
    mem_frontier_of_meetOf_eq_singleton hr.le hP' hQ' hq⟩

/-! ## Part 3: the uniform-continuity partition

The blueprint asks for "a partition `0 = t₀ < t₁ < ⋯ < t_k = 1`, with `k ≥ 3`, such that every
point of `α([t_{i-1}, t_i])` is at distance less than `ε` from `α(t_{i-1})`", and separately for
a refinement of it inside each piece.  Both are served by the **even** partition: nothing in
the proof uses anything about the partition beyond the mesh bound, and taking `t_i = i/n`
makes "the fine partition refines the coarse one" the arithmetic identity `sample (k*m) (i*m)
= sample k i` rather than a bookkeeping argument.  The number of pieces can be forced to be a
multiple of any prescribed `k` and hence as large as one likes, which covers the `k ≥ 3`
clause. -/

@[simp] theorem sample_zero (n : ℕ) : sample n 0 = 0 := by simp [sample]

theorem sample_last {n : ℕ} (hn : 0 < n) : sample n n = 1 := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [sample, div_self hne]

theorem sample_nonneg (n i : ℕ) : 0 ≤ sample n i :=
  div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n)

theorem sample_mono {n i j : ℕ} (h : i ≤ j) : sample n i ≤ sample n j := by
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  have key : sample n j - sample n i = ((j : ℝ) - i) / n := by simp only [sample] <;> ring
  have hpos : 0 ≤ ((j : ℝ) - i) / n := div_nonneg (by linarith) (Nat.cast_nonneg n)
  linarith [key, hpos]

theorem sample_strictMono {n i j : ℕ} (hn : 0 < n) (h : i < j) :
    sample n i < sample n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hij : (i : ℝ) < j := by exact_mod_cast h
  have key : sample n j - sample n i = ((j : ℝ) - i) / n := by simp only [sample] <;> ring
  have hpos : 0 < ((j : ℝ) - i) / n := div_pos (by linarith) hnR
  linarith [key, hpos]

theorem sample_le_one {n i : ℕ} (h : i ≤ n) : sample n i ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sample, Nat.le_zero.1 h]
  · rw [← sample_last hn]; exact sample_mono h

theorem sample_mem_I {n i : ℕ} (h : i ≤ n) : sample n i ∈ I :=
  ⟨sample_nonneg n i, sample_le_one h⟩

/-- Consecutive samples are `1/n` apart. -/
theorem sample_succ_sub (n i : ℕ) :
    sample n (i + 1) - sample n i = 1 / n := by
  simp only [sample, Nat.cast_add, Nat.cast_one]
  rw [div_sub_div_same]
  norm_num

/-- The fine partition refines the coarse one: the multiples of `m` among the `k*m` samples
are the `k` samples. -/
theorem sample_mul {k m i : ℕ} (hm : 0 < m) : sample (k * m) (i * m) = sample k i := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  simp only [sample, Nat.cast_mul]
  rw [mul_comm (i : ℝ) (m : ℝ), mul_comm (k : ℝ) (m : ℝ), mul_div_mul_left _ _ hmR]

theorem Icc_sample_subset_I {n i : ℕ} (h : i + 1 ≤ n) :
    Icc (sample n i) (sample n (i + 1)) ⊆ I := fun _ hs =>
  ⟨le_trans (sample_nonneg n i) hs.1, le_trans hs.2 (sample_le_one h)⟩

/-- Every parameter lies in one of the `n` closed cells of the even partition. -/
theorem exists_mem_Icc_sample {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : s ∈ I) :
    ∃ i < n, s ∈ Icc (sample n i) (sample n (i + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set j : ℕ := ⌊s * n⌋₊ with hj
  have hs0 : 0 ≤ s := hs.1
  have hjle : (j : ℝ) ≤ s * n := Nat.floor_le (mul_nonneg hs0 hnR.le)
  have hjlt : s * n < j + 1 := Nat.lt_floor_add_one _
  by_cases hjn : j < n
  · refine ⟨j, hjn, ?_, ?_⟩
    · rw [sample, div_le_iff₀ hnR]; exact hjle
    · rw [sample, le_div_iff₀ hnR]; push_cast <;> linarith
  · -- The floor can only reach `n` at `s = 1`; then the last cell contains `s`.
    have hjn' : n ≤ j := Nat.not_lt.1 hjn
    have hsn : s * n ≤ n := by nlinarith [hs.2, hnR.le]
    have hjeq : (j : ℝ) ≤ n := le_trans hjle hsn
    have hjn'' : j = n := le_antisymm (by exact_mod_cast hjeq) hjn'
    have hge : (n : ℝ) ≤ s * n := hjn'' ▸ hjle
    have hs1 : s = 1 := le_antisymm hs.2 (by nlinarith [hge, hnR])
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · rw [hs1]; exact sample_le_one (by omega)
    · rw [show n - 1 + 1 = n from by omega, sample_last hn]; exact hs.2

/-- **The uniform-continuity partition.**  For every `ε > 0` and every prescribed `k > 0` there
is a multiple `k * m` of `k` such that on each cell of the even partition into `k * m` pieces
the map moves by less than `ε`.  Taking `k = 1` gives the plain statement; taking `k` to be the
size of a coarser partition makes this one a refinement of it, by `sample_mul`. -/
theorem exists_mesh {α : ℝ → Plane} (hα : ContinuousOn α I) {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧ ∀ i < k * m, ∀ s ∈ Icc (sample (k * m) i) (sample (k * m) (i + 1)),
      dist (α s) (α (sample (k * m) i)) < ε := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_I.uniformContinuousOn_of_continuous hα) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, Nat.succ_pos N, fun i hi s hs => ?_⟩
  set n : ℕ := k * (N + 1) with hn
  have hnpos : 0 < n := Nat.mul_pos hk (Nat.succ_pos N)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- `1/n < δ`, because `n ≥ N + 1 > 1/δ`.
  have hstep : 1 / (n : ℝ) < δ := by
    have h1 : (1 : ℝ) / δ < n := by
      refine lt_of_lt_of_le hN ?_
      have : N + 1 ≤ n := by
        calc N + 1 = 1 * (N + 1) := (one_mul _).symm
          _ ≤ k * (N + 1) := Nat.mul_le_mul_right _ hk
      exact_mod_cast le_trans (Nat.le_succ N) this
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hnR]
    linarith
  have hiI : sample n i ∈ I := sample_mem_I (by omega)
  have hsI : s ∈ I := Icc_sample_subset_I (n := n) (by omega) hs
  refine hδ' s hsI (sample n i) hiI ?_
  rw [Real.dist_eq, abs_sub_lt_iff]
  have hd := sample_succ_sub n i
  constructor <;> [linarith [hs.1, hs.2]; linarith [hs.1, hs.2]]

/-! ## Part 4: nonadjacent subarcs are at positive distance -/

/-- The `i`-th subarc of the even partition of an arc into `n` pieces. -/
def subarcCell (α : ℝ → Plane) (n i : ℕ) : Set Plane :=
  α '' Icc (sample n i) (sample n (i + 1))

theorem isCompact_subarcCell {α : ℝ → Plane} (hα : ContinuousOn α I) {n i : ℕ}
    (h : i + 1 ≤ n) : IsCompact (subarcCell α n i) :=
  isCompact_image_of_subset_I hα (Icc_sample_subset_I h) isClosed_Icc

/-- Nonadjacent cells of an injective parametrisation are disjoint: their parameter intervals
are, and injectivity carries that to the images. -/
theorem disjoint_subarcCell {α : ℝ → Plane} (hinj : InjOn α I) {n i j : ℕ}
    (hi : i + 1 ≤ n) (hj : j + 1 ≤ n) (hij : i + 2 ≤ j) :
    Disjoint (subarcCell α n i) (subarcCell α n j) := by
  have hn : 0 < n := by omega
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have huI : u ∈ I := Icc_sample_subset_I hi hu
  have hvI : v ∈ I := Icc_sample_subset_I hj hv
  have : v = u := hinj hvI huI hvu
  subst this
  have h1 : v ≤ sample n (i + 1) := hu.2
  have h2 : sample n j ≤ v := hv.1
  have hlt : sample n (i + 1) < sample n j := sample_strictMono hn (by omega)
  exact absurd (lt_of_le_of_lt h2 (lt_of_le_of_lt h1 hlt)) (lt_irrefl _)

/-- **Nonadjacent subarcs are at positive distance** — the blueprint's `δ'`.  A finite family
of positive separations, merged by `exists_pos_forall_of_finite`. -/
theorem exists_pos_dist_nonadjacent {α : ℝ → Plane} (hα : ContinuousOn α I) (hinj : InjOn α I)
    {n : ℕ} :
    ∃ ρ > 0, ∀ i < n, ∀ j < n, i + 2 ≤ j →
      ∀ x ∈ subarcCell α n i, ∀ y ∈ subarcCell α n j, ρ ≤ dist x y := by
  classical
  set S : Set (ℕ × ℕ) := {p | p.1 < n ∧ p.2 < n} with hS
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_Iio n |>.prod (Set.finite_Iio n)) ?_
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    exact ⟨hi, hj⟩
  have hmono : ∀ p : ℕ × ℕ, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε →
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, ε ≤ dist x y) →
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, δ ≤ dist x y) :=
    fun _ _ _ _ hle h had x hx y hy => le_trans hle (h had x hx y hy)
  have hex : ∀ p ∈ S, ∃ ε > 0,
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, ε ≤ dist x y) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    by_cases had : i + 2 ≤ j
    · have hcK : IsCompact (subarcCell α n i) := isCompact_subarcCell hα (by omega)
      have hcL : IsCompact (subarcCell α n j) := isCompact_subarcCell hα (by omega)
      obtain ⟨ρ, hρ, hbound⟩ := Plane.exists_dist_pos hcK hcL
        (disjoint_subarcCell hinj (by omega) (by omega) had)
      exact ⟨ρ, hρ, fun _ => hbound⟩
    · exact ⟨1, one_pos, fun h => absurd h had⟩
  obtain ⟨ρ, hρ, hall⟩ := exists_pos_forall_of_finite hSfin hmono hex
  exact ⟨ρ, hρ, fun i hi j hj had => hall (i, j) ⟨hi, hj⟩ had⟩

/-! ## Part 5: the covering clause -/

/-- **Every point of the arc lies in or on one of the small squares.**  This is what makes the
outer face of the assembled graph disjoint from the arc: a point of the arc is either inside
one of the squares — and then separated from the outer face by that square's boundary cycle —
or on one, and then it is a point of the graph. -/
theorem image_subset_iUnion_closedSquare {α : ℝ → Plane} {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hmesh : ∀ i < n, ∀ s ∈ Icc (sample n i) (sample n (i + 1)),
      dist (α s) (α (sample n i)) < ε) :
    α '' I ⊆ ⋃ i ∈ Finset.range n, closedSquare (α (sample n i)) ε := by
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨i, hi, hmem⟩ := exists_mem_Icc_sample hn hs
  refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, ?_⟩
  have hd : dist (α s) (α (sample n i)) < ε := hmesh i hi s hmem
  change Plane.supDist (α s) (α (sample n i)) ≤ ε
  calc Plane.supDist (α s) (α (sample n i)) = Plane.supNorm (α s - α (sample n i)) := rfl
    _ ≤ ‖α s - α (sample n i)‖ := Plane.supNorm_le_norm _
    _ = dist (α s) (α (sample n i)) := (dist_eq_norm _ _).symm
    _ ≤ ε := le_of_lt hd

/-! ## The shape of `lem:outer-chain` this module expects to be handed

This is a note to the integrator, not a declaration.  `thm:arc-complement` consumes the
outer-chain lemma exactly once, and the form that makes the assembly short is the following.
`Γ : ℕ → Graph Plane Piece` are the chain graphs, all subgraphs of **one** overlay graph `G`
built from the concatenation of the `squarePieces` of every sample — so that "after subdividing
common points into vertices" is discharged by construction rather than assumed, and so that all
the `Γ i` are `Graph.Compatible` with each other for free (they share edge names because they
share the ambient edge type `Piece`).

```
theorem outer_chain {k : ℕ} (hk : 3 ≤ k) (Γ : ℕ → Graph Plane Piece)
    (drawing : Piece → ℝ → Plane)
    (hfin : ∀ i < k, (Γ i).Finite)
    (hdraw : ∀ i < k, Graph.IsDrawing (Γ i) drawing)
    (h2c : ∀ i < k, (Γ i).IsTwoConnected)
    (hshare : ∀ i, i + 1 < k → ∃ a b : Plane, a ≠ b ∧
      a ∈ V(Γ i) ∧ a ∈ V(Γ (i+1)) ∧ b ∈ V(Γ i) ∧ b ∈ V(Γ (i+1)))
    (hfar : ∀ i j, i < k → j < k → i + 2 ≤ j →
      Disjoint (Graph.pointSet (Γ i) drawing) (Graph.pointSet (Γ j) drawing))
    {x : Plane}
    (houter : ∀ i, i + 1 < k → ¬ Bornology.IsBounded
      (Graph.face ((Γ i).union (Γ (i+1))) drawing x)) :
    ¬ Bornology.IsBounded (Graph.face (chainUnion Γ k) drawing x)
```

with `chainUnion Γ k` the fold of `Graph.union` over `i < k`, exported as a `def` with
`vertexSet` / `edgeSet` / `IsLink` lemmas.  Three things matter for the join:

* **"outer face" must be stated as `¬ IsBounded (face …)`, not as `face … = face … base` for
  some chosen base point.**  `Graph.exists_unbounded_face` and `Graph.unbounded_face_unique`
  make the two equivalent, but the arc-complement proof gets its hypothesis from
  `Graph.beyondSquare_subset_face` applied to a containing square, which is naturally an
  unboundedness statement about `x`'s own face.
* **`hshare` must be about vertices**, which is what `exists_two_common_vertices` and
  `exists_two_cut_points` + `exists_overlayPiece_end_subset` above deliver.  Two common
  *points* would not compose with `Graph.IsTwoConnected.union`.
* **`hfar` is about point sets, not vertex sets.**  The arc-complement proof gets it from
  `exists_pos_dist_nonadjacent`: nonadjacent samples are at distance `≥ δ` while the squares
  have radius `δ/4`, so the two point sets are `δ/2` apart.
-/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Graph.chainUnion_succ _root_.Graph.pointSet_union _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

/-! ### Deleting one vertex -/

/-! ### Walks across a vertex deletion -/

/-! ### Cut vertices -/

/-! ### At least three vertices -/

/-! ### Two-connectivity -/

/-! ### The union of two graphs -/

/-- **`lem:union-two-connected`**: two 2-connected graphs with at least two vertices in common
have 2-connected union.

The blueprint's proof is one sentence — after deleting one vertex, each graph remains
connected and at least one common vertex remains. The work is the case where the deleted
vertex belongs to only one of the two graphs: the other graph never had it, so nothing was
deleted from it, and `Graph.deleteVerts_singleton_eq_self` makes that a rewriting step rather
than an argument. -/
theorem IsTwoConnected.union (hcompat : G.Compatible H) (hG : G.IsTwoConnected)
    (hH : H.IsTwoConnected) (hab : a ≠ b) (haG : a ∈ V(G)) (haH : a ∈ V(H)) (hbG : b ∈ V(G))
    (hbH : b ∈ V(H)) : (G.union H).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G H).vertexSet_mono
  connected := hcompat.union_connected hG.connected hH.connected haG haH
  deleteVerts_connected := by
    intro x _
    -- One of the two common vertices survives the deletion.
    obtain ⟨c, hcG, hcH, hcx⟩ : ∃ c, c ∈ V(G) ∧ c ∈ V(H) ∧ c ≠ x := by
      by_cases ha : a = x
      · exact ⟨b, hbG, hbH, by rintro rfl; exact hab ha⟩
      · exact ⟨a, haG, haH, ha⟩
    refine Connected.of_two_subgraphs (G₁ := G.deleteVerts {x}) (G₂ := H.deleteVerts {x})
      (deleteVerts_mono (left_le_union G H) _) (deleteVerts_mono hcompat.right_le_union _)
      ?_ (hG.deleteVerts_connected' x) (hH.deleteVerts_connected' x)
      (mem_deleteVerts_singleton_of_ne hcG hcx) (mem_deleteVerts_singleton_of_ne hcH hcx)
    simp [union_sdiff_distrib]

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Combinatorial invariance

The first module of Part II. It introduces the abstract record of a matched cellulation, the
notion of a geometric realization of that record, and proves that everything a realization
inherits from the record is the same for two realizations of one record —
`lem:combinatorial-invariance`.

Per the blueprint's citation index this lemma has no internal prerequisites: the whole point of
the design is that the combinatorial content of the cellulation machinery is separated from all
of the geometry, so this can be built while the Jordan curve theorem is still unproved.

## What is defined here, and how faithful it is

`CellStructure` is the *abstract* record of `def:matched-cellulation`: the finite cell sets in
each dimension, the endpoint maps, the outer subcomplex, the boundary walks, and the subcell
relation. Cells of all three dimensions are names drawn from one type `γ`; the 0- and 1-cells
are the vertices and the edges of an abstract multigraph `skel : Graph γ γ`, the 2-cells are a
set `faces`, and the three collections are disjoint. What is deliberately **not** in the record:
the parent maps (they belong to a refinement — a pair of stages — not to a stage), and any
compatibility between `sub` and the realizations (that is assertion (ix) of
`lem:cellulation-invariants`, and the blueprint is explicit that `≼_abs` "enters as a raw
datum"). No reflexivity or transitivity of `sub` is assumed; the one lemma that needs
transitivity takes it as a hypothesis.

`CellStructure.Realization` is one of the two geometric realizations. The repository's plane
graphs have `V(G) : Set Plane` — vertices *are* points — so the drawn skeleton cannot literally
be the abstract graph. It is instead the pushforward `S.skel.map pos` along the positions of
the 0-cells, with `pos` injective on `V(S.skel)`. This is the representation choice of the
module, and the alternative — carrying an abstract graph isomorphism as data — was rejected
because with the pushforward "the two skeleta realize the *same* abstract graph" is a
definitional identity rather than a theorem, which is exactly what the blueprint's proof of
part (a) asserts.

The price of the choice is paid here, once: `Graph.isTwoConnected_map_iff` and
`Graph.connected_map_iff` transport connectivity along an injective relabelling of the
vertices, so that 2-connectivity of the *drawn* graph — which is what
`def:admissible-graph` requires — transfers between the realizations. Those two, and the walk
and vertex-deletion lemmas they rest on, are general facts about `Graph.map` in the root
`Graph` namespace and belong in `Schoenflies/Graph/` if a second consumer appears.

`SkeletonHomeo` is `g : |Γ| → |Γ'|` of `def:matched-pair`, as a set-level homeomorphism with
its inverse supplied as data (so that no finiteness hypothesis is needed to invert it).
Clause 3 of `def:matched-pair` is recorded in the weaker form "`g` carries each drawn edge onto
the corresponding drawn edge", which is all that is used and which the full clause implies.

## The three parts of the lemma

Only part (b) has topological content. Parts (a) and (c) are, under this representation, either
definitional identities or one-line consequences of the fact that the index sets involved are
fields of the single structure both realizations realize; that is precisely the blueprint's
argument ("all the data in (c) belong to the common abstract cell structure"), and the
statements below are shaped so that a consumer gets the geometric conclusion on *both* sides
from one combinatorial hypothesis.

## Blueprint

* `Schoenflies.CellStructure` — the abstract record of `def:matched-cellulation`.
* `Schoenflies.CellStructure.Realization` — one of its two geometric realizations.
* `Schoenflies.CellStructure.Realization.nonboundary` — the open nonboundary part
  `|Γ| \ C` of `def:admissible-graph`.
* `Schoenflies.CellStructure.Realization.star` — the closed star `St(σ) = ⋃_{σ ≼ τ} closure τ`.
* `Schoenflies.CellStructure.SkeletonHomeo` — the skeleton homeomorphism of
  `def:matched-pair`.
* `Schoenflies.CellStructure.combinatorial_invariance` — `lem:combinatorial-invariance`,
  assembled from:
  * (a) `Realization.graph_eq_map`, `Realization.edgeSet_graph_congr`,
    `Realization.isTwoConnected_congr`, `SkeletonHomeo.image_outerSet`;
  * (b) `SkeletonHomeo.image_nonboundary`, `SkeletonHomeo.isConnected_nonboundary_iff`;
  * (c) `Realization.star_mono`, `Realization.star_transfer`,
    `Realization.star_subset_of_sub`, `outerEdge_face_corresponds`.
* `Graph.isTwoConnected_map_iff`, `Graph.connected_map_iff` — connectivity is invariant under
  an injective relabelling of the vertices; the transport that the pushforward representation
  of a realization needs.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

namespace CellStructure

variable (S : CellStructure γ)

/-! ### Realizations -/

namespace Realization

variable {S}
variable (R : S.Realization)

theorem outerSet_subset_skeletonSet : R.outerSet ⊆ R.skeletonSet :=
  pointSet_mono (S.outerGraph_le.map R.pos)

end Realization

/-! ### The skeleton homeomorphism -/

/-! ### Combinatorial invariance -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Component
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet _root_.Graph.pathGraphOf_isLink _root_.Graph.pathGraphOf_vertexSet _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Components and shortest paths

The two prerequisites of the relative ear decomposition (`lem:relative-ear`) that no earlier
module builds: the **component** of a vertex, and a **shortest** walk between two vertices.
Both are then spent on the geometric heart of that lemma — a component of `G - S` has two
distinct neighbours in `S`, and a path between two of them whose interior lies outside `S`.

## The component is a comprehension

`G.component u = {v | G.Reaches u v}`, exactly as `connectedComponentIn` collects the points
a space reaches. Nothing restricts the comprehension to `V(G)`: the empty walk already demands
a vertex of the graph (`Graph.IsWalk.nil`), so `G.Reaches u v` carries `v ∈ V(G)` with it, and
a clause `v ∈ V(G) ∧ …` would be redundant noise at every use site. When `u ∉ V(G)` the
component is empty, which is the convention that makes the covering statement
`Graph.iUnion_component` true with no side condition.

Reachability is an equivalence relation on `V(G)`, so the component is closed under `Reaches`,
two components are equal or disjoint, and the components cover `V(G)`. The one statement that
is not pure equivalence-relation bookkeeping is that the **induced** subgraph on a component
is connected: a walk between two vertices of a component never leaves it
(`Graph.IsWalk.walkVertices_subset_component`), so it is already a walk of the induced
subgraph, by `Graph.IsWalk.anti`.

## Shortest walks need no finiteness

The set of lengths of walks from `u` to `v` is a nonempty set of naturals, so it has a least
element — `Nat.find`, with no `Graph.Finite` hypothesis anywhere. That is worth noticing: the
blueprint says "in a finite graph", but finiteness is used there only to terminate the ear
*process*, never to find one shortest path.

A minimum-length walk is automatically a path (`Graph.IsWalk.isPath_of_minLength`). The proof
is the induction of `Graph.IsWalk.contains_path` run once more, with lengths attached: if the
step's source were revisited later, `Graph.IsPath.from_visited` would cut the tail down to a
strictly shorter walk with the same ends, and a path's edge list repeats nothing
(`Graph.IsPath.nodup`), so the cut piece really is no longer than what it came from
(`List.subperm_of_subset`).

## The two neighbours, without a contradiction

The blueprint argues by contradiction: "otherwise its unique neighbour would be a cut vertex".
Here the two neighbours are *constructed*, in the shape `Graph.IsTwoConnected.no_bridge`
already uses. A walk from the component out to a vertex of `S` crosses the boundary
(`Graph.IsWalk.crossing`), and the crossing edge's far end is in `S` — because a neighbour
outside `S` would still be in the component. That is the first neighbour `c`. For the second,
delete `c`: the big graph is still connected, so the same crossing argument runs inside
`G - c`, and its crossing edge's far end is a neighbour that is not `c`.

Two distinct vertices of `S` are needed, and used exactly once: the walk of the second step
must aim at a vertex of `S` other than `c`. In the application `S` is the vertex set of a
2-connected subgraph, which has three.

## Blueprint

* `Graph.component`, `Graph.induce_component_connected` — "a component `L` of `G - V(H₀)`" in
  the proof of `lem:relative-ear`.
* `Graph.exists_minLength_isPath` — "a shortest path through `L`", same proof.
* `Graph.IsTwoConnected.component_two_neighbors` — "if a component `L` of `G - V(H₀)` contains
  a vertex, it has at least two distinct neighbors in `H₀`; otherwise its unique neighbor
  would be a cut vertex of `G`".
* `Graph.IsTwoConnected.exists_path_through_component` — "a shortest path through `L` between
  two such neighbors is an ear": a path of `G` between two distinct vertices of `S`, whose
  every other vertex is outside `S`, which has at least one such vertex, and each of whose
  edges has an end outside `S`. The word *ear* is not used here and nothing about ears is
  assumed; this is the raw path that a consumer recognises as one.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

/-! ### Components -/

theorem component_subset_vertexSet : G.component u ⊆ V(G) := fun _ h ↦ Reaches.right_mem h

theorem mem_component_self (hu : u ∈ V(G)) : u ∈ G.component u := Reaches.refl hu

/-- **A component is closed under reachability**, which is the property every consumer uses:
whatever a vertex of the component reaches is in the component. -/
theorem mem_component_of_reaches (hv : v ∈ G.component u) (h : G.Reaches v w) :
    w ∈ G.component u :=
  Reaches.trans hv h

/-- A component is closed under taking an edge. -/
theorem mem_component_of_isLink (hx : x ∈ G.component u) (hl : G.IsLink e x y) :
    y ∈ G.component u :=
  mem_component_of_reaches hx (Reaches.of_isLink hl)

/-! ### The subgraph induced on a component -/

/-! ### Shortest walks and shortest paths -/

/-- **A shortest walk is a path.** If the vertex a step departs from were visited again, the
tail could be cut there (`Graph.IsPath.from_visited`) and the result would be a strictly
shorter walk with the same ends — strictly, because a path repeats no edge and the cut piece
is a sublist-up-to-permutation of what it came from. -/
theorem IsWalk.isPath_of_minLength (h : G.IsWalk u W v)
    (hmin : ∀ W', G.IsWalk u W' v → W.length ≤ W'.length) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW ih =>
    -- The tail is shortest among walks from the waypoint: prepending `e` to a shorter one
    -- would beat the whole walk.
    have hmin' : ∀ W', G.IsWalk w W' v → W.length ≤ W'.length := fun W' hW' ↦ by
      have := hmin (e :: W') (.cons hl hW')
      simp only [List.length_cons] at this
      omega
    have hP : G.IsPath w W v := ih hmin'
    refine .cons hl hP fun hmem ↦ ?_
    obtain ⟨T, hT, hTW⟩ := hP.from_visited hmem
    have h₁ : T.length ≤ W.length := (List.subperm_of_subset hT.nodup hTW).length_le
    have h₂ := hmin T hT.isWalk
    simp only [List.length_cons] at h₂
    omega

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

/-- The component of `G - S` at `x`, seen in `G`: outside `S`, and inside `V(G)`. -/
theorem component_deleteVerts_subset : (G.deleteVerts S).component x ⊆ V(G) \ S := by
  intro z hz
  have := component_subset_vertexSet hz
  rwa [vertexSet_deleteVerts] at this

/-- **A neighbour of a component of `G - S` that is outside `S` is in the component.** The
edge joining them survives the deletion, so it extends the walk. -/
theorem mem_component_deleteVerts_of_isLink (hp : p ∈ (G.deleteVerts S).component x)
    (hl : G.IsLink e p q) (hq : q ∉ S) : q ∈ (G.deleteVerts S).component x :=
  mem_component_of_isLink hp
    ((deleteVerts_isLink G S).2 ⟨hl, (component_deleteVerts_subset hp).2, hq⟩)

/-- **Walking out of a component of `G - S` meets `S` along an edge.** The walk may live in
any subgraph `K` of `G` — it is run inside `G - c` once — but the component is always the one
of `G - S`, which is what makes the conclusion usable twice.

This is `Graph.IsWalk.crossing` plus the previous lemma: the crossing edge's far end is
outside the component, so it cannot be outside `S`. -/
theorem exists_isLink_out_of_component {K : Graph α β} (hKG : K ≤ G)
    (h : K.IsWalk x W v) (hx : x ∈ (G.deleteVerts S).component x) (hv : v ∈ S) :
    ∃ p ∈ (G.deleteVerts S).component x, ∃ g ∈ W, ∃ t ∈ S, K.IsLink g p t := by
  have hvL : v ∉ (G.deleteVerts S).component x := fun hmem ↦
    (component_deleteVerts_subset hmem).2 hv
  obtain ⟨g, hg, s, t, hst, hs, ht⟩ := h.crossing hx hvL
  refine ⟨s, hs, g, hg, t, ?_, hst⟩
  by_contra htS
  exact ht (mem_component_deleteVerts_of_isLink hs (hst.mono hKG) htS)

/-! ### The two neighbours of a component, and the path through it -/

/-- **A component of `G - S` has two distinct neighbours in `S`** — the first half of
`lem:relative-ear`, with the blueprint's contradiction turned into a construction.

`S` must contain two distinct vertices; in the application it is the vertex set of a
2-connected subgraph, which has three. The first neighbour `c` comes from a walk of `G` out of
the component to a vertex of `S`; the second from the same walk run inside `G - c`, which is
still connected because `G` is 2-connected, and aimed at a vertex of `S` other than `c`. -/
theorem IsTwoConnected.component_two_neighbors (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (∃ p ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g p c) ∧
      (∃ q ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g q d) := by
  have hxD : x ∈ V(G.deleteVerts S) := by rw [vertexSet_deleteVerts]; exact ⟨hx, hxS⟩
  have hxL : x ∈ (G.deleteVerts S).component x := mem_component_self hxD
  -- First neighbour: walk from `x` to `a` in `G` and take the edge where it leaves.
  obtain ⟨W, hW⟩ := hG.connected.reaches hx (hS ha)
  obtain ⟨p, hp, g, -, c, hc, hgpc⟩ := exists_isLink_out_of_component le_rfl hW hxL ha
  -- Second neighbour: aim at a vertex of `S` other than `c`, inside `G - c`.
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ S, t ≠ c := by
    rcases eq_or_ne a c with rfl | hac
    · exact ⟨b, hb, fun h ↦ hab h.symm⟩
    · exact ⟨a, ha, hac⟩
  have hxc : x ∈ V(G.deleteVerts {c}) :=
    mem_deleteVerts_singleton_of_ne hx fun h ↦ hxS (h ▸ hc)
  have htc' : t ∈ V(G.deleteVerts {c}) := mem_deleteVerts_singleton_of_ne (hS ht) htc
  obtain ⟨W', hW'⟩ := (hG.deleteVerts_connected' c).reaches hxc htc'
  obtain ⟨q, hq, g', -, d, hd, hgqd⟩ :=
    exists_isLink_out_of_component deleteVerts_le hW' hxL ht
  -- The second crossing edge lives in `G - c`, so its far end is not `c`.
  have hdc : d ≠ c := by
    have := ((deleteVerts_isLink G {c}).1 hgqd).2.2
    simpa using this
  exact ⟨c, hc, d, hd, fun h ↦ hdc h.symm, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd.mono deleteVerts_le⟩⟩

/-- **The path through a component** — the second half of `lem:relative-ear`, without the word
*ear*: in a 2-connected `G`, from a vertex outside a set `S` that has two distinct vertices,
one gets a path of `G` whose two endpoints are distinct vertices of `S`, whose every other
vertex is outside `S`, which has at least one vertex outside `S`, and each of whose edges has
an end outside `S`.

The last two clauses are what make the ear process terminate and what make the path *new*: it
really does add a vertex, and none of its edges belongs to a subgraph whose vertices all lie
in `S`.

The path is built from the two neighbours of the component: the edge into the component, a
path across the component (in `G - S`, hence never touching `S`), and the edge back out. -/
theorem IsTwoConnected.exists_path_through_component (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, ∃ P, c ≠ d ∧ G.IsPath c P d ∧
      (∀ y ∈ G.walkVertices c P, y ≠ c → y ≠ d → y ∉ S) ∧
      (∃ y ∈ G.walkVertices c P, y ∉ S) ∧
      ∀ f ∈ P, ∃ y, G.Inc f y ∧ y ∉ S := by
  obtain ⟨c, hc, d, hd, hcd, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd⟩⟩ :=
    hG.component_two_neighbors hS ha hb hab hx hxS
  have hpS : p ∉ S := (component_deleteVerts_subset hp).2
  have hqS : q ∉ S := (component_deleteVerts_subset hq).2
  -- A path across the component, taken in `G - S` so that it cannot touch `S`.
  obtain ⟨Q, hQ⟩ := Reaches.exists_isPath (Reaches.trans (Reaches.symm hq) hp)
  have hQvert : G.walkVertices q Q ⊆ V(G) \ S :=
    hQ.isWalk.walkVertices_subset_of_deleteVerts
  have hQG : G.IsPath q Q p := hQ.mono deleteVerts_le
  -- Cap it with the edge `p — c`, which is fresh because `c ∈ S`.
  have hcQ : c ∉ G.walkVertices q Q := fun hmem ↦ (hQvert hmem).2 hc
  have hQc : G.IsPath q (Q ++ [g]) c := hQG.extend_at_target hgpc hcQ
  -- Prepend the edge `d — q`, fresh because `d ∈ S` and `d ≠ c`.
  have hdQc : d ∉ G.walkVertices q (Q ++ [g]) := by
    intro hmem
    rcases mem_walkVertices_append_singleton hmem with hmem' | hinc
    · exact (hQvert hmem').2 hd
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS hd, hcd rfl]
  have hpath : G.IsPath d (g' :: (Q ++ [g])) c := .cons hgqd.symm hQc hdQc
  refine ⟨d, hd, c, hc, _, fun h ↦ hcd h.symm, hpath, fun y hy hyd hyc ↦ ?_,
    ⟨q, mem_walkVertices_cons_of_mem hgqd.symm mem_walkVertices_self, hqS⟩, fun f hf ↦ ?_⟩
  · -- Every vertex is `d`, `c`, or one that `G - S` reached.
    rcases mem_walkVertices_cons hgqd.symm hy with rfl | hy'
    · exact absurd rfl hyd
    rcases mem_walkVertices_append_singleton hy' with hmem | hinc
    · exact (hQvert hmem).2
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS, absurd rfl hyc]
  · -- Every edge touches the component: the two capping edges at `q` and at `p`, the rest at
    -- both of their ends.
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨q, hgqd.inc_left, hqS⟩
    rcases List.mem_append.1 hf' with hf' | hf'
    · have hfE := hQ.isWalk.edge_mem hf'
      rw [edgeSet_deleteVerts] at hfE
      obtain ⟨s, t, hst, hs, -⟩ := hfE
      exact ⟨s, hst.inc_left, hs⟩
    · obtain rfl : f = g := by simpa using hf'
      exact ⟨p, hgpc.inc_left, hpS⟩

end Graph
end

section
-- module Solutions.Q146_CD.Graph_PathGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

/-! ### Reaching an end of a path after a deletion -/

/-! ### A graph that is a path -/

namespace IsPathGraph

theorem mem_edgeSet (h : P.IsPathGraph u W v) (he : e ∈ W) : e ∈ E(P) := by
  rw [h.edgeSet_eq]; exact he

theorem target_mem (h : P.IsPathGraph u W v) : v ∈ V(P) := h.isPath.right_mem

end IsPathGraph

/-! ### Constructing a path graph -/

/-- The path runs inside the subgraph it spans. -/
theorem IsPath.pathGraphOf (h : G.IsPath u W v) : (G.pathGraphOf u W).IsPath u W v :=
  h.anti (pathGraphOf_le h.isWalk) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h.isWalk) ▸ he

/-- **A path of `G` spans a path graph.** This is the construction the whole file exists
for: the object every `Graph.IsPathGraph` hypothesis elsewhere is discharged by. -/
theorem IsPath.isPathGraph_pathGraphOf (h : G.IsPath u W v) :
    (G.pathGraphOf u W).IsPathGraph u W v where
  isPath := h.pathGraphOf
  edgeSet_eq := pathGraphOf_edgeSet h.isWalk
  vertexSet_eq := by rw [pathGraphOf_vertexSet, walkVertices_pathGraphOf]

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Tree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

open Set
open scoped Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

namespace Graph

/-! ### Trees -/

/-! ### A walk departs along an edge -/

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-! ### A longest path -/

/-- A path repeats no edge, so it is no longer than the graph has edges. -/
theorem IsPath.length_le_ncard_edgeSet [G.Finite] (h : G.IsPath u P v) :
    P.length ≤ E(G).ncard := by
  classical
  have hsub : P.toFinset ⊆ G.edgeFinset := fun f hf ↦
    mem_edgeFinset.2 (h.edge_mem (List.mem_toFinset.1 hf))
  calc P.length = P.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
    _ = E(G).ncard := card_edgeFinset

/-- **A finite graph with a vertex has a longest path.** The lengths of paths are bounded by
the number of edges, so `Nat.findGreatest` picks the largest length that occurs, and the
witnessing path is longest. -/
theorem exists_longest_path [G.Finite] (hu : u ∈ V(G)) :
    ∃ x y Q, G.IsPath x Q y ∧ ∀ x' y' (Q' : List β), G.IsPath x' Q' y' → Q'.length ≤ Q.length := by
  classical
  -- `p n` : some path has length exactly `n`.
  set p : ℕ → Prop :=
    fun n ↦ ∃ (x : α) (y : α) (Q : List β), G.IsPath x Q y ∧ Q.length = n with hp
  have hp0 : p 0 := ⟨u, u, [], .nil hu, rfl⟩
  obtain ⟨x, y, Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le E(G).ncard) hp0
  refine ⟨x, y, Q, hQ, fun x' y' Q' hQ' ↦ ?_⟩
  have hle := Nat.le_findGreatest (P := p) hQ'.length_le_ncard_edgeSet ⟨x', y', Q', hQ', rfl⟩
  omega

/-! ### Both ends of a longest path are leaves -/

/-! ### A path steers clear of a leaf -/

/-! ### Vertex deletion -/

/-! ### A tree has one edge fewer than it has vertices -/

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_RelativeEar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-! ### The relative ear -/

/-- **`lem:relative-ear`, the ear.** A 2-connected subgraph `K` of a loopless 2-connected `G`
that is missing a vertex or an edge has a *relative* ear: a path of `G` whose two distinct
endpoints lie in `K`, whose every other vertex lies **outside** `K`, and none of whose edges
belongs to `K`.

This is the blueprint's own construction, and the freshness of the interior is what
distinguishes it from `Graph.IsTwoConnected.ear_exists`. The first branch takes a component
`L` of `G - V(K)` and a path across it between two of its neighbours in `K`
(`Graph.IsTwoConnected.exists_path_through_component`); the two distinct vertices of `V(K)`
that construction needs are supplied by the counting clause of `K.IsTwoConnected`. The second
branch is the blueprint's "if all vertices are already present, add a missing edge as an ear
of length one", and it is the only place looplessness is used. -/
theorem IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    -- The subgraph's three vertices supply the two distinct targets the component needs.
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    -- Each edge of the ear has an end outside `V(K)`, so it is not an edge of `K`.
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · -- Every vertex is already present, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · -- A one-edge path visits nothing but its two ends, so freshness is vacuous.
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

/-- **One step of the relative ear decomposition.** The ear of
`Graph.IsTwoConnected.relative_ear_exists`, glued on with `Graph.IsTwoConnected.ear`: the
enlarged graph is again a 2-connected subgraph of `G` between `K` and `G`, and it has an edge
that `K` did not have.

The ear data is handed back alongside the enlarged graph, because a consumer of the geometric
version needs the *path*, not merely the fact that the subgraph grew. -/
theorem IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

/-! ### Iterating: the decomposition itself -/

/-- **`lem:relative-ear`.** A 2-connected subgraph `K` of a finite loopless 2-connected graph
`G` grows to `G` by repeatedly adding relative ears, stated as the induction principle a
consumer uses: whatever holds of `K` and survives the addition of one ear holds of `G`.

The step is given the whole ear — the path `D` of `G`, its two distinct ends in the current
subgraph `B`, and the fact that its other vertices are outside `B` — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`.

"Finiteness terminates the process" is the strong induction below on `(E(G) \ E(B)).ncard`:
every ear contributes an edge of `G` that `B` was missing, and the process can only be stuck
when `B` has all of `G`'s vertices and edges, which makes `B = G`. -/
theorem IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  -- One step, packaged with the strict drop of the measure.
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    -- A subgraph that is not the graph is missing a vertex or an edge.
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    -- The new edge is one the old subgraph was missing, and nothing was lost.
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  -- Strong induction on the number of edges of `G` the subgraph is still missing.
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · -- Nothing is missing, yet an ear was found: its edges were missing after all.
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end Graph
end

section
-- module Solutions.Q146_CD.FaceCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Graph.chainUnion_succ
/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-- **A vertex of a loopless 2-connected graph has a neighbour other than any prescribed
vertex** — in particular it has two distinct neighbours, and neither is itself. -/
theorem IsTwoConnected.exists_adj_ne (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) (hv : v ∈ V(G)) (w : α) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  rcases eq_or_ne v w with rfl | hvw
  · -- Deleting nothing: a walk to any other vertex leaves along a non-loop.
    obtain ⟨z, hz, hzv, -⟩ := h.hasThreeVertices.exists_ne_ne v v
    obtain ⟨T, hT⟩ := h.connected.reaches hv hz
    cases hT with
    | nil => exact absurd rfl hzv
    | @cons _ y _ g _ hl _ => exact ⟨y, ⟨g, hl⟩, fun hh ↦ hnl (hh ▸ hl)⟩
  · -- Deleting `w`: a walk to a third vertex leaves along an edge that survived it.
    obtain ⟨z, hz, hzv, hzw⟩ := h.hasThreeVertices.exists_ne_ne v w
    obtain ⟨T, hT⟩ := (h.deleteVerts_connected' w).reaches
      (mem_deleteVerts_singleton_of_ne hv hvw) (mem_deleteVerts_singleton_of_ne hz hzw)
    cases hT with
    | nil => exact absurd rfl (Ne.symm hzv)
    | @cons _ y _ g _ hl _ =>
      exact ⟨y, ⟨g, hl.mono deleteVerts_le⟩, (mem_deleteVerts_singleton.1 hl.right_mem).2⟩

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

/-- The two ends of the edge are distinct: otherwise the detour would be a path from a vertex
to itself, hence empty, and would visit no third vertex. -/
theorem ne : u ≠ v := by
  rintro rfl
  have hnil : D = [] := h.isPath.eq_nil_of_eq
  have hmem := h.mem
  rw [hnil, walkVertices_nil] at hmem
  exact h.ne_left hmem

end IsLongCycle

/-- **"The resulting closed subpath is a cycle of length at least three."** A finite loopless
2-connected graph has a cycle with three distinct vertices.

Take a maximal path `u —W→ v`. Its source `u` has a neighbour `x` other than the vertex `w₀`
the path first steps to (`Graph.IsTwoConnected.exists_adj_ne`), and `x` lies on the path:
otherwise the edge to it could be prepended, contradicting maximality. Cutting the path at `x`
gives a path from `u` to `x` whose first step is still to `w₀`, and the chord closes it into a
cycle through `u`, `w₀` and `x`. The chord is not an edge of that piece: an edge at `u` in the
tail is what the path's freshness clause forbids, and the first edge is not the chord because
their far ends differ. -/
theorem IsTwoConnected.exists_long_cycle [G.Finite] (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) :
    ∃ g u x D w, G.IsLongCycle g u x D w := by
  obtain ⟨p, hp, -⟩ := h.hasThreeVertices
  obtain ⟨u, v, W, hpath, hmax⟩ := exists_longest_path hp
  -- The maximal path is not empty: an edge at its source could otherwise be prepended.
  obtain ⟨f, W', rfl⟩ : ∃ f W', W = f :: W' := by
    cases hW : W with
    | cons f W' => exact ⟨f, W', rfl⟩
    | nil =>
      obtain ⟨y, ⟨g, hl⟩, hyu⟩ := h.exists_adj_ne hnl hpath.left_mem u
      have hle := hmax _ _ _ (IsPath.single hl.symm hyu)
      rw [hW] at hle
      simp at hle
  obtain ⟨w₀, hl₀, hpath', hfresh⟩ : ∃ w₀, G.IsLink f u w₀ ∧ G.IsPath w₀ W' v ∧
      u ∉ G.walkVertices w₀ W' := by
    cases hpath with
    | cons hl hW hfr => exact ⟨_, hl, hW, hfr⟩
  -- A second neighbour of the source, distinct from the vertex the path first steps to.
  obtain ⟨x, ⟨g, hlg⟩, hxw₀⟩ := h.exists_adj_ne hnl hpath.left_mem w₀
  have hxu : x ≠ u := fun hh ↦ hnl (hh ▸ hlg)
  -- It lies on the path: otherwise the chord would prepend to it.
  have hxW : x ∈ G.walkVertices u (f :: W') := by
    by_contra hx
    have hle := hmax _ _ _ (IsPath.cons hlg.symm hpath hx)
    simp at hle
  obtain ⟨W₁, W₂, hsplit, h₁, -, -⟩ := hpath.split hxW
  have hW₁sub : W₁ ⊆ f :: W' := hsplit ▸ List.subset_append_left _ _
  -- The chord is not an edge of the piece: not the first edge, and not one further along.
  have hgW₁ : g ∉ W₁ := by
    intro hg
    rcases List.mem_cons.1 (hW₁sub hg) with rfl | hg'
    · exact hxw₀ (hlg.right_unique hl₀)
    · exact hfresh (mem_walkVertices_of_mem_covered ⟨g, hg', hlg.inc_left⟩)
  -- The piece starts with the first edge, so it visits the vertex the path first stepped to.
  have hfW₁ : f ∈ W₁ := by
    rcases W₁ with _ | ⟨a, T⟩
    · exact absurd h₁.isWalk.eq_of_nil (Ne.symm hxu)
    · obtain ⟨rfl, -⟩ : f = a ∧ W' = T ++ W₂ := by simpa using hsplit
      exact List.mem_cons_self
  exact ⟨g, u, x, W₁, w₀, ⟨hlg, h₁, hgW₁⟩,
    mem_walkVertices_of_mem_covered ⟨f, hfW₁, hl₀.inc_right⟩,
    fun hh ↦ hnl (hh ▸ hl₀), Ne.symm hxw₀⟩

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

/-- **A cycle with three vertices is 2-connected**, which is what
`Graph.IsTwoConnected.ear_decomposition` asks of its starting subgraph.

Delete a vertex `c`. One of the two ends of the cycle's edge survives, and it is the hub:
every remaining vertex reaches an end of the *detour* inside the detour
(`Graph.IsPathGraph.reaches_an_end`), an end which — having been reached after the deletion —
survived it too, so the cycle's edge is still there to carry it the rest of the way. -/
theorem isTwoConnected : (G.cycleGraph u e D).IsTwoConnected where
  hasThreeVertices :=
    ⟨u, h.isCycle.left_mem_cycleGraph, v, h.isCycle.right_mem_cycleGraph,
      w, h.mem_cycleGraph, h.ne, Ne.symm h.ne_left, Ne.symm h.ne_right⟩
  connected := h.isCycle.cycleGraph_connected
  deleteVerts_connected := by
    intro c _
    set Kc := G.cycleGraph u e D with hKc
    set Pc := G.pathGraphOf u D with hPc
    have hPK : Pc.deleteVerts {c} ≤ Kc.deleteVerts {c} :=
      deleteVerts_mono pathGraphOf_le_cycleGraph _
    have hPpath : Pc.IsPathGraph u D v := h.isPath.isPathGraph_pathGraphOf
    -- The hub is whichever end of the cycle's edge survived; the argument is symmetric in
    -- the two, so it is done once for a named pair and applied twice.
    have main : ∀ a b : α, Kc.IsLink e a b → a ≠ c →
        (∀ x ∈ V(Kc), x ≠ c →
          (Pc.deleteVerts {c}).Reaches x a ∨ (Pc.deleteVerts {c}).Reaches x b) →
        (Kc.deleteVerts {c}).Connected := by
      intro a b hab hac hends
      refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hab.left_mem hac) fun x hx ↦ ?_
      rw [vertexSet_deleteVerts] at hx
      obtain ⟨hxK, hxc⟩ := hx
      have hxc' : x ≠ c := by simpa using hxc
      rcases hends x hxK hxc' with hr | hr
      · exact (hr.mono hPK).symm
      · -- The far end was reached, so it survived; the cycle's edge joins it to the hub.
        have hbc : b ≠ c := (mem_deleteVerts_singleton.1 (hr.mono hPK).right_mem).2
        have hedge : (Kc.deleteVerts {c}).Reaches b a :=
          ⟨[e], IsWalk.single ((deleteVerts_isLink _ _).2 ⟨hab.symm, by simpa using hbc,
            by simpa using hac⟩)⟩
        exact ((hr.mono hPK).trans hedge).symm
    have hV : ∀ x ∈ V(Kc), x ∈ V(Pc) := fun x hx ↦ by
      rw [hKc, h.isCycle.cycleGraph_vertexSet] at hx; exact hx
    by_cases hcu : u = c
    · -- The source is gone, so the target is the hub.
      refine main v u h.isCycle.cycleGraph_isLink.symm (fun hh ↦ h.ne (hh.trans hcu.symm).symm)
        fun x hx hxc ↦ (hPpath.reaches_an_end (hV x hx) hxc).symm
    · exact main u v h.isCycle.cycleGraph_isLink hcu
        fun x hx hxc ↦ hPpath.reaches_an_end (hV x hx) hxc

end IsLongCycle


/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-- **An edge of an ear that the subgraph already has is the whole ear.** Both ends of such an
edge lie in the subgraph, so the ear's freshness clause makes them the ear's own two ends; the
edge is then the ear's first edge and its far end is the ear's target, so nothing follows it.
-/
theorem IsPath.eq_singleton_of_edge_mem (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B))
    (hg : g ∈ D) (hgB : g ∈ E(B)) : D = [g] ∧ G.IsLink g u v := by
  -- Both ends of the edge lie in the subgraph, so both are ends of the path.
  have hends : ∀ y, G.Inc g y → y = u ∨ y = v := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact hint y (mem_walkVertices_of_mem_covered ⟨g, hg, hy⟩) hcon.1 hcon.2
      (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hy)
  -- The edge is not a loop, so its two ends are exactly the two ends of the path.
  obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (hpath.edge_mem hg)
  have hpqne : p ≠ q := by rintro rfl; exact hpath.not_isLoopAt hg p hpq
  have hincu : G.Inc g u := by
    rcases hends p hpq.inc_left with rfl | rfl
    · exact hpq.inc_left
    · rcases hends q hpq.inc_right with rfl | rfl
      · exact hpq.inc_right
      · exact absurd rfl hpqne
  -- So it is the path's first edge, and its far end is the path's target.
  obtain ⟨w, T, rfl, hl, hT⟩ := hpath.eq_cons_of_inc_left hg hincu
  have hwv : w = v := by
    rcases hends w hl.inc_right with rfl | hh
    · exact absurd hl (hpath.not_isLoopAt List.mem_cons_self _)
    · exact hh
  subst hwv
  exact ⟨by rw [hT.eq_nil_of_eq], hl⟩

/-- **Either every edge of the ear is new, or the ear changes nothing.** The disjunction the
step of `Graph.IsTwoConnected.ear_decomposition` has to open before it can do any geometry. -/
theorem ear_edges_notMem_or_union_eq (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hu : u ∈ V(B)) (hv : v ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B)) :
    (∀ g ∈ D, g ∉ E(B)) ∨ B.union (G.pathGraphOf u D) = B := by
  by_cases hall : ∀ g ∈ D, g ∉ E(B)
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨g, hg, hgB⟩ := hall
  obtain ⟨rfl, hl⟩ := hpath.eq_singleton_of_edge_mem hBG huv hint hg hgB
  -- The ear is a single edge the subgraph already carries, joining two of its own vertices.
  refine le_antisymm (union_le le_rfl ?_) (left_le_union _ _)
  refine ⟨fun y hy ↦ ?_, fun f x y hf ↦ ?_⟩
  · rcases mem_walkVertices_iff.1 (pathGraphOf_vertexSet ▸ hy) with rfl | ⟨f, hf, hinc⟩
    · exact hu
    · obtain rfl : f = g := by simpa using hf
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      exacts [hu, hv]
  · obtain ⟨hfg, hxy, -, -⟩ := pathGraphOf_isLink.1 hf
    obtain rfl : f = g := by simpa using hfg
    exact (hBG.isLink_iff hgB).2 hxy

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

end Graph
end

section
-- module Solutions.Q146_CD.TwoArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

open Set unitInterval

namespace Schoenflies

namespace IsLoop

variable {f : ℝ → Plane} {s t : ℝ}

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

/-! ### The three pieces are arcs -/

/-- The middle piece is an arc between the two cut points. -/
theorem middle_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1)
    (hst : s < t) : IsArcBetween (f '' Icc s t) (f s) (f t) := by
  rw [← uIcc_of_le hst.le]
  refine isArcBetween_subarc hf.continuousOn ?_ hs ht (ne_of_lt hst)
  rw [uIcc_of_le hst.le]
  exact hf.injective_on_middle hs ht ht1

/-- The front piece is an arc from the start to the first cut point. -/
theorem front_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) (hs0 : 0 < s) :
    IsArcBetween (f '' Icc 0 s) (f 0) (f s) := by
  rw [← uIcc_of_le hs0.le]
  refine isArcBetween_subarc hf.continuousOn ?_ zero_mem_I hs (ne_of_lt hs0)
  rw [uIcc_of_le hs0.le]
  exact hf.injective_on_front hs hs1

/-- The back piece is an arc from the second cut point to the finish. -/
theorem back_IsArcBetween (hf : IsLoop f) (ht : t ∈ I) (ht1 : t ≠ 1) (ht0 : 0 < t) :
    IsArcBetween (f '' Icc t 1) (f t) (f 1) := by
  rw [← uIcc_of_le ht.2]
  refine isArcBetween_subarc hf.continuousOn ?_ ht one_mem_I ht1
  rw [uIcc_of_le ht.2]
  exact hf.injective_on_back ht ht0

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-- **The outside piece is an arc between the two cut points.** -/
theorem outside_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    IsArcBetween (f '' Icc 0 s ∪ f '' Icc t 1) (f t) (f s) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hback : IsArcBetween (f '' Icc t 1) (f t) (f 1) := hf.back_IsArcBetween ht ht1 ht0
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s` is the start: the front interval is the single parameter `0`, whose point the back
    -- piece already carries at its far end, so the outside is the back piece alone.
    have hfront : f '' Icc 0 s = {f 1} := by
      rw [← hs0, Icc_self, image_singleton, hf.finish_eq_start]
    have hone : f 1 ∈ f '' Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    rw [hfront, singleton_union, insert_eq_self.mpr hone, ← hs0, ← hf.finish_eq_start]
    exact hback
  · -- Otherwise the two end intervals are genuine arcs, glued where the loop closes up.
    have hfront : IsArcBetween (f '' Icc 0 s) (f 1) (f s) := by
      rw [hf.finish_eq_start]
      exact hf.front_IsArcBetween hs hs1 hs0
    have := hback.concatenate hfront (fun z hzb hzf => hf.back_meet_front hs ht hs1 hst hzb hzf)
    rwa [union_comm] at this

/-! ### Covering, and where the pieces meet -/

/-! ### The two arcs, at chosen parameters -/

/-- **Two parameters short of the finish cut the loop's image into two arcs between the points
they carry, which cover it and meet in exactly those two points.**

The pieces are named by the parameters, not chosen: the first is the middle interval's image,
the second the outside's. -/
theorem two_arcs_at_parameters (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    ∃ A B, IsArcBetween A (f s) (f t) ∧ IsArcBetween B (f t) (f s) ∧
      A ∪ B = f '' I ∧ A ∩ B = {f s, f t} :=
  ⟨f '' Icc s t, f '' Icc 0 s ∪ f '' Icc t 1,
    hf.middle_IsArcBetween hs ht ht1 hst,
    hf.outside_IsArcBetween hs ht hs1 ht1 hst,
    pieces_cover hs ht,
    hf.pieces_meet_at_ends hs ht hs1 ht1 hst⟩

end IsLoop

/-! ### The theorem -/

/-- **Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points.**

The parameters carrying the two points come in one order or the other, and the conclusion is
symmetric in the two pieces, so the second case is the first with the roles exchanged: the
union and the intersection commute, and the unordered pair does too.

This is the exact converse of `IsJordanCurve.of_two_arcs`: that theorem's hypotheses are two
arcs between the same two points meeting only there, which is what the two pieces produced
here are — see `IsJordanCurve.two_arcs_of_two_arcs`. -/
theorem IsJordanCurve.two_arcs {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∪ B = C ∧ A ∩ B = {p, q} := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨s, hs, hs1, rfl⟩ := hf.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hf.parameter_before_finish hq
  -- Distinct points, so distinct parameters, so one of the two orders holds.
  rcases lt_or_gt_of_ne (fun h : s = t => hpq (by rw [h])) with hst | hts
  · obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters hs ht hs1 ht1 hst
    exact ⟨A, B, hA, hB.reverse, hcov, hmeet⟩
  · -- The middle piece now runs from `f t` to `f s`, so it is the *second* piece here.
    obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters ht hs ht1 hs1 hts
    refine ⟨B, A, hB, hA.reverse, ?_, ?_⟩
    · rw [union_comm]; exact hcov
    · rw [inter_comm, hmeet, pair_comm]

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCyclesProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-- **An arc between two points contained in an arc between the same two points is all of
it.** Removing an interior point of the ambient arc splits it into two relatively open halves;
a connected subset containing both ends would have to meet both and therefore their empty
intersection. -/
theorem IsArcBetween.eq_of_subset {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hBA : B ⊆ A) : B = A := by
  obtain ⟨f, hc, hi, hAim, hf0, hf1⟩ := hA
  refine Set.Subset.antisymm hBA fun x hx => ?_
  by_contra hxB
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ I, f t = x := by rw [← hAim] at hx; exact hx
  -- The parameter is strictly inside, since both ends belong to `B`.
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | h
    · exact absurd (hf0 ▸ hB.left_mem) hxB
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact absurd (hf1 ▸ hB.right_mem) hxB
    · exact h
  obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hc hi (U := Iio t) isOpen_Iio
  obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hc hi (U := Ioi t) isOpen_Ioi
  rw [hAim] at hV₁ hV₂
  -- The two halves are disjoint, by injectivity of the parametrisation.
  have hdisj : (A ∩ (V₁ ∩ V₂)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z ⟨hzA, hz₁, hz₂⟩ => ?_
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzA⟩
    obtain ⟨r, hr, hrs⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzA⟩
    have hrs' : r = s := hi hr.2 hs.2 hrs
    have h1 : t < r := hr.1
    have h2 : s < t := hs.1
    rw [hrs'] at h1
    linarith
  -- `B` misses the removed point, so it lies in the union of the two halves.
  have hsub : B ⊆ V₁ ∪ V₂ := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by
      have := hBA hz; rw [← hAim] at this; exact this
    have hst : s ≠ t := by rintro rfl; exact hxB hz
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inl (by
        have : f s ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
    · exact Or.inr (by
        have : f s ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
  have hp₁ : (B ∩ V₁).Nonempty := by
    refine ⟨p, hB.left_mem, ?_⟩
    have : f 0 ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨0, ⟨ht0, zero_mem_I⟩, rfl⟩
    exact hf0 ▸ this.1
  have hq₂ : (B ∩ V₂).Nonempty := by
    refine ⟨q, hB.right_mem, ?_⟩
    have : f 1 ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨1, ⟨ht1, one_mem_I⟩, rfl⟩
    exact hf1 ▸ this.1
  obtain ⟨z, hzB, hz⟩ :=
    hB.isArc.isConnected.isPreconnected V₁ V₂ hV₁open hV₂open hsub hp₁ hq₂
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨hBA hzB, hz⟩

/-! ## Concatenating polylines -/

/-- **Two polylines meeting end to head concatenate.** The joining segment collapses to the
shared vertex. -/
theorem poly_append_of_eq {as bs : List Plane} (h₁ : as ≠ []) (h₂ : bs ≠ [])
    (h : as.getLast h₁ = bs.head h₂) : poly (as ++ bs) = poly as ∪ poly bs := by
  rw [poly_append_join h₁ h₂, h, segment_same, Set.union_assoc, Set.singleton_union,
    Set.insert_eq_self.2 (head_mem_poly h₂)]

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-! ## A polygonal arc is a polyline running from one end to the other -/

/-- **A polygonal arc is `poly` of a vertex list running from one of its ends to the other.**
`Schoenflies.exists_simple_poly_of_isPolygonal` produces a simple polygonal arc *inside* the
set between the two points; being an arc between the same two ends it is the whole of it, by
`Schoenflies.IsArcBetween.eq_of_subset`. -/
theorem IsArcBetween.exists_poly_eq {A : Set Plane} {p q : Plane} (harc : IsArcBetween A p q)
    (hpoly : IsPolygonal A) (hpq : p ≠ q) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = p ∧ vs.getLast h = q ∧ poly vs = A := by
  obtain ⟨vs, hvs, hhead, hlast, hsub, hsubarc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly harc.isArc.isConnected.isPreconnected hpq
      harc.left_mem harc.right_mem
  exact ⟨vs, hvs, hhead, hlast, harc.eq_of_subset hsubarc hsub⟩

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a list of edges draws depends only on which edges are on it -/

/-! ## The induction step: one ear

"Suppose it holds for the current graph and add the next geometric ear. Its interior is
connected and disjoint from the current graph, so it lies in one current face `F` … the ear is
therefore a crosscut of that side, and Theorem `thm:polygonal-crosscut` replaces `F` by exactly
two regions, both bounded by cycles; all other faces are unchanged."

Everything here is proved, except that the appeal to Theorem 2.8 is to the hypothesis
`Schoenflies.CrosscutSplitsRegion` instead. -/

/-! ## `lem:face-cycles`

"The cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`. We prove
by induction that every face is exactly one of the two regions bounded by its boundary cycle." -/

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane
graph has a cycle as its boundary and is one of the two complementary regions of that cycle.

**The statement carries the hypothesis `Schoenflies.CrosscutSplitsRegion`**, which is *not*
proved anywhere: it is the exhaustion clause of `thm:polygonal-crosscut` at a crosscut whose
endpoints need not be corners of the curve, and `main`'s Theorem 2.8 cannot supply it — see the
docstring of `Schoenflies.CrosscutSplitsRegion`. Everything else in the blueprint's proof is
discharged here: the base cycle and its 2-connectivity (`Schoenflies/FaceCycles.lean`), that
its realisation separates the plane (`Graph.IsDrawing.cycle_isSeparating`), that the ear lies in
one face and is a crosscut of it, that all other faces are unchanged, and that the two new
faces are bounded by the two cycles the ear splices onto the two arcs of the old one. -/
theorem face_cycles [G.Finite] (hobl : CrosscutSplitsRegion) (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => h.not_isLoopAt g x
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  refine hG.ear_decomposition (motive := fun B => HasFaceCycles B drawing) hnl
    hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (h.hasFaceCycles_cycleGraph hpoly hcyc.isCycle) ?_
  intro B a b D' _ _ hBG hmot hpathD hab haB hbB hintB
  -- Either the ear is genuinely new, or it is an edge the subgraph already had and adding it
  -- changes nothing.
  rcases ear_edges_notMem_or_union_eq hBG hpathD hab haB hbB hintB with hnew | heq
  · exact h.hasFaceCycles_union hobl hpoly hBG hmot hpathD hab haB hbB hintB hnew
  · rw [heq]; exact hmot

end Graph
end

section
-- module Solutions.Q146_CD.FaceCyclesLand
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `lem:face-cycles`, with nothing assumed

`Schoenflies/FaceCyclesProof.lean` proves `lem:face-cycles` modulo one hypothesis,
`Schoenflies.CrosscutSplitsRegion`: the exhaustion clause of `thm:polygonal-crosscut` for a
crosscut whose two endpoints are *arbitrary points* of the curve. This module proves that
hypothesis and restates the lemma without it (`Graph.face_cycles'`,
`Graph.IsDrawing.hasFaceCycles_union'`).

## Why the crosscut theorem had to be redone, and how far

`main`'s Theorem 2.8 (`Schoenflies.IsPolygonalCrosscut`) cuts a `ClosedPolygon` at two of *its
vertices*, and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says a point at which the curve runs
straight is a vertex of no `ClosedPolygon` presentation of it. In the ear induction the two cut
points are graph vertices, at which the two cycle edges may leave along opposite rays. So the
presentation has to be `Schoenflies.PrePolygon`, which has no `corner` field, and the two `main`
hypotheses `edges₁`/`edges₂` — multiset equalities `SameEdges Jᵢ.pieces (Aᵢ ++ K)` — have to go
as well, for the reason `Schoenflies/FaceCyclesProof.lean` records: the merged curve `Aᵢ ∪ P` may
run straight through a cut point, and then no presentation of it has an edge ending there.

Both go away at once by never realizing `J₁` and `J₂` at all. The two curves of the split are
given by *literal* edge lists `Aᵢ ++ K`, so Lemma 2.7 (`Schoenflies.parity_split`) applies with
nothing to check, and only the *easy* half of Theorem 2.3 is asked of them: "points in the same
region have the same crossing count", which is Lemma 2.2
(`Schoenflies.parity_eq_of_mem_connectedComponentIn`) and needs no realization. The hard half —
the two values `0` and `1` — is needed for `J` alone, where
`Schoenflies.PrePolygon.parity_eq_one_iff` of `Schoenflies/PrePolygonSep.lean` supplies it. That
is the whole of the reduction; Lemma 2.6 (`Schoenflies.crosscut_cells`) is already stated at the
set level and is quoted unchanged.

What the presentation still has to do is put the two cut points *on* its vertex list, and that is
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`, the inverse of
`Schoenflies.PrePolygon.deleteLast`. A point interior to an edge is brought to the last edge by
`Schoenflies.PrePolygon.rotate` and the edge is split in two; simplicity survives because the far
end of the split edge lies on neither half.

## For the integrator

The `Schoenflies.PrePolygon` arc apparatus this module runs on —
`Schoenflies.PrePolygon.arcPieces`, `…arc`, `…arcList`, `…insertLast` and
`Schoenflies.exists_prePolygon_split` — lives in `Schoenflies/PrePolygonArc.lean`, shared with
`Schoenflies/Graph/K33Land.lean`. It is `Schoenflies.ClosedPolygon.arcPieces` and its API of
`Schoenflies/ParitySplitting.lean` and `Schoenflies/Realization.lean` transcribed with the
structure changed — the proofs use `vertex_inj` and `edges_meet` and nothing else. The right
arrangement, as `Schoenflies/PrePolygonSep.lean` already says of `pieces`, is to prove them once
for `PrePolygon` and define the `ClosedPolygon` versions as `P.toPre.arcPieces`; that needs
`PrePolygon` moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

Three declarations here are general and belong elsewhere:
`Schoenflies.isSeparating_of_isJordanCurve` in `Schoenflies/Realization.lean`,
`Schoenflies.IsArcBetween.ne` in `Schoenflies/Curve.lean`, and
`Schoenflies.isChainFrom_segsOf` in `Schoenflies/ParitySplitting.lean` beside
`Schoenflies.isChainFrom_pathPieces`. `Schoenflies.two_arcs_unique_of_isClosed` subsumes
`Schoenflies.two_arcs_unique` and should replace it in `Schoenflies/Realization.lean`.

Once this module is moved above `Schoenflies/FaceCyclesProof.lean`, the hypothesis
`Schoenflies.CrosscutSplitsRegion` can be deleted from `Graph.face_cycles` and
`Graph.IsDrawing.hasFaceCycles_union`, and the two primed statements at the end here dropped.

## Blueprint

* `Schoenflies.two_arcs_unique_of_isClosed` — the two arcs a pair of points cuts a curve into are
  determined, with the competing splitting known only to be closed and nondegenerate.
* `Schoenflies.crosscutSplitsRegion` — the exhaustion clause of `thm:polygonal-crosscut` at
  arbitrary cut points: `Schoenflies.CrosscutSplitsRegion`, proved.
* `Graph.IsDrawing.hasFaceCycles_union'` — one ear of `lem:face-cycles`.
* `Graph.face_cycles'` — **`lem:face-cycles`**.
* `Graph.IsFaceCycle.eq_inside_of_isBounded'` — "in particular, every bounded face is the
  interior of its boundary cycle".
-/
open Bornology Metric Set

namespace Schoenflies

/-! ## Small pieces the assembly needs -/

/-- **A polygonal Jordan curve separates the plane** (Theorem 2.3, at the set level): realize it
and quote `Schoenflies.ClosedPolygon.isSeparating_carrier`. -/
theorem isSeparating_of_isJordanCurve {S : Set Plane} (hJ : IsJordanCurve S)
    (hP : IsPolygonal S) : IsSeparating S := by
  obtain ⟨m, Q, hQ⟩ := exists_closedPolygon hJ hP
  exact hQ ▸ Q.isSeparating_carrier

/-- **A polyline is a chain from its first point to its last**, with its degenerate steps
dropped. `Schoenflies.isChainFrom_pathPieces` says this for `Schoenflies.pathPieces`, which keeps
them; `Schoenflies.segsOf` is the list a consumer needing nondegenerate edges must use. -/
theorem isChainFrom_segsOf : ∀ (vs : List Plane) (h : vs ≠ []),
    IsChainFrom (segsOf vs) (vs.head h) (vs.getLast h)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isChainFrom_nil v
  | u :: v :: rest, hu => by
    classical
    have hne : (v :: rest) ≠ [] := List.cons_ne_nil _ _
    have ih : IsChainFrom (segsOf (v :: rest)) v ((v :: rest).getLast hne) :=
      isChainFrom_segsOf (v :: rest) hne
    have hgl : (u :: v :: rest).getLast hu = (v :: rest).getLast hne := List.getLast_cons hne
    rw [show (u :: v :: rest).head hu = u from rfl, hgl, segsOf_cons_cons]
    split_ifs with huv
    · rw [huv]; exact ih
    · intro f
      simp only [List.map_cons, List.sum_cons]
      rw [ih f]
      linear_combination add_self_zmod_two (f v)

/-- **The two-arc decomposition is determined, and the competitor need not be known to be two
arcs.** This is `Schoenflies.two_arcs_unique` with the hypotheses on the second splitting weakened
to what its proof uses: the two sets are closed and neither is just the two cut points. The edge
lists of a polygon supply exactly that, and nothing tells us they are arcs until this lemma has
said so. -/
theorem two_arcs_unique_of_isClosed {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hc1 : IsClosed D₁) (hc2 : IsClosed D₂)
    (hn1 : ¬ D₁ ⊆ ({p, q} : Set Plane)) (hn2 : ¬ D₂ ⊆ ({p, q} : Set Plane)) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ D₁
      · by_cases h2 : w ∈ D₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hD] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun w hw => ?_)
      by_contra hwD2
      exact hnone (hconn _ _ hc1.isOpen_compl hc2.isOpen_compl hsub hcase ⟨w, hw, hwD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun w hw => ?_)
      by_contra hwD1
      exact hcase ⟨w, hw, hwD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} →
      ¬ D' ⊆ ({p, q} : Set Plane) → A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'n h1 h2
    refine hD'n ?_
    rw [← hDDi]
    intro w hw
    have hwC : w ∈ C := by rw [← hDD]; exact Or.inr hw
    rw [← hA] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := by rw [← hX'Y']; exact Or.inl hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hn2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hn1 h1 h2) (by simp)

/-! ## Theorem 2.8 at arbitrary cut points

The blueprint's Theorem 2.8 is proved on `main` for a crosscut cutting a `ClosedPolygon` at two
of *its vertices*; `Schoenflies.ClosedPolygon.isCornerAt_vertex` makes that a real restriction,
since a point where the curve runs straight is a vertex of no `ClosedPolygon` presentation. The
exhaustion clause is what a consumer splitting a face at two graph vertices needs, and here it is
proved with no condition on the two points beyond lying on the curve.

The route is the blueprint's, with `PrePolygon` in place of `ClosedPolygon` and with the two
`Schoenflies.SameEdges` hypotheses of `Schoenflies.IsPolygonalCrosscut` replaced by *literal*
edge lists: the two curves of the split are presented as `Aᵢ ++ K`, so Lemma 2.7
(`Schoenflies.parity_split`) applies with nothing to check. Only one direction of Theorem 2.3 is
needed for those two lists — "the same region forces the same count", which is Lemma 2.2 and asks
for no realization at all. The other direction is needed only for the curve `C` itself, and there
`Schoenflies.PrePolygon.parity_eq_one_iff` supplies it. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.** This is
`Schoenflies.CrosscutSplitsRegion`, the hypothesis `Schoenflies/FaceCyclesProof.lean` was left
with. -/
theorem crosscutSplitsRegion : CrosscutSplitsRegion := by
  intro J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2 hunion hinter hParc hPJ hΩ hPsub z hz
  have hpq : p ≠ q := hA1.ne
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ :=
    exists_prePolygon_split hJsep.isJordanCurve hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  have hpqD1 : ({p, q} : Set Plane) ⊆ C.arc a k := by
    rw [← hDinter]; exact Set.inter_subset_left
  have hpqD2 : ({p, q} : Set Plane) ⊆ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) := by
    rw [← hDinter]; exact Set.inter_subset_right
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating.
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A reference point in the region the crosscut does not enter.
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyJ : y ∉ J := hΩpair.right.subset_compl hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ S : Set Plane, S ⊆ J → Ω' ⊆ (S ∪ P)ᶜ := by
    intro S hSJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hSJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ C.arc a k ∪ P := hΩ'sub _ hD1J hy
  have hyJ2 : y ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := hΩ'sub _ hD2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (C.arc a k ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD1J)
  have hΩW2 : Ω' ⊆
      connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD2J)
  have heqΩ' : connectedComponentIn Jᶜ y = Ω' := hΩpair.right.connectedComponentIn_eq hJsep hy
  -- 6. Lemma 2.6: the two cells are components of `Ω ∖ P`.
  obtain ⟨⟨-, hV1comp⟩, ⟨-, hV2comp⟩, -, -, -⟩ :=
    crosscut_cells hJsep hJ1 hJ2 hD1J hD2J (by rw [hPJ]; exact hpqD1) (by rw [hPJ]; exact hpqD2)
      (arcs_ne (le_of_eq hDinter) hD1n) hΩpair (hJ1.isRegionPair_farRegion hyJ1) hΩW1
      (hJ2.isRegionPair_farRegion hyJ2) hΩW2
  -- 7. Exhaustion, by Lemma 2.7 and the two values of Theorem 2.3.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  have hexh : ∀ w ∈ Ω \ P, w ∈ farRegion (C.arc a k ∪ P) y ∨
      w ∈ farRegion (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) y := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hwJ : w ∉ J := hΩ.subset_compl hw.1
    have hw1 : w ∉ C.arc a k ∪ P := by
      rintro (h | h)
      · exact hwJ (hD1J h)
      · exact hw.2 h
    have hw2 : w ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      · exact hwJ (hD2J h)
      · exact hw.2 h
    have hmem1 : w ∈ connectedComponentIn (C.arc a k ∪ P)ᶜ y := by
      by_contra hc1
      exact hn1 ⟨hw1, hc1⟩
    have hmem2 : w ∈
        connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y := by
      by_contra hc2
      exact hn2 ⟨hw2, hc2⟩
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) w
        = parity u (C.arcPieces a k ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev1 hclosed1 (by rw [hcov1]; exact hyJ1)
        (by rw [hcov1]; exact hmem1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev2 hclosed2 (by rw [hcov2]; exact hyJ2)
        (by rw [hcov2]; exact hmem2)
    have hkey : parity u C.pieces w = parity u C.pieces y := by
      rw [← hsplit w, ← hsplit y, hp1, hp2]
    rcases hΩpair with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · rw [C.parity_eq_one_of_mem_inside hu hlevC
          (show w ∈ inside C.carrier by rw [hcar]; exact hin ▸ hw.1),
        C.parity_eq_zero_of_mem_outside hu hlevC
          (show y ∈ outside C.carrier by rw [hcar]; exact hout ▸ hy)] at hkey
      exact absurd hkey (by decide)
    · rw [C.parity_eq_zero_of_mem_outside hu hlevC
          (show w ∈ outside C.carrier by rw [hcar]; exact hout ▸ hw.1),
        C.parity_eq_one_of_mem_inside hu hlevC
          (show y ∈ inside C.carrier by rw [hcar]; exact hin ▸ hy)] at hkey
      exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hexh z hz with hv | hv
    · exact Or.inl (by rw [e1, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inr (by rw [e2, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)
  · rcases hexh z hz with hv | hv
    · exact Or.inr (by rw [e2, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inl (by rw [e1, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

/-! ## `lem:face-cycles`, with nothing assumed

`Graph.IsDrawing.hasFaceCycles_union` and `Graph.face_cycles` of
`Schoenflies/FaceCyclesProof.lean` carry the hypothesis `Schoenflies.CrosscutSplitsRegion`;
`Schoenflies.crosscutSplitsRegion` above proves it, so here are the two statements with the
hypothesis discharged. **These are the forms a consumer should use.** Once this module's
`PrePolygon` development is hoisted above `Schoenflies/FaceCyclesProof.lean` the hypothesis can
be deleted from the originals and the primes here dropped. -/

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane graph
has a cycle as its boundary and is one of the two complementary regions of that cycle.

This is `Graph.face_cycles` with its hypothesis `Schoenflies.CrosscutSplitsRegion` discharged by
`Schoenflies.crosscutSplitsRegion`; nothing is assumed. -/
theorem face_cycles' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing :=
  face_cycles crosscutSplitsRegion h hpoly hG

end Graph
end

section
-- module Solutions.Q146_CD.OuterChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The outer face of a chain of plane graphs

`lem:outer-chain`. Let `Γ 0, …, Γ n` (`n ≥ 2`, so at least three graphs) be finite 2-connected
polygonal plane graphs, consecutive ones sharing at least two vertices and nonconsecutive ones
disjoint. If a point `x` is in the outer face of every consecutive pair `Γ p ∪ Γ (p+1)`, then it
is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

## How the chain is formalised

The blueprint says "after subdividing common points into vertices". Here that is true by
construction rather than by a theorem: the family shares **one** ambient edge type `β` and
**one** drawing `drawing : β → ℝ → Plane`, and every member is a subgraph of a single plane
graph `G` — see `Graph.IsPlaneChain`. Two members therefore agree about the ends of a shared
edge, meet only where `G` lets them meet, and `Γ p ∪ Γ q` is `Graph.union` with nothing to
check. The ambient `G` is allowed to be larger than the chain's own union; a consumer that has
built all its pieces inside one polygonal overlay hands that overlay over as `G`.

`Graph.chainUnion Γ i m` is the block `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`, indexed by its **length**
`m` rather than by its right endpoint, so that the recursion is on `m` and the blueprint's
"choose `i ≤ j` with `j - i` minimum" is a plain strong induction on `m`. A consecutive pair is
`chainUnion Γ p 1`.

"`x` is in the outer face of `H`" is spelled, as everywhere in this development, as *`x` is off
the drawing and the face through it is unbounded* — `x ∈ exterior H drawing` together with
`¬ Bornology.IsBounded (face H drawing x)`. `Graph.unbounded_face_unique` is what makes that
"the" outer face, and `Graph.beyondSquare_subset_face` is how a consumer proves it.

## What is proved and what is assumed

The blueprint's proof is a minimal-counterexample argument on two measures: first the length of
the index interval, then the number of edges of the enclosing cycle lying outside `Γ (j-1)`.
Both minimisations are carried out here, as strong inductions, together with

* the reduction of "`x` lies in a bounded face" to "some cycle encloses `x`"
  (`Graph.encloses_of_isBounded_face`, from `Graph.face_cycles'`) and back
  (`Graph.isBounded_face_of_encloses`);
* 2-connectivity of every block, by iterating `Graph.IsTwoConnected.union`
  (`lem:union-two-connected`);
* the base case `j - i ≤ 1`, which is the blueprint's paragraph "If `j-i ≤ 1`, choose a
  consecutive pair `H` containing that union …";
* the two minimality consequences "`C` contains an edge of `Γ j` outside `Γ (j-1)`" and "`C`
  contains an edge of the earlier chain outside `Γ (j-1)`", each proved by pushing the cycle
  down into a shorter block with `Graph.IsCycleThrough.anti`;
* the splicing of a crosscut onto each of the two arcs (`Graph.exists_spliced_cycles`, from
  `Graph.exists_spliced_cycle`) and the edge count that makes the splice a strict improvement
  (`Graph.edgesOutside_splice_lt`, `Graph.exists_cycle_edgesOutside_lt`).

`Graph.Descent` is the middle paragraph of the blueprint's proof — from a cycle `C` of
`Γ i ∪ ⋯ ∪ Γ j` enclosing `x` and having an edge of `Γ j` and an edge of `Γ i ∪ ⋯ ∪ Γ (j-2)`
outside `Γ (j-1)`, produce a cycle of the same block enclosing `x` with strictly fewer edges
outside `Γ (j-1)`. It is a statement about **one** step, not about the chain's outer face.

It was assumed when this module was written. Both halves are now proved:

* `Schoenflies/CrosscutExists.lean` — combinatorial: build the crosscut, as
  `Graph.IsPlaneChain.crosscutExists`. Nothing geometric enters beyond
  `Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
  `Γ (j-1)`".
* `Schoenflies/CrosscutEncloses.lean` — geometric: "the path `R` lies on one side of `C` and is
  a crosscut there; by `thm:polygonal-crosscut`, at least one of `R ∪ C₁`, `R ∪ C₂` encloses
  `x`", as `Graph.crosscutEnclosesOff`. That module also carries the counterexample showing why
  the clause `x ∈ exterior H drawing` cannot be dropped — see the comment below, where the false
  version of it used to stand.

`Schoenflies/OuterChainClosed.lean` combines the two, and states `lem:outer-chain` with nothing
assumed.

## Blueprint

* `Graph.chainUnion` — `Γ i ∪ ⋯ ∪ Γ (i+m)`, with `chainUnion_le`, `le_chainUnion`,
  `chainUnion_finite`, `chainUnion_isTwoConnected` (the last is repeated
  `lem:union-two-connected`).
* `Graph.Encloses` — "that face is the interior of its boundary cycle, which therefore encloses
  `x`", as a property of a graph.
* `Graph.encloses_of_isBounded_face`, `Graph.isBounded_face_of_encloses` — the two directions
  of that reduction; the second is the blueprint's "the face of `H` containing `x` … lies in the
  bounded set `Int(C)` and therefore is not the outer face of `H`".
* `Graph.IsPlaneChain` — the hypotheses of `lem:outer-chain`; `Graph.OuterOnPairs` — its
  hypothesis on consecutive pairs.
* `Graph.IsCycleCrosscut` — the crosscut `R` of the cycle `C`, with the two arcs it cuts.
* `Graph.exists_spliced_cycles` — the two cycles `R ∪ C₁`, `R ∪ C₂`.
* `Graph.edgesOutside`, `Graph.edgesOutside_splice_lt`,
  `Graph.exists_cycle_edgesOutside_lt` — "it has fewer edges outside `Γ (j-1)` than `C`, since
  one nonempty outside portion of `C` has been replaced by `R ⊆ Γ (j-1)`".
* `Graph.Descent` — the crosscut paragraph of the proof; discharged in
  `Schoenflies/CrosscutEncloses.lean` from `Graph.CrosscutExists` alone.
* `Graph.IsPlaneChain.not_encloses` — the double minimisation.
* `Graph.IsPlaneChain.outer_chain` — **`lem:outer-chain`**, from `Graph.Descent`;
  `Graph.IsPlaneChain.outer_chain'` in `Schoenflies/OuterChainClosed.lean` is the same
  statement with nothing assumed.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ## Blocks of a chain -/

section General

variable {α β : Type*} {Γ : ℕ → Graph α β} {G K : Graph α β} {i m p : ℕ}

/-- A block sits inside any graph containing all of its members. -/
theorem chainUnion_le (h : ∀ p, i ≤ p → p ≤ i + m → Γ p ≤ G) : chainUnion Γ i m ≤ G := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    exact union_le (ih fun p hp hp' => h p hp (by omega)) (h (i + m + 1) (by omega) le_rfl)

/-- Each member of a block is a subgraph of it. The compatibility hypothesis is what makes the
*right*-hand summand of a `Graph.union` a subgraph, and it is free once every member lies in one
ambient graph. -/
theorem le_chainUnion (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G) (hp : i ≤ p) (hp' : p ≤ i + m) :
    Γ p ≤ chainUnion Γ i m := by
  induction m with
  | zero =>
    obtain rfl : p = i := by omega
    exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge p (i + m + 1) with h | h
    · exact (ih (fun q hq hq' => hle q hq (by omega)) (by omega)).trans (left_le_union _ _)
    · obtain rfl : p = i + m + 1 := by omega
      have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
        Compatible.of_le_le (chainUnion_le fun q hq hq' => hle q hq (by omega))
          (hle _ (by omega) le_rfl)
      exact hcompat.right_le_union

/-- **`lem:union-two-connected`, iterated.** A block of 2-connected graphs in which consecutive
members share two distinct vertices is 2-connected. -/
theorem chainUnion_isTwoConnected (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G)
    (htc : ∀ q, i ≤ q → q ≤ i + m → (Γ q).IsTwoConnected)
    (hmeet : ∀ q, i ≤ q → q < i + m → ∃ a b : α, a ≠ b ∧ a ∈ V(Γ q) ∧ a ∈ V(Γ (q + 1)) ∧
      b ∈ V(Γ q) ∧ b ∈ V(Γ (q + 1))) :
    (chainUnion Γ i m).IsTwoConnected := by
  induction m with
  | zero => exact htc i le_rfl le_rfl
  | succ m ih =>
    have hle' : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G := fun q hq hq' => hle q hq (by omega)
    have hih := ih hle' (fun q hq hq' => htc q hq (by omega))
      (fun q hq hq' => hmeet q hq (by omega))
    obtain ⟨a, b, hab, haq, haq', hbq, hbq'⟩ := hmeet (i + m) (by omega) (by omega)
    have hsub : Γ (i + m) ≤ chainUnion Γ i m := le_chainUnion hle' (by omega) le_rfl
    have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
      Compatible.of_le_le (chainUnion_le hle') (hle _ (by omega) le_rfl)
    exact hih.union hcompat (htc _ (by omega) le_rfl) hab (hsub.vertexSet_mono haq) haq'
      (hsub.vertexSet_mono hbq) hbq'

/-! ### Reading a cycle inside a subgraph

`Graph.IsCycleThrough.anti` is the cycle counterpart of `Graph.IsPath.anti`; it is what turns
"no edge of `C` is outside this block" into "`C` is a cycle of this block". -/

/-! ### A crosscut of a cycle, with the two arcs it cuts

This is the combinatorial output of the blueprint's crosscut paragraph, bundled: the path `R` in
`F = Γ (j-1)`, its two endpoints `a, b` on the cycle, and the two arcs `D₁, D₂` the endpoints cut
the cycle into. Both arcs are required to carry an edge that `F` does not have — the blueprint's
"each arc contains an edge outside `Γ (j-1)`, because its endpoints belong to different maximal
subpaths of the intersection" — which is what makes the splice a strict improvement on **both**
sides, so that it does not matter which of the two spliced cycles turns out to enclose `x`. -/

/-- **The two cycles a crosscut splices**, `R ∪ C₁` and `R ∪ C₂`, as cycles of the ambient graph
with their edge lists named. Both are produced by `Graph.exists_spliced_cycle`, applied to the
cycle's own subgraph and to each arc in turn. -/
theorem exists_spliced_cycles {H F : Graph α β} {e : β} {u v a b : α} {D R D₁ D₂ : List β}
    (hcyc : H.IsCycleThrough e u v D) (hcc : IsCycleCrosscut H F e u v D a b R D₁ D₂) :
    ∃ (e₁ e₂ : β) (u₁ v₁ u₂ v₂ : α) (T₁ T₂ : List β),
      H.IsCycleThrough e₁ u₁ v₁ T₁ ∧ H.IsCycleThrough e₂ u₂ v₂ T₂ ∧
        (e₁ :: T₁).Perm (D₁ ++ R) ∧ (e₂ :: T₂).Perm (D₂ ++ R) := by
  have hBle : H.cycleGraph u e D ≤ H := hcyc.cycleGraph_le
  have haB : a ∈ V(H.cycleGraph u e D) := by
    rw [hcyc.cycleGraph_vertexSet]; exact hcc.mem_left
  -- Both arcs consist of edges of the cycle, hence of the cycle's own subgraph.
  have harc : ∀ {W : List β}, (∀ g ∈ W, g ∈ D₁ ++ D₂) →
      ∀ g ∈ W, g ∈ E(H.cycleGraph u e D) := by
    intro W hW g hg
    rw [hcyc.cycleGraph_edgeSet, Set.mem_setOf_eq, List.mem_append]
    rcases List.mem_cons.1 (hcc.split.mem_iff.1 (hW g hg)) with rfl | h
    · exact Or.inr (List.mem_singleton_self _)
    · exact Or.inl h
  have hnew : ∀ g ∈ R, g ∉ E(H.cycleGraph u e D) := by
    intro g hg hmem
    rw [hcyc.cycleGraph_edgeSet, Set.mem_setOf_eq] at hmem
    exact hcc.edges_new g hg hmem
  have hint : ∀ y ∈ H.walkVertices a R, y ≠ a → y ≠ b → y ∉ V(H.cycleGraph u e D) := by
    intro y hy hya hyb
    rw [hcyc.cycleGraph_vertexSet]
    exact hcc.interior y hy hya hyb
  have hHle : (H.cycleGraph u e D).union (H.pathGraphOf a R) ≤ H :=
    union_le hBle (pathGraphOf_le hcc.isPath.isWalk)
  -- Splice the crosscut onto the first arc …
  obtain ⟨f₁, x₁, y₁, T₁, hc₁, hp₁⟩ :=
    exists_spliced_cycle hBle
      (hcc.arc₁.anti hBle haB (harc fun g hg => List.mem_append_left _ hg))
      hcc.isPath hcc.ne hnew hint
  -- … and onto the second, run backwards so that it too starts at `a`.
  obtain ⟨f₂, x₂, y₂, T₂, hc₂, hp₂⟩ :=
    exists_spliced_cycle hBle
      (hcc.arc₂.reverse.anti hBle haB
        (harc fun g hg => List.mem_append_right _ (List.mem_reverse.1 hg)))
      hcc.isPath hcc.ne hnew hint
  exact ⟨f₁, f₂, x₁, y₁, x₂, y₂, T₁, T₂, hc₁.mono hHle, hc₂.mono hHle, hp₁,
    hp₂.trans ((List.reverse_perm D₂).append_right R)⟩

end General

/-! ## Enclosing a point -/

section Plane

variable {β : Type*} {H K : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

/-- **"The face of `H` containing `x` is connected and disjoint from `C`; since it contains
`x ∈ Int(C)` it lies in the bounded set `Int(C)`."** An enclosed point has a bounded face. -/
theorem isBounded_face_of_encloses (hx : x ∈ exterior H drawing)
    (henc : Encloses H drawing x) : Bornology.IsBounded (face H drawing x) := by
  obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
  have hsub : edgesCover drawing (e :: D) ⊆ pointSet H drawing :=
    edgesCover_subset_pointSet fun g hg => hcyc.mem_edgeSet_cons hg
  -- The face is a connected subset of the complement of the cycle through `x`, so it lies in
  -- the component of `x` there, which is bounded because `x` is inside.
  have h1 : face H drawing x ⊆ connectedComponentIn (edgesCover drawing (e :: D))ᶜ x :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hx) fun w hw hw' => (face_subset_exterior _ _ _ hw) (hsub hw')
  exact (mem_inside_iff.1 hin).2.subset h1

/-- **"By `lem:face-cycles`, that face is the interior of its boundary cycle."** A point in a
bounded face of a finite 2-connected polygonal plane graph is enclosed by a cycle of it. -/
theorem encloses_of_isBounded_face [H.Finite] (hd : IsDrawing H drawing)
    (hpoly : ∀ g ∈ E(H), IsPolygonal (edgeArc drawing g)) (h2 : H.IsTwoConnected)
    (hx : x ∈ exterior H drawing) (hb : Bornology.IsBounded (face H drawing x)) :
    Encloses H drawing x := by
  obtain ⟨e, u, v, D, hfc⟩ := face_cycles' hd hpoly h2 x hx
  exact ⟨e, u, v, D, hfc.isCycle, hfc.eq_inside_of_isBounded' hb ▸ mem_face hx⟩

/-- **The last mile of the descent step.** Suppose the cycle `C = e :: D` of `H` splits at two
of its vertices into arcs carrying `D₁` and `D₂`, each with an edge that the graph `F` does not
have; suppose `R` is a list of edges of `F`; and suppose `Z₁, Z₂` are cycles of `H` carrying
`D₁ ++ R` and `D₂ ++ R`. If `x` is inside one of `Z₁, Z₂`, then some cycle of `H` encloses `x`
with strictly fewer edges outside `F` than `C` has.

This is everything in the blueprint's crosscut paragraph after "exactly one of the two cycles
`R ∪ C₁`, `R ∪ C₂` encloses `x`", so a discharger of `Graph.Descent` has only to produce the
crosscut and decide which side. The splitting of the cycle is `Graph.IsCycleThrough.split_at`
and the two spliced cycles are `Graph.exists_spliced_cycle`; both hand back exactly the
permutation statements assumed here. -/
theorem exists_cycle_edgesOutside_lt {H F : Graph Plane β} {e : β} {u v : Plane} {D : List β}
    (hcyc : H.IsCycleThrough e u v D) {D₁ D₂ R : List β} (hperm : (e :: D).Perm (D₁ ++ D₂))
    (hR : ∀ g ∈ R, g ∈ E(F)) (h₁ : ∃ g ∈ D₁, g ∉ E(F)) (h₂ : ∃ g ∈ D₂, g ∉ E(F))
    {e₁ e₂ : β} {u₁ v₁ u₂ v₂ : Plane} {T₁ T₂ : List β}
    (hZ₁ : H.IsCycleThrough e₁ u₁ v₁ T₁) (hZ₂ : H.IsCycleThrough e₂ u₂ v₂ T₂)
    (hp₁ : (e₁ :: T₁).Perm (D₁ ++ R)) (hp₂ : (e₂ :: T₂).Perm (D₂ ++ R))
    (hone : x ∈ inside (edgesCover drawing (e₁ :: T₁)) ∨
      x ∈ inside (edgesCover drawing (e₂ :: T₂))) :
    ∃ (e' : β) (u' v' : Plane) (D' : List β), H.IsCycleThrough e' u' v' D' ∧
      x ∈ inside (edgesCover drawing (e' :: D')) ∧
      (edgesOutside F (e' :: D')).ncard < (edgesOutside F (e :: D)).ncard := by
  -- A cycle's edge list repeats no edge: the detour is a path and the named edge is not on it.
  have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hcyc.notMem, hcyc.isPath.nodup⟩
  rcases hone with hx | hx
  · exact ⟨e₁, u₁, v₁, T₁, hZ₁, hx, edgesOutside_splice_lt hnodup hperm hp₁ hR h₂⟩
  · exact ⟨e₂, u₂, v₂, T₂, hZ₂, hx,
      edgesOutside_splice_lt hnodup (hperm.trans List.perm_append_comm) hp₂ hR h₁⟩

end Plane

/-! ## The chain -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ} {x : Plane}

/-- **The hypotheses of `lem:outer-chain`.** `Γ 0, …, Γ n` are finite 2-connected polygonal
plane graphs, all drawn inside one ambient plane graph `G` — which is what makes "after
subdividing common points into vertices" true by construction — with consecutive members
sharing at least two vertices and nonconsecutive members disjoint. `n ≥ 2` is the blueprint's
`k ≥ 3`. -/
structure IsPlaneChain (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (G : Graph Plane β)
    (n : ℕ) : Prop where
  /-- At least three graphs. -/
  two_le : 2 ≤ n
  /-- Every member is drawn inside the ambient plane graph. -/
  le_ambient : ∀ p ≤ n, Γ p ≤ G
  /-- The ambient graph is a plane graph. -/
  isDrawing : IsDrawing G drawing
  /-- Its edges are polygonal. -/
  polygonal : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)
  /-- Every member is finite. -/
  finite : ∀ p ≤ n, (Γ p).Finite
  /-- Every member is 2-connected. -/
  twoConnected : ∀ p ≤ n, (Γ p).IsTwoConnected
  /-- Consecutive members have at least two vertices in common. -/
  meet : ∀ p, p + 1 ≤ n → ∃ a b : Plane, a ≠ b ∧ a ∈ V(Γ p) ∧ a ∈ V(Γ (p + 1)) ∧
      b ∈ V(Γ p) ∧ b ∈ V(Γ (p + 1))
  /-- Nonconsecutive members are disjoint — as point sets, which is what the blueprint means
  and what the crosscut step of the proof uses. -/
  disjoint : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      Disjoint (pointSet (Γ p) drawing) (pointSet (Γ q) drawing)

namespace IsPlaneChain

variable {i m p : ℕ}

theorem block_le (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) : chainUnion Γ i m ≤ G :=
  chainUnion_le fun p _ hp' => h.le_ambient p (by omega)

theorem le_block (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) (hp : i ≤ p)
    (hp' : p ≤ i + m) : Γ p ≤ chainUnion Γ i m :=
  le_chainUnion (G := G) (fun q _ hq' => h.le_ambient q (by omega)) hp hp'

theorem block_finite (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).Finite :=
  chainUnion_finite fun p _ hp' => h.finite p (by omega)

theorem block_isDrawing (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    IsDrawing (chainUnion Γ i m) drawing :=
  h.isDrawing.mono (h.block_le hm)

theorem block_polygonal (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    ∀ g ∈ E(chainUnion Γ i m), IsPolygonal (edgeArc drawing g) :=
  fun g hg => h.polygonal g ((h.block_le hm).edgeSet_mono hg)

theorem block_isTwoConnected (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).IsTwoConnected :=
  chainUnion_isTwoConnected (G := G) (fun q _ hq' => h.le_ambient q (by omega))
    (fun q _ hq' => h.twoConnected q (by omega)) fun q _ hq' => h.meet q (by omega)

/-- **"`Γ j` meets the earlier chain only through `Γ (j-1)`."** The block `Γ i ∪ ⋯ ∪ Γ (i+m)` and
the member `Γ (i+m+2)` are disjoint, every pair of indices involved being nonconsecutive. This
is the form the descent step consumes. -/
theorem disjoint_block_far (h : IsPlaneChain Γ drawing G n) (hm : i + m + 2 ≤ n) :
    Disjoint (pointSet (chainUnion Γ i m) drawing) (pointSet (Γ (i + m + 2)) drawing) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨q, -, hq', hzq⟩ := mem_pointSet_block hz
  exact Set.disjoint_left.1 (h.disjoint q (i + m + 2) (by omega) (by omega) (by omega)) hzq hz'

/-- Nonconsecutive members share no edge: an edge of both would be drawn inside both point
sets. -/
theorem disjoint_edgeSet (h : IsPlaneChain Γ drawing G n) {q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (hpq : p + 1 < q) : Disjoint E(Γ p) E(Γ q) := by
  rw [Set.disjoint_left]
  intro g hgp hgq
  have hmem : drawing g 0 ∈ edgeArc drawing g := ⟨0, unitInterval.zero_mem, rfl⟩
  exact Set.disjoint_left.1 (h.disjoint p q hp hq hpq)
    (edgeArc_subset_pointSet hgp hmem) (edgeArc_subset_pointSet hgq hmem)

end IsPlaneChain

/-! ### The assumed step

Everything in the blueprint's proof except this one paragraph is discharged below. -/

/-! ### `Descent`, split into a combinatorial and a geometric half

`Graph.Descent` is what the main theorem consumes, and `Graph.descent_of_crosscut` derives it
from the two halves below, doing the splicing and the edge count in between. A module wishing to
discharge `Descent` may therefore prove these two instead, which is the natural division of
labour: `CrosscutExists` is a statement about walks in graphs with no geometry in it beyond the
disjointness of nonconsecutive members, and `CrosscutEncloses` is a statement about **one**
plane graph, **one** cycle and **one** crosscut, with no chain in it at all. -/

namespace IsPlaneChain

variable {i m p : ℕ}
/-- **The base case, `j = i + 1`.** No cycle of a consecutive pair encloses a point of that
pair's outer face. -/
theorem not_encloses_pair (hout : OuterOnPairs Γ drawing n x) (hp : p + 1 ≤ n) :
    ¬ Encloses (chainUnion Γ p 1) drawing x := fun henc =>
  (hout p hp).2 (isBounded_face_of_encloses (hout p hp).1 henc)

/-- **The base case, `j = i`.** A single member of the chain is contained in a consecutive pair
— the one after it, or, at the far end, the one before it. -/
theorem not_encloses_single (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hp : p ≤ n) : ¬ Encloses (Γ p) drawing x := by
  intro henc
  have hn : 2 ≤ n := h.two_le
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := p) (m := 1) (by omega) le_rfl (by omega)))
  · -- `p = n ≥ 2`, so the pair `Γ (p-1) ∪ Γ p` exists.
    obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := q) (m := 1) (by omega) (by omega) (by omega)))

/-- **The double minimal-counterexample argument.** No block of the chain encloses `x`.

The outer induction is on the length `m` of the block — the blueprint's "choose indices `i ≤ j`
with `j - i` minimum". Inside it, for a block of length at least two, the induction on `c` is
the blueprint's "choose `C` so that the number of its edges outside `Γ (j-1)` is minimum". -/
theorem not_encloses (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    ∀ m i, i + m ≤ n → ¬ Encloses (chainUnion Γ i m) drawing x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => exact fun i him => h.not_encloses_single hout (by omega)
    | 1 => exact fun i him => not_encloses_pair hout (by omega)
    | (m + 2) =>
      intro i him henc
      -- The inner minimisation, as an induction on a bound for the number of edges of the
      -- cycle lying outside `Γ (i+m+1)`.
      have inner : ∀ c (e : β) (u v : Plane) (D : List β),
          (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
          x ∈ inside (edgesCover drawing (e :: D)) →
          (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard < c → False := by
        intro c
        induction c with
        | zero => exact fun _ _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)
        | succ c ihc =>
          intro e u v D hcyc hin hlt
          -- Every edge of the cycle is an edge of some member of the block.
          have hmem : ∀ g ∈ e :: D, ∃ q, i ≤ q ∧ q ≤ i + (m + 2) ∧ g ∈ E(Γ q) := fun g hg =>
            mem_edgeSet_chainUnion.1 (hcyc.mem_edgeSet_cons hg)
          -- **"`C` contains an edge of `Γ j` outside `Γ (j-1)`."** Otherwise the cycle lives
          -- in the block one shorter, which the outer induction has excluded.
          have hA : ∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ i (m + 1)) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 2) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩
              · obtain rfl : q = i + m + 2 := by omega
                exact mem_edgeSet_chainUnion.2
                  ⟨i + m + 1, by omega, by omega, hcon g hg hgq⟩
            exact ih (m + 1) (by omega) i (by omega)
              ⟨e, u, v, D, hcyc.anti (left_le_union _ _) hE, hin⟩
          -- **"… and an edge of the earlier chain outside `Γ (j-1)`."** Otherwise the cycle
          -- lives in the consecutive pair `Γ (j-1) ∪ Γ j`.
          have hB : ∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hpair : chainUnion Γ (i + m + 1) 1 ≤ chainUnion Γ i (m + 2) :=
              chainUnion_le fun q hq hq' =>
                h.le_block him (by omega) (by omega)
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ (i + m + 1) 1) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 1) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨i + m + 1, by omega, by omega,
                  hcon g hg (mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩)⟩
              · exact mem_edgeSet_chainUnion.2 ⟨q, by omega, by omega, hgq⟩
            exact ih 1 (by omega) (i + m + 1) (by omega)
              ⟨e, u, v, D, hcyc.anti hpair hE, hin⟩
          -- The assumed crosscut step now produces a cycle with a smaller count.
          obtain ⟨e', u', v', D', hcyc', hin', hlt'⟩ := hdesc i m him e u v D hcyc hin hA hB
          exact ihc e' u' v' D' hcyc' hin' (by omega)
      obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
      exact inner _ e u v D hcyc hin (Nat.lt_succ_self _)

/-- `x` is off the whole chain: it is off every consecutive pair, and every member belongs to
one. -/
theorem mem_exterior_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing := by
  intro hx
  have hn : 2 ≤ n := h.two_le
  obtain ⟨p, -, hp, hxp⟩ := mem_pointSet_block hx
  -- The member `Γ p` lies in a consecutive pair, whose point set `x` avoids.
  have key : ∀ q, q + 1 ≤ n → x ∉ pointSet (Γ q) drawing ∧ x ∉ pointSet (Γ (q + 1)) drawing := by
    intro q hq
    have := (hout q hq).1
    rw [exterior, chainUnion_one, Set.mem_compl_iff, pointSet_union] at this
    exact ⟨fun hc => this (Or.inl hc), fun hc => this (Or.inr hc)⟩
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact (key p (by omega)).1 hxp
  · obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact (key q (by omega)).2 hxp

/-- **`lem:outer-chain` (outer face of a chain).** If `x` is in the outer face of every
consecutive pair `Γ p ∪ Γ (p+1)`, then `x` is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

"In the outer face" is `x ∈ exterior … ∧ ¬ IsBounded (face … x)`; by
`Graph.unbounded_face_unique` there is only one unbounded face, so this really does say `x` is
in *the* outer face. -/
theorem outer_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) := by
  have hext := h.mem_exterior_chain hout
  refine ⟨hext, fun hb => ?_⟩
  haveI : (chainUnion Γ 0 n).Finite := h.block_finite (i := 0) (m := n) (by omega)
  exact h.not_encloses hout hdesc n 0 (by omega)
    (encloses_of_isBounded_face (h.block_isDrawing (by omega)) (h.block_polygonal (by omega))
      (h.block_isTwoConnected (by omega)) hext hb)

end IsPlaneChain

end Chain

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutEncloses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `thm:polygonal-crosscut` at the level of sets, and the geometric half of the outer-chain descent

The blueprint sentence this module discharges is one line of the proof of `lem:outer-chain`:

> The path `R` lies on one side of `C` and is a crosscut there. By `thm:polygonal-crosscut`,
> exactly one of the two cycles `R ∪ C₁`, `R ∪ C₂` encloses `x`.

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean` is that sentence weakened to *at least*
one, which is all the descent uses; the weakening is not undone here.

## One theorem, no case split

The blueprint — and the note in `Schoenflies/OuterChain.lean` — distinguishes the crosscut running
inside `C` (settled by `Schoenflies.crosscutSplitsRegion`) from the crosscut running outside it
(`Schoenflies.IsPolygonalCrosscut.inside_exactly_one`). **Neither case distinction is needed.**
Both are consequences of Lemma 2.7, the parity identity

    π_{A₁ ∪ P} + π_{A₂ ∪ P} = π_J        at *every* point of the plane,

which holds with no geometry whatever (`Schoenflies.parity_split`), together with the *one*
direction of Theorem 2.3 that needs no realization of the two spliced curves:

    a closed chain whose cover separates has crossing count `0` on the unbounded region

(`Schoenflies.parity_eq_zero_of_mem_outside_cover`). If `x` were outside both spliced curves the
identity would read `0 + 0 = π_J(x)`, whereas `π_J(x) = 1` because `x` is inside `J`. That is the
whole proof of `Schoenflies.crosscut_inside_at_least_one`, and it is uniform in which side the
crosscut runs on. The `ClosedPolygon`-level `Schoenflies.IsPolygonalCrosscut.inside_exactly_one`,
whose `SameEdges` hypotheses cannot be met at graph vertices (see the section docstring of
`Schoenflies/FaceCyclesLand.lean`), is therefore not used at all.

The price is that the conclusion is "at least one" rather than "exactly one": the converse
direction of Theorem 2.3 for the spliced curves — `π = 1` forces the bounded region — *does* need
them realized, and the descent does not want it.

## The set-level statement is the artefact

`Schoenflies.crosscut_inside_at_least_one` takes sets and arcs, not polygons and not graphs:

    `J` a polygonal Jordan curve, `A₁, A₂` arcs from `p` to `q` covering it, `P` a polygonal arc
    from `p` to `q` meeting `J` only at `p, q`; then a point inside `J` and off `P` is inside
    `A₁ ∪ P` or inside `A₂ ∪ P`.

That is `thm:polygonal-crosscut` in the shape every plane-graph consumer wants, and
`Graph.crosscutEnclosesOff` is a two-page corollary of it. A second general fact falls out on the
way: `Schoenflies.two_arcs_inter_of_union` — two arcs with the same ends that cover a Jordan curve
meet **exactly** at those ends. That removes the "the two arcs meet only at the cut points" clause
from every consumer's obligations, which matters here because `Graph.IsCycleCrosscut` does not
record it (see below).

## Two defects of the interface handed to this module — read before integrating

**1. `Graph.CrosscutEncloses` as stated on `main` is false**, and the deliverable is
`Graph.CrosscutEnclosesOff`, which is it plus one hypothesis: `x ∈ exterior H drawing`. Nothing in
`Graph.CrosscutEncloses` prevents `x` from lying **on the crosscut's own drawing**: `x` is only
assumed to be inside the cycle `C`, and a crosscut running inside `C` may pass through `x`. Then
`x ∈ (A₁ ∪ P) ∩ (A₂ ∪ P)`, so `x` is inside neither spliced curve and the conclusion fails.

**The repair costs the chain nothing.** `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block lies inside the chain
(`Graph.pointSet_mono`), so the clause can be produced where it is needed instead of being carried.
`Graph.IsPlaneChain.descent_of_crosscutOff` below therefore proves `Graph.Descent` **exactly as it
stands on `main`**, and `Graph.IsPlaneChain.outer_chain_of_crosscutExists` is `lem:outer-chain` with
`Graph.CrosscutEncloses` discharged outright. Nothing in `Schoenflies/OuterChain.lean` has to
change; `Graph.CrosscutEncloses` should simply be deleted, together with
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut`, which the
two theorems here replace.

**2. `Graph.IsCycleCrosscut` does not record that the two arcs meet only at the two cut points**,
although `Graph.IsCycleThrough.split_at` — the theorem that builds them — produces exactly that
clause. It is not needed here, because `Schoenflies.two_arcs_inter_of_union` recovers the geometric
consequence from the Jordan curve; but a consumer that wants the *combinatorial* statement will
have to add the field.

## Blueprint

* `Schoenflies.two_arcs_inter_of_union` — §1: two arcs with the same ends covering a Jordan curve
  meet exactly at those ends. General; belongs beside `Schoenflies.two_arcs_unique` in
  `Schoenflies/Realization.lean`.
* `Schoenflies.crosscut_inside_at_least_one` — **`thm:polygonal-crosscut`**, at the level of sets:
  a point inside the curve and off the crosscut is inside one of the two spliced curves.
* `Graph.IsDrawing.mem_edgesCover_of_mem_walkVertices` — the converse of
  `Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover`; general, belongs in
  `Schoenflies/Graph/CycleJordan.lean`.
* `Graph.CrosscutEnclosesOff`, `Graph.crosscutEnclosesOff` — the geometric half of the descent
  step of `lem:outer-chain`: `Graph.CrosscutEncloses` with the missing hypothesis restored,
  **proved**.
* `Graph.IsPlaneChain.descent_of_crosscutOff` — `Graph.Descent` from `Graph.CrosscutExists` alone;
  a drop-in replacement for `Graph.IsPlaneChain.descent_of_crosscut`.
* `Graph.IsPlaneChain.outer_chain_of_crosscutExists` — **`lem:outer-chain`**, assuming only the
  combinatorial half `Graph.CrosscutExists`.
-/

open Bornology Set

namespace Schoenflies

/-! ## Two arcs that cover a Jordan curve meet at their ends

`Schoenflies.two_arcs_unique_of_isClosed` identifies a *given* two-arc splitting with any other
splitting whose two pieces are known to meet exactly at the two points. What a graph consumer has
is weaker: two arcs of a cycle whose union is the whole curve, with nothing said about their
intersection. This lemma supplies the intersection, by comparing with the splitting that
`Schoenflies.IsJordanCurve.two_arcs` produces out of nothing. -/

/-- **Two arcs with the same ends that cover a Jordan curve meet exactly at those ends.**

The proof is the `key` step of `Schoenflies.two_arcs_unique_of_isClosed` run against the reference
splitting: an arc from `p` to `q` inside the curve has connected complement-of-endpoints, so it
lands in one piece of any splitting whose two pieces meet exactly at `p, q`; the two arcs cannot
land in the same piece, since the other piece would then be just `{p, q}`; and once they land in
different pieces they exhaust them. -/
theorem two_arcs_inter_of_union {C A₁ A₂ : Set Plane} {p q : Plane} (hC : IsJordanCurve C)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C) :
    A₁ ∩ A₂ = {p, q} := by
  have hpq : p ≠ q := hA1.ne
  have hpC : p ∈ C := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqC : q ∈ C := by rw [← hunion]; exact Or.inl hA1.right_mem
  obtain ⟨B₁, B₂, hB1, hB2, hBunion, hBinter⟩ := hC.two_arcs hpC hqC hpq
  have hB1C : B₁ ⊆ C := by rw [← hBunion]; exact Set.subset_union_left
  have hB2C : B₂ ⊆ C := by rw [← hBunion]; exact Set.subset_union_right
  have hA1C : A₁ ⊆ C := by rw [← hunion]; exact Set.subset_union_left
  have hA2C : A₂ ⊆ C := by rw [← hunion]; exact Set.subset_union_right
  -- An arc between the two points lies on one side of the reference splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ B₁ ∨ A ⊆ B₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ B₁ᶜ ∪ B₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ B₁
      · by_cases h2 : w ∈ B₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hBinter]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (B₁ᶜ ∩ B₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hBunion] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ B : Set Plane, p ∈ B → q ∈ B → A \ {p, q} ⊆ B → A ⊆ B := by
      intro B hpB hqB hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpB, hqB]
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ B₁ᶜ).Nonempty
    · refine Or.inr (hends B₂ hB2.left_mem hB2.right_mem fun w hw => ?_)
      by_contra hwB2
      exact hnone (hconn _ _ hB1.isArc.isClosed.isOpen_compl hB2.isArc.isClosed.isOpen_compl
        hsub hcase ⟨w, hw, hwB2⟩)
    · refine Or.inl (hends B₁ hB1.left_mem hB1.right_mem fun w hw => ?_)
      by_contra hwB1
      exact hcase ⟨w, hw, hwB1⟩
  -- An arc is more than its two ends.
  have hbig : ∀ A : Set Plane, IsArcBetween A p q → ¬ A ⊆ ({p, q} : Set Plane) := by
    intro A hAar hsub
    obtain ⟨-, w, hw⟩ := hAar.preconnected_diff
    exact hw.2 (hsub hw.1)
  -- The two arcs cannot land in the same piece: the other piece would be just `{p, q}`.
  have hclash : ∀ B B' : Set Plane, B ∪ B' = C → B ∩ B' = {p, q} → IsArcBetween B' p q →
      A₁ ⊆ B → A₂ ⊆ B → False := by
    intro B B' hBB hBBi hB' h1 h2
    refine hbig B' hB' fun w hw => ?_
    rw [← hBBi]
    have hwC : w ∈ C := by rw [← hBB]; exact Or.inr hw
    rw [← hunion] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  -- Once they land in different pieces they exhaust them.
  have hfill : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∩ Y' = {p, q} → X' ⊆ C →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y'i hX'C hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := hX'C hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  rcases key A₁ hA1 hA1C with h1 | h1 <;> rcases key A₂ hA2 hA2C with h2 | h2
  · exact absurd (hclash B₁ B₂ hBunion hBinter hB2 h1 h2) (by simp)
  · rw [hfill A₁ A₂ B₁ B₂ hunion hBinter hB1C hA1.left_mem hA1.right_mem h1 h2,
      hfill A₂ A₁ B₂ B₁ (by rw [Set.union_comm]; exact hunion)
        (by rw [Set.inter_comm]; exact hBinter) hB2C hA2.left_mem hA2.right_mem h2 h1]
    exact hBinter
  · rw [hfill A₁ A₂ B₂ B₁ hunion (by rw [Set.inter_comm]; exact hBinter) hB2C
        hA1.left_mem hA1.right_mem h1 h2,
      hfill A₂ A₁ B₁ B₂ (by rw [Set.union_comm]; exact hunion) hBinter hB1C
        hA2.left_mem hA2.right_mem h2 h1, Set.inter_comm]
    exact hBinter
  · exact absurd (hclash B₂ B₁ (by rw [Set.union_comm]; exact hBunion)
      (by rw [Set.inter_comm]; exact hBinter) hB1 h1 h2) (by simp)

/-! ## `thm:polygonal-crosscut` at the level of sets

The statement a plane-graph consumer wants: sets and arcs, no polygon presentation anywhere in the
hypotheses, and the two spliced curves named by the literal unions `Aᵢ ∪ P`. -/

/-- **The polygonal crosscut theorem, at the level of sets.** `J` is a polygonal Jordan curve, cut
by the two points `p, q` into the arcs `A₁, A₂`; `P` is a polygonal arc from `p` to `q` meeting `J`
in nothing but `p` and `q`. Then a point inside `J` and off `P` lies inside at least one of the two
spliced curves `A₁ ∪ P`, `A₂ ∪ P`.

Nothing is assumed about which side of `J` the crosscut runs on; the proof does not distinguish the
two cases of the blueprint. Nor is `A₁ ∩ A₂ = {p, q}` assumed — it is derived, by
`Schoenflies.two_arcs_inter_of_union`.

The route: present `J` as a `Schoenflies.PrePolygon` with `p` and `q` among its vertices
(`Schoenflies.exists_prePolygon_split`), identify the two given arcs with the two arcs of that
presentation (`Schoenflies.two_arcs_unique_of_isClosed`), and read the parity identity
`π_{A₁ ∪ P} + π_{A₂ ∪ P} = π_J` (`Schoenflies.parity_split`) at the point. Were the point outside
both spliced curves both left-hand terms would vanish
(`Schoenflies.parity_eq_zero_of_mem_outside_cover`, which needs no realization of `Aᵢ ∪ P`),
while the right-hand side is `1` because the point is inside `J`. -/
theorem crosscut_inside_at_least_one {J A₁ A₂ P : Set Plane} {p q x : Plane}
    (hJ : IsJordanCurve J) (hJpoly : IsPolygonal J) (hPpoly : IsPolygonal P)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = J)
    (hParc : IsArcBetween P p q) (hPJ : P ∩ J = {p, q})
    (hx : x ∈ inside J) (hxP : x ∉ P) :
    x ∈ inside (A₁ ∪ P) ∨ x ∈ inside (A₂ ∪ P) := by
  have hpq : p ≠ q := hA1.ne
  have hinter : A₁ ∩ A₂ = {p, q} := two_arcs_inter_of_union hJ hA1 hA2 hunion
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ := exists_prePolygon_split hJ hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating: each is an arc glued to the crosscut.
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A ray direction transverse to every edge in play.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  -- 6. Lemma 2.7: the two crossing counts add up to the curve's, at every point.
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  -- 7. Outside both spliced curves the two counts vanish, and the sum cannot then be `1`.
  have main : x ∈ inside (C.arc a k ∪ P) ∨
      x ∈ inside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hxJ : x ∉ J := (mem_inside_iff.1 hx).1
    have hx1 : x ∉ C.arc a k ∪ P := by
      rintro (h | h)
      exacts [hxJ (hD1J h), hxP h]
    have hx2 : x ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      exacts [hxJ (hD2J h), hxP h]
    have hout1 : x ∈ outside (C.arc a k ∪ P) := by
      have hm : x ∈ inside (C.arc a k ∪ P) ∪ outside (C.arc a k ∪ P) := by
        rw [inside_union_outside]; exact hx1
      exact hm.resolve_left hn1
    have hout2 : x ∈ outside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
      have hm : x ∈ inside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) ∪
          outside (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) := by
        rw [inside_union_outside]; exact hx2
      exact hm.resolve_left hn2
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) x = 0 :=
      parity_eq_zero_of_mem_outside_cover hu hlev1 hclosed1 (by rw [hcov1]; exact hJ1)
        (by rw [hcov1]; exact hout1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) x = 0 :=
      parity_eq_zero_of_mem_outside_cover hu hlev2 hclosed2 (by rw [hcov2]; exact hJ2)
        (by rw [hcov2]; exact hout2)
    have hkey := hsplit x
    rw [hp1, hp2, C.parity_eq_one_of_mem_inside hu hlevC
      (show x ∈ inside C.carrier by rw [hcar]; exact hx)] at hkey
    exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; exact main
  · rw [e1, e2]; exact main.symm

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {H F : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What a walk visits lies on what it draws

`Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover` goes the other way; this direction is the
first half of the proof of `Graph.IsDrawing.pointSet_pathGraphOf`, extracted. -/

/-! ## The geometric half of the descent step

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean`, plus the hypothesis it is missing. -/

/-- **The geometric half of the descent step of `lem:outer-chain`.** "The path `R` lies on one side
of `C` and is a crosscut there; by `thm:polygonal-crosscut`, exactly one of the two cycles
`R ∪ C₁`, `R ∪ C₂` encloses `x`" — weakened to *at least* one, and with `x` required to be off the
drawing.

Everything geometric is `Schoenflies.crosscut_inside_at_least_one`; what happens here is the
translation of the graph data into its hypotheses. The two arcs of the cycle are arcs of the plane
by `Graph.IsDrawing.path_isArcBetween`, they cover the cycle's realisation because their edge lists
do, and they meet exactly at the two cut points by `Schoenflies.two_arcs_inter_of_union` — which is
why `Graph.IsCycleCrosscut` gets away with not recording that. That the crosscut meets the cycle
only at its ends is the `edges_new` and `interior` clauses read through
`Graph.IsDrawing.edge_inter`. -/
theorem crosscutEnclosesOff (drawing : β → ℝ → Plane) (x : Plane) :
    CrosscutEnclosesOff drawing x := by
  intro H F _ hd hpoly hxext e u v a b D R D₁ D₂ hcyc hcc hin e₁ e₂ u₁ v₁ u₂ v₂ T₁ T₂ _ _ hp₁ hp₂
  have hab : a ≠ b := hcc.ne
  have hRne : R ≠ [] := hcc.isPath.ne_nil hab
  have hD1ne : D₁ ≠ [] := hcc.arc₁.ne_nil hab
  have hD2ne : D₂ ≠ [] := hcc.arc₂.ne_nil hab.symm
  -- A cycle's detour is nonempty: its named edge joins two distinct vertices.
  have hDne : D ≠ [] := fun h0 =>
    hd.ne_of_isLink hcyc.isLink (h0 ▸ hcyc.isPath.isWalk).eq_of_nil
  -- The realisation of the cycle, and of the three edge lists.
  have hJcurve : IsJordanCurve (edgesCover drawing (e :: D)) := hd.cycle_isJordanCurve hcyc
  have hJpoly : IsPolygonal (edgesCover drawing (e :: D)) :=
    hd.isPolygonal_edgesCover hpoly hcyc.isWalk_cons (List.cons_ne_nil _ _)
  have hPpoly : IsPolygonal (edgesCover drawing R) :=
    hd.isPolygonal_edgesCover hpoly hcc.isPath.isWalk hRne
  have hA1 : IsArcBetween (edgesCover drawing D₁) a b := hd.path_isArcBetween hcc.arc₁ hD1ne
  have hA2 : IsArcBetween (edgesCover drawing D₂) a b :=
    (hd.path_isArcBetween hcc.arc₂ hD2ne).reverse
  have hParc : IsArcBetween (edgesCover drawing R) a b := hd.path_isArcBetween hcc.isPath hRne
  -- The two arcs cover the cycle, because their edge lists do.
  have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
    rw [← edgesCover_append]
    exact edgesCover_perm hcc.split
  -- The cut points lie on the cycle's realisation.
  have hcut : ∀ y : Plane, y ∈ H.walkVertices u D → y ∈ edgesCover drawing (e :: D) := by
    intro y hy
    exact edgesCover_mono (fun g hg => List.mem_cons_of_mem _ hg)
      (hd.mem_edgesCover_of_mem_walkVertices hcyc.isPath.isWalk hDne hy)
  -- **"No edge of `R` is an edge of `C`; its internal vertices do not lie on `C`."** Two distinct
  -- edges meet only at a vertex incident with both, so a common point of the two realisations is
  -- a vertex of the crosscut and of the cycle, hence one of the two cut points.
  have hPJ : edgesCover drawing R ∩ edgesCover drawing (e :: D) = {a, b} := by
    refine Set.Subset.antisymm (fun z hz => ?_) ?_
    · obtain ⟨hzR, hzJ⟩ := hz
      obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hzR
      obtain ⟨g', hg', hzg'⟩ := mem_edgesCover_iff.1 hzJ
      have hne : g ≠ g' := by
        rintro rfl
        refine hcc.edges_new g hg ?_
        rcases List.mem_cons.1 hg' with rfl | h
        · exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_left _ h
      obtain ⟨-, hincg, hincg'⟩ := hd.edge_inter (hcc.isPath.edge_mem hg)
        (hcyc.mem_edgeSet_cons hg') hne hzg hzg'
      have hzR' : z ∈ H.walkVertices a R := mem_walkVertices_of_mem_covered ⟨g, hg, hincg⟩
      have hzD : z ∈ H.walkVertices u D := by
        rcases List.mem_cons.1 hg' with rfl | h
        · rcases hincg'.eq_or_eq_of_isLink hcyc.isLink with rfl | rfl
          · exact mem_walkVertices_self
          · exact hcyc.isPath.target_mem_walkVertices
        · exact mem_walkVertices_of_mem_covered ⟨g', h, hincg'⟩
      rcases eq_or_ne z a with rfl | hza
      · exact Set.mem_insert _ _
      rcases eq_or_ne z b with rfl | hzb
      · exact Set.mem_insert_of_mem _ rfl
      exact absurd hzD (hcc.interior z hzR' hza hzb)
    · rintro z (rfl | rfl)
      · exact ⟨hParc.left_mem, hcut z hcc.mem_left⟩
      · exact ⟨hParc.right_mem, hcut z hcc.mem_right⟩
  -- **The clause `Graph.CrosscutEncloses` is missing**: `x` is off the crosscut, because it is off
  -- the whole drawing.
  have hxP : x ∉ edgesCover drawing R := fun hxR =>
    hxext (edgesCover_subset_pointSet (fun g hg => hcc.isPath.edge_mem hg) hxR)
  have hmain := crosscut_inside_at_least_one hJcurve hJpoly hPpoly hA1 hA2 hunion hParc hPJ
    hin hxP
  -- The two spliced cycles draw exactly the two unions.
  have hc₁ : edgesCover drawing (e₁ :: T₁) = edgesCover drawing D₁ ∪ edgesCover drawing R := by
    rw [edgesCover_perm hp₁, edgesCover_append]
  have hc₂ : edgesCover drawing (e₂ :: T₂) = edgesCover drawing D₂ ∪ edgesCover drawing R := by
    rw [edgesCover_perm hp₂, edgesCover_append]
  rw [hc₁, hc₂]
  exact hmain

/-! ## `lem:outer-chain` needs only the combinatorial half now

The extra hypothesis of `Graph.CrosscutEnclosesOff` does **not** have to be threaded through
`Graph.Descent`: the chain hypothesis `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block of the chain lies inside it. So the
repair costs the interface nothing at all — `Graph.Descent` is used here exactly as it stands on
`main`, and the two theorems below are drop-in replacements for
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut` with
`Graph.CrosscutEncloses` discharged. -/

namespace IsPlaneChain

variable {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {n : ℕ} {x : Plane}

/-- **The descent step from its two halves**, with the geometric half taken in the corrected form
`Graph.CrosscutEnclosesOff`. The missing clause "`x` is off the drawing of the block" is supplied
from `Graph.OuterOnPairs`, so `Graph.Descent` is produced with its statement on `main` unchanged.
-/
theorem descent_of_crosscutOff (h : IsPlaneChain Γ drawing G n)
    (hout : OuterOnPairs Γ drawing n x) (hce : CrosscutExists Γ drawing n x)
    (hcen : CrosscutEnclosesOff drawing x) : Descent Γ drawing n x := by
  have hext : x ∈ exterior (chainUnion Γ 0 n) drawing := h.mem_exterior_chain hout
  intro i m him e u v D hcyc hin hA hB
  -- Every block of the chain sits inside the whole chain, so `x` is off it too.
  have hblock : chainUnion Γ i (m + 2) ≤ chainUnion Γ 0 n :=
    chainUnion_le fun p _ hp' =>
      h.le_block (i := 0) (m := n) (by omega) (Nat.zero_le p) (by omega)
  have hxb : x ∈ exterior (chainUnion Γ i (m + 2)) drawing :=
    fun hx => hext (pointSet_mono hblock hx)
  obtain ⟨a, b, R, D₁, D₂, hcc⟩ := hce i m him e u v D hcyc hin hA hB
  obtain ⟨e₁, e₂, u₁, v₁, u₂, v₂, T₁, T₂, hc₁, hc₂, hp₁, hp₂⟩ := exists_spliced_cycles hcyc hcc
  exact exists_cycle_edgesOutside_lt hcyc hcc.split.symm hcc.edges_mem hcc.outside₁ hcc.outside₂
    hc₁ hc₂ hp₁ hp₂
    (hcen _ _ (h.block_finite him) (h.block_isDrawing him) (h.block_polygonal him) hxb
      e u v a b D R D₁ D₂ hcyc hcc hin e₁ e₂ u₁ v₁ u₂ v₂ T₁ T₂ hc₁ hc₂ hp₁ hp₂)

/-- **`lem:outer-chain` (outer face of a chain), with the geometric half of the descent step
discharged.** Only `Graph.CrosscutExists` — the purely combinatorial construction of the crosscut
— is still assumed.

This is `Graph.IsPlaneChain.outer_chain_of_crosscut` with the argument `hcen` supplied by
`Graph.crosscutEnclosesOff`. -/
theorem outer_chain_of_crosscutExists (h : IsPlaneChain Γ drawing G n)
    (hout : OuterOnPairs Γ drawing n x) (hce : CrosscutExists Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ IsBounded (face (chainUnion Γ 0 n) drawing x) :=
  h.outer_chain hout (h.descent_of_crosscutOff hout hce (crosscutEnclosesOff drawing x))

end IsPlaneChain

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutExists
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Building the crosscut of the outer-chain descent

`Graph.CrosscutExists`, the combinatorial half of the descent step of `lem:outer-chain`,
discharged. Nothing here is geometric: the only fact about the plane that enters is
`Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
`Γ (j-1)`", and it is used exactly twice, to say that a vertex cannot lie on both
`Γ i ∪ ⋯ ∪ Γ (j-2)` and `Γ j`.

## The blueprint's argument, and how it is formalised here

The blueprint chooses points `a, b` in the relative interiors of an edge of `Γ j` and an edge
of the earlier chain, cuts the cycle `C` there, observes that each of the two arcs must meet
`Γ (j-1)`, and takes a minimum-length path of `Γ (j-1)` between two *maximal subpaths of
`C ∩ Γ (j-1)`* lying on different arcs.

Cutting a cycle at interior points of two of its edges is, combinatorially, the statement that
two distinct edges `g₁ ≠ g₂` of the cycle split the remaining edges into two arcs
(`Graph.IsCycleThrough.split_at_edges`): the closed walk reads

  `… ─g₁→ p ─W₁→ q ─g₂→ q' ─W₂→ p' ─g₁→ …`

and the two arcs are `W₁` and `W₂`, whose visited sets `S₁`, `S₂` are **disjoint** and
**cover** the vertices of the cycle. That pair of facts replaces the notion of a maximal
subpath entirely:

* "`a` and `b` lie on different maximal subpaths of `C ∩ Γ (j-1)`" becomes `a ∈ S₁`, `b ∈ S₂`;
* the property of maximal subpaths that the argument actually consumes — that no subpath of
  `C ∩ Γ (j-1)` joins two of them — becomes `Graph.exists_isCycleCrosscut`'s hypothesis
  `hpres`: *every edge of the cycle that `Γ (j-1)` also has keeps both of its ends on the same
  side*. That is immediate here, because the only cycle edges joining the two sides are `g₁`
  and `g₂`, and neither is an edge of `Γ (j-1)`.

With that, walking along cycle edges of `Γ (j-1)` cannot cross from `S₁` to `S₂`, and all four
minimality clauses of `Graph.IsCycleCrosscut` fall out of one minimisation: among all walks of
`Γ (j-1)` from `S₁` to `S₂`, take one of least length.

* it is a path, because any walk between its own two ends is a competitor
  (`Graph.IsWalk.isPath_of_minLength`);
* its internal vertices miss `C`, because a vertex of `C` on it lies in `S₁` or in `S₂`, and
  either way one of the two halves is a strictly shorter competitor;
* no edge of it is an edge of `C`: such an edge has both ends on `C`, hence both ends among
  `{a, b}` by the previous clause, hence joins `S₁` to `S₂` while lying in `Γ (j-1)`, which
  `hpres` forbids;
* each arc of `C` between `a` and `b` carries an edge outside `Γ (j-1)`, since otherwise the
  arc itself would be a walk of cycle edges of `Γ (j-1)` from `S₁` to `S₂`.

## Two general lemmas

`Graph.IsPath.split_at_edge` (cut a path at one of its edges, with the two freshness clauses
`Graph.IsCycleThrough.split_aux` asks for) and `Graph.IsCycleThrough.rotate` (present a cycle
through any one of its edges) are general facts about walks with nothing to do with this
development; they are the missing companions of `Graph.IsPath.split_meet` and
`Graph.IsCycleThrough.split_at` and belong in `Schoenflies/Graph/Walk.lean` and
`Schoenflies/FaceCyclesProof.lean` respectively.

## Blueprint

* `Graph.IsPath.split_at_edge`, `Graph.IsCycleThrough.rotate`,
  `Graph.IsCycleThrough.split_at_edges` — "choose points `a, b` in the relative interiors of
  these two edges. The two arcs of the cycle `C` from `a` to `b` are internally disjoint",
  read combinatorially (`lem:outer-chain`).
* `Graph.exists_isCycleCrosscut` — "since `Γ_{j-1}` is connected, there is a path in `Γ_{j-1}`
  from `P` to `C ∖ V(P)`. Choose such a path `R` of minimum length …", the whole minimality
  paragraph of `lem:outer-chain`, with the chain abstracted away into the two sides `S₁, S₂`.
* `Graph.IsPlaneChain.crosscutExists` — **`Graph.CrosscutExists`**, the combinatorial half of
  the descent step of `lem:outer-chain`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ## Cutting a path at an edge, and rotating a cycle -/

section General

variable {α β : Type*} {G : Graph α β}

/-! ## The crosscut, from a two-sided cycle and a connected subgraph -/

/-- **The minimality paragraph of `lem:outer-chain`, with the chain abstracted away.**

The cycle `e :: D` of `H` has its vertices split into two disjoint sides `S₁, S₂` — in the
application, the two arcs cut off by an edge of `Γ j` and an edge of the earlier chain — in
such a way that no edge of the cycle lying in `F` joins the two sides (`hpres`). If `F` is
connected and has a vertex on each side, then a minimum-length path of `F` from one side to
the other is a crosscut of the cycle in the sense of `Graph.IsCycleCrosscut`.

`hpres` is what the blueprint's *maximal subpaths of `C ∩ Γ (j-1)`* are for: it is the only
property of them the argument uses, and here it is a one-line consequence of the two cut edges
being outside `F`. -/
theorem exists_isCycleCrosscut {H F : Graph α β} {e : β} {u v : α} {D : List β}
    (hcyc : H.IsCycleThrough e u v D) (hFH : F ≤ H) {S₁ S₂ : Set α}
    (hdisj : Disjoint S₁ S₂) (hcover : H.walkVertices u D = S₁ ∪ S₂)
    (hpres : ∀ f ∈ e :: D, f ∈ E(F) → ∀ z w, H.IsLink f z w → (z ∈ S₁ ↔ w ∈ S₁))
    (hconn : F.Connected) (ha : ∃ a ∈ S₁, a ∈ V(F)) (hb : ∃ b ∈ S₂, b ∈ V(F)) :
    ∃ (a b : α) (R D₁ D₂ : List β), IsCycleCrosscut H F e u v D a b R D₁ D₂ := by
  classical
  -- Walking along cycle edges that `F` also has never crosses from one side to the other.
  have hside : ∀ (a' b' : α) (T : List β), H.IsWalk a' T b' → (∀ f ∈ T, f ∈ E(F)) →
      (∀ f ∈ T, f ∈ e :: D) → a' ∈ S₁ → b' ∈ S₁ := by
    intro a' b' T hw
    induction hw with
    | nil => exact fun _ _ hm => hm
    | @cons z w b' f T hl hW ih =>
      intro hFe hCe hz
      exact ih (fun f' hf' => hFe f' (List.mem_cons_of_mem _ hf'))
        (fun f' hf' => hCe f' (List.mem_cons_of_mem _ hf'))
        ((hpres f (hCe f List.mem_cons_self) (hFe f List.mem_cons_self) z w hl).1 hz)
  -- **"Choose such a path `R` of minimum length."**
  obtain ⟨a₀, ha₀S, ha₀F⟩ := ha
  obtain ⟨b₀, hb₀S, hb₀F⟩ := hb
  have hex : ∃ k, ∃ (T : List β) (a b : α),
      T.length = k ∧ F.IsWalk a T b ∧ a ∈ S₁ ∧ b ∈ S₂ := by
    obtain ⟨T, hT⟩ := hconn.reaches ha₀F hb₀F
    exact ⟨T.length, T, a₀, b₀, rfl, hT, ha₀S, hb₀S⟩
  obtain ⟨T, a, b, hTlen, hTwalk, haS, hbS⟩ := Nat.find_spec hex
  have hmin : ∀ (T' : List β) (a' b' : α), F.IsWalk a' T' b' → a' ∈ S₁ → b' ∈ S₂ →
      T.length ≤ T'.length := by
    intro T' a' b' hw' h1 h2
    rw [hTlen]
    exact Nat.find_le ⟨T', a', b', rfl, hw', h1, h2⟩
  -- A shortest walk between its own two ends is a path.
  have hR : F.IsPath a T b := hTwalk.isPath_of_minLength fun W' hW' => hmin W' a b hW' haS hbS
  have hTedges : ∀ f ∈ T, f ∈ E(F) := fun f hf => hR.edge_mem hf
  have hab : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.1 hdisj haS hbS
  have haC : a ∈ H.walkVertices u D := by rw [hcover]; exact Or.inl haS
  have hbC : b ∈ H.walkVertices u D := by rw [hcover]; exact Or.inr hbS
  obtain ⟨D₁, D₂, harc₁, harc₂, hsplit, -⟩ := hcyc.split_at haC hbC hab
  -- **"Its internal vertices do not lie on `C`."**
  have hTvert : H.walkVertices a T = F.walkVertices a T := walkVertices_congr_of_le hFH hTedges
  have hinterior : ∀ y ∈ H.walkVertices a T, y ≠ a → y ≠ b → y ∉ H.walkVertices u D := by
    intro y hy hya hyb hyC
    rw [hTvert] at hy
    obtain ⟨T₁, T₂, hTcat, hT₁, hT₂, -⟩ := hR.split hy
    have hlen₁ : 1 ≤ T₁.length := by
      cases T₁ with
      | nil => exact absurd hT₁.isWalk.eq_of_nil.symm hya
      | cons _ _ => simp
    have hlen₂ : 1 ≤ T₂.length := by
      cases T₂ with
      | nil => exact absurd hT₂.isWalk.eq_of_nil hyb
      | cons _ _ => simp
    have hcat : T.length = T₁.length + T₂.length := by rw [hTcat, List.length_append]
    rw [hcover] at hyC
    rcases hyC with hy₁ | hy₂
    · have := hmin T₂ y b hT₂.isWalk hy₁ hbS
      omega
    · have := hmin T₁ a y hT₁.isWalk haS hy₂
      omega
  -- **"No edge of `R` is an edge of `C`."**
  have hedges_new : ∀ f ∈ T, f ∉ D ++ [e] := by
    intro f hf hfC
    have hfC' : f ∈ e :: D := by
      simp only [List.mem_append, List.mem_cons] at hfC ⊢
      tauto
    have hfF : f ∈ E(F) := hTedges f hf
    obtain ⟨z, w, hlfF⟩ := exists_isLink_of_mem_edgeSet hfF
    have hlf : H.IsLink f z w := hlfF.mono hFH
    have hz' : z = a ∨ z = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior z (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_left⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_left)
    have hw' : w = a ∨ w = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior w (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_right⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_right)
    have hzw : z ≠ w := by
      rintro rfl
      exact hR.not_isLoopAt hf z hlfF
    -- The edge would then join the two sides while lying in `F`.
    have hlink : H.IsLink f a b := by
      rcases hz' with rfl | rfl
      · rcases hw' with rfl | rfl
        · exact absurd rfl hzw
        · exact hlf
      · rcases hw' with rfl | rfl
        · exact hlf.symm
        · exact absurd rfl hzw
    refine Set.disjoint_left.1 hdisj (hside a b [f] (IsWalk.single hlink) ?_ ?_ haS) hbS
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfF
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfC'
  -- **"Each arc contains an edge outside `Γ (j-1)`."**
  have houtside : ∀ (T' : List β), H.IsWalk a T' b → (∀ f ∈ T', f ∈ e :: D) →
      ∃ f ∈ T', f ∉ E(F) := by
    intro T' hw hC
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.1 hdisj (hside a b T' hw hcon hC haS) hbS
  have hD₁C : ∀ f ∈ D₁, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_left _ hf)
  have hD₂C : ∀ f ∈ D₂, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_right _ hf)
  obtain ⟨f₂, hf₂, hf₂F⟩ := houtside D₂.reverse harc₂.reverse.isWalk
    fun f hf => hD₂C f (List.mem_reverse.1 hf)
  exact ⟨a, b, T, D₁, D₂,
    { ne := hab
      arc₁ := harc₁
      arc₂ := harc₂
      split := hsplit
      isPath := hR.mono hFH
      mem_left := haC
      mem_right := hbC
      edges_mem := hTedges
      edges_new := hedges_new
      interior := hinterior
      outside₁ := houtside D₁ harc₁.isWalk hD₁C
      outside₂ := ⟨f₂, List.mem_reverse.1 hf₂, hf₂F⟩ }⟩

end General

/-! ## The descent step's crosscut -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ}

/-- **`Graph.CrosscutExists`, discharged.** From a cycle of the block
`Γ i ∪ ⋯ ∪ Γ (i+m+2)` carrying an edge of `Γ (i+m+2)` and an edge of the earlier chain, both
outside `Γ (i+m+1)`, build a crosscut of that cycle inside `Γ (i+m+1)`.

The two named edges cut the cycle into two arcs (`Graph.IsCycleThrough.split_at_edges`). Each
arc has a vertex in `Γ (i+m+1)`: walking along it from the edge of `Γ (i+m+2)` to the edge of
the earlier chain leaves `V(Γ (i+m+2))` at some edge, and that edge belongs neither to
`Γ (i+m+2)` (both its ends would stay inside) nor to the earlier chain (its end inside
`V(Γ (i+m+2))` would then lie on both, which
`Graph.IsPlaneChain.disjoint_block_far` forbids), so it belongs to `Γ (i+m+1)`. The rest is
`Graph.exists_isCycleCrosscut`. -/
theorem IsPlaneChain.crosscutExists (h : IsPlaneChain Γ drawing G n) {x : Plane} :
    CrosscutExists Γ drawing n x := by
  intro i m him e u v D hcyc _hin hA hB
  obtain ⟨gA, hgAC, hgAJ, hgAF⟩ := hA
  obtain ⟨gB, hgBC, hgBL, hgBF⟩ := hB
  -- The three pieces of the block, inside the block.
  have hFH : Γ (i + m + 1) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hJH : Γ (i + m + 2) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hLH : chainUnion Γ i m ≤ chainUnion Γ i (m + 2) :=
    chainUnion_le fun p hp _ => h.le_block him hp (by omega)
  -- Every edge of the block is an edge of one of the three.
  have hsplit : ∀ f ∈ E(chainUnion Γ i (m + 2)),
      f ∈ E(chainUnion Γ i m) ∨ f ∈ E(Γ (i + m + 1)) ∨ f ∈ E(Γ (i + m + 2)) := by
    intro f hf
    obtain ⟨p, hp, hp', hfp⟩ := mem_edgeSet_chainUnion.1 hf
    rcases Nat.lt_or_ge p (i + m + 1) with hlt | hge
    · exact Or.inl (mem_edgeSet_chainUnion.2 ⟨p, hp, by omega, hfp⟩)
    rcases Nat.lt_or_ge p (i + m + 2) with hlt' | hge'
    · obtain rfl : p = i + m + 1 := by omega
      exact Or.inr (Or.inl hfp)
    · obtain rfl : p = i + m + 2 := by omega
      exact Or.inr (Or.inr hfp)
  -- **"`Γ j` meets the earlier chain only through `Γ (j-1)`."** The only geometry used.
  have hVdisj : ∀ z : Plane, z ∈ V(chainUnion Γ i m) → z ∈ V(Γ (i + m + 2)) → False := by
    intro z hz hz'
    exact Set.disjoint_left.1 (h.disjoint_block_far (by omega))
      (vertexSet_subset_pointSet hz) (vertexSet_subset_pointSet hz')
  have hgAB : gA ≠ gB := by
    rintro rfl
    obtain ⟨p, hp, hp', hgp⟩ := mem_edgeSet_chainUnion.1 hgBL
    exact Set.disjoint_left.1
      (h.disjoint_edgeSet (p := p) (q := i + m + 2) (by omega) (by omega) (by omega)) hgp hgAJ
  obtain ⟨p₀, p₁, q₀, q₁, W₁, W₂, hlA, hW₁, hlB, hW₂, hperm, hdisj, hcover⟩ :=
    hcyc.split_at_edges hgAC hgBC hgAB
  have hlAJ : (Γ (i + m + 2)).IsLink gA p₁ p₀ := (hJH.isLink_iff hgAJ).2 hlA
  have hlBL : (chainUnion Γ i m).IsLink gB q₀ q₁ := (hLH.isLink_iff hgBL).2 hlB
  -- Neither cut edge is an edge of `Γ (i+m+1)`, so every cycle edge that is keeps its two
  -- ends on one arc.
  have hpres : ∀ f ∈ e :: D, f ∈ E(Γ (i + m + 1)) → ∀ z w : Plane,
      (chainUnion Γ i (m + 2)).IsLink f z w →
      (z ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁ ↔
        w ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁) := by
    intro f hfC hfF z w hlf
    have hfA : f ≠ gA := fun hh => hgAF (hh ▸ hfF)
    have hfB : f ≠ gB := fun hh => hgBF (hh ▸ hfF)
    have hfW : f ∈ W₁ ∨ f ∈ W₂ := by
      rcases List.mem_cons.1 (hperm.mem_iff.2 hfC) with rfl | hmem
      · exact absurd rfl hfA
      rcases List.mem_append.1 hmem with hmem' | hmem'
      · exact Or.inl hmem'
      rcases List.mem_cons.1 hmem' with rfl | hmem''
      · exact absurd rfl hfB
      · exact Or.inr hmem''
    rcases hfW with hfW | hfW
    · exact iff_of_true (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
        (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
    · refine iff_of_false (fun hz => ?_) fun hw => ?_
      · exact Set.disjoint_left.1 hdisj hz
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
      · exact Set.disjoint_left.1 hdisj hw
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
  -- **"Each of those two arcs must meet `Γ (j-1)`."** First arc.
  have hclaimA : ∃ a ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁, a ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk p₁ (gA :: (W₁ ++ [gB])) q₁ :=
      .cons hlA (hW₁.isWalk.append (IsWalk.single hlB))
    obtain ⟨f, hf, z, w, hlf, hzJ, hwJ⟩ := hwalk.crossing (S := V(Γ (i + m + 2)))
      hlAJ.left_mem fun hh => hVdisj q₁ hlBL.right_mem hh
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh => hwJ ((hJH.isLink_iff hh).2 hlf).right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh =>
      hVdisj z ((hLH.isLink_iff hh).2 hlf).left_mem hzJ
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₁ : f ∈ W₁ := by
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact absurd hfF hgAF
      rcases List.mem_append.1 hf' with hf'' | hf''
      · exact hf''
      · obtain rfl : f = gB := by simpa using hf''
        exact absurd hfF hgBF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₁, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  -- Second arc, with the roles of the two ends of the chain exchanged.
  have hclaimB : ∃ b ∈ (chainUnion Γ i (m + 2)).walkVertices q₁ W₂, b ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk q₁ (W₂ ++ [gA]) p₀ :=
      hW₂.isWalk.append (IsWalk.single hlA)
    obtain ⟨f, hf, z, w, hlf, hzL, hwL⟩ := hwalk.crossing (S := V(chainUnion Γ i m))
      hlBL.right_mem fun hh => hVdisj p₀ hh hlAJ.right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh => hwL ((hLH.isLink_iff hh).2 hlf).right_mem
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh =>
      hVdisj z hzL ((hJH.isLink_iff hh).2 hlf).left_mem
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₂ : f ∈ W₂ := by
      rcases List.mem_append.1 hf with hf' | hf'
      · exact hf'
      · obtain rfl : f = gA := by simpa using hf'
        exact absurd hfF hgAF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₂, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  exact exists_isCycleCrosscut hcyc hFH hdisj hcover hpres
    (h.twoConnected _ (by omega)).connected hclaimA hclaimB

end Chain

end Graph
end

section
-- module Solutions.Q146_CD.OuterChainClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `lem:outer-chain`, with nothing assumed

`Schoenflies/OuterChain.lean` proves the outer-chain lemma from `Graph.Descent`, the middle
paragraph of the blueprint's proof, which it states and assumes. `Descent` splits into a
combinatorial half and a geometric half, and the two are proved in the two modules imported
here. This file is the one line that puts them together.

The split was worth making. The combinatorial half is a minimisation over walks with no
geometry in it at all; the geometric half is one plane graph, one cycle and one crosscut, with
no chain. Neither module has to know the other exists, and the geometric half turned out to be
**false as the assumed version stated it** — see the counterexample recorded in
`Schoenflies/OuterChain.lean` where that version used to stand. Had the gap been a `sorry`
instead of a named hypothesis, the falsity would have surfaced only when someone came back to
fill it in, and every consumer written in the meantime would have been built on sand.

## Blueprint

* `Graph.IsPlaneChain.outer_chain'` — **`lem:outer-chain`**: if `x` is in the outer face of
  every consecutive pair `Γ p ∪ Γ (p+1)`, it is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`. Same
  statement as `Graph.IsPlaneChain.outer_chain`, with its hypothesis discharged.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {n : ℕ} {x : Plane}

namespace IsPlaneChain

/-- **`lem:outer-chain`.** Let `Γ 0, …, Γ n` (`n ≥ 2`) be finite 2-connected polygonal plane
graphs inside one ambient plane graph, consecutive ones sharing at least two vertices and
nonconsecutive ones disjoint. If `x` is in the outer face of every consecutive pair, it is in
the outer face of the whole chain.

"In the outer face" is spelled as everywhere in this development: off the drawing, with an
unbounded face through it. -/
theorem outer_chain' (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) :=
  h.outer_chain_of_crosscutExists hout h.crosscutExists

end IsPlaneChain

end Graph
end

section
-- module Solutions.Q146_CD.ArcComplement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A simple arc does not separate the plane

`thm:arc-complement`.  Two points off a simple arc `A` are covered by a chain of small
axis-parallel squares strung along `A`; the two points lie in the outer face of every
consecutive pair of links, hence — by `lem:outer-chain` — in the outer face of the whole chain,
which is an open connected set missing `A`.  `lem:polygonal-connected` then joins them there.

## The single-ambient-graph obligation, and how it is met

`Graph.IsPlaneChain` requires every link `Γ i` to be a subgraph of **one** ambient plane graph
with **one** drawing.  A link built as the polygonal overlay of its own squares would *not*
qualify: the total overlay cuts those same segments at the crossings with the squares of other
links as well, so a sub-overlay has edges the total overlay has subdivided further.

The construction is therefore inverted.  `familyPieces c N r` is **one** list holding the four
sides of every small square; `familyOverlay c N r` is the one overlay of that list; and a link
is carved out of it by restricting the *edge set*:

* `segGraph S` — the plane graph spanned by a set `S` of straight edges, with the ends of those
  edges as vertices.  `overlayGraph pieces points = segGraph {Q | Q ∈ overlayPieces pieces
  points}` holds by `rfl`, so `segGraph_mono` turns a subset of the overlay's edges into a
  subgraph of the overlay with nothing to prove.
* `squareGraph pieces points c r` — the edges of the overlay lying on the boundary of the square
  of radius `r` about `c`, spanned.  It occupies exactly that boundary
  (`pointSet_squareGraph`), and every cut point on the boundary is one of its vertices
  (`mem_vertexSet_squareGraph`), which is what `Graph.IsTwoConnected.union` needs.
* `familyChain c N m r i` — the `i`-th link: `Graph.chainUnion` of the `m + 1` square graphs of
  the `i`-th coarse subarc.  Consecutive links share the square at the sample they have in
  common; nonconsecutive links are disjoint.

`isPlaneChain_familyChain` is the theorem that this family is a `Graph.IsPlaneChain`, stated for
an arbitrary family of centres `c : ℕ → Plane` with two geometric hypotheses — consecutive
centres closer than one radius, nonconsecutive-block centres further apart than two radii.  The
arc enters only in `exists_face_of_notMem_arc`, where `c j = α(j/N)`.

## What is assumed

Three hypotheses, all named in the statements that carry them.

* `SquaresTwoConnected` — **the part of a polygonal overlay lying on the boundary of one of its
  squares is 2-connected.**  That part is the subdivided boundary cycle of an axis-parallel
  square: four sides, cut at finitely many interior points, every cut point a vertex, the four
  corners among the vertices.  It is a cycle, so `Graph.IsLongCycle.isTwoConnected` finishes;
  what a discharger must build is the cyclic order of the cut points along the four sides, for
  which `Schoenflies/SegmentOrder.lean` is the tool.  Nothing about the arc, the chain or the
  outer face enters the statement.
* `Graph.CrosscutExists` and `Graph.CrosscutEncloses` — the two halves of the descent step of
  `lem:outer-chain`, quoted from `Schoenflies/OuterChain.lean` unchanged.  Because the chain is
  built from choices made inside the proof of `exists_face_of_notMem_arc`, they appear there in
  ∀-form: `CrosscutExists` conditioned on `Graph.IsPlaneChain` (which is how a discharger will
  state it) and `CrosscutEncloses` for every point.

## Blueprint

* `segGraph`, `squareGraph`, `familyPieces`, `familyOverlay`, `familySquare`, `familyChain` —
  the construction of the proof of `thm:arc-complement`: "around every sample draw the boundary
  of the axis-parallel square of `ℓ^∞`-radius `δ/4`, and let `Γ_i` be the polygonal overlay
  (`lem:polygonal-overlay`) of the square boundaries associated with `A_i`".
* `familyChain_isTwoConnected` — "it follows inductively from `lem:union-two-connected` that
  `Γ_i` is 2-connected".
* `isPlaneChain_familyChain` — "consecutive graphs `Γ_i, Γ_{i+1}` share the square at their
  common sample.  If `|i-j| ≥ 2`, then `Γ_i` and `Γ_j` are disjoint".
* `outer_of_notMem_closedSquare`, `outerOnPairs_familyChain` — "the graph `Γ_i ∪ Γ_{i+1}` is
  contained in the `ℓ^∞`-square of radius `3d` centered at `a_i` … both `p` and `q` lie outside
  this containing square and hence in the outer face of the pair".
* `notMem_face_of_mem_openSquare` — "if it lies inside, the boundary cycle of that square
  separates it from the outer face of `G`".
* `exists_face_of_notMem_arc` — the whole proof of `thm:arc-complement` up to the last sentence.
* `isConnected_compl_arc`, `exists_simple_poly_compl_arc` — **`thm:arc-complement`**: the
  complement of a simple arc is connected, and any two of its points are joined in it by a
  simple polygonal arc.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## Part 1: the subgraph of the plane spanned by a set of straight edges -/

variable {S T : Set Piece} {P : Piece} {x y v : Plane}

/-- An end of an edge is a vertex. -/
theorem mem_vertexSet_segGraph_of_end (hP : P ∈ S) (h : v = P.1 ∨ v = P.2) :
    v ∈ V(segGraph S) := ⟨P, hP, h⟩

/-- **More edges, larger graph.**  This is the whole point of `segGraph`: the pieces of the
chain are subgraphs of one ambient overlay by construction. -/
theorem segGraph_mono (h : S ⊆ T) : segGraph S ≤ segGraph T where
  vertexSet_mono := by rintro v ⟨P, hP, hv⟩; exact ⟨P, h hP, hv⟩
  isLink_mono := by rintro P a b ⟨hP, hab⟩; exact ⟨h hP, hab⟩

theorem segGraph_finite (hS : S.Finite) : Graph.Finite (segGraph S) where
  finite_vertexSet := by
    refine Set.Finite.subset ((hS.image (fun P : Piece => P.1)).union
      (hS.image (fun P : Piece => P.2))) ?_
    rintro v ⟨P, hP, rfl | rfl⟩
    exacts [Or.inl ⟨P, hP, rfl⟩, Or.inr ⟨P, hP, rfl⟩]
  finite_edgeSet := hS

/-- What a spanned graph occupies is the union of its segments: every vertex is an end of an
edge, so the vertices add nothing. -/
theorem pointSet_segGraph (S : Set Piece) :
    Graph.pointSet (segGraph S) segmentDrawing = ⋃ P ∈ S, P.seg := by
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, segGraph_vertexSet,
    mem_setOf_eq, segGraph_edgeSet, edgeArc_segmentDrawing]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ## Part 2: the part of an overlay lying on one square

The chain graphs are assembled out of these.  Each is the set of overlay edges whose segment
lies on one small square boundary, spanned by `segGraph` — so it is a subgraph of the *total*
overlay, not an overlay of the four sides of that square alone. -/

/-- **Every point of a source segment lies on an overlay edge inside that source segment.**
`Schoenflies.exists_overlayPiece_end_subset` is the same statement for a *cut* point, with the
edge pinned so as to have that point among its ends; this is the plain covering form, and it is
what makes the part of the overlay on a square occupy the whole of that square's boundary. -/
theorem exists_overlayPiece_mem_subset {pieces : List Piece} {points : List Plane}
    {x : Plane} {P₀ : Piece} (hP₀ : P₀ ∈ pieces) (hx : x ∈ P₀.seg) :
    ∃ Q ∈ overlayPieces pieces points, x ∈ Q.seg ∧ Q.seg ⊆ P₀.seg := by
  -- The pieces of the subdivision of `[P₀]` alone already cover `P₀.seg`.
  have hcov : x ∈ cover (subdivide [P₀] points) := by
    rw [subdivide_cover, cover_cons, cover_nil, union_empty]
    exact hx
  simp only [cover, mem_iUnion, exists_prop] at hcov
  obtain ⟨Q, hQ, hxQ⟩ := hcov
  have hQpieces : Q ∈ subdivide pieces points :=
    subdivide_mono points (by simpa using hP₀) Q hQ
  have hQsub : Q.seg ⊆ P₀.seg := by
    obtain ⟨R, hR, hseg, -⟩ := subdivide_subset [P₀] points Q hQ
    rw [List.mem_singleton] at hR
    exact hR ▸ hseg
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQpieces, rfl⟩, by rwa [orientPiece_seg],
    by rw [orientPiece_seg]; exact hQsub⟩

variable {pieces : List Piece} {points : List Plane} {c c₁ c₂ : Plane} {r : ℝ}

/-- The edges of an overlay whose segment lies on the boundary of the square of `ℓ^∞`-radius
`r` about `c`. -/
def squareEdges (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) : Set Piece :=
  {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ frontier (Plane.closedSquare c r)}

/-- **The part of one overlay lying on one square boundary.**  A subgraph of that overlay by
construction (`squareGraph_le`), which is the single-ambient-graph obligation of
`Graph.IsPlaneChain` discharged at the bottom of the tower. -/
def squareGraph (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) :
    Graph Plane Piece :=
  segGraph (squareEdges pieces points c r)

theorem squareEdges_finite : (squareEdges pieces points c r).Finite :=
  (overlayPieces pieces points).finite_toSet.subset fun _ hQ => hQ.1

theorem squareGraph_le : squareGraph pieces points c r ≤ overlayGraph pieces points :=
  segGraph_mono fun _ hQ => hQ.1

instance squareGraph_finite : Graph.Finite (squareGraph pieces points c r) :=
  segGraph_finite squareEdges_finite

theorem pointSet_squareGraph_subset :
    Graph.pointSet (squareGraph pieces points c r) segmentDrawing ⊆
      frontier (Plane.closedSquare c r) := by
  rw [squareGraph, pointSet_segGraph]
  exact iUnion₂_subset fun _ hQ => hQ.2

/-- **The part of the overlay on a square occupies the whole square boundary.**  Every point of
the boundary lies on one of the four sides, and the overlay subdivides that side into pieces
that stay inside it. -/
theorem pointSet_squareGraph (hr : 0 ≤ r) (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    Graph.pointSet (squareGraph pieces points c r) segmentDrawing =
      frontier (Plane.closedSquare c r) := by
  refine subset_antisymm pointSet_squareGraph_subset fun z hz => ?_
  rw [← cover_squarePieces c hr] at hz
  simp only [cover, mem_iUnion, exists_prop] at hz
  obtain ⟨P₀, hP₀, hzP₀⟩ := hz
  obtain ⟨Q, hQ, hzQ, hQsub⟩ := exists_overlayPiece_mem_subset (points := points) (hsub P₀ hP₀) hzP₀
  have hQfr : Q.seg ⊆ frontier (Plane.closedSquare c r) := by
    rw [← cover_squarePieces c hr]
    exact hQsub.trans fun w hw => mem_iUnion₂.2 ⟨P₀, hP₀, hw⟩
  rw [squareGraph, pointSet_segGraph]
  exact mem_iUnion₂.2 ⟨Q, ⟨hQ, hQfr⟩, hzQ⟩

/-- A cut point on a square boundary is a **vertex** of the part of the overlay on that
square.  This is what turns "two nearby squares meet in two points" into the two common
*vertices* that `Graph.IsTwoConnected.union` consumes. -/
theorem mem_vertexSet_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg) (hr : 0 ≤ r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {z : Plane} (hz : z ∈ points)
    (hzf : z ∈ frontier (Plane.closedSquare c r)) :
    z ∈ V(squareGraph pieces points c r) := by
  rw [← cover_squarePieces c hr] at hzf
  simp only [cover, mem_iUnion, exists_prop] at hzf
  obtain ⟨P₀, hP₀, hzP₀⟩ := hzf
  obtain ⟨Q, hQ, hend, hQsub⟩ :=
    exists_overlayPiece_end_subset (points := points) hnd hz (hsub P₀ hP₀) hzP₀
  have hQfr : Q.seg ⊆ frontier (Plane.closedSquare c r) := by
    rw [← cover_squarePieces c hr]
    exact hQsub.trans fun w hw => mem_iUnion₂.2 ⟨P₀, hP₀, hw⟩
  exact mem_vertexSet_segGraph_of_end ⟨hQ, hQfr⟩ hend

/-- **Two nearby congruent squares contribute two common vertices**, each a vertex of the part
of the overlay lying on its own square.  With equal centres this produces two vertices of one
square, which is how consecutive links of the chain are shown to meet. -/
theorem exists_two_vertices_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r) (hd : Plane.supDist c₁ c₂ < r)
    (h₁ : ∀ P ∈ squarePieces c₁ r, P ∈ pieces) (h₂ : ∀ P ∈ squarePieces c₂ r, P ∈ pieces) :
    ∃ a b : Plane, a ≠ b ∧
      a ∈ V(squareGraph pieces points c₁ r) ∧ a ∈ V(squareGraph pieces points c₂ r) ∧
      b ∈ V(squareGraph pieces points c₁ r) ∧ b ∈ V(squareGraph pieces points c₂ r) := by
  obtain ⟨a, b, hab, ha, hb, haf, hbf⟩ :=
    exists_two_cut_points (points := points) hnd hMeets hr hd h₁ h₂
  exact ⟨a, b, hab,
    mem_vertexSet_squareGraph hnd hr.le h₁ ha haf.1,
    mem_vertexSet_squareGraph hnd hr.le h₂ ha haf.2,
    mem_vertexSet_squareGraph hnd hr.le h₁ hb hbf.1,
    mem_vertexSet_squareGraph hnd hr.le h₂ hb hbf.2⟩

/-! ## Part 3: the chain of square boundaries

Everything here is about a family of centres `c : ℕ → Plane` and one radius `r`; the arc enters
only in Part 5, where `c j = α (j / N)`.  Separating the two keeps the single-ambient-graph
bookkeeping free of parametrisation arithmetic. -/

/-- **The one list of source segments**: the four sides of the square of `ℓ^∞`-radius `r`
about each of the centres `c 0, …, c N`.

The whole proof rests on this being *one* list.  A chain link built as the overlay of its own
squares would not be a subgraph of the total overlay, because the total overlay cuts those
segments at the crossings with squares of other links as well. -/
noncomputable def familyPieces (c : ℕ → Plane) (N : ℕ) (r : ℝ) : List Piece :=
  (List.range (N + 1)).flatMap fun j => squarePieces (c j) r

variable {c : ℕ → Plane} {N m i j : ℕ}

theorem mem_familyPieces {P : Piece} :
    P ∈ familyPieces c N r ↔ ∃ j ≤ N, P ∈ squarePieces (c j) r := by
  simp only [familyPieces, List.mem_flatMap, List.mem_range]
  exact ⟨fun ⟨j, hj, hP⟩ => ⟨j, by omega, hP⟩, fun ⟨j, hj, hP⟩ => ⟨j, by omega, hP⟩⟩

theorem squarePieces_subset_familyPieces (hj : j ≤ N) :
    ∀ P ∈ squarePieces (c j) r, P ∈ familyPieces c N r :=
  fun _ hP => mem_familyPieces.2 ⟨j, hj, hP⟩

theorem familyPieces_nondeg (hr : 0 < r) : ∀ P ∈ familyPieces c N r, P.Nondeg := by
  intro P hP
  obtain ⟨j, -, hPj⟩ := mem_familyPieces.1 hP
  exact squarePieces_nondeg (c j) hr P hPj

/-- The cut points of that list, chosen once and for all.  `Schoenflies.exists_cut_points`
produces them existentially; naming them here is what lets every chain link be a subgraph of
*the same* overlay. -/
noncomputable def familyPoints (c : ℕ → Plane) (N : ℕ) (r : ℝ) : List Plane :=
  (exists_cut_points (familyPieces c N r)).choose

theorem familyPoints_endsAreCut : EndsAreCut (familyPieces c N r) (familyPoints c N r) :=
  (exists_cut_points (familyPieces c N r)).choose_spec.1

theorem familyPoints_meetsAreCut : MeetsAreCut (familyPieces c N r) (familyPoints c N r) :=
  (exists_cut_points (familyPieces c N r)).choose_spec.2

/-- **The single ambient plane graph of the whole proof**: the polygonal overlay of every small
square at once (`lem:polygonal-overlay`). -/
noncomputable def familyOverlay (c : ℕ → Plane) (N : ℕ) (r : ℝ) : Graph Plane Piece :=
  overlayGraph (familyPieces c N r) (familyPoints c N r)

/-- The part of the ambient overlay lying on the `j`-th small square. -/
noncomputable def familySquare (c : ℕ → Plane) (N : ℕ) (r : ℝ) (j : ℕ) : Graph Plane Piece :=
  squareGraph (familyPieces c N r) (familyPoints c N r) (c j) r

/-- **The `i`-th link of the chain, `Γ_i`**: the squares at the `m + 1` fine samples
`i·m, …, i·m + m` of the `i`-th coarse subarc.  Consecutive links share the square at the
sample they have in common. -/
noncomputable def familyChain (c : ℕ → Plane) (N m : ℕ) (r : ℝ) (i : ℕ) : Graph Plane Piece :=
  Graph.chainUnion (familySquare c N r) (i * m) m

theorem familySquare_le : familySquare c N r j ≤ familyOverlay c N r := squareGraph_le

instance familySquare_finite : Graph.Finite (familySquare c N r j) := squareGraph_finite

theorem familyChain_le : familyChain c N m r i ≤ familyOverlay c N r :=
  Graph.chainUnion_le fun _ _ _ => familySquare_le

theorem familyChain_finite : (familyChain c N m r i).Finite :=
  Graph.chainUnion_finite fun _ _ _ => familySquare_finite

/-- The drawing of the ambient overlay: every edge is a straight segment. -/
theorem familyOverlay_isDrawing (hr : 0 < r) :
    Graph.IsDrawing (familyOverlay c N r) segmentDrawing :=
  overlayGraph_isDrawing _ _ (familyPieces_nondeg hr) familyPoints_endsAreCut
    familyPoints_meetsAreCut

theorem pointSet_familySquare (hr : 0 < r) (hj : j ≤ N) :
    Graph.pointSet (familySquare c N r j) segmentDrawing =
      frontier (Plane.closedSquare (c j) r) :=
  pointSet_squareGraph hr.le (squarePieces_subset_familyPieces hj)

/-- A point of a chain link lies on one of that link's squares. -/
theorem exists_mem_frontier_of_mem_pointSet_familyChain {z : Plane}
    (hz : z ∈ Graph.pointSet (familyChain c N m r i) segmentDrawing) :
    ∃ j, i * m ≤ j ∧ j ≤ i * m + m ∧ z ∈ frontier (Plane.closedSquare (c j) r) := by
  obtain ⟨p, hp, hp', hzp⟩ := Graph.IsPlaneChain.mem_pointSet_block hz
  exact ⟨p, hp, hp', pointSet_squareGraph_subset hzp⟩

/-- **Assumed**: the part of a polygonal overlay lying on the boundary of one of its squares is
2-connected.

It is the subdivided boundary of an axis-parallel square — four sides, cut at finitely many
points, each cut point a vertex — so it is a cycle, and `Graph.IsLongCycle.isTwoConnected`
finishes.  What a discharging module must build is the cyclic order of the cut points along the
four sides; `Schoenflies/SegmentOrder.lean` is the tool.  Nothing about the arc, the chain or
the outer face enters the statement. -/
def SquaresTwoConnected : Prop :=
  ∀ (pieces : List Piece) (points : List Plane), (∀ P ∈ pieces, P.Nondeg) →
    EndsAreCut pieces points → MeetsAreCut pieces points →
    ∀ (c : Plane) (r : ℝ), 0 < r → (∀ P ∈ squarePieces c r, P ∈ pieces) →
      (squareGraph pieces points c r).IsTwoConnected

theorem familySquare_isTwoConnected (h2c : SquaresTwoConnected) (hr : 0 < r) (hj : j ≤ N) :
    (familySquare c N r j).IsTwoConnected :=
  h2c _ _ (familyPieces_nondeg hr) familyPoints_endsAreCut familyPoints_meetsAreCut _ r hr
    (squarePieces_subset_familyPieces hj)

/-- Two squares whose centres are within one radius contribute two common vertices to the two
parts of the overlay lying on them.  With equal centres this gives two vertices of one square,
which is how consecutive links of the chain are shown to meet. -/
theorem exists_two_vertices_familySquare (hr : 0 < r) {j j' : ℕ} (hj : j ≤ N) (hj' : j' ≤ N)
    (hd : Plane.supDist (c j) (c j') < r) :
    ∃ a b : Plane, a ≠ b ∧ a ∈ V(familySquare c N r j) ∧ a ∈ V(familySquare c N r j') ∧
      b ∈ V(familySquare c N r j) ∧ b ∈ V(familySquare c N r j') :=
  exists_two_vertices_squareGraph (familyPieces_nondeg hr) familyPoints_meetsAreCut hr hd
    (squarePieces_subset_familyPieces hj) (squarePieces_subset_familyPieces hj')

/-- Each link of the chain is 2-connected: consecutive squares in it share two vertices, so
`lem:union-two-connected` applies all the way along. -/
theorem familyChain_isTwoConnected (h2c : SquaresTwoConnected) (hr : 0 < r)
    (hi : i * m + m ≤ N) (hstep : ∀ q < N, Plane.supDist (c q) (c (q + 1)) < r) :
    (familyChain c N m r i).IsTwoConnected :=
  Graph.chainUnion_isTwoConnected (G := familyOverlay c N r)
    (fun _ _ _ => familySquare_le)
    (fun q _ hq' => familySquare_isTwoConnected h2c hr (by omega))
    fun q _ hq' => exists_two_vertices_familySquare hr (by omega) (by omega)
      (hstep q (by omega))

/-! ## Part 4: the chain satisfies `Graph.IsPlaneChain`

This is the obligation `Schoenflies/OuterChain.lean` flagged: every link must be a subgraph of
**one** ambient plane graph with **one** drawing.  It is discharged by construction — every link
is a `Graph.chainUnion` of `familySquare`s, and every `familySquare` is a `segGraph` on a subset
of the edges of the one overlay `familyOverlay c N r`. -/

/-- **The chain of square boundaries is a plane chain.**

The two geometric hypotheses are the blueprint's: consecutive centres are closer than one square
radius (`hstep`), and centres belonging to nonconsecutive links are more than two radii apart
(`hfar`).  Everything else — one ambient graph, one drawing, finiteness, polygonality — is
discharged by the construction. -/
theorem isPlaneChain_familyChain {n : ℕ} (h2c : SquaresTwoConnected) (hr : 0 < r)
    (hn : 2 ≤ n) (hN : n * m + m ≤ N)
    (hstep : ∀ q < N, Plane.supDist (c q) (c (q + 1)) < r)
    (hfar : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ j', q * m ≤ j' → j' ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c j')) :
    Graph.IsPlaneChain (familyChain c N m r) segmentDrawing (familyOverlay c N r) n := by
  -- Every index the chain uses is one of the `N + 1` centres.
  have hblock : ∀ p ≤ n, p * m + m ≤ N := by
    intro p hp
    have : p * m ≤ n * m := Nat.mul_le_mul_right _ hp
    omega
  refine ⟨hn, fun _ _ => familyChain_le, familyOverlay_isDrawing hr, ?_,
    fun _ _ => familyChain_finite, ?_, ?_, ?_⟩
  · -- Every edge of the overlay is drawn as a straight segment.
    intro g _
    rw [edgeArc_segmentDrawing]
    exact isPolygonal_segment g.1 g.2
  · exact fun p hp => familyChain_isTwoConnected h2c hr (hblock p hp) hstep
  · -- Consecutive links share the square at the sample they have in common.
    intro p hp
    have hpm : (p + 1) * m = p * m + m := by ring
    have hjN : p * m + m ≤ N := hblock p (by omega)
    obtain ⟨a, b, hab, ha, -, hb, -⟩ :=
      exists_two_vertices_familySquare (c := c) hr hjN hjN
        (by rw [Plane.supDist_self]; exact hr)
    -- The shared square is a member of both blocks.
    have hle₁ : familySquare c N r (p * m + m) ≤ familyChain c N m r p :=
      Graph.le_chainUnion (G := familyOverlay c N r) (fun _ _ _ => familySquare_le)
        (by omega) (by omega)
    have hle₂ : familySquare c N r (p * m + m) ≤ familyChain c N m r (p + 1) :=
      Graph.le_chainUnion (G := familyOverlay c N r) (fun _ _ _ => familySquare_le)
        (by omega) (by omega)
    exact ⟨a, b, hab, hle₁.vertexSet_mono ha, hle₂.vertexSet_mono ha,
      hle₁.vertexSet_mono hb, hle₂.vertexSet_mono hb⟩
  · -- Nonconsecutive links are disjoint: a common point would put two far-apart centres within
    -- two radii of each other.
    intro p q hp hq hpq
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨j, hj, hj', hzj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hz
    obtain ⟨k, hk, hk', hzk⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hz'
    rw [Plane.frontier_closedSquare, mem_setOf_eq] at hzj hzk
    have htri := Plane.supDist_triangle (c j) z (c k)
    rw [Plane.supDist_comm (c j) z] at htri
    exact absurd (hfar p q hp hq hpq j hj hj' k hk hk') (by rw [hzj, hzk] at htri; linarith)

/-! ## Part 5: the outer face of the chain

Two plane facts, both general, and then the hypothesis of `lem:outer-chain` on consecutive
pairs. -/

/-- **The outside of a square containing the whole drawing lies in one unbounded face.**
`Graph.beyondSquare_subset_face` is this statement for a square centred at the origin; the
chain argument needs it about a square centred at a sample of the arc, and the connectedness of
the outside of an arbitrary square is `Plane.isConnected_compl_closedSquare`. -/
theorem outer_of_notMem_closedSquare {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {c₀ : Plane} {R : ℝ} (hsub : Graph.pointSet G drawing ⊆ Plane.closedSquare c₀ R)
    {base : Plane} (hbase : base ∉ Plane.closedSquare c₀ R) :
    base ∈ Graph.exterior G drawing ∧ ¬ Bornology.IsBounded (Graph.face G drawing base) := by
  refine ⟨fun h => hbase (hsub h), fun hb => ?_⟩
  have hsub' : (Plane.closedSquare c₀ R)ᶜ ⊆ Graph.face G drawing base :=
    (Plane.isConnected_compl_closedSquare c₀ R).isPreconnected.subset_connectedComponentIn
      hbase (compl_subset_compl.2 hsub)
  exact Plane.not_isBounded_compl_closedSquare c₀ R (hb.subset hsub')

/-- The complement of a square's boundary has the open square as one whole component. -/
theorem connectedComponentIn_compl_frontier_closedSquare {c₀ : Plane} {R : ℝ} {z : Plane}
    (hz : z ∈ Plane.openSquare c₀ R) :
    connectedComponentIn (frontier (Plane.closedSquare c₀ R))ᶜ z = Plane.openSquare c₀ R :=
  Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare c₀ R)
    (Plane.convex_openSquare c₀ R).isPreconnected
    (by rw [Plane.compl_frontier_closedSquare]; exact subset_union_left)
    (by
      rw [eq_empty_iff_forall_notMem]
      exact fun w hw => hw.2 (Plane.frontier_openSquare_subset c₀ R hw.1))
    hz

/-- **"If it lies inside, the boundary cycle of that square separates it from the outer
face."**  A point strictly inside a square whose boundary the drawing carries is not in any
unbounded face: the face would be a connected subset of the complement of that boundary meeting
the inside, hence inside, hence bounded. -/
theorem notMem_face_of_mem_openSquare {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {c₀ : Plane} {R : ℝ} (hfr : frontier (Plane.closedSquare c₀ R) ⊆ Graph.pointSet G drawing)
    {base z : Plane} (hb : ¬ Bornology.IsBounded (Graph.face G drawing base))
    (hz : z ∈ Plane.openSquare c₀ R) : z ∉ Graph.face G drawing base := by
  intro hmem
  have hsub : Graph.face G drawing base ⊆ (frontier (Plane.closedSquare c₀ R))ᶜ :=
    fun w hw hw' => Graph.face_subset_exterior _ _ _ hw (hfr hw')
  have hcomp : Graph.face G drawing base ⊆
      connectedComponentIn (frontier (Plane.closedSquare c₀ R))ᶜ z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hmem hsub
  rw [connectedComponentIn_compl_frontier_closedSquare hz] at hcomp
  exact hb ((Plane.isBounded_closedSquare c₀ R).subset
    (hcomp.trans fun w hw => show Plane.supDist w c₀ ≤ R from le_of_lt hw))

/-- **The hypothesis of `lem:outer-chain` on consecutive pairs.**  Every consecutive pair of
links is contained in one square of radius `R` about the pair's first centre, and `x` is outside
that square. -/
theorem outerOnPairs_familyChain {n : ℕ} {R : ℝ} {x : Plane}
    (hcontain : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) + r ≤ R)
    (hx : ∀ p, p + 1 ≤ n → R < Plane.supDist x (c (p * m))) :
    Graph.OuterOnPairs (familyChain c N m r) segmentDrawing n x := by
  intro p hp
  refine outer_of_notMem_closedSquare (c₀ := c (p * m)) (R := R) ?_ ?_
  · -- Every point of either link is within `r` of one of the centres of the pair.
    intro z hz
    rw [Graph.chainUnion_one, Graph.pointSet_union] at hz
    have key : ∀ i, p ≤ i → i ≤ p + 1 →
        z ∈ Graph.pointSet (familyChain c N m r i) segmentDrawing →
        z ∈ Plane.closedSquare (c (p * m)) R := by
      intro i hi hi' hzi
      obtain ⟨j, hj, hj', hzj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hzi
      rw [Plane.frontier_closedSquare, mem_setOf_eq] at hzj
      have hjlo : p * m ≤ j := le_trans (Nat.mul_le_mul_right _ hi) hj
      have hjhi : j ≤ p * m + m + m := by
        have : i * m ≤ (p + 1) * m := Nat.mul_le_mul_right _ hi'
        have hpm : (p + 1) * m = p * m + m := by ring
        omega
      have htri := Plane.supDist_triangle z (c j) (c (p * m))
      have := hcontain p hp j hjlo hjhi
      exact show Plane.supDist z (c (p * m)) ≤ R by rw [hzj] at htri; linarith
    rcases hz with hz | hz
    · exact key p le_rfl (by omega) hz
    · exact key (p + 1) (by omega) le_rfl hz
  · exact fun hmem => absurd (hx p hp) (not_lt.2 hmem)

/-- **`lem:outer-chain`, applied to the chain of squares.**  Stated with the two halves of the
descent step exactly as `Schoenflies/OuterChain.lean` defines them and for *this* chain, so that
a discharger's terms substitute here with nothing to adapt. -/
theorem outer_face_familyChain {n : ℕ} {x : Plane}
    (hchain : Graph.IsPlaneChain (familyChain c N m r) segmentDrawing (familyOverlay c N r) n)
    (hout : Graph.OuterOnPairs (familyChain c N m r) segmentDrawing n x) :
    x ∈ Graph.exterior (Graph.chainUnion (familyChain c N m r) 0 n) segmentDrawing ∧
      ¬ Bornology.IsBounded
        (Graph.face (Graph.chainUnion (familyChain c N m r) 0 n) segmentDrawing x) :=
  hchain.outer_chain' hout

/-! ## Part 6: from the Euclidean distance to the sup distance

The only place the two metrics have to be compared. `‖·‖ ≤ √2‖·‖∞` and `√2 < 2`, so half the
Euclidean distance is a *strict* lower bound for the sup distance — which is what turns the
blueprint's separation constants into square radii. -/

theorem lt_supDist_of_le_dist {x y : Plane} {t : ℝ} (ht : 0 < t) (h : t ≤ dist x y) :
    t / 2 < Plane.supDist x y := by
  have h2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hle : dist x y ≤ Real.sqrt 2 * Plane.supDist x y := by
    rw [dist_eq_norm]
    exact Plane.norm_le_sqrt_two_mul_supNorm _
  have hsd : 0 < Plane.supDist x y := by nlinarith
  nlinarith

/-- The block of fine samples belonging to one coarse cell lies in that coarse cell. -/
theorem sample_mem_Icc_of_block {K m j p : ℕ} (hm : 0 < m) (h₁ : p * m ≤ j)
    (h₂ : j ≤ (p + 1) * m) : sample (K * m) j ∈ Icc (sample K p) (sample K (p + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [← sample_mul (k := K) (i := p) hm]; exact sample_mono h₁
  · rw [← sample_mul (k := K) (i := p + 1) hm]; exact sample_mono h₂

/-- Every index below `(n+1)·m` belongs to one of the `n + 1` blocks of length `m`. -/
theorem exists_block_index {j m n : ℕ} (hj : j ≤ (n + 1) * m) :
    ∃ i ≤ n, i * m ≤ j ∧ j ≤ i * m + m := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp, by simpa using hj⟩
  | succ n ih =>
    by_cases h : j ≤ (n + 1) * m
    · obtain ⟨i, hi, h₁, h₂⟩ := ih h
      exact ⟨i, Nat.le_succ_of_le hi, h₁, h₂⟩
    · exact ⟨n + 1, le_rfl, (not_le.1 h).le,
        le_trans hj (le_of_eq (by ring))⟩

/-! ## Part 7: `thm:arc-complement`

The blueprint's proof, in its own order.  The two hypotheses `hce` and `hcen` are the two halves
of the descent step of `lem:outer-chain`, quoted verbatim from `Schoenflies/OuterChain.lean`;
`h2c` is the 2-connectivity of one subdivided square, discussed at `SquaresTwoConnected`. -/

/-- **The heart of `thm:arc-complement`**: two points off a simple arc lie in a common open
connected set missing the arc — the outer face of the chain of small squares along the arc. -/
theorem exists_face_of_notMem_arc {A : Set Plane} (hA : IsArc A) (h2c : SquaresTwoConnected)
    {u w : Plane} (hu : u ∉ A) (hw : w ∉ A) :
    ∃ F : Set Plane, IsOpen F ∧ IsConnected F ∧ u ∈ F ∧ w ∈ F ∧ Disjoint F A := by
  obtain ⟨α, hα, hinj, rfl⟩ := hA
  have hAc : IsCompact (α '' I) := isCompact_image_of_subset_I hα subset_rfl isCompact_I.isClosed
  -- **Step 1.** `d > 0` with both points at sup-distance more than `4d` from the arc.
  have hpair : IsCompact ({u, w} : Set Plane) :=
    ((Set.finite_singleton w).insert u).isCompact
  have hdisj : Disjoint ({u, w} : Set Plane) (α '' I) := by
    rw [Set.disjoint_left]
    intro z hz hzA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    exacts [hu hzA, hw hzA]
  obtain ⟨ρ, hρ, hbound⟩ := Plane.exists_dist_pos hpair hAc hdisj
  set d : ℝ := ρ / 8 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hfar4 : ∀ z ∈ ({u, w} : Set Plane), ∀ y ∈ α '' I, 4 * d < Plane.supDist z y := by
    intro z hz y hy
    have hlt := lt_supDist_of_le_dist hρ (hbound z hz y hy)
    rw [hd_def]; linarith
  -- **Step 2.** The coarse partition, into `K = 3·m₁ ≥ 3` cells of diameter less than `d`.
  obtain ⟨m₁, hm₁, hmesh₁⟩ := exists_mesh hα hd 3 (by norm_num)
  obtain ⟨n, hK⟩ : ∃ n, 3 * m₁ = n + 1 := ⟨3 * m₁ - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [hK] at hmesh₁
  -- **Step 3.** `δ = min(d, d')`, the second the separation of nonadjacent coarse subarcs.
  obtain ⟨ρ', hρ', hsep⟩ := exists_pos_dist_nonadjacent hα hinj (n := n + 1)
  set δ : ℝ := min d ρ' with hδ_def
  have hδ : 0 < δ := lt_min hd hρ'
  have hδd : δ ≤ d := min_le_left _ _
  have hδρ : δ ≤ ρ' := min_le_right _ _
  -- **Step 4.** The fine partition, refining the coarse one, of mesh less than `δ/4`.
  obtain ⟨m, hm, hmesh₂⟩ := exists_mesh hα (by linarith : (0 : ℝ) < δ / 4) (n + 1) (by omega)
  -- **Step 5.** The squares of radius `δ/4` about the fine samples, overlaid all at once.
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Plane, ∀ j, c j = α (sample ((n + 1) * m) j) := ⟨_, fun _ => rfl⟩
  set r : ℝ := δ / 4 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  -- Consecutive centres are closer than one radius.
  have hstep : ∀ q < (n + 1) * m, Plane.supDist (c q) (c (q + 1)) < r := by
    intro q hq
    have hmem : sample ((n + 1) * m) (q + 1) ∈
        Icc (sample ((n + 1) * m) q) (sample ((n + 1) * m) (q + 1)) :=
      ⟨sample_mono (Nat.le_succ q), le_rfl⟩
    have hlt := hmesh₂ q hq _ hmem
    rw [Plane.supDist_comm, hc, hc]
    exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
  -- A fine sample of the `p`-th block lies on the `p`-th coarse subarc.
  have hcell : ∀ p j, p * m ≤ j → j ≤ p * m + m → c j ∈ subarcCell α (n + 1) p := by
    intro p j h₁ h₂
    refine ⟨sample ((n + 1) * m) j, sample_mem_Icc_of_block hm h₁ ?_, (hc j).symm⟩
    calc j ≤ p * m + m := h₂
      _ = (p + 1) * m := by ring
  -- Centres of nonconsecutive links are more than two radii apart.
  have hfarblock : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ j', q * m ≤ j' → j' ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c j') := by
    intro p q hp hq hpq j hj hj' k hk hk'
    have hdist := hsep p (by omega) q (by omega) (by omega) _ (hcell p j hj hj')
      _ (hcell q k hk hk')
    have hlt := lt_supDist_of_le_dist hρ' hdist
    rw [hr_def]; linarith
  -- **Step 6.** The chain is a plane chain.
  have hchain := isPlaneChain_familyChain (c := c) (N := (n + 1) * m) (m := m) (r := r) (n := n)
    h2c hr hn (le_of_eq (by ring)) hstep hfarblock
  -- **Step 7.** Each consecutive pair sits in the square of radius `3d` about its first centre.
  have hcpm : ∀ p, c (p * m) = α (sample (n + 1) p) := fun p => by
    rw [hc, sample_mul (k := n + 1) hm]
  have hnear : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) < 2 * d := by
    intro p hp j h₁ h₂
    -- Membership of a fine sample in a coarse cell, as a distance bound from its base point.
    have base : ∀ q, q < n + 1 → ∀ k, q * m ≤ k → k ≤ q * m + m →
        Plane.supDist (c k) (α (sample (n + 1) q)) < d := by
      intro q hq k hk hk'
      have hmem : sample ((n + 1) * m) k ∈ Icc (sample (n + 1) q) (sample (n + 1) (q + 1)) :=
        sample_mem_Icc_of_block hm hk (by calc k ≤ q * m + m := hk'
          _ = (q + 1) * m := by ring)
      have hlt := hmesh₁ q hq _ hmem
      rw [hc]
      exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
    by_cases hcase : j ≤ p * m + m
    · have := base p (by omega) j h₁ hcase
      rw [hcpm]; linarith
    · -- `j` is in the next block: go through the shared sample `α(t_{p+1})`.
      have h₁' : (p + 1) * m ≤ j := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have h₂' : j ≤ (p + 1) * m + m := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have hA' := base (p + 1) (by omega) j h₁' h₂'
      -- The two consecutive coarse samples are themselves within `d`.
      have hB' : Plane.supDist (α (sample (n + 1) (p + 1))) (α (sample (n + 1) p)) < d := by
        have hmem : sample (n + 1) (p + 1) ∈
            Icc (sample (n + 1) p) (sample (n + 1) (p + 1)) :=
          ⟨sample_mono (Nat.le_succ p), le_rfl⟩
        exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) (hmesh₁ p (by omega) _ hmem)
      have htri := Plane.supDist_triangle (c j) (α (sample (n + 1) (p + 1))) (c (p * m))
      rw [hcpm] at htri ⊢
      linarith
  have hcontain : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) + r ≤ 3 * d := by
    intro p hp j h₁ h₂
    have := hnear p hp j h₁ h₂
    rw [hr_def]; linarith
  have hxfar : ∀ z ∈ ({u, w} : Set Plane), ∀ p, p + 1 ≤ n →
      3 * d < Plane.supDist z (c (p * m)) := by
    intro z hz p hp
    have hmemA : c (p * m) ∈ α '' I :=
      ⟨sample (n + 1) p, sample_mem_I (by omega), (hcpm p).symm⟩
    have := hfar4 z hz _ hmemA
    linarith
  -- **Step 8.** `lem:outer-chain`.
  have hmemu : u ∈ ({u, w} : Set Plane) := Or.inl rfl
  have hmemw : w ∈ ({u, w} : Set Plane) := Or.inr rfl
  have houtu := outer_face_familyChain hchain
    (outerOnPairs_familyChain hcontain (hxfar u hmemu))
  have houtw := outer_face_familyChain hchain
    (outerOnPairs_familyChain hcontain (hxfar w hmemw))
  haveI : (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n).Finite :=
    hchain.block_finite (i := 0) (m := n) (by omega)
  have hdraw : Graph.IsDrawing (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n)
      segmentDrawing := hchain.block_isDrawing (by omega)
  have hface := Graph.unbounded_face_unique hdraw houtw.2 houtu.2
  -- **Step 9.** The outer face misses the arc.
  have hmiss : Disjoint (Graph.face (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n)
      segmentDrawing u) (α '' I) := by
    rw [Set.disjoint_right]
    intro z hz hzF
    obtain ⟨j, hjr, hzj⟩ := Set.mem_iUnion₂.1
      (image_subset_iUnion_closedSquare (α := α) (n := (n + 1) * m) (by positivity) hmesh₂ hz)
    rw [Finset.mem_range] at hjr
    -- The `j`-th square belongs to one link of the chain, hence to the whole chain.
    obtain ⟨i, hi, h₁, h₂⟩ := exists_block_index (j := j) (n := n) (m := m) (by omega)
    have hle₁ : familySquare c ((n + 1) * m) r j ≤ familyChain c ((n + 1) * m) m r i :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familySquare_le) h₁ h₂
    have hle₂ : familyChain c ((n + 1) * m) m r i ≤
        Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familyChain_le) (Nat.zero_le _) (by omega)
    have hfrsub : frontier (Plane.closedSquare (c j) r) ⊆
        Graph.pointSet (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n) segmentDrawing := by
      rw [← pointSet_familySquare (c := c) hr (le_of_lt hjr)]
      exact Graph.pointSet_mono (hle₁.trans hle₂)
    have hzj' : Plane.supDist z (c j) ≤ r := by rw [hc]; exact hzj
    rcases lt_or_eq_of_le hzj' with hlt | heq
    · exact notMem_face_of_mem_openSquare hfrsub houtu.2 hlt hzF
    · exact (Graph.face_subset_exterior _ _ _ hzF)
        (hfrsub (by rw [Plane.frontier_closedSquare]; exact heq))
  exact ⟨_, hdraw.isOpen_face u, Graph.isConnected_face houtu.1, Graph.mem_face houtu.1,
    hface ▸ Graph.mem_face houtw.1, hmiss⟩

/-- **`thm:arc-complement`.**  The complement of a simple arc in the plane is connected. -/
theorem isConnected_compl_arc {A : Set Plane} (hA : IsArc A) (h2c : SquaresTwoConnected) :
    IsConnected Aᶜ := by
  refine ⟨?_, isPreconnected_of_forall_pair fun z hz y hy => ?_⟩
  · -- An arc is compact, so it misses the outside of a large square.
    obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hA.isCompact.isBounded
    obtain ⟨t, ht⟩ := (Plane.isConnected_beyondSquare s).nonempty
    rw [Plane.beyondSquare_eq_compl] at ht
    exact ⟨t, fun htA => ht (hs htA)⟩
  · obtain ⟨F, -, hFconn, hzF, hyF, hFA⟩ := exists_face_of_notMem_arc hA h2c hz hy
    exact ⟨F, fun v hv => Set.disjoint_left.1 hFA hv, hzF, hyF, hFconn.isPreconnected⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneralCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The crosscut theorem for a general Jordan curve

`P` is a simple polygonal arc with distinct endpoints `p, q` on a Jordan curve `C` and all its
remaining points in `D = Int(C)`; `A₁, A₂` are the two arcs of `C` from `p` to `q`. Then
`D ∖ P` has exactly two components, namely `Int(A₁ ∪ P)` and `Int(A₂ ∪ P)`, and consequently
`ℝ² ∖ (C ∪ P)` has precisely three regions, with boundaries `C`, `A₁ ∪ P`, `A₂ ∪ P`.

The proof is short because both halves already exist. `Schoenflies.crosscut_cells` exhibits two
distinct components of `D ∖ P`; `Schoenflies.crosscut_components_exhaust` says there are no
others; and the final paragraph is `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`
applied three times. All this module does is fit the pieces together and name the result.

## The two sides are named by their arcs, and they are `inside (Aᵢ ∪ P)`

Everything Part II asks of this theorem is asked of *one labelled side*:
`lem:crosscut-side-correspondence` wants "the component whose closure meets `C` in `Aᵢ`" as a
function of `i`, and `prop:initial-pair`, `lem:cellulation-invariants` and `thm:finite-transfer`
all consume the labelled form. So there is no existential anywhere in the conclusions below: the
side belonging to the arc `A` is literally `Schoenflies.inside (A ∪ P)`, which is already a
function of `A`, carries the whole `inside`/`IsSeparating` API, and is exactly the set the
blueprint writes `Int(A ∪ P)`. The labelling lemma is `IsCrosscut.closure_side_inter`:

    closure (inside (A₁ ∪ P)) ∩ C = A₁.

Each statement is proved for `A₁` only; `IsCutPair.symm` swaps the two arcs, so
`h.foo hjordan hcut.symm` is the `A₂` instance of `h.foo hjordan hcut`. That is why no lemma
below mentions `A₂` in its conclusion.

## What is assumed

Two hypotheses are threaded through, both of which are being discharged elsewhere right now:

* `hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S` — `thm:jordan`. Only the
  separation clause is used; the boundary clause is part of `Schoenflies.IsSeparating`, so no
  second hypothesis is needed.
* `hcollars : HasArcCollars (inside C) P` — blueprint Lemma 1.8 (b) for the arc `P` inside the
  Jordan domain, the standing hypothesis of `Schoenflies/CrosscutAtMostTwo.lean`.

Neither is a restatement of anything proved here.

## Blueprint

* `Schoenflies.IsCrosscut` — the hypotheses of `thm:general-crosscut` on `C, P, p, q`.
* `Schoenflies.IsCutPair` — "`A₁, A₂` the two arcs of `C` from `p` to `q`, as in
  `lem:jordan-circle`"; `Schoenflies.exists_isCutPair` produces one from
  `IsJordanCurve.two_arcs`.
* `Schoenflies.IsCrosscut.side_subset`, `.side_isComponent`, `.closure_side_inter`,
  `.side_ne`, `.disjoint_sides`, `.components_eq`, `.inside_diff_eq` — the first half of
  `thm:general-crosscut`, one labelled side at a time, and then the exhaustion. The side's own
  topology comes with it: `.isOpen_side`, `.isConnected_side`, `.isBounded_side`,
  `.side_nonempty`, `.frontier_side`, `.closure_side`.
* `Schoenflies.general_crosscut` — `thm:general-crosscut`, first sentence, bundled.
* `Schoenflies.IsCrosscut.compl_eq`, `.compl_eq_three`, `.outside_isComponent`,
  `.side_isComponent_compl`, `.three_regions` — the "consequently" sentence.
* `Schoenflies.general_crosscut_three_regions` — `thm:general-crosscut`, second sentence,
  bundled, with the three boundaries.
* `Schoenflies.IsArcBetween.not_subset_pair` — an arc is more than its two endpoints; general,
  and the only new fact about arcs this module needs.
-/

open Bornology Set unitInterval

namespace Schoenflies

variable {C P A A₁ A₂ : Set Plane} {p q z : Plane}

/-! ### An arc is more than its two endpoints

This is what `Schoenflies.arcs_ne` needs in order to conclude `A₁ ≠ A₂` from the fact that the
two arcs meet only at `p` and `q`. It is a general fact about arcs and belongs in
`Schoenflies/Curve.lean`; it is here because nothing on `main` states it. -/

/-! ### The configuration

Two bundles of hypotheses. `IsCrosscut C P p q` is the blueprint's "`P` is a simple polygonal
arc with distinct endpoints `p, q ∈ C` and all other points in `D = Int(C)`"; distinctness of
`p` and `q` is *not* a field, since an arc between two points always has them distinct.
`IsCutPair C p q A₁ A₂` is "`A₁, A₂` are the two arcs of `C` from `p` to `q`". The two are kept
apart because the arcs are a *choice* — swapping them is a symmetry of the whole theorem, and
`IsCutPair.symm` is what makes every statement below need proving only once. -/

/-! ### Elementary consequences of the configuration

Nothing here needs `thm:jordan`: these are the set-theoretic facts that turn "the crosscut runs
inside the curve" into the hypotheses `Schoenflies.crosscut_cells` takes. -/

namespace IsCrosscut

/-! ### The two separating curves, and where the outside of `C` sits

This is the paragraph of the blueprint proof that pins the roles of `Wᵢ` and `Vᵢ`:
`Ω† = Ext(C)` is connected, unbounded and disjoint from `Jᵢ`, hence lies in `Ext(Jᵢ)`. -/

/-! ### The first half: `Int(A₁ ∪ P)` is a component of `Int(C) ∖ P` with closure meeting `C`
in `A₁`

Three applications of `Schoenflies.crosscut_cells`, one clause each. Everything is stated for the
arc `A₁`; `IsCutPair.symm` supplies the `A₂` instance. -/

/-! ### The second half: there are no other components

`Schoenflies.crosscut_components_exhaust` applied to the two sides, which the previous section
has just shown to be distinct components. -/

/-- **Every component of `Int(C) ∖ P` is one of the two sides.** This is the "at most two"
half, `lem:crosscut-at-most-two`, applied to the two components `lem:crosscut-cells` produced. -/
theorem components_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    ∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
      connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  obtain ⟨v₁, hv₁⟩ := h.side_nonempty hjordan hcut
  obtain ⟨v₂, hv₂⟩ := h.side_nonempty hjordan hcut.symm
  have hc₁ := h.side_isComponent hjordan hcut v₁ hv₁
  have hc₂ := h.side_isComponent hjordan hcut.symm v₂ hv₂
  have hexh := crosscut_components_exhaust hsep.isOpen_inside
    hsep.isConnected_inside.isPreconnected h.arc h.polygonal
    h.left_notMem_inside h.right_notMem_inside h.sdiff_subset hcollars
    (h.side_subset hjordan hcut hv₁) (h.side_subset hjordan hcut.symm hv₂)
    (by rw [hc₁, hc₂]; exact h.side_ne hjordan hcut)
  intro z hz
  rcases hexh z hz with hzz | hzz
  · rw [hc₁] at hzz
    exact Or.inl (h.side_isComponent hjordan hcut z hzz)
  · rw [hc₂] at hzz
    exact Or.inr (h.side_isComponent hjordan hcut.symm z hzz)

/-- **`Int(C) ∖ P` is the disjoint union of the two sides.** -/
theorem inside_diff_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
  refine Subset.antisymm (fun z hz => ?_)
    (union_subset (h.side_subset hjordan hcut) (h.side_subset hjordan hcut.symm))
  rcases h.components_eq hjordan hcut hcollars z hz with heq | heq
  · exact Or.inl (heq ▸ mem_connectedComponentIn hz)
  · exact Or.inr (heq ▸ mem_connectedComponentIn hz)

end IsCrosscut

/-! ### The three regions of `ℝ² ∖ (C ∪ P)`

The blueprint's final paragraph. `P` misses `Ext(C)`, so the complement of `C ∪ P` splits as
`Ext(C) ⊔ (Int(C) ∖ P)`; the first half has just split the second summand in two; and each of
the three pieces is a component of the whole because its boundary misses it
(`lem:clopen-component`, here `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`). -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Generated matched cell structures

The spine of Part II. `def:generated-structure` says that every cell structure the Schönflies
construction ever meets is obtained from the initial two-face structure of
`prop:initial-pair` by a finite sequence of two elementary operations — *edge subdivision* and
*2-cell splitting by an ear* — performed simultaneously in the two realizations. This module
builds the two operations as `def`s on `Schoenflies.CellStructure`, closes them into the
inductive `Schoenflies.GeneratedStructure`, and proves the assertions of
`lem:cellulation-invariants` that are within reach.

## Blueprint

* `Schoenflies.CellStructure.SubdivData`, `Schoenflies.CellStructure.subdivideEdge` — the first
  elementary operation of `def:generated-structure` (tex, operation 1).
* `Schoenflies.CellStructure.SplitData`, `Schoenflies.CellStructure.splitFace` — the second
  (tex, operation 2).
* `Schoenflies.GeneratedStructure` — `def:generated-structure`, as the inductive closure of a
  base structure under the two operations.
* `Schoenflies.CellStructure.SubdivData.parent`,
  `Schoenflies.CellStructure.SplitData.parent`,
  `Schoenflies.CellStructure.SubdivData.sub_parent`,
  `Schoenflies.CellStructure.SplitData.sub_parent` — assertion (iv) of
  `lem:cellulation-invariants`, the parent map of one elementary refinement and the
  compatibility `σ ≼ τ → par σ ≼ par τ`.
* `Schoenflies.CellStructure.CombInvariants`, its two preservation theorems
  `Schoenflies.CellStructure.SubdivData.combInvariants` and
  `Schoenflies.CellStructure.SplitData.combInvariants`, and
  `Schoenflies.GeneratedStructure.combInvariants`, which closes the induction — assertions
  (iii), (v), (vi), together with the abstract form of (viii) and the bookkeeping facts about
  `≼_abs` that the blueprint uses silently.
* `Schoenflies.GeneratedStructure.trans` — refinement sequences compose.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition` — assertion (i) for one
  realization, and from it, with no further geometry:
  `.frontier_property` (assertion (ii)), `.sub_iff_subset_closure` and
  `Schoenflies.CellStructure.subset_closure_congr` (assertion (ix)), and `.face_eq`
  (assertion (viii)).
* `Schoenflies.CellStructure.SubdivData.IsRefinement` and
  `Schoenflies.CellStructure.SubdivData.IsRefinement.isCellDecomposition` — the induction step
  of assertion (i) over the *first* constructor: a realization of the subdivided structure that
  refines a realization of the old one inherits (i).
* `Schoenflies.crosscut_cell_partition` — the geometric content of one 2-cell split, from
  `Schoenflies.general_crosscut`, in the shape assertion (i) consumes.

**Not here.** The induction step of (i) over the *second* constructor, and assertion (vii) in
either. `crosscut_cell_partition` is the geometric input the split step needs; what is missing
is the `SplitData` analogue of `IsRefinement` — a relation between a realization of
`S.splitFace d` and one of `S`, saying that the ear is drawn as a crosscut of the realized open
2-cell — and the identification of the abstract boundary walk of a 2-cell with the Jordan curve
of assertion (vii). Assertions (ii), (viii) and (ix) are stated here against `(i)` as a
hypothesis, so later constructors can use the resulting theorem directly.

Two general graph facts are proved here for want of a home: `Schoenflies.subdivGraph` (with
`Schoenflies.subdivGraph_mono` and `Schoenflies.subdivGraph_eq_self`) and
`Schoenflies.isLink_of_le_of_mem_edgeSet`. The second belongs in `Schoenflies/Graph/`; nothing
on `main` states it.

## Design

**The base case is a parameter.** `prop:initial-pair` is being built elsewhere, so
`GeneratedStructure S₀ S` is relative to an arbitrary base `S₀`, and every invariant theorem
reads "the invariants of `S₀` propagate to `S`". That is both cleaner and independent of the
initial pair's schedule: the consumer supplies `S₀` and the base case, and gets the invariant
at every stage.

**`rem:intermediate-disconnection` is honoured by omission.** Nothing in this module mentions
`Realization.nonboundary`, let alone its connectedness: an intermediate stage really can have
disconnected open nonboundary part, and every statement here is proved without that hypothesis.

**`≼_abs` stays a raw datum.** `CellStructure.sub` is not made a preorder. The reflexivity and
transitivity facts that the blueprint uses are fields of `CombInvariants`, established for the
base and propagated, never assumed of an arbitrary `CellStructure`.

**Fidelity note on reflexivity.** The blueprint's two update lists (tex, operations 1 and 2)
do not mention the reflexive pairs of the *new* cells, while the base relation is declared to
contain "the reflexive pairs". Assertion (i) forces them: the closure of a new open cell
contains that cell, and (i) says a closed cell is the union of its open subcells. Both `subRel`
definitions below therefore declare `σ ≼ σ` for every new cell; that is the only place where
this module adds a pair the blueprint's prose does not list.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

variable {γ : Type*}

/-! ### Subdividing an edge of a graph

The graph-theoretic half of the first elementary operation, stated for an arbitrary graph so
that one definition serves both the skeleton and the outer cycle: when `H` does not carry `e`
from `x` to `y` — which is the case for the outer cycle whenever the subdivided edge is not an
outer edge — the construction leaves `H` alone (`subdivGraph_eq_self`). Without that, the
definition of `CellStructure.subdivideEdge` would need a case split on whether the subdivided
edge is outer, and every lemma about it would inherit the split. -/

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

/-! ### The cells of an abstract structure -/

namespace CellStructure

variable (S : CellStructure γ)

variable {S}

theorem pathCells_subset_cells {u : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    S.pathCells u W ⊆ S.cells := by
  rintro z (hz | hz)
  · exact S.mem_cells_of_mem_edgeSet (h.edge_mem hz)
  · exact S.mem_cells_of_mem_vertexSet (h.walkVertices_subset hz)

/-! ### Elementary operation 1: edge subdivision

Blueprint, `def:generated-structure`, operation 1: "the edge `e` is replaced by a new vertex
`v` and two new edges `e₁, e₂`, whose endpoints are `v` together with one old endpoint of `e`
each; the relation `≼_abs` is extended by declaring `v ≼ e₁` and `v ≼ e₂`, each old endpoint of
`e` a subcell of its adjacent new edge, and `v, e₁, e₂` subcells of exactly the old strict
supercells of `e`; all pairs not involving `e` are unchanged." -/

variable {S : CellStructure γ} (d : S.SubdivData)

/-! ### Elementary operation 2: splitting a 2-cell by an ear

Blueprint, `def:generated-structure`, operation 2: "the 2-cell `R` is replaced by `R₁, R₂`; the
new interior vertices and edges of the ear `P` are added with their incidences along `P` (each
interior vertex a subcell of its two adjacent ear edges, each ear endpoint a subcell of its
adjacent ear edge); the relation `≼_abs` is extended by declaring every cell of the boundary
walk of `Rᵢ`, together with every cell of `P`, a subcell of `Rᵢ`, for `i = 1, 2`; no 2-cell is
declared a subcell of another, and all pairs not involving `R` or the new cells are unchanged."

The ear enters as a *graph* `ear` together with `Graph.IsPathGraph`, rather than as a bare list
of names: the incidences "along `P`" are then `ear.Inc`, and the union `S.skel.union ear` is
the new skeleton with no further bookkeeping. -/

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

/-- **The two boundary paths share no edge**, recovered from `paths_meet`: a common edge would
lie in the intersection, hence be one of the two ends, which are 0-cells. -/
theorem paths_disjoint ⦃f : γ⦄ (h₁ : f ∈ d.path₁) (h₂ : f ∈ d.path₂) : False := by
  have hmem : f ∈ S.pathCells d.source d.path₁ ∩ S.pathCells d.source d.path₂ :=
    ⟨Or.inl h₁, Or.inl h₂⟩
  rw [d.paths_meet] at hmem
  have hfE : f ∈ E(S.skel) := d.isPath₁.isWalk.edge_mem h₁
  rcases hmem with rfl | rfl
  exacts [S.disjoint_vertexSet_edgeSet.ne_of_mem d.isPath₁.left_mem hfE rfl,
    S.disjoint_vertexSet_edgeSet.ne_of_mem d.isPath₁.right_mem hfE rfl]

theorem source_mem_cells : d.source ∈ S.cells := S.mem_cells_of_mem_vertexSet d.source_mem_skel

theorem target_mem_cells : d.target ∈ S.cells := S.mem_cells_of_mem_vertexSet d.target_mem_skel

theorem face_mem_cells : d.face ∈ S.cells := S.mem_cells_of_mem_faces d.face_mem

theorem cells₁_subset : d.cells₁ ⊆ S.cells := pathCells_subset_cells d.isPath₁.isWalk

theorem cells₂_subset : d.cells₂ ⊆ S.cells := pathCells_subset_cells d.isPath₂.isWalk

variable {d}

theorem notMem_cells_of_mem_newCells {z : γ} (h : z ∈ d.newCells) : z ∉ S.cells := by
  rcases h with (⟨hz, hz'⟩ | hz) | hz
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
    push Not at hz'
    exact d.vertex_fresh hz hz'.1 hz'.2
  · exact d.edge_fresh hz
  · rcases hz with rfl | rfl
    exacts [d.face₁_notMem, d.face₂_notMem]

theorem notMem_newCells_of_mem_cells {z : γ} (h : z ∈ S.cells) : z ∉ d.newCells := fun hz =>
  notMem_cells_of_mem_newCells hz h

variable (d)

theorem face₁_mem_newCells : d.face₁ ∈ d.newCells := Or.inr (Or.inl rfl)

theorem face₂_mem_newCells : d.face₂ ∈ d.newCells := Or.inr (Or.inr rfl)

theorem compatible : S.skel.Compatible d.ear :=
  Graph.Compatible.of_disjoint_edgeSet d.disjoint_edgeSet

theorem ear_le_skeleton : d.ear ≤ d.skeleton := d.compatible.right_le_union

end SplitData

variable {S : CellStructure γ} (c : S.SplitData)

/-- The cells after a split: the old ones except the split 2-cell, plus the ear's cells and the
two new 2-cells. (The ear's two ends are old cells and appear on both sides.) -/
theorem splitFace_cells : (S.splitFace c).cells = (S.cells \ {c.face}) ∪ c.newCells := by
  ext z
  simp only [cells, splitFace_skel, splitFace_faces, c.skeleton_vertexSet, c.skeleton_edgeSet,
    SplitData.newCells, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ((hz | hz) | hz)
    · rcases hz with hz | hz
      · exact Or.inl ⟨S.mem_cells_of_mem_vertexSet hz,
          fun h => S.faces_ne_vertexSet c.face_mem hz h.symm⟩
      · by_cases hcell : z ∈ S.cells
        · rcases c.mem_cells_of_mem_ear_vertexSet hz hcell with rfl | rfl
          · exact Or.inl ⟨c.source_mem_cells,
              fun h => S.faces_ne_vertexSet c.face_mem c.source_mem_skel h.symm⟩
          · exact Or.inl ⟨c.target_mem_cells,
              fun h => S.faces_ne_vertexSet c.face_mem c.target_mem_skel h.symm⟩
        · refine Or.inr (Or.inl (Or.inl ⟨hz, ?_⟩))
          rintro (rfl | rfl)
          exacts [hcell c.source_mem_cells, hcell c.target_mem_cells]
    · rcases hz with hz | hz
      · exact Or.inl ⟨S.mem_cells_of_mem_edgeSet hz,
          fun h => S.faces_ne_edgeSet c.face_mem hz h.symm⟩
      · exact Or.inr (Or.inl (Or.inr hz))
    · rcases hz with rfl | rfl | ⟨hz, hz'⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl ⟨S.mem_cells_of_mem_faces hz, hz'⟩
  · rintro (⟨hz, hz'⟩ | ((⟨hz, -⟩ | hz) | (rfl | rfl)))
    · rcases hz with (hz | hz) | hz
      · exact Or.inl (Or.inl (Or.inl hz))
      · exact Or.inl (Or.inr (Or.inl hz))
      · exact Or.inr (Or.inr (Or.inr ⟨hz, hz'⟩))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inl (Or.inr (Or.inr hz))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

end CellStructure

/-! ### Generated matched cell structures -/

namespace CellStructure

/-! ### The combinatorial invariants

Assertions (iii), (v) and (vi) of `lem:cellulation-invariants`, together with the abstract form
of (viii) and the bookkeeping facts about `≼_abs` that the blueprint's proof uses without
comment (the relation relates cells to cells, it is reflexive, and a vertex is below each edge
it bounds). They are bundled because the induction propagates them together: the preservation
proof of each one reads the others at the previous stage. -/

/-! ### Edge subdivision preserves the combinatorial invariants -/

/-! ### A 2-cell split preserves the combinatorial invariants -/

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

theorem source_mem_cells₁ : d.source ∈ d.cells₁ := Or.inr Graph.mem_walkVertices_self

theorem target_mem_cells₁ : d.target ∈ d.cells₁ := Or.inr d.isPath₁.target_mem_walkVertices

theorem cells₁_ne_face {σ : γ} (h : σ ∈ d.cells₁) : σ ≠ d.face := by
  rcases h with h | h
  · exact fun heq => S.faces_ne_edgeSet d.face_mem (d.isPath₁.edge_mem h) heq.symm
  · exact fun heq =>
      S.faces_ne_vertexSet d.face_mem (d.isPath₁.isWalk.walkVertices_subset h) heq.symm

theorem cells₂_ne_face {σ : γ} (h : σ ∈ d.cells₂) : σ ≠ d.face := by
  rcases h with h | h
  · exact fun heq => S.faces_ne_edgeSet d.face_mem (d.isPath₂.edge_mem h) heq.symm
  · exact fun heq =>
      S.faces_ne_vertexSet d.face_mem (d.isPath₂.isWalk.walkVertices_subset h) heq.symm

theorem notMem_faces_of_mem_cells₁ {σ : γ} (h : σ ∈ d.cells₁) (hσ : σ ∈ S.faces) : False := by
  rcases h with h | h
  · exact S.faces_ne_edgeSet hσ (d.isPath₁.edge_mem h) rfl
  · exact S.faces_ne_vertexSet hσ (d.isPath₁.isWalk.walkVertices_subset h) rfl

theorem notMem_faces_of_mem_cells₂ {σ : γ} (h : σ ∈ d.cells₂) (hσ : σ ∈ S.faces) : False := by
  rcases h with h | h
  · exact S.faces_ne_edgeSet hσ (d.isPath₂.edge_mem h) rfl
  · exact S.faces_ne_vertexSet hσ (d.isPath₂.isWalk.walkVertices_subset h) rfl

/-- An edge of the skeleton belongs to the cells of a boundary path exactly when it is one of
that path's edges — a vertex of the walk cannot be an edge name. -/
theorem edge_mem_cells₁_iff {f : γ} (hf : f ∈ E(S.skel)) : f ∈ d.cells₁ ↔ f ∈ d.path₁ := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | h
  · exact h
  · exact absurd rfl (S.vertexSet_ne_edgeSet (d.isPath₁.isWalk.walkVertices_subset h) hf)

theorem edge_mem_cells₂_iff {f : γ} (hf : f ∈ E(S.skel)) : f ∈ d.cells₂ ↔ f ∈ d.path₂ := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | h
  · exact h
  · exact absurd rfl (S.vertexSet_ne_edgeSet (d.isPath₂.isWalk.walkVertices_subset h) hf)

/-- The ear has at least one edge: its two ends are distinct, so its walk is not empty. -/
theorem exists_ear_edge : ∃ f, f ∈ E(d.ear) := by
  rcases hw : d.earWalk with _ | ⟨f, rest⟩
  · exfalso
    have hmem := d.isPathGraph.target_mem
    rw [d.isPathGraph.vertexSet_eq, hw, Graph.walkVertices_nil, Set.mem_singleton_iff] at hmem
    exact d.source_ne_target hmem.symm
  · exact ⟨f, d.isPathGraph.mem_edgeSet (by rw [hw]; exact List.mem_cons_self ..)⟩

theorem subRel_of_old {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.face) (hτ : τ ≠ d.face) (h : S.sub σ τ) : d.subRel σ τ :=
  Or.inl ⟨notMem_newCells_of_mem_cells hσc, notMem_newCells_of_mem_cells hτc, hσ, hτ, h⟩

/-- On old cells other than the split 2-cell, the relation is unchanged: "all pairs not
involving `R` or the new cells are unchanged". -/
theorem old_subRel_iff {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.face) (hτ : τ ≠ d.face) : d.subRel σ τ ↔ S.sub σ τ := by
  refine ⟨fun h => ?_, d.subRel_of_old hσc hτc hσ hτ⟩
  rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hσc (notMem_cells_of_mem_newCells h)
  · exact absurd hτc (d.edge_fresh h.edge_mem)
  · exact absurd (h ▸ hτc) d.face₁_notMem
  · exact absurd (h ▸ hτc) d.face₂_notMem

/-- The cells below the first new 2-cell are exactly the ear's cells, the first boundary path's
cells, and itself. -/
theorem subRel_face₁_iff {σ : γ} :
    d.subRel σ d.face₁ ↔ (σ = d.face₁ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₁) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))⟩
  rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | h | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd d.face₁_mem_newCells h
  · exact Or.inl h
  · exact absurd h.edge_mem fun hh => d.face₁_notMem_ear (Or.inr hh)
  · exact h
  · exact absurd h d.face_ne

theorem subRel_face₂_iff {σ : γ} :
    d.subRel σ d.face₂ ↔ (σ = d.face₂ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₂) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))⟩
  rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd d.face₂_mem_newCells h
  · exact Or.inl h
  · exact absurd h.edge_mem fun hh => d.face₂_notMem_ear (Or.inr hh)
  · exact absurd h.symm d.face_ne
  · exact h

theorem mem_splitFace_cells_of_old {z : γ} (hz : z ∈ S.cells) (hzf : z ≠ d.face) :
    z ∈ (S.splitFace d).cells := by
  rw [splitFace_cells]; exact Or.inl ⟨hz, hzf⟩

theorem mem_splitFace_cells_of_new {z : γ} (hz : z ∈ d.newCells) :
    z ∈ (S.splitFace d).cells := by
  rw [splitFace_cells]; exact Or.inr hz

theorem mem_splitFace_cells_of_ear {z : γ} (hz : z ∈ d.earCells) :
    z ∈ (S.splitFace d).cells := by
  rcases hz with hz | hz
  · by_cases hc : z ∈ S.cells
    · rcases d.mem_cells_of_mem_ear_vertexSet hz hc with rfl | rfl
      · exact d.mem_splitFace_cells_of_old hc fun h =>
          S.faces_ne_vertexSet d.face_mem d.source_mem_skel h.symm
      · exact d.mem_splitFace_cells_of_old hc fun h =>
          S.faces_ne_vertexSet d.face_mem d.target_mem_skel h.symm
    · refine d.mem_splitFace_cells_of_new (Or.inl (Or.inl ⟨hz, ?_⟩))
      rintro (rfl | rfl)
      exacts [hc d.source_mem_cells, hc d.target_mem_cells]
  · exact d.mem_splitFace_cells_of_new (Or.inl (Or.inr hz))

/-- **A 2-cell split preserves the combinatorial invariants**: the induction step of assertions
(iii), (v), (vi) — and of abstract (viii) — over the second constructor. -/
theorem combInvariants (hS : S.CombInvariants) : (S.splitFace d).CombInvariants where
  sub_mem_left := by
    rintro σ τ (⟨-, -, hσ, -, h⟩ | ⟨-, h⟩ | h | ⟨-, h⟩ | ⟨-, h⟩)
    · exact d.mem_splitFace_cells_of_old (hS.sub_mem_left h) hσ
    · exact d.mem_splitFace_cells_of_new h
    · exact d.mem_splitFace_cells_of_ear (Or.inl h.vertex_mem)
    · rcases h with rfl | h | h
      · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₁_subset h) (d.cells₁_ne_face h)
    · rcases h with rfl | h | h
      · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₂_subset h) (d.cells₂_ne_face h)
  sub_mem_right := by
    rintro σ τ (⟨-, -, -, hτ, h⟩ | ⟨rfl, h⟩ | h | ⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact d.mem_splitFace_cells_of_old (hS.sub_mem_right h) hτ
    · exact d.mem_splitFace_cells_of_new h
    · exact d.mem_splitFace_cells_of_ear (Or.inr h.edge_mem)
    · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
    · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
  sub_refl := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσ, hσf⟩ | hσ
    · exact d.subRel_of_old hσ hσ hσf hσf (hS.sub_refl hσ)
    · exact Or.inr (Or.inl ⟨rfl, hσ⟩)
  sub_isLink := by
    intro f a b hl
    rw [splitFace_skel, skeleton, d.compatible.union_isLink] at hl
    rcases hl with hl | hl
    · exact d.subRel_of_old (S.mem_cells_of_mem_vertexSet hl.left_mem)
        (S.mem_cells_of_mem_edgeSet hl.edge_mem)
        (fun h => S.faces_ne_vertexSet d.face_mem hl.left_mem h.symm)
        (fun h => S.faces_ne_edgeSet d.face_mem hl.edge_mem h.symm) (hS.sub_isLink hl)
    · exact Or.inr (Or.inr (Or.inl ⟨b, hl⟩))
  face_maximal := by
    intro F τ hF h
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd d.face₁_mem_newCells h
      · exact h.symm
      · exact absurd h.vertex_mem fun hh => d.face₁_notMem_ear (Or.inl hh)
      · exact h
      · rcases h with h | h | h
        · exact absurd h d.face_ne
        · exact absurd h d.face₁_notMem_ear
        · exact absurd (d.cells₂_subset h) d.face₁_notMem
    · rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | h | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd d.face₂_mem_newCells h
      · exact h.symm
      · exact absurd h.vertex_mem fun hh => d.face₂_notMem_ear (Or.inl hh)
      · rcases h with h | h | h
        · exact absurd h.symm d.face_ne
        · exact absurd h d.face₂_notMem_ear
        · exact absurd (d.cells₁_subset h) d.face₂_notMem
      · exact h
    · have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
      have hFear : F ∉ d.earCells := by
        rintro (hh | hh)
        · rcases d.mem_cells_of_mem_ear_vertexSet hh hFc with rfl | rfl
          exacts [S.faces_ne_vertexSet hF d.source_mem_skel rfl,
            S.faces_ne_vertexSet hF d.target_mem_skel rfl]
        · exact d.edge_fresh hh hFc
      rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | h | ⟨-, h⟩ | ⟨-, h⟩
      · exact hS.face_maximal hF h
      · exact absurd hFc (notMem_cells_of_mem_newCells h)
      · exact absurd (Or.inl h.vertex_mem) hFear
      · rcases h with rfl | h | h
        · exact absurd hFc d.face₁_notMem
        · exact absurd h hFear
        · exact (d.notMem_faces_of_mem_cells₁ h hF).elim
      · rcases h with rfl | h | h
        · exact absurd hFc d.face₂_notMem
        · exact absurd h hFear
        · exact (d.notMem_faces_of_mem_cells₂ h hF).elim
  nonboundary_edge := by
    intro F hF
    rw [splitFace_faces] at hF
    obtain ⟨f, hf⟩ := d.exists_ear_edge
    have hfnew : f ∈ E((S.splitFace d).skel) := Or.inr hf
    have hfout : f ∉ E((S.splitFace d).outerGraph) := by
      rw [splitFace_outerGraph]
      exact fun hh => d.edge_fresh hf (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hh))
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · exact ⟨f, hfnew, hfout, d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inr hf)))⟩
    · exact ⟨f, hfnew, hfout, d.subRel_face₂_iff.2 (Or.inr (Or.inl (Or.inr hf)))⟩
    · obtain ⟨g, hgE, hgO, hgsub⟩ := hS.nonboundary_edge hF
      refine ⟨g, Or.inl hgE, hgO, d.subRel_of_old (S.mem_cells_of_mem_edgeSet hgE)
        (S.mem_cells_of_mem_faces hF) (fun h => S.faces_ne_edgeSet d.face_mem hgE h.symm)
        hFne hgsub⟩
  mem_face := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσ, hσf⟩ | hσ
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face hσ
      by_cases hFf : F = d.face
      · subst hFf
        rcases d.sub_face.1 hsub with h | h | h
        · exact absurd h hσf
        · exact ⟨d.face₁, Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inr (Or.inr h))⟩
        · exact ⟨d.face₂, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
            d.subRel_face₂_iff.2 (Or.inr (Or.inr h))⟩
      · exact ⟨F, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFf⟩),
          d.subRel_of_old hσ (S.mem_cells_of_mem_faces hF) hσf
            hFf hsub⟩
    · rcases hσ with (⟨hσ, -⟩ | hσ) | hσ
      · exact ⟨d.face₁, Set.mem_insert _ _,
          d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inl hσ)))⟩
      · exact ⟨d.face₁, Set.mem_insert _ _,
          d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inr hσ)))⟩
      · rcases hσ with rfl | rfl
        · exact ⟨d.face₁, Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inl rfl)⟩
        · exact ⟨d.face₂, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
            d.subRel_face₂_iff.2 (Or.inl rfl)⟩
  outerEdge_unique := by
    intro f hf
    rw [splitFace_outerGraph] at hf
    have hfE : f ∈ E(S.skel) := S.outerGraph_le.edgeSet_mono hf
    have hfc : f ∈ S.cells := S.mem_cells_of_mem_edgeSet hfE
    have hff : f ≠ d.face := fun h => S.faces_ne_edgeSet d.face_mem hfE h.symm
    have hfear : f ∉ d.earCells := by
      rintro (hh | hh)
      · rcases d.mem_cells_of_mem_ear_vertexSet hh hfc with rfl | rfl
        exacts [S.vertexSet_ne_edgeSet d.source_mem_skel hfE rfl,
          S.vertexSet_ne_edgeSet d.target_mem_skel hfE rfl]
      · exact d.edge_fresh hh hfc
    obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hf
    by_cases hFf : F = d.face
    · subst hFf
      -- the old incident 2-cell is the one being split: exactly one boundary path carries `f`
      have hcells : f ∈ d.cells₁ ∨ f ∈ d.cells₂ := by
        rcases d.sub_face.1 hsub with h | h | h
        exacts [absurd h hff, Or.inl h, Or.inr h]
      have hexcl : ¬ (f ∈ d.cells₁ ∧ f ∈ d.cells₂) := fun ⟨h₁, h₂⟩ =>
        d.paths_disjoint ((d.edge_mem_cells₁_iff hfE).1 h₁) ((d.edge_mem_cells₂_iff hfE).1 h₂)
      have hother : ∀ T, T ∈ S.faces → T ≠ d.face → ¬ S.sub f T := fun T hT hTf hsubT =>
        hTf (huniq T ⟨hT, hsubT⟩ ▸ rfl)
      rcases hcells with h | h
      · refine ⟨d.face₁, ⟨Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inr (Or.inr h))⟩,
          fun T hT => ?_⟩
        rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
        · rfl
        · rcases d.subRel_face₂_iff.1 hT.2 with hh | hh | hh
          · exact absurd (hh ▸ hfc) d.face₂_notMem
          · exact absurd hh hfear
          · exact absurd ⟨h, hh⟩ hexcl
        · exact absurd ((d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2)
            (hother T hT' hT'')
      · refine ⟨d.face₂, ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _),
          d.subRel_face₂_iff.2 (Or.inr (Or.inr h))⟩, fun T hT => ?_⟩
        rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
        · rcases d.subRel_face₁_iff.1 hT.2 with hh | hh | hh
          · exact absurd (hh ▸ hfc) d.face₁_notMem
          · exact absurd hh hfear
          · exact absurd ⟨hh, h⟩ hexcl
        · rfl
        · exact absurd ((d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2)
            (hother T hT' hT'')
    · refine ⟨F, ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFf⟩),
        d.subRel_of_old hfc (S.mem_cells_of_mem_faces hF) hff hFf hsub⟩, fun T hT => ?_⟩
      rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
      · rcases d.subRel_face₁_iff.1 hT.2 with hh | hh | hh
        · exact absurd (hh ▸ hfc) d.face₁_notMem
        · exact absurd hh hfear
        · exact absurd (huniq d.face ⟨d.face_mem, d.sub_face.2 (Or.inr (Or.inl hh))⟩).symm hFf
      · rcases d.subRel_face₂_iff.1 hT.2 with hh | hh | hh
        · exact absurd (hh ▸ hfc) d.face₂_notMem
        · exact absurd hh hfear
        · exact absurd (huniq d.face ⟨d.face_mem, d.sub_face.2 (Or.inr (Or.inr hh))⟩).symm hFf
      · exact huniq T ⟨hT', (d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2⟩

/-! #### The parent map of a 2-cell split -/

open scoped Classical in
/-- **The parent map of one 2-cell split** — assertion (iv). The ear's interior cells and both
new 2-cells have the split 2-cell as parent; every surviving cell — including the ear's two
endpoints, which the split does not create — is its own parent. -/
noncomputable def parent : γ → γ := fun σ => if σ ∈ d.newCells then d.face else σ

theorem parent_of_mem_newCells {σ : γ} (h : σ ∈ d.newCells) : d.parent σ = d.face := by
  rw [parent]; exact if_pos h

theorem parent_of_notMem_newCells {σ : γ} (h : σ ∉ d.newCells) : d.parent σ = σ := by
  rw [parent]; exact if_neg h

theorem parent_of_mem_cells {σ : γ} (h : σ ∈ S.cells) : d.parent σ = σ :=
  d.parent_of_notMem_newCells (notMem_newCells_of_mem_cells h)

theorem sub_parent_of_mem_cells₁ {σ : γ} (h : σ ∈ d.cells₁) : S.sub (d.parent σ) d.face := by
  rw [d.parent_of_mem_cells (d.cells₁_subset h)]; exact d.sub_face.2 (Or.inr (Or.inl h))

theorem sub_parent_of_mem_cells₂ {σ : γ} (h : σ ∈ d.cells₂) : S.sub (d.parent σ) d.face := by
  rw [d.parent_of_mem_cells (d.cells₂_subset h)]; exact d.sub_face.2 (Or.inr (Or.inr h))

theorem sub_parent_of_mem_earCells (hS : S.CombInvariants) {σ : γ} (h : σ ∈ d.earCells) :
    S.sub (d.parent σ) d.face := by
  rcases h with h | h
  · by_cases hc : σ ∈ S.cells
    · rcases d.mem_cells_of_mem_ear_vertexSet h hc with rfl | rfl
      · exact d.sub_parent_of_mem_cells₁ d.source_mem_cells₁
      · exact d.sub_parent_of_mem_cells₁ d.target_mem_cells₁
    · rw [d.parent_of_mem_newCells (Or.inl (Or.inl ⟨h, by
        rintro (rfl | rfl)
        exacts [hc d.source_mem_cells, hc d.target_mem_cells]⟩))]
      exact hS.sub_refl d.face_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl (Or.inr h))]; exact hS.sub_refl d.face_mem_cells

/-- **Assertion (iv), the compatibility clause**, for a 2-cell split. -/
theorem sub_parent (hS : S.CombInvariants) {σ τ : γ} (h : (S.splitFace d).sub σ τ) :
    S.sub (d.parent σ) (d.parent τ) := by
  rcases h with ⟨hσ, hτ, -, -, h⟩ | ⟨rfl, hσ⟩ | h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [d.parent_of_notMem_newCells hσ, d.parent_of_notMem_newCells hτ]; exact h
  · rw [d.parent_of_mem_newCells hσ]; exact hS.sub_refl d.face_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl (Or.inr h.edge_mem))]
    exact d.sub_parent_of_mem_earCells hS (Or.inl h.vertex_mem)
  · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]
    rcases h with rfl | h | h
    · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]; exact hS.sub_refl d.face_mem_cells
    · exact d.sub_parent_of_mem_earCells hS h
    · exact d.sub_parent_of_mem_cells₁ h
  · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]
    rcases h with rfl | h | h
    · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]; exact hS.sub_refl d.face_mem_cells
    · exact d.sub_parent_of_mem_earCells hS h
    · exact d.sub_parent_of_mem_cells₂ h

end SplitData

/-! ### The invariants at every stage -/

/-! ### The geometric assertions

Assertion (i) is the only geometric input the rest need: (ii), (viii) and (ix) follow from it
formally, with no further topology beyond "a nonempty open set contained in a closure meets the
set". That is why they are stated here for an arbitrary realization satisfying (i), rather than
by induction: the induction is entirely in (i) and (vii), and those are the standing gap of this
module. -/

namespace Realization

namespace IsCellDecomposition

variable {S : CellStructure γ} {R : S.Realization} {D : Set Plane} {σ τ ρ : γ}

/-- A point of an open cell lying in a closed cell forces the abstract relation. This is the
one step of the argument; everything below is a corollary of it. -/
theorem sub_of_mem (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) (hτ : τ ∈ S.cells)
    {z : Plane} (hzσ : z ∈ R.cell σ) (hzτ : z ∈ closure (R.cell τ)) : S.sub σ τ := by
  rw [h.closure_eq hτ] at hzτ
  obtain ⟨ρ, hρ, hzρ⟩ := Set.mem_iUnion₂.1 hzτ
  by_cases hne : σ = ρ
  · exact hne ▸ hρ.2
  · exact absurd hzρ (Set.disjoint_left.1 (h.disjoint hσ hρ.1 hne) hzσ)

theorem sub_of_subset_closure (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hτ : τ ∈ S.cells) (hsub : R.cell σ ⊆ closure (R.cell τ)) : S.sub σ τ := by
  obtain ⟨z, hz⟩ := h.nonempty hσ
  exact h.sub_of_mem hσ hτ hz (hsub hz)

/-- On a structure with a cell decomposition `≼_abs` *is* reflexive on cells — the blueprint's
"each geometric relation is reflexive". It is not assumed of a `CellStructure`; it is read off
(i). -/
theorem sub_refl (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : S.sub σ σ :=
  h.sub_of_subset_closure hσ hσ _root_.subset_closure

end IsCellDecomposition

end Realization

/-! ### Assertion (i) is preserved by an edge subdivision

The induction step of (i) over the first constructor. It relates two realizations of two
different structures, so it needs a name for "`R'` refines `R` along `d`": that is
`SubdivData.IsRefinement`, whose fields are exactly the blueprint's sentence "the corresponding
point is inserted into the corresponding edge using the edge parametrization", read as a
statement about the resulting open cells and their closures. -/

end CellStructure

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- **The Jordan domain is the disjoint union of the two sides and the open crosscut.** This is
the shape assertion (i) consumes at a 2-cell split: the old open 2-cell is partitioned into the
two new open 2-cells together with the open cells of the ear (here the ear is one open edge,
its two endpoints being old cells). -/
theorem IsCrosscut.inside_eq_split (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {p, q}) := by
  conv_lhs => rw [← Set.sdiff_union_inter (inside C) P]
  rw [h.inside_diff_eq hjordan hcut hcollars, h.inside_inter]

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cyclic boundaries of abstract 2-cells

The abstract `CellStructure.boundary` field is only a list of edge names.  The finite-transfer
construction needs the stronger invariant that each face boundary is a simple cycle and that
its vertices and edges are exactly the strict subcells of the face.  This module packages that
invariant in the representation already used by `Graph.IsLongCycle`.

The distinguished edge `edge` closes the simple detour `walk`.  The list `edge :: walk` is a
closed walk when started at `target`: it crosses the distinguished edge backwards to `source`
and follows the detour back to `target`.  Two-edge cycles are allowed: an ear split can
legitimately create a digon even when the initial outer cycle has at least three vertices.
Stating the carrier clause with
`CellStructure.pathCells` makes it directly comparable with `SplitData.sub_face`.

## Blueprint

* `Schoenflies.CellStructure.FaceCycle`, `BoundaryCycles` — the maintained form of the
  sentence in `lem:cellulation-invariants` that the cells below every 2-cell form its boundary
  cycle.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*}

namespace FaceCycle

variable {S : CellStructure γ} {F : γ}

/-- Path cells split over the concatenation of two composable walks. -/
theorem pathCells_append {u w v : γ} {W₁ W₂ : List γ}
    (h₁ : S.skel.IsWalk u W₁ w) (h₂ : S.skel.IsWalk w W₂ v) :
    S.pathCells u (W₁ ++ W₂) = S.pathCells u W₁ ∪ S.pathCells w W₂ := by
  apply Set.Subset.antisymm
  · rintro σ (hσ | hσ)
    · rcases List.mem_append.1 hσ with hσ | hσ
      · exact Or.inl (Or.inl hσ)
      · exact Or.inr (Or.inl hσ)
    · rcases Graph.walkVertices_append_subset hσ with hσ | hσ
      · exact Or.inl (Or.inr hσ)
      · exact Or.inr (Or.inr hσ)
  · rintro σ (hσ | hσ)
    · rcases hσ with hσ | hσ
      · exact Or.inl (List.mem_append_left W₂ hσ)
      · exact Or.inr (Graph.walkVertices_mono (List.subset_append_left W₁ W₂) hσ)
    · rcases hσ with hσ | hσ
      · exact Or.inl (List.mem_append_right W₁ hσ)
      · rcases Graph.mem_walkVertices_iff.1 hσ with rfl | hcov
        · exact Or.inr
            (Graph.walkVertices_mono (List.subset_append_left W₁ W₂)
              h₁.target_mem_walkVertices)
        · exact Or.inr (Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_append.symm ▸ Or.inr hcov))

/-- Reversing a walk changes neither its edge cells nor its vertex cells. -/
theorem pathCells_reverse {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    S.pathCells v W.reverse = S.pathCells u W := by
  rw [CellStructure.pathCells, CellStructure.pathCells, h.reverse_walkVertices]
  simp

end FaceCycle

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.JordanSeparates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A Jordan curve separates the plane

Half of the Jordan curve theorem: the complement of a Jordan curve `C` is disconnected. The
proof is the blueprint's — build a subdivision of `K(3,3)` out of the curve, a chord of it, a
detour above it, and a connecting arc, and appeal to `Graph.IsArcK33.elim`.

## The configuration

Fix a coordinate `i` in which `C` has nonzero width, and let `j` be the other one. Write `m`
and `M` for the extreme `i`-coordinates on `C`, and let `p₁`, `p₂` be the points of `C` on the
two supporting lines `{z | z i = m}`, `{z | z i = M}` with the largest `j`-coordinate. Two
points of a Jordan curve cut it into two arcs `C₁`, `C₂` (`IsJordanCurve.two_arcs`). Both meet
the middle line `{z | z i = (m + M) / 2}`, by the intermediate value theorem; a closest pair
`a ∈ C₁`, `b ∈ C₂` on that line spans a segment `L₄` whose interior misses `C`. Running up the
two supporting lines and across above the curve gives a polygonal set meeting `C` exactly in
`{p₁, p₂}` and missing `L₄`; a simple arc `L₅` inside it (`exists_simple_poly_of_poly`) is the
blueprint's detour.

The blueprint argues inside the unbounded component: it supposes `L₄ \ {a, b}` to lie there,
and concludes that it does not. Here the contradiction hypothesis is the statement being
negated — that the whole complement is preconnected — which is weaker to assume and gives the
same `K(3,3)`. Nothing about the unbounded component is needed, so nothing about it is proved;
`exists_unique_unbounded_connectedComponentIn_compl` at the end is the separate cheap fact.

*If* the complement were preconnected, a simple polygonal arc `R` inside it would join an
interior point of `L₄` to an interior point of `L₅`. Its last parameter on `L₄` and the first
one after that on `L₅` cut out a piece `L₆` meeting `L₄ ∪ L₅` only at its two ends — this is
why the blueprint takes such care over the order in which `c'` and `d'` are chosen. Cutting
`C₁` at `a`, `C₂` at `b`, `L₅` at the far end `d'` of `L₆` and `L₄` at its near end `c'`
produces nine arcs on the six points `{p₁, p₂, c'}`, `{a, b, d'}`, meeting only where a
`K(3,3)` forces them to. That is impossible, so the complement is not preconnected.

## Coordinates instead of a rotation

The blueprint rotates so that the direction of nonzero width becomes horizontal. Here the two
coordinate indices are carried as parameters `i ≠ j` of `not_isPreconnected_compl_of_coord`
instead, and the headline theorem picks whichever pair works. No rotation, no trigonometry and
no coordinate-swap symmetry lemma is needed: every step is symmetric in the two indices except
for which one is named.

The blueprint's opening step — a Jordan curve is not contained in a line — is not needed in
this form. All it is used for is a direction of nonzero width, and that follows from the curve
having two distinct points (`IsJordanCurve.exists_ne`). The degenerate configurations the
blueprint's step rules out are excluded downstream instead, by `C₁ ∩ C₂ = {p₁, p₂}`.

## Blueprint

* `Schoenflies.not_isPreconnected_compl_of_coord`,
  `Schoenflies.IsJordanCurve.not_isPreconnected_compl`,
  `Schoenflies.IsJordanCurve.exists_connectedComponentIn_ne` — `prop:jordan-disconnected`.
* `Schoenflies.exists_unique_unbounded_connectedComponentIn_compl` — the opening sentence of
  the blueprint's Jordan section: the complement of a compact set has exactly one unbounded
  component.
* `Graph.isArcK33_of_pieces` — the packaging of `cor:k33-subdivision` (through
  `Graph.IsArcK33.elim`) that this configuration fits.
* `Schoenflies.IsArcBetween.exists_split` — an arc cut at an interior point; the arc analogue
  of the second clause of `lem:jordan-circle`, which `Schoenflies.IsJordanCurve.two_arcs` is.

## For the integrator

Three groups of declarations here are general and have no home yet on `main`:

* `Schoenflies.Plane.coord_ext`, `axisVec`, `setCoord`, `coord_eq_of_mem_segment`,
  `le_coord_of_mem_segment`, `coord_le_of_mem_segment` belong beside the coordinate
  half-planes in `Schoenflies/Square.lean`.
* `Schoenflies.IsArcBetween.exists_split` belongs in `Schoenflies/Subarc.lean`, next to
  `IsArc.exists_isArcBetween_subset`; `Schoenflies.injective_three` is a `Fin 3` triviality.
* `Graph.isArcK33_of_pieces` belongs in `Schoenflies/Graph/K33Planar.lean`, next to
  `Graph.IsArcK33`.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

theorem axisVec_of_ne {i j : Fin 2} (h : i ≠ j) : axisVec j i = 0 := by
  revert h; fin_cases i <;> fin_cases j <;> intro h <;> simp_all [axisVec]

theorem setCoord_of_ne {i j : Fin 2} (h : i ≠ j) (z : Plane) (t : ℝ) :
    setCoord z j t i = z i := by
  simp [setCoord, axisVec_of_ne h]

/-! ### Coordinates along a segment -/

variable {k : Fin 2} {r : ℝ} {s t z : Plane}

/-- A coordinate constant at both ends of a segment is constant along it. -/
theorem coord_eq_of_mem_segment (hs : s k = r) (ht : t k = r) (hz : z ∈ segment ℝ s t) :
    z k = r :=
  le_antisymm ((convex_coord_le k r).segment_subset hs.le ht.le hz)
    ((convex_coord_ge k r).segment_subset hs.ge ht.ge hz)

/-- A lower bound on a coordinate at both ends of a segment holds along it. -/
theorem le_coord_of_mem_segment (hs : r ≤ s k) (ht : r ≤ t k) (hz : z ∈ segment ℝ s t) :
    r ≤ z k :=
  (convex_coord_ge k r).segment_subset hs ht hz

/-- An upper bound on a coordinate at both ends of a segment holds along it. -/
theorem coord_le_of_mem_segment (hs : s k ≤ r) (ht : t k ≤ r) (hz : z ∈ segment ℝ s t) :
    z k ≤ r :=
  (convex_coord_le k r).segment_subset hs ht hz

end Plane

/-! ### Cutting an arc at an interior point -/

/-- **An arc splits at any of its interior points** into two arcs which cover it and meet
exactly there. This is the arc analogue of `IsJordanCurve.two_arcs`, and is what turns each
branch of the configuration below into two branch paths of the `K(3,3)`. -/
theorem IsArcBetween.exists_split {A : Set Plane} {p q z : Plane} (h : IsArcBetween A p q)
    (hz : z ∈ A) (hzp : z ≠ p) (hzq : z ≠ q) :
    ∃ A₁ A₂, IsArcBetween A₁ p z ∧ IsArcBetween A₂ z q ∧ A₁ ∪ A₂ = A ∧ A₁ ∩ A₂ = {z} := by
  obtain ⟨f, hc, hi, rfl, rfl, rfl⟩ := h
  obtain ⟨r, hr, rfl⟩ := hz
  have hr0 : (0 : ℝ) ≠ r := fun hc => hzp (by rw [hc])
  have hr1 : r ≠ (1 : ℝ) := fun hc => hzq (by rw [hc])
  have hsub₁ : Icc (0 : ℝ) r ⊆ I := Icc_subset_Icc le_rfl hr.2
  have hsub₂ : Icc r (1 : ℝ) ⊆ I := Icc_subset_Icc hr.1 le_rfl
  refine ⟨f '' Icc 0 r, f '' Icc r 1, ?_, ?_, ?_, ?_⟩
  · have := isArcBetween_subarc_of_injOn_I hc hi zero_mem_I hr hr0
    rwa [uIcc_of_le hr.1] at this
  · have := isArcBetween_subarc_of_injOn_I hc hi hr one_mem_I hr1
    rwa [uIcc_of_le hr.2] at this
  · rw [← image_union, Icc_union_Icc_eq_Icc hr.1 hr.2]
  · rw [← hi.image_inter hsub₁ hsub₂, Icc_inter_Icc, max_eq_right hr.1, min_eq_left hr.2,
      Icc_self, image_singleton]

end Schoenflies

namespace Graph

open Schoenflies

/-- **Nine arcs assembled from three chains, two bridges of a fourth, and a ninth arc.**

This is a packaging lemma: it repackages the `meet` clause of `Graph.IsArcK33` as the five
containment facts that a `K(3,3)` subdivision found inside a plane configuration actually
produces. The rows `0` and `1` of `P` are the two halves of three chains `Ch 0, Ch 1, Ch 2`
running from `x 0` to `x 1`, each cut at the point `y j`; row `2` holds three further pieces,
carried by sets `Sg j`, that all issue from `x 2`.

The hypotheses are exactly what the separation proof below has to hand, and nothing about
their geometry is used: only the listed intersections. -/
theorem isArcK33_of_pieces {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}
    {Ch Sg : Fin 3 → Set Plane}
    (harc : ∀ i j, IsArcBetween (P i j) (x i) (y j))
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j)
    (hsubCh₀ : ∀ j, P 0 j ⊆ Ch j) (hsubCh₁ : ∀ j, P 1 j ⊆ Ch j) (hsubSg : ∀ j, P 2 j ⊆ Sg j)
    (hsplit : ∀ j, P 0 j ∩ P 1 j ⊆ {y j})
    (hChCh : ∀ j l, j ≠ l → Ch j ∩ Ch l ⊆ {x 0, x 1})
    (hChSg : ∀ j l, Ch j ∩ Sg l ⊆ {y j})
    (hSgSg : ∀ j l, j ≠ l → P 2 j ∩ P 2 l ⊆ {x 2}) :
    IsArcK33 x y P := by
  -- `x 0` is an endpoint of every piece in row `0`; were it also on a piece of row `1` it would
  -- be the cut point `y j` the two share, and the six points are distinct.
  have hx0 : ∀ j, x 0 ∉ P 1 j := fun j hmem =>
    hxy 0 j (hsplit j ⟨(harc 0 j).left_mem, hmem⟩)
  have hx1 : ∀ j, x 1 ∉ P 0 j := fun j hmem =>
    hxy 1 j (hsplit j ⟨hmem, (harc 1 j).left_mem⟩)
  have hrow : ∀ m : Fin 3, m ≠ 2 → m = 0 ∨ m = 1 := by decide
  have hsubCh : ∀ i j, i ≠ 2 → P i j ⊆ Ch j := by
    intro i j hi
    rcases hrow i hi with rfl | rfl
    exacts [hsubCh₀ j, hsubCh₁ j]
  -- Half of the `meet` clause; the other half is this one with the two index pairs exchanged.
  have key : ∀ i j k l : Fin 3, (i, j) ≠ (k, l) → P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) := by
    rintro i j k l hne z ⟨hz1, hz2⟩
    rcases eq_or_ne i 2 with rfl | hi2
    · rcases eq_or_ne k 2 with rfl | hk2
      · -- Two pieces of the bottom row: they meet only at `x 2`.
        exact Or.inl (hSgSg j l (fun h => hne (by rw [h])) ⟨hz1, hz2⟩)
      · -- A bottom-row piece against a piece of the chain `Ch l`.
        have hzl : z = y l := hChSg l j ⟨hsubCh k l hk2 hz2, hsubSg j hz1⟩
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr hzl
        · -- `y l` is an endpoint of `P 2 l` too, so it is on two bottom-row pieces: it is `x 2`.
          exact Or.inl (hSgSg l j (Ne.symm hjl)
            ⟨by rw [hzl]; exact (harc 2 l).right_mem, hz1⟩)
    · rcases eq_or_ne k 2 with rfl | hk2
      · exact Or.inr (hChSg j l ⟨hsubCh i j hi2 hz1, hsubSg l hz2⟩)
      · rcases eq_or_ne j l with rfl | hjl
        · -- Same chain, the two halves: they meet at the cut point.
          have hik : i ≠ k := fun h => hne (by rw [h])
          rcases hrow i hi2 with rfl | rfl <;> rcases hrow k hk2 with rfl | rfl
          · exact absurd rfl hik
          · exact Or.inr (hsplit j ⟨hz1, hz2⟩)
          · exact Or.inr (hsplit j ⟨hz2, hz1⟩)
          · exact absurd rfl hik
        · -- Distinct chains: their common points are the two ends `x 0`, `x 1`.
          rcases hChCh j l hjl ⟨hsubCh i j hi2 hz1, hsubCh k l hk2 hz2⟩ with rfl | rfl
          · rcases hrow i hi2 with rfl | rfl
            · exact Or.inl rfl
            · exact absurd hz1 (hx0 j)
          · rcases hrow i hi2 with rfl | rfl
            · exact absurd hz1 (hx1 j)
            · exact Or.inl rfl
  exact { arc := harc, x_injective := hx, y_injective := hy, ne := hxy,
          meet := fun i j k l hne => subset_inter (key i j k l hne)
            (by rw [inter_comm]; exact key k l i j (Ne.symm hne)) }

end Graph

namespace Schoenflies

open Plane

/-! ### The separation proof -/

/-- **Proposition 3.2 (a Jordan curve separates)**, with the coordinate direction named.

`i` is the blueprint's horizontal direction and `j` its vertical one; the hypothesis on `u`
and `v` is that the projection of `C` to the `i`-th coordinate has nonzero width, which is all
the blueprint's rotation achieves. `IsJordanCurve.not_isPreconnected_compl` discharges it. -/
theorem not_isPreconnected_compl_of_coord {C : Set Plane} (hC : IsJordanCurve C)
    {i j : Fin 2} (hij : i ≠ j) {u v : Plane} (hu : u ∈ C) (hv : v ∈ C) (huv : u i ≠ v i) :
    ¬ IsPreconnected Cᶜ := by
  intro hconn
  have hCcomp : IsCompact C := hC.isCompact
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hCne : C.Nonempty := ⟨u, hu⟩
  have hlineClosed : ∀ r : ℝ, IsClosed {z : Plane | z i = r} := fun r =>
    isClosed_eq (continuous_coord i) continuous_const
  -- ## The two supporting lines
  obtain ⟨z₁, hz₁C, hz₁min⟩ := hCcomp.exists_isMinOn hCne (continuous_coord i).continuousOn
  obtain ⟨z₂, hz₂C, hz₂max⟩ := hCcomp.exists_isMaxOn hCne (continuous_coord i).continuousOn
  have hmin : ∀ z ∈ C, z₁ i ≤ z i := isMinOn_iff.mp hz₁min
  have hmax : ∀ z ∈ C, z i ≤ z₂ i := isMaxOn_iff.mp hz₂max
  set m : ℝ := z₁ i
  set M : ℝ := z₂ i
  -- The curve has two points with different `i`-coordinates, so the strip between the two
  -- supporting lines is nondegenerate: were the two extremes equal, every point of `C` would
  -- be squeezed onto that one value.
  have hmM : m < M := by
    rcases eq_or_lt_of_le (hmin z₂ hz₂C) with h | h
    · refine absurd ?_ huv
      rw [le_antisymm (by rw [h]; exact hmax u hu) (hmin u hu),
        le_antisymm (by rw [h]; exact hmax v hv) (hmin v hv)]
    · exact h
  -- ## The highest point of the curve on each supporting line
  obtain ⟨p₁, hp₁mem, hp₁max⟩ := (hCcomp.inter_right (hlineClosed m)).exists_isMaxOn
    ⟨z₁, hz₁C, rfl⟩ (continuous_coord j).continuousOn
  obtain ⟨p₂, hp₂mem, hp₂max⟩ := (hCcomp.inter_right (hlineClosed M)).exists_isMaxOn
    ⟨z₂, hz₂C, rfl⟩ (continuous_coord j).continuousOn
  have hp₁C : p₁ ∈ C := hp₁mem.1
  have hp₂C : p₂ ∈ C := hp₂mem.1
  have hp₁i : p₁ i = m := hp₁mem.2
  have hp₂i : p₂ i = M := hp₂mem.2
  have hp₁top : ∀ z ∈ C, z i = m → z j ≤ p₁ j := fun z hz hzi => isMaxOn_iff.mp hp₁max z ⟨hz, hzi⟩
  have hp₂top : ∀ z ∈ C, z i = M → z j ≤ p₂ j := fun z hz hzi => isMaxOn_iff.mp hp₂max z ⟨hz, hzi⟩
  have hp₁p₂ : p₁ ≠ p₂ := by
    intro h; rw [h, hp₂i] at hp₁i; exact hmM.ne' hp₁i
  -- ## The two arcs of the curve between them
  obtain ⟨C₁, C₂, harc₁, harc₂, hcover, hCmeet⟩ := hC.two_arcs hp₁C hp₂C hp₁p₂
  have hC₁sub : C₁ ⊆ C := by rw [← hcover]; exact subset_union_left
  have hC₂sub : C₂ ⊆ C := by rw [← hcover]; exact subset_union_right
  -- ## A line strictly between the two supporting lines
  set mid : ℝ := (m + M) / 2 with hmid
  have hmmid : m < mid := by rw [hmid]; linarith
  have hmidM : mid < M := by rw [hmid]; linarith
  -- A point on that line is neither of the two chosen curve points.
  have hne_mid : ∀ z : Plane, z i = mid → z ≠ p₁ ∧ z ≠ p₂ := by
    refine fun z hz => ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, hp₁i] at hz; exact hmmid.ne hz
    · rw [h, hp₂i] at hz; exact hmidM.ne' hz
  -- Both arcs meet the middle line, by the intermediate value theorem on the `i`-coordinate.
  have hmeets : ∀ A : Set Plane, IsArcBetween A p₁ p₂ → ∃ z ∈ A, z i = mid := by
    intro A hA
    have hIVT := hA.isArc.isConnected.isPreconnected.intermediate_value hA.left_mem hA.right_mem
      (continuous_coord i).continuousOn
    exact hIVT (show mid ∈ Icc (p₁ i) (p₂ i) by rw [hp₁i, hp₂i]; exact ⟨hmmid.le, hmidM.le⟩)
  obtain ⟨w₁, hw₁A, hw₁i⟩ := hmeets C₁ harc₁
  obtain ⟨w₂, hw₂A, hw₂i⟩ := hmeets C₂ harc₂
  -- ## The closest pair on the middle line
  obtain ⟨⟨a, b⟩, hab, habmin⟩ :=
    ((harc₁.isArc.isCompact.inter_right (hlineClosed mid)).prod
      (harc₂.isArc.isCompact.inter_right (hlineClosed mid))).exists_isMinOn
      ⟨(w₁, w₂), ⟨⟨hw₁A, hw₁i⟩, ⟨hw₂A, hw₂i⟩⟩⟩ continuous_dist.continuousOn
  obtain ⟨haC₁, hai⟩ := hab.1
  obtain ⟨hbC₂, hbi⟩ := hab.2
  have hminab : ∀ s ∈ C₁ ∩ {z : Plane | z i = mid}, ∀ t ∈ C₂ ∩ {z : Plane | z i = mid},
      dist a b ≤ dist s t := fun s hs t ht => isMinOn_iff.mp habmin (s, t) ⟨hs, ht⟩
  have hab_ne : a ≠ b := by
    intro h
    have hmem : a ∈ C₁ ∩ C₂ := ⟨haC₁, h ▸ hbC₂⟩
    rw [hCmeet] at hmem
    rcases hmem with h₁ | h₁
    · exact (hne_mid a hai).1 h₁
    · exact (hne_mid a hai).2 h₁
  -- The open segment between the closest pair misses the curve.
  have hopenSeg : ∀ z ∈ openSegment ℝ a b, z ∉ C := by
    intro z hz hzC
    have hzseg : z ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hz
    have hzi : z i = mid := coord_eq_of_mem_segment hai hbi hzseg
    have hlt : dist a z < dist a b :=
      (dist_lt_of_mem_openSegment hab_ne (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
        hab_ne (by simp) hz).2
    have hgt : dist b z < dist b a :=
      (dist_lt_of_mem_openSegment hab_ne.symm (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)
        hab_ne.symm (by simp) (by rwa [openSegment_symm] at hz)).2
    rw [← hcover] at hzC
    rcases hzC with h | h
    · exact absurd (hminab z ⟨h, hzi⟩ b ⟨hbC₂, hbi⟩)
        (not_le.mpr (by rw [dist_comm z b, dist_comm a b]; exact hgt))
    · exact absurd (hminab a ⟨haC₁, hai⟩ z ⟨h, hzi⟩) (not_le.mpr hlt)
  have hsegC : ∀ z ∈ segment ℝ a b, z ∈ C → z = a ∨ z = b := by
    intro z hz hzC
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hzC (hopenSeg z hz)
  -- ## The detour above the curve
  obtain ⟨z₃, hz₃C, hz₃max⟩ := hCcomp.exists_isMaxOn hCne (continuous_coord j).continuousOn
  set top : ℝ := z₃ j + 1 with htop
  have hCtop : ∀ z ∈ C, z j < top := by
    intro z hz; have := isMaxOn_iff.mp hz₃max z hz; rw [htop]; linarith
  set q₁ : Plane := setCoord p₁ j top with hq₁
  set q₂ : Plane := setCoord p₂ j top with hq₂
  have hq₁i : q₁ i = m := by rw [hq₁, setCoord_of_ne hij, hp₁i]
  have hq₂i : q₂ i = M := by rw [hq₂, setCoord_of_ne hij, hp₂i]
  have hq₁j : q₁ j = top := by rw [hq₁, setCoord_self]
  have hq₂j : q₂ j = top := by rw [hq₂, setCoord_self]
  have hWeq : poly [p₁, q₁, q₂, p₂] =
      segment ℝ p₁ q₁ ∪ (segment ℝ q₁ q₂ ∪ segment ℝ q₂ p₂) := by
    rw [poly_cons_cons, poly_cons_cons, poly_pair]
  -- The detour meets the curve exactly at its two endpoints ...
  have hWsubC : ∀ z ∈ poly [p₁, q₁, q₂, p₂], z ∈ C → z = p₁ ∨ z = p₂ := by
    intro z hzW hzC
    rw [hWeq] at hzW
    rcases hzW with h | h | h
    · refine Or.inl (coord_ext hij ?_ ?_)
      · rw [coord_eq_of_mem_segment hp₁i hq₁i h, hp₁i]
      · exact le_antisymm (hp₁top z hzC (coord_eq_of_mem_segment hp₁i hq₁i h))
          (le_coord_of_mem_segment le_rfl (by rw [hq₁j]; exact (hCtop p₁ hp₁C).le) h)
    · exact absurd (hCtop z hzC) (by rw [coord_eq_of_mem_segment hq₁j hq₂j h]; exact lt_irrefl top)
    · refine Or.inr (coord_ext hij ?_ ?_)
      · rw [coord_eq_of_mem_segment hq₂i hp₂i h, hp₂i]
      · exact le_antisymm (hp₂top z hzC (coord_eq_of_mem_segment hq₂i hp₂i h))
          (le_coord_of_mem_segment (by rw [hq₂j]; exact (hCtop p₂ hp₂C).le) le_rfl h)
  -- ... and misses the closest-pair segment altogether.
  have hWL₄ : ∀ z ∈ poly [p₁, q₁, q₂, p₂], z ∉ segment ℝ a b := by
    intro z hzW hzL₄
    have hzmid : z i = mid := coord_eq_of_mem_segment hai hbi hzL₄
    rw [hWeq] at hzW
    rcases hzW with h | h | h
    · rw [coord_eq_of_mem_segment hp₁i hq₁i h] at hzmid; exact hmmid.ne hzmid
    · have hzj : z j ≤ z₃ j := coord_le_of_mem_segment
        (isMaxOn_iff.mp hz₃max a (hC₁sub haC₁)) (isMaxOn_iff.mp hz₃max b (hC₂sub hbC₂)) hzL₄
      rw [coord_eq_of_mem_segment hq₁j hq₂j h, htop] at hzj; linarith
    · rw [coord_eq_of_mem_segment hq₂i hp₂i h] at hzmid; exact hmidM.ne' hzmid
  -- ## The detour, made into a simple arc
  obtain ⟨L₅, hL₅sub, hL₅arc⟩ : ∃ A ⊆ poly [p₁, q₁, q₂, p₂], IsArcBetween A p₁ p₂ := by
    have hlne : ([p₁, q₁, q₂, p₂] : List Plane) ≠ [] := by simp
    obtain ⟨ws, -, -, -, hsub, harc⟩ := exists_simple_poly_of_poly
      (vs := [p₁, q₁, q₂, p₂]) (isConnected_poly hlne).isPreconnected hp₁p₂
      (mem_poly_of_mem (by simp)) (mem_poly_of_mem (by simp))
    exact ⟨poly ws, hsub, harc⟩
  have hL₅C : ∀ z ∈ L₅, z ∈ C → z = p₁ ∨ z = p₂ := fun z hz => hWsubC z (hL₅sub hz)
  have hL₅L₄ : ∀ z ∈ L₅, z ∉ segment ℝ a b := fun z hz => hWL₄ z (hL₅sub hz)
  -- ## Interior points of the two crossings
  obtain ⟨d, hdL₅, hdp₁, hdp₂⟩ : ∃ d ∈ L₅, d ≠ p₁ ∧ d ≠ p₂ := by
    obtain ⟨g, -, hgi, hgim, hg0, hg1⟩ := hL₅arc
    have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
    refine ⟨g (1 / 2), by rw [← hgim]; exact mem_image_of_mem g hhalf, ?_, ?_⟩
    · rw [← hg0]; intro hcon; have := hgi hhalf zero_mem_I hcon; norm_num at this
    · rw [← hg1]; intro hcon; have := hgi hhalf one_mem_I hcon; norm_num at this
  obtain ⟨cpt, hcptOpen⟩ : ∃ c : Plane, c ∈ openSegment ℝ a b :=
    ⟨_, ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩⟩
  have hcptSeg : cpt ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hcptOpen
  have hcptCc : cpt ∈ Cᶜ := hopenSeg cpt hcptOpen
  have hdCc : d ∈ Cᶜ := fun hcon => by
    rcases hL₅C d hdL₅ hcon with h | h
    exacts [hdp₁ h, hdp₂ h]
  have hcd : cpt ≠ d := fun h => hL₅L₄ d hdL₅ (h ▸ hcptSeg)
  -- ## A simple polygonal arc joining them in the complement
  obtain ⟨R, hRsub, -, hRarc⟩ := exists_simple_arc_of_isPreconnected hCopen hconn hcptCc hdCc hcd
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hRarc
  have hL₄closed : IsClosed (segment ℝ a b) := (isCompact_segment a b).isClosed
  have hL₅closed : IsClosed L₅ := hL₅arc.isArc.isClosed
  -- The last parameter at which the arc is on the closest-pair segment ...
  obtain ⟨sp, hspI, hspSeg, hspmax⟩ :
      ∃ s ∈ I, f s ∈ segment ℝ a b ∧ ∀ t ∈ I, f t ∈ segment ℝ a b → t ≤ s := by
    have hcl : IsClosed (I ∩ f ⁻¹' segment ℝ a b) :=
      hfc.preimage_isClosed_of_isClosed isClosed_Icc hL₄closed
    have h0 : (0 : ℝ) ∈ I ∩ f ⁻¹' segment ℝ a b :=
      ⟨zero_mem_I, by rw [mem_preimage, hf0]; exact hcptSeg⟩
    have hbdd : BddAbove (I ∩ f ⁻¹' segment ℝ a b) := ⟨1, fun t ht => ht.1.2⟩
    obtain ⟨h1, h2⟩ := hcl.csSup_mem ⟨0, h0⟩ hbdd
    exact ⟨_, h1, h2, fun t ht hmem => le_csSup hbdd ⟨ht, hmem⟩⟩
  -- ... and the first parameter after it at which the arc is on the detour.
  obtain ⟨tp, htpmem, htpL₅, htpmin⟩ :
      ∃ t ∈ Icc sp 1, f t ∈ L₅ ∧ ∀ r ∈ Icc sp 1, f r ∈ L₅ → t ≤ r := by
    have hcl : IsClosed (Icc sp 1 ∩ f ⁻¹' L₅) :=
      (hfc.mono (Icc_subset_Icc hspI.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc hL₅closed
    have h1mem : (1 : ℝ) ∈ Icc sp 1 ∩ f ⁻¹' L₅ :=
      ⟨⟨hspI.2, le_rfl⟩, by rw [mem_preimage, hf1]; exact hdL₅⟩
    have hbdd : BddBelow (Icc sp 1 ∩ f ⁻¹' L₅) := ⟨sp, fun t ht => ht.1.1⟩
    obtain ⟨h1, h2⟩ := hcl.csInf_mem ⟨1, h1mem⟩ hbdd
    exact ⟨_, h1, h2, fun r hr hmem => csInf_le hbdd ⟨hr, hmem⟩⟩
  have htpI : tp ∈ I := ⟨hspI.1.trans htpmem.1, htpmem.2⟩
  have hsptp : sp ≠ tp := fun hcon => hL₅L₄ (f tp) htpL₅ (hcon ▸ hspSeg)
  -- ## The last branch arc: the piece of `R` between those two parameters
  obtain ⟨L₆, hL₆arc, hL₆C, hL₆L₄, hL₆L₅⟩ :
      ∃ L₆, IsArcBetween L₆ (f sp) (f tp) ∧ (∀ z ∈ L₆, z ∉ C) ∧
        (∀ z ∈ L₆, z ∈ segment ℝ a b → z = f sp) ∧ (∀ z ∈ L₆, z ∈ L₅ → z = f tp) := by
    refine ⟨f '' Icc sp tp, ?_, ?_, ?_, ?_⟩
    · have := isArcBetween_subarc_of_injOn_I hfc hfi hspI htpI hsptp
      rwa [uIcc_of_le (lt_of_le_of_ne htpmem.1 hsptp).le] at this
    · rintro _ ⟨r, hr, rfl⟩
      exact hRsub (by rw [← hfim]; exact mem_image_of_mem f ⟨hspI.1.trans hr.1, hr.2.trans htpI.2⟩)
    · rintro _ ⟨r, hr, rfl⟩ hmem
      rw [le_antisymm (hspmax r ⟨hspI.1.trans hr.1, hr.2.trans htpI.2⟩ hmem) hr.1]
    · rintro _ ⟨r, hr, rfl⟩ hmem
      rw [le_antisymm hr.2 (htpmin r ⟨hr.1, hr.2.trans htpI.2⟩ hmem)]
  have hcpC : f sp ∉ C := hL₆C _ hL₆arc.left_mem
  have hdpC : f tp ∉ C := hL₆C _ hL₆arc.right_mem
  -- ## The six branch vertices are six distinct points
  have hp₁a : p₁ ≠ a := fun h => (hne_mid a hai).1 h.symm
  have hp₁b : p₁ ≠ b := fun h => (hne_mid b hbi).1 h.symm
  have hp₂a : p₂ ≠ a := fun h => (hne_mid a hai).2 h.symm
  have hp₂b : p₂ ≠ b := fun h => (hne_mid b hbi).2 h.symm
  have hp₁dp : p₁ ≠ f tp := fun h => hdpC (h ▸ hp₁C)
  have hp₂dp : p₂ ≠ f tp := fun h => hdpC (h ▸ hp₂C)
  have hp₁cp : p₁ ≠ f sp := fun h => hcpC (h ▸ hp₁C)
  have hp₂cp : p₂ ≠ f sp := fun h => hcpC (h ▸ hp₂C)
  have hcpa : f sp ≠ a := fun h => hcpC (h ▸ hC₁sub haC₁)
  have hcpb : f sp ≠ b := fun h => hcpC (h ▸ hC₂sub hbC₂)
  have hdpa : f tp ≠ a := fun h => hdpC (h ▸ hC₁sub haC₁)
  have hdpb : f tp ≠ b := fun h => hdpC (h ▸ hC₂sub hbC₂)
  have hcpdp : f sp ≠ f tp := fun h => hL₅L₄ (f tp) htpL₅ (h ▸ hspSeg)
  -- ## Cutting the four branches
  obtain ⟨A₁, A₂, hA₁, hA₂, hAcov, hAmeet⟩ :=
    harc₁.exists_split haC₁ (hne_mid a hai).1 (hne_mid a hai).2
  obtain ⟨B₁, B₂, hB₁, hB₂, hBcov, hBmeet⟩ :=
    harc₂.exists_split hbC₂ (hne_mid b hbi).1 (hne_mid b hbi).2
  obtain ⟨E₁, E₂, hE₁, hE₂, hEcov, hEmeet⟩ := hL₅arc.exists_split htpL₅ hp₁dp.symm hp₂dp.symm
  obtain ⟨D₁, D₂, hD₁, hD₂, hDcov, hDmeet⟩ :=
    (isArcBetween_segment hab_ne).exists_split hspSeg hcpa hcpb
  have hA₁sub : A₁ ⊆ C₁ := by rw [← hAcov]; exact subset_union_left
  have hA₂sub : A₂ ⊆ C₁ := by rw [← hAcov]; exact subset_union_right
  have hB₁sub : B₁ ⊆ C₂ := by rw [← hBcov]; exact subset_union_left
  have hB₂sub : B₂ ⊆ C₂ := by rw [← hBcov]; exact subset_union_right
  have hE₁sub : E₁ ⊆ L₅ := by rw [← hEcov]; exact subset_union_left
  have hE₂sub : E₂ ⊆ L₅ := by rw [← hEcov]; exact subset_union_right
  have hD₁sub : D₁ ⊆ segment ℝ a b := by rw [← hDcov]; exact subset_union_left
  have hD₂sub : D₂ ⊆ segment ℝ a b := by rw [← hDcov]; exact subset_union_right
  -- ## The remaining pairwise intersections
  have hbC₁ : b ∉ C₁ := by
    intro hcon
    have hmem : b ∈ C₁ ∩ C₂ := ⟨hcon, hbC₂⟩
    rw [hCmeet] at hmem
    rcases hmem with h | h
    exacts [(hne_mid b hbi).1 h, (hne_mid b hbi).2 h]
  have haC₂ : a ∉ C₂ := by
    intro hcon
    have hmem : a ∈ C₁ ∩ C₂ := ⟨haC₁, hcon⟩
    rw [hCmeet] at hmem
    rcases hmem with h | h
    exacts [(hne_mid a hai).1 h, (hne_mid a hai).2 h]
  have hC₁L₄ : ∀ z ∈ C₁, z ∈ segment ℝ a b → z = a := by
    intro z h1 h2
    rcases hsegC z h2 (hC₁sub h1) with h | h
    exacts [h, absurd (h ▸ h1) hbC₁]
  have hC₂L₄ : ∀ z ∈ C₂, z ∈ segment ℝ a b → z = b := by
    intro z h1 h2
    rcases hsegC z h2 (hC₂sub h1) with h | h
    exacts [absurd (h ▸ h1) haC₂, h]
  -- ## The configuration is a subdivision of `K(3,3)`, which the plane cannot carry
  -- The bipartition is `{p₁, p₂, c'}` against `{a, b, d'}`, with `c' = f sp` and `d' = f tp`.
  -- Row `i`, column `j` of `P` is the branch path from the `i`-th point of the first side to
  -- the `j`-th point of the second: the halves of `C₁`, `C₂` and `L₅` in rows `0` and `1`, the
  -- two halves of the chord `L₄` and the connecting arc `L₆` in row `2`.
  refine (Graph.isArcK33_of_pieces (x := ![p₁, p₂, f sp]) (y := ![a, b, f tp])
    (P := ![![A₁, B₁, E₁], ![A₂, B₂, E₂], ![D₁, D₂, L₆]])
    (Ch := ![C₁, C₂, L₅]) (Sg := ![segment ℝ a b, segment ℝ a b, L₆])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).elim
  · intro r c
    fin_cases r <;> fin_cases c
    exacts [hA₁, hB₁, hE₁, hA₂.reverse, hB₂.reverse, hE₂.reverse, hD₁.reverse, hD₂, hL₆arc]
  · exact injective_three hp₁p₂ hp₁cp hp₂cp
  · exact injective_three hab_ne hdpa.symm hdpb.symm
  · intro r c
    fin_cases r <;> fin_cases c
    exacts [hp₁a, hp₁b, hp₁dp, hp₂a, hp₂b, hp₂dp, hcpa, hcpb, hcpdp]
  · intro c; fin_cases c
    exacts [hA₁sub, hB₁sub, hE₁sub]
  · intro c; fin_cases c
    exacts [hA₂sub, hB₂sub, hE₂sub]
  · intro c; fin_cases c
    exacts [hD₁sub, hD₂sub, subset_rfl]
  · intro c; fin_cases c
    exacts [hAmeet.subset, hBmeet.subset, hEmeet.subset]
  · intro c e hne
    fin_cases c <;> fin_cases e
    · exact absurd rfl hne
    · exact hCmeet.subset
    · rintro z ⟨h1, h2⟩; exact hL₅C z h2 (hC₁sub h1)
    · rintro z ⟨h1, h2⟩; exact hCmeet.subset ⟨h2, h1⟩
    · exact absurd rfl hne
    · rintro z ⟨h1, h2⟩; exact hL₅C z h2 (hC₂sub h1)
    · rintro z ⟨h1, h2⟩; exact hL₅C z h1 (hC₁sub h2)
    · rintro z ⟨h1, h2⟩; exact hL₅C z h1 (hC₂sub h2)
    · exact absurd rfl hne
  · intro c e
    fin_cases c <;> fin_cases e
    · rintro z ⟨h1, h2⟩; exact hC₁L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact hC₁L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact absurd (hC₁sub h1) (hL₆C z h2)
    · rintro z ⟨h1, h2⟩; exact hC₂L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact hC₂L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact absurd (hC₂sub h1) (hL₆C z h2)
    · rintro z ⟨h1, h2⟩; exact absurd h2 (hL₅L₄ z h1)
    · rintro z ⟨h1, h2⟩; exact absurd h2 (hL₅L₄ z h1)
    · rintro z ⟨h1, h2⟩; exact hL₆L₅ z h2 h1
  · intro c e hne
    fin_cases c <;> fin_cases e
    · exact absurd rfl hne
    · exact hDmeet.subset
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h2 (hD₁sub h1)
    · rintro z ⟨h1, h2⟩; exact hDmeet.subset ⟨h2, h1⟩
    · exact absurd rfl hne
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h2 (hD₂sub h1)
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h1 (hD₁sub h2)
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h1 (hD₂sub h2)
    · exact absurd rfl hne

/-! ### The headline -/

/-- A Jordan curve carries two distinct points: the loop parametrising it is injective on
`[0, 1)`, which has two distinct points. -/
theorem IsJordanCurve.exists_ne {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v := by
  obtain ⟨g, hg, rfl⟩ := hC
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨g 0, mem_image_of_mem g zero_mem_I, g (1 / 2),
    mem_image_of_mem g ⟨by norm_num, by norm_num⟩, fun hcon => ?_⟩
  have := hg.injOn h0 hh hcon
  norm_num at this

/-- **Proposition 3.2 (a Jordan curve separates the plane).** The complement of a Jordan curve
is not preconnected.

The direction hypothesis of `not_isPreconnected_compl_of_coord` is discharged here: the curve
has two distinct points, so they differ in one of the two coordinates, and that coordinate
plays the role of the blueprint's horizontal one. No rotation is performed — the proof is run
for whichever coordinate projection has nonzero width, with the two coordinate indices carried
as parameters. -/
theorem IsJordanCurve.not_isPreconnected_compl {C : Set Plane} (hC : IsJordanCurve C) :
    ¬ IsPreconnected Cᶜ := by
  obtain ⟨u, hu, v, hv, huv⟩ := hC.exists_ne
  have hk : ∃ k : Fin 2, u k ≠ v k := by
    by_contra hcon
    push Not at hcon
    exact huv (by ext k; exact hcon k)
  obtain ⟨k, hk⟩ := hk
  fin_cases k
  · exact not_isPreconnected_compl_of_coord hC (i := 0) (j := 1) (by decide) hu hv hk
  · exact not_isPreconnected_compl_of_coord hC (i := 1) (j := 0) (by decide) hu hv hk

/-- **Proposition 3.2, in the form the Jordan curve theorem consumes**: the complement of a
Jordan curve has at least two connected components. Stated as two of its points lying in
different components, since that is what `thm:jordan` starts from.

It is genuinely the same statement: a set all of whose points share one component *is* that
component, and a component is preconnected. -/
theorem IsJordanCurve.exists_connectedComponentIn_ne {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ u ∈ Cᶜ, ∃ v ∈ Cᶜ, connectedComponentIn Cᶜ u ≠ connectedComponentIn Cᶜ v := by
  by_contra hcon
  push Not at hcon
  -- The complement is nonempty: the empty set is preconnected, and this one is not.
  rcases eq_empty_or_nonempty Cᶜ with hempty | ⟨u, hu⟩
  · exact hC.not_isPreconnected_compl (hempty ▸ isPreconnected_empty)
  · have heq : Cᶜ = connectedComponentIn Cᶜ u := by
      refine subset_antisymm (fun v hv => ?_) (connectedComponentIn_subset _ _)
      rw [← hcon v hv u hu]
      exact mem_connectedComponentIn hv
    exact hC.not_isPreconnected_compl (by rw [heq]; exact isPreconnected_connectedComponentIn)

/-! ### The unbounded component

Cheap, and what `thm:jordan` needs to name the exterior: a compact set sits inside a square,
the outside of that square is connected and misses it, so the whole outside lies in one
component of the complement — the only unbounded one. -/

/-- **The unbounded component of the complement of a compact set.** It exists, it swallows the
outside of any square containing the set, and it is the only unbounded component. -/
theorem exists_unique_unbounded_connectedComponentIn_compl {C : Set Plane} (hC : IsCompact C) :
    ∃ base ∈ Cᶜ, ¬ Bornology.IsBounded (connectedComponentIn Cᶜ base) ∧
      ∀ z ∈ Cᶜ, ¬ Bornology.IsBounded (connectedComponentIn Cᶜ z) →
        connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ base := by
  obtain ⟨r, -, hr⟩ := hC.exists_closedSquare
  have hbeyond : beyondSquare r ⊆ Cᶜ := by
    rw [beyondSquare_eq_compl]; exact compl_subset_compl.mpr hr
  obtain ⟨base, hbase⟩ : (beyondSquare r).Nonempty := (isConnected_beyondSquare r).nonempty
  -- The outside of the square is preconnected and inside the complement, so it lies in the
  -- single component named by any of its points.
  have hsub : beyondSquare r ⊆ connectedComponentIn Cᶜ base :=
    (isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hbase hbeyond
  refine ⟨base, hbeyond hbase, fun hb => Graph.not_isBounded_beyondSquare r (hb.subset hsub), ?_⟩
  intro z hz hzu
  -- An unbounded component escapes the square, so it meets the outside, so it is that one.
  obtain ⟨w, hw1, hw2⟩ : ∃ w, w ∈ connectedComponentIn Cᶜ z ∧ w ∈ beyondSquare r := by
    by_contra hcon
    push Not at hcon
    refine hzu ((Graph.isBounded_closedSquare r).subset fun w hw => ?_)
    by_contra hout
    exact hcon w hw (by rw [beyondSquare_eq_compl]; exact hout)
  rw [connectedComponentIn_eq hw1, connectedComponentIn_eq (hsub hw2)]

end Schoenflies
end

section
-- module Solutions.Q146_CD.Jordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Jordan curve theorem

The complement of a Jordan curve has exactly two regions, one bounded and one unbounded, and
both have the curve as their boundary. That is `Schoenflies.IsSeparating C` — the very
predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes for a polygon — so every consumer of
the polygonal case applies verbatim to the general one, `inside C` and `outside C` included.

Everything here takes one hypothesis, carried explicitly through every statement
that needs it:

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

which is `thm:arc-complement`, the complement of a simple arc is connected. Nothing else is
assumed; in particular no part of `thm:jordan` itself is.

## The two theorems

`lem:accessible-dense` (`Schoenflies.accessible_dense`) says the points of `C` reachable from a
fixed `x ∉ C` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. Its proof
is the blueprint's: delete a small open subarc `J₀`, leaving a simple arc whose complement is
connected by `harc`; join `x` there to a point of another component of `Cᶜ`; the joining chain
must cross `C`, and it can only do so inside `J₀`.

`thm:jordan` (`Schoenflies.IsJordanCurve.isSeparating`) then needs "at most two components",
which is `Schoenflies.not_three_components`, and the boundary clause, which is
`lem:accessible-dense` again: an accessible point is a limit of the region it is accessible
from, so `C` lies in the closure of each region and, being disjoint from both, in each
frontier.

## Three places where this departs from the blueprint's route

**The first meeting is taken on a vertex list, not on a parametrisation.**
`Schoenflies.exists_first_meeting` recurses on the list: on the first segment the first hit is
the infimum of the hitting parameters, and if the first segment misses the obstacle it is
swallowed by the component of the start and the recursion moves on. It returns the *initial
chain*, so both consumers — the accessibility of the meeting point, and the third branch of a
tripod — read off the same lemma.

**The tripod is built without a graph.** The blueprint overlays the three access arcs
(`lem:polygonal-overlay`), takes a minimal connected spanning subgraph, and extracts its unique
degree-three vertex by `lem:three-leaf-tree`. `Schoenflies.exists_tripod` instead joins the
first two terminals by a crosscut (`lem:accessible-endpoints`), runs a chain from the third
terminal to that crosscut, and takes the first meeting: that meeting point *is* the branch
vertex, and cutting the crosscut there (`IsArcBetween.exists_split`) gives the other two
branches. Neither `Schoenflies.polygonal_overlay` nor `Graph.IsTree.three_leaves` is used.

**The nine terminals are chosen in nine prescribed parameter windows.** The blueprint chooses
them distinct — proving that a dense set meets a nonempty relatively open subarc infinitely
often — and then *orders* the three on each closed arc `Q_j` to find the middle one `y_j`.
`Schoenflies.exists_windows` supplies nine pairwise separated windows inside `(0,1)`, in three
blocks of three; distinctness is then disjointness of the windows, the middle terminal of a
block is always the one with row index `1`, and no order on the curve is ever constructed. The
blueprint's `Q_j` never appears: only the parameter blocks `[t 0 j, t 2 j]` do.

## Blueprint

* `Schoenflies.exists_first_meeting_segment`, `Schoenflies.exists_first_meeting`,
  `Schoenflies.exists_arc_to_first_meeting`, `Schoenflies.polyAccessible_first_meeting` — the
  first-meeting machinery `lem:accessible-dense` and `thm:jordan` both run on. General enough
  to be hoisted if a second module needs it.
* `Schoenflies.PolyAccessible.mem_closure` — an accessible point of `∂Ω` lies in `closure Ω`.
* `Schoenflies.IsLoop.compl_openArc` — `lem:jordan-circle` in the form used here: the curve
  minus an open subarc is the complementary closed arc.
* `Schoenflies.exists_polyAccessible_openArc`, `Schoenflies.accessible_dense` —
  `lem:accessible-dense`, in the parameter form the proof produces and in the closure form.
* `Schoenflies.exists_tripod` — the three internally disjoint branches of the blueprint's
  `T_i`, at the H5 step of `thm:jordan`.
* `Schoenflies.exists_windows`, `Schoenflies.uIcc_inter_uIcc_mid` — the choice of the nine
  terminals and the middle-point bookkeeping that replaces "order `p_{1j}, p_{2j}, p_{3j}`
  along `Q_j`".
* `Schoenflies.not_three_components` — the `K(3,3)` half of `thm:jordan`, through
  `Graph.IsArcK33.elim` (`cor:k33-subdivision`).
* `Schoenflies.subset_closure_of_accessible_dense`, `Schoenflies.IsJordanCurve.isSeparating` —
  `thm:jordan`.
-/

open Bornology Metric Set unitInterval

namespace Schoenflies

variable {C S U Ω : Set Plane} {u v : Plane}

/-! ### The first meeting of a polygonal chain with a closed set

A chain that starts off a closed obstacle `S` and eventually hits it has a *first* hit, and
the piece of the chain before it never leaves the component of `U` its start lies in. This is
the only reason `lem:accessible-dense` produces an *accessible* point rather than merely a
point of the curve, and it is proved by structural recursion on the vertex list: on the first
segment the first hit is the infimum of the hitting parameters, and if the first segment
misses `S` the segment itself is swallowed by the component and the recursion moves on. -/

/-- **The first meeting on a single segment.** The parameter interval of the hits is closed and
bounded below, so it has a least element; before it the segment stays in `U`, hence in the
component of `U` carrying the near endpoint. -/
theorem exists_first_meeting_segment (hS : IsClosed S) (hUS : Disjoint U S) (hu : u ∈ U)
    (hsub : segment ℝ u v ⊆ U ∪ S) (hmeet : (segment ℝ u v ∩ S).Nonempty) :
    ∃ p ∈ segment ℝ u v ∩ S, segment ℝ u p ⊆ segment ℝ u v ∧
      segment ℝ u p \ {p} ⊆ connectedComponentIn U u := by
  set φ : ℝ → Plane := fun t => u + t • (v - u) with hφ
  have hcont : Continuous φ := by fun_prop
  have hseg : segment ℝ u v = φ '' Icc 0 1 := segment_eq_image' ℝ u v
  -- The parameters at which the segment sits on the obstacle.
  set T : Set ℝ := Icc 0 1 ∩ φ ⁻¹' S with hT
  have hTclosed : IsClosed T := isClosed_Icc.inter (hS.preimage hcont)
  have hTne : T.Nonempty := by
    obtain ⟨z, hz, hzS⟩ := hmeet
    rw [hseg] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, hzS⟩
  have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
  set t₀ : ℝ := sInf T with ht₀
  have ht₀T : t₀ ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht₀I : t₀ ∈ Icc (0 : ℝ) 1 := ht₀T.1
  have ht₀S : φ t₀ ∈ S := ht₀T.2
  -- The infimum is positive: the near endpoint is off the obstacle.
  have ht₀pos : 0 < t₀ := by
    rcases ht₀I.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hmem : φ 0 ∈ S := by rw [h]; exact ht₀S
      have hu' : φ 0 = u := by simp [hφ]
      rw [hu'] at hmem
      exact hUS.ne_of_mem hu hmem rfl
  -- Before the infimum the segment misses the obstacle, so it lies in `U`.
  have hbefore : φ '' Ico 0 t₀ ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans ht₀I.2⟩
    have : φ t ∉ S := fun hcon => absurd (csInf_le hTbdd ⟨htI, hcon⟩) (not_le.2 ht.2)
    exact (hsub (hseg ▸ mem_image_of_mem φ htI)).resolve_right this
  have hcomp : φ '' Ico 0 t₀ ⊆ connectedComponentIn U u := by
    refine (isPreconnected_Ico.image φ hcont.continuousOn).subset_connectedComponentIn ?_ hbefore
    exact ⟨0, ⟨le_rfl, ht₀pos⟩, by simp [hφ]⟩
  refine ⟨φ t₀, ⟨hseg ▸ mem_image_of_mem φ ht₀I, ht₀S⟩, ?_, ?_⟩
  · -- The initial piece of the segment is a piece of the segment.
    rw [segment_eq_image' ℝ u (φ t₀), hseg]
    rintro z ⟨θ, hθ, rfl⟩
    refine ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, ?_⟩, ?_⟩
    · nlinarith [hθ.1, hθ.2, ht₀I.1, ht₀I.2]
    · simp only [hφ, add_sub_cancel_left, smul_smul]
  · rintro z ⟨hz, hzne⟩
    rw [mem_singleton_iff] at hzne
    rw [segment_eq_image' ℝ u (φ t₀)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    replace hzne : u + θ • (φ t₀ - u) ≠ φ t₀ := hzne
    change u + θ • (φ t₀ - u) ∈ connectedComponentIn U u
    have hzeq : u + θ • (φ t₀ - u) = φ (θ * t₀) := by
      simp only [hφ, add_sub_cancel_left, smul_smul]
    rw [hzeq] at hzne ⊢
    -- The excluded point is exactly the parameter `1`, so the rest is strictly below `t₀`.
    have hθ1 : θ < 1 := by
      rcases hθ.2.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [h, one_mul]) hzne
    exact hcomp ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, by nlinarith⟩, rfl⟩

/-- **The first meeting of a polygonal chain with a closed set.** A chain that starts in `U`,
runs inside `U ∪ S` and meets the closed set `S` has an initial piece — again a chain from the
same start — that reaches `S` exactly at its far end and otherwise stays inside the *component*
of `U` carrying the start.

The chain is returned as `u :: ws`, so that "same start" is definitional and no
`List.head` obligation is ever produced. -/
theorem exists_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) :
    ∀ (u : Plane) (vs : List Plane), u ∈ U → poly (u :: vs) ⊆ U ∪ S →
      (poly (u :: vs) ∩ S).Nonempty →
      ∃ (ws : List Plane) (p : Plane), p ∈ poly (u :: vs) ∩ S ∧
        poly (u :: ws) ⊆ poly (u :: vs) ∧
        (u :: ws).getLast (List.cons_ne_nil u ws) = p ∧
        poly (u :: ws) \ {p} ⊆ connectedComponentIn U u
  | u, [], hu, _, hmeet => by
      -- A one-vertex chain carries only its vertex, which is in `U` and so off `S`.
      obtain ⟨z, hz, hzS⟩ := hmeet
      rw [poly_singleton, mem_singleton_iff] at hz
      exact absurd (hz ▸ hzS) (fun h => hUS.ne_of_mem hu h rfl)
  | u, v :: rest, hu, hsub, hmeet => by
      rw [poly_cons_cons] at hsub hmeet ⊢
      by_cases hfirst : (segment ℝ u v ∩ S).Nonempty
      · -- The obstacle is met already on the first segment.
        obtain ⟨p, hp, hpsub, hpcomp⟩ :=
          exists_first_meeting_segment hS hUS hu (hsub.trans' subset_union_left) hfirst
        exact ⟨[p], p, ⟨Or.inl hp.1, hp.2⟩, by rw [poly_pair]; exact hpsub.trans subset_union_left,
          rfl, by rw [poly_pair]; exact hpcomp⟩
      · -- The first segment misses the obstacle, so it is swallowed by the component.
        rw [not_nonempty_iff_eq_empty] at hfirst
        have hempty : ∀ z, z ∈ segment ℝ u v → z ∉ S := fun z hz hzS =>
          Set.eq_empty_iff_forall_notMem.1 hfirst z ⟨hz, hzS⟩
        have hsegU : segment ℝ u v ⊆ U := fun z hz =>
          (hsub (Or.inl hz)).resolve_right (hempty z hz)
        have hsegcomp : segment ℝ u v ⊆ connectedComponentIn U u :=
          (convex_segment u v).isPreconnected.subset_connectedComponentIn
            (left_mem_segment ℝ u v) hsegU
        have hvU : v ∈ U := hsegU (right_mem_segment ℝ u v)
        have hvcomp : connectedComponentIn U v = connectedComponentIn U u :=
          (connectedComponentIn_eq (hsegcomp (right_mem_segment ℝ u v))).symm
        have hrestsub : poly (v :: rest) ⊆ U ∪ S := hsub.trans' subset_union_right
        have hrestmeet : (poly (v :: rest) ∩ S).Nonempty := by
          obtain ⟨z, hz, hzS⟩ := hmeet
          rcases hz with hz | hz
          · exact absurd hzS (hempty z hz)
          · exact ⟨z, hz, hzS⟩
        obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ :=
          exists_first_meeting hS hUS v rest hvU hrestsub hrestmeet
        refine ⟨v :: ws, p, ⟨Or.inr hp.1, hp.2⟩, ?_, ?_, ?_⟩
        · rw [poly_cons_cons]
          exact union_subset_union_right _ hwsub
        · rw [List.getLast_cons (List.cons_ne_nil v ws)]; exact hwlast
        · rw [poly_cons_cons]
          rintro z ⟨hz | hz, hzne⟩
          · exact hsegcomp hz
          · exact hvcomp ▸ hwcomp ⟨hz, hzne⟩

/-- **The first meeting, as a simple arc.** The initial piece of the chain is re-extracted as a
*simple polygonal arc* from the first meeting point back to the start; it meets `S` only at
that point, and everything else on it stays in the component of `U` carrying the start.

This is the form both consumers want: `lem:accessible-dense` reads off the accessibility of `p`,
and the tripod construction of `thm:jordan` needs the arc itself. -/
theorem exists_arc_to_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P p u ∧
      P ⊆ poly (u :: vs) ∧ P \ {p} ⊆ connectedComponentIn U u := by
  obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hne : (u :: ws) ≠ [] := List.cons_ne_nil u ws
  have hpY : p ∈ poly (u :: ws) := hwlast ▸ getLast_mem_poly hne
  have huY : u ∈ poly (u :: ws) := head_mem_poly hne
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  obtain ⟨qs, hqs, hqhead, hqlast, hqsub, hqcomp, hqarc⟩ :=
    exists_simple_poly_of_isPolygonal_pinned ⟨u :: ws, rfl⟩ (isConnected_poly hne).2 hpu hpY huY
      hwcomp
  exact ⟨p, hp, poly qs, ⟨qs, rfl⟩, hqarc, hqsub.trans hwsub, hqcomp⟩

/-- The accessibility statement `lem:accessible-dense` produces: the first meeting point is
polygonally accessible from the component of `U` the chain started in. -/
theorem polyAccessible_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, PolyAccessible (connectedComponentIn U u) p := by
  obtain ⟨ws, p, hp, -, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  exact ⟨p, hp, polyAccessible_of_poly' (List.cons_ne_nil u ws) hwlast
    (fun hcon => hpu hcon.symm) hwcomp⟩

/-! ### An accessible point is a limit of the region

The half of `thm:jordan`'s boundary clause that `lem:accessible-dense` supplies: an accessible
point of the curve is in the closure of the region it is accessible from. The access chain is
connected and carries a point of the region, so the accessible point is not isolated on it. -/

/-- **An accessible point off the region lies in its closure.** -/
theorem PolyAccessible.mem_closure {a : Plane} (h : PolyAccessible Ω a) (ha : a ∉ Ω) :
    a ∈ closure Ω := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  refine closure_mono hint ?_
  have haY : a ∈ poly vs := hhead ▸ head_mem_poly hvs
  have hzY : vs.getLast hvs ∈ poly vs := getLast_mem_poly hvs
  have hzne : vs.getLast hvs ≠ a := fun hcon => ha (hcon ▸ hlast)
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- Were `a` isolated on the chain, the ball around it and the complement of `{a}` would
  -- split the chain into two nonempty relatively open pieces — but the chain is connected.
  obtain ⟨w, hwY, hwball, hwne⟩ :=
    (isConnected_poly hvs).2 (Metric.ball a ε) {a}ᶜ Metric.isOpen_ball isOpen_compl_singleton
      (fun z _ => by
        rcases eq_or_ne z a with rfl | hza
        · exact Or.inl (Metric.mem_ball_self hε)
        · exact Or.inr hza)
      ⟨a, haY, Metric.mem_ball_self hε⟩ ⟨vs.getLast hvs, hzY, hzne⟩
  have := hcon w ⟨hwY, hwne⟩
  rw [Metric.mem_ball, dist_comm] at hwball
  exact absurd hwball (not_lt.2 this)

/-! ### The curve with an open subarc deleted

`lem:jordan-circle`'s "two points cut the curve into two arcs" in the form
`lem:accessible-dense` consumes it: the complement *in the curve* of a relatively open subarc
is one closed arc. The proof is the parameter bookkeeping of `Schoenflies/TwoArcs.lean` — no
new topology. -/

/-- **The curve minus an open subarc is the complementary closed arc.** -/
theorem IsLoop.compl_openArc {f : ℝ → Plane} (hf : IsLoop f) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a < b) :
    f '' I \ f '' Ioo a b = f '' Icc 0 a ∪ f '' Icc b 1 := by
  have halt1 : a < 1 := lt_of_lt_of_le hab hb.2
  have hmI : ∀ m ∈ Ioo a b, m ∈ I ∧ m ≠ 1 := fun m hm =>
    ⟨⟨ha.1.trans hm.1.le, hm.2.le.trans hb.2⟩, ne_of_lt (lt_of_lt_of_le hm.2 hb.2)⟩
  -- No parameter outside `(a, b)` carries a point of the open subarc.
  have hfront : ∀ s ∈ Icc (0 : ℝ) a, f s ∉ f '' Ioo a b := by
    rintro s hs ⟨m, hm, hms⟩
    have hsI : s ∈ I := ⟨hs.1, hs.2.trans ha.2⟩
    have hs1 : s ≠ 1 := ne_of_lt (lt_of_le_of_lt hs.2 halt1)
    have := hf.injective_before_finish (hmI m hm).1 hsI (hmI m hm).2 hs1 hms
    exact absurd (this ▸ hm.1) (not_lt.2 hs.2)
  have hback : ∀ t ∈ Icc b (1 : ℝ), f t ∉ f '' Ioo a b := by
    rintro t ht ⟨m, hm, hms⟩
    have htI : t ∈ I := ⟨hb.1.trans ht.1, ht.2⟩
    rcases eq_or_ne t 1 with rfl | ht1
    · -- The finish carries the start, and the start is strictly before the open subarc.
      have := hf.injective_before_finish (hmI m hm).1 zero_mem_I (hmI m hm).2 one_ne_zero.symm
        (hms.trans hf.closes.symm)
      exact absurd (this ▸ hm.1) (not_lt.2 ha.1)
    · have := hf.injective_before_finish (hmI m hm).1 htI (hmI m hm).2 ht1 hms
      exact absurd (this ▸ hm.2) (not_lt.2 ht.1)
  apply Subset.antisymm
  · rintro z ⟨⟨t, htI, rfl⟩, hz⟩
    rcases le_or_gt t a with h | h
    · exact mem_union_left _ (mem_image_of_mem f ⟨htI.1, h⟩)
    · rcases le_or_gt b t with h' | h'
      · exact mem_union_right _ (mem_image_of_mem f ⟨h', htI.2⟩)
      · exact absurd (mem_image_of_mem f (⟨h, h'⟩ : t ∈ Ioo a b)) hz
  · rintro z (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨mem_image_of_mem f ⟨hs.1, hs.2.trans ha.2⟩, hfront s hs⟩
    · exact ⟨mem_image_of_mem f ⟨hb.1.trans ht.1, ht.2⟩, hback t ht⟩

/-! ### Density of accessible points, `lem:accessible-dense`

The blueprint's proof verbatim: shrink the given relatively open arc to one whose closure is
inside it, delete it from the curve to leave a simple arc, join `x` to a point of another
component in the (connected) complement of that arc by a polygonal chain, and take the first
meeting of the chain with the curve.

The shrinking step is done on parameters. Instead of "an open arc `J₀` with closure inside
`J`" the statement below takes the open subarc `f '' Ioo a b` with `0 < a < b < 1`, which is
already strictly inside the parameter interval; every relatively open piece of the curve
contains such a subarc (`Schoenflies.basic_piece_inside_ball` supplies one inside any ball),
and that is all the blueprint's `J₀` is for. -/

/-- **`lem:accessible-dense`, in the parameter form the proof produces.** Every open subarc
strictly inside the parameter interval carries a point accessible from the component of `x`.

`harc` is `thm:arc-complement`: the complement of a simple arc is connected. -/
theorem exists_polyAccessible_openArc (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    {f : ℝ → Plane} (hf : IsLoop f) {x : Plane} (hx : x ∉ f '' I)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ p ∈ f '' Ioo a b, PolyAccessible (connectedComponentIn (f '' I)ᶜ x) p := by
  have hCurve : IsJordanCurve (f '' I) := ⟨f, hf, rfl⟩
  have haI : a ∈ I := ⟨ha.le, (hab.trans hb).le⟩
  have hbI : b ∈ I := ⟨(ha.trans hab).le, hb.le⟩
  -- The curve minus the open subarc is a simple arc, so its complement is connected.
  set D : Set Plane := f '' Icc 0 a ∪ f '' Icc b 1 with hD
  have hDeq : f '' I \ f '' Ioo a b = D := hf.compl_openArc haI hbI hab
  have hDarc : IsArc D :=
    (hf.outside_IsArcBetween haI hbI (ne_of_lt (hab.trans hb)) (ne_of_lt hb) hab).isArc
  have hDconn : IsConnected Dᶜ := harc D hDarc
  have hDopen : IsOpen Dᶜ := hDarc.isClosed.isOpen_compl
  have hDsub : D ⊆ f '' I := hDeq ▸ sdiff_subset
  have hxD : x ∈ Dᶜ := fun hcon => hx (hDsub hcon)
  -- A point in another component of the complement of the curve.
  obtain ⟨y, hyC, hyne⟩ : ∃ y ∈ (f '' I)ᶜ,
      connectedComponentIn (f '' I)ᶜ y ≠ connectedComponentIn (f '' I)ᶜ x := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hCurve.exists_connectedComponentIn_ne
    by_cases h : connectedComponentIn (f '' I)ᶜ u₁ = connectedComponentIn (f '' I)ᶜ x
    · exact ⟨u₂, hu₂, fun hcon => hne (h.trans hcon.symm)⟩
    · exact ⟨u₁, hu₁, h⟩
  have hyD : y ∈ Dᶜ := fun hcon => hyC (hDsub hcon)
  obtain ⟨vs, hvs, hvsub, hvhead, hvlast⟩ :=
    exists_poly_of_isPreconnected hDopen hDconn.isPreconnected hxD hyD
  -- Present the chain as one headed by `x`, which is what the first-meeting lemma consumes.
  have hlist : x :: vs.tail = vs := by rw [← hvhead]; exact List.cons_head_tail hvs
  have hsubC : poly (x :: vs.tail) ⊆ (f '' I)ᶜ ∪ f '' I := fun z _ => em' (z ∈ f '' I)
  have hmeet : (poly (x :: vs.tail) ∩ f '' I).Nonempty := by
    rw [hlist]
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    -- Otherwise the chain avoids the curve, so it lies in one component — but its two ends
    -- were chosen in different ones.
    have hsubcompl : poly vs ⊆ (f '' I)ᶜ := fun z hz hzC =>
      Set.eq_empty_iff_forall_notMem.1 hcon z ⟨hz, hzC⟩
    have hone := (isConnected_poly hvs).2.subset_connectedComponentIn
      (hvhead ▸ head_mem_poly hvs) hsubcompl
    exact hyne (connectedComponentIn_eq (hone (hvlast ▸ getLast_mem_poly hvs))).symm
  obtain ⟨p, hp, hacc⟩ :=
    polyAccessible_first_meeting hCurve.isClosed disjoint_compl_left hx hsubC hmeet
  rw [hlist] at hp
  refine ⟨p, ?_, hacc⟩
  -- The first meeting is off the deleted arc, so it lies on the open subarc.
  by_contra hcon
  exact absurd (hDeq ▸ (⟨hp.2, hcon⟩ : p ∈ f '' I \ f '' Ioo a b)) (hvsub hp.1)

/-- **`lem:accessible-dense` (density of accessible points).** The points of `C` reachable from
`x` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. -/
theorem accessible_dense (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) {x : Plane} (hx : x ∉ C) :
    C ⊆ closure {p | p ∈ C ∧ PolyAccessible (connectedComponentIn Cᶜ x) p} := by
  obtain ⟨f, hf, rfl⟩ := hC
  intro z hz
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨c, d, hzcd, hball⟩ := basic_piece_inside_ball hf.continuousOn hz hr
  obtain ⟨w, hw, -⟩ := hzcd
  -- Trim the basic piece to an open subarc strictly inside the parameter interval.
  have h1 : c < w := hw.1.1
  have h2 : w < d := hw.1.2
  have h3 : (0 : ℝ) ≤ w := hw.2.1
  have h4 : w ≤ 1 := hw.2.2
  have hαβ : max c 0 < min d 1 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by norm_num⟩⟩
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right c 0
  have hd1 : min d 1 ≤ 1 := min_le_right d 1
  have hct : c ≤ max c 0 := le_max_left c 0
  have hdt : min d 1 ≤ d := min_le_left d 1
  set a : ℝ := max c 0 + (min d 1 - max c 0) / 3 with hadef
  set b : ℝ := max c 0 + 2 * (min d 1 - max c 0) / 3 with hbdef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hb1 : b < 1 := by rw [hbdef]; linarith
  have hsub : Ioo a b ⊆ Ioo c d ∩ I := by
    rintro t ⟨ht1, ht2⟩
    rw [hadef] at ht1
    rw [hbdef] at ht2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨p, hpIoo, hacc⟩ := exists_polyAccessible_openArc harc hf hx ha0 hab hb1
  refine ⟨p, ⟨image_mono (hsub.trans inter_subset_right) hpIoo, hacc⟩, ?_⟩
  rw [dist_comm]
  exact hball (image_mono hsub hpIoo)

/-! ### The tripod at a component

The blueprint builds the three internally disjoint branches from `x_i` to the three terminals
by overlaying the three access arcs, taking a minimal connected spanning subgraph, and reading
off its unique degree-three vertex (`lem:three-leaf-tree`). The construction below reaches the
same object without a graph: join the first two terminals by a *crosscut* — a simple polygonal
arc meeting the curve exactly at its two endpoints (`lem:accessible-endpoints` in crosscut
form) — then run a chain from the third terminal into the region and on to a point of that
crosscut, and take its **first meeting** with the crosscut. That meeting point is the branch
vertex; cutting the crosscut there (`IsArcBetween.exists_split`) supplies the other two
branches.

The output is the same three internally disjoint arcs, with the same two properties every
later step uses: each meets the curve only at its terminal, and two of them meet only at the
branch vertex. -/

/-- **Three internally disjoint arcs from one point of a region to three accessible points of
its complementary set.** The blueprint's `T_i` with its three branches, for `Ω` the `i`-th
component and the three points the terminals `p_{ij}`. -/
theorem exists_tripod (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hdisj : Disjoint Ω C) {a b c : Plane} (haC : a ∈ C) (hbC : b ∈ C) (hcC : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) (hc : PolyAccessible Ω c) :
    ∃ x ∈ Ω, ∃ Ta Tb Tc : Set Plane,
      IsArcBetween Ta x a ∧ IsArcBetween Tb x b ∧ IsArcBetween Tc x c ∧
        Ta \ {a} ⊆ Ω ∧ Tb \ {b} ⊆ Ω ∧ Tc \ {c} ⊆ Ω ∧
        Ta ∩ Tb ⊆ {x} ∧ Ta ∩ Tc ⊆ {x} ∧ Tb ∩ Tc ⊆ {x} := by
  classical
  -- The crosscut from `a` to `b`.
  obtain ⟨ws, hws, hwhead, hwlast, hwΩ, hwarc, hwC⟩ :=
    exists_crosscut_of_polyAccessible hΩopen hΩconn hdisj hab haC hbC ha hb
  set A : Set Plane := poly ws with hA
  have hAclosed : IsClosed A := (isCompact_poly ws).isClosed
  have hcA : c ∉ A := fun hcon => by
    rcases (hwC ▸ (⟨hcon, hcC⟩ : c ∈ A ∩ C) : c ∈ ({a, b} : Set Plane)) with h | h
    exacts [hac h.symm, hbc h.symm]
  -- The access chain from `c`, continued inside `Ω` to an interior point of the crosscut.
  obtain ⟨cs, hcs, hchead, hclast, hcsub⟩ := hc
  obtain ⟨w, hwmem⟩ := hwarc.nonempty_diff
  have hwΩ' : w ∈ Ω := hwΩ hwmem
  obtain ⟨ls, hls, hlsub, hlhead, hllast⟩ :=
    exists_poly_of_isPreconnected hΩopen hΩconn hclast hwΩ'
  have hcatlist : cs ++ ls = cs ++ cs.getLast hcs :: ls.tail := by
    rw [← hlhead, List.cons_head_tail hls]
  have hcat : poly (cs ++ ls) = poly cs ∪ poly ls := by
    rw [hcatlist, poly_append hcs _ _ rfl, ← hlhead, List.cons_head_tail hls]
  -- The full chain starts at `c`, runs in `Ω ∪ {c}`, and reaches the crosscut.
  have hfullne : cs ++ ls ≠ [] := by simp [hcs]
  have hfullhead : (cs ++ ls).head hfullne = c := by
    rw [List.head_append_of_ne_nil hcs, hchead]
  have hfulllist : c :: (cs ++ ls).tail = cs ++ ls := by
    rw [← hfullhead]; exact List.cons_head_tail hfullne
  set U : Set Plane := (Ω ∪ {c}) \ A with hU
  have hUS : Disjoint U A := disjoint_sdiff_left
  have hcU : c ∈ U := ⟨Or.inr rfl, hcA⟩
  have hfullsub : poly (c :: (cs ++ ls).tail) ⊆ U ∪ A := by
    rw [hfulllist, hcat]
    rintro z hz
    have hzΩ : z ∈ Ω ∪ {c} := by
      rcases hz with hz | hz
      · rcases eq_or_ne z c with rfl | hzc
        · exact Or.inr rfl
        · exact Or.inl (hcsub ⟨hz, hzc⟩)
      · exact Or.inl (hlsub hz)
    rcases em (z ∈ A) with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hzΩ, h⟩
  have hfullmeet : (poly (c :: (cs ++ ls).tail) ∩ A).Nonempty := by
    rw [hfulllist, hcat]
    exact ⟨w, Or.inr (hllast ▸ getLast_mem_poly hls), hwmem.1⟩
  obtain ⟨x, hx, P, -, hParc, -, hPcomp⟩ :=
    exists_arc_to_first_meeting hAclosed hUS hcU hfullsub hfullmeet
  rw [hfulllist, hcat] at hx
  -- The branch vertex is interior to the crosscut.
  have hxU : ∀ z ∈ P, z ≠ x → z ∈ U := fun z hz hzx =>
    connectedComponentIn_subset _ _ (hPcomp ⟨hz, hzx⟩)
  have hxΩ : x ∈ Ω := by
    rcases hx.1 with hz | hz
    · rcases eq_or_ne x c with rfl | hxc
      · exact absurd hx.2 hcA
      · exact hcsub ⟨hz, hxc⟩
    · exact hlsub hz
  have hPC : P ∩ C = {c} := by
    apply Subset.antisymm
    · rintro z ⟨hzP, hzC⟩
      rcases eq_or_ne z x with rfl | hzx
      · exact absurd rfl (hdisj.ne_of_mem hxΩ hzC)
      · rcases (hxU z hzP hzx).1 with h | h
        · exact absurd rfl (hdisj.ne_of_mem h hzC)
        · exact h
    · rintro z rfl; exact ⟨hParc.right_mem, hcC⟩
  have hPΩ : P \ {c} ⊆ Ω := by
    rintro z ⟨hzP, hzc⟩
    rcases eq_or_ne z x with rfl | hzx
    · exact hxΩ
    · exact ((hxU z hzP hzx).1).resolve_right hzc
  have hPA : P ∩ A ⊆ {x} := by
    rintro z ⟨hzP, hzA⟩
    by_contra hzx
    exact (hxU z hzP (fun h => hzx (by rw [h]; rfl))).2 hzA
  -- Cut the crosscut at the branch vertex.
  have hxa : x ≠ a := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ haC) rfl
  have hxb : x ≠ b := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ hbC) rfl
  obtain ⟨A₁, A₂, hA₁, hA₂, hAcov, hAmeet⟩ := hwarc.exists_split hx.2 hxa hxb
  have hbA₁ : b ∉ A₁ := fun hcon => hxb (by
    have : b ∈ A₁ ∩ A₂ := ⟨hcon, hA₂.right_mem⟩
    rw [hAmeet] at this; exact this.symm)
  have haA₂ : a ∉ A₂ := fun hcon => hxa (by
    have : a ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hcon⟩
    rw [hAmeet] at this; exact this.symm)
  have hAΩ : A \ {a, b} ⊆ Ω := hwΩ
  refine ⟨x, hxΩ, A₁, A₂, P, hA₁.reverse, hA₂, hParc, ?_, ?_, hPΩ, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hza⟩
    refine hAΩ ⟨hAcov ▸ mem_union_left _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [hza rfl, hbA₁ hz]
  · rintro z ⟨hz, hzb⟩
    refine hAΩ ⟨hAcov ▸ mem_union_right _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [haA₂ hz, hzb rfl]
  · exact hAmeet.subset
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_left _ hz.1⟩
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_right _ hz.1⟩

/-! ### Nine parameter windows

The blueprint chooses the nine terminals `p_{ij}` distinct and then *orders* the three on each
arc `Q_j` to find the middle one `y_j`. Choosing them in nine prescribed, pairwise separated
parameter windows does both jobs at once: distinctness is disjointness of the windows, and the
middle one is always the terminal of the middle index. No order on the curve is ever
constructed.

The windows are `((6j + 2i + 2)/24, (6j + 2i + 3)/24)`, which for `i, j < 3` are nine disjoint
intervals inside `(0, 1)`, ordered lexicographically by `(j, i)`. -/

/-! ### At most two components

The heart of `thm:jordan`. Three components would give three tripods, whose nine branches,
extended along the curve to the three middle terminals, are a plane `K(3,3)` subdivision —
excluded by `cor:k33-subdivision` (`Graph.IsArcK33.elim`). -/

/-- **Three points of the complement of a Jordan curve cannot lie in three distinct
components.** -/
theorem not_three_components (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) {q : Fin 3 → Plane} (hqC : ∀ i, q i ∉ C)
    (hqne : ∀ i k, i ≠ k → connectedComponentIn Cᶜ (q i) ≠ connectedComponentIn Cᶜ (q k)) :
    False := by
  classical
  obtain ⟨f, hf, rfl⟩ := hC
  have hCclosed : IsClosed (f '' I) := IsJordanCurve.isClosed ⟨f, hf, rfl⟩
  set Ω : Fin 3 → Set Plane := fun i => connectedComponentIn (f '' I)ᶜ (q i) with hΩdef
  have hΩopen : ∀ i, IsOpen (Ω i) := fun _ =>
    Plane.isOpen_connectedComponentIn hCclosed.isOpen_compl
  have hΩconn : ∀ i, IsPreconnected (Ω i) := fun _ => isPreconnected_connectedComponentIn
  have hΩdisj : ∀ i, Disjoint (Ω i) (f '' I) := fun i =>
    Set.disjoint_left.2 fun z hz => connectedComponentIn_subset _ _ hz
  have hΩij : ∀ i k, i ≠ k → Disjoint (Ω i) (Ω k) := by
    intro i k hik
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hqne i k hik ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm)
  -- Nine terminals, one per window, each accessible from its own component.
  obtain ⟨w, hw0, hw1, hwstep⟩ := exists_windows
  have key : ∀ i j : Fin 3, ∃ s : ℝ, s ∈ Ioo (w i j) (w i j + 1 / 24) ∧
      PolyAccessible (Ω i) (f s) := by
    intro i j
    obtain ⟨-, ⟨s, hs, rfl⟩, hacc⟩ :=
      exists_polyAccessible_openArc harc hf (hqC i) (hw0 i j)
        (by linarith : w i j < w i j + 1 / 24) (hw1 i j)
    exact ⟨s, hs, hacc⟩
  choose t ht hacc using key
  /- ### Parameter bookkeeping -/
  have hmono : ∀ i j k l : Fin 3, (j = l ∧ i.val < k.val) ∨ j.val < l.val → t i j < t k l :=
    fun i j k l h => lt_of_lt_of_le (ht i j).2 (le_trans (hwstep i j k l h) (ht k l).1.le)
  have htI : ∀ i j, t i j ∈ Ico (0 : ℝ) 1 :=
    fun i j => ⟨((hw0 i j).trans (ht i j).1).le, (ht i j).2.trans (hw1 i j)⟩
  have htI' : ∀ i j, t i j ∈ I := fun i j => ⟨(htI i j).1, (htI i j).2.le⟩
  have hle : ∀ i k j : Fin 3, i.val ≤ k.val → t i j ≤ t k j := by
    intro i k j h
    rcases h.lt_or_eq with h | h
    · exact (hmono i j k j (Or.inl ⟨rfl, h⟩)).le
    · rw [Fin.val_injective h]
  have htinj : ∀ i j k l : Fin 3, t i j = t k l → i = k ∧ j = l := by
    intro i j k l h
    rcases lt_trichotomy j.val l.val with hjl | hjl | hjl
    · exact absurd h (ne_of_lt (hmono i j k l (Or.inr hjl)))
    · have hjl' : j = l := Fin.val_injective hjl
      subst hjl'
      rcases lt_trichotomy i.val k.val with hik | hik | hik
      · exact absurd h (ne_of_lt (hmono i j k j (Or.inl ⟨rfl, hik⟩)))
      · exact ⟨Fin.val_injective hik, rfl⟩
      · exact absurd h.symm (ne_of_lt (hmono k j i j (Or.inl ⟨rfl, hik⟩)))
    · exact absurd h.symm (ne_of_lt (hmono k l i j (Or.inr hjl)))
  have hpC : ∀ i j, f (t i j) ∈ f '' I := fun i j => mem_image_of_mem f (htI' i j)
  have hpinj : ∀ i j k l : Fin 3, f (t i j) = f (t k l) → i = k ∧ j = l :=
    fun i j k l h => htinj i j k l (hf.injOn (htI i j) (htI k l) h)
  -- The block of parameters carrying the three terminals of one arc `Q_j`.
  have htM : ∀ i j : Fin 3, t i j ∈ Icc (t 0 j) (t 2 j) := fun i j =>
    ⟨hle 0 i j (Nat.zero_le _), hle i 2 j (Nat.lt_succ_iff.1 i.isLt)⟩
  have hMIco : ∀ (j : Fin 3), Icc (t 0 j) (t 2 j) ⊆ Ico (0 : ℝ) 1 := fun j s hs =>
    ⟨(htI 0 j).1.trans hs.1, lt_of_le_of_lt hs.2 (htI 2 j).2⟩
  have hMdisj : ∀ j l : Fin 3, j.val < l.val →
      ∀ s ∈ Icc (t 0 j) (t 2 j), ∀ s' ∈ Icc (t 0 l) (t 2 l), s < s' := fun j l h s hs s' hs' =>
    lt_of_le_of_lt hs.2 (lt_of_lt_of_le (hmono 2 j 0 l (Or.inr h)) hs'.1)
  /- ### The three arcs along the curve -/
  have hRparam : ∀ i j : Fin 3, uIcc (t i j) (t 1 j) ⊆ Icc (t 0 j) (t 2 j) := fun i j =>
    uIcc_subset_Icc (htM i j) (htM 1 j)
  have hRC : ∀ i j : Fin 3, f '' uIcc (t i j) (t 1 j) ⊆ f '' I := fun i j =>
    image_mono ((hRparam i j).trans ((hMIco j).trans Ico_subset_Icc_self))
  have hpR : ∀ i j : Fin 3, f (t i j) ∈ f '' uIcc (t i j) (t 1 j) := fun i j =>
    mem_image_of_mem f left_mem_uIcc
  have hRRdisj : ∀ i j k l : Fin 3, j ≠ l →
      f '' uIcc (t i j) (t 1 j) ∩ f '' uIcc (t k l) (t 1 l) = ∅ := by
    intro i j k l hjl
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨s, hs, rfl⟩, s', hs', hz'⟩
    have h1 : s ∈ Icc (t 0 j) (t 2 j) := hRparam i j hs
    have h2 : s' ∈ Icc (t 0 l) (t 2 l) := hRparam k l hs'
    have hss : s' = s := hf.injOn (hMIco l h2) (hMIco j h1) hz'
    rw [hss] at h2
    rcases lt_trichotomy j.val l.val with h | h | h
    · exact absurd (hMdisj j l h s h1 s h2) (lt_irrefl s)
    · exact hjl (Fin.val_injective h)
    · exact absurd (hMdisj l j h s h2 s h1) (lt_irrefl s)
  have hRRmeet : ∀ i j k : Fin 3, i ≠ k →
      f '' uIcc (t i j) (t 1 j) ∩ f '' uIcc (t k j) (t 1 j) ⊆ {f (t 1 j)} := by
    intro i j k hik
    have hord : ∀ c e : Fin 3, c.val < e.val → t c j ≤ t 1 j ∧ t 1 j ≤ t e j := by
      intro c e h
      have he := e.isLt
      exact ⟨hle c 1 j (by omega), hle 1 e j (by omega)⟩
    rintro z ⟨⟨s, hs, rfl⟩, s', hs', hz'⟩
    have hss : s' = s := hf.injOn (hMIco j (hRparam k j hs')) (hMIco j (hRparam i j hs)) hz'
    subst hss
    rcases lt_trichotomy i.val k.val with h | h | h
    · exact mem_singleton_iff.2 (by
        rw [uIcc_inter_uIcc_mid (hord i k h).1 (hord i k h).2 ⟨hs, hs'⟩])
    · exact absurd (Fin.val_injective h) hik
    · exact mem_singleton_iff.2 (by
        rw [uIcc_inter_uIcc_mid (hord k i h).1 (hord k i h).2 ⟨hs', hs⟩])
  /- ### The three tripods -/
  have htri : ∀ i : Fin 3, ∃ xc : Plane, xc ∈ Ω i ∧ ∃ T : Fin 3 → Set Plane,
      (∀ j, IsArcBetween (T j) xc (f (t i j))) ∧ (∀ j, T j \ {f (t i j)} ⊆ Ω i) ∧
        (∀ j l, j ≠ l → T j ∩ T l ⊆ {xc}) := by
    intro i
    have hne : ∀ j l : Fin 3, j ≠ l → f (t i j) ≠ f (t i l) := fun j l hjl hcon =>
      hjl (hpinj i j i l hcon).2
    obtain ⟨xc, hxc, Ta, Tb, Tc, hTa, hTb, hTc, hTa', hTb', hTc', h01, h02, h12⟩ :=
      exists_tripod (hΩopen i) (hΩconn i) (hΩdisj i) (hpC i 0) (hpC i 1) (hpC i 2)
        (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
        (hacc i 0) (hacc i 1) (hacc i 2)
    refine ⟨xc, hxc, ![Ta, Tb, Tc], ?_, ?_, ?_⟩
    · intro j; fin_cases j <;> assumption
    · intro j; fin_cases j <;> assumption
    · intro j l hjl
      fin_cases j <;> fin_cases l <;>
        first
          | exact absurd rfl hjl
          | assumption
          | (rw [inter_comm]; assumption)
  choose xx hxxΩ TT hTTarc hTTsub hTTmeet using htri
  /- ### Assembling the `K(3,3)` -/
  have hTC : ∀ i j, TT i j ∩ f '' I = {f (t i j)} := by
    intro i j
    apply Subset.antisymm
    · rintro z ⟨hz1, hz2⟩
      by_contra hzne
      exact (hΩdisj i).ne_of_mem (hTTsub i j ⟨hz1, hzne⟩) hz2 rfl
    · rintro z rfl
      exact ⟨(hTTarc i j).right_mem, hpC i j⟩
  have hTR : ∀ i j k l : Fin 3, ∀ z ∈ TT i j, z ∈ f '' uIcc (t k l) (t 1 l) →
      z = f (t i j) ∧ f (t i j) ∈ f '' uIcc (t k l) (t 1 l) := by
    intro i j k l z hz hz'
    have hzp : z = f (t i j) := by
      have hmem : z ∈ TT i j ∩ f '' I := ⟨hz, hRC k l hz'⟩
      rw [hTC i j] at hmem
      exact hmem
    exact ⟨hzp, hzp ▸ hz'⟩
  have hTTdisj : ∀ i j k l : Fin 3, i ≠ k → TT i j ∩ TT k l = ∅ := by
    intro i j k l hik
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    rcases eq_or_ne z (f (t i j)) with rfl | h1
    · have hmem : f (t i j) ∈ TT k l ∩ f '' I := ⟨hz2, hpC i j⟩
      rw [hTC k l] at hmem
      exact hik (hpinj i j k l hmem).1
    · rcases eq_or_ne z (f (t k l)) with rfl | h2
      · have hmem : f (t k l) ∈ TT i j ∩ f '' I := ⟨hz1, hpC k l⟩
        rw [hTC i j] at hmem
        exact hik (hpinj k l i j hmem).1.symm
      · exact (hΩij i k hik).ne_of_mem (hTTsub i j ⟨hz1, h1⟩) (hTTsub k l ⟨hz2, h2⟩) rfl
  -- The nine branch paths: a tripod branch, continued along the curve to the middle terminal.
  have harcP : ∀ i j : Fin 3,
      IsArcBetween (TT i j ∪ f '' uIcc (t i j) (t 1 j)) (xx i) (f (t 1 j)) := by
    intro i j
    rcases eq_or_ne i 1 with rfl | hi1
    · -- The middle terminal *is* the terminal: the arc along the curve degenerates.
      have hdeg : f '' uIcc (t 1 j) (t 1 j) = {f (t 1 j)} := by
        rw [uIcc_self, image_singleton]
      rw [hdeg, union_eq_self_of_subset_right
        (singleton_subset_iff.2 (hTTarc 1 j).right_mem)]
      exact hTTarc 1 j
    · have hne : t i j ≠ t 1 j := fun hcon => hi1 (htinj i j 1 j hcon).1
      have harcR : IsArcBetween (f '' uIcc (t i j) (t 1 j)) (f (t i j)) (f (t 1 j)) :=
        isArcBetween_subarc hf.continuousOn
          (hf.injOn.mono ((hRparam i j).trans (hMIco j)))
          (htI' i j) (htI' 1 j) hne
      refine (hTTarc i j).concatenate harcR (fun z hz hz' => ?_)
      exact (hTR i j i j z hz hz').1
  refine (Graph.IsArcK33.elim (x := xx) (y := fun j => f (t 1 j))
    (P := fun i j => TT i j ∪ f '' uIcc (t i j) (t 1 j)) ?_)
  have hmeetHalf : ∀ i j k l : Fin 3, (i, j) ≠ (k, l) →
      (TT i j ∪ f '' uIcc (t i j) (t 1 j)) ∩ (TT k l ∪ f '' uIcc (t k l) (t 1 l)) ⊆
        ({xx i, f (t 1 j)} : Set Plane) := by
    rintro i j k l hne z ⟨hz1, hz2⟩
    have hRRne : ∀ c e d g : Fin 3, d ≠ g → f (t c d) ∈ f '' uIcc (t e g) (t 1 g) → False :=
      fun c e d g hdg hmem =>
        absurd (hRRdisj c d e g hdg) (Set.nonempty_iff_ne_empty.1 ⟨f (t c d), hpR c d, hmem⟩)
    rcases eq_or_ne i k with rfl | hik
    · have hjl : j ≠ l := fun h => hne (by rw [h])
      rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
      · exact Or.inl (hTTmeet i j l hjl ⟨hz1, hz2⟩)
      · exact absurd ((hTR i j i l z hz1 hz2).2) (fun h => hRRne i i j l hjl h)
      · exact absurd ((hTR i l i j z hz2 hz1).2) (fun h => hRRne i i l j (Ne.symm hjl) h)
      · exact absurd (hRRdisj i j i l hjl) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
    · rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
      · exact absurd (hTTdisj i j k l hik) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
      · obtain ⟨hzp, hmem⟩ := hTR i j k l z hz1 hz2
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (by rw [hzp]; exact hRRmeet i j k hik ⟨hpR i j, hmem⟩)
        · exact absurd hmem (fun h => hRRne i k j l hjl h)
      · obtain ⟨hzp, hmem⟩ := hTR k l i j z hz2 hz1
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (by rw [hzp]; exact hRRmeet k j i (Ne.symm hik) ⟨hpR k j, hmem⟩)
        · exact absurd hmem (fun h => hRRne k i l j (Ne.symm hjl) h)
      · rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (hRRmeet i j k hik ⟨hz1, hz2⟩)
        · exact absurd (hRRdisj i j k l hjl) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
  exact
    { arc := harcP
      x_injective := by
        intro i k hik
        by_contra hne
        exact (hΩij i k hne).ne_of_mem (hxxΩ i) (hik ▸ hxxΩ k) rfl
      y_injective := fun j l h => (hpinj 1 j 1 l h).2
      ne := fun i j hcon =>
        (hΩdisj i).ne_of_mem (hxxΩ i) (hcon ▸ hpC 1 j) rfl
      meet := fun i j k l hne =>
        subset_inter (hmeetHalf i j k l hne)
          (by rw [inter_comm]; exact hmeetHalf k l i j (Ne.symm hne)) }

/-! ### The Jordan curve theorem

Stated as `IsSeparating C`, the predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes in the polygonal case. Unfolding it,
that is exactly the blueprint's statement: `inside C` and `outside C` are each a single region,
one bounded and one unbounded (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`), and both have `C` as boundary. Every consumer written
against the polygonal case therefore applies verbatim. -/

/-- A point of the curve is in the closure of any region it is accessible from — the reverse
inclusion of the boundary clause, packaged for both regions at once. -/
theorem subset_closure_of_accessible_dense
    (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ) (hC : IsJordanCurve C) {x : Plane}
    (hx : x ∉ C) : C ⊆ closure (connectedComponentIn Cᶜ x) := by
  refine (accessible_dense harc hC hx).trans (closure_mono ?_) |>.trans closure_closure.subset
  rintro p ⟨hpC, hacc⟩
  exact hacc.mem_closure fun hcon => absurd hpC (connectedComponentIn_subset _ _ hcon)

/-- **`thm:jordan` (the Jordan curve theorem).** The complement of a Jordan curve has exactly
two regions, one bounded and one unbounded, and both have the curve as their boundary.

`harc` is `thm:arc-complement`. -/
theorem IsJordanCurve.isSeparating (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) : IsSeparating C := by
  have hCclosed : IsClosed C := hC.isClosed
  -- The unbounded region is the component of the outside of a large square.
  obtain ⟨base, hbase, hbaseub, hbaseuniq⟩ :=
    exists_unique_unbounded_connectedComponentIn_compl hC.isCompact
  have houtside : Schoenflies.outside C = connectedComponentIn Cᶜ base := by
    apply Subset.antisymm
    · intro z hz
      rw [← hbaseuniq z hz.1 hz.2]
      exact mem_connectedComponentIn hz.1
    · intro z hz
      refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
      rw [← connectedComponentIn_eq hz]
      exact hbaseub
  -- The complement has a bounded component too: at most one component is unbounded.
  obtain ⟨z₀, hz₀⟩ : (Schoenflies.inside C).Nonempty := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hC.exists_connectedComponentIn_ne
    by_cases h₁ : IsBounded (connectedComponentIn Cᶜ u₁)
    · exact ⟨u₁, hu₁, h₁⟩
    · by_cases h₂ : IsBounded (connectedComponentIn Cᶜ u₂)
      · exact ⟨u₂, hu₂, h₂⟩
      · exact absurd ((hbaseuniq u₁ hu₁ h₁).trans (hbaseuniq u₂ hu₂ h₂).symm) hne
  -- Any two points of the bounded part share a component: a third would give three.
  have hsame : ∀ z ∈ Schoenflies.inside C,
      connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ z₀ := by
    intro z hz
    by_contra hne
    -- `z`, `z₀` and the unbounded base would be three distinct components.
    refine not_three_components harc hC (q := ![z, z₀, base]) ?_ ?_
    · intro i; fin_cases i
      exacts [hz.1, hz₀.1, hbase]
    · have hzb : connectedComponentIn Cᶜ z ≠ connectedComponentIn Cᶜ base := fun hcon =>
        hbaseub (hcon ▸ hz.2)
      have hz₀b : connectedComponentIn Cᶜ z₀ ≠ connectedComponentIn Cᶜ base := fun hcon =>
        hbaseub (hcon ▸ hz₀.2)
      intro i k hik
      fin_cases i <;> fin_cases k <;>
        first
          | exact absurd rfl hik
          | exact hne
          | exact hzb
          | exact hz₀b
          | exact Ne.symm hne
          | exact Ne.symm hzb
          | exact Ne.symm hz₀b
  have hinside : Schoenflies.inside C = connectedComponentIn Cᶜ z₀ := by
    refine Subset.antisymm (fun z hz => ?_) (connectedComponentIn_subset_inside hz₀)
    rw [← hsame z hz]
    exact mem_connectedComponentIn hz.1
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · rw [hinside]
    exact ⟨⟨z₀, mem_connectedComponentIn hz₀.1⟩, isPreconnected_connectedComponentIn⟩
  · rw [houtside]
    exact ⟨⟨base, mem_connectedComponentIn hbase⟩, isPreconnected_connectedComponentIn⟩
  · apply Subset.antisymm
    · rw [hinside]; exact Plane.frontier_connectedComponentIn_compl_subset hCclosed z₀
    · rw [(Schoenflies.isOpen_inside hCclosed).frontier_eq]
      exact subset_sdiff.2 ⟨hinside ▸ subset_closure_of_accessible_dense harc hC hz₀.1,
        Set.disjoint_left.2 fun z hzC hzin => hzin.1 hzC⟩
  · apply Subset.antisymm
    · rw [houtside]; exact Plane.frontier_connectedComponentIn_compl_subset hCclosed base
    · rw [(Schoenflies.isOpen_outside hCclosed).frontier_eq]
      exact subset_sdiff.2 ⟨houtside ▸ subset_closure_of_accessible_dense harc hC hbase,
        Set.disjoint_left.2 fun z hzC hzout => hzout.1 hzC⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolyArcRealize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a simple polygonal arc as a `PolyArc`

`Schoenflies/ArcCollars.lean` proves blueprint Lemma 1.8 (b) — the two-sided collar of an arc,
hence `Schoenflies.HasArcCollars` — for an arc *presented by its vertex list*, a
`Schoenflies.PolyArc`, and carries the presentation itself as the hypothesis
`Schoenflies.IsPolyArcCarrier`. Nothing on `main` could supply that hypothesis for anything but
a straight segment, so `lem:crosscut-at-most-two` and `thm:general-crosscut` were not in fact
unblocked. This module closes the gap: a set that is both an arc between two points and
polygonal *is* the carrier of a `PolyArc`.

This is the arc analogue of `Schoenflies.exists_closedPolygon`, and the route is the one
`Schoenflies/Realization.lean` takes in the closed case, on a linear index instead of a cyclic
one. The closed-case machinery is reused verbatim wherever it does not mention the loop.

## The three steps

1. **Cut the point set into pieces.** `Schoenflies.exists_isClean` gives a finite list `Q` of
   nondegenerate segments occupying `P`, with pairwise disjoint interiors and no end interior to
   any of them; the two endpoints `a`, `b` of the arc are put on the cut list, so both are ends
   of pieces.
2. **Order the pieces along the arc.** The parametrisation `f` reaches an end of a piece at
   finitely many parameters; listed in increasing order they cut `[0, 1]` into gaps. A gap image
   is connected and misses the ends, so it lies in one piece interior; the interior is connected
   and covered by the closed gap images, so it lies in that one gap. Gaps and pieces correspond
   one to one and the ends, in the order `f` reaches them, are a *linear* vertex list.

   The only change from the closed case is bookkeeping at the far end. There the loop returns to
   `f 0`, so the parameters live in `[0, 1)` and the last gap wraps; here `f 1 = b` is a genuine
   extra vertex. Taking the parameter set to be `{t ∈ [0, 1) | f t` is an end of a piece`}` —
   *exactly* the set `Schoenflies/Realization.lean` uses — makes `Schoenflies.parNext` of the
   last index equal `1` by definition, which is precisely the missing right end. So
   `Schoenflies.par`, `Schoenflies.parNext` and `Schoenflies.exists_mem_gap` are used unchanged,
   and `n` parameters give `n` edges and `n + 1` vertices.
3. **Delete redundant vertices.** `Schoenflies.PreArc` is a `PolyArc` less its `corner` field,
   and `Schoenflies.PreArc.deleteVertex` removes one vertex at which the two edges are
   collinear. Each deletion shortens the list by one, so the induction terminates; unlike the
   cyclic case it can never get stuck, because a one-edge arc satisfies `corner` vacuously.

## Why the arc is not closed into a curve first

The tempting shortcut is to join `b` back to `a` by one extra polygonal path far from the arc,
apply `Schoenflies.exists_closedPolygon_arcs` to the resulting Jordan curve, and read the arc off
the cyclic list. It is circular. The return path has to meet `P` only at `a` and `b`, so it has
to leave `a` in a direction along which the arc does not run; knowing that there *is* such a
direction — that `P` is locally one segment at `a` — is a consequence of the realization, not an
input to it. A *straight* segment from `b` to `a` will not do either: an arc can perfectly well
cross the chord joining its endpoints. And avoiding `P` in the large needs `ℝ² ∖ P` connected,
which is `thm:arc-complement`, stated there with an explicit hypothesis. Route (A) below needs
none of this.

## Padding the vertex list

`PolyArc.vertex` is a function on all of `ℕ` asked to be *globally* injective — the convention
its docstring records, which supplies `A.tang i` and `A.len i` directly. A realization
produces `n + 1` vertices and nothing beyond, so the list has to be padded.
`Schoenflies.exists_injective_extend` does it once and for all, by walking off along the first
coordinate past every value the finite list takes.

## Blueprint

There is no blueprint label for this statement: like the closed-curve realization theorem of
`Schoenflies/Realization.lean` it is the bridge the blueprint takes for granted when it says
"let `P` be a simple polygonal arc with vertices `v_0, …, v_{n+1}`". Its consumers are
`lem:polygonal-collar` (b) and, through it, `lem:crosscut-at-most-two` and
`thm:general-crosscut`.

* `Schoenflies.exists_injective_extend` — a finite injective vertex list extends to an injective
  sequence.
* `Schoenflies.PreArc` — a `PolyArc` less the `corner` field: a simple polygonal arc presented by
  a vertex list, redundant vertices allowed. The arc analogue of `Schoenflies.PrePolygon`.
* `Schoenflies.skipIdx`, `Schoenflies.PreArc.deleteVertex`,
  `Schoenflies.PreArc.carrier_deleteVertex` — the blueprint's "delete redundant vertices at which
  two consecutive edges are collinear", as an operation. The arc analogue of
  `Schoenflies.PrePolygon.deleteLast`, and simpler: with a linear index no rotation is needed, so
  the vertex to be deleted stays where it is.
* `Schoenflies.PreArc.exists_polyArc` — the deletion run to completion. The arc analogue of
  `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.
* `Schoenflies.exists_preArc_of_isArcBetween` — steps 1 and 2: a set-level simple polygonal arc
  is the carrier of a vertex list. The arc analogue of
  `Schoenflies.exists_prePolygon_of_isJordanCurve`.
* `Schoenflies.isPolyArcCarrier_of_isPolygonal` — **the realization theorem for arcs**, and the
  discharge of `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.hasArcCollars_of_isPolygonal` — blueprint Lemma 1.8 (b) for a set-level simple
  polygonal arc, with nothing left standing.
* `Schoenflies.IsCrosscut.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_isPolygonal` — the
  same at the call site of `thm:general-crosscut`.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Padding a finite vertex list to an injective sequence

`PolyArc` asks for a globally injective `vertex : ℕ → Plane`; a realization only produces
`n + 2` points. The padding walks off along the first coordinate, past every value the finite
part takes, which keeps the extension injective and disjoint from the finite part. -/

/-- **A vertex list injective on an initial segment extends to an injective sequence.** This is
the padding convention `Schoenflies.PolyArc`'s docstring describes, supplied once. -/
theorem exists_injective_extend {N : ℕ} (v : ℕ → Plane)
    (hv : ∀ i < N, ∀ j < N, v i = v j → i = j) :
    ∃ w : ℕ → Plane, Function.Injective w ∧ ∀ k < N, w k = v k := by
  classical
  -- A bound on the first coordinates of the finite part.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k < N, v k 0 ≤ M := by
    obtain ⟨M, hM⟩ := ((Set.finite_lt_nat N).image fun k => v k 0).bddAbove
    exact ⟨M, fun k hk => hM ⟨k, hk, rfl⟩⟩
  refine ⟨fun k => if k < N then v k else Plane.mk (M + 1 + k) 0, ?_, fun k hk => by simp [hk]⟩
  intro k l hkl
  dsimp only at hkl
  by_cases hk : k < N <;> by_cases hl : l < N
  · rw [if_pos hk, if_pos hl] at hkl
    exact hv k hk l hl hkl
  · -- A listed point cannot equal a padded one: its first coordinate is too small.
    exfalso
    rw [if_pos hk, if_neg hl] at hkl
    have h1 : v k 0 = M + 1 + (l : ℝ) := by rw [hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h3 := hM k hk
    linarith
  · exfalso
    rw [if_neg hk, if_pos hl] at hkl
    have h1 : v l 0 = M + 1 + (k : ℝ) := by rw [← hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 := hM l hl
    linarith
  · rw [if_neg hk, if_neg hl] at hkl
    have h1 : M + 1 + (k : ℝ) = M + 1 + (l : ℝ) := by
      rw [← Plane.mk_zero (M + 1 + (k : ℝ)) 0, hkl]; exact Plane.mk_zero _ _
    exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))

/-! ## The index map of a deletion

On a linear index there is nothing to rotate: a vertex is deleted where it stands, and `skipIdx i`
is the inclusion of the shortened index set into the old one — the identity up to `i`, a shift by
one beyond it. It is the arc analogue of `Schoenflies.PrePolygon.emb`, and much simpler, because
that one has to wrap. -/

/-! ## Arcs before normalization

`PreArc` is `PolyArc` with the `corner` field removed, exactly as `Schoenflies.PrePolygon` is
`Schoenflies.ClosedPolygon` with it removed. Realization produces one of these; normalization
turns it into a `PolyArc`. -/

namespace PreArc

variable {n i j k : ℕ}

/-- The carrier of the arc: the union of its `n + 1` edges. -/
def carrier (A : PreArc n) : Set Plane := ⋃ i, ⋃ (_ : i ≤ n), A.edge i

variable {A : PreArc n}

theorem mem_carrier_iff {x : Plane} : x ∈ A.carrier ↔ ∃ i ≤ n, x ∈ A.edge i := mem_iUnion_le_nat

theorem edge_subset_carrier (hi : i ≤ n) : A.edge i ⊆ A.carrier :=
  fun _ hx => mem_carrier_iff.2 ⟨i, hi, hx⟩

/-! ### Deleting a redundant vertex

The blueprint's opening move in the strip lemma, "delete redundant vertices at which two
consecutive edges are collinear", as an operation rather than an invariant. -/

theorem deleteVertex_vertex_zero (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex 0 = A.vertex 0 := by
  rw [deleteVertex_vertex, skipIdx_of_le (Nat.zero_le i)]

theorem deleteVertex_vertex_last (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex (n + 1) = A.vertex (n + 1 + 1) := by
  rw [deleteVertex_vertex, skipIdx_of_lt (by omega)]

/-- **Deleting a redundant vertex does not move the arc.** -/
theorem carrier_deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).carrier = A.carrier := by
  have hplain : ∀ l, l ≠ i → (A.deleteVertex hi hdet).edge l = A.edge (skipIdx i l) :=
    fun l hl => by rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_succ hl]; rfl
  have hmerge : (A.deleteVertex hi hdet).edge i = A.edge i ∪ A.edge (i + 1) := by
    rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_of_le (le_refl i),
      skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    by_cases hli : l = i
    · subst hli
      rcases (hmerge ▸ hzl : z ∈ A.edge l ∪ A.edge (l + 1)) with h | h
      exacts [edge_subset_carrier (by omega) h, edge_subset_carrier (by omega) h]
    · refine edge_subset_carrier (show skipIdx i l ≤ n + 1 by simp only [skipIdx]; split_ifs <;>
        omega) ((hplain l hli) ▸ hzl)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    rcases Nat.lt_trichotomy l i with hlt | heq | hgt
    · refine mem_carrier_iff.2 ⟨l, by omega, ?_⟩
      rw [hplain l (by omega), skipIdx_of_le (by omega)]
      exact hzl
    · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inl (heq ▸ hzl)⟩
    · rcases Nat.lt_or_ge (i + 1) l with hlt' | hle'
      · refine mem_carrier_iff.2 ⟨l - 1, by omega, ?_⟩
        rw [hplain (l - 1) (by omega), skipIdx_of_lt (by omega), show l - 1 + 1 = l by omega]
        exact hzl
      · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inr (show l = i + 1 by omega ▸ hzl)⟩

/-- **Every `PreArc` normalizes to a `PolyArc` with the same carrier and the same two extreme
vertices.** This is the blueprint's "delete redundant vertices at which two consecutive edges are
collinear", run to completion. Unlike the closed case the induction can never get stuck: a
one-edge arc satisfies `corner` vacuously. -/
theorem exists_polyArc : ∀ (n : ℕ) (A : PreArc n), ∃ (m : ℕ) (B : PolyArc m),
    B.carrier = A.carrier ∧ B.vertex 0 = A.vertex 0 ∧ B.vertex (m + 1) = A.vertex (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro A
      exact ⟨0, ⟨A.vertex, A.vertex_inj, A.edges_meet, fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
        rfl, rfl, rfl⟩
  | succ n ih =>
      intro A
      by_cases hc : ∀ i < n + 1,
          det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 2) - A.vertex (i + 1)) ≠ 0
      · exact ⟨n + 1, ⟨A.vertex, A.vertex_inj, A.edges_meet, hc⟩, rfl, rfl, rfl⟩
      · push Not at hc
        obtain ⟨i, hi, hdet⟩ := hc
        obtain ⟨m, B, hcar, h0, hlast⟩ := ih (A.deleteVertex hi hdet)
        exact ⟨m, B, by rw [hcar, carrier_deleteVertex],
          by rw [h0, deleteVertex_vertex_zero], by rw [hlast, deleteVertex_vertex_last]⟩

end PreArc

/-! ## From a clean presentation to a linear vertex list

The arc reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the arc reaches them, are the vertex list
of a `PreArc` whose edges are the pieces.

The parameter set is taken inside `[0, 1)`, exactly as in the closed case, so that
`Schoenflies.parNext` of the last index is `1` by definition. That is not a trick: `f 1 = b` is
the last vertex, and this is what puts it there. Both `a` and `b` are forced onto the cut list,
which is what makes `0` a parameter and `b` an end of a piece. -/

/-- **A simple polygonal arc is the carrier of a vertex list.** The arc analogue of
`Schoenflies.exists_prePolygon_of_isJordanCurve`. -/
theorem exists_preArc_of_isArcBetween {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) :
    ∃ (n : ℕ) (A : PreArc n), A.carrier = P ∧ A.vertex 0 = a ∧ A.vertex (n + 1) = b := by
  classical
  obtain ⟨f, hcont, hinj, hfP, hf0, hf1⟩ := hP
  have hIco : ∀ s ∈ Ico (0 : ℝ) 1, s ∈ I := fun s hs => ⟨hs.1, hs.2.le⟩
  have hmemP : ∀ s ∈ I, f s ∈ P := fun s hs => hfP ▸ ⟨s, hs, rfl⟩
  have haP : a ∈ P := by rw [← hf0]; exact hmemP 0 zero_mem_I
  have hbP : b ∈ P := by rw [← hf1]; exact hmemP 1 one_mem_I
  have hab : a ≠ b := by
    rw [← hf0, ← hf1]
    exact fun he => absurd (hinj zero_mem_I one_mem_I he) (by norm_num)
  -- Both endpoints of the arc are forced to be ends of pieces.
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hpoly haP hbP hab [a, b]
  obtain ⟨Ra, hRa, hRaend⟩ := hextra a (by simp) haP
  obtain ⟨Rb, hRb, hRbend⟩ := hextra b (by simp) hbP
  have h0V : f 0 ∈ endSet Q := by rw [hf0]; exact ⟨Ra, hRa, hRaend⟩
  have h1V : f 1 ∈ endSet Q := by rw [hf1]; exact ⟨Rb, hRb, hRbend⟩
  -- Every point of the arc away from the ends is reached strictly before the far endpoint.
  have hsurj : ∀ z ∈ P \ endSet Q, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by rw [← hfP] at hz; exact hz.1
    refine ⟨s, ⟨hs.1, ?_⟩, rfl⟩
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact absurd h1V hz.2
    · exact hlt
  -- The parameters at which the arc is at an end of a piece, before the far endpoint.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hinj.mono fun t ht => hIco t ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, h0V⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces; for the last gap the right end is `f 1 = b`.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · exact h1V
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i => ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hcont.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ P \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemP s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hcont (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (P \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hinj (hIco _ (hIoo j ht)) (hIco _ (hIoo i hs)) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the arc away from the ends of the pieces.
  have hcov : (⋃ i, G i) = P \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (hpcsub i)
    set W : Set Plane := ⋃ j ∈ ({i}ᶜ : Set (Fin n)), Z j with hW
    have hWclosed : IsClosed W :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => (hZcompact j).isClosed
    have hAdiff : (pc i).interior ⊆ P \ endSet Q := by
      rw [hQ.diff_endSet_eq]
      exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
    have hAZ : (pc i).interior ⊆ Z i ∪ W := by
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hAdiff hz)
      by_cases hji : j = i
      · exact Or.inl ((hZeq i) ▸ Or.inl (hji ▸ hj))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, (hZeq j) ▸ Or.inl hj⟩)
    have hGW : ∀ z ∈ G i, z ∉ W := by
      intro z hz hzW
      obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
      have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hGdiff i hz⟩
      exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j (Ne.symm hji)) z ⟨hz, this⟩
    have hcover2 : (pc i).interior ⊆ Wᶜ ∪ (Z i)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · exact Or.inr fun hzZ => hGW z ((hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩) hzW
      · exact Or.inl hzW
    have hnone : ¬ ((pc i).interior ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
      rintro ⟨z, hz, hzW, hzZ⟩
      rcases hAZ hz with h | h
      exacts [hzZ h, hzW h]
    have hconv : IsPreconnected ((pc i).interior) := (convex_openSegment _ _).isPreconnected
    obtain ⟨z₀, hz₀⟩ := hGne i
    have hAu : ((pc i).interior ∩ Wᶜ).Nonempty := ⟨z₀, hpcsub i hz₀, hGW z₀ hz₀⟩
    have hnotv : ¬ ((pc i).interior ∩ (Z i)ᶜ).Nonempty := fun hv =>
      hnone (hconv _ _ hWclosed.isOpen_compl (hZcompact i).isClosed.isOpen_compl hcover2 hAu hv)
    intro z hz
    have hzZ : z ∈ Z i := by
      by_contra hzZ
      exact hnotv ⟨z, hz, hzZ⟩
    exact (hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R := by
    intro R hR
    have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ P \ endSet Q := by
      rw [hQ.diff_endSet_eq]; exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hxd)
    refine ⟨i, ?_⟩
    by_contra hne'
    exact hQ.interiors (pc i) (hpcQ i) R hR hne' _ (hpceq i ▸ hi) hx
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    have hnd : (pc i).1 ≠ (pc i).2 := hQ.nondeg _ (hpcQ i)
    have hclosure : (pc i).seg ⊆ Z i := by
      have hcl : closure ((pc i).interior) ⊆ Z i := by
        rw [hpceq i]
        exact closure_minimal (fun z hz => (hZeq i) ▸ Or.inl hz) (hZcompact i).isClosed
      rwa [Piece.interior, closure_openSegment] at hcl
    have hmem : ∀ z, z = (pc i).1 ∨ z = (pc i).2 → z = f (tp i) ∨ z = f (nx i) := by
      intro z hz
      have hzseg : z ∈ (pc i).seg := by
        rcases hz with rfl | rfl
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hZeq i) ▸ hclosure hzseg with hzG | hzE
      · exfalso
        rw [← hpceq i] at hzG
        rcases hz with rfl | rfl
        exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
    exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  -- There is at least one gap, and the first one starts at `0`.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  -- The linear vertex list: the ends, in the order the arc reaches them, and then `b`.
  set vf : ℕ → Plane := fun k => if h : k < n then f (par TF hcard ⟨k, h⟩) else b with hvf
  have hvflt : ∀ (k : ℕ) (hk : k < n), vf k = f (tp ⟨k, hk⟩) := by
    intro k hk; rw [hvf]; simp only [dif_pos hk, htp]
  have hvfn : vf n = b := by rw [hvf]; simp only [dif_neg (lt_irrefl n)]
  -- `f 1 = b` is the right end of the last gap, so the list has the right successor at each step.
  have hvfsucc : ∀ (k : ℕ) (hk : k < n), vf (k + 1) = f (nx ⟨k, hk⟩) := by
    intro k hk
    by_cases hk1 : k + 1 < n
    · rw [hvflt (k + 1) hk1, htp, hnx, parNext,
        dif_pos (show (⟨k, hk⟩ : Fin n).val + 1 < n from hk1)]
      rfl
    · have : k + 1 = n := by omega
      rw [this, hvfn, hnx, parNext,
        dif_neg (show ¬ ((⟨k, hk⟩ : Fin n).val + 1 < n) from hk1), hf1]
  -- The vertex list is injective on `{0, …, n}`: `f` is, and the parameters are increasing.
  have hvfinj : ∀ i < n + 1, ∀ j < n + 1, vf i = vf j → i = j := by
    have hkey : ∀ i < n, ∀ j < n, vf i = vf j → i = j := by
      intro i hi j hj he
      rw [hvflt i hi, hvflt j hj] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩)))
        (hIco _ (hTle _ (par_mem hcard ⟨j, hj⟩))) he
      exact congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1)
    have hlast : ∀ i < n, vf i ≠ vf n := by
      intro i hi he
      rw [hvflt i hi, hvfn, ← hf1] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩))) one_mem_I he
      exact absurd (h1 ▸ (hTle _ (par_mem hcard ⟨i, hi⟩)).2) (lt_irrefl 1)
    intro i hi j hj he
    rcases Nat.lt_or_ge i n with hi' | hi'
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact hkey i hi' j hj' he
      · exact absurd (show j = n by omega ▸ he) (hlast i hi')
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact absurd (show i = n by omega ▸ he.symm) (hlast j hj')
      · omega
  obtain ⟨w, hwinj, hwval⟩ := exists_injective_extend vf hvfinj
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Edge `i` of the list is piece `i`.
  have hwedge : ∀ (i : ℕ) (hi : i < m + 1),
      segment ℝ (w i) (w (i + 1)) = (pc ⟨i, hi⟩).seg := by
    intro i hi
    rw [hwval i (by omega), hwval (i + 1) (by omega), hvflt i hi, hvfsucc i hi, hpcseg]
  -- Simplicity, transported from the clean presentation.
  have hmeet : ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i hi j hj hij
    rw [hwedge i (by omega), hwedge j (by omega)]
    have hne' : pc ⟨i, by omega⟩ ≠ pc ⟨j, by omega⟩ := fun he =>
      hij (congrArg Fin.val (hpcinj he))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i, by omega⟩) := by rw [hwval i (by omega), hvflt i (by omega)]
    have hwi' : w (i + 1) = f (nx ⟨i, by omega⟩) := by
      rw [hwval (i + 1) (by omega), hvfsucc i (by omega)]
    rcases hends ⟨i, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwi']
    · rw [h1, h2, ← hwi, ← hwi', Set.pair_comm]
  -- The carrier is the union of the pieces, which is the arc.
  have hcarrier : (⋃ i, ⋃ (_ : i ≤ m), segment ℝ (w i) (w (i + 1))) = P := by
    rw [← hQ.cover_eq]
    refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion_le_nat.1 hz
      rw [hwedge i (by omega)] at hzi
      exact mem_cover (hpcQ _) hzi
    · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
      obtain ⟨i, rfl⟩ := hpcsurj R hR
      refine mem_iUnion_le_nat.2 ⟨i.val, by omega, ?_⟩
      rw [hwedge i.val i.isLt]
      exact hzR
  have hzero : w 0 = a := by rw [hwval 0 (by omega), hvflt 0 hn0, htp0, hf0]
  have hlastv : w (m + 1) = b := by rw [hwval (m + 1) (by omega), hvfn]
  exact ⟨m, ⟨w, hwinj, hmeet⟩, hcarrier, hzero, hlastv⟩

/-! ## The realization theorem for arcs

Realization followed by normalization. This is the statement
`Schoenflies/ArcCollars.lean` names at the end of its file as the one thing it does not prove. -/

/-- **Every simple polygonal arc is the carrier of a `PolyArc`.** The arc analogue of
`Schoenflies.exists_closedPolygon`, and the discharge of `Schoenflies.IsPolyArcCarrier`.

No `a ≠ b` hypothesis is needed: an arc between two points has them distinct, because its
parametrisation is injective on `[0, 1]`. -/
theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) : IsPolyArcCarrier P a b := by
  obtain ⟨n, A, hcar, h0, hlast⟩ := exists_preArc_of_isArcBetween hP hpoly
  obtain ⟨m, B, hcar', h0', hlast'⟩ := PreArc.exists_polyArc n A
  exact ⟨m, B, by rw [hcar', hcar], by rw [h0', h0], by rw [hlast', hlast]⟩

/-! ## The collar hypothesis at the call site of `thm:general-crosscut`

`Schoenflies.IsCrosscut` carries exactly what the discharge needs: `P` is an arc from `p` to `q`,
`P` is polygonal, and `P ∖ {p, q}` lies in `inside C`, whose openness comes from the curve being
closed. So `hcollars` is never again a hypothesis of the crosscut theorem — only `thm:jordan`
is. -/

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- **The collar hypothesis of `thm:general-crosscut`, discharged.** -/
theorem IsCrosscut.hasArcCollars (h : IsCrosscut C P p q) : HasArcCollars (inside C) P :=
  Schoenflies.hasArcCollars (isOpen_inside h.curve.isClosed) h.left_notMem_inside
    h.right_notMem_inside h.sdiff_subset (isPolyArcCarrier_of_isPolygonal h.arc h.polygonal)

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareCycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The subdivided boundary of a square is a cycle

`Schoenflies.SquaresTwoConnected`, the last hypothesis between this library and
`thm:jordan`, discharged.

## What has to be built

`Schoenflies.squareGraph pieces points c r` is the part of a polygonal overlay lying on the
boundary of the axis-parallel square of `ℓ^∞`-radius `r` about `c`, when the four sides of that
square are among the overlay's source segments.  It is the subdivided boundary of the square,
so it is a cycle, and `Graph.IsLongCycle.isTwoConnected` finishes.  What is missing on `main`
is the **cyclic order** of the cut points: the graph is presented as a set of edges, with
nothing saying which edge follows which.

## The route

One real-valued coordinate does the whole of it.  `Schoenflies.sqCoord c r` is the *perimeter
coordinate*: the distance travelled from the north-east corner going counterclockwise round the
boundary, a number in `[0, 8r)`.  It is affine on each side, and it is the ordering tool of
`Schoenflies/SegmentOrder.lean` — distance from the side's first corner — with an offset.

* `Graph.IsIncWalk` is a walk along which a chosen real function strictly increases.  Such a
  walk is automatically a **path** (`Graph.IsIncWalk.isPath`): the freshness clause of
  `Graph.IsPath` says the vertex a step departs from is not visited later, and a vertex visited
  later has a strictly larger value.  This is the only place where "the cut points are in
  order" is turned into a combinatorial statement, and it replaces every argument about
  distinctness of vertices.
* `Schoenflies.exists_incWalk_of_chain` is the one-dimensional heart: a finite family of
  nondegenerate segments inside one ambient segment `[a, b]`, with pairwise disjoint interiors,
  with every end of every one of them interior to none of them, and covering `[a, b]`, is a
  **chain** from `a` to `b` — an `IsIncWalk` for the coordinate `dist a ·` whose edge list is
  exactly the family.  The induction is on the number of segments, and the step is
  `Schoenflies.exists_next_piece`: the piece leaving the current point is the one covering a
  point just beyond it, "just" being measured by the least end-coordinate strictly ahead.
* The four sides are chained separately and concatenated.  The concatenation is a closed walk
  at the north-east corner, so its last edge is split off (`Graph.IsIncWalk.split_last`) and
  becomes the distinguished edge of `Graph.IsCycleThrough`.

## Blueprint

* `Schoenflies.squaresTwoConnected` — the hypothesis `Schoenflies.SquaresTwoConnected` of
  `thm:arc-complement`, discharged.  In the blueprint this is the unstated step of
  "it follows inductively from `lem:union-two-connected` that `Γ_i` is 2-connected": the
  induction starts from one subdivided square boundary, and that it is a cycle is taken for
  granted there.
* `Schoenflies.exists_isLongCycle_squareGraph` — the cycle itself, with the clause that makes
  it usable: the cycle graph **is** `squareGraph`, not merely a subgraph of it.  A consumer
  wanting the boundary cycle of a square as an object, rather than 2-connectedness, takes it
  from here.
* `Schoenflies.exists_incWalk_insideEdges` — the subdivision of one source segment of a
  polygonal overlay, as a **path**.  `Schoenflies/SquareMeshConnected.lean` names exactly this
  as the theorem missing from `main` that blocks `prop:anchored-square-mesh` from being carried
  over to `Schoenflies.squareMesh`.  Its own ground is `Schoenflies.exists_incWalk_of_chain`,
  which knows nothing about overlays either.
* `Graph.IsIncWalk` — no blueprint statement; it is the device that makes
  `lem:polygonal-overlay`'s cut points into an ordered cycle.
-/

open Metric Set
open scoped Graph

/-! ## Part 1: a walk along which a real function increases -/

namespace Graph

variable {α β : Type*} {G H : Graph α β} {f g : α → ℝ} {u v w x : α} {e : β}
  {W W₁ W₂ : List β}

namespace IsIncWalk

/-- An increasing walk from a vertex to itself is empty. -/
theorem eq_nil_of_eq (h : G.IsIncWalk f u W u) : W = [] := h.isPath.eq_nil_of_eq

/-- **Splitting off the last step.**  An increasing walk between distinct vertices has a last
edge, and what precedes it is again an increasing walk.  This is what turns the closed walk
round the square into the edge plus detour that `Graph.IsCycleThrough` asks for. -/
theorem split_last (h : G.IsIncWalk f u W v) (huv : u ≠ v) :
    ∃ (W' : List β) (e : β) (z : α), W = W' ++ [e] ∧ G.IsIncWalk f u W' z ∧
      G.IsLink e z v ∧ f z < f v := by
  induction h with
  | nil hx => exact absurd rfl huv
  | @cons u w v e W hl hf hW ih =>
    by_cases hwv : w = v
    · subst hwv
      obtain rfl : W = [] := hW.eq_nil_of_eq
      exact ⟨[], e, u, by simp, .nil hl.left_mem, hl, hf⟩
    · obtain ⟨W', e', z, rfl, h₁, h₂, h₃⟩ := ih hwv
      exact ⟨e :: W', e', z, by simp, .cons hl hf h₁, h₂, h₃⟩

end IsIncWalk

end Graph

/-! ## Part 2: a tiling of one segment is a chain

Everything here happens along a single ambient segment `[a, b]`, and the coordinate is the one
`Schoenflies/SegmentOrder.lean` supplies: the distance from `a`.  A finite family of
nondegenerate pieces inside `[a, b]`, with disjoint interiors, no end interior to any of them,
and covering the part of `[a, b]` ahead of the current point, is walked through from the current
point to `b`, one piece at a time, in increasing distance from `a`. -/

namespace Schoenflies

open Plane

variable {a b p : Plane} {E : Set Piece}

/-- Every point of `[a, b]` at a prescribed distance from `a` — the surjectivity of the
coordinate, which is what lets an argument name a point "just ahead" of another. -/
theorem exists_mem_segment_dist (hab : a ≠ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ dist a b) :
    ∃ x ∈ segment ℝ a b, dist a x = t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  refine ⟨AffineMap.lineMap a b (t / dist a b), ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t / dist a b, ⟨by positivity, by rw [div_le_one hd]; exact ht1⟩, rfl⟩
  · rw [dist_left_lineMap_of_nonneg a b (by positivity)]
    field_simp

/-- The coordinate of a point of `[a, b]` lies between `0` and the segment's length. -/
theorem dist_le_dist_of_mem_segment {x : Plane} (hab : a ≠ b) (hx : x ∈ segment ℝ a b) :
    dist a x ≤ dist a b :=
  (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    (by rw [dist_self]; exact dist_nonneg) hx).2

/-- **The two ends of a piece, near end first.**  Every one-dimensional citation wants them in
that order, and which of the two names is the near one is none of the caller's business. -/
theorem exists_ordered_ends (a : Plane) (Q : Piece) :
    ∃ u v : Plane, ((u = Q.1 ∧ v = Q.2) ∨ (u = Q.2 ∧ v = Q.1)) ∧ dist a u ≤ dist a v ∧
      segment ℝ u v = Q.seg ∧ openSegment ℝ u v = Q.interior := by
  rcases le_total (dist a Q.1) (dist a Q.2) with h | h
  · exact ⟨Q.1, Q.2, Or.inl ⟨rfl, rfl⟩, h, rfl, rfl⟩
  · exact ⟨Q.2, Q.1, Or.inr ⟨rfl, rfl⟩, h, segment_symm ℝ _ _, openSegment_symm ℝ _ _⟩

/-- Ordered ends of a nondegenerate piece are distinct. -/
theorem ne_of_ordered_ends {Q : Piece} {u v : Plane} (hQ : Q.Nondeg)
    (h : (u = Q.1 ∧ v = Q.2) ∨ (u = Q.2 ∧ v = Q.1)) : u ≠ v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hQ, fun e => hQ e.symm]

/-- **The data of the induction**: a finite family of pieces filling the part of `[a, b]` from
`p` onwards.

`cover` asks nothing at `b` itself, and cannot: at `p = b` the family is empty, and an empty
family covers nothing. -/
structure IsPieceChain (a b p : Plane) (E : Set Piece) : Prop where
  /-- Finitely many pieces. -/
  finite : E.Finite
  /-- None of them a point. -/
  nondeg : ∀ Q ∈ E, Q.Nondeg
  /-- All of them ahead of `p`. -/
  sub : ∀ Q ∈ E, Q.seg ⊆ segment ℝ p b
  /-- The current point is on the ambient segment. -/
  memP : p ∈ segment ℝ a b
  /-- Every end of every piece is interior to none of them — the cut-point condition. -/
  ends : ∀ Q ∈ E, ∀ z, (z = Q.1 ∨ z = Q.2) → ∀ Q' ∈ E, z ∉ Q'.interior
  /-- Distinct pieces have disjoint interiors. -/
  disj : ∀ Q ∈ E, ∀ Q' ∈ E, Q ≠ Q' → ∀ x, x ∈ Q.interior → x ∉ Q'.interior
  /-- Every point ahead of `p`, short of `b`, is on a piece. -/
  cover : ∀ x ∈ segment ℝ p b, x ≠ b → ∃ Q ∈ E, x ∈ Q.seg

namespace IsPieceChain

variable (hC : IsPieceChain a b p E)
include hC

theorem segment_subset : segment ℝ p b ⊆ segment ℝ a b :=
  (convex_segment a b).segment_subset hC.memP (right_mem_segment ℝ a b)

theorem sub_ab : ∀ Q ∈ E, Q.seg ⊆ segment ℝ a b :=
  fun Q hQ => (hC.sub Q hQ).trans hC.segment_subset

/-- The current point is not interior to any piece: every piece lies ahead of it, so its near
end is already at or beyond `p`. -/
theorem notMem_interior (hab : a ≠ b) : ∀ Q ∈ E, p ∉ Q.interior := by
  intro Q hQ hmem
  obtain ⟨u, v, hends, huv, -, hint⟩ := exists_ordered_ends a Q
  have hu : u ∈ segment ℝ a b := by
    refine hC.sub_ab Q hQ ?_
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hv : v ∈ segment ℝ a b := by
    refine hC.sub_ab Q hQ ?_
    rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [right_mem_segment ℝ _ _, left_mem_segment ℝ _ _]
  -- the near end is ahead of `p`, so `p` cannot be strictly beyond it
  have hup : dist a p ≤ dist a u := by
    refine (dist_le_of_mem_segment hab hC.memP (right_mem_segment ℝ a b)
      (dist_le_dist_of_mem_segment hab hC.memP) ?_).1
    refine hC.sub Q hQ ?_
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have := dist_lt_of_mem_openSegment hab hu hv (ne_of_ordered_ends (hC.nondeg Q hQ) hends) huv
    (hint ▸ hmem)
  linarith [this.1]

end IsPieceChain

/-- **The piece leaving the current point.**

Let `m` be the least coordinate of an end of a piece strictly ahead of `p` (the far end `b`
being counted, so that there is one).  A point `x` strictly between `p` and `m` is covered by
some piece; that piece's near end is at or before `p`, because it is at most `x`'s coordinate,
which is short of `m`; and it is at or after `p`, because `p` is interior to no piece and the
far end is beyond `p`.  So the near end **is** `p`.

Stated with explicit hypotheses rather than with `Schoenflies.IsPieceChain`, because it is
applied once at the current point and once at the point one step ahead, and at the latter
the family is no longer confined to what lies beyond. -/
theorem exists_next_piece (hab : a ≠ b) (hfin : E.Finite)
    (hsub : ∀ Q ∈ E, Q.seg ⊆ segment ℝ a b) (hp : p ∈ segment ℝ a b)
    (hpnot : ∀ Q ∈ E, p ∉ Q.interior)
    (hcover : ∀ x ∈ segment ℝ p b, x ≠ b → ∃ Q ∈ E, x ∈ Q.seg) (hpb : p ≠ b) :
    ∃ Q ∈ E, ∃ w, ((p = Q.1 ∧ w = Q.2) ∨ (p = Q.2 ∧ w = Q.1)) ∧ dist a p < dist a w := by
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hpb' : dist a p < dist a b :=
    lt_of_le_of_ne (dist_le_dist_of_mem_segment hab hp)
      fun h => hpb (eq_of_dist_left_eq hab hp hbseg h)
  -- the ends of the pieces, as a finite set of coordinates, together with the far end `b`
  have hendsfin : {z : Plane | ∃ Q ∈ E, z = Q.1 ∨ z = Q.2}.Finite := by
    refine Set.Finite.subset ((hfin.image (fun Q : Piece => Q.1)).union
      (hfin.image (fun Q : Piece => Q.2))) ?_
    rintro z ⟨Q, hQ, rfl | rfl⟩
    exacts [Or.inl ⟨Q, hQ, rfl⟩, Or.inr ⟨Q, hQ, rfl⟩]
  set D : Set ℝ := (fun z => dist a z) '' {z : Plane | ∃ Q ∈ E, z = Q.1 ∨ z = Q.2} ∪
    {dist a b} with hD
  have hDfin : D.Finite := (hendsfin.image _).union (Set.finite_singleton _)
  set D' : Set ℝ := {t ∈ D | dist a p < t} with hD'
  obtain ⟨m, hmD', hmmin⟩ := Set.exists_min_image D' id (hDfin.subset fun _ ht => ht.1)
    ⟨dist a b, Or.inr rfl, hpb'⟩
  have hmlt : dist a p < m := hmD'.2
  have hmle : m ≤ dist a b := hmmin _ ⟨Or.inr rfl, hpb'⟩
  -- a point strictly between `p` and the first end ahead of it
  obtain ⟨x, hxseg, hxd⟩ := exists_mem_segment_dist hab
    (t := (dist a p + m) / 2) (by linarith [dist_nonneg (x := a) (y := p)]) (by linarith)
  have hxlt : dist a x < m := by rw [hxd]; linarith
  have hxgt : dist a p < dist a x := by rw [hxd]; linarith
  have hxpb : x ∈ segment ℝ p b :=
    mem_segment_of_dist_le hab hp hbseg hxseg hxgt.le (by linarith)
  have hxb : x ≠ b := fun h => by rw [h] at hxlt; linarith
  obtain ⟨Q, hQE, hxQ⟩ := hcover x hxpb hxb
  obtain ⟨u, v, hends, huv, hseg, hint⟩ := exists_ordered_ends a Q
  have humem : u = Q.1 ∨ u = Q.2 := by
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [.inl rfl, .inr rfl]
  have hvmem : v = Q.1 ∨ v = Q.2 := by
    rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [.inr rfl, .inl rfl]
  have hu : u ∈ segment ℝ a b := by
    refine hsub Q hQE ?_
    rcases humem with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hv : v ∈ segment ℝ a b := by
    refine hsub Q hQE ?_
    rcases hvmem with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  obtain ⟨hux, hxv⟩ := dist_le_of_mem_segment hab hu hv huv (hseg ▸ hxQ)
  -- the near end is at or before `p`: it is short of `m`, and `m` is the least end ahead
  have hulep : dist a u ≤ dist a p := by
    by_contra hcon
    have : dist a u ∈ D' := ⟨Or.inl ⟨u, ⟨Q, hQE, humem⟩, rfl⟩, lt_of_not_ge hcon⟩
    have := hmmin _ this
    simp only [id] at this
    linarith
  -- and at or after it: otherwise `p` would be interior to the piece
  have hpleu : dist a p ≤ dist a u := by
    by_contra hcon
    exact hpnot Q hQE (hint ▸ mem_openSegment_of_dist_lt hab hu hv hp (lt_of_not_ge hcon)
      (by linarith))
  have hpu : u = p := eq_of_dist_left_eq hab hu hp (le_antisymm hulep hpleu)
  subst hpu
  refine ⟨Q, hQE, v, ?_, by linarith⟩
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  exacts [Or.inl ⟨h₁, h₂⟩, Or.inr ⟨h₁, h₂⟩]

/-- An end of a piece lies on it. -/
theorem mem_seg_of_end {Q : Piece} {z : Plane} (h : z = Q.1 ∨ z = Q.2) : z ∈ Q.seg := by
  rcases h with rfl | rfl
  exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]

/-- **A tiling of a segment is a chain.**  The pieces are walked through from `p` to `b`, one
at a time, in increasing distance from `a`; the walk's edge list is exactly the family.

The induction is on the number of pieces, and the step removes the piece leaving `p`.  Three
of the seven clauses of `Schoenflies.IsPieceChain` are inherited verbatim by the smaller
family; the work is in re-establishing the other two — that everything left lies beyond the
new point, and that it still covers. -/
theorem exists_incWalk_of_chain {G : Graph Plane Piece} (hab : a ≠ b) (hbG : b ∈ V(G)) :
    ∀ (n : ℕ) (p : Plane) (E : Set Piece), E.ncard = n → IsPieceChain a b p E →
      (∀ Q ∈ E, G.IsLink Q Q.1 Q.2) →
      ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ E) ∧ G.IsIncWalk (fun z => dist a z) p W b := by
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p E hcard hC hlink
  by_cases hpb : p = b
  · -- Nothing is left: a piece would have to lie in the single point `b`.
    subst hpb
    have hE : E = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro Q hQ
      have h1 := hC.sub Q hQ
      rw [segment_same] at h1
      exact hC.nondeg Q hQ
        ((h1 (left_mem_segment ℝ Q.1 Q.2)).trans (h1 (right_mem_segment ℝ Q.1 Q.2)).symm)
    exact ⟨[], by simp [hE], .nil hbG⟩
  · obtain ⟨Q, hQE, w, hQw, hlt⟩ := exists_next_piece hab hC.finite hC.sub_ab hC.memP
      (hC.notMem_interior hab) hC.cover hpb
    have hwQ : w = Q.1 ∨ w = Q.2 := by
      rcases hQw with ⟨-, rfl⟩ | ⟨-, rfl⟩
      exacts [.inr rfl, .inl rfl]
    have hpQ : p = Q.1 ∨ p = Q.2 := by
      rcases hQw with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [.inl rfl, .inr rfl]
    have hQseg : Q.seg = segment ℝ p w := by
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [rfl, segment_symm ℝ _ _]
    have hQint : Q.interior = openSegment ℝ p w := by
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [rfl, openSegment_symm ℝ _ _]
    have hlinkQ : G.IsLink Q p w := by
      have := hlink Q hQE
      rcases hQw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [this, this.symm]
    have hwpb : w ∈ segment ℝ p b := hC.sub Q hQE (mem_seg_of_end hwQ)
    have hwab : w ∈ segment ℝ a b := hC.segment_subset hwpb
    have hwsub : segment ℝ w b ⊆ segment ℝ p b :=
      (convex_segment p b).segment_subset hwpb (right_mem_segment ℝ p b)
    -- The pieces other than `Q`, with the current point moved to `w`.
    have hcov' : ∀ x ∈ segment ℝ w b, x ≠ b → ∃ R ∈ E \ {Q}, x ∈ R.seg := by
      intro x hx hxb
      obtain ⟨R, hRE, hxR⟩ := hC.cover x (hwsub hx) hxb
      by_cases hRQ : R = Q
      · -- `x` is on `Q` and beyond `w`, so it *is* `w`; the piece leaving `w` is a second one
        subst hRQ
        have hxw : x = w := by
          have h1 : dist a x ≤ dist a w :=
            (dist_le_of_mem_segment hab hC.memP hwab hlt.le (hQseg ▸ hxR)).2
          have h2 : dist a w ≤ dist a x :=
            (dist_le_of_mem_segment hab hwab hbseg
              (dist_le_dist_of_mem_segment hab hwab) hx).1
          exact eq_of_dist_left_eq hab (hC.segment_subset (hwsub hx)) hwab (le_antisymm h1 h2)
        subst hxw
        obtain ⟨R', hR'E, w', hR'w, hlt'⟩ := exists_next_piece hab hC.finite hC.sub_ab hwab
          (fun S hS => hC.ends R hRE x hwQ S hS)
          (fun y hy hyb => hC.cover y (hwsub hy) hyb) hxb
        refine ⟨R', ⟨hR'E, ?_⟩, mem_seg_of_end (by
          rcases hR'w with ⟨h, -⟩ | ⟨h, -⟩
          exacts [.inl h, .inr h])⟩
        -- the new piece is not `R`: otherwise it would run backwards
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        subst hmem
        have : x = p ∨ w' = p := by
          rcases hR'w with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rcases hQw with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩
          exacts [Or.inl (e₁.trans f₁.symm), Or.inr (e₂.trans f₁.symm),
            Or.inr (e₂.trans f₁.symm), Or.inl (e₁.trans f₁.symm)]
        rcases this with h | h
        · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
        · rw [h] at hlt'; linarith
      · exact ⟨R, ⟨hRE, by simpa using hRQ⟩, hxR⟩
    have hsub' : ∀ R ∈ E \ {Q}, R.seg ⊆ segment ℝ w b := by
      rintro R ⟨hRE, hRQ⟩ y hy
      rw [Set.mem_singleton_iff] at hRQ
      obtain ⟨u, v, hends, huv, hseg, hint⟩ := exists_ordered_ends a R
      have hu : u ∈ segment ℝ a b :=
        hC.sub_ab R hRE (mem_seg_of_end (by
          rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
          exacts [.inl rfl, .inr rfl]))
      have hv : v ∈ segment ℝ a b :=
        hC.sub_ab R hRE (mem_seg_of_end (by
          rcases hends with ⟨-, rfl⟩ | ⟨-, rfl⟩
          exacts [.inr rfl, .inl rfl]))
      have hpu : dist a p ≤ dist a u :=
        (dist_le_of_mem_segment hab hC.memP hbseg (dist_le_dist_of_mem_segment hab hC.memP)
          (hC.sub R hRE (mem_seg_of_end (by
            rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
            exacts [.inl rfl, .inr rfl])))).1
      have huv' : dist a u < dist a v :=
        lt_of_le_of_ne huv fun h =>
          ne_of_ordered_ends (hC.nondeg R hRE) hends (eq_of_dist_left_eq hab hu hv h)
      have hwnot : w ∉ openSegment ℝ u v := hint ▸ hC.ends Q hQE w hwQ R hRE
      have hdi : dist a w ≤ dist a u ∨ dist a v ≤ dist a w := by
        by_contra hcon
        push Not at hcon
        exact hwnot (mem_openSegment_of_dist_lt hab hu hv hwab hcon.1 hcon.2)
      rcases hdi with hdi | hdi
      · obtain ⟨h1, h2⟩ := dist_le_of_mem_segment hab hu hv huv (hseg ▸ hy)
        exact mem_segment_of_dist_le hab hwab hbseg (hC.sub_ab R hRE hy) (hdi.trans h1)
          (h2.trans (dist_le_dist_of_mem_segment hab hv))
      · -- `R` would sit inside `Q`, and their interiors would then meet
        exfalso
        obtain ⟨y', hy'seg, hy'd⟩ := exists_mem_segment_dist hab
          (t := (dist a u + dist a v) / 2) (by linarith [dist_nonneg (x := a) (y := u)])
          (by linarith [dist_le_dist_of_mem_segment hab hv])
        refine hC.disj R hRE Q hQE hRQ y' ?_ ?_
        · exact hint ▸ mem_openSegment_of_dist_lt hab hu hv hy'seg
            (by rw [hy'd]; linarith) (by rw [hy'd]; linarith)
        · exact hQint ▸ mem_openSegment_of_dist_lt hab hC.memP hwab hy'seg
            (by rw [hy'd]; linarith) (by rw [hy'd]; linarith)
    have hC' : IsPieceChain a b w (E \ {Q}) :=
      { finite := hC.finite.subset Set.sdiff_subset
        nondeg := fun R hR => hC.nondeg R hR.1
        sub := hsub'
        memP := hwab
        ends := fun R hR z hz R' hR' => hC.ends R hR.1 z hz R' hR'.1
        disj := fun R hR R' hR' hne => hC.disj R hR.1 R' hR'.1 hne
        cover := hcov' }
    have hcard' : (E \ {Q}).ncard < n := by
      rw [← hcard]; exact Set.ncard_sdiff_singleton_lt_of_mem hQE hC.finite
    obtain ⟨W, hWmem, hWwalk⟩ :=
      ih _ hcard' w (E \ {Q}) rfl hC' (fun R hR => hlink R hR.1)
    refine ⟨Q :: W, fun R => ?_, .cons hlinkQ hlt hWwalk⟩
    simp only [List.mem_cons, hWmem, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨h, -⟩)
      exacts [hQE, h]
    · intro hR
      by_cases h : R = Q
      · exact Or.inl h
      · exact Or.inr ⟨hR, h⟩

/-! ## Part 3: the perimeter coordinate of a square boundary

The four sides of the square are axis-parallel, so on each of them the Euclidean distance from
the side's first corner is the difference of one coordinate.  `Schoenflies.sqCoord` glues the
four into one function on the plane: the distance travelled from the north-east corner going
counterclockwise.  It is `dist` from the side's first corner plus a multiple of `2r`, and that
is the *only* property of it that is ever used. -/

variable {c z : Plane} {r : ℝ}

open Plane

/-- The distance between two points at the same height. -/
theorem dist_eq_abs_fst {z w : Plane} (h : z 1 = w 1) : dist z w = |z 0 - w 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, h, sub_self,
    abs_zero]
  rw [show |z 0 - w 0| ^ 2 + (0 : ℝ) ^ 2 = |z 0 - w 0| ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_abs]

/-- The distance between two points on the same vertical. -/
theorem dist_eq_abs_snd {z w : Plane} (h : z 0 = w 0) : dist z w = |z 1 - w 1| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, h, sub_self,
    abs_zero]
  rw [show (0 : ℝ) ^ 2 + |z 1 - w 1| ^ 2 = |z 1 - w 1| ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_abs]

theorem dist_sqNE_sqNW (c : Plane) (hr : 0 ≤ r) : dist (sqNE c r) (sqNW c r) = 2 * r := by
  rw [dist_eq_abs_fst (by simp)]
  simp only [sqNE_zero, sqNW_zero]
  rw [show c 0 + r - (c 0 - r) = 2 * r by ring, abs_of_nonneg (by linarith)]

theorem dist_sqNW_sqSW (c : Plane) (hr : 0 ≤ r) : dist (sqNW c r) (sqSW c r) = 2 * r := by
  rw [dist_eq_abs_snd (by simp)]
  simp only [sqNW_one, sqSW_one]
  rw [show c 1 + r - (c 1 - r) = 2 * r by ring, abs_of_nonneg (by linarith)]

theorem dist_sqSW_sqSE (c : Plane) (hr : 0 ≤ r) : dist (sqSW c r) (sqSE c r) = 2 * r := by
  rw [dist_eq_abs_fst (by simp)]
  simp only [sqSW_zero, sqSE_zero]
  rw [show c 0 - r - (c 0 + r) = -(2 * r) by ring, abs_neg, abs_of_nonneg (by linarith)]

/-! ### The distance from a side's first corner, in coordinates -/

/-! ### Where two sides meet -/

theorem eq_sqNW_of_mem_top_left (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h₂ : z ∈ segment ℝ (sqNW c r) (sqSW c r)) : z = sqNW c r := by
  rw [mem_seg_top hr] at h₁
  rw [mem_seg_left hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

theorem notMem_top_of_mem_bottom (hr : 0 < r) (h₁ : z ∈ segment ℝ (sqSW c r) (sqSE c r)) :
    z ∉ segment ℝ (sqNE c r) (sqNW c r) := by
  rw [mem_seg_bottom hr.le] at h₁
  rw [mem_seg_top hr.le]
  rintro ⟨h, -⟩
  rw [h₁.1] at h
  linarith

theorem eq_sqNE_of_mem_top_right (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h₂ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) : z = sqNE c r := by
  rw [mem_seg_top hr] at h₁
  rw [mem_seg_right hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

theorem eq_sqSW_of_mem_left_bottom (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqNW c r) (sqSW c r))
    (h₂ : z ∈ segment ℝ (sqSW c r) (sqSE c r)) : z = sqSW c r := by
  rw [mem_seg_left hr] at h₁
  rw [mem_seg_bottom hr] at h₂
  ext i
  fin_cases i
  exacts [h₁.1, h₂.1]

theorem notMem_left_of_mem_right (hr : 0 < r) (h₁ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) :
    z ∉ segment ℝ (sqNW c r) (sqSW c r) := by
  rw [mem_seg_right hr.le] at h₁
  rw [mem_seg_left hr.le]
  rintro ⟨h, -⟩
  rw [h₁.1] at h
  linarith

theorem eq_sqSE_of_mem_bottom_right (hr : 0 ≤ r) (h₁ : z ∈ segment ℝ (sqSW c r) (sqSE c r))
    (h₂ : z ∈ segment ℝ (sqSE c r) (sqNE c r)) : z = sqSE c r := by
  rw [mem_seg_bottom hr] at h₁
  rw [mem_seg_right hr] at h₂
  ext i
  fin_cases i
  exacts [h₂.1, h₁.1]

/-! ### The perimeter coordinate -/

open scoped Classical in
/-- **The perimeter coordinate**: the distance travelled from the north-east corner going
counterclockwise round the boundary of the square.  Junk away from the boundary.

The four branches agree at the three corners where consecutive sides meet, so the value is the
geometric one on all four sides at once — with the single exception of the north-east corner
itself, where the walk both starts and would end.  That exception is the whole reason the
closing edge of the cycle has to be split off. -/
noncomputable def sqCoord (c : Plane) (r : ℝ) (z : Plane) : ℝ :=
  if z ∈ segment ℝ (sqNE c r) (sqNW c r) then dist (sqNE c r) z
  else if z ∈ segment ℝ (sqNW c r) (sqSW c r) then 2 * r + dist (sqNW c r) z
  else if z ∈ segment ℝ (sqSW c r) (sqSE c r) then 4 * r + dist (sqSW c r) z
  else 6 * r + dist (sqSE c r) z

theorem sqCoord_top (hz : z ∈ segment ℝ (sqNE c r) (sqNW c r)) :
    sqCoord c r z = dist (sqNE c r) z := by
  classical
  rw [sqCoord, if_pos hz]

theorem sqCoord_left (hr : 0 ≤ r) (hz : z ∈ segment ℝ (sqNW c r) (sqSW c r)) :
    sqCoord c r z = 2 * r + dist (sqNW c r) z := by
  classical
  by_cases htop : z ∈ segment ℝ (sqNE c r) (sqNW c r)
  · -- the shared corner, where the two formulas agree
    obtain rfl := eq_sqNW_of_mem_top_left hr htop hz
    rw [sqCoord, if_pos htop, dist_sqNE_sqNW c hr, dist_self, add_zero]
  · rw [sqCoord, if_neg htop, if_pos hz]

theorem sqCoord_bottom (hr : 0 < r) (hz : z ∈ segment ℝ (sqSW c r) (sqSE c r)) :
    sqCoord c r z = 4 * r + dist (sqSW c r) z := by
  classical
  have htop : z ∉ segment ℝ (sqNE c r) (sqNW c r) := notMem_top_of_mem_bottom hr hz
  by_cases hleft : z ∈ segment ℝ (sqNW c r) (sqSW c r)
  · obtain rfl := eq_sqSW_of_mem_left_bottom hr.le hleft hz
    rw [sqCoord, if_neg htop, if_pos hleft, dist_sqNW_sqSW c hr.le, dist_self, add_zero]
    ring
  · rw [sqCoord, if_neg htop, if_neg hleft, if_pos hz]

theorem sqCoord_right (hr : 0 < r) (hz : z ∈ segment ℝ (sqSE c r) (sqNE c r))
    (hne : z ≠ sqNE c r) : sqCoord c r z = 6 * r + dist (sqSE c r) z := by
  classical
  have htop : z ∉ segment ℝ (sqNE c r) (sqNW c r) :=
    fun h => hne (eq_sqNE_of_mem_top_right hr.le h hz)
  have hleft : z ∉ segment ℝ (sqNW c r) (sqSW c r) := notMem_left_of_mem_right hr hz
  by_cases hbot : z ∈ segment ℝ (sqSW c r) (sqSE c r)
  · obtain rfl := eq_sqSE_of_mem_bottom_right hr.le hbot hz
    rw [sqCoord, if_neg htop, if_neg hleft, if_pos hbot, dist_sqSW_sqSE c hr.le, dist_self,
      add_zero]
    ring
  · rw [sqCoord, if_neg htop, if_neg hleft, if_neg hbot]

/-! ## Part 4: the overlay edges on one side

A nondegenerate straight segment inside the boundary of a square lies inside **one** side: its
midpoint is on the boundary, so one of the two coordinates is extreme there, and an average of
two numbers at most `c i + r` can only equal `c i + r` when both are.  That is
`Schoenflies.exists_side_of_mem_squareEdges`, and it is the only genuinely two-dimensional step
in the file. -/

variable {pieces : List Piece} {points : List Plane}

/-- The edges of the overlay lying on one prescribed side of the square. -/
def sideEdges (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) (S : Piece) :
    Set Piece := {Q | Q ∈ squareEdges pieces points c r ∧ Q.seg ⊆ S.seg}

/-- A coordinate of a point of a segment lies on the segment of the coordinates: the coordinate
map is linear. -/
theorem coord_mem_segment {y u v : Plane} (i : Fin 2) (h : y ∈ segment ℝ u v) :
    y i ∈ segment ℝ (u i) (v i) := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  exact ⟨p, q, hp, hq, hpq, by rw [Plane.smul_add_apply]; simp [smul_eq_mul]⟩

/-- A point of the boundary of a square has both coordinates within `r` of the centre's. -/
theorem abs_le_of_mem_frontier {y : Plane} (hy : y ∈ frontier (closedSquare c r)) :
    |y 0 - c 0| ≤ r ∧ |y 1 - c 1| ≤ r := by
  rw [mem_frontier_closedSquare] at hy
  exact ⟨hy ▸ le_max_left _ _, hy ▸ le_max_right _ _⟩

/-- **Every edge of the overlay on a square lies on one of the four sides.** -/
theorem exists_side_of_mem_squareEdges (hr : 0 < r)
    {Q : Piece} (hQ : Q ∈ squareEdges pieces points c r) :
    ∃ S ∈ squarePieces c r, Q ∈ sideEdges pieces points c r S := by
  obtain ⟨hQov, hQfr⟩ := hQ
  -- both ends, and the midpoint, are on the boundary
  have h1 := abs_le_of_mem_frontier (hQfr (left_mem_segment ℝ Q.1 Q.2))
  have h2 := abs_le_of_mem_frontier (hQfr (right_mem_segment ℝ Q.1 Q.2))
  have hmseg : (2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2 ∈ Q.seg :=
    ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm0 : ((2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2) 0 = (Q.1 0 + Q.2 0) / 2 := by
    rw [Plane.smul_add_apply]; ring
  have hm1 : ((2⁻¹ : ℝ) • Q.1 + (2⁻¹ : ℝ) • Q.2) 1 = (Q.1 1 + Q.2 1) / 2 := by
    rw [Plane.smul_add_apply]; ring
  have hmax : max |(Q.1 0 + Q.2 0) / 2 - c 0| |(Q.1 1 + Q.2 1) / 2 - c 1| = r := by
    have := mem_frontier_closedSquare.1 (hQfr hmseg)
    rwa [hm0, hm1] at this
  -- a coordinate that both ends share is shared by every point of the piece
  have key : ∀ (i : Fin 2) (t : ℝ), Q.1 i = t → Q.2 i = t → ∀ y ∈ Q.seg, y i = t := by
    intro i t hu' hv' y hy
    have hc := coord_mem_segment i (show y ∈ segment ℝ Q.1 Q.2 from hy)
    rw [hu', hv', segment_same, mem_singleton_iff] at hc
    exact hc
  simp only [abs_le] at h1 h2
  rcases max_choice |(Q.1 0 + Q.2 0) / 2 - c 0| |(Q.1 1 + Q.2 1) / 2 - c 1| with hch | hch <;>
      rw [hch] at hmax <;> rcases (abs_eq hr.le).1 hmax with heq | heq
  · -- the east side
    have e₁ : Q.1 0 = c 0 + r := by linarith [h1.1.2, h2.1.2]
    have e₂ : Q.2 0 = c 0 + r := by linarith [h1.1.2, h2.1.2]
    exact ⟨(sqSE c r, sqNE c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_right hr.le).2 ⟨key 0 (c 0 + r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).2⟩⟩
  · -- the west side
    have e₁ : Q.1 0 = c 0 - r := by linarith [h1.1.1, h2.1.1]
    have e₂ : Q.2 0 = c 0 - r := by linarith [h1.1.1, h2.1.1]
    exact ⟨(sqNW c r, sqSW c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_left hr.le).2 ⟨key 0 (c 0 - r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).2⟩⟩
  · -- the north side
    have e₁ : Q.1 1 = c 1 + r := by linarith [h1.2.2, h2.2.2]
    have e₂ : Q.2 1 = c 1 + r := by linarith [h1.2.2, h2.2.2]
    exact ⟨(sqNE c r, sqNW c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_top hr.le).2 ⟨key 1 (c 1 + r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).1⟩⟩
  · -- the south side
    have e₁ : Q.1 1 = c 1 - r := by linarith [h1.2.1, h2.2.1]
    have e₂ : Q.2 1 = c 1 - r := by linarith [h1.2.1, h2.2.1]
    exact ⟨(sqSW c r, sqSE c r), by simp [squarePieces], ⟨hQov, hQfr⟩, fun y hy =>
      (mem_seg_bottom hr.le).2 ⟨key 1 (c 1 - r) e₁ e₂ y hy,
        (abs_le_of_mem_frontier (hQfr hy)).1⟩⟩

/-! ## Part 5: the four sides, chained

Each side of the square is a source segment of the overlay, so the edges lying on it tile it,
and Part 2 walks through them.  The four walks are then glued at the corners. -/

/-- An end of an edge is incident with it. -/
theorem inc_of_mem_squareEdges {Q : Piece} {y : Plane}
    (hQ : Q ∈ squareEdges pieces points c r) (hy : y = Q.1 ∨ y = Q.2) :
    (squareGraph pieces points c r).Inc Q y := by
  rcases hy with rfl | rfl
  exacts [⟨Q.2, hQ, Or.inl ⟨rfl, rfl⟩⟩, ⟨Q.1, hQ, Or.inr ⟨rfl, rfl⟩⟩]

/-- Every edge of the graph is drawn where its own name says. -/
theorem isLink_of_mem_squareEdges {Q : Piece} (hQ : Q ∈ squareEdges pieces points c r) :
    (squareGraph pieces points c r).IsLink Q Q.1 Q.2 := ⟨hQ, Or.inl ⟨rfl, rfl⟩⟩

/-- A side of the square lies on its boundary. -/
theorem side_subset_frontier (hr : 0 ≤ r) {S : Piece} (hS : S ∈ squarePieces c r) :
    S.seg ⊆ frontier (closedSquare c r) := by
  rw [← cover_squarePieces c hr]
  exact fun y hy => Set.mem_iUnion₂.2 ⟨S, hS, hy⟩

/-! ### The subdivision of one source segment

Nothing about squares enters here.  `Schoenflies/SquareMeshConnected.lean` records this as the
theorem missing from `main` — "the subdivision of a segment at a finite point set is a path" —
that blocks `prop:anchored-square-mesh` from being carried over to `Schoenflies.squareMesh`. -/

/-- The edges of an overlay lying inside one of its source segments. -/
def insideEdges (pieces : List Piece) (points : List Plane) (P₀ : Piece) : Set Piece :=
  {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ P₀.seg}

/-- **The edges inside one source segment tile it.**  Every clause is a property of the
polygonal overlay already on `main`; the covering clause is the one that needs `P₀` to be a
source segment. -/
theorem isPieceChain_insideEdges (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) {P₀ : Piece}
    (hP₀ : P₀ ∈ pieces) : IsPieceChain P₀.1 P₀.2 P₀.1 (insideEdges pieces points P₀) where
  finite := (overlayPieces pieces points).finite_toSet.subset fun _ h => h.1
  nondeg := fun Q hQ => overlayPieces_nondeg points hnd Q hQ.1
  sub := fun Q hQ => hQ.2
  memP := left_mem_segment ℝ P₀.1 P₀.2
  ends := fun Q hQ z hz Q' hQ' =>
    overlayPieces_avoids hnd z (overlayPieces_ends_cut hEnds Q hQ.1 z hz) Q' hQ'.1
  disj := fun Q hQ Q' hQ' hne x hx =>
    overlayPieces_disjoint_interiors hnd hEnds hMeets hQ.1 hQ'.1 hne hx
  cover := by
    intro x hx _
    obtain ⟨Q, hQ, hxQ, hQsub⟩ := exists_overlayPiece_mem_subset (points := points) hP₀ hx
    exact ⟨Q, ⟨hQ, hQsub⟩, hxQ⟩

/-- On a side of the square, "inside the boundary" is automatic. -/
theorem sideEdges_eq_insideEdges (hr : 0 ≤ r) {S : Piece} (hS : S ∈ squarePieces c r) :
    sideEdges pieces points c r S = insideEdges pieces points S := by
  ext Q
  exact ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, h.2.trans (side_subset_frontier hr hS)⟩, h.2⟩⟩

/-- **The edges on one side tile it.** -/
theorem isPieceChain_sideEdges (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {S : Piece} (hS : S ∈ squarePieces c r) :
    IsPieceChain S.1 S.2 S.1 (sideEdges pieces points c r S) :=
  sideEdges_eq_insideEdges (pieces := pieces) (points := points) hr.le hS ▸
    isPieceChain_insideEdges hnd hEnds hMeets (hsub S hS)

/-- The far corner of a side is a vertex: it is an end of a source segment, hence a cut
point, and it lies on the boundary. -/
theorem corner_mem_vertexSet (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hr : 0 < r) (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {S : Piece}
    (hS : S ∈ squarePieces c r) : S.2 ∈ V(squareGraph pieces points c r) :=
  mem_vertexSet_squareGraph hnd hr.le hsub (hEnds S (hsub S hS) S.2 (Or.inr rfl))
    (side_subset_frontier hr.le hS (right_mem_segment ℝ S.1 S.2))

/-- **The walk along one side**, from its first corner to its second, taking every edge of the
overlay that lies on it exactly once, in increasing distance from the first corner. -/
theorem exists_side_walk (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {u v : Plane}
    (hS : (u, v) ∈ squarePieces c r) :
    ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ sideEdges pieces points c r (u, v)) ∧
      (squareGraph pieces points c r).IsIncWalk (fun z => dist u z) u W v :=
  exists_incWalk_of_chain (squarePieces_nondeg c hr _ hS)
    (corner_mem_vertexSet hnd hEnds hr hsub hS) _ u _ rfl
    (isPieceChain_sideEdges hnd hEnds hMeets hr hsub hS)
    fun _ hQ => isLink_of_mem_squareEdges hQ.1

/-- What a walk of the square graph visits stays inside anything its edges stay inside. -/
theorem walkVertices_squareGraph_subset {u : Plane} {W : List Piece} {T : Set Plane}
    (hu : u ∈ T) (hW : ∀ Q ∈ W, Q.seg ⊆ T) :
    (squareGraph pieces points c r).walkVertices u W ⊆ T := by
  rintro x hx
  rcases Graph.mem_walkVertices_iff.1 hx with rfl | ⟨Q, hQ, y, hy⟩
  · exact hu
  · refine hW Q hQ (mem_seg_of_end ?_)
    rcases hy.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]

/-- A piece all of whose points are one point is degenerate. -/
theorem not_nondeg_of_seg_subset_singleton {Q : Piece} {t : Plane} (h : ∀ y ∈ Q.seg, y = t) :
    ¬ Q.Nondeg := fun hne =>
  hne ((h Q.1 (left_mem_segment ℝ _ _)).trans (h Q.2 (right_mem_segment ℝ _ _)).symm)

/-! ## Part 6: the cycle, and `SquaresTwoConnected`

The four walks are concatenated into a closed walk at the north-east corner.  The perimeter
coordinate increases along the first three sides and along all of the fourth but its last step,
which returns to the corner where the coordinate is `0`; so that step is split off and becomes
the distinguished edge of `Graph.IsCycleThrough`. -/

theorem sqNW_ne_sqNE (c : Plane) (hr : 0 < r) : sqNW c r ≠ sqNE c r := by
  intro h
  have h0 := congrArg (fun p : Plane => p 0) h
  simp only [sqNW_zero, sqNE_zero] at h0
  linarith

theorem sqSE_ne_sqNE (c : Plane) (hr : 0 < r) : sqSE c r ≠ sqNE c r := by
  intro h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp only [sqSE_one, sqNE_one] at h1
  linarith

/-- **The boundary cycle of a subdivided square.**  The whole of `squareGraph` is a cycle: an
edge `e`, a detour `D` running the other way round, and a third vertex.  The second clause is
what makes the first usable — `Graph.IsLongCycle.isTwoConnected` proves the *cycle graph*
2-connected, and here the cycle graph is the graph itself. -/
theorem exists_isLongCycle_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    ∃ (e : Piece) (u v : Plane) (D : List Piece) (w : Plane),
      (squareGraph pieces points c r).IsLongCycle e u v D w ∧
        (squareGraph pieces points c r).cycleGraph u e D = squareGraph pieces points c r := by
  set K := squareGraph pieces points c r with hKdef
  have hS₁ : (sqNE c r, sqNW c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₂ : (sqNW c r, sqSW c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₃ : (sqSW c r, sqSE c r) ∈ squarePieces c r := by simp [squarePieces]
  have hS₄ : (sqSE c r, sqNE c r) ∈ squarePieces c r := by simp [squarePieces]
  obtain ⟨W₁, hm₁, hw₁⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₁
  obtain ⟨W₂, hm₂, hw₂⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₂
  obtain ⟨W₃, hm₃, hw₃⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₃
  obtain ⟨W₄, hm₄, hw₄⟩ := exists_side_walk hnd hEnds hMeets hr hsub hS₄
  -- each walk stays on its own side …
  have hv₁ : K.walkVertices (sqNE c r) W₁ ⊆ segment ℝ (sqNE c r) (sqNW c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₁ Q).1 hQ).2
  have hv₂ : K.walkVertices (sqNW c r) W₂ ⊆ segment ℝ (sqNW c r) (sqSW c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₂ Q).1 hQ).2
  have hv₃ : K.walkVertices (sqSW c r) W₃ ⊆ segment ℝ (sqSW c r) (sqSE c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ => ((hm₃ Q).1 hQ).2
  -- … so the distance from its own corner is the perimeter coordinate, up to the offset
  have hc₁ : K.IsIncWalk (sqCoord c r) (sqNE c r) W₁ (sqNW c r) :=
    hw₁.congr_walkVertices fun x hx => (sqCoord_top (hv₁ hx)).symm
  have hc₂ : K.IsIncWalk (sqCoord c r) (sqNW c r) W₂ (sqSW c r) :=
    (hw₂.const_add (2 * r)).congr_walkVertices fun x hx => (sqCoord_left hr.le (hv₂ hx)).symm
  have hc₃ : K.IsIncWalk (sqCoord c r) (sqSW c r) W₃ (sqSE c r) :=
    (hw₃.const_add (4 * r)).congr_walkVertices fun x hx => (sqCoord_bottom hr (hv₃ hx)).symm
  -- the fourth side, with its last step split off: it returns to coordinate `0`
  obtain ⟨W₄', e, z, hW₄eq, hw₄', hlinke, hlte⟩ :=
    (hw₄.const_add (6 * r)).split_last (sqSE_ne_sqNE c hr)
  have hv₄ : K.walkVertices (sqSE c r) W₄' ⊆ segment ℝ (sqSE c r) (sqNE c r) :=
    walkVertices_squareGraph_subset (left_mem_segment ℝ _ _) fun Q hQ =>
      ((hm₄ Q).1 (by rw [hW₄eq]; exact List.mem_append_left _ hQ)).2
  have hzright : z ∈ segment ℝ (sqSE c r) (sqNE c r) :=
    hv₄ hw₄'.isWalk.target_mem_walkVertices
  have hne₄ : ∀ x ∈ K.walkVertices (sqSE c r) W₄', x ≠ sqNE c r := by
    intro x hx hxeq
    have h1 := hw₄'.le_target x hx
    rw [hxeq] at h1
    exact absurd hlte (not_lt.2 h1)
  have hzne : z ≠ sqNE c r := hne₄ z hw₄'.isWalk.target_mem_walkVertices
  have hc₄ : K.IsIncWalk (sqCoord c r) (sqSE c r) W₄' z :=
    hw₄'.congr_walkVertices fun x hx => (sqCoord_right hr (hv₄ hx) (hne₄ x hx)).symm
  set D : List Piece := W₁ ++ W₂ ++ W₃ ++ W₄' with hDdef
  have hD : K.IsIncWalk (sqCoord c r) (sqNE c r) D z := ((hc₁.append hc₂).append hc₃).append hc₄
  have hin₁ : ∀ Q ∈ W₁, Q ∈ D := fun Q h => by
    rw [hDdef]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  have hin₂ : ∀ Q ∈ W₂, Q ∈ D := fun Q h => by
    rw [hDdef]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have hin₃ : ∀ Q ∈ W₃, Q ∈ D := fun Q h => by
    rw [hDdef]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have hin₄ : ∀ Q ∈ W₄', Q ∈ D := fun Q h => by
    rw [hDdef]; exact List.mem_append_right _ h
  -- the closing edge is on the east side, and on no other
  have heE₄ : e ∈ sideEdges pieces points c r (sqSE c r, sqNE c r) :=
    (hm₄ e).1 (by rw [hW₄eq]; simp)
  have hendeg : e.Nondeg := overlayPieces_nondeg points hnd e heE₄.1.1
  have henotD : e ∉ D := by
    rw [hDdef]
    simp only [List.mem_append, not_or]
    refine ⟨⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩, fun h => ?_⟩
    · exact not_nondeg_of_seg_subset_singleton (t := sqNE c r) (fun y hy =>
        eq_sqNE_of_mem_top_right hr.le (((hm₁ e).1 h).2 hy) (heE₄.2 hy)) hendeg
    · exact notMem_left_of_mem_right hr (heE₄.2 (left_mem_segment ℝ e.1 e.2))
        (((hm₂ e).1 h).2 (left_mem_segment ℝ e.1 e.2))
    · exact not_nondeg_of_seg_subset_singleton (t := sqSE c r) (fun y hy =>
        eq_sqSE_of_mem_bottom_right hr.le (((hm₃ e).1 h).2 hy) (heE₄.2 hy)) hendeg
    · have hnodup : W₄.Nodup := hw₄.isPath.nodup
      rw [hW₄eq] at hnodup
      exact (List.nodup_append.1 hnodup).2.2 e h e (by simp) rfl
  have hcyc : K.IsCycleThrough e (sqNE c r) z D := ⟨hlinke.symm, hD.isPath, henotD⟩
  -- the third vertex: the north-west corner
  have hNWmem : sqNW c r ∈ K.walkVertices (sqNE c r) D :=
    Graph.walkVertices_mono hin₁ hc₁.isWalk.target_mem_walkVertices
  have hNWnez : sqNW c r ≠ z := by
    intro h
    have h1 : sqCoord c r (sqNW c r) = 2 * r := by
      rw [sqCoord_top (right_mem_segment ℝ _ _), dist_sqNE_sqNW c hr.le]
    have h2 : sqCoord c r z = 6 * r + dist (sqSE c r) z := sqCoord_right hr hzright hzne
    rw [h, h2] at h1
    have := dist_nonneg (x := sqSE c r) (y := z)
    linarith
  refine ⟨e, sqNE c r, z, D, sqNW c r, ⟨hcyc, hNWmem, sqNW_ne_sqNE c hr, hNWnez⟩, ?_⟩
  -- every edge of the graph is on the cycle
  have hEsub : ∀ Q ∈ squareEdges pieces points c r, Q ∈ D ++ [e] := by
    intro Q hQ
    obtain ⟨S, hS, hQS⟩ := exists_side_of_mem_squareEdges hr hQ
    simp only [squarePieces, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (hin₁ Q ((hm₁ Q).2 hQS))
    · exact List.mem_append_left _ (hin₂ Q ((hm₂ Q).2 hQS))
    · exact List.mem_append_left _ (hin₃ Q ((hm₃ Q).2 hQS))
    · have hQ₄ : Q ∈ W₄ := (hm₄ Q).2 hQS
      rw [hW₄eq] at hQ₄
      rcases List.mem_append.1 hQ₄ with h | h
      · exact List.mem_append_left _ (hin₄ Q h)
      · exact List.mem_append_right _ h
  -- and every vertex is visited
  have hVsub : V(K) ⊆ K.walkVertices (sqNE c r) D := by
    rintro y ⟨Q, hQ, hy⟩
    rcases List.mem_append.1 (hEsub Q hQ) with h | h
    · exact Graph.mem_walkVertices_of_mem_covered ⟨Q, h, inc_of_mem_squareEdges hQ hy⟩
    · rw [List.mem_singleton] at h
      subst h
      have hyz : y = z ∨ y = sqNE c r := by
        rcases hlinke.2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hy with rfl | rfl
        exacts [Or.inl h₁.symm, Or.inr h₂.symm, Or.inr h₂.symm, Or.inl h₁.symm]
      rcases hyz with rfl | rfl
      exacts [hD.isWalk.target_mem_walkVertices, Graph.mem_walkVertices_self]
  refine le_antisymm hcyc.cycleGraph_le ⟨?_, ?_⟩
  · rw [hcyc.cycleGraph_vertexSet]
    exact hVsub
  · intro Q x y hlink
    simp only [Graph.cycleGraph, Graph.pathGraphOf_isLink]
    refine ⟨hEsub Q hlink.1, hlink, ?_, ?_⟩ <;> rw [hcyc.walkVertices_round]
    exacts [hVsub hlink.left_mem, hVsub hlink.right_mem]

/-- **The part of a polygonal overlay on the boundary of one of its squares is 2-connected.**
It is a cycle through at least four vertices — the corners — so
`Graph.IsLongCycle.isTwoConnected` finishes. -/
theorem squareGraph_isTwoConnected (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) (hr : 0 < r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    (squareGraph pieces points c r).IsTwoConnected := by
  obtain ⟨e, u, v, D, w, hlong, heq⟩ :=
    exists_isLongCycle_squareGraph hnd hEnds hMeets hr hsub
  exact heq ▸ hlong.isTwoConnected

/-- **`Schoenflies.SquaresTwoConnected`, discharged.**  Substituting this into
`Schoenflies.exists_face_of_notMem_arc` makes `thm:arc-complement`, `lem:accessible-dense` and
`thm:jordan` without an auxiliary separation hypothesis. -/
theorem squaresTwoConnected : SquaresTwoConnected :=
  fun _ _ hnd hEnds hMeets _ _ hr hsub =>
    squareGraph_isTwoConnected hnd hEnds hMeets hr hsub

end Schoenflies
end

section
-- module Solutions.Q146_CD.JordanClosed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Part I, with nothing assumed

The end of Part I. Everything below is already proved elsewhere; this module supplies the last
arguments and states the four headline theorems with no hypotheses at all, so that a consumer —
and the axiom audit — sees them in the form the blueprint states them.

Two hypotheses were carried, deliberately, across three waves of parallel work, under the
standing rule that a missing result is named rather than `sorry`-ed:

* `Schoenflies.SquaresTwoConnected`, in `Schoenflies/ArcComplement.lean` — a subdivided
  axis-parallel square boundary is 2-connected. Discharged by
  `Schoenflies.squaresTwoConnected` in `Schoenflies/SquareCycle.lean`.
* `Schoenflies.IsPolyArcCarrier`, in `Schoenflies/ArcCollars.lean` — every simple polygonal arc
  is the carrier of a `PolyArc`. Discharged by
  `Schoenflies.isPolyArcCarrier_of_isPolygonal` in `Schoenflies/PolyArcRealize.lean`, the arc
  analogue of the realization theorem that `Schoenflies/Realization.lean` proves for closed
  curves.

Discharging the first makes `thm:arc-complement`, and with it `lem:accessible-dense` and
`thm:jordan`. Supplying the second removes the collar hypothesis from
`lem:crosscut-at-most-two`, and with `thm:jordan` that finishes `thm:general-crosscut`.

## Blueprint

* `Schoenflies.arc_complement` — **`thm:arc-complement`**: the complement of a simple arc in
  the plane is connected.
* `Schoenflies.jordan_curve_theorem` — **`thm:jordan`**: a Jordan curve separates the plane
  into exactly two regions, one bounded and one unbounded, each with the curve as its boundary.
  Stated as `IsSeparating C`, the same predicate `thm:polygonal-jordan` uses, so that every
  consumer written against the polygonal case applies verbatim.
* `Schoenflies.crosscut_theorem`, `Schoenflies.crosscut_theorem_three_regions` —
  **`thm:general-crosscut`**.
-/

open Set

namespace Schoenflies

/-- **`thm:arc-complement`.** If `A` is a simple arc in the plane, then `ℝ² ∖ A` is connected. -/
theorem arc_complement {A : Set Plane} (hA : IsArc A) : IsConnected Aᶜ :=
  isConnected_compl_arc hA squaresTwoConnected

/-- **`thm:jordan`, the Jordan curve theorem.** The complement of a Jordan curve has exactly two
regions, one bounded and one unbounded, and both have the curve as their boundary.

`IsSeparating` packages all of that, and is the same predicate the polygonal case
(`Schoenflies.ClosedPolygon.polygonal_jordan`) is stated through — so `Schoenflies.inside`,
`Schoenflies.outside` and the whole region API of `Schoenflies/CrosscutCells.lean` apply to a
general Jordan curve with nothing to transport. -/
theorem jordan_curve_theorem {C : Set Plane} (hC : IsJordanCurve C) : IsSeparating C :=
  hC.isSeparating fun _ hA => arc_complement hA

end Schoenflies
end

section
-- module Solutions.Q146_CD.RefinementStars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Carriers, refinement compatibility, and the star lemmas

The interface between the *construction* of the nested cellulations and the *abstraction* the
limit homeomorphism uses. The blueprint says at the head of that section (tex, "The limit
homeomorphism of the interiors") that it "forgets how the decompositions were constructed and
uses only their nesting, matching, and shrinking properties"; everything below is therefore
stated for an abstract refinement relation `Realization.Refines` between two realizations of two
generated structures, and *not* for either elementary constructor. The two constructors enter
only at the very end, as the two theorems that produce a `Refines` from them.

## The carrier is a function

`Realization.carrier` is `car_Γ(x)` of the blueprint, exported as a total function `Plane → γ`
rather than as an existential: `σ_n(x)` is used on every line of the limit argument. Outside the
closed domain it is junk (whence the `[Nonempty γ]`), and every lemma about it carries the
hypothesis `x ∈ D` that makes it meaningful. Its characterising property is
`IsCellDecomposition.carrier_eq`: *any* cell whose open part contains `x` is the carrier.

## What `Refines` is, and why it is the right shape

`R'.Refines R par` says: `par` maps cells of the finer structure to cells of the coarser one and
2-cells to 2-cells, it is compatible with `≼_abs` (assertion (iv) of `lem:cellulation-invariants`),
and each *open* cell of the finer realization sits inside the open cell of its parent. The last
clause is the geometric content of the blueprint's proof of
`lem:refinement-compatibility`(a) — "a point in either new subedge or at the new vertex
had the old open edge as its old carrier" — and it implies the weaker
`closure (R'.cell σ) ⊆ closure (R.cell (par σ))` that part (b) needs.

`Refines` is a relation between two realizations of two *different* abstract structures over the
same name type `γ`, parametrised by the composite parent map. `Refines.trans` composes them, so
"a finite sequence of elementary refinements" needs no separate treatment: a consumer that builds
its stages one operation at a time gets the composite by iterating `trans`.

Part (c) of `lem:refinement-compatibility` — "corresponding cells have corresponding parents" —
is, under the representation of `CombinatorialInvariance.lean`, the statement that *one and the
same* `par : γ → γ` serves both realizations: cells are abstract names, and two `Refines`
instances sharing a `par` is exactly a compatible matched refinement. There is nothing to
transport, and the substance of (c) is its consequence, `Refines.carrier_congr`.

## Blueprint

* `Schoenflies.CellStructure.Realization.carrier` — `car_Γ(x)`, with
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.carrier_eq` its characterisation.
* `Schoenflies.CellStructure.Realization.Refines` — a refinement of one generated matched cell
  structure by another, with `Refines.trans` for a finite sequence of them.
* `lem:refinement-compatibility`:
  * (a) `Schoenflies.CellStructure.Realization.Refines.parent_carrier`;
  * (b) `Schoenflies.CellStructure.Realization.Refines.star_subset` (cells) and
    `Schoenflies.CellStructure.Realization.Refines.star_carrier_subset` (points);
  * (c) `Schoenflies.CellStructure.SkeletonHomeo.carrier_congr` (corresponding *skeleton points*
    have corresponding carriers, via
    `Schoenflies.CellStructure.SkeletonHomeo.image_cell`),
    `Schoenflies.CellStructure.Realization.Refines.carrier_congr` (and then at every earlier
    stage), and the form the limit argument actually cites,
    `Schoenflies.CellStructure.Realization.Refines.target_star_subset` (`T_{n+1}(x) ⊆ T_n(x)`).
* `lem:star-intersection` — `Schoenflies.CellStructure.Realization.star_inter_nonempty_congr`.
* `lem:star-face-mesh` — `Schoenflies.CellStructure.Realization.IsCellDecomposition.star_eq_faces`,
  with (a) `…diam_star_le`, `…diam_star_lt`, `…diam_star_carrier_lt` and (b)
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le`,
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le_of_forall`.
* `lem:cell-neighborhood` — `Schoenflies.CellStructure.Realization.cellNbhd` and
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.cell_neighborhood`.
* `rem:inductive-invariants` — honoured: nothing here is proved by a case check on the
  constructors. The inductive content lives in `GeneratedStructure.lean`; the two bridge theorems
  `Schoenflies.CellStructure.SubdivData.IsRefinement.refines` and
  `Schoenflies.CellStructure.SplitData.refines` are the only declarations that mention a
  constructor at all.

`Schoenflies.CellStructure.refines_of_elementary` is the shared bridge: both elementary
operations replace a single cell `c` by a set `N` of fresh cells and send `N` to `c`, so one
lemma serves both.
-/

open Set Metric Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-! ### Elementary facts about the closed star

`Realization.star` is the `St` of the blueprint and is defined in `CombinatorialInvariance.lean`;
these are the membership and containment lemmas its consumers need. -/

/-! ### The carrier of a point

`car_Γ(x)`, the unique open cell containing `x`. It is a total function; off the closed domain
its value is junk, and every lemma below supplies `x ∈ D`. -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-- A point of the closed domain lies in some open cell — the covering half of assertion (i). -/
theorem exists_cell (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ := by
  rw [← h.iUnion_eq] at hx
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨σ, hσ, hxσ⟩

end IsCellDecomposition

/-! ### Refinement

The abstract relation "`R'` refines `R` with parent map `par`". It is deliberately not tied to
either elementary operation: the limit argument uses only these three clauses. -/

/-! ### Matched refinements: part (c)

Two realizations of one abstract structure are matched; a *compatible matched refinement* is a
pair of `Refines` instances sharing one parent map. That sharing **is** the blueprint's
"corresponding cells have corresponding parents": the parent map is a map of abstract names, so
there is only ever one of it. The substance is the consequence recorded here. -/

/-! ### Intersection of corresponding stars -/

/-! ### Stars and the face mesh -/

/-! ### Finite cell neighborhoods -/

/-! ### Corresponding skeleton points

The second sentence of `lem:refinement-compatibility`(c). A point of the realized skeleton lies
in an open 0-cell or an open 1-cell, and the skeleton homeomorphism carries each of those onto
the open cell of the *same abstract name*; so corresponding skeleton points have carriers that
correspond, with nothing to transport. -/

end Realization

/-! ### The two elementary operations produce refinements

Both operations have the same shape: a single cell `c` is replaced by a set `N` of fresh cells,
and the parent map sends `N` to `c` and fixes everything else. `refines_of_elementary` proves the
geometric clause of `Refines` from that shape alone — the fresh cells must land inside `c`,
because any other cell of the old stage survives and is unmoved, and open cells of one stage are
disjoint. -/

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {c : γ} {N : Set γ} {D : Set Plane}

/-- **The shape shared by the two elementary operations.** Given that the refined cells are the
old ones minus `c` together with the fresh set `N`, that `par` collapses `N` to `c` and fixes old
cells, and that both stages decompose the *same* closed domain with the surviving cells unmoved,
the refined realization refines the old one. -/
theorem refines_of_elementary (hc : c ∈ S.cells) (hcells : S'.cells = (S.cells \ {c}) ∪ N)
    (hfresh : ∀ ⦃σ⦄, σ ∈ N → σ ∉ S.cells) (hpar_new : ∀ ⦃σ⦄, σ ∈ N → par σ = c)
    (hpar_old : ∀ ⦃σ⦄, σ ∈ S.cells → par σ = σ)
    (hfaces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces)
    (hsub : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ))
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ c → R'.cell σ = R.cell σ)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D) : R'.Refines R par where
  parent_mem_cells := by
    intro σ hσ
    rw [hcells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [hpar_old hσc]; exact hσc
    · rw [hpar_new hσN]; exact hc
  parent_mem_faces := hfaces
  sub_parent := hsub
  cell_subset := by
    intro σ hσ
    have hσ' := hσ
    rw [hcells] at hσ'
    rcases hσ' with ⟨hσc, hσne⟩ | hσN
    · rw [hpar_old hσc, hcell_eq hσc hσne]
    · rw [hpar_new hσN]
      intro w hw
      -- `w` lies in the old open cell of some old cell `ρ`; every old cell but `c` survives
      -- unmoved, and open cells of the refined stage are disjoint, so `ρ = c`.
      obtain ⟨ρ, hρ, hwρ⟩ := h.exists_cell (h'.cell_subset_domain hσ hw)
      by_cases hρc : ρ = c
      · exact hρc ▸ hwρ
      · have hρ' : ρ ∈ S'.cells := by rw [hcells]; exact Or.inl ⟨hρ, hρc⟩
        have hne : σ ≠ ρ := by rintro rfl; exact hfresh hσN hρ
        have hwρ' : w ∈ R'.cell ρ := by rw [hcell_eq hρ hρc]; exact hwρ
        exact absurd hwρ' (Set.disjoint_left.1 (h'.disjoint hσ hρ' hne) hw)

namespace SplitData

variable {d : S.SplitData}

/-- **A 2-cell split is a refinement.** The geometric input is assertion (i) at the refined stage
together with "the split leaves the other cells where they were"; both are supplied by the
consumer, since the split analogue of `SubdivData.IsRefinement` is not yet on `main`. -/
theorem refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.splitFace d).Realization} {D : Set Plane} (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D)
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ) :
    R'.Refines R d.parent := by
  refine refines_of_elementary d.face_mem_cells (splitFace_cells d)
    (fun _ hσ => notMem_cells_of_mem_newCells hσ) (fun _ hσ => d.parent_of_mem_newCells hσ)
    (fun _ hσ => d.parent_of_mem_cells hσ) ?_ (fun _ _ h => d.sub_parent hS h) hcell_eq h h'
  intro F hF
  rw [splitFace_faces] at hF
  rcases hF with rfl | rfl | ⟨hFc, -⟩
  · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hFc)]; exact hFc

end SplitData

/-! ### The interface, exercised

The limit homeomorphism opens with: "the sets `T_n(x)` are nonempty and compact … the cell-star
inclusion gives `T_{n+1}(x) ⊆ T_n(x)` … their diameters tend to zero … by
`lem:nested-compact` their intersection is one point". This anonymous example is a machine-checked
statement that the four facts that sentence needs come out of this module for an *abstract*
nested sequence: nothing below mentions how the stages were built, and the mesh hypothesis is
read in the target realization while the carrier is read in the source one. -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CellulationInvariants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The two cellulation invariants that need the crosscut theorem

`Schoenflies/GeneratedStructure.lean` proves seven of the nine assertions of
`lem:cellulation-invariants` — (ii), (iii), (iv), (v), (vi), (viii) and (ix), and (i) for the
edge-subdivision constructor. The two it leaves open are exactly the two whose induction step is
`thm:general-crosscut`:

* **(vii)** in each realization every 2-cell boundary is a Jordan curve and the open 2-cell is
  its bounded complementary region;
* **(i)** at the *split* constructor.

Both are proved here. `Schoenflies.crosscut_theorem` does not depend on `main`, and neither does
anything in this module.

## Realizations stay outside the inductive

`Schoenflies.GeneratedStructure` is purely abstract — it carries no realizations at all — while
(i), (vii), (viii) and (ix) are statements about realizations. `RefinementStars.lean` bridges
that by stating its lemmas for an arbitrary `Realization` satisfying `IsCellDecomposition`, and
this module follows the same pattern: the induction over the constructors is replaced by two
*step* theorems, one per constructor, each relating a realization of the refined structure to a
realization of the old one. A consumer building a sequence of stages carries the realizations
itself and applies the step theorem at each stage.

The alternative — realizations as fields of the inductive — was rejected for the reason
`RefinementStars.lean` gives: the limit argument "forgets how the decompositions were
constructed", so the abstract closure and the geometric invariants must be separable. It would
also force every consumer to commit to *two* realizations at the moment it builds an abstract
stage, which `thm:finite-transfer` does not do.

## What assertion (vii) is stated against, and why not the boundary walk

The blueprint phrases (vii) as "every 2-cell boundary **walk** is realized by a Jordan curve".
`CellStructure.boundary : γ → List γ` is a raw datum on which `CellStructure` imposes *no*
axiom whatever: nothing says `S.boundary F` is a closed walk, nothing ties it to `S.sub`, and
nothing ties it to `F`. A version of (vii) phrased against it therefore needs the separate
boundary-cycle invariant that the finite-transfer construction maintains.

So (vii) is stated against the cells: `Realization.faceBoundary F` is the union of the open
cells strictly below `F`, and `IsCellDecomposition.faceBoundary_eq_frontier` identifies it with
`frontier (R.cell F)` as soon as the open 2-cell is open. Assertion (vii) then reads: that
frontier is a Jordan curve, and `R.cell F` is its `inside`. This is the content every consumer
uses — (viii) needs only openness of the 2-cell, `lem:star-face-mesh` needs only the closed
2-cells, and the limit map needs `R.cell F = inside (…)`. Nothing downstream reads the cyclic
order of the walk.

## The orientation-aware update of `subdivideEdge`

`CellStructure.subdivideEdge` cannot compute a corrected boundary from an edge list alone: a
walk traverses `d.edge` in a definite direction, while the same interior edge occurs in the two
incident face boundaries with opposite orientations. `SubdivData` therefore carries the new
boundary lists as data, together with `SubstWalk` proofs that each list replaces the old closed
walk in the correct direction. `SubstWalk.isWalk` proves that every new boundary is again a
closed walk.

## Blueprint

* `Schoenflies.CellStructure.Realization.cellUnion`, `Schoenflies.CellStructure.subcells`,
  `Schoenflies.CellStructure.Realization.faceBoundary` — the realized point set of a set of
  abstract cells, and the boundary of a 2-cell read off the abstract data.
* `Schoenflies.CellStructure.Realization.IsFaceJordan` — **assertion (vii)** of
  `lem:cellulation-invariants`, for one realization.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.face_eq_of_isFaceJordan`,
  `…sub_face_eq` — **assertion (viii)** with its openness hypothesis discharged by (vii).
* `Schoenflies.CellStructure.SubdivData.IsRefinement.isFaceJordan` — (vii) is preserved by an
  edge subdivision.
* `Schoenflies.CellStructure.SplitData.IsRefinement` — the split analogue of
  `SubdivData.IsRefinement`, and `…IsRefinement.isCellDecomposition` — **assertion (i) at the
  split constructor**.
* `Schoenflies.CellStructure.SplitData.IsRefinement.refines` — the one-liner
  `RefinementStars.lean` asked for, next to `SubdivData.IsRefinement.refines`.
* `Schoenflies.CellStructure.SplitData.IsCrosscutSplit`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isRefinement`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isFaceJordan` — the geometric input of one
  split (the ear drawn as a crosscut of the old Jordan face), and the two invariants
  *constructed* from it by `Schoenflies.crosscut_theorem`. This is the blueprint's
  "Theorem `thm:general-crosscut` decomposes the old open 2-cell into the disjoint union of the
  two new open 2-cells and the open cells of the ear, and gives
  `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`".
* `Schoenflies.CellStructure.SubdivData.SubstWalk`,
  `Schoenflies.CellStructure.SubdivData.SubstWalk.isWalk`,
  `Schoenflies.CellStructure.SubdivData.boundary_isWalk` — the orientation-aware boundary-walk
  update. Not a blueprint statement: the blueprint's operation 1 does not spell the update
  out, and this is what it has to be.
-/

open Set Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- The subcells of a cell: the index set of its closed cell in assertion (i). -/
def subcells (S : CellStructure γ) (τ : γ) : Set γ := {σ | σ ∈ S.cells ∧ S.sub σ τ}

theorem mem_subcells_iff {σ τ : γ} : σ ∈ S.subcells τ ↔ σ ∈ S.cells ∧ S.sub σ τ := Iff.rfl

namespace Realization

variable {R : S.Realization} {D : Set Plane} {F T σ τ : γ}

/-! ### The realized point set of a set of cells

Every geometric statement of `lem:cellulation-invariants` is about a *union of open cells*: the
closure of a cell, the boundary of a 2-cell, the realized ear, the realized boundary path. One
notation serves them all. -/

theorem cellUnion_union (R : S.Realization) (Cs Ds : Set γ) :
    R.cellUnion (Cs ∪ Ds) = R.cellUnion Cs ∪ R.cellUnion Ds := Set.biUnion_union _ _ _

theorem cellUnion_insert (R : S.Realization) (σ : γ) (Cs : Set γ) :
    R.cellUnion (insert σ Cs) = R.cell σ ∪ R.cellUnion Cs := Set.biUnion_insert _ _ _

theorem cellUnion_pair (R : S.Realization) (σ τ : γ) :
    R.cellUnion {σ, τ} = R.cell σ ∪ R.cell τ := Set.biUnion_pair _ _ _

theorem cellUnion_subset {Cs : Set γ} {A : Set Plane} (h : ∀ σ ∈ Cs, R.cell σ ⊆ A) :
    R.cellUnion Cs ⊆ A := Set.iUnion₂_subset h

/-- Two realizations — of the same structure or of two different ones over the same names — that
agree cell by cell on a set of cells realize that set by the same point set. -/
theorem cellUnion_congr {S₁ S₂ : CellStructure γ} {R₁ : S₁.Realization} {R₂ : S₂.Realization}
    {Cs : Set γ} (h : ∀ σ ∈ Cs, R₁.cell σ = R₂.cell σ) : R₁.cellUnion Cs = R₂.cellUnion Cs :=
  Set.iUnion₂_congr h

/-- The **realized boundary of a 2-cell**, read off the abstract data: the union of the open
cells strictly below it. Under assertion (i) this is the topological frontier of the open
2-cell (`IsCellDecomposition.faceBoundary_eq_frontier`), which is what makes it the right thing
for the blueprint's "boundary walk of `F`" without a walk being available. -/
def faceBoundary (R : S.Realization) (F : γ) : Set Plane := R.cellUnion (S.subcells F \ {F})

namespace IsCellDecomposition

/-- Assertion (i)'s closure clause, in `cellUnion` notation. -/
theorem closure_cell_eq (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cellUnion (S.subcells τ) := h.closure_eq hτ

theorem mem_subcells_self (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) : τ ∈ S.subcells τ :=
  ⟨hτ, h.sub_refl hτ⟩

/-- A closed cell is its open cell together with the open cells strictly below it. -/
theorem closure_cell_eq_union (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cell τ ∪ R.faceBoundary τ := by
  rw [h.closure_cell_eq hτ, faceBoundary, ← R.cellUnion_insert,
    Set.insert_sdiff_singleton, Set.insert_eq_self.2 (h.mem_subcells_self hτ)]

/-- The open cells strictly below `τ` miss the open cell `τ`. -/
theorem disjoint_faceBoundary (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    Disjoint (R.cell τ) (R.faceBoundary τ) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  obtain ⟨σ, ⟨⟨hσ, -⟩, hσne⟩, hzσ⟩ := mem_cellUnion_iff.1 hz'
  exact Set.disjoint_left.1 (h.disjoint hτ hσ (Ne.symm hσne)) hz hzσ

/-- **The realized boundary of an open cell is its frontier.** The blueprint reads the boundary
of a 2-cell off the cells below it; this says that reading agrees with the topology, which is
what lets assertion (vii) be stated without the boundary-walk datum. -/
theorem faceBoundary_eq_frontier (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells)
    (hopen : IsOpen (R.cell τ)) : R.faceBoundary τ = frontier (R.cell τ) := by
  rw [hopen.frontier_eq, h.closure_cell_eq_union hτ, Set.union_sdiff_left,
    sdiff_eq_left.2 (h.disjoint_faceBoundary hτ).symm]

end IsCellDecomposition

/-! ### Assertion (vii)

"In each of the two realizations, every 2-cell boundary walk is realized by a Jordan curve, and
the open 2-cell is the bounded complementary region of that curve."

`Schoenflies.inside` is the union of the *bounded* complementary components of a set, so
"the bounded complementary region of the Jordan curve `J`" is literally `inside J`; and by
`Schoenflies.jordan_curve_theorem` it is a single region. -/

namespace IsFaceJordan

/-- Each 2-cell boundary separates the plane. This is where `thm:jordan` enters; it is
independent of `main`. -/
theorem isSeparating (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) :
    IsSeparating (frontier (R.cell F)) :=
  jordan_curve_theorem (hJ.isJordanCurve hF)

/-- **An open 2-cell is open.** This is the clause `lem:cellulation-invariants`(viii) needs, and
the only thing the blueprint's proof of (viii) really uses. -/
theorem isOpen (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsOpen (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isOpen_inside

/-- **Assertion (vii) in the blueprint's own words**: the union of the open cells strictly below
a 2-cell is a Jordan curve, and the open 2-cell is its bounded complementary region. -/
theorem faceBoundary_eq (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D) (hF : F ∈ S.faces) :
    R.faceBoundary F = frontier (R.cell F) :=
  h.faceBoundary_eq_frontier (S.mem_cells_of_mem_faces hF) (hJ.isOpen hF)

end IsFaceJordan

end Realization

/-! ### Assertion (vii) is preserved by an edge subdivision

"An edge subdivision changes no 2-cell." Literally: the 2-cells of `S.subdivideEdge d` are those
of `S`, and each is an old cell distinct from the subdivided edge, so `SubdivData.IsRefinement`
leaves its open cell exactly where it was. -/

/-! ### Assertion (i) at the split constructor

The split analogue of `SubdivData.IsRefinement`, and the propagation of assertion (i) across it.
The blueprint's proof of this step is exactly

> `thm:general-crosscut` decomposes the old open 2-cell into the disjoint union of the two new
> open 2-cells and the open cells of the ear, and gives `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`.

so those two identities, together with the incidences along the ear, are the fields of
`SplitData.IsRefinement`; `SplitData.IsCrosscutSplit` below constructs them from
`Schoenflies.crosscut_theorem`. -/

namespace SplitData

variable {d : S.SplitData} {R : S.Realization} {R' : (S.splitFace d).Realization}

/-- The cells the ear **creates**: its interior vertices and its edges. The two ends of the ear
are old vertices, and the blueprint is explicit that the split does not create them. -/
def earNewCells (d : S.SplitData) : Set γ := (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear)

theorem earNewCells_subset_newCells (d : S.SplitData) : d.earNewCells ⊆ d.newCells :=
  Set.subset_union_left

theorem mem_earNewCells_of_mem_ear_vertexSet {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : z ∈ d.earNewCells :=
  Or.inl ⟨hz, by rintro (h | h); exacts [hs h, ht h]⟩

theorem mem_earNewCells_of_mem_ear_edgeSet {f : γ} (hf : f ∈ E(d.ear)) : f ∈ d.earNewCells :=
  Or.inr hf

theorem mem_splitFace_cells_of_earNew {z : γ} (hz : z ∈ d.earNewCells) :
    z ∈ (S.splitFace d).cells :=
  d.mem_splitFace_cells_of_new (d.earNewCells_subset_newCells hz)

/-! #### The subcells of each kind of cell after a split -/

/-- On old cells other than the split 2-cell the relation is unchanged, and **only** old cells
lie below such a cell. This is `SplitData.old_subRel_iff` with the membership of `σ` derived
rather than assumed, which is what the closure clause of assertion (i) needs. -/
theorem subRel_iff_of_mem_cells (hS : S.CombInvariants) (d : S.SplitData) {σ τ : γ}
    (hτc : τ ∈ S.cells) (hτf : τ ≠ d.face) :
    d.subRel σ τ ↔ (σ ∈ S.cells ∧ σ ≠ d.face ∧ S.sub σ τ) := by
  refine ⟨fun h => ?_, fun h => d.subRel_of_old h.1 hτc h.2.1 hτf h.2.2⟩
  rcases h with ⟨-, -, hσf, -, hsub⟩ | ⟨heq, hσn⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
  · exact ⟨hS.sub_mem_left hsub, hσf, hsub⟩
  · exact absurd (heq ▸ hσn) (notMem_newCells_of_mem_cells hτc)
  · exact absurd hτc (d.edge_fresh hinc.edge_mem)
  · exact absurd (heq ▸ hτc) d.face₁_notMem
  · exact absurd (heq ▸ hτc) d.face₂_notMem

/-- The subcells of a surviving cell are its old subcells. -/
theorem subcells_of_mem_cells (hS : S.CombInvariants) (d : S.SplitData) {τ : γ}
    (hτc : τ ∈ S.cells) (hτf : τ ≠ d.face) : (S.splitFace d).subcells τ = S.subcells τ := by
  ext σ
  constructor
  · rintro ⟨-, hsub⟩
    obtain ⟨hσc, -, hσ⟩ := (subRel_iff_of_mem_cells hS d hτc hτf).1 hsub
    exact ⟨hσc, hσ⟩
  · rintro ⟨hσc, hσ⟩
    have hσf : σ ≠ d.face := by
      rintro rfl
      exact hτf (hS.face_maximal d.face_mem hσ)
    exact ⟨d.mem_splitFace_cells_of_old hσc hσf,
      (subRel_iff_of_mem_cells hS d hτc hτf).2 ⟨hσc, hσf, hσ⟩⟩

/-- Nothing lies below an interior vertex of the ear but the vertex itself. -/
theorem subRel_earVertex_iff (d : S.SplitData) {z σ : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : d.subRel σ z ↔ σ = z := by
  have hzn : z ∈ d.newCells :=
    d.earNewCells_subset_newCells (mem_earNewCells_of_mem_ear_vertexSet hz hs ht)
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨h, h ▸ hzn⟩)⟩
  rcases h with ⟨-, hzn', -, -, -⟩ | ⟨heq, -⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
  · exact absurd hzn hzn'
  · exact heq
  · exact absurd hinc.edge_mem (Set.disjoint_left.1 d.ear_disjoint hz)
  · exact absurd (heq ▸ hz) fun hh => d.face₁_notMem_ear (Or.inl hh)
  · exact absurd (heq ▸ hz) fun hh => d.face₂_notMem_ear (Or.inl hh)

/-- The cells below an ear edge are it and its two endpoints. -/
theorem subRel_earEdge_iff (d : S.SplitData) {f a b σ : γ} (hl : d.ear.IsLink f a b) :
    d.subRel σ f ↔ (σ = f ∨ σ = a ∨ σ = b) := by
  have hfn : f ∈ d.newCells :=
    d.earNewCells_subset_newCells (mem_earNewCells_of_mem_ear_edgeSet hl.edge_mem)
  constructor
  · intro h
    rcases h with ⟨-, hfn', -, -, -⟩ | ⟨heq, -⟩ | hinc | ⟨heq, -⟩ | ⟨heq, -⟩
    · exact absurd hfn hfn'
    · exact Or.inl heq
    · exact Or.inr (hinc.eq_or_eq_of_isLink hl)
    · exact absurd (heq ▸ hl.edge_mem) fun hh => d.face₁_notMem_ear (Or.inr hh)
    · exact absurd (heq ▸ hl.edge_mem) fun hh => d.face₂_notMem_ear (Or.inr hh)
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl ⟨rfl, hfn⟩)
    · exact Or.inr (Or.inr (Or.inl hl.inc_left))
    · exact Or.inr (Or.inr (Or.inl hl.inc_right))

theorem subcells_earVertex (d : S.SplitData) {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : (S.splitFace d).subcells z = {z} := by
  ext σ
  refine ⟨fun hσ => (d.subRel_earVertex_iff hz hs ht).1 hσ.2, ?_⟩
  rintro rfl
  exact ⟨d.mem_splitFace_cells_of_earNew (mem_earNewCells_of_mem_ear_vertexSet hz hs ht),
    (d.subRel_earVertex_iff hz hs ht).2 rfl⟩

theorem subcells_earEdge (d : S.SplitData) {f a b : γ} (hl : d.ear.IsLink f a b) :
    (S.splitFace d).subcells f = {f, a, b} := by
  ext σ
  refine ⟨fun hσ => (d.subRel_earEdge_iff hl).1 hσ.2,
    fun hσ => ⟨?_, (d.subRel_earEdge_iff hl).2 hσ⟩⟩
  rcases hσ with rfl | rfl | rfl
  · exact d.mem_splitFace_cells_of_earNew (mem_earNewCells_of_mem_ear_edgeSet hl.edge_mem)
  · exact d.mem_splitFace_cells_of_ear (Or.inl hl.left_mem)
  · exact d.mem_splitFace_cells_of_ear (Or.inl hl.right_mem)

theorem subcells_face₁ (d : S.SplitData) :
    (S.splitFace d).subcells d.face₁ = {d.face₁} ∪ d.earCells ∪ d.cells₁ := by
  ext σ
  constructor
  · intro hσ
    rcases d.subRel_face₁_iff.1 hσ.2 with h | h | h
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]
  · intro hσ
    have hcell : σ ∈ (S.splitFace d).cells := by
      rcases hσ with (rfl | h) | h
      · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₁_subset h) (d.cells₁_ne_face h)
    refine ⟨hcell, d.subRel_face₁_iff.2 ?_⟩
    rcases hσ with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

theorem subcells_face₂ (d : S.SplitData) :
    (S.splitFace d).subcells d.face₂ = {d.face₂} ∪ d.earCells ∪ d.cells₂ := by
  ext σ
  constructor
  · intro hσ
    rcases d.subRel_face₂_iff.1 hσ.2 with h | h | h
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]
  · intro hσ
    have hcell : σ ∈ (S.splitFace d).cells := by
      rcases hσ with (rfl | h) | h
      · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₂_subset h) (d.cells₂_ne_face h)
    refine ⟨hcell, d.subRel_face₂_iff.2 ?_⟩
    rcases hσ with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

/-! #### The refinement relation of one split -/

/-- **`R'` refines `R` along the split `d`.** The fields are the blueprint's own sentences: the
old open 2-cell is the disjoint union of the two new open 2-cells and the *open* cells of the
ear; the closure of each new 2-cell is itself together with the ear and its own boundary path;
and the ear's own cells are incident as a path.

Exactly as with `SubdivData.IsRefinement`, this is local data — it speaks only of the cells the
split creates and of the split 2-cell — and `IsRefinement.isCellDecomposition` upgrades it to
assertion (i) for the whole refined structure. `IsCrosscutSplit.isRefinement` constructs it from
`thm:general-crosscut`. -/
structure IsRefinement (d : S.SplitData) (R : S.Realization)
    (R' : (S.splitFace d).Realization) : Prop where
  /-- Surviving cells are unmoved. -/
  cell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ
  /-- The old open 2-cell is the two new open 2-cells together with the open cells of the ear. -/
  cell_face : R.cell d.face =
    R'.cell d.face₁ ∪ R'.cell d.face₂ ∪ R'.cellUnion d.earNewCells
  /-- The new open cells are nonempty. -/
  nonempty : ∀ ⦃σ⦄, σ ∈ d.newCells → (R'.cell σ).Nonempty
  /-- …and pairwise disjoint. -/
  disjoint : ∀ ⦃σ τ⦄, σ ∈ d.newCells → τ ∈ d.newCells → σ ≠ τ → Disjoint (R'.cell σ) (R'.cell τ)
  /-- An interior vertex of the ear is a closed cell. -/
  closure_earVertex : ∀ ⦃z⦄, z ∈ V(d.ear) → z ≠ d.source → z ≠ d.target →
    closure (R'.cell z) = R'.cell z
  /-- The closure of an ear edge is it together with its two endpoints. -/
  closure_earEdge : ∀ ⦃f a b⦄, d.ear.IsLink f a b →
    closure (R'.cell f) = R'.cell f ∪ (R'.cell a ∪ R'.cell b)
  /-- `closure R₁ = R₁ ∪ P ∪ B₁`. -/
  closure_face₁ : closure (R'.cell d.face₁) =
    R'.cell d.face₁ ∪ R'.cellUnion d.earCells ∪ R'.cellUnion d.cells₁
  /-- `closure R₂ = R₂ ∪ P ∪ B₂`. -/
  closure_face₂ : closure (R'.cell d.face₂) =
    R'.cell d.face₂ ∪ R'.cellUnion d.earCells ∪ R'.cellUnion d.cells₂

namespace IsRefinement

variable {D : Set Plane}

/-- Every cell the split creates lies inside the old open 2-cell. -/
theorem cell_subset_face (href : d.IsRefinement R R') {σ : γ} (hσ : σ ∈ d.newCells) :
    R'.cell σ ⊆ R.cell d.face := by
  rw [href.cell_face]
  rcases hσ with hσ | hσ
  · exact fun _ hz => Or.inr (R'.cell_subset_cellUnion hσ hz)
  · rcases hσ with rfl | rfl
    exacts [fun _ hz => Or.inl (Or.inl hz), fun _ hz => Or.inl (Or.inr hz)]

/-- **Assertion (i) is preserved by a 2-cell split.** -/
theorem isCellDecomposition (hS : S.CombInvariants) (href : d.IsRefinement R R')
    (h : R.IsCellDecomposition D) : R'.IsCellDecomposition D where
  nonempty := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσc, hσf⟩ | hσn
    · rw [href.cell_eq hσc hσf]; exact h.nonempty hσc
    · exact href.nonempty hσn
  disjoint := by
    intro σ τ hσ hτ hne
    rw [splitFace_cells] at hσ hτ
    rcases hσ with ⟨hσc, hσf⟩ | hσn <;> rcases hτ with ⟨hτc, hτf⟩ | hτn
    · rw [href.cell_eq hσc hσf, href.cell_eq hτc hτf]; exact h.disjoint hσc hτc hne
    · rw [href.cell_eq hσc hσf]
      exact (h.disjoint hσc d.face_mem_cells hσf).mono_right (href.cell_subset_face hτn)
    · rw [href.cell_eq hτc hτf]
      exact (h.disjoint d.face_mem_cells hτc (Ne.symm hτf)).mono_left
        (href.cell_subset_face hσn)
    · exact href.disjoint hσn hτn hne
  iUnion_eq := by
    rw [← h.iUnion_eq]
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨σ, hσ, hz⟩
      rw [splitFace_cells] at hσ
      rcases hσ with ⟨hσc, hσf⟩ | hσn
      · exact ⟨σ, hσc, by rwa [href.cell_eq hσc hσf] at hz⟩
      · exact ⟨d.face, d.face_mem_cells, href.cell_subset_face hσn hz⟩
    · rintro ⟨σ, hσ, hz⟩
      by_cases hσf : σ = d.face
      · subst hσf
        rw [href.cell_face] at hz
        rcases hz with hz | hz
        · rcases hz with hz | hz
          · exact ⟨d.face₁, d.mem_splitFace_cells_of_new d.face₁_mem_newCells, hz⟩
          · exact ⟨d.face₂, d.mem_splitFace_cells_of_new d.face₂_mem_newCells, hz⟩
        · obtain ⟨ρ, hρ, hzρ⟩ := Realization.mem_cellUnion_iff.1 hz
          exact ⟨ρ, d.mem_splitFace_cells_of_earNew hρ, hzρ⟩
      · exact ⟨σ, d.mem_splitFace_cells_of_old hσ hσf, by rwa [href.cell_eq hσ hσf]⟩
  closure_eq := by
    intro τ hτ
    change closure (R'.cell τ) = R'.cellUnion ((S.splitFace d).subcells τ)
    rw [splitFace_cells] at hτ
    rcases hτ with ⟨hτc, hτf⟩ | hτn
    · -- a surviving cell: neither it nor anything below it has moved
      rw [href.cell_eq hτc hτf, h.closure_cell_eq hτc, d.subcells_of_mem_cells hS hτc hτf]
      refine Set.iUnion₂_congr fun σ hσ => ?_
      refine (href.cell_eq hσ.1 ?_).symm
      rintro rfl
      exact hτf (hS.face_maximal d.face_mem hσ.2)
    · rcases hτn with hτn | hτn
      · rcases hτn with ⟨hzV, hznot⟩ | hfE
        · -- an interior vertex of the ear
          have hs : τ ≠ d.source := fun hh => hznot (Or.inl hh)
          have ht : τ ≠ d.target := fun hh => hznot (Or.inr hh)
          rw [d.subcells_earVertex hzV hs ht, Realization.cellUnion_singleton,
            href.closure_earVertex hzV hs ht]
        · -- an edge of the ear
          obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hfE
          rw [d.subcells_earEdge hl, href.closure_earEdge hl, Realization.cellUnion_insert,
            Realization.cellUnion_pair]
      · rcases hτn with rfl | rfl
        · rw [href.closure_face₁, d.subcells_face₁, Realization.cellUnion_union,
            Realization.cellUnion_union, Realization.cellUnion_singleton]
        · rw [href.closure_face₂, d.subcells_face₂, Realization.cellUnion_union,
            Realization.cellUnion_union, Realization.cellUnion_singleton]

/-- **A 2-cell split is a refinement**, in the sense of `Realization.Refines`. The one-liner
`RefinementStars.lean` left for this module, beside `SubdivData.IsRefinement.refines`; it feeds
`SplitData.refines` the argument `h'` that module could not construct. -/
theorem refines (hS : S.CombInvariants) (href : d.IsRefinement R R')
    (h : R.IsCellDecomposition D) : R'.Refines R d.parent :=
  SplitData.refines hS h (href.isCellDecomposition hS h) href.cell_eq

end IsRefinement

/-! #### The geometric input of one split, and the two invariants constructed from it

`thm:general-crosscut` is applied here, and only here. Its two standing hypotheses on `main` —
`thm:jordan` and `HasArcCollars` — are both discharged: the first by
`Schoenflies.jordan_curve_theorem`, the second by `Schoenflies.IsCrosscut.hasArcCollars`, which
is why `IsCrosscutSplit` need not mention either. -/

/-- **The geometric input of one 2-cell split**: the realized ear is a polygonal crosscut of the
Jordan region realizing the split 2-cell, the two abstract boundary paths realize the two arcs
that crosscut cuts the boundary curve into, and the two new open 2-cells are the two sides.

Everything the split needs downstream — assertion (i) at the new stage
(`IsCrosscutSplit.isRefinement`) and assertion (vii) at the new stage
(`IsCrosscutSplit.isFaceJordan`) — is *constructed* from this by
`Schoenflies.crosscut_theorem`, not assumed.

The four clauses about the ear's own cells are the only thing left assumed: the crosscut theorem
treats the ear as a single arc `P` and says nothing about how the ear's vertices and edges
subdivide it. They are statements about the drawing of a path graph and belong with whichever
module draws the ear. -/
structure IsCrosscutSplit (d : S.SplitData) (R : S.Realization)
    (R' : (S.splitFace d).Realization) : Prop where
  /-- Surviving cells are unmoved. -/
  cell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ
  /-- The realized ear is a polygonal crosscut of the old Jordan face. -/
  isCrosscut : IsCrosscut (frontier (R.cell d.face)) (R'.cellUnion d.earCells)
    (R.pos d.source) (R.pos d.target)
  /-- The two boundary paths realize the two arcs of the old 2-cell boundary. -/
  isCutPair : IsCutPair (frontier (R.cell d.face)) (R.pos d.source) (R.pos d.target)
    (R.cellUnion d.cells₁) (R.cellUnion d.cells₂)
  /-- The first new open 2-cell is the side of the crosscut bounded by the first path. -/
  cell_face₁ : R'.cell d.face₁ = inside (R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells)
  /-- The second new open 2-cell is the other side. -/
  cell_face₂ : R'.cell d.face₂ = inside (R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells)
  /-- The *open* cells of the ear are the crosscut with its two endpoints removed. -/
  cellUnion_earNewCells : R'.cellUnion d.earNewCells =
    R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target}
  /-- The open cells the ear creates are nonempty. -/
  earNonempty : ∀ ⦃σ⦄, σ ∈ d.earNewCells → (R'.cell σ).Nonempty
  /-- …and pairwise disjoint. -/
  earDisjoint : ∀ ⦃σ τ⦄, σ ∈ d.earNewCells → τ ∈ d.earNewCells → σ ≠ τ →
    Disjoint (R'.cell σ) (R'.cell τ)
  /-- An interior vertex of the ear is a closed cell. -/
  closure_earVertex : ∀ ⦃z⦄, z ∈ V(d.ear) → z ≠ d.source → z ≠ d.target →
    closure (R'.cell z) = R'.cell z
  /-- The closure of an ear edge is it together with its two endpoints. -/
  closure_earEdge : ∀ ⦃f a b⦄, d.ear.IsLink f a b →
    closure (R'.cell f) = R'.cell f ∪ (R'.cell a ∪ R'.cell b)

namespace IsCrosscutSplit

/-- The boundary paths are realized identically before and after the split: their cells are old
cells, and none of them is the split 2-cell. -/
theorem cellUnion_cells₁ (hc : d.IsCrosscutSplit R R') :
    R'.cellUnion d.cells₁ = R.cellUnion d.cells₁ :=
  Realization.cellUnion_congr fun _ hσ => hc.cell_eq (d.cells₁_subset hσ) (d.cells₁_ne_face hσ)

theorem cellUnion_cells₂ (hc : d.IsCrosscutSplit R R') :
    R'.cellUnion d.cells₂ = R.cellUnion d.cells₂ :=
  Realization.cellUnion_congr fun _ hσ => hc.cell_eq (d.cells₂_subset hσ) (d.cells₂_ne_face hσ)

/-- Every open cell the ear creates lies in the open crosscut. -/
theorem cell_earNew_subset (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    R'.cell σ ⊆ R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target} := by
  rw [← hc.cellUnion_earNewCells]
  exact R'.cell_subset_cellUnion hσ

/-- **The Jordan curve of the first new 2-cell** is `B₁ ∪ P`. -/
theorem frontier_face₁ (hc : d.IsCrosscutSplit R R') :
    frontier (R'.cell d.face₁) = R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells := by
  rw [hc.cell_face₁]
  exact hc.isCrosscut.frontier_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair

theorem frontier_face₂ (hc : d.IsCrosscutSplit R R') :
    frontier (R'.cell d.face₂) = R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells := by
  rw [hc.cell_face₂]
  exact hc.isCrosscut.frontier_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm

theorem disjoint_faces (hc : d.IsCrosscutSplit R R') :
    Disjoint (R'.cell d.face₁) (R'.cell d.face₂) := by
  rw [hc.cell_face₁, hc.cell_face₂]
  exact hc.isCrosscut.disjoint_sides (fun _ hs => jordan_curve_theorem hs) hc.isCutPair

theorem disjoint_face₁_earNew (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    Disjoint (R'.cell d.face₁) (R'.cell σ) := by
  rw [hc.cell_face₁]
  exact (hc.isCrosscut.disjoint_side_crosscut (fun _ hs => jordan_curve_theorem hs)
    hc.isCutPair).mono_right (hc.cell_earNew_subset hσ)

theorem disjoint_face₂_earNew (hc : d.IsCrosscutSplit R R') {σ : γ} (hσ : σ ∈ d.earNewCells) :
    Disjoint (R'.cell d.face₂) (R'.cell σ) := by
  rw [hc.cell_face₂]
  exact (hc.isCrosscut.disjoint_side_crosscut (fun _ hs => jordan_curve_theorem hs)
    hc.isCutPair.symm).mono_right (hc.cell_earNew_subset hσ)

/-- **Assertion (i) at the split, constructed from `thm:general-crosscut`.** The crosscut theorem
decomposes the old open 2-cell into the two new open 2-cells and the open cells of the ear, and
gives `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`; those are exactly the fields of `SplitData.IsRefinement` that
are not about the ear's own drawing.

The old instance of assertion (vii) is what identifies the old open 2-cell with the Jordan
domain the crosscut cuts. -/
theorem isRefinement (hc : d.IsCrosscutSplit R R') (hJ : R.IsFaceJordan) :
    d.IsRefinement R R' where
  cell_eq := hc.cell_eq
  cell_face := by
    calc R.cell d.face = inside (frontier (R.cell d.face)) := hJ.cell_eq_inside d.face_mem
      _ = inside (R.cellUnion d.cells₁ ∪ R'.cellUnion d.earCells) ∪
            inside (R.cellUnion d.cells₂ ∪ R'.cellUnion d.earCells) ∪
            (R'.cellUnion d.earCells \ {R.pos d.source, R.pos d.target}) :=
          hc.isCrosscut.inside_eq_split (fun _ hs => jordan_curve_theorem hs) hc.isCutPair
            hc.isCrosscut.hasArcCollars
      _ = R'.cell d.face₁ ∪ R'.cell d.face₂ ∪ R'.cellUnion d.earNewCells := by
          rw [hc.cell_face₁, hc.cell_face₂, hc.cellUnion_earNewCells]
  nonempty := by
    rintro σ (hσ | (rfl | rfl))
    · exact hc.earNonempty hσ
    · rw [hc.cell_face₁]
      exact hc.isCrosscut.side_nonempty (fun _ hs => jordan_curve_theorem hs) hc.isCutPair
    · rw [hc.cell_face₂]
      exact hc.isCrosscut.side_nonempty (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm
  disjoint := by
    rintro σ τ (hσ | (rfl | rfl)) (hτ | (rfl | rfl)) hne
    · exact hc.earDisjoint hσ hτ hne
    · exact (hc.disjoint_face₁_earNew hσ).symm
    · exact (hc.disjoint_face₂_earNew hσ).symm
    · exact hc.disjoint_face₁_earNew hτ
    · exact absurd rfl hne
    · exact hc.disjoint_faces
    · exact hc.disjoint_face₂_earNew hτ
    · exact hc.disjoint_faces.symm
    · exact absurd rfl hne
  closure_earVertex := hc.closure_earVertex
  closure_earEdge := hc.closure_earEdge
  closure_face₁ := by
    rw [hc.cell_face₁, hc.cellUnion_cells₁,
      hc.isCrosscut.closure_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair]
    simp only [Set.union_assoc, Set.union_comm]
  closure_face₂ := by
    rw [hc.cell_face₂, hc.cellUnion_cells₂,
      hc.isCrosscut.closure_side (fun _ hs => jordan_curve_theorem hs) hc.isCutPair.symm]
    simp only [Set.union_assoc, Set.union_comm]

/-- **Assertion (vii) is preserved by a 2-cell split.** The two new open 2-cells are the two
sides of the crosscut, and `thm:general-crosscut` says each is the bounded complementary region
of the Jordan curve `Bᵢ ∪ P`; every other 2-cell is unmoved. -/
theorem isFaceJordan (hc : d.IsCrosscutSplit R R') (hJ : R.IsFaceJordan) : R'.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hFc, hFf⟩
    · rw [hc.frontier_face₁]; exact hc.isCrosscut.isJordanCurve_union hc.isCutPair
    · rw [hc.frontier_face₂]; exact hc.isCrosscut.isJordanCurve_union hc.isCutPair.symm
    · rw [hc.cell_eq (S.mem_cells_of_mem_faces hFc) hFf]; exact hJ.isJordanCurve hFc
  cell_eq_inside := by
    intro F hF
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hFc, hFf⟩
    · rw [hc.frontier_face₁]; exact hc.cell_face₁
    · rw [hc.frontier_face₂]; exact hc.cell_face₂
    · rw [hc.cell_eq (S.mem_cells_of_mem_faces hFc) hFf]; exact hJ.cell_eq_inside hFc

/-- **Both invariants at once**: one 2-cell split of a realization satisfying (i) and (vii)
produces a realization satisfying (i) and (vii), and the pair is a `Realization.Refines`. This
is the whole induction step of `lem:cellulation-invariants` over the second constructor. -/
theorem isCellDecomposition_and_isFaceJordan (hc : d.IsCrosscutSplit R R')
    (hS : S.CombInvariants) {D : Set Plane} (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    R'.IsCellDecomposition D ∧ R'.IsFaceJordan ∧ R'.Refines R d.parent :=
  ⟨(hc.isRefinement hJ).isCellDecomposition hS h, hc.isFaceJordan hJ,
    (hc.isRefinement hJ).refines hS h⟩

end IsCrosscutSplit

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryCyclesGenerated
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Boundary cycles under the elementary cellulation operations

This module proves that the face-boundary invariant used to construct the two paths of an ear
step is closed under face splitting and edge subdivision.  The split proof is combinatorial:
each new boundary is one old boundary arc followed by the reverse of the inserted ear.

## Blueprint

* `Schoenflies.CellStructure.SplitData.boundaryCycles` — preservation under operation 2 of
  `def:generated-structure`.
* `Schoenflies.CellStructure.SubdivData.boundaryCycles` — preservation under operation 1.
* `Schoenflies.GeneratedStructure.boundaryCycles` — the closed induction.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace SplitData

variable (d : S.SplitData)

/-- An old walk visits the same vertices when read in the enlarged skeleton. -/
theorem walkVertices_oldWalk {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    d.skeleton.walkVertices u W = S.skel.walkVertices u W := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hlink⟩
    · exact Graph.mem_walkVertices_self
    · rw [SplitData.skeleton, d.compatible.union_isLink] at hlink
      rcases hlink with hlink | hlink
      · exact Graph.mem_walkVertices_of_mem_covered ⟨f, hf, y, hlink⟩
      · exact (Set.disjoint_left.1 d.disjoint_edgeSet (h.edge_mem hf)
          hlink.edge_mem).elim
  · exact Graph.walkVertices_mono_of_le d.le_skeleton

/-- The ear walk visits exactly the vertices of the abstract ear graph, even when read in the
enlarged skeleton. -/
theorem walkVertices_earWalk :
    d.skeleton.walkVertices d.source d.earWalk = V(d.ear) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hlink⟩
    · exact d.isPathGraph.source_mem
    · rw [SplitData.skeleton, d.compatible.union_isLink] at hlink
      rcases hlink with hlink | hlink
      · exact (Set.disjoint_left.1 d.disjoint_edgeSet hlink.edge_mem
          (d.isPathGraph.mem_edgeSet hf)).elim
      · exact hlink.left_mem
  · rw [d.isPathGraph.vertexSet_eq]
    exact Graph.walkVertices_mono_of_le d.ear_le_skeleton

/-- The reverse ear walk has the same vertex carrier. -/
theorem walkVertices_reverse_earWalk :
    d.skeleton.walkVertices d.target d.earWalk.reverse = V(d.ear) := by
  rw [(d.isPathGraph.isWalk.mono d.ear_le_skeleton).reverse_walkVertices]
  exact d.walkVertices_earWalk

/-- The cells of an old walk are unchanged in the enlarged skeleton. -/
theorem pathCells_oldWalk {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    (S.splitFace d).pathCells u W = S.pathCells u W := by
  rw [CellStructure.pathCells, CellStructure.pathCells, splitFace_skel,
    d.walkVertices_oldWalk h]

/-- The cells of the ear walk, read in the enlarged skeleton, are exactly the cells of the
abstract ear graph. -/
theorem pathCells_earWalk :
    (S.splitFace d).pathCells d.source d.earWalk = d.earCells := by
  rw [CellStructure.pathCells, splitFace_skel, d.walkVertices_earWalk, SplitData.earCells,
    d.isPathGraph.edgeSet_eq]
  exact Set.union_comm _ _

/-- Reversing the ear walk does not change its cell carrier. -/
theorem pathCells_reverse_earWalk :
    (S.splitFace d).pathCells d.target d.earWalk.reverse = d.earCells := by
  rw [FaceCycle.pathCells_reverse (d.isPathGraph.isPath.mono d.ear_le_skeleton).isWalk]
  exact d.pathCells_earWalk

/-- One old boundary path closed by the reverse ear is a boundary cycle of a new face. -/
theorem faceCycle_of_boundaryPath {newFace : γ} {P : List γ}
    (hface : newFace ∈ (S.splitFace d).faces)
    (hboundary : (S.splitFace d).boundary newFace = P ++ d.earWalk.reverse)
    (hP : S.skel.IsPath d.source P d.target)
    (hsub : ∀ ⦃σ : γ⦄, (S.splitFace d).sub σ newFace ↔
      σ = newFace ∨ σ ∈ d.earCells ∨ σ ∈ S.pathCells d.source P) :
    Nonempty ((S.splitFace d).FaceCycle newFace) := by
  have hPne : P ≠ [] := hP.ne_nil d.source_ne_target
  cases P with
  | nil => exact (hPne rfl).elim
  | cons f R => cases hP with
  | @cons _ w _ _ _ hlink hR hfresh =>
    have hR' := hR.mono d.le_skeleton
    have hQ' := d.isPathGraph.isPath.reverse.mono d.ear_le_skeleton
    have hmeet : ∀ y ∈ d.skeleton.walkVertices w R,
        y ∈ d.skeleton.walkVertices d.target d.earWalk.reverse → y = d.target := by
      intro y hyR hyQ
      have hyOld : y ∈ S.skel.walkVertices w R := by
        rw [← d.walkVertices_oldWalk hR.isWalk]
        exact hyR
      have hyEar : y ∈ V(d.ear) := d.walkVertices_reverse_earWalk ▸ hyQ
      have hyEnds : y ∈ ({d.source, d.target} : Set γ) := by
        rw [← d.vertexSet_inter]
        exact ⟨hyEar, hR.isWalk.walkVertices_subset hyOld⟩
      rcases hyEnds with rfl | rfl
      · exact (hfresh hyOld).elim
      · rfl
    have hpath : d.skeleton.IsPath w (R ++ d.earWalk.reverse) d.source :=
      hR'.append hQ' hmeet
    have hfreshEdge : f ∉ R ++ d.earWalk.reverse := by
      rw [List.mem_append, List.mem_reverse]
      rintro (hfR | hfQ)
      · exact (List.nodup_cons.1 (Graph.IsPath.nodup (.cons hlink hR hfresh))).1 hfR
      · exact Set.disjoint_left.1 d.disjoint_edgeSet hlink.edge_mem
          (d.isPathGraph.mem_edgeSet hfQ)
    have hcarrier : (S.splitFace d).pathCells d.source
          ((f :: R) ++ d.earWalk.reverse) =
        S.pathCells d.source (f :: R) ∪ d.earCells := by
      calc
        (S.splitFace d).pathCells d.source ((f :: R) ++ d.earWalk.reverse) =
            (S.splitFace d).pathCells d.source (f :: R) ∪
              (S.splitFace d).pathCells d.target d.earWalk.reverse :=
          FaceCycle.pathCells_append
            ((Graph.IsWalk.cons hlink hR.isWalk).mono d.le_skeleton)
            hQ'.isWalk
        _ = S.pathCells d.source (f :: R) ∪ d.earCells := by
          rw [d.pathCells_oldWalk (Graph.IsWalk.cons hlink hR.isWalk),
            d.pathCells_reverse_earWalk]
    refine ⟨{
      face_mem := hface
      edge := f
      source := w
      target := d.source
      walk := R ++ d.earWalk.reverse
      boundary_eq := hboundary
      isCycle := ⟨hlink.symm.mono d.le_skeleton, hpath, hfreshEdge⟩
      sub_face := ?_
    }⟩
    intro σ
    rw [hsub]
    change (σ = newFace ∨ σ ∈ d.earCells ∨ σ ∈ S.pathCells d.source (f :: R)) ↔
      σ = newFace ∨ σ ∈ (S.splitFace d).pathCells d.source
        ((f :: R) ++ d.earWalk.reverse)
    rw [hcarrier]
    simp only [Set.mem_union]
    tauto

/-- Face splitting preserves cyclic boundaries. -/
theorem boundaryCycles (hcycles : S.BoundaryCycles) (hS : S.CombInvariants) :
    (S.splitFace d).BoundaryCycles where
  cycle F hF := by
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · apply d.faceCycle_of_boundaryPath (P := d.path₁)
      · rw [splitFace_faces]; exact Set.mem_insert _ _
      · simp [CellStructure.splitFace]
      · exact d.isPath₁
      · intro σ
        rw [splitFace_sub, d.subRel_face₁_iff]
        rfl
    · apply d.faceCycle_of_boundaryPath (P := d.path₂)
      · rw [splitFace_faces]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · simp [CellStructure.splitFace, d.face_ne.symm]
      · exact d.isPath₂
      · intro σ
        rw [splitFace_sub, d.subRel_face₂_iff]
        rfl
    · obtain ⟨c⟩ := hcycles.cycle F hF
      have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
      have hF₁ : F ≠ d.face₁ := fun heq => d.face₁_notMem (heq ▸ hFc)
      have hF₂ : F ≠ d.face₂ := fun heq => d.face₂_notMem (heq ▸ hFc)
      have hsubOld : ∀ σ, (S.splitFace d).sub σ F ↔ S.sub σ F := by
        intro σ
        rw [splitFace_sub, subRel_iff_of_mem_cells hS d hFc hFne]
        constructor
        · exact fun h => h.2.2
        · intro h
          refine ⟨hS.sub_mem_left h, ?_, h⟩
          rintro rfl
          exact hFne (hS.face_maximal d.face_mem h)
      have hclosed : S.skel.IsWalk c.target (c.edge :: c.walk) c.target :=
        .cons c.isCycle.isLink.symm c.isCycle.isPath.isWalk
      refine ⟨{
        face_mem := by
          rw [splitFace_faces]
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFne⟩)
        edge := c.edge
        source := c.source
        target := c.target
        walk := c.walk
        boundary_eq := by
          simp [CellStructure.splitFace, hF₁, hF₂, c.boundary_eq]
        isCycle := ⟨c.isCycle.isLink.mono d.le_skeleton,
          c.isCycle.isPath.mono d.le_skeleton, c.isCycle.notMem⟩
        sub_face := ?_
      }⟩
      intro σ
      rw [hsubOld, c.sub_face, d.pathCells_oldWalk hclosed]

end SplitData

/-! ### The invariant at every generated stage -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Relabelling the edges of a multigraph

Mathlib's `Graph.map` changes vertex names and deliberately leaves edge names fixed.  The ear
construction needs the complementary operation: give the finitely many edges of an ambient path
fresh abstract cell names while retaining every vertex and every incidence.

The relabelling map only has to be injective on the graph's edge set.  Walks, paths, and path
graphs then push forward by mapping their edge lists.
-/

open Set
open Schoenflies
open unitInterval
open scoped _root_.Graph

namespace Graph

variable {α β δ : Type*} {G : Graph α β} {f : β → δ}

/-- A graph which is exactly a path remains so after an injective edge relabelling. -/
theorem IsPathGraph.relabelEdges {P : Graph α β} (hf : InjOn f E(P))
    (h : P.IsPathGraph u W v) :
    (P.relabelEdges f hf).IsPathGraph u (W.map f) v where
  isPath := h.isPath.relabelEdges hf
  edgeSet_eq := by
    rw [edgeSet_relabelEdges, h.edgeSet_eq]
    ext d
    simp
  vertexSet_eq := by
    rw [vertexSet_relabelEdges, walkVertices_relabelEdges hf u h.isWalk.edgeSet_subset,
      h.vertexSet_eq]

/-! ### Relabelling a drawing -/

section Drawing

variable {G : Graph Plane β} {drawing : β → ℝ → Plane}

theorem edgeArc_relabelDrawing [Nonempty β] (hf : InjOn f E(G))
    {e : β} (he : e ∈ E(G)) :
    edgeArc (relabelDrawing G f drawing) (f e) = edgeArc drawing e := by
  change relabelDrawing G f drawing (f e) '' I = drawing e '' I
  rw [relabelDrawing_apply hf he]

/-- Injectively changing edge names preserves a plane drawing and all of its drawn arcs. -/
theorem IsDrawing.relabelEdges [Nonempty β] (h : IsDrawing G drawing)
    (hf : InjOn f E(G)) :
    IsDrawing (G.relabelEdges f hf) (relabelDrawing G f drawing) where
  edge_param := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := hd
    rw [relabelDrawing_apply hf he]
    obtain ⟨hc, hi, hlink⟩ := h.edge_param he
    exact ⟨hc, hi, hlink.relabelEdges hf⟩
  vertex_mem_edgeArc := by
    intro d x y v hlink hv hz
    rcases hlink with ⟨e, he, rfl, hxy⟩
    rw [edgeArc_relabelDrawing hf he] at hz
    exact h.vertex_mem_edgeArc hxy hv hz
  edge_inter := by
    intro d g hd hg hdg z hzd hzg
    obtain ⟨e, he, rfl⟩ := hd
    obtain ⟨e', he', rfl⟩ := hg
    rw [edgeArc_relabelDrawing hf he] at hzd
    rw [edgeArc_relabelDrawing hf he'] at hzg
    have hee' : e ≠ e' := fun hEq => hdg (congrArg f hEq)
    obtain ⟨hzV, ⟨x, hex⟩, ⟨y, he'y⟩⟩ := h.edge_inter he he' hee' hzd hzg
    exact ⟨hzV, ⟨x, hex.relabelEdges hf⟩, ⟨y, he'y.relabelEdges hf⟩⟩

end Drawing

end Graph
end

section
-- module Solutions.Q146_CD.RealizeSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a 2-cell split

`Schoenflies/CellulationInvariants.lean` proves the *step* theorems of the second elementary
operation: given a realization `R'` of `S.splitFace d` standing in the relation
`SplitData.IsCrosscutSplit` to a realization `R` of `S`, the two invariants of
`lem:cellulation-invariants` propagate. Nothing built such an `R'`. This module does.

## Blueprint

* `def:generated-structure`, operation 2 — the 2-cell split whose realization is constructed
  here.
* `lem:cellulation-invariants` (i), (vii) — the invariants that
  `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` derives from the output of
  this module.
* `thm:general-crosscut` (`Schoenflies.crosscut_theorem`) — what turns the constructed ear into
  the two new open 2-cells; it is applied inside `IsCrosscutSplit.isRefinement`, and this module
  supplies its hypotheses.

## What is constructed

* `Schoenflies.CellStructure.SplitData.EarCrosscut` — the geometric input: an assignment of
  points to the ear's vertices and of parametrizations to the ear's edges, drawing the ear as a
  polygonal crosscut of the realized open 2-cell.
* `Schoenflies.CellStructure.SplitData.realize` — the realization of `S.splitFace d` built from
  `R` and such an ear. It is a `def` with lemmas, not an existential: `splitPos`,
  `splitDrawing`, `splitCell` are its three components, each with its own reduction lemmas
  (`splitCell_face₁`, `splitCell_of_mem_cells`, `splitCell_earVertex`, `splitCell_earEdge`, …),
  and `realize_pos` / `realize_drawing` / `realize_cell` connect them to the record.
* `Schoenflies.CellStructure.SplitData.isCrosscutSplit_realize` — the constructed realization
  stands in the relation `IsCrosscutSplit` to `R`. Composed with
  `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the full induction step.

## What is assumed, and who discharges it

`realize` itself asks only for `EarCrosscut`, whose six fields — `pos_source`, `pos_target`,
`injOn`, `isDrawing`, `subset_face`, `polygonal` — say that the ear is drawn as a simple
polygonal arc from `R.pos d.source` to `R.pos d.target` whose interior lies in the open 2-cell,
plus the seventh, `disjoint_skeleton`, which is a fact about `R` alone and is discharged by
`Realization.disjoint_cell_skeletonSet` from assertion (i). A producer that starts from
`Schoenflies.exists_crosscut_of_polyAccessible` — a polygonal arc inside the face with both
ends on its boundary — and cuts that arc into the ear's edges has all seven in hand.

`isCrosscutSplit_realize` asks in addition only for `R.IsCellDecomposition D` and
`R.IsFaceJordan`.

It used to ask for a third thing — that the two boundary paths of the split 2-cell share nothing
but their two ends — because `SplitData` did not imply it: its field `paths_disjoint` forbade
the two paths a common *edge* but said nothing about a common interior *vertex*, and with a
common interior vertex the two realized paths meet in a third point, so the `IsCutPair` clause
of `IsCrosscutSplit` is false. That gap has since been closed at the source: `SplitData` now
carries `paths_meet` and derives `paths_disjoint` from it. What follows is the record of a
condition that
producer of the `SplitData` chooses them (as the two arcs of one boundary cycle) and so can
supply it. If a later wave prefers it as a field of `SplitData`, that is the right place for it.

## The general lemmas this needed

Three facts about drawings and paths had no home on `main` and are proved here in the root
`Graph` namespace. If a second consumer appears they belong in `Schoenflies/Graph/`:

* `Graph.IsPath.map`, `Graph.walkVertices_map`, `Graph.IsPathGraph.map` — a path pushes forward
  along an injective relabelling of the vertices. `Graph.IsWalk.map` was already on `main` (in
  `Schoenflies/CombinatorialInvariance.lean`); the path version needs the injectivity, because
  the freshness clause is a *non*-membership.
* `Graph.IsDrawing.isArcBetween_walkPointSet` — **the point set of a drawn path is a simple
  arc between its two ends.** This is the workhorse: it is what makes the realized ear an arc
  (so `IsCrosscut` applies) and what makes each realized boundary path an arc (so `IsCutPair`
  applies). The induction is on `Graph.IsPath`, and the freshness clause of a path is exactly
  what rules out the returning point that would break `IsArcBetween.concatenate`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ## What a realization does to a walk

Two facts about an existing realization, both of the shape "the realized cells of a piece of
the skeleton occupy the point set that piece of the drawing occupies". They are what let the
crosscut theorem, which speaks of point sets, be fed from the cell structure, which speaks of
cells. -/

namespace Realization

variable (R : S.Realization)

theorem walkVertices_graph (u : γ) (W : List γ) :
    R.graph.walkVertices (R.pos u) W = R.pos '' S.skel.walkVertices u W :=
  Graph.walkVertices_map _ _ _

/-- **The realized cells of a path occupy the point set the drawn path occupies.** The two
differ only in the endpoints an open 1-cell drops, and those are the points of the 0-cells the
walk visits. -/
theorem cellUnion_pathCells {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    R.cellUnion (S.pathCells u W) = Graph.walkPointSet R.graph R.drawing (R.pos u) W := by
  have hsub : S.skel.walkVertices u W ⊆ V(S.skel) :=
    Graph.walkVertices_subset_vertexSet h.left_mem
  have hV : R.cellUnion (S.skel.walkVertices u W) = R.pos '' S.skel.walkVertices u W := by
    refine Set.Subset.antisymm (cellUnion_subset fun z hz => ?_) ?_
    · rw [R.cell_vertex (hsub hz)]
      exact Set.singleton_subset_iff.2 ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cell_subset_cellUnion hz (by rw [R.cell_vertex (hsub hz)]; rfl)
  rw [CellStructure.pathCells, cellUnion_union, hV, Graph.walkPointSet, R.walkVertices_graph]
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.union_subset (cellUnion_subset fun f hf => ?_) Set.subset_union_left
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    rw [R.cell_edge hl]
    exact fun x hx => Or.inr (Set.mem_biUnion hf hx.1)
  · refine Set.union_subset Set.subset_union_right (Set.iUnion₂_subset fun f hf x hx => ?_)
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · exact Or.inr ⟨a, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_left⟩, rfl⟩
      · exact Or.inr ⟨b, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_right⟩, rfl⟩
    · exact Or.inl (cell_subset_cellUnion hf (by rw [R.cell_edge hl]; exact ⟨hx, hxab⟩))

/-- The drawn skeleton is covered by the open cells of dimension 0 and 1. -/
theorem skeletonSet_subset_cellUnion :
    R.skeletonSet ⊆ R.cellUnion (V(S.skel) ∪ E(S.skel)) := by
  intro x hx
  rcases hx with hx | hx
  · rw [Realization.vertexSet_graph] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
    rw [R.cell_vertex hz]
    rfl
  · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx
    rw [Realization.edgeSet_graph] at hf
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.left_mem) ?_
        rw [R.cell_vertex hl.left_mem]
        rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.right_mem) ?_
        rw [R.cell_vertex hl.right_mem]
        rfl
    · refine cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
      rw [R.cell_edge hl]
      exact ⟨hxf, hxab⟩

/-- **An open 2-cell misses the drawn skeleton.** Immediate from the disjointness clause of
assertion (i): the skeleton is covered by cells of lower dimension. -/
theorem disjoint_cell_skeletonSet {D : Set Plane} (hcd : R.IsCellDecomposition D) {F : γ}
    (hF : F ∈ S.faces) : Disjoint (R.cell F) R.skeletonSet := by
  refine Set.disjoint_right.2 fun x hx hxF => ?_
  obtain ⟨σ, hσ, hxσ⟩ := mem_cellUnion_iff.1 (R.skeletonSet_subset_cellUnion hx)
  have hne : F ≠ σ := by
    rintro rfl
    rcases hσ with hσ | hσ
    exacts [Set.disjoint_left.1 S.disjoint_faces_vertexSet hF hσ,
      Set.disjoint_left.1 S.disjoint_faces_edgeSet hF hσ]
  have hσc : σ ∈ S.cells := by
    rcases hσ with hσ | hσ
    exacts [S.mem_cells_of_mem_vertexSet hσ, S.mem_cells_of_mem_edgeSet hσ]
  exact Set.disjoint_left.1 (hcd.disjoint (S.mem_cells_of_mem_faces hF) hσc hne) hxF hxσ

end Realization

/-! ## The ear, drawn

`SplitData` fixes the *abstract* ear: a path graph `d.ear` glued to the skeleton at
`d.source` and `d.target`. Drawing it means choosing a point for each of its vertices and a
parametrization for each of its edges. `EarCrosscut` is the bundle of conditions under which
that drawing is a polygonal crosscut of the realized open 2-cell `R.cell d.face`. -/

namespace SplitData

variable (d : S.SplitData)

theorem source_mem_cells₂ : d.source ∈ d.cells₂ :=
  Or.inr Graph.mem_walkVertices_self

theorem target_mem_cells₂ : d.target ∈ d.cells₂ :=
  Or.inr d.isPath₂.isWalk.target_mem_walkVertices

/-- **The cells strictly below the split 2-cell are the cells of its two boundary paths.**
This is `SplitData.sub_face` read as a set identity; with assertion (i) it identifies the
frontier of the old open 2-cell with the two realized boundary paths. -/
theorem subcells_face_diff : S.subcells d.face \ {d.face} = d.cells₁ ∪ d.cells₂ := by
  ext σ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, CellStructure.mem_subcells_iff, Set.mem_union]
  constructor
  · rintro ⟨⟨-, hsub⟩, hne⟩
    rcases d.sub_face.1 hsub with rfl | h
    · exact absurd rfl hne
    · exact h
  · intro h
    refine ⟨⟨?_, d.sub_face.2 (Or.inr h)⟩, ?_⟩
    · rcases h with h | h
      exacts [d.cells₁_subset h, d.cells₂_subset h]
    · rcases h with h | h
      exacts [d.cells₁_ne_face h, d.cells₂_ne_face h]

/-! ## The realization built from a drawn ear -/

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

theorem splitCell_face₁ : d.splitCell R earPos earDraw d.face₁ =
    inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [if_pos rfl]

theorem splitCell_face₂ : d.splitCell R earPos earDraw d.face₂ =
    inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [if_neg (Ne.symm d.face_ne), if_pos rfl]

/-- **The frontier of the old open 2-cell is the union of its two realized boundary paths.**
`SplitData.sub_face` says which cells lie below the split 2-cell, and assertion (i) turns the
union of those open cells into the topological frontier. -/
theorem frontier_cell_face {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    frontier (R.cell d.face) = R.cellUnion d.cells₁ ∪ R.cellUnion d.cells₂ := by
  rw [← hJ.faceBoundary_eq hcd d.face_mem, Realization.faceBoundary, d.subcells_face_diff,
    Realization.cellUnion_union]

theorem pos_source_mem_cellUnion_cells₁ : R.pos d.source ∈ R.cellUnion d.cells₁ :=
  Realization.cell_subset_cellUnion d.source_mem_cells₁
    (by rw [R.cell_vertex d.source_mem_skel]; rfl)

theorem pos_source_mem_cellUnion_cells₂ : R.pos d.source ∈ R.cellUnion d.cells₂ :=
  Realization.cell_subset_cellUnion d.source_mem_cells₂
    (by rw [R.cell_vertex d.source_mem_skel]; rfl)

theorem pos_target_mem_cellUnion_cells₁ : R.pos d.target ∈ R.cellUnion d.cells₁ :=
  Realization.cell_subset_cellUnion d.target_mem_cells₁
    (by rw [R.cell_vertex d.target_mem_skel]; rfl)

theorem pos_target_mem_cellUnion_cells₂ : R.pos d.target ∈ R.cellUnion d.cells₂ :=
  Realization.cell_subset_cellUnion d.target_mem_cells₂
    (by rw [R.cell_vertex d.target_mem_skel]; rfl)

/-- **A realized boundary path is a simple arc between the ear's two ends.** -/
theorem isArcBetween_cellUnion_cells₁ :
    IsArcBetween (R.cellUnion d.cells₁) (R.pos d.source) (R.pos d.target) := by
  rw [cells₁, R.cellUnion_pathCells d.isPath₁.isWalk]
  exact R.isDrawing.isArcBetween_walkPointSet (d.isPath₁.map R.injOn_pos)
    (fun h => d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h))

theorem isArcBetween_cellUnion_cells₂ :
    IsArcBetween (R.cellUnion d.cells₂) (R.pos d.source) (R.pos d.target) := by
  rw [cells₂, R.cellUnion_pathCells d.isPath₂.isWalk]
  exact R.isDrawing.isArcBetween_walkPointSet (d.isPath₂.map R.injOn_pos)
    (fun h => d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h))

/-- **The two boundary paths cut the old 2-cell's boundary curve in two.**

This is where `SplitData.paths_meet` is spent, and it is the only place: `paths_disjoint` alone
forbids the two paths a common *edge* but not a common interior *vertex*, and with a common
interior vertex the two realized paths meet in more than the two cut points. See the module
docstring. -/
theorem isCutPair_of_inter {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    IsCutPair (frontier (R.cell d.face)) (R.pos d.source) (R.pos d.target)
      (R.cellUnion d.cells₁) (R.cellUnion d.cells₂) where
  fst := isArcBetween_cellUnion_cells₁
  snd := isArcBetween_cellUnion_cells₂
  union_eq := (frontier_cell_face hcd hJ).symm
  inter_eq := by
    refine Set.Subset.antisymm (fun x ⟨hx₁, hx₂⟩ => ?_) ?_
    · obtain ⟨σ, hσ, hxσ⟩ := Realization.mem_cellUnion_iff.1 hx₁
      obtain ⟨τ, hτ, hxτ⟩ := Realization.mem_cellUnion_iff.1 hx₂
      have hστ : σ = τ := by
        by_contra hne
        exact Set.disjoint_left.1
          (hcd.disjoint (d.cells₁_subset hσ) (d.cells₂_subset hτ) hne) hxσ hxτ
      subst hστ
      have hmem : σ ∈ ({d.source, d.target} : Set γ) := d.paths_meet ▸ ⟨hσ, hτ⟩
      rcases hmem with rfl | rfl
      · rw [R.cell_vertex d.source_mem_skel] at hxσ
        exact Or.inl hxσ
      · rw [R.cell_vertex d.target_mem_skel] at hxσ
        exact Or.inr hxσ
    · rintro x (rfl | rfl)
      exacts [⟨pos_source_mem_cellUnion_cells₁, pos_source_mem_cellUnion_cells₂⟩,
        ⟨pos_target_mem_cellUnion_cells₁, pos_target_mem_cellUnion_cells₂⟩]

namespace EarCrosscut

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- **The drawn ear is a crosscut of the old Jordan face.** -/
theorem isCrosscut_earSet {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    IsCrosscut (frontier (R.cell d.face)) (d.earSet earPos earDraw)
      (R.pos d.source) (R.pos d.target) where
  curve := hJ.isJordanCurve d.face_mem
  arc := hE.isArcBetween_earSet
  polygonal := hE.polygonal
  left_mem := (frontier_cell_face hcd hJ) ▸ Or.inl pos_source_mem_cellUnion_cells₁
  right_mem := (frontier_cell_face hcd hJ) ▸ Or.inl pos_target_mem_cellUnion_cells₁
  sdiff_subset := by
    rw [← hJ.cell_eq_inside d.face_mem]
    exact hE.subset_face

/-- The closure of an ear edge's open arc is the closed arc. -/
theorem closure_edgeArc_diff {f a b : γ} (hl : d.ear.IsLink f a b) :
    closure (Graph.edgeArc earDraw f \ {earPos a, earPos b}) = Graph.edgeArc earDraw f := by
  have harc : IsArcBetween (Graph.edgeArc earDraw f) (earPos a) (earPos b) :=
    hE.isDrawing.edge_isArcBetween (hl.map earPos)
  refine Set.Subset.antisymm (closure_minimal Set.sdiff_subset harc.isArc.isCompact.isClosed) ?_
  intro x hx
  by_cases hxab : x ∈ ({earPos a, earPos b} : Set Plane)
  · rcases hxab with rfl | rfl
    exacts [harc.left_mem_closure_diff, harc.right_mem_closure_diff]
  · exact subset_closure ⟨hx, hxab⟩

end EarCrosscut

/-! ## The realization -/

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- **The realized ear is the drawn ear.** The open cells of the ear together with the two old
0-cells at its ends occupy exactly the crosscut. -/
theorem cellUnion_earCells :
    (realize R d earPos earDraw hE).cellUnion d.earCells = d.earSet earPos earDraw := by
  refine Set.Subset.antisymm (Realization.cellUnion_subset fun σ hσ => ?_) ?_
  · have hσ' : σ ∈ V(d.ear) ∪ E(d.ear) := hσ
    rcases hσ' with hσ' | hσ'
    · rw [realize_cell, hE.splitCell_earVertex hσ']
      exact Set.singleton_subset_iff.2 (EarCrosscut.mem_earSet_of_mem_ear hσ')
    · rw [realize_cell, splitCell_earEdge hσ']
      exact Set.Subset.trans Set.sdiff_subset (EarCrosscut.edgeArc_subset_earSet hσ')
  · intro x hx
    have hx' : x ∈ V(d.earGraph earPos) ∪
        ⋃ e ∈ E(d.earGraph earPos), Graph.edgeArc earDraw e := hx
    by_cases hxv : x ∈ earPos '' V(d.ear)
    · obtain ⟨z, hz, rfl⟩ := hxv
      refine Realization.cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
      rw [realize_cell, hE.splitCell_earVertex hz]
      rfl
    · rcases hx' with hx' | hx'
      · rw [d.vertexSet_earGraph] at hx'
        exact absurd hx' hxv
      · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx'
        rw [d.edgeSet_earGraph] at hf
        refine Realization.cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
        rw [realize_cell, splitCell_earEdge hf]
        exact ⟨hxf, hxv⟩

/-- **The open cells the ear creates are the crosscut minus its two endpoints.** -/
theorem cellUnion_earNewCells :
    (realize R d earPos earDraw hE).cellUnion d.earNewCells =
      d.earSet earPos earDraw \ {R.pos d.source, R.pos d.target} := by
  refine Set.Subset.antisymm (Realization.cellUnion_subset fun σ hσ => ?_) ?_
  · have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    rcases hσ' with ⟨hσV, hσn⟩ | hσE
    · rw [realize_cell, hE.splitCell_earVertex hσV]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσn
      push Not at hσn
      refine Set.singleton_subset_iff.2 ⟨EarCrosscut.mem_earSet_of_mem_ear hσV, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hσn.1 (hE.injOn hσV d.source_mem_ear (h.trans hE.pos_source.symm))
      · exact hσn.2 (hE.injOn hσV d.target_mem_ear (h.trans hE.pos_target.symm))
    · rw [realize_cell, splitCell_earEdge hσE]
      rintro x ⟨hxa, hxv⟩
      refine ⟨EarCrosscut.edgeArc_subset_earSet hσE hxa, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact hxv ⟨d.source, d.source_mem_ear, hE.pos_source⟩
      · exact hxv ⟨d.target, d.target_mem_ear, hE.pos_target⟩
  · rintro x ⟨hx, hxn⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxn
    push Not at hxn
    have hx' : x ∈ V(d.earGraph earPos) ∪
        ⋃ e ∈ E(d.earGraph earPos), Graph.edgeArc earDraw e := hx
    by_cases hxv : x ∈ earPos '' V(d.ear)
    · obtain ⟨z, hz, rfl⟩ := hxv
      have hzs : z ≠ d.source := fun h => hxn.1 (by rw [h, hE.pos_source])
      have hzt : z ≠ d.target := fun h => hxn.2 (by rw [h, hE.pos_target])
      have hzmem : z ∈ V(d.ear) \ ({d.source, d.target} : Set γ) := by
        refine ⟨hz, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨hzs, hzt⟩
      refine Realization.cell_subset_cellUnion (Set.mem_union_left _ hzmem) ?_
      rw [realize_cell, hE.splitCell_earVertex hz]
      rfl
    · rcases hx' with hx' | hx'
      · rw [d.vertexSet_earGraph] at hx'
        exact absurd hx' hxv
      · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx'
        rw [d.edgeSet_earGraph] at hf
        refine Realization.cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
        rw [realize_cell, splitCell_earEdge hf]
        exact ⟨hxf, hxv⟩

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.MatchedSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The skeleton homeomorphism across a 2-cell split

`Schoenflies/RealizeSplit.lean` builds **one** realization of `S.splitFace d` from a realization
`R` of `S` and a drawing of the ear as a polygonal crosscut. A *matched* cellulation is two
realizations of one abstract structure together with the skeleton homeomorphism between them
(`def:matched-pair` clause 3), so the split has to be performed on both sides at once and the
skeleton homeomorphism has to be carried across. That is what this module does.

## Blueprint

* `def:matched-pair`, clause 3 — the chosen homeomorphism `g : |Γ| → |Γ'|`, recorded as
  `Schoenflies.CellStructure.SkeletonHomeo`, extended across one split.
* `def:generated-structure`, operation 2 — the 2-cell split, whose two realizations are the
  output of `Schoenflies.CellStructure.SplitData.realize`.

## What is constructed

* `Schoenflies.CellStructure.SplitData.skeletonSet_realize` — **the split's realized 1-skeleton
  is the old one together with the drawn ear**, as a point set. Everything else rests on this.
* `Schoenflies.CellStructure.SplitData.EarHomeo` — the chosen homeomorphism between the two
  drawn ears (see the next section).
* `Schoenflies.CellStructure.SplitData.EarHomeo.symm` — the same chosen matching with source
  and target reversed, used by finite-transfer direction (b).
* `Schoenflies.CellStructure.SplitData.splitMap` / `splitInvMap` — the transported map and its
  inverse, as plain functions `Plane → Plane`: `g` on the old skeleton, the ear map off it.
* `Schoenflies.CellStructure.SplitData.splitHomeo` — the `SkeletonHomeo` between the two split
  realizations. A `def` with lemmas, not an `∃`-packaged bundle.
* `Schoenflies.CellStructure.SplitData.splitHomeo_eqOn` — **the transported map agrees with `g`
  on the whole old skeleton.** This is exactly `Schoenflies.StageSequence.skelHomeo_succ` at a
  split step, and it is the reason the construction is "extend `g` by the ear map" rather than
  "rebuild a homeomorphism from scratch".

## How the ear map is presented, and why

Two shapes were available.

(a) **As data**: a map `Plane → Plane` (with an inverse) carrying the drawn source ear onto the
drawn target ear, vertex to corresponding vertex and edge arc to corresponding edge arc.

(b) **Built edge by edge** from the two `EarCrosscut`s, by composing one edge's parametrization
with the inverse of the other's.

This module takes **(a)**, as `EarHomeo`. The reason is the consumer, not the construction:
`def:matched-pair` clause 3 says that `g` *restricts to a fixed chosen homeomorphism* on each
corresponding pair of cells, so a caller assembling a matched pair is holding such a chosen
homeomorphism already — for the old cells it is `g` itself, and for the ear's cells it is
whatever the producer of the two crosscuts chose. Shape (b) would manufacture a second,
different homeomorphism from the two parametrizations, and the caller would then have to prove
that its own choice agrees with the manufactured one. It would also silently fix an orientation
of every ear edge: `Graph.IsDrawing.edge_param` is orientation-free, so `earDraw₁ f 0` and
`earDraw₂ f 0` need not be the ends that correspond, and (b) would need the `SubdivData.leftParam`
trick of `Schoenflies/RealizeSubdiv.lean` replayed per edge.

Every field of `EarHomeo` is therefore something the caller supplies, and none of them mentions
`R₁`, `R₂` or `g`: the ear map is a statement about the two drawn ears alone. In particular
**no compatibility hypothesis between `m` and `g` is asked for**, because none is needed: at the
ear's two ends `m.toFun` and `g.toFun` are *forced* to agree, both being pinned to
`R₂.pos d.source` and `R₂.pos d.target` — `m` by `earPos_apply` together with the two `pos_source`
/ `pos_target` clauses of the two `EarCrosscut`s, and `g` by its own `pos_apply`. That is
`EarHomeo.toFun_pos_source` / `toFun_pos_target` below.

## The proof, in one paragraph

The new skeleton is a union of two **closed** sets — the old realized skeleton
(`Realization.isCompact_skeletonSet`) and the drawn ear, which is an arc
(`EarCrosscut.isArcBetween_earSet`) and hence compact. Continuity of the transported map is the
pasting lemma `Schoenflies.Plane.continuousOn_union_of_isClosed` on those two pieces; the two
pieces meet exactly in the ear's two ends (`EarCrosscut.earSet_inter_skeletonSet`, which is
`SplitData.vertexSet_inter` made geometric), and there the two prescriptions agree. Injectivity
and the two inverse laws are injectivity on each piece plus the fact that the *images* also meet
only in the two images of the ends — for which the target-side
`EarCrosscut.earSet_inter_skeletonSet` is again what is spent. `pos_apply` and `edgeArc_image`
split into the old cells, where `g`'s own fields serve verbatim, and the ear's cells, where
`EarHomeo`'s two matching clauses are the statement.

## What is *not* here

The **subdivision** analogue — the transported skeleton homeomorphism across an edge
subdivision — is deliberately absent. It is being built concurrently on branch
`wt/arc-monotone`, where the missing ingredient (a homeomorphism between two arcs fixing their
ends is monotone, hence carries initial subarcs to initial subarcs — see the section
"What is *not* here" of `Schoenflies/RealizeSubdiv.lean`) is the actual content. Nothing below
depends on it, and nothing below should be duplicated there: this module is the split case only.

## The general lemma this needed

`Graph.pointSet_congr` — the point set of a plane graph depends on the drawing only through the
arcs of the graph's own edges. It is stated in the root `Graph` namespace next to
`Graph.pointSet_union` (which lives in `Schoenflies/FaceCycles.lean`); if a second consumer
appears it belongs there or in `Schoenflies/Graph/Drawing.lean`.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace SplitData

variable {d : S.SplitData}

/-! ## The realized 1-skeleton of a split

A 2-cell split adds the drawn ear to the drawn 1-skeleton and changes nothing else. This is the
geometric statement the whole module rests on: it turns every clause of `SkeletonHomeo`, which
quantifies over the *new* skeleton, into a pair of clauses over the two closed pieces. -/

/-- **A 2-cell split only grows the realized 1-skeleton.** This is the field
`Schoenflies.StageSequence.skeletonSet_mono` at a split step. -/
theorem skeletonSet_subset_realize {R : S.Realization} {earPos : γ → Plane}
    {earDraw : γ → ℝ → Plane} (hE : d.EarCrosscut R earPos earDraw) :
    R.skeletonSet ⊆ (d.realize R earPos earDraw hE).skeletonSet :=
  (skeletonSet_realize hE).symm ▸ Set.subset_union_left

/-! ## The chosen homeomorphism between the two drawn ears -/

/-! ## The transported map -/

/-! ## The skeleton homeomorphism across the split -/

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite transfer, direction (a): toward the square

`thm:finite-transfer` is the largest single statement of the manuscript. This module states it —
in full, with every hypothesis — for **direction (a)** only, and proves as much of its four-step
proof as is within reach of what is on `main`.

Direction (b) is deliberately absent: its extra accessibility problem at the wild source
boundary needs `lem:tangent-cone`, `lem:compact-separation`(c) and the fresh-point bookkeeping
of the target mesh, none of which enters (a).

## The statement, and how it is read

The blueprint's (a) reads: *let `(Γ, Γ')` be a generated matched cellulation; suppose `H` is a
finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`, with every
nonboundary edge polygonal, and with `|H| ∖ C` connected; then the common subdivision can be
made on `Γ'`, and `H` can be transferred to an admissible target realization `H'`; the resulting
generated matched cellulation refines the old one by explicit parent maps.*

Four objects carry that sentence.

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible` and
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`. The weak form
  is exactly the strong one with connectedness of the open nonboundary part waived, which is
  what `def:generated-structure` requires of an intermediate stage and what
  `rem:intermediate-disconnection` insists on.
* `Schoenflies.GeneratedPair` — a generated matched cell structure *with its geometry*: the
  abstract structure, its two realizations, the skeleton homeomorphism, and the two cell
  decompositions. This is the Lean form of "`(Γ, Γ')` is a generated matched cellulation".
  It is a bundle of **data**, not an existential: every consumer reads `.src`, `.tgt`, `.homeo`
  by name.
* `Schoenflies.IsSourceExtension` — the hypotheses on `H`.
* `Schoenflies.IsTransferOf` — the conclusion, relating the new pair to the old one by an
  explicit parent map.

The one place where the Lean statement is *weaker in form* than the prose, and deliberately so:
"`H` can be transferred" is recorded as `T.src.skeletonSet = pointSet H Hdraw`, an equality of
point sets, rather than as a graph isomorphism onto `H`. The reason is step 1: the common
subdivision inserts a vertex at every intersection of a new edge with an old one, so the source
realization of the transferred structure realizes a *subdivision* of `H`, never `H` itself. What
survives verbatim is what the construction uses downstream — the occupied set, the
2-connectivity (which `lem:combinatorial-invariance` moves to the target) and the refinement.

## What is proved here

* **Step 1, the overlay** — `Schoenflies.exists_overlay_of_biUnion_finite`: the union of
  finitely many nondegenerate polygonal sets is the point set of a finite plane graph drawn by
  straight segments. That is `lem:polygonal-overlay` in the form step 1 needs, bridging
  `Schoenflies.polygonal_overlay`, which is stated for a list of segments, to the finite family
  of polygonal *arcs* a skeleton stage arrives as.
* **Step 4, target side** — `Schoenflies.exists_target_crosscut` and
  `Schoenflies.exists_target_crosscut_split`. In direction (a) the target face `F*` is a
  polygonal Jordan region in the square by `lem:cellulation-invariants`(vii); every point of its
  boundary is polygonally accessible from its interior by `lem:polygonal-side-accessibility`
  (target half); and `lem:accessible-endpoints` gives a polygonal crosscut `P* ⊆ closure F*`
  from `v*` to `w*`, which by `thm:general-crosscut` splits `F*` into exactly the two Jordan
  regions bounded by `P*` and the two boundary paths. These constructions supply the complete
  target-side argument.
* **The second sentence of step 2** — `…IsCellDecomposition.exists_unique_face_subset_cell` and
  `…IsCellDecomposition.exists_face_of_ear`: the interior of an ear lies in one current face,
  because it is connected and disjoint from the current skeleton, and its two endpoints then lie
  on that face's boundary cycle. `IsCellDecomposition.cellsAbsorb` derives the formerly named
  `CellsAbsorb` premise from the maintained cell-decomposition and Jordan-face invariants, so
  this requires no additional interface.
* **One ear insertion, step 3** — `exists_sourceEarStepData`,
  `EarCrosscut.exists_matched_target`, `earStepConstruction`, and `earStep`. The ambient source
  path is given fresh abstract cell names, its face split is realized on both sides, and a
  parameter-matching homeomorphism divides the target polygonal crosscut into exactly the same
  abstract edges. Matching source and target crosscuts then produce the next pair, compose both
  refinement maps, preserve every bundle invariant, and enlarge the occupied source graph by
  exactly the supplied ear, under the necessary `[Infinite γ]` name supply.
* **The last paragraph of the proof** — `Schoenflies.GeneratedPair.src_isAdmissible` and
  `Schoenflies.GeneratedPair.tgt_isAdmissible`. Admissibility of the *final* object is
  recovered from `lem:combinatorial-invariance`: the reproduced realization has the same
  2-connectivity and the same connectedness of the open nonboundary part as the given one.
  This uses only the hypotheses of the finite-transfer statement.
* **The induction scheme, steps 2 and 3** — `Schoenflies.transfer_of_ears`. With `earStep`
  supplying each insertion, `lem:relative-ear` in its iterated form
  (`Graph.IsTwoConnected.ear_decomposition`) transfers the whole extension. This is the backbone
  of the induction, and it honours `rem:intermediate-disconnection`: the invariant carried
  through the induction, `Schoenflies.IsPartialTransferOf`, asks only for *weak* admissibility,
  and connectedness of the open nonboundary part is restored only at the very end.

## Completion of step 1

This module keeps `Schoenflies.CommonSubdivision` as the compositional interface consumed by the
ear induction.  `Schoenflies/CommonSubdivision.lean` constructs it: it traces the part of `H`
supported on the old skeleton, proves that trace 2-connected, and carries all of its finitely many
vertices through matched source/target edge subdivisions.  Consequently direction (a) is exposed
there as `Schoenflies.finite_transfer_toward_square`.

## Blueprint

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible`,
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`.
* `Schoenflies.GeneratedPair` — `def:generated-structure` with its two realizations,
  `def:matched-pair` and `def:matched-cellulation` folded in.
* `Schoenflies.IsSourceExtension` — the hypotheses of `thm:finite-transfer`(a) on `H`.
* `Schoenflies.IsPartialTransferOf`, `Schoenflies.IsTransferOf` — the conclusion of
  `thm:finite-transfer`, at an intermediate stage and at the end.
* `Schoenflies.exists_target_crosscut`, `Schoenflies.exists_target_crosscut_split` —
  the fourth paragraph of the proof of `thm:finite-transfer`, direction (a):
  `lem:cellulation-invariants`(vii) + `lem:polygonal-side-accessibility` +
  `lem:accessible-endpoints` + `thm:general-crosscut`.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.exists_unique_face_subset_cell`,
  `…IsCellDecomposition.exists_face_of_ear`,
  `…IsCellDecomposition.sub_of_pos_mem_closure_cell` — "the interior of each ear lies in one
  current face", with the two supporting facts
  `Schoenflies.CellStructure.Realization.cell_subset_skeletonSet` (hoisted to
  `Schoenflies/CombinatorialInvariance.lean`) and
  `Schoenflies.CellStructure.Realization.mem_faces_of_notMem_skeletonSet`.
* `Schoenflies.CellStructure.Realization.pos_mem_closure_cell_congr`,
  `Schoenflies.exists_target_ear` — "let `F*, v*, w*` be the corresponding face and endpoints in
  the other realization", and the whole fourth paragraph assembled from the source-side data.
* `Schoenflies.GeneratedPair.src_isAdmissible`, `Schoenflies.GeneratedPair.tgt_isAdmissible` —
  the last paragraph of the proof, via `lem:combinatorial-invariance`.
* `Schoenflies.exists_overlay_of_biUnion_finite` — `lem:polygonal-overlay` and
  `rem:polygonal-overlay-convention`, for a finite family of polygonal sets: the first half of
  step 1.
* `Schoenflies.earStep` — step 3; `Schoenflies.CommonSubdivision` — the step-1 interface,
  discharged by `Schoenflies.commonSubdivision` in `CommonSubdivision.lean`.
* `Schoenflies.transfer_of_ears_of_commonSubdivision_of_earStep`,
  `Schoenflies.finite_transfer_toward_square_of_commonSubdivision_of_earStep` — the
  finite-transfer induction parametrized by its two construction interfaces.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

/-! ### `def:admissible-graph`

An admissible graph in the closed Jordan domain is a finite 2-connected plane graph whose outer
cycle is `C`, whose edges not contained in `C` are polygonal arcs with interiors in `D`, and
whose open nonboundary part `|Γ| ∖ C` is connected. A *weakly* admissible graph satisfies
everything but the last clause.

`outer` is the realized outer cycle and `dom` the closed domain; the open domain is `dom ∖
outer`. On the source side that reads `C` and `C ∪ D`; on the target side `S` and `Q`. -/

namespace CellStructure

namespace SplitData.EarCrosscut

variable {S : CellStructure γ}
variable {d : S.SplitData} {R : S.Realization} {outer dom : Set Plane}
  {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

/-- Weak admissibility is preserved by adjoining a polygonal ear inside one old face.  This is
the geometric bookkeeping common to the source and target halves of every ear step. -/
theorem isWeaklyAdmissible_realize (hE : d.EarCrosscut R earPos earDraw)
    (hR : R.IsWeaklyAdmissible outer dom) (hcd : R.IsCellDecomposition dom)
    (hpoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc earDraw e)) :
    (d.realize R earPos earDraw hE).IsWeaklyAdmissible outer dom where
  isTwoConnected := by
    change ((S.splitFace d).skel.map (d.splitPos R earPos)).IsTwoConnected
    rw [hE.splitGraph_eq]
    have hcompat : R.graph.Compatible (d.earGraph earPos) :=
      Graph.Compatible.of_disjoint_edgeSet (by
        rw [Realization.edgeSet_graph, d.edgeSet_earGraph]
        exact d.disjoint_edgeSet)
    exact hR.isTwoConnected.ear hcompat hE.isPathGraph_earGraph source_ne_target_pos
      (by rw [R.vertexSet_graph]; exact ⟨d.source, d.source_mem_skel, rfl⟩)
      (by rw [R.vertexSet_graph]; exact ⟨d.target, d.target_mem_skel, rfl⟩)
  outerSet_eq := by
    change Graph.pointSet ((S.splitFace d).outerGraph.map (d.splitPos R earPos))
      (d.splitDrawing R earDraw) = outer
    rw [CellStructure.splitFace_outerGraph]
    have hgraph : S.outerGraph.map (d.splitPos R earPos) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq (S.outerGraph_le.vertexSet_mono hz)
    rw [hgraph]
    calc
      Graph.pointSet (S.outerGraph.map R.pos) (d.splitDrawing R earDraw) =
          Graph.pointSet (S.outerGraph.map R.pos) R.drawing := by
        apply Graph.pointSet_congr
        intro e he
        rw [Graph.edgeSet_map] at he
        exact d.edgeArc_splitDrawing_of_mem_skel (S.outerGraph_le.edgeSet_mono he)
      _ = R.outerSet := rfl
      _ = outer := hR.outerSet_eq
  isPolygonal := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_skel he]
      exact hR.isPolygonal he houter
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_ear he]
      exact hpoly he
  cell_subset := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · rw [CellStructure.SplitData.realize_cell,
        d.splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet he)]
      exact hR.cell_subset he houter
    · rw [CellStructure.SplitData.realize_cell, d.splitCell_earEdge he]
      intro x hx
      have hxEar : x ∈ d.earSet earPos earDraw :=
        edgeArc_subset_earSet he hx.1
      have hxEnds : x ∉ ({R.pos d.source, R.pos d.target} : Set Plane) := by
        rintro (rfl | rfl)
        · exact hx.2 ⟨d.source, d.source_mem_ear, hE.pos_source⟩
        · exact hx.2 ⟨d.target, d.target_mem_ear, hE.pos_target⟩
      have hxFace : x ∈ R.cell d.face := hE.subset_face ⟨hxEar, hxEnds⟩
      refine ⟨hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem) hxFace, ?_⟩
      intro hxOuter
      have hxSkel : x ∈ R.skeletonSet := by
        apply R.outerSet_subset_skeletonSet
        rw [hR.outerSet_eq]
        exact hxOuter
      exact Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd d.face_mem) hxFace hxSkel
  skeletonSet_subset := by
    rw [d.skeletonSet_realize hE]
    refine Set.union_subset hR.skeletonSet_subset ?_
    intro x hx
    by_cases hxEnds : x ∈ ({R.pos d.source, R.pos d.target} : Set Plane)
    · rcases hxEnds with rfl | rfl
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.source_mem_skel)
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.target_mem_skel)
    · exact hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem)
        (hE.subset_face ⟨hx, hxEnds⟩)

end SplitData.EarCrosscut

end CellStructure

/-! ### A generated matched cell structure, with its geometry

`def:generated-structure` says what the *abstract* object is; `GeneratedStructure` in
`Schoenflies/GeneratedStructure.lean` is that. What a transfer produces, and what the
finite-transfer theorem consumes, is the abstract object together with its two realizations, the
skeleton homeomorphism between them, and the two cell decompositions of
`lem:cellulation-invariants`(i). That bundle is `GeneratedPair`.

It is data, not a `Prop`: a consumer reads `.src`, `.tgt`, `.homeo`, `.str` by name. -/

/-! ### The hypotheses of direction (a) on the given extension

*`H` is a finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`,
with every nonboundary edge polygonal, and with `|H| ∖ C` connected.*

"Contains a subdivision of `Γ`" is recorded by three clauses: every old vertex is a vertex of
`H`; the old skeleton is inside `|H|`; and any edge of `H` whose nonvertex part meets an *open*
old edge lies inside that old edge. Together those say that each old edge is cut into a chain of
`H`-edges. A transverse crossing is allowed only at a vertex of `H`, exactly as produced by the
polygonal overlay.

"With outer cycle `C`, with every nonboundary edge polygonal" is `edge_dichotomy`: each edge of
`H` either lies inside the outer curve or is polygonal with its interior in the open domain.
Recording the outer cycle as a *subgraph* would put data inside a `Prop`; this reading is what
every step of the proof actually uses, and `outer ⊆ pointSet H Hdraw` comes for free from
`skeletonSet_subset`. -/

/-! ### The conclusion

`IsPartialTransferOf T P B par` is the invariant the induction of steps 2–3 carries: `T` is a
generated pair refining `P` along `par` whose source realization occupies exactly what the
current subgraph `B` of `H` occupies. It asks for **no** connectedness of the open nonboundary
part — `rem:intermediate-disconnection` — because an ear with both endpoints on the outer cycle
really does disconnect it, and later ears reconnect it.

`IsTransferOf` is the same with admissibility of both final realizations added; that is the
theorem's conclusion, and `GeneratedPair.src_isAdmissible` / `GeneratedPair.tgt_isAdmissible`
are what produce it from the connectedness hypothesis on `H`. -/

/-! #### The output data of one realized ear

The former `EarStep` interface ended directly in an existential `GeneratedPair`.  That hid all
of the actual constructor data and made the last half of the proof impossible to reuse or
inspect.  `EarStepData` exposes the abstract split, its two geometric crosscuts, and the chosen
map between them.  Its `pair` and `isPartialTransferOf_pair` declarations below perform the
assembly. -/

/-! #### Locating the source face of a graph-theoretic ear -/

/-! ### The two assumed steps

Both are strictly weaker than `thm:finite-transfer`(a) itself, and both are statements a later
module can discharge without circularity.

`CommonSubdivision` is **step 1**: after overlaying the proposed polygonal nonboundary edges
with the old polygonal nonboundary skeleton and subdividing at every intersection — and
transferring each new point to the other realization along the chosen edge parametrization —
the old skeleton is literally a subgraph of the new one on both sides. In Lean that is: some
2-connected subgraph `K ≤ H` carries a generated pair refining the given one. It is not the
theorem: it makes only edge subdivisions, inserts no ear, and its conclusion is about a subgraph
of `H`, not about `H`.

`EarStep` is **step 3**: one ear insertion — at most two edge subdivisions followed by one
2-cell split — carries a partial transfer of `B` to a partial transfer of `B` with the ear glued
on. Its geometric core in direction (a) is `Schoenflies.exists_target_crosscut_split` below,
which is proved here; only the abstract-data bookkeeping around it is assumed.

**`EarStep` carries `[Infinite γ]`, and without it the hypothesis is false.** Every cell of
every structure in sight is a *name* drawn from the one type `γ`: `V(skel)`, `E(skel)` and
`faces` are three disjoint subsets of it. An ear insertion consumes fresh names — one per
interior vertex of the ear, one per ear edge, and two for the 2-cells the split creates
(`SplitData.edge_fresh`, `.vertex_fresh`, `.face₁_notMem`, `.face₂_notMem`) — while the
conclusion `IsPartialTransferOf T' P (B ∪ ear) Hdraw par'` forces `T'` to realize a subdivision
of the enlarged graph, so `V(B ∪ ear) ⊆ V(T'.src.graph) = T'.src.pos '' V(T'.str.skel)` and the
new skeleton must occupy strictly more of the plane than the old one. On a finite `γ` those
demands eventually exceed the supply: a structure realizing a subdivision of a 2-connected graph
with `e` edges needs at least `e` edge names, at least as many vertex names, and at least one
face name per complementary region, all pairwise distinct inside `γ`. A `γ` large enough to
carry the transfer of `B` and too small to carry the transfer of `B` with one more ear makes the
hypotheses of `EarStep` satisfiable and its conclusion unsatisfiable.

That argument is prose, not machine-checked: pinning it down needs a `GeneratedPair` over an
exactly-exhausted finite `γ`, which is a page of construction for a defect the type class
removes outright. What *is* machine-checked is that nothing below needs more than `Infinite γ`,
and the consumer instantiates `γ := ℕ`. The rule that found this is the standing one: a
hypothesis must be a statement one believes, and `EarStep` without a supply of fresh names is
not one. -/

/-! ### Steps 2 and 3: the induction through the ear sequence -/

/-! ### `thm:finite-transfer`(a) -/

/-! ### Step 4, direction (a): the target crosscut

*In part (a), `F*` is a polygonal Jordan region in the square, by
`lem:cellulation-invariants`(vii). Every point of its boundary is polygonally accessible from its
interior. `lem:accessible-endpoints` therefore gives a polygonal crosscut `P* ⊆ closure F*` from
`v*` to `w*`.* Then: *`thm:general-crosscut` says that the crosscut splits the face into exactly
the two Jordan regions bounded by the crosscut together with those two paths.*

That whole paragraph is proved below. It is stated for a *target* face — a
member of a family of components of `Q ∖ |G|` for an ambient open region `Q` whose frontier
belongs to the skeleton — because that is the shape
`Graph.polygonal_side_accessibility_target` consumes, and it is the shape a target realization
of a generated structure has: `Q` is the open square, `|G|` the target skeleton, and the family
is the set of realized open 2-cells. -/

/-! ### Completing the ear step -/

/-! ### The ear's endpoints, transferred

*Let `F*, v*, w*` be the corresponding face and endpoints in the other realization.* Under the
representation of `Schoenflies/CombinatorialInvariance.lean` there is nothing to transport: `F`
and the two endpoint 0-cells are cells of the **one** abstract structure both realizations
realize, and assertion (ix) turns "the source endpoint lies on the boundary of the source face"
into the abstract statement `a ≼ F`, which reads back in the target realization. -/

/-! ### Step 1: the overlay

*By `lem:polygonal-overlay`, using the convention of `rem:polygonal-overlay-convention`, first
overlay the proposed polygonal nonboundary edges with the old polygonal nonboundary skeleton and
subdivide at all intersections.*

`Schoenflies.polygonal_overlay` does that for a **list of segments**. What step 1 has instead is
a finite family of polygonal *arcs* — the old nonboundary edges and the proposed new ones — so
the two have to be bridged. `Schoenflies.exists_overlay_of_biUnion_finite` is that bridge, and it
is the half of step 1 that is proved here: the union of finitely many nondegenerate polygonal
sets is the point set of a finite plane graph drawn by straight segments, whose vertices are the
ends of the subdivided pieces and therefore include every intersection point.

The nondegeneracy hypothesis is necessary, not cosmetic: a one-point set is polygonal
(`poly [a] = {a}`) and is not the point set of any overlay graph, whose vertices are the ends of
nondegenerate segments.

The matching-subdivision half of step 1 is completed in `CommonSubdivision.lean`: every source
subdivision point is transported through the chosen edge parametrization to the other
realization. -/

/-! ### The interface, exercised

`thm:finite-transfer` exists to feed the recursion of the quantitative-refinement section, which
consumes a transfer only through `Realization.Refines`. This anonymous example is a
machine-checked statement that the conclusion of `finite_transfer_toward_square` delivers exactly
what that recursion reads: the source carrier refines (`lem:refinement-compatibility`(a)), the
same parent map serves both sides (part (c)), and the closed target star of a fixed source point
shrinks (`T_{n+1}(x) \subseteq T_n(x)`).

Nothing below mentions how the transfer was built. If a later change to `IsTransferOf` stopped
serving that recursion, this would break. -/

end Schoenflies
end



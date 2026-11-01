-- Prove2me | Definitions.Def_Q146C009
-- name    : Q146C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:26:21.206049+00:00
-- url     : https://prove2.me/theorems/7724fe5f-7927-42a9-9417-41a6bdd9cca3
-- title:
--   Definitions bundle Q146C009 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 452 declarations of OpenAI's Lean: 54 definitions, 33 inductive types or structures, 6 instances and 359 theorems. The definitions and types are `Graph.traceGraph`, `Schoenflies.CellStructure.BoundaryCycles.boundaryPaths`, `Schoenflies.CellStructure.OuterEdgesFormCycle`, `Schoenflies.CommonSubdivision`, `Schoenflies.CommonSubdivisionData`, `Schoenflies.EarStep`, `Schoenflies.EarStepConstruction`, `Schoenflies.EarStepData`, `Schoenflies.EarStepData.pair`, `Schoenflies.FreshNet`, `Schoenflies.GeneratedPair.SourceEndpointFreshCombinatorics`, `Schoenflies.GeneratedPair.SubdivideAtData`, `Schoenflies.GeneratedPair.SubdivideSetData`, `Schoenflies.GeneratedPair.sourceNonboundaryGraph`, `Schoenflies.GeneratedPair.sourceNonboundaryVertices`, `Schoenflies.GeneratedPair.split`, `Schoenflies.GeneratedPair.subdivide`, `Schoenflies.InitialData.generatedPair`, `Schoenflies.IsPartialTransferOf`, `Schoenflies.IsPlaneSubdivisionExtension`, `Schoenflies.IsSourceExtension`, `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.IsTargetTransferOf`, `Schoenflies.IsTransferOf`, `Schoenflies.JoinedLocalGridSourceExtensionData`, `Schoenflies.LocalGridForwardStageData`, `Schoenflies.LocalGridSourceExtensionData`, `Schoenflies.NewTargetBoundaryAnchored`, `Schoenflies.NoNewNonouterIncidenceAtBoundary`, `Schoenflies.QuantitativeForwardStage`, `Schoenflies.QuantitativeForwardStage.pair`, `Schoenflies.QuantitativeReverseStage`, `Schoenflies.QuantitativeReverseStage.pair`, `Schoenflies.QuantitativeSchedule`, `Schoenflies.QuantitativeSchedule.centre`, `Schoenflies.QuantitativeSuccessor`, `Schoenflies.QuantitativeSuccessor.pair`, `Schoenflies.RefinedCrosscutOverlayData`, `Schoenflies.RefinedSourceFaceCrosscutData`, `Schoenflies.SourceCrosscutGeometry` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `ArcComplementPrep`, `BoundaryContinuity2`, `BoundaryCycles`, `BoundaryCyclesGenerated`, `CellulationInvariants`, `CombinatorialInvariance`, `CommonSubdivision`, `CrosscutAtMostTwo`, `Endgame`, `FiniteTransfer`, `FiniteTransferTarget`, `FiniteTransferTargetMesh`, `FreshDenseSelection`, `GeneralCrosscut`, `GeneratedStructure`, `Graph_Ear`, `Graph_Relabel`, `GridAttach`, `InitialGenerated`, `InitialPair`, `InitialPairFixed`, `LocalGrid`, `MatchedArc`, `OverlayExtension`, `QuantitativeForwardStages`, `QuantitativeRecursion`, `QuantitativeStages`, `RealizeSplit`, `SourceAttachment`, `SourceJoining`, `SourceOverlay`, `SquareMesh`, `SquareMeshConnected`, `StageTower`, `StageTransition`, `TargetOverlay`.
--
--   **Imports.** It imports the bundles `Q146C006` and `Q146C007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q146C011`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_Q146C006
import Definitions.Def_Q146C007

section
-- module Solutions.Q146_CD.ArcComplementPrep
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-- **The inside of a square boundary is the open square.** -/
theorem inside_frontier_closedSquare (c : Plane) (r : ℝ) :
    inside (frontier (closedSquare c r)) = openSquare c r := by
  have hcompl := Plane.compl_frontier_closedSquare c r
  -- Both pieces of the complement are whole components, by `lem:recognizing-a-component`.
  have hcomp₁ : ∀ x ∈ openSquare c r,
      connectedComponentIn (frontier (closedSquare c r))ᶜ x = openSquare c r := by
    intro x hx
    refine Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare c r)
      (Plane.convex_openSquare c r).isPreconnected ?_ ?_ hx
    · rw [hcompl]; exact subset_union_left
    · rw [eq_empty_iff_forall_notMem]
      exact fun z hz => hz.2 (Plane.frontier_openSquare_subset c r hz.1)
  have hcomp₂ : ∀ x ∈ (closedSquare c r)ᶜ,
      connectedComponentIn (frontier (closedSquare c r))ᶜ x = (closedSquare c r)ᶜ := by
    intro x hx
    refine Plane.connectedComponentIn_eq_of_frontier_disjoint
      (Plane.isClosed_closedSquare c r).isOpen_compl
      (Plane.isConnected_compl_closedSquare c r).isPreconnected ?_ ?_ hx
    · rw [hcompl]; exact subset_union_right
    · rw [eq_empty_iff_forall_notMem]
      intro z hz
      rw [frontier_compl] at hz
      exact hz.2 hz.1
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    have hx : x ∈ openSquare c r ∪ (closedSquare c r)ᶜ := by
      rw [← hcompl]; exact hx
    rcases hx with hx | hx
    · exact hx
    · rw [hcomp₂ x hx] at hb
      exact absurd hb (Plane.not_isBounded_compl_closedSquare c r)
  · intro hx
    have hxc : x ∈ (frontier (closedSquare c r))ᶜ := by rw [hcompl]; exact Or.inl hx
    refine ⟨hxc, ?_⟩
    rw [hcomp₁ x hx]
    exact (Plane.isBounded_closedSquare c r).subset (Plane.openSquare_subset_closedSquare' c r)


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

/-! ### A vertical side crosses a horizontal side in one point -/

/-! ### From a meeting point to a vertex of the overlay

`Graph.IsTwoConnected.union` needs two common **vertices**, not two common points.  The
overlay's cut-point condition `MeetsAreCut` says that both ends of the meet of two source
pieces are cut points; when the meet is a *singleton* both ends are that one point, so the
crossing point is a cut point, and `overlayGraph_mem_vertexSet_of_mem_cover` promotes a cut
point on the union to a vertex.  This is the whole bridge, and it is why `exists_two_meets` is
stated with singleton meets rather than with mere common points. -/

/-! ### Localizing a cut point to one source piece

`overlayGraph_mem_vertexSet_of_mem_cover` says a cut point on the union is a vertex, but it
says nothing about *which* edge it is an end of.  The next wave has to place the two common
points of two neighbouring squares in the vertex sets of the two graphs being unioned, and for
that the edge must be pinned inside the boundary it came from.  The three lemmas below do that;
the first two are general facts about `subdivide` whose home is `Schoenflies/Subdivide.lean`. -/

/-! ## Part 3: the uniform-continuity partition

The blueprint asks for "a partition `0 = t₀ < t₁ < ⋯ < t_k = 1`, with `k ≥ 3`, such that every
point of `α([t_{i-1}, t_i])` is at distance less than `ε` from `α(t_{i-1})`", and separately for
a refinement of it inside each piece.  Both are served by the **even** partition: nothing in
the proof uses anything about the partition beyond the mesh bound, and taking `t_i = i/n`
makes "the fine partition refines the coarse one" the arithmetic identity `sample (k*m) (i*m)
= sample k i` rather than a bookkeeping argument.  The number of pieces can be forced to be a
multiple of any prescribed `k` and hence as large as one likes, which covers the `k ≥ 3`
clause. -/

/-! ## Part 4: nonadjacent subarcs are at positive distance -/

/-! ## Part 5: the covering clause -/

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
-- module Solutions.Q146_CD.CrosscutAtMostTwo
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PolyArc.coordAcross_off _root_.Schoenflies.PolyArc.coordAlong_off _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-! ### The clopen step -/

/-! ### Lemma "At most two sides" -/

/-! ### The collar hypothesis is not vacuous: a straight crosscut

The collar of a *straight* crosscut is a rectangle, and the free-standing frame toolkit of
`Schoenflies/Strip.lean` — `coordAlong`, `coordAcross`, `strip`, `isOpen_strip`, `convex_strip`,
`dist_foot`, `frame_decomp` — builds it directly, with no cyclic vertex family in sight. So
`HasArcCollars` is discharged outright in the simplest crosscut configuration, and
`segment_crosscut_at_most_two` below is a hypothesis-free instance of the lemma.

This is the shape a general discharger has to reproduce along a chain of edges: it is exactly
the blueprint's edge block, and what is missing is the vertex disks between consecutive blocks
and the end cross-sections. -/

open Plane in
/-- **A straight crosscut has two-sided collars.** For a nondegenerate segment whose endpoints
lie outside the region and whose remaining points lie inside, blueprint Lemma 1.8 (b) is a
rectangle: an open block around the subarc, of half-width small enough to stay inside the
region, split by the line of the segment into two convex halves.

This discharges `HasArcCollars` in the one case the existing strip apparatus reaches without an
arc collar being built, and so certifies that the hypothesis of `crosscut_at_most_two` is
satisfiable. -/
theorem hasArcCollars_segment {a b : Plane} (hab : a ≠ b) (hDopen : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : segment ℝ a b \ {a, b} ⊆ D) :
    HasArcCollars D (segment ℝ a b) := by
  obtain ⟨u, L, hL, hu, hLu⟩ := exists_direction_length hab
  -- Reading the two coordinates off a frame position, and off the two endpoints.
  have hAlong : ∀ c s : ℝ, coordAlong a u (a + c • u + s • perp u) = c :=
    fun c s => coordAlong_param hu a c s
  have hAcross : ∀ c s : ℝ, coordAcross a u (a + c • u + s • perp u) = s :=
    fun c s => coordAcross_param hu a c s
  have hzero : ∀ c : ℝ, a + c • u = a + c • u + (0 : ℝ) • perp u := fun c => by module
  have hfoot : ∀ c : ℝ, coordAlong a u (a + c • u) = c := fun c => by
    rw [hzero c]; exact hAlong c 0
  have hfoot' : ∀ c : ℝ, coordAcross a u (a + c • u) = 0 := fun c => by
    rw [hzero c]; exact hAcross c 0
  have hAa : coordAlong a u a = 0 := by simp [coordAlong]
  have hAb : coordAlong a u b = L := by
    rw [coordAlong, ← hLu, real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hu.norm]
    ring
  -- A point of the line strictly between the two endpoints is inside the region.
  have hline : ∀ c : ℝ, 0 < c → c < L → a + c • u ∈ D ∩ segment ℝ a b := by
    intro c hc0 hcL
    have hmem : a + c • u ∈ segment ℝ a b :=
      (mem_segment_iff_coord hL hu hLu).2 ⟨hfoot' c, by rw [hfoot c]; exact ⟨hc0.le, hcL.le⟩⟩
    refine ⟨hPD ⟨hmem, ?_⟩, hmem⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro (h | h)
    · have hcc := hfoot c
      rw [h, hAa] at hcc
      exact absurd hcc.symm (ne_of_gt hc0)
    · have hcc := hfoot c
      rw [h, hAb] at hcc
      exact absurd hcc.symm (ne_of_lt hcL)
  intro K hKsub hKcompact _ hKnontriv
  -- The progress of a point of `K` is strictly between `0` and `L`: at the two extremes the
  -- point would be an endpoint of the segment, and the endpoints are outside `D`.
  have hKcoord : ∀ x ∈ K, coordAcross a u x = 0 ∧ 0 < coordAlong a u x ∧ coordAlong a u x < L := by
    intro x hx
    obtain ⟨h0, hc⟩ := (mem_segment_iff_coord hL hu hLu).1 (hKsub hx).2
    refine ⟨h0, lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩
    · intro hz
      have hxa : x = a := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rwa [← hz, zero_smul, add_zero] at h
      exact ha (hxa ▸ (hKsub hx).1)
    · intro hz
      have hxb : x = b := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rw [hz, hLu, show a + (b - a) = b from by module] at h
        exact h
      exact hb (hxb ▸ (hKsub hx).1)
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcompact.exists_isMinOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  obtain ⟨q, hqK, hqmax⟩ :=
    hKcompact.exists_isMaxOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  have hc₁pos : 0 < coordAlong a u p := (hKcoord p hpK).2.1
  have hc₂lt : coordAlong a u q < L := (hKcoord q hqK).2.2
  have hc₁c₂ : coordAlong a u p ≤ coordAlong a u q := isMinOn_iff.1 hpmin q hqK
  set t₁ := coordAlong a u p / 2 with ht₁
  set t₂ := (coordAlong a u q + L) / 2 with ht₂
  have ht₁pos : 0 < t₁ := by rw [ht₁]; linarith
  have ht₁c₁ : t₁ < coordAlong a u p := by rw [ht₁]; linarith
  have hc₂t₂ : coordAlong a u q < t₂ := by rw [ht₂]; linarith
  have ht₂L : t₂ < L := by rw [ht₂]; linarith
  have ht₁t₂ : t₁ < t₂ := by linarith
  -- The core of the block: the closed piece of the line over `[t₁, t₂]`, compact and inside `D`.
  have hScompact : IsCompact ((fun c : ℝ => a + c • u) '' Icc t₁ t₂) :=
    isCompact_Icc.image (by fun_prop)
  have hSsub : (fun c : ℝ => a + c • u) '' Icc t₁ t₂ ⊆ D := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hline c (lt_of_lt_of_le ht₁pos hc.1) (lt_of_le_of_lt hc.2 ht₂L)).1
  obtain ⟨ρ, hρ, hρD⟩ := Plane.exists_thickening_subset hScompact hDopen hSsub
  -- Both halves reach every point of `K`, by offsetting it perpendicularly.
  have hclose : ∀ x ∈ K, ∀ d : ℝ,
      dist x (a + (coordAlong a u x) • u + d • perp u) = |d| := by
    intro x hx d
    nth_rewrite 1 [eq_foot_of_coordAcross_eq_zero hu (hKcoord x hx).1]
    rw [dist_eq_norm,
      show a + (coordAlong a u x) • u -
        (a + (coordAlong a u x) • u + d • perp u) = (-d) • perp u from by module,
      norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one, abs_neg]
  have hKt : ∀ x ∈ K, t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ := fun x hx =>
    ⟨lt_of_lt_of_le ht₁c₁ (isMinOn_iff.1 hpmin x hx),
      lt_of_le_of_lt (isMaxOn_iff.1 hqmax x hx) hc₂t₂⟩
  refine ⟨{ nbhd := strip a u t₁ t₂ (-ρ) ρ
            left := strip a u t₁ t₂ 0 ρ
            right := strip a u t₁ t₂ (-ρ) 0
            isOpen_nbhd := isOpen_strip a u t₁ t₂ (-ρ) ρ
            subset_nbhd := ?_
            nbhd_subset := ?_
            nbhd_diff := ?_
            isConnected_left := ?_
            isConnected_right := ?_
            subset_closure_left := ?_
            subset_closure_right := ?_ }⟩
  · -- `K` is inside the block: its progress is between the two bounds and its offset is zero.
    intro x hx
    exact ⟨(hKt x hx).1, (hKt x hx).2, by rw [(hKcoord x hx).1]; linarith,
      by rw [(hKcoord x hx).1]; exact hρ⟩
  · -- The block is inside `D`: every point is within `ρ` of the foot of its perpendicular.
    intro x hx
    refine hρD (mem_thickening_iff.2 ⟨a + (coordAlong a u x) • u, ⟨_, ⟨hx.1.le, hx.2.1.le⟩, rfl⟩,
      ?_⟩)
    rw [dist_foot hu, abs_lt]
    exact ⟨hx.2.2.1, hx.2.2.2⟩
  · -- Off the segment, the block is the two open halves: a point of the block at signed distance
    -- zero is on the segment, because its progress lies inside `[0, L]`.
    ext x
    simp only [mem_sdiff, mem_union, mem_strip_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      rcases lt_trichotomy (coordAcross a u x) 0 with h | h | h
      · exact Or.inr ⟨h1, h2, h3, h⟩
      · exact absurd ((mem_segment_iff_coord hL hu hLu).2
          ⟨h, by linarith [ht₁pos], by linarith [ht₂L]⟩) h5
      · exact Or.inl ⟨h1, h2, h, h4⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨⟨h1, h2, by linarith, h4⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
      · refine ⟨⟨h1, h2, h3, by linarith⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
  · exact (convex_strip a u t₁ t₂ 0 ρ).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (ρ / 2) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · exact (convex_strip a u t₁ t₂ (-ρ) 0).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (-(ρ / 2)) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (min (ρ / 2) (ε / 2)) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2, hσ,
        lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩, ?_⟩
    rw [hclose x hx _, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (-(min (ρ / 2) (ε / 2))) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2,
        by have := min_le_left (ρ / 2) (ε / 2); linarith, neg_neg_iff_pos.2 hσ⟩, ?_⟩
    rw [hclose x hx _, abs_neg, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneralCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-- Two distinct points of a Jordan curve cut it into a pair of arcs. This is
`IsJordanCurve.two_arcs`, repackaged. -/
theorem exists_isCutPair (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A₁ A₂, IsCutPair C p q A₁ A₂ := by
  obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hC.two_arcs hp hq hpq
  exact ⟨A, B, hA, hB, hcov, hmeet⟩

/-! ### Elementary consequences of the configuration

Nothing here needs `thm:jordan`: these are the set-theoretic facts that turn "the crosscut runs
inside the curve" into the hypotheses `Schoenflies.crosscut_cells` takes. -/

/-! ### The three regions of `ℝ² ∖ (C ∪ P)`

The blueprint's final paragraph. `P` misses `Ext(C)`, so the complement of `C ∪ P` splits as
`Ext(C) ⊔ (Int(C) ∖ P)`; the first half has just split the second summand in two; and each of
the three pieces is a component of the whole because its boundary misses it
(`lem:clopen-component`, here `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`). -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-! ### The skeleton homeomorphism -/

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

/-- **The open nonboundary part corresponds** — the geometric half of part (b) of
lem:combinatorial-invariance. The skeleton homeomorphism carries the outer cycle onto the
outer cycle, hence restricts to a bijection of the two open nonboundary parts. -/
theorem image_nonboundary : g.toFun '' R₁.nonboundary = R₂.nonboundary := by
  have : g.toFun '' (R₁.skeletonSet \ R₁.outerSet) = R₂.skeletonSet \ R₂.outerSet := by
    rw [g.injOn.image_sdiff_subset R₁.outerSet_subset_skeletonSet, g.image_skeletonSet,
      g.image_outerSet]
  exact this

/-- **Connectedness of the open nonboundary part is invariant** — part (b) of
lem:combinatorial-invariance. This is the one clause with genuine topological content: it is
what makes admissibility (def:admissible-graph) transfer between the two realizations. -/
theorem isConnected_nonboundary_iff (g : SkeletonHomeo R₁ R₂) :
    IsConnected R₁.nonboundary ↔ IsConnected R₂.nonboundary := by
  constructor
  · intro h
    rw [← g.image_nonboundary]
    exact h.image _ (g.continuousOn_toFun.mono Set.sdiff_subset)
  · intro h
    rw [← g.symm.image_nonboundary]
    exact h.image _ (g.symm.continuousOn_toFun.mono Set.sdiff_subset)

end SkeletonHomeo

/-! ### Combinatorial invariance -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Ear
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Graph.chainUnion_succ _root_.Graph.mem_vertexSet_induce_component _root_.Graph.pointSet_union _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-! ### Attaching an ear -/

/-! ### Replacing an edge by a path -/

/-- **`lem:subdivision-ear-preserve` (a): a subdivision of a 2-connected graph is
2-connected.** Stated for a replacement *path* rather than for a single new vertex, because
nothing in the argument cares how long the replacement is; subdividing one edge by one vertex
is the case where `P` has two edges.

Delete a vertex `c`. One end of the replaced edge survives and is the hub. Everything on the
old side reaches it by `Graph.Reaches.across_edge_replacement`, whose `routed` premise is
discharged by the three-way case analysis: if `c` is an end of the replaced edge there is
nothing to route; if `c` is an old vertex then it is not on the path — this is where the
freshness hypothesis `hnew` is used — and the path itself joins the ends; and if `c` is new
then the old graph is untouched and has no bridge. Everything on the path side reaches an end
of the path, and an end reached after the deletion survived it. -/
theorem IsTwoConnected.replace_edge_by_path (hG : G.IsTwoConnected) (hl : G.IsLink e u v)
    (huv : u ≠ v) (hcompat : (G.deleteEdges {e}).Compatible P) (hP : P.IsPathGraph u W v)
    (hnew : ∀ x ∈ V(P), x ≠ u → x ≠ v → x ∉ V(G)) :
    ((G.deleteEdges {e}).union P).IsTwoConnected := by
  set T := G.deleteEdges {e} with hT
  set S := T.union P with hS
  have hTS : T ≤ S := left_le_union T P
  have hPS : P ≤ S := hcompat.right_le_union
  have hVT : V(T) = V(G) := by rw [hT]; simp
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  -- Every old edge but the replaced one links the same pair in the new graph.
  have hGS : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → S.IsLink g p q := by
    intro g p q hg hge
    refine hTS.isLink_mono (show T.IsLink g p q from ?_)
    rw [hT]
    exact ⟨hg, by simpa using hge⟩
  have hVGS : V(G) ⊆ V(S) := by
    rw [hS, vertexSet_union, hVT]
    exact Set.subset_union_left
  -- The replacement route.
  have hPuv : P.Reaches u v := hP.connected.reaches hP.source_mem hP.target_mem
  refine ⟨hG.hasThreeVertices.mono hVGS, ?_, ?_⟩
  · refine Connected.of_hub (hVGS hu) fun x hx ↦ ?_
    rcases (hx : x ∈ V(T) ∪ V(P)) with hxT | hxP
    · refine Reaches.reroute (e := e) hVGS hGS ?_
        (hG.connected.reaches hu (by rwa [hVT] at hxT))
      intro p q hpq
      rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hPuv.mono hPS, (hPuv.mono hPS).symm]
    · exact (hP.connected.reaches hP.source_mem hxP).mono hPS
  intro c _
  -- One end of the replaced edge survives; it is the hub.
  obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
    by_cases hcu : u = c
    · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
    · exact ⟨u, hu, hcu⟩
  have hTle : T.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hTS _
  have hPle : P.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hPS _
  have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
  -- The replaced edge's ends are still joined, unless the deleted vertex is one of them.
  have routed : (S.deleteVerts {c}).Reaches u v ∨ G.Inc e c := by
    by_cases hcu : c = u
    · exact Or.inr (hcu ▸ hl.inc_left)
    by_cases hcv : c = v
    · exact Or.inr (hcv ▸ hl.inc_right)
    by_cases hcG : c ∈ V(G)
    · -- An old vertex and not an end: the path is untouched, and it joins the ends.
      have hcP : c ∉ V(P) := fun hh ↦ hnew c hh hcu hcv hcG
      have hreach : (P.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcP]; exact hPuv
      exact Or.inl (hreach.mono hPle)
    · -- A new vertex: the old graph is untouched, and it has no bridge.
      have hcT : c ∉ V(T) := by rw [hVT]; exact hcG
      have hreach : (T.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcT, hT]
        exact hG.no_bridge hl
      exact Or.inl (hreach.mono hTle)
  -- Every surviving old vertex reaches the hub.
  have key : ∀ x ∈ V(G), x ≠ c → (S.deleteVerts {c}).Reaches x z := by
    intro x hx hxc
    refine Reaches.across_edge_replacement (e := e) ?_ hl ?_ routed
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hx hxc)
        (mem_deleteVerts_singleton_of_ne hzG hzc))
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hVGS
    · intro g p q hg hge
      rw [deleteVerts_isLink] at hg ⊢
      exact ⟨hGS hg.1 hge, hg.2.1, hg.2.2⟩
  refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGS hzG) hzc) fun x hx ↦ ?_
  rw [vertexSet_deleteVerts] at hx
  obtain ⟨hxS, hxc⟩ := hx
  have hxc' : x ≠ c := by simpa using hxc
  rcases (hxS : x ∈ V(T) ∪ V(P)) with hxT | hxP
  · exact (key x (by rwa [hVT] at hxT) hxc').symm
  · rcases hP.reaches_an_end hxP hxc' with hr | hr
    · have hune : u ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key u hu hune).symm.trans (hr.mono hPle).symm
    · have hvne : v ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key v hv hvne).symm.trans (hr.mono hPle).symm

/-! ### Finding an ear -/

end Graph
end

section
-- module Solutions.Q146_CD.Endgame
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The endgame: from the square extension to the relative Jordan–Schönflies theorem

This module carries the whole tail of the manuscript — `prop:square-reduction`,
`thm:closed-interior-extension`, `prop:pointed-extension`, `prop:exterior-extension` and
`thm:main` — parametrically over the square-extension interface.

Every theorem below takes `Schoenflies.SquareExtension` as an explicit hypothesis and assumes
nothing else. In particular the standing hypothesis `harc` that older modules thread is
discharged here at the call site, from `Schoenflies.arc_complement` in
`Schoenflies/JordanClosed.lean`; it no longer appears in any signature. The implication proved
by this module is

    SquareExtension  ⟹  thm:main.

`Schoenflies/JordanSchoenflies.lean` supplies `SquareExtension` from the quantitative
boundary construction and therefore closes this implication without an extra hypothesis.

## What `SquareExtension` says

`Schoenflies.SquareExtension` is `thm:square-extension` written in the `Schoenflies.IsHomeoOn`
style of `Schoenflies/Inversion.lean`: for every Jordan curve `C` and every restricted
homeomorphism `u : C → S` (with named inverse `v`) there are maps `F`, `G` restricting to
mutually inverse homeomorphisms between `C ∪ Int(C)` and `Q`, with `F = u` on `C`. Here
`S = Schoenflies.modelCurve` and `Q = Schoenflies.Plane.closedSquare 0 1`; `S = ∂Q` is
`Schoenflies.modelCurve_eq_frontier`, so this is literally the blueprint's `Q = [-1,1]²`,
`S = ∂Q`.

## The chain

* `prop:square-reduction` is the blueprint's: pick a homeomorphism `h : C' → S`
  (`lem:jordan-circle`), extend `h ∘ f` and `h` to the square, and compose one with the inverse
  of the other. `thm:closed-interior-extension` is the same statement — under the standing
  assumption of `SquareExtension` the reduction *is* the theorem — and is recorded separately
  because everything downstream cites it by that name.
* `prop:pointed-extension` is the interesting one. Given the closed-interior extension `Φ` and
  a square chart `Θ` of the *target* disc, the two points `Θ(Φ(a))` and `Θ(b)` are interior to
  `Q`, because `Θ` carries `C'` onto `∂Q` and hence — being a bijection — `Int(C')` onto
  `Q ∖ ∂Q`. `lem:square-point-mover` then supplies a boundary-fixing self-homeomorphism `M` of
  `Q` moving the first to the second, and `Θ⁻¹ ∘ M ∘ Θ ∘ Φ` is the pointed extension: it agrees
  with `Φ` on `C` because `M` fixes `∂Q` pointwise. This discharges
  `Schoenflies.PointedInteriorExtension`, the last hypothesis of `prop:exterior-extension`.
* `thm:main` is the closed pasting lemma applied twice, once to `F` and once to its inverse.
  The one point the blueprint leaves implicit is that the pasted map is *injective*: the
  interior extension carries `Int(C)` onto `Int(C')` and the exterior extension carries
  `Ext(C)` onto `Ext(C')`, so the two pieces cannot collide. Both facts are instances of
  `Schoenflies.image_eq_diff_of_bijOn_union`, which is the "a bijection matching one part of a
  partition matches the other part" principle.

## The parametric construction interface

Within this deliberately parametric module, every conclusion depends on the *Prop*
`SquareExtension`, so no `def` can produce the maps without an application of choice to that
hypothesis. What is exported as data independently of the interface is
`Schoenflies.paste` (the pasted map itself, with its two evaluation lemmas) and
`Schoenflies.IsHomeoOn.homeomorphOfUniv` (the passage from a global `IsHomeoOn` to a genuine
`Plane ≃ₜ Plane`). The theorems below return the maps in the unbundled `∃ F G, IsHomeoOn F G …`
shape of `Schoenflies.exterior_extension`, which composes.

## Blueprint

* `Schoenflies.SquareExtension` — the **`thm:square-extension`** interface, discharged in
  `Schoenflies/JordanSchoenflies.lean`.
* `Schoenflies.square_reduction` — `prop:square-reduction`.
* `Schoenflies.closed_interior_extension` — **`thm:closed-interior-extension`**.
* `Schoenflies.pointed_extension` — `prop:pointed-extension`; it proves
  `Schoenflies.PointedInteriorExtension` of `Schoenflies/Inversion.lean`.
* `Schoenflies.exterior_extension_of_squareExtension` — `prop:exterior-extension`, restated
  with `harc` discharged and only `SquareExtension` left.
* `Schoenflies.jordan_schoenflies_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_homeomorph_of_squareExtension`,
  `Schoenflies.jordan_schoenflies_of_homeomorph_of_squareExtension` — **`thm:main`**, the relative
  Jordan–Schönflies theorem, in the unbundled, the bundled, and the blueprint's own shape.

Supporting material with no blueprint statement, all general and all candidates for hoisting
into the module that owns `Schoenflies.IsHomeoOn`:
`Schoenflies.exists_isHomeoOn_of_homeomorph`, `Schoenflies.IsHomeoOn.homeomorphOfUniv`,
`Schoenflies.IsHomeoOn.image_inv_eq`, `Schoenflies.image_eq_diff_of_bijOn_union`,
`Schoenflies.paste` and `Schoenflies.Plane.IsSquareMover.isHomeoOn`.
-/

open Bornology Metric Set

namespace Schoenflies

/-! ### Restricted homeomorphisms: three general tools

`Schoenflies.IsHomeoOn` (in `Schoenflies/Inversion.lean`) is the unbundled "restricts to a
homeomorphism of `S` onto `T`". Three facts about it are needed below and are not there; they
are general, and the section comment at `IsHomeoOn` already asks for the whole notion to be
hoisted, so these should travel with it. -/

/-! ### The pasted map

`thm:main` glues the interior and the exterior extension. The glued map is `Set.piecewise`
under a different name, spelled so that the two evaluation lemmas below are the only interface
the proof needs. -/

/-! ### The square `Q` and its boundary `S`

The blueprint's `Q = [-1,1]²` is `Plane.closedSquare 0 1` and its boundary `S = ∂Q` is
`modelCurve`, by `modelCurve_eq_frontier`. One consequence is needed: removing the boundary
from the closed square leaves the open square, which is where `lem:square-point-mover` wants
its two points. -/

/-- `Q ∖ S = Q°`. -/
theorem closedSquare_sdiff_modelCurve :
    Plane.closedSquare 0 1 \ modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier, Plane.frontier_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 h2
  · intro h
    have h' : Plane.supDist z 0 < 1 := h
    exact ⟨h'.le, ne_of_lt h'⟩

/-! ### `thm:square-extension`, assumed

This is the one statement the module assumes, and the only thing standing between the library
and `thm:main`. It is the last big theorem of the manuscript; its proof occupies the whole of
Part II §§"Strongly accessible boundary points"–"Continuity at the Jordan curve". -/

/-! ### Disjointness of a curve from its two regions

A curve is disjoint from either of its two regions, and adding it and removing it again is the
identity. The pastings below use these constantly. -/

/-! ### `prop:square-reduction` and `thm:closed-interior-extension`

The blueprint's proof verbatim: choose `h : C' → S` by `lem:jordan-circle`, extend `h ∘ f` and
`h` over the two closed discs by `thm:square-extension`, and take `Ψ⁻¹ ∘ Φ`. -/

/-! ### `prop:pointed-extension`

The blueprint's proof, with one step made explicit: the square chart `Θ` of the *target* disc
carries `Int(C')` onto `Q ∖ ∂Q = Q°`, because it carries `C'` onto `∂Q` and is a bijection of
the closed disc onto `Q`. That is what puts the two points `Θ(Φ(a))` and `Θ(b)` in the open
square, where `lem:square-point-mover` lives. -/

/-! ### `prop:exterior-extension`, from the square extension

`Schoenflies.exterior_extension` in `Schoenflies/Inversion.lean` is proved already; it carries
two hypotheses, the standing `harc` of `thm:jordan` and `PointedInteriorExtension`. Part I
discharges the first (`Schoenflies.arc_complement`) and the previous theorem discharges the
second, so only `SquareExtension` survives. -/

/-! ### `thm:main`

The closed pasting lemma, twice. The blueprint's proof is three sentences; the two facts it
leaves implicit are that the closed interior and the closed exterior are *closed* (they are the
closures of the two regions, `IsRegionOf.closure_eq`) and that the pasted map is injective,
which is `image_inside_eq` and `image_outside_eq`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryContinuity2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Continuity at the Jordan curve, and `thm:square-extension`

The last three statements of the manuscript: `lem:crosscut-side-correspondence`,
`prop:boundary-continuity`, and the assembly of `thm:square-extension` from them.

`Schoenflies/BoundaryContinuity.lean` proves the statement with the real combinatorial content,
`lem:skeleton-crosscuts` (`Graph.IsStageOn.exists_crosscut`), for one finite
plane graph. This module takes the crosscuts as given and finishes the section.

## The construction inputs

This module isolates the construction-dependent data as explicit hypotheses. They are supplied
for the quantitative stage recursion in `Schoenflies/InteriorHomeomorphism.lean` and
`Schoenflies/BoundaryAnchors.lean`. Nothing else is assumed: `thm:jordan` and
`thm:general-crosscut` are used through `Schoenflies/JordanClosed.lean`, where their hypotheses
are supplied.

* **`prop:interior-homeomorphism`** enters as `IsHomeoOn F F' (inside C) (Plane.openSquare 0 1)`
  — the `Schoenflies.IsHomeoOn` shape of `Schoenflies/Inversion.lean`: a map, a named inverse,
  and the continuity and inverse laws on the two sets.
* **`lem:skeleton-crosscuts` + `prop:skeleton-agreement`** enter as
  `Schoenflies.HasAnchorCrosscuts`: for two distinct anchors `a, b` a crosscut `P` of `C` from
  `a` to `b`, a crosscut `P'` of `Q°` from `u a` to `u b`, and the agreement
  `F '' (P ∖ {a,b}) = P' ∖ {u a, u b}`. This is exactly what the finite skeleton homeomorphism
  produces once `Graph.IsStageOn.exists_crosscut` has been run in the stage containing `a`
  and `b` (see `Graph.IsStageOn.exists_isCrosscut` below, which does the packaging).
* **`lem:anchor-density`** enters as the two clauses `𝒜 ⊆ C` and `C ⊆ closure 𝒜`, plus its
  "incident with a nonboundary edge" clause in the germ form `Schoenflies.HasSpokes`: at an
  anchor `c`, arbitrarily small connected pieces `J` of the Jordan domain which cling to `c`
  and whose `F`-images cling to `u c`. That is the initial subarc of the spoke at `c`, and its
  image, which is the initial subarc of the target spoke — the *only* use the blueprint makes
  of the spokes, in the paragraph of `lem:crosscut-side-correspondence` beginning "Choose
  `c ∈ 𝒜` in the relative interior of `Aᵢ`".

`Schoenflies.HasLimitHomeomorphism` bundles the four over all curves, and
`Schoenflies.squareExtension_of_hasLimitHomeomorphism` derives
`Schoenflies.SquareExtension` — the exact `def` of
`Schoenflies/Endgame.lean` — from it. The proof of `HasLimitHomeomorphism` assembled in
`Schoenflies/JordanSchoenflies.lean` closes the full theorem.

## The two arguments

*Which side maps to which side* is `Schoenflies.crosscut_side_correspondence`. The homeomorphism
of the interiors carries `Int(C) ∖ P` onto `Q° ∖ P'` (`Schoenflies.image_inside_sdiff`), hence
carries each of the two components onto one of the two; the labels are pinned by a spoke germ
`J` at an anchor `c` in the relative interior of `A₁`. `J` is connected, misses `P` because it
is small and `c ∉ P`, so it lies in one side; `c ∈ closure J` and `closure(Uᵢ) ∩ C = Aᵢ` force
that side to be `U₁`. The same two facts on the target, applied to `F '' J`, force `F '' U₁` to
be `U'₁`.

*Boundary continuity* is `Schoenflies.tendsto_nhdsWithin_inside`. The blueprint argues on a
subsequence; the filter form of the same argument avoids extracting one. If `F` does not tend
to `u p` along `𝓝[Int C] p`, then `l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` is a nonzero filter for some
open `W ∋ u p`, and compactness of `Q` gives a cluster point `q ∈ Wᶜ` of `F` along `l'`. If
`q ∈ Q°` then pushing `l'` through `F'` shows `p = F' q ∈ Int(C)`, impossible. Otherwise
`q ∈ S`; anchors `a, b` separating `p` from `r = u⁻¹ q` give a crosscut whose `p`-side contains
every point of `Int(C)` near `p`, so `l'` sits on that side, so `q` lies in the closure of the
corresponding target side, whose trace on `S` is `u(A₁)` — and `r ∉ A₁`.

## Blueprint

* `Graph.IsStageOn.exists_isCrosscut` — **`lem:skeleton-crosscuts`** repackaged as
  `Schoenflies.IsCrosscut`, the form `thm:general-crosscut` consumes.
* `Schoenflies.IsCutPair.separates`, `Schoenflies.exists_separating_anchors` — the selection
  step of `prop:boundary-continuity`: two anchors putting two prescribed points of the curve on
  opposite arcs. Uses **`lem:anchor-density`** through the density hypothesis alone.
* `Schoenflies.IsCrosscut.image_of_injOn`, `Schoenflies.image_sdiff_eq_of_eqOn` — the two
  steps a consumer performs to discharge `Schoenflies.HasAnchorCrosscuts` from a finite skeleton
  homeomorphism. No blueprint statement of their own; they are the second paragraph of the
  proof of **`lem:skeleton-crosscuts`**, "the finite skeleton homeomorphism sends `P` to a
  simple path `P'`".
* `Schoenflies.crosscut_side_correspondence` — **`lem:crosscut-side-correspondence`**.
* `Schoenflies.extendByBoundary`, `Schoenflies.tendsto_nhdsWithin_inside`,
  `Schoenflies.boundary_continuity` — **`prop:boundary-continuity`**.
* `Schoenflies.isHomeoOn_extendByBoundary`,
  `Schoenflies.squareExtension_of_hasLimitHomeomorphism` —
  **`thm:square-extension`**.
-/

open Bornology Filter Metric Schoenflies Set Topology
open scoped _root_.Graph

namespace Schoenflies

variable {C 𝒜 A₁ A₂ B₁ B₂ P P' : Set Plane} {u v F F' : Plane → Plane} {a b p r : Plane}

/-! ### Two elementary facts about the model square

`Q° = Int(S)`: the open square is the Jordan domain of the model curve. This is the bridge
between the shape `prop:interior-homeomorphism` is stated in (a homeomorphism onto
`Plane.openSquare 0 1`) and the shape `thm:general-crosscut` speaks in (`inside modelCurve`). -/

/-- The Jordan domain of the model curve is the open square. -/
theorem inside_modelCurve : inside modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier]
  exact inside_frontier_closedSquare 0 1

/-! ### Pushing arcs forward

`lem:crosscut-side-correspondence` labels the target sides by `u(A₁)` and `u(A₂)`, so the two
target arcs have to be produced as images. Nothing here is specific to the square. -/

/-! ### Anchors that separate

The selection step of `prop:boundary-continuity`. Given two distinct points `p, r` of the curve
and a dense set `𝒜` of anchors, we need anchors `a, b` with `p` and `r` on opposite arcs of `C`
from `a` to `b`. Density produces one anchor on each of the two open arcs of `C` from `p` to
`r`; the separation is then automatic, because an arc from `a` to `b` avoiding `p` and `r`
would be a connected subset of `C ∖ {p, r}` meeting both of its two (relatively open) halves. -/

/-- **The selection step of `prop:boundary-continuity`.** Two distinct points of the curve are
separated by two anchors of any dense set of anchors. -/
theorem exists_separating_anchors (hC : IsJordanCurve C) (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hp : p ∈ C) (hr : r ∈ C) (hpr : p ≠ r) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ A₁ A₂ : Set Plane, a ≠ b ∧ IsCutPair C a b A₁ A₂ ∧
      p ∈ A₁ ∧ p ∉ A₂ ∧ r ∈ A₂ ∧ r ∉ A₁ := by
  obtain ⟨B₁, B₂, hB⟩ := exists_isCutPair hC hp hr hpr
  obtain ⟨a, ha𝒜, haB, haB'⟩ := exists_anchor_mem_arc hsub hdense hB
  obtain ⟨b, hb𝒜, hbB, hbB'⟩ := exists_anchor_mem_arc hsub hdense hB.symm
  have hab : a ≠ b := fun h => haB' (h ▸ hbB)
  obtain ⟨A₁, A₂, hA⟩ := exists_isCutPair hC (hsub ha𝒜) (hsub hb𝒜) hab
  -- the two points are not the anchors, so each lies on exactly one arc
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  have hsplit : ∀ (D₁ D₂ : Set Plane), IsCutPair C a b D₁ D₂ → ∀ z : Plane,
      z ∈ B₁ ∩ B₂ → z ∈ D₁ → z ∉ D₂ := by
    intro D₁ D₂ hD z hz hzD hzD'
    have : z ∈ ({a, b} : Set Plane) := by rw [← hD.inter_eq]; exact ⟨hzD, hzD'⟩
    rcases this with rfl | rfl
    · exact haB' hz.2
    · exact hbB' hz.1
  rcases hB.separates hA haB' hbB' with ⟨hp1, hr2⟩ | ⟨hp2, hr1⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hA, hp1, hsplit A₁ A₂ hA p hpB hp1, hr2,
      hsplit A₂ A₁ hA.symm r hrB hr2⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₂, A₁, hab, hA.symm, hp2, hsplit A₂ A₁ hA.symm p hpB hp2, hr1,
      hsplit A₁ A₂ hA r hrB hr1⟩

/-! ### The hypotheses

Two predicates, one for each thing that is still being built. Both are *statements about one
curve*, so a consumer can discharge them curve by curve. -/

/-! ### Discharging `HasAnchorCrosscuts` from a skeleton homeomorphism

The two steps a consumer has to perform, isolated so that they need not be reinvented: the
image of a crosscut under the finite skeleton homeomorphism is again a crosscut, and the
agreement clause follows from agreement of the limit map with that homeomorphism on the
crosscut. Neither says anything about the square, so both apply to the source and the target
side of any of the stages. -/

/-! ### `lem:crosscut-side-correspondence` -/

/-! ### `prop:boundary-continuity` -/

/-! ### `thm:square-extension` -/

/-! ### The assembled hypothesis, and `Schoenflies.SquareExtension` -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-! ### The invariants at every stage -/

/-- **Assertions (iii), (v), (vi) and abstract (viii) hold at every generated stage.** The
induction is over the two constructors; the base case is supplied by the producer of `S₀` —
`prop:initial-pair` for the blueprint's own generated structures. -/
theorem _root_.Schoenflies.GeneratedStructure.combInvariants {S₀ S : CellStructure γ}
    (h : GeneratedStructure S₀ S) (h₀ : S₀.CombInvariants) : S.CombInvariants := by
  induction h with
  | base => exact h₀
  | subdivideEdge _ d ih => exact d.combInvariants ih
  | splitFace _ d ih => exact d.combInvariants ih

/-! ### The geometric assertions

Assertion (i) is the only geometric input the rest need: (ii), (viii) and (ix) follow from it
formally, with no further topology beyond "a nonempty open set contained in a closure meets the
set". That is why they are stated here for an arbitrary realization satisfying (i), rather than
by induction: the induction is entirely in (i) and (vii), and those are the standing gap of this
module. -/

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

/-- **One 2-cell split, geometrically** — the induction step of assertions (i) and (vii),
assembled from `Schoenflies.general_crosscut`.

The old open 2-cell `Int(C)` is the disjoint union of the two new open 2-cells and the open
crosscut; each new open 2-cell is open and nonempty; and the closure of each is that open
2-cell together with its own boundary curve `Aᵢ ∪ P`, which is "every closed cell is the union
of its open subcells" for the two new 2-cells. -/
theorem crosscut_cell_partition (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {p, q}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {p, q}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {p, q}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) :=
  ⟨h.inside_eq_split hjordan hcut hcollars, h.disjoint_sides hjordan hcut,
    h.disjoint_side_crosscut hjordan hcut, h.disjoint_side_crosscut hjordan hcut.symm,
    h.isOpen_side hjordan hcut, h.isOpen_side hjordan hcut.symm,
    h.side_nonempty hjordan hcut, h.side_nonempty hjordan hcut.symm,
    h.closure_side hjordan hcut, h.closure_side hjordan hcut.symm⟩

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

/-- Cutting a cyclic face at two distinct boundary vertices gives the two pieces required by
`SplitData`.  The second path returned by `Graph.IsCycleThrough.split_at` is reversed so that
both displayed paths run from `a` to `b`. -/
theorem boundaryPaths (h : S.FaceCycle F) {a b : γ} (ha : a ∈ V(S.skel))
    (hb : b ∈ V(S.skel)) (haF : S.sub a F) (hbF : S.sub b F) (hab : a ≠ b) :
    Nonempty (S.BoundaryPaths F a b) := by
  have haW := h.mem_walk_of_vertex_sub ha haF
  have hbW := h.mem_walk_of_vertex_sub hb hbF
  obtain ⟨D₁, D₂, h₁, h₂, hperm, hmeet⟩ :=
    h.isCycle.split_at haW hbW hab
  have hnodup : (h.edge :: h.walk).Nodup :=
    List.nodup_cons.2 ⟨h.isCycle.notMem, h.isCycle.isPath.nodup⟩
  have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg₁ hg₂ =>
    (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg₁ g hg₂ rfl
  have hclosed : S.skel.IsWalk h.target (h.edge :: h.walk) h.target :=
    .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk
  have hcarrier : S.pathCells a D₁ ∪ S.pathCells a D₂.reverse =
      S.pathCells h.target (h.edge :: h.walk) := by
    calc
      S.pathCells a D₁ ∪ S.pathCells a D₂.reverse =
          S.pathCells a D₁ ∪ S.pathCells b D₂ := by
            rw [pathCells_reverse h₂.isWalk]
      _ = S.pathCells a (D₁ ++ D₂) := (pathCells_append h₁.isWalk h₂.isWalk).symm
      _ = S.pathCells h.target (h.edge :: h.walk) :=
        pathCells_eq_of_perm (h₁.isWalk.append h₂.isWalk) hclosed hperm
          (List.append_ne_nil_of_left_ne_nil (h₁.ne_nil hab) D₂) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hinter : S.pathCells a D₁ ∩ S.pathCells a D₂.reverse = {a, b} := by
    apply Set.Subset.antisymm
    · rintro σ ⟨hσ₁, hσ₂⟩
      have hσ₂' : σ ∈ S.pathCells b D₂ := by
        rw [← pathCells_reverse h₂.isWalk]
        exact hσ₂
      rcases hσ₁ with he₁ | hv₁
      · rcases hσ₂' with he₂ | hv₂
        · exact (hdisj σ he₁ he₂).elim
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (h₂.isWalk.walkVertices_subset hv₂) (h₁.edge_mem he₁)).elim
      · rcases hσ₂' with he₂ | hv₂
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (h₁.isWalk.walkVertices_subset hv₁) (h₂.edge_mem he₂)).elim
        · exact hmeet σ hv₁ hv₂
    · rintro σ (rfl | rfl)
      · exact ⟨Or.inr Graph.mem_walkVertices_self, Or.inr Graph.mem_walkVertices_self⟩
      · exact ⟨Or.inr h₁.target_mem_walkVertices,
          Or.inr h₂.reverse.target_mem_walkVertices⟩
  exact ⟨{
    path₁ := D₁
    path₂ := D₂.reverse
    isPath₁ := h₁
    isPath₂ := h₂.reverse
    sub_face := by intro σ; rw [h.sub_face, hcarrier]
    paths_meet := hinter
  }⟩

end FaceCycle

namespace BoundaryCycles

variable {S : CellStructure γ}

/-- The two chosen boundary paths between distinct vertices of a cyclic face. -/
noncomputable def boundaryPaths (h : S.BoundaryCycles) (F : γ) (hF : F ∈ S.faces)
    (a b : γ) (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (haF : S.sub a F) (hbF : S.sub b F) (hab : a ≠ b) : S.BoundaryPaths F a b :=
  Classical.choice ((h.faceCycle F hF).boundaryPaths ha hb haF hbF hab)

end BoundaryCycles

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CellulationInvariants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
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

namespace Realization

variable {R : S.Realization} {D : Set Plane} {F T σ τ : γ}

/-! ### The realized point set of a set of cells

Every geometric statement of `lem:cellulation-invariants` is about a *union of open cells*: the
closure of a cell, the boundary of a 2-cell, the realized ear, the realized boundary path. One
notation serves them all. -/

/-! ### Assertion (vii)

"In each of the two realizations, every 2-cell boundary walk is realized by a Jordan curve, and
the open 2-cell is the bounded complementary region of that curve."

`Schoenflies.inside` is the union of the *bounded* complementary components of a set, so
"the bounded complementary region of the Jordan curve `J`" is literally `inside J`; and by
`Schoenflies.jordan_curve_theorem` it is a single region. -/

namespace IsFaceJordan

theorem isConnected (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsConnected (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isConnected_inside

theorem isBounded (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsBounded (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isBounded_inside

theorem nonempty (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : (R.cell F).Nonempty :=
  (hJ.isConnected hF).nonempty

end IsFaceJordan

namespace IsCellDecomposition

/-- **Assertion (viii)**, with the openness hypothesis of
`IsCellDecomposition.face_eq` discharged by assertion (vii): distinct open 2-cells are never
comparable. -/
theorem face_eq_of_isFaceJordan (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : R.cell F ⊆ closure (R.cell T)) : F = T :=
  h.face_eq hF hT (hJ.isOpen hF) hsub

/-- **Assertion (viii)** against the abstract relation. -/
theorem sub_face_eq (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : S.sub F T) : F = T :=
  h.face_eq_of_isFaceJordan hJ hF hT
    (h.subset_closure (S.mem_cells_of_mem_faces hF) (S.mem_cells_of_mem_faces hT) hsub)

end IsCellDecomposition

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

namespace SubdivData

variable (d : S.SubdivData)

/-- Edge subdivision preserves cyclic boundaries. -/
theorem boundaryCycles (d : S.SubdivData) (hcycles : S.BoundaryCycles)
    (hS : S.CombInvariants) : (S.subdivideEdge d).BoundaryCycles where
  cycle F hF := by
    rw [subdivideEdge_faces] at hF
    obtain ⟨c⟩ := hcycles.cycle F hF
    obtain ⟨u, hW, hsub⟩ := d.boundary_subst hF
    rw [c.boundary_eq] at hW hsub
    obtain ⟨e', a', D', hlist, hcycle⟩ :=
      SubdivData.SubstWalk.exists_isCycleThrough hsub hW c.isCycle
    have hclosed : S.skel.IsWalk c.target (c.edge :: c.walk) c.target :=
      .cons c.isCycle.isLink.symm c.isCycle.isPath.isWalk
    have hOldCarrier : S.pathCells u (c.edge :: c.walk) =
        S.pathCells c.target (c.edge :: c.walk) :=
      FaceCycle.pathCells_eq_of_perm hW hclosed (.refl _) (by simp) (by simp)
    have hNewCarrier : (S.subdivideEdge d).pathCells u (e' :: D') =
        {z | (z ∈ S.pathCells u (c.edge :: c.walk) ∧ z ≠ d.edge) ∨
          (d.edge ∈ c.edge :: c.walk ∧ z ∈ d.newCells)} := by
      rw [← hlist]
      exact SubdivData.SubstWalk.pathCells_eq hsub hW
    have hedgeList : d.edge ∈ S.pathCells u (c.edge :: c.walk) ↔
        d.edge ∈ c.edge :: c.walk := by
      constructor
      · rintro (he | hv)
        · exact he
        · exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (hW.walkVertices_subset hv) d.edge_mem_edgeSet).elim
      · exact Or.inl
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    refine ⟨{
      face_mem := by rwa [subdivideEdge_faces]
      edge := e'
      source := a'
      target := u
      walk := D'
      boundary_eq := hlist
      isCycle := hcycle
      sub_face := ?_
    }⟩
    intro σ
    rw [subdivideEdge_sub, hNewCarrier]
    change d.subRel σ F ↔ σ = F ∨
      ((σ ∈ S.pathCells u (c.edge :: c.walk) ∧ σ ≠ d.edge) ∨
        (d.edge ∈ c.edge :: c.walk ∧ σ ∈ d.newCells))
    constructor
    · intro h
      rcases h with ⟨-, -, hσe, -, h⟩ | ⟨heq, hnew⟩ | ⟨hσ, hFnew⟩ |
          ⟨hσ, hFnew⟩ | ⟨hσ, hFnew⟩ | ⟨hnew, -, h⟩
      · rcases c.sub_face.1 h with rfl | hcarrier
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hOldCarrier.symm ▸ hcarrier, hσe⟩)
      · exact absurd (heq ▸ hnew) (SubdivData.notMem_newCells_of_mem_cells hFc)
      · rcases hFnew with rfl | rfl
        exacts [(d.newEdge₁_notMem hFc).elim, (d.newEdge₂_notMem hFc).elim]
      · exact (d.newEdge₁_notMem (hFnew ▸ hFc)).elim
      · exact (d.newEdge₂_notMem (hFnew ▸ hFc)).elim
      · rcases c.sub_face.1 h with hedge | hcarrier
        · exact absurd hedge.symm hFe
        · exact Or.inr (Or.inr ⟨hedgeList.1 (hOldCarrier.symm ▸ hcarrier), hnew⟩)
    · rintro (rfl | (⟨hcarrier, hσe⟩ | ⟨helist, hnew⟩))
      · exact d.subRel_of_old hFc hFc hFe hFe (hS.sub_refl hFc)
      · have hσc : σ ∈ S.cells := CellStructure.pathCells_subset_cells hW hcarrier
        have hsubOld : S.sub σ F := c.sub_face.2
          (Or.inr (hOldCarrier ▸ hcarrier))
        exact d.subRel_of_old hσc hFc hσe hFe hsubOld
      · have hsubEdge : S.sub d.edge F := c.sub_face.2
          (Or.inr (hOldCarrier ▸ hedgeList.2 helist))
        exact (d.newCells_subRel_iff hnew hFc).2 ⟨hFe, hsubEdge⟩

end SubdivData

/-! ### The invariant at every generated stage -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.overlayGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-! ### Relabelling a drawing -/

section Drawing

variable {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- Edge relabelling changes neither the occupied point set nor any geometric edge arc. -/
theorem pointSet_relabelEdges [Nonempty β] (hf : InjOn f E(G)) :
    pointSet (G.relabelEdges f hf) (relabelDrawing G f drawing) = pointSet G drawing := by
  rw [pointSet, pointSet, vertexSet_relabelEdges, edgeSet_relabelEdges]
  congr 1
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun d hd => ?_
    obtain ⟨e, he, rfl⟩ := hd
    rw [edgeArc_relabelDrawing hf he]
    intro x hx
    exact Set.mem_iUnion₂_of_mem he hx
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [← edgeArc_relabelDrawing hf he]
    intro x hx
    exact Set.mem_iUnion₂_of_mem (show f e ∈ f '' E(G) from ⟨e, he, rfl⟩) hx

end Drawing

end Graph
end

section
-- module Solutions.Q146_CD.MatchedArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Matching and cutting simple polygonal arcs

An ear can have an arbitrary finite number of abstract edges.  On the target side we only
obtain one set-level polygonal crosscut.  This module supplies the two facts that reconcile
those descriptions.

* Two named arcs admit an endpoint-preserving homeomorphism, obtained by matching their
  parameters.
* An arc contained in a polygonal arc is polygonal.  Consequently the images of all source
  edge arcs under the parameter-matching homeomorphism are polygonal target edge arcs.
-/

open Set unitInterval

namespace Schoenflies

/-! ## The inverse of a compact parametrisation -/

/-! ## A subarc of a polygonal arc is polygonal -/

/-- Every closed subarc of a polygonal arc is polygonal. -/
theorem IsArcBetween.isPolygonal_of_subset_arc {A C : Set Plane} {p q r s : Plane}
    (hA : IsArcBetween A p q) (hC : IsArcBetween C r s)
    (hpoly : IsPolygonal C) (hAC : A ⊆ C) : IsPolygonal A := by
  have hpq : p ≠ q := by
    obtain ⟨f, -, hi, -, h0, h1⟩ := hA
    intro hpq'
    exact zero_ne_one (hi zero_mem_I one_mem_I (by simpa [h0, h1] using hpq'))
  obtain ⟨vs, hvs, -, -, hsub, hvsArc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly hC.isArc.isConnected.isPreconnected hpq
      (hAC hA.left_mem) (hAC hA.right_mem)
  have heq := hA.eq_of_subset_arc hvsArc hC hAC hsub
  exact ⟨vs, heq⟩

/-! ## Matching two named arcs -/

/-! ## Transporting a plane drawing along an arc homeomorphism -/

end Schoenflies

open Schoenflies
end

section
-- module Solutions.Q146_CD.RealizeSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
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

/-! ## The ear, drawn

`SplitData` fixes the *abstract* ear: a path graph `d.ear` glued to the skeleton at
`d.source` and `d.target`. Drawing it means choosing a point for each of its vertices and a
parametrization for each of its edges. `EarCrosscut` is the bundle of conditions under which
that drawing is a polygonal crosscut of the realized open 2-cell `R.cell d.face`. -/

namespace SplitData

variable (d : S.SplitData)

/-! ## The realization built from a drawn ear -/

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

/-! ## The realization -/

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- **The constructed realization is a crosscut split of the old one** — every clause of
`SplitData.IsCrosscutSplit`, discharged.

Composed with `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the whole
induction step of `lem:cellulation-invariants` over the second elementary operation. -/
theorem isCrosscutSplit_realize {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    d.IsCrosscutSplit R (realize R d earPos earDraw hE) where
  cell_eq := fun _ hσ _ => splitCell_of_mem_cells hσ
  isCrosscut := by
    rw [cellUnion_earCells]
    exact hE.isCrosscut_earSet hcd hJ
  isCutPair := isCutPair_of_inter hcd hJ
  cell_face₁ := by rw [realize_cell, splitCell_face₁, cellUnion_earCells]
  cell_face₂ := by rw [realize_cell, splitCell_face₂, cellUnion_earCells]
  cellUnion_earNewCells := by rw [cellUnion_earNewCells, cellUnion_earCells]
  earNonempty := by
    intro σ hσ
    have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    rcases hσ' with ⟨hσV, -⟩ | hσE
    · rw [realize_cell, hE.splitCell_earVertex hσV]
      exact ⟨earPos σ, rfl⟩
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hσE
      rw [realize_cell, splitCell_earEdge hσE, hE.edgeArc_diff hl]
      exact (hE.isDrawing.edge_isArcBetween (hl.map earPos)).nonempty_diff
  earDisjoint := by
    intro σ τ hσ hτ hne
    have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    have hτ' : τ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hτ
    rcases hσ' with ⟨hσV, -⟩ | hσE <;> rcases hτ' with ⟨hτV, -⟩ | hτE
    · rw [realize_cell, hE.splitCell_earVertex hσV, hE.splitCell_earVertex hτV]
      refine Set.disjoint_left.2 ?_
      rintro x rfl hx
      exact hne (hE.injOn hσV hτV (Set.mem_singleton_iff.1 hx))
    · rw [realize_cell, hE.splitCell_earVertex hσV, splitCell_earEdge hτE]
      refine Set.disjoint_left.2 ?_
      rintro x rfl hx
      exact hx.2 ⟨σ, hσV, rfl⟩
    · rw [realize_cell, splitCell_earEdge hσE, hE.splitCell_earVertex hτV]
      refine Set.disjoint_right.2 ?_
      rintro x rfl hx
      exact hx.2 ⟨τ, hτV, rfl⟩
    · rw [realize_cell, splitCell_earEdge hσE, splitCell_earEdge hτE]
      refine Set.disjoint_left.2 fun x hx hx' => hx.2 ?_
      have hmem := hE.isDrawing.edge_inter (by rwa [d.edgeSet_earGraph])
        (by rwa [d.edgeSet_earGraph]) hne hx.1 hx'.1
      rw [d.vertexSet_earGraph] at hmem
      exact hmem.1
  closure_earVertex := by
    intro z hz _ _
    rw [realize_cell, hE.splitCell_earVertex hz]
    exact closure_singleton
  closure_earEdge := by
    intro f a b hl
    have harc := hE.isDrawing.edge_isArcBetween (hl.map earPos)
    rw [realize_cell, splitCell_earEdge hl.edge_mem, hE.edgeArc_diff hl,
      hE.splitCell_earVertex hl.left_mem, hE.splitCell_earVertex hl.right_mem,
      hE.closure_edgeArc_diff hl]
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · by_cases hxab : x ∈ ({earPos a, earPos b} : Set Plane)
      · rcases hxab with rfl | rfl
        exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
      · exact Or.inl ⟨hx, hxab⟩
    · rintro x (hx | hx | hx)
      · exact hx.1
      · rw [Set.mem_singleton_iff.1 hx]
        exact harc.left_mem
      · rw [Set.mem_singleton_iff.1 hx]
        exact harc.right_mem

/-- **The induction step of `lem:cellulation-invariants` over the second elementary operation,
end to end.** From a realization of `S` satisfying assertions (i) and (vii) and a drawing of
the ear as a polygonal crosscut, a realization of `S.splitFace d` satisfying (i) and (vii),
refining it along `SplitData.parent`. -/
theorem isCellDecomposition_and_isFaceJordan_realize (hS : S.CombInvariants) {D : Set Plane}
    (hcd : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    (realize R d earPos earDraw hE).IsCellDecomposition D ∧
      (realize R d earPos earDraw hE).IsFaceJordan ∧
      (realize R d earPos earDraw hE).Refines R d.parent :=
  (isCrosscutSplit_realize hE hcd hJ).isCellDecomposition_and_isFaceJordan hS hcd hJ

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
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

variable {S : CellStructure γ} {d : S.SplitData} {R₁ R₂ : S.Realization}
  {srcPos : γ → Plane} {srcDraw : γ → ℝ → Plane}

/-- A set-level target crosscut can be divided into exactly the abstract edges of an already
drawn source ear.  The division is obtained by matching the parameters of the two whole arcs:
each target edge is the image of its source counterpart.  Closed subarcs of the polygonal
target crosscut are polygonal, so no relation between the number of straight segments on the
two sides is needed. -/
theorem exists_matched_target (hsrc : d.EarCrosscut R₁ srcPos srcDraw)
    {A : Set Plane} (hApoly : IsPolygonal A)
    (hAarc : IsArcBetween A (R₂.pos d.source) (R₂.pos d.target))
    (hAsub : A \ {R₂.pos d.source, R₂.pos d.target} ⊆ R₂.cell d.face)
    (hdisj : Disjoint (R₂.cell d.face) R₂.skeletonSet) :
    ∃ tgtPos : γ → Plane, ∃ tgtDraw : γ → ℝ → Plane,
      ∃ _ : d.EarHomeo srcPos srcDraw tgtPos tgtDraw,
      d.EarCrosscut R₂ tgtPos tgtDraw ∧
      ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (Graph.edgeArc tgtDraw e) := by
  classical
  let m : ArcHomeo (d.earSet srcPos srcDraw) A
      (R₁.pos d.source) (R₁.pos d.target) (R₂.pos d.source) (R₂.pos d.target) :=
    Classical.choice (exists_arcHomeo hsrc.isArcBetween_earSet hAarc)
  let tgtPos : γ → Plane := fun z => m.toFun (srcPos z)
  let tgtDraw : γ → ℝ → Plane := Graph.mapDrawing m srcDraw
  have hgraph : d.earGraph tgtPos = (d.earGraph srcPos).map m.toFun := by
    change d.ear.map tgtPos = (d.ear.map srcPos).map m.toFun
    rw [Graph.map_map]
    rfl
  have hset : d.earSet tgtPos tgtDraw = A := by
    rw [CellStructure.SplitData.earSet, hgraph,
      Graph.pointSet_map_mapDrawing (G := d.earGraph srcPos)]
    exact m.image_eq
  have htgt : d.EarCrosscut R₂ tgtPos tgtDraw := {
    pos_source := by
      change m.toFun (srcPos d.source) = R₂.pos d.source
      rw [hsrc.pos_source]
      exact m.map_left
    pos_target := by
      change m.toFun (srcPos d.target) = R₂.pos d.target
      rw [hsrc.pos_target]
      exact m.map_right
    injOn := by
      intro x hx y hy hxy
      apply hsrc.injOn hx hy
      apply m.injOn (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hx)
        (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hy)
      exact hxy
    isDrawing := by
      rw [hgraph]
      exact hsrc.isDrawing.map_arcHomeo m rfl
    subset_face := by
      intro x hx
      apply hAsub
      exact ⟨hset ▸ hx.1, hx.2⟩
    disjoint_skeleton := hdisj
    polygonal := hset ▸ hApoly
  }
  have hhomeo : d.EarHomeo srcPos srcDraw tgtPos tgtDraw := {
    toFun := m.toFun
    invFun := m.invFun
    continuousOn_toFun := m.continuousOn_toFun
    continuousOn_invFun := by
      rw [hset]
      exact m.continuousOn_invFun
    leftInvOn := m.leftInvOn
    rightInvOn := by
      rw [hset]
      exact m.rightInvOn
    earPos_apply := by intro z _; rfl
    edgeArc_image := by
      intro e _
      exact (Graph.edgeArc_mapDrawing m e).symm
  }
  refine ⟨tgtPos, tgtDraw, hhomeo, htgt, ?_⟩
  intro e he
  obtain ⟨x, y, hxy⟩ := d.ear.exists_isLink_of_mem_edgeSet he
  have hedge : IsArcBetween (Graph.edgeArc tgtDraw e) (tgtPos x) (tgtPos y) :=
    htgt.isDrawing.edge_isArcBetween (hxy.map tgtPos)
  exact hedge.isPolygonal_of_subset_arc hAarc hApoly
    (hset ▸ CellStructure.SplitData.EarCrosscut.edgeArc_subset_earSet he)

end SplitData.EarCrosscut

namespace Realization

variable {S : CellStructure γ}

/-! #### Where an ear can lie

*The interior of each ear lies in one current face, because it is connected and disjoint from the
current skeleton.* That is the second sentence of step 2, and it is proved here for an arbitrary
connected subset of the closed domain missing the skeleton.

The only input beyond assertion (i) is `Schoenflies.CellsAbsorb` — assertion (i) in the
"a connected set disjoint from the skeleton that meets a 2-cell lies in it" reading, which
`Schoenflies/SkeletonAccess.lean` also carries as its single hypothesis and which
`Schoenflies.cellsAbsorb_of_isComponent_in` discharges on the target side. -/

variable {R : S.Realization} {D N Q : Set Plane} {F σ : γ} {z : Plane}

namespace IsCellDecomposition

/-- The frontier of a Jordan face is part of the realized 1-skeleton.  Assertion (i) writes the
frontier as the union of strict subcells; assertion (vii) rules out a second face among those
subcells, leaving only vertices and edges. -/
theorem frontier_cell_subset_skeletonSet (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : frontier (R.cell F) ⊆ R.skeletonSet := by
  rw [← hJ.faceBoundary_eq h hF, Realization.faceBoundary]
  rintro z hz
  obtain ⟨σ, ⟨⟨hσ, hσF⟩, hσne⟩, hz⟩ := Realization.mem_cellUnion_iff.1 hz
  rcases hσ with (hv | he) | hface
  · exact R.cell_subset_skeletonSet (Or.inl hv) hz
  · exact R.cell_subset_skeletonSet (Or.inr he) hz
  · exact absurd (h.sub_face_eq hJ hface hF hσF) hσne

/-- Assertions (i) and (vii) discharge the `CellsAbsorb` reading of the cellulation invariant:
a connected set missing the skeleton cannot cross the Jordan frontier of a face it meets. -/
theorem cellsAbsorb (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F} := by
  rintro N hN hNdisj A ⟨F, hF, rfl⟩ hmeet
  exact subset_of_isPreconnected_of_frontier_disjoint (hJ.isOpen hF) hN
    (hNdisj.mono_right (h.frontier_cell_subset_skeletonSet hJ hF)) hmeet

/-- A Jordan face contained in an ambient open set `Q` is a connected component of
`Q \ skeleton` as soon as its frontier belongs to the skeleton. -/
theorem face_eq_connectedComponentIn (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hFQ : R.cell F ⊆ Q) (z : Plane)
    (hz : z ∈ R.cell F) :
    R.cell F = connectedComponentIn (Q \ R.skeletonSet) z := by
  symm
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hJ.isOpen hF)
    (hJ.isConnected hF).isPreconnected ?_ ?_ hz
  · exact fun x hx => ⟨hFQ hx,
      Set.disjoint_left.1 (R.disjoint_cell_skeletonSet h hF) hx⟩
  · refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨hxfr, -, hxskel⟩
    exact hxskel (h.frontier_cell_subset_skeletonSet hJ hF hxfr)

/-- A 0-cell in the closure of an open 2-cell is a subcell of it — assertion (ix) read at a
vertex. This is how an ear's endpoint is recognised as lying on the boundary cycle of the face
its interior occupies. -/
theorem sub_of_pos_mem_closure_cell (h : R.IsCellDecomposition D) {a F : γ}
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R.pos a ∈ closure (R.cell F)) :
    S.sub a F := by
  refine h.sub_of_subset_closure (S.mem_cells_of_mem_vertexSet ha)
    (S.mem_cells_of_mem_faces hF) ?_
  rw [R.cell_vertex ha]
  exact Set.singleton_subset_iff.2 hmem

/-- **An ear lies in a single current face.** A nonempty connected subset of the closed domain
disjoint from the realized skeleton lies inside one open 2-cell, and inside only that one. -/
theorem exists_unique_face_subset_cell (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨z, hz⟩ := hNne
  obtain ⟨F, hFc, hzF⟩ := h.exists_cell (hND hz)
  have hznot : z ∉ R.skeletonSet := Set.disjoint_left.1 hNdisj hz
  have hFf : F ∈ S.faces := R.mem_faces_of_notMem_skeletonSet hFc hzF hznot
  refine ⟨F, hFf, hcells N hN hNdisj (R.cell F) ⟨F, hFf, rfl⟩ ⟨z, hz, hzF⟩, fun T hT hNT => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (S.mem_cells_of_mem_faces hT) hFc hne) (hNT hz) hzF

/-- **One ear, placed — the source-side input of the induction step.** The open part `N` of the
ear is connected, inside the closed domain and disjoint from the current skeleton, so it lies in
a unique current 2-cell `F`; and each endpoint of the ear, being a 0-cell in the closure of `N`,
is a subcell of `F`, i.e. lies on its boundary cycle.

Feeding the two `S.sub` conclusions back through `IsCellDecomposition.subset_closure` in the
*other* realization is exactly `Schoenflies.exists_target_ear`'s two closure hypotheses. -/
theorem exists_face_of_ear (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (hacl : R.pos a ∈ closure N) (hbcl : R.pos b ∈ closure N) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ S.sub a F ∧ S.sub b F ∧
      ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨F, hF, hNF, huniq⟩ := h.exists_unique_face_subset_cell hcells hN hNne hND hNdisj
  exact ⟨F, hF, hNF,
    h.sub_of_pos_mem_closure_cell ha hF (closure_mono hNF hacl),
    h.sub_of_pos_mem_closure_cell hb hF (closure_mono hNF hbcl), huniq⟩

end IsCellDecomposition

end Realization

end CellStructure

/-! ### A generated matched cell structure, with its geometry

`def:generated-structure` says what the *abstract* object is; `GeneratedStructure` in
`Schoenflies/GeneratedStructure.lean` is that. What a transfer produces, and what the
finite-transfer theorem consumes, is the abstract object together with its two realizations, the
skeleton homeomorphism between them, and the two cell decompositions of
`lem:cellulation-invariants`(i). That bundle is `GeneratedPair`.

It is data, not a `Prop`: a consumer reads `.src`, `.tgt`, `.homeo`, `.str` by name. -/

namespace GeneratedPair

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The combinatorial invariants hold at every generated stage, once they hold at the base —
`Schoenflies.GeneratedStructure.combInvariants`, read off the bundle. -/
theorem combInvariants (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h₀ : S₀.CombInvariants) : P.str.CombInvariants :=
  P.generated.combInvariants h₀

/-- **The last paragraph of the proof of `thm:finite-transfer`, target half.** Once the source
realization's open nonboundary part is connected, so is the target's — this is part (b) of
`lem:combinatorial-invariance` — and the target realization, weakly admissible by construction,
is therefore admissible. -/
theorem tgt_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.tgt.IsAdmissible tgtOuter tgtDom :=
  { P.tgt_isWeaklyAdmissible with
    isConnected_nonboundary := P.homeo.isConnected_nonboundary_iff.1 h }

/-- Every target face lies in the open part of the prescribed target domain. -/
theorem tgt_face_subset_interior (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) : P.tgt.cell F ⊆ tgtDom \ tgtOuter := by
  intro x hx
  refine ⟨P.tgt_isCellDecomposition.cell_subset_domain
    (P.str.mem_cells_of_mem_faces hF) hx, ?_⟩
  intro hxOuter
  have hxSkel : x ∈ P.tgt.skeletonSet := by
    rw [← P.tgt_isWeaklyAdmissible.outerSet_eq] at hxOuter
    exact P.tgt.outerSet_subset_skeletonSet hxOuter
  exact Set.disjoint_left.1
    (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hx hxSkel

/-- Target faces have the component presentation consumed by polygonal side accessibility. -/
theorem tgt_face_isComponent (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) :
    P.tgt.cell F ⊆ tgtDom \ tgtOuter ∧
      ∃ z, P.tgt.cell F =
        connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
  have hne := P.tgt_isFaceJordan.nonempty hF
  obtain ⟨z, hz⟩ := hne
  exact ⟨P.tgt_face_subset_interior hF, z,
    P.tgt_isCellDecomposition.face_eq_connectedComponentIn P.tgt_isFaceJordan hF
      (P.tgt_face_subset_interior hF) z hz⟩

/-! #### The matched split constructor

`RealizeSplit` and `MatchedSplit` construct the two new realizations and their skeleton
homeomorphism.  The definition below is the missing bundle-level constructor: it installs those
objects in a `GeneratedPair` and records the propagated cell-decomposition and Jordan-face
invariants.  Weak admissibility is then derived from the old pair and the two polygonal ear
drawings by `EarCrosscut.isWeaklyAdmissible_realize`. -/

/-- Build the next generated pair from matching geometric realizations of one abstract face
split. -/
noncomputable def split (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := P.str.splitFace d
  generated := .splitFace P.generated d
  str_combInvariants := d.combInvariants hS
  str_boundaryCycles := d.boundaryCycles P.str_boundaryCycles hS
  src := d.realize P.src srcPos srcDraw hsrc
  tgt := d.realize P.tgt tgtPos tgtDraw htgt
  homeo := d.splitHomeo P.homeo hsrc htgt m
  src_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.1
  tgtInterior_isOpen := P.tgtInterior_isOpen
  tgtInterior_frontier_subset := P.tgtInterior_frontier_subset.trans
    (d.skeletonSet_subset_realize htgt)
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(d.skeleton) at he
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_skel he]
      exact P.tgt_isPolygonal he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_ear he]
      exact htgtEdgePoly he
  src_isWeaklyAdmissible := hsrc.isWeaklyAdmissible_realize P.src_isWeaklyAdmissible
    P.src_isCellDecomposition hsrcEdgePoly
  tgt_isWeaklyAdmissible := htgt.isWeaklyAdmissible_realize P.tgt_isWeaklyAdmissible
    P.tgt_isCellDecomposition htgtEdgePoly

@[simp] theorem split_str (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    (P.split hS d srcPos srcDraw tgtPos tgtDraw hsrc htgt m hsrcEdgePoly
      htgtEdgePoly).str =
      P.str.splitFace d := rfl

end GeneratedPair

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

/-- **The hypotheses of `thm:finite-transfer`(a) on the extension `H`.** -/
structure IsSourceExtension {S : CellStructure γ} (R : S.Realization) (outer dom : Set Plane)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop where
  /-- `H` is finite. -/
  finite : H.Finite
  /-- `H` is a plane graph. -/
  isDrawing : IsDrawing H Hdraw
  /-- `H` is 2-connected. -/
  isTwoConnected : H.IsTwoConnected
  /-- Every 0-cell of `Γ` is a vertex of `H`. -/
  vertexSet_subset : V(R.graph) ⊆ V(H)
  /-- `|Γ| ⊆ |H|`. -/
  skeletonSet_subset : R.skeletonSet ⊆ pointSet H Hdraw
  /-- An edge of `H` whose interior meets an open edge of `Γ` runs inside it.  Intersections at
  vertices of `H` are deliberately excluded: a transverse crossing is first made a vertex by
  the polygonal overlay, and does not make either of its two incident branches part of the old
  edge. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → ∀ ⦃f⦄, f ∈ E(H) →
    (edgeArc Hdraw f ∩ (R.cell e \ V(H))).Nonempty →
      edgeArc Hdraw f ⊆ edgeArc R.drawing e
  /-- `H` is drawn in the closed domain. -/
  pointSet_subset : pointSet H Hdraw ⊆ dom
  /-- Each edge of `H` is an outer edge or a polygonal nonboundary edge with interior in the
  open domain. -/
  edge_dichotomy : ∀ ⦃f⦄, f ∈ E(H) → edgeArc Hdraw f ⊆ outer ∨
    (IsPolygonal (edgeArc Hdraw f) ∧ edgeArc Hdraw f \ V(H) ⊆ dom \ outer)
  /-- `|H| ∖ C` is connected. -/
  isConnected : IsConnected (pointSet H Hdraw \ outer)

/-! ### The conclusion

`IsPartialTransferOf T P B par` is the invariant the induction of steps 2–3 carries: `T` is a
generated pair refining `P` along `par` whose source realization occupies exactly what the
current subgraph `B` of `H` occupies. It asks for **no** connectedness of the open nonboundary
part — `rem:intermediate-disconnection` — because an ear with both endpoints on the outer cycle
really does disconnect it, and later ears reconnect it.

`IsTransferOf` is the same with admissibility of both final realizations added; that is the
theorem's conclusion, and `GeneratedPair.src_isAdmissible` / `GeneratedPair.tgt_isAdmissible`
are what produce it from the connectedness hypothesis on `H`. -/

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Extend two prescribed, distinct names to an injection on a finite set, with every other
value fresh outside a prescribed finite set. -/
theorem exists_injective_pinned_avoiding [Infinite γ]
    {used : Set γ} (hused : used.Finite) {u v : γ}
    (hu : u ∈ used) (hv : v ∈ used) (huv : u ≠ v)
    {s : Set α} (hs : s.Finite) {a b : α} (hab : a ≠ b) :
    ∃ name : α → γ, name a = u ∧ name b = v ∧ InjOn name s ∧
      ∀ x ∈ s, x ≠ a → x ≠ b → name x ∉ used := by
  classical
  let inner := {x : α // x ∈ s ∧ x ≠ a ∧ x ≠ b}
  letI : Finite inner := Set.finite_coe_iff.mpr (hs.subset fun x hx => hx.1)
  obtain ⟨fresh, hfresh, havoid⟩ := exists_injective_avoiding used hused inner
  let name : α → γ := fun x =>
    if hxa : x = a then u else if hxb : x = b then v
    else if hx : x ∈ s then fresh ⟨x, hx, hxa, hxb⟩ else u
  have hnamea : name a = u := by simp [name]
  have hnameb : name b = v := by simp [name, Ne.symm hab]
  have hname_inner (x : α) (hx : x ∈ s) (hxa : x ≠ a) (hxb : x ≠ b) :
      name x = fresh (⟨x, hx, hxa, hxb⟩ : inner) := by
    simp [name, hxa, hxb, hx]
  refine ⟨name, hnamea, hnameb, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      by_cases hyb : y = b
      · subst y
        exact absurd (hnamea.symm.trans (hxy.trans hnameb)) huv
      · exfalso
        apply havoid ⟨y, hy, hya, hyb⟩
        rw [← hname_inner y hy hya hyb, ← hxy, hnamea]
        exact hu
    · by_cases hxb : x = b
      · subst x
        by_cases hya : y = a
        · subst y
          exact absurd (hnameb.symm.trans (hxy.trans hnamea)) huv.symm
        by_cases hyb : y = b
        · exact hyb.symm
        · exfalso
          apply havoid ⟨y, hy, hya, hyb⟩
          rw [← hname_inner y hy hya hyb, ← hxy, hnameb]
          exact hv
      · by_cases hya : y = a
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnamea]
          exact hu
        by_cases hyb : y = b
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnameb]
          exact hv
        · have hsub : (⟨x, hx, hxa, hxb⟩ : inner) = ⟨y, hy, hya, hyb⟩ := by
            apply hfresh
            calc
            fresh (⟨x, hx, hxa, hxb⟩ : inner) = name x :=
              (hname_inner x hx hxa hxb).symm
            _ = name y := hxy
            _ = fresh (⟨y, hy, hya, hyb⟩ : inner) := hname_inner y hy hya hyb
          exact congrArg (fun z : inner => z.1) hsub
  · intro x hx hxa hxb
    rw [hname_inner x hx hxa hxb]
    exact havoid ⟨x, hx, hxa, hxb⟩

/-- **An intermediate stage of the transfer.** -/
structure IsPartialTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the old one along `par` — assertion (iv). -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the old one along the *same* parent map. That sharing
  is `lem:refinement-compatibility`(c). -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The evolving source skeleton contains the original source skeleton. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- On the original source skeleton, the evolving skeleton map is still the original map. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The new source skeleton occupies exactly what the current subgraph occupies. -/
  skeletonSet_eq : T.src.skeletonSet = pointSet B Hdraw
  /-- Every vertex of the current subgraph is a 0-cell of the new structure: the new structure
  realizes a subdivision of `B`, so it has at least `B`'s vertices. -/
  vertexSet_subset : V(B) ⊆ V(T.src.graph)

/-! #### The output data of one realized ear

The former `EarStep` interface ended directly in an existential `GeneratedPair`.  That hid all
of the actual constructor data and made the last half of the proof impossible to reuse or
inspect.  `EarStepData` exposes the abstract split, its two geometric crosscuts, and the chosen
map between them.  Its `pair` and `isPartialTransferOf_pair` declarations below perform the
assembly. -/

/-- Complete constructor data for adjoining the geometric path `D` to a partial transfer. -/
structure EarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  /-- The abstract face split, including the freshly named copy of the ear. -/
  splitData : T.str.SplitData
  /-- The source positions and edge parametrizations of that abstract ear. -/
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  /-- The target positions and edge parametrizations. -/
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  /-- Both drawings are crosscuts of the corresponding old face. -/
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  /-- The cellwise homeomorphism used to extend the old skeleton homeomorphism. -/
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
  /-- Every edge of both realized ears is polygonal. -/
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc tgtDraw e)
  /-- The relabelled source ear occupies exactly the path supplied by the ambient graph. -/
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
  /-- Every old or newly introduced graph vertex is a vertex of the new realization. -/
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

namespace EarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- The generated pair assembled from the data of one realized ear. -/
noncomputable def pair (w : EarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : EarStepData T B H Hdraw a D) :
    w.pair.src = w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : EarStepData T B H Hdraw a D) :
    w.pair.tgt = w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

/-- The exposed constructor data really performs one `EarStep`: the pair it builds refines the
original pair along the composite parent map, occupies the enlarged source graph, and contains
all of that graph's vertices as 0-cells. -/
theorem isPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : EarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsPartialTransferOf T P B Hdraw par) :
    IsPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans hT.refines_tgt
  sourceSkeletonSet_subset :=
    hT.sourceSkeletonSet_subset.trans
      (w.splitData.skeletonSet_subset_realize w.srcCrosscut)
  homeo_eqOn := by
    intro x hx
    calc
      w.pair.homeo.toFun x = T.homeo.toFun x :=
        w.splitData.splitHomeo_eqOn
          (g := T.homeo) (hE₁ := w.srcCrosscut) (hE₂ := w.tgtCrosscut)
          (m := w.earHomeo) (hT.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := hT.homeo_eqOn hx
  skeletonSet_eq := by
    change (w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.srcEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).graph)
    exact w.vertexSet_subset

end EarStepData

/-! #### Locating the source face of a graph-theoretic ear -/

/-- A nontrivial graph-theoretic ear determines two abstract endpoint vertices and a unique
source face containing its open arc.  This is the complete source-side input needed to choose
the boundary paths of `SplitData`; in particular `CellsAbsorb` is no longer an extra
hypothesis. -/
theorem exists_source_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.src.pos u = a ∧ T.src.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ srcDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.src.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.src_isCellDecomposition.exists_face_of_ear
      (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

/-- Every edge of a genuine source ear is polygonal.  The source-extension dichotomy allows an
edge to be nonpolygonal only when its whole arc lies in the outer curve.  But that curve is in
the current skeleton, whereas the open ear lies in one current face and hence misses the
skeleton; a nondegenerate drawn edge cannot then remain. -/
theorem source_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F) :
    ∀ e ∈ D, IsPolygonal (edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exfalso
    have houterSkel : srcOuter ⊆ T.src.skeletonSet := by
      intro z hz
      apply T.src.outerSet_subset_skeletonSet
      rw [T.src_isWeaklyAdmissible.outerSet_eq]
      exact hz
    have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
      intro z hz
      by_contra hzpair
      have hzCell : z ∈ T.src.cell F :=
        hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
      have hzSkel : z ∈ T.src.skeletonSet := houterSkel (houter hz)
      exact Set.disjoint_left.1
        (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF) hzCell hzSkel
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
    have harc := hH.isDrawing.edge_isArcBetween hxy
    have hxyne := hH.isDrawing.ne_of_isLink hxy
    rcases harcPair harc.left_mem with rfl | rfl <;>
      rcases harcPair harc.right_mem with rfl | rfl
    · exact hxyne rfl
    · exact harc.not_subset_pair harcPair
    · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
    · exact hxyne rfl
  · exact hpoly.1

/-- **The conclusion of `thm:finite-transfer`(a).** -/
structure IsTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible — "`H` can be transferred to an
  admissible target realization `H'`". -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

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

/-- **Step 1, the common subdivision**, as an interface. -/
def CommonSubdivision (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOf T₀ P K Hdraw par₀

/-- **Step 3, one ear insertion**, as an interface.

The data handed to the step is exactly what `Graph.IsTwoConnected.ear_decomposition` supplies:
the current subgraph `B`, the ear `D` as a path of `H` between two distinct vertices of `B`, and
the freshness of the ear's interior — which is what makes the ear's interior lie in a single
current face, since it is connected and disjoint from the current skeleton.

`Infinite γ` is not decoration: the step consumes fresh cell names, and on a finite `γ` the
statement is false. See the section docstring above. -/
def EarStep [Infinite γ] (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-- The constructive content needed in the nontrivial branch of `EarStep`: for an ear whose
edges are genuinely new, produce the explicit split and its two realized crosscuts.  The
degenerate branch in which the proposed path was already in `B` is handled by
`earStep_of_data`. -/
def EarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par → Nonempty (EarStepData T B H Hdraw a D)

structure SourceEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  splitData : T.str.SplitData
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) → IsPolygonal (Graph.edgeArc srcDraw e)
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

/-- The ambient path is injectively renamed with fresh abstract vertex and edge cells, two more
fresh names become the new faces, and the resulting abstract split is realized on the source. -/
theorem exists_sourceEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsPartialTransferOf T P B Hdraw par → Nonempty (SourceEarStepData T B H Hdraw a D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_source_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv
      hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  letI : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb
        (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let srcPos : γ → Plane := Function.invFunOn vname V(Q)
  let srcDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled srcDraw := by
    exact hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph srcPos = relabelled := by
    change (relabelled.map vname).map srcPos = relabelled
    simpa [srcPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have hsrcSet : d.earSet srcPos srcDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have hsrcEdgeOrig := source_ear_edge_polygonal hH hpath hF hinside
  have hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc srcDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply hsrcEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have hsrcPoly : IsPolygonal (d.earSet srcPos srcDraw) := by
    rw [hsrcSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => hsrcEdgeOrig f (by rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have hsrc : d.EarCrosscut T.src srcPos srcDraw := {
    pos_source := by
      change srcPos u = T.src.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change srcPos v = T.src.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [hsrcSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
    polygonal := hsrcPoly
  }
  refine ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    srcCrosscut := hsrc
    srcEdgePolygonal := hsrcEdgePoly
    srcEarSet_eq := hsrcSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.src srcPos))
  rw [hsrc.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

/-- **`EarStep`, assembled from explicit constructor data.**  This is the end-to-end
bookkeeping theorem: the nontrivial branch is realized by `EarStepData.pair`; if the proposed
ear contains an old edge, `Graph.ear_edges_notMem_or_union_eq` shows that the union did not
change and the current transfer itself is the answer. -/
theorem earStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hbuild : EarStepConstruction P H Hdraw hH) :
    EarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

/-! ### Steps 2 and 3: the induction through the ear sequence -/

/-- **Steps 2 and 3 of the proof of `thm:finite-transfer`.** By `lem:relative-ear` the new finite
2-connected graph is obtained from the old subdivided graph by a finite sequence of ears; each
ear insertion is at most two edge subdivisions plus one 2-cell split, so every intermediate stage
is a generated matched cell structure. Given step 1 and one ear, the whole extension transfers.

The invariant carried through the induction is `IsPartialTransferOf`, which does **not** mention
connectedness of the open nonboundary part: `rem:intermediate-disconnection` says an
intermediate stage may genuinely have it disconnected, and nothing here assumes otherwise. -/
theorem transfer_of_ears_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-! ### `thm:finite-transfer`(a) -/

/-- **`thm:finite-transfer`, direction (a): transfer toward the square.**

Let `(Γ, Γ')` be a generated matched cellulation. Suppose `H` is a finite 2-connected plane graph
containing a subdivision of `Γ`, with outer cycle `C`, with every nonboundary edge polygonal, and
with `|H| ∖ C` connected. Then the common subdivision can be made on `Γ'`, and `H` can be
transferred to an admissible target realization `H'`; the resulting generated matched cellulation
refines the old one by an explicit parent map.

This compatibility form accepts both step interfaces as arguments. `earStep` discharges the
second, while `commonSubdivision` in `CommonSubdivision.lean` discharges the first. -/
theorem finite_transfer_toward_square_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    transfer_of_ears_of_commonSubdivision_of_earStep hH hsub hstep
  -- The final source realization occupies `|H|`, so its open nonboundary part is `|H| ∖ C`,
  -- which the hypothesis on `H` says is connected. Combinatorial invariance moves that to the
  -- target, and both realizations are then admissible.
  have hconn : IsConnected T.src.nonboundary := by
    rw [T.src_nonboundary_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  exact ⟨T, par, hT, T.src_isAdmissible hconn, T.tgt_isAdmissible hconn⟩

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

section TargetEar

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {Q F J P A₁ A₂ : Set Plane} {cells : Set (Set Plane)} {v w : Plane}

/-- A target 2-cell is an open connected set disjoint from the skeleton. Everything the crosscut
construction needs about it, read off the presentation as a component of `Q ∖ |G|`. -/
theorem isOpen_isPreconnected_disjoint_of_target_cell [G.Finite] (h : IsDrawing G drawing)
    (hQ : IsOpen Q)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) :
    IsOpen F ∧ IsPreconnected F ∧ Disjoint F (pointSet G drawing) := by
  obtain ⟨-, z, rfl⟩ := hcell F hF
  have hopen : IsOpen (Q \ pointSet G drawing) := hQ.sdiff h.isClosed_pointSet
  exact ⟨hopen.connectedComponentIn, isPreconnected_connectedComponentIn,
    Set.disjoint_left.2 fun _ hx => (connectedComponentIn_subset _ _ hx).2⟩

/-- **The target crosscut of `thm:finite-transfer`(a), step 4.** Two distinct points of a curve
`J` inside the target skeleton, both in the closure of a target 2-cell `F`, are joined by a
simple polygonal arc lying in `F` apart from its two endpoints and meeting `J` exactly there.

The three inputs are the three the blueprint names: `lem:polygonal-side-accessibility` on the
target side for the accessibility of each endpoint, and `lem:accessible-endpoints` in its
crosscut form for the join. Nothing is assumed. -/
theorem exists_target_crosscut [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} := by
  obtain ⟨hopen, hconn, hdisj⟩ :=
    isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  obtain ⟨ws, -, -, -, hsub, harc, hmeet⟩ :=
    exists_crosscut_of_polyAccessible hopen hconn (hdisj.mono_right hJ) hvw hvJ hwJ
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw)
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub, hmeet⟩

end TargetEar

/-- A face and two distinct boundary vertices of a generated pair admit the target polygonal
crosscut needed by an ear insertion.  All accessibility hypotheses are discharged from the
fields maintained by `GeneratedPair`. -/
theorem GeneratedPair.exists_target_crosscut
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {u v F : γ} (hu : u ∈ V(P.str.skel)) (hv : v ∈ V(P.str.skel))
    (huv : u ≠ v) (hF : F ∈ P.str.faces) (huF : P.str.sub u F)
    (hvF : P.str.sub v F) :
    ∃ A : Set Plane, IsPolygonal A ∧
      IsArcBetween A (P.tgt.pos u) (P.tgt.pos v) ∧
      A \ {P.tgt.pos u, P.tgt.pos v} ⊆ P.tgt.cell F ∧
      A ∩ frontier (P.tgt.cell F) = {P.tgt.pos u, P.tgt.pos v} := by
  have hucl : P.tgt.pos u ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hu) (P.str.mem_cells_of_mem_faces hF) huF
    rw [P.tgt.cell_vertex hu] at hsub
    exact hsub (Set.mem_singleton _)
  have hvcl : P.tgt.pos v ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hv) (P.str.mem_cells_of_mem_faces hF) hvF
    rw [P.tgt.cell_vertex hv] at hsub
    exact hsub (Set.mem_singleton _)
  have huJ : P.tgt.pos u ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hucl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hu)
  have hvJ : P.tgt.pos v ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hvcl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hv)
  letI : (P.str.skel.map P.tgt.pos).Finite := {
    finite_vertexSet := by
      rw [Graph.vertexSet_map]
      exact P.str.finite_vertexSet.image _
    finite_edgeSet := by
      rw [Graph.edgeSet_map]
      exact P.str.finite_edgeSet
  }
  have hcell : ∀ A ∈ {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T},
      A ⊆ tgtDom \ tgtOuter ∧
        ∃ z, A = connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
    rintro A ⟨T, hT, rfl⟩
    exact P.tgt_face_isComponent hT
  have hfaceMem : P.tgt.cell F ∈
      {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T} := ⟨F, hF, rfl⟩
  exact Schoenflies.exists_target_crosscut P.tgt.isDrawing P.tgt_isPolygonal
    P.tgtInterior_isOpen P.tgtInterior_frontier_subset
    hcell hfaceMem
    (P.tgt_isCellDecomposition.frontier_cell_subset_skeletonSet P.tgt_isFaceJordan hF)
    (fun h => huv (P.tgt.injOn_pos hu hv h)) huJ hvJ hucl hvcl

/-! ### Completing the ear step -/

/-- **The constructive ear interface.** The source half is the freshly
renamed path supplied by `exists_sourceEarStepData`; the target half is a polygonal crosscut of
the corresponding face, divided edge-for-edge by `EarCrosscut.exists_matched_target`. -/
theorem earStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    EarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_sourceEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  obtain ⟨A, hApoly, hAarc, hAsub, -⟩ :=
    T.exists_target_crosscut d.source_mem_skel d.target_mem_skel d.source_ne_target
      d.face_mem hsourceSub htargetSub
  obtain ⟨tgtPos, tgtDraw, earHomeo, htgt, htgtEdgePoly⟩ :=
    w.srcCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := w.srcPos
    srcDraw := w.srcDraw
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    srcCrosscut := w.srcCrosscut
    tgtCrosscut := htgt
    earHomeo := earHomeo
    srcEdgePolygonal := w.srcEdgePolygonal
    tgtEdgePolygonal := htgtEdgePoly
    srcEarSet_eq := w.srcEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

/-- **One ear insertion, with no remaining hypothesis.** -/
theorem earStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : EarStep P H Hdraw :=
  earStep_of_data hH (earStepConstruction P H Hdraw hH)

/-- **Finite transfer toward the square from an explicitly supplied common subdivision.** -/
theorem finite_transfer_toward_square_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision_of_earStep hH hsub
    (earStep P H Hdraw hH)

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

section
-- module Solutions.Q146_CD.CommonSubdivision
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.attachUnion_succ _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Common subdivision for finite transfer

This module proves step 1 of finite transfer.  The part of the extension graph supported on the
old source skeleton is extracted as a trace graph.  It is a subdivision of the old skeleton and
remains 2-connected.  Its finitely many vertices are then inserted, one at a time, into both
realizations of the generated pair.  `CellStructure.SubdivData.realizeHomeo` transports every
source subdivision parameter to the matching target edge.

The resulting theorem `Schoenflies.commonSubdivision` discharges the former
`Schoenflies.CommonSubdivision` interface under the same infinite name-supply assumption used by
the ear construction.

## Blueprint

* `Schoenflies.commonSubdivision` — the common-subdivision part of step 1 in the proof of
  `thm:finite-transfer`(a).
* `Schoenflies.finite_transfer_toward_square` — `thm:finite-transfer`(a).
* `Schoenflies.IsPlaneSubdivisionExtension.trace_isTwoConnected` — the trace theorem for two
  arbitrary plane drawings, used when assembling target/mesh overlays.
-/

open Set
open scoped Graph

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {e : β} {x y : Plane}

/-- A finite plane graph with nonempty, preconnected point set is combinatorially connected. -/
theorem connected_of_isPreconnected_pointSet [G.Finite]
    (hdraw : IsDrawing G drawing) (hconn : IsPreconnected (pointSet G drawing))
    (hne : V(G).Nonempty) : G.Connected := by
  refine ⟨hne, fun x hx y hy => ?_⟩
  by_contra hxy
  let A : Graph Plane β := G.induce (G.component x)
  let B : Graph Plane β := G.induce (V(G) \ G.component x)
  have hAle : A ≤ G := G.induce_le component_subset_vertexSet
  have hBle : B ≤ G := G.induce_le Set.sdiff_subset
  letI : A.Finite := Graph.Finite.of_le hAle
  letI : B.Finite := Graph.Finite.of_le hBle
  have hAclosed : IsClosed (pointSet A drawing) := (hdraw.mono hAle).isClosed_pointSet
  have hBclosed : IsClosed (pointSet B drawing) := (hdraw.mono hBle).isClosed_pointSet
  have hcover : pointSet G drawing ⊆ pointSet A drawing ∪ pointSet B drawing := by
    intro z hz
    rcases hz with hzV | hzE
    · by_cases hzC : z ∈ G.component x
      · exact Or.inl (Or.inl hzC)
      · exact Or.inr (Or.inl ⟨hzV, hzC⟩)
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
      by_cases huC : u ∈ G.component x
      · have hvC : v ∈ G.component x := mem_component_of_isLink huC huv
        exact Or.inl (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(A) by
            rw [edgeSet_eq_setOf_exists_isLink]
            exact ⟨u, v, huv, huC, hvC⟩) hze))
      · have hvC : v ∉ G.component x := by
          intro hvC
          exact huC (mem_component_of_isLink hvC huv.symm)
        exact Or.inr (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(B) by
            rw [edgeSet_eq_setOf_exists_isLink]
            exact ⟨u, v, huv, ⟨huv.left_mem, huC⟩, ⟨huv.right_mem, hvC⟩⟩) hze))
  have hAB : Disjoint (pointSet A drawing) (pointSet B drawing) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rcases hzA with hzAV | hzAE <;> rcases hzB with hzBV | hzBE
    · exact hzBV.2 hzAV
    · obtain ⟨e, heB, hze⟩ := Set.mem_iUnion₂.1 hzBE
      rw [edgeSet_eq_setOf_exists_isLink] at heB
      obtain ⟨u, v, huv, huB, hvB⟩ := heB
      have hzinc := hdraw.vertex_mem_edgeArc huv (component_subset_vertexSet hzAV) hze
      rcases hzinc with rfl | rfl
      exacts [huB.2 hzAV, hvB.2 hzAV]
    · obtain ⟨e, heA, hze⟩ := Set.mem_iUnion₂.1 hzAE
      rw [edgeSet_eq_setOf_exists_isLink] at heA
      obtain ⟨u, v, huv, huA, hvA⟩ := heA
      have hzinc := hdraw.vertex_mem_edgeArc huv hzBV.1 hze
      rcases hzinc with rfl | rfl
      exacts [hzBV.2 huA, hzBV.2 hvA]
    · obtain ⟨e, heA, hzeA⟩ := Set.mem_iUnion₂.1 hzAE
      obtain ⟨f, hfB, hzfB⟩ := Set.mem_iUnion₂.1 hzBE
      have heG : e ∈ E(G) := hAle.edgeSet_mono heA
      have hfG : f ∈ E(G) := hBle.edgeSet_mono hfB
      have hef : e ≠ f := by
        intro hef
        subst f
        rw [edgeSet_eq_setOf_exists_isLink] at heA hfB
        obtain ⟨u, v, huv, huA, -⟩ := heA
        obtain ⟨u', v', huv', huB, hvB⟩ := hfB
        rcases huv.left_eq_or_eq huv' with h | h
        · exact huB.2 (h ▸ huA)
        · exact hvB.2 (h ▸ huA)
      obtain ⟨hzV, ⟨u, heu⟩, ⟨v, hfv⟩⟩ :=
        hdraw.edge_inter heG hfG hef hzeA hzfB
      rw [edgeSet_eq_setOf_exists_isLink] at heA hfB
      obtain ⟨a, b, hab, haA, hbA⟩ := heA
      obtain ⟨c, d, hcd, hcB, hdB⟩ := hfB
      rcases heu.left_eq_or_eq hab with rfl | rfl <;>
        rcases hfv.left_eq_or_eq hcd with rfl | rfl
      all_goals first | exact hcB.2 haA | exact hdB.2 haA | exact hcB.2 hbA | exact hdB.2 hbA
  have hdisj : pointSet G drawing ∩ (pointSet A drawing ∩ pointSet B drawing) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hconn
      _ _ hAclosed hBclosed hcover hdisj) with hsub | hsub
  · have hyB : y ∈ pointSet B drawing := Or.inl ⟨hy, hxy⟩
    exact Set.disjoint_left.1 hAB (hsub (Or.inl hy)) hyB
  · have hxA : x ∈ pointSet A drawing := Or.inl (mem_component_self hx)
    exact Set.disjoint_left.1 hAB hxA (hsub (Or.inl hx))

/-- The part of a drawn graph supported on a prescribed set. -/
def traceGraph (G : Graph Plane β) (drawing : β → ℝ → Plane) (A : Set Plane) :
    Graph Plane β :=
  (G.restrict {e | edgeArc drawing e ⊆ A}).induce (V(G) ∩ A)

/-- The vertices retained by a trace graph. -/
@[simp] theorem traceGraph_vertexSet (A : Set Plane) :
    V(traceGraph G drawing A) = V(G) ∩ A := rfl

/-- A trace edge is exactly an ambient edge whose full arc and endpoints lie in the support. -/
@[simp] theorem traceGraph_isLink (A : Set Plane) :
    (traceGraph G drawing A).IsLink e x y ↔
      edgeArc drawing e ⊆ A ∧ G.IsLink e x y ∧ x ∈ A ∧ y ∈ A := by
  simp only [traceGraph, induce_isLink, restrict_isLink, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hsub, hlink⟩, ⟨-, hxA⟩, ⟨-, hyA⟩⟩
    exact ⟨hsub, hlink, hxA, hyA⟩
  · rintro ⟨hsub, hlink, hxA, hyA⟩
    exact ⟨⟨hsub, hlink⟩, ⟨hlink.left_mem, hxA⟩, ⟨hlink.right_mem, hyA⟩⟩

/-- A trace graph is a subgraph of its ambient graph. -/
theorem traceGraph_le (A : Set Plane) : traceGraph G drawing A ≤ G :=
  le_trans (induce_le Set.inter_subset_left) restrict_le

/-- Enlarging the support enlarges the trace graph. -/
theorem traceGraph_mono {A B : Set Plane} (hAB : A ⊆ B) :
    traceGraph G drawing A ≤ traceGraph G drawing B where
  vertexSet_mono := by
    rw [traceGraph_vertexSet, traceGraph_vertexSet]
    exact Set.inter_subset_inter_right _ hAB
  isLink_mono := by
    intro e x y hlink
    rw [traceGraph_isLink] at hlink ⊢
    exact ⟨hlink.1.trans hAB, hlink.2.1, hAB hlink.2.2.1, hAB hlink.2.2.2⟩

/-- The trace graph occupies only its prescribed support. -/
theorem pointSet_traceGraph_subset (A : Set Plane) :
    pointSet (traceGraph G drawing A) drawing ⊆ A := by
  rintro z (hz | hz)
  · exact hz.2
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    rw [edgeSet_eq_setOf_exists_isLink] at he
    obtain ⟨x, y, hxy⟩ := he
    exact (traceGraph_isLink A).1 hxy |>.1 hze

/-- An absorbed subset of a finite drawing is exactly the point set of its trace graph. -/
theorem pointSet_traceGraph_eq (hdraw : IsDrawing G drawing) (A : Set Plane)
    (hsub : A ⊆ pointSet G drawing)
    (habsorb : ∀ ⦃e⦄, e ∈ E(G) →
      (edgeArc drawing e ∩ (A \ V(G))).Nonempty → edgeArc drawing e ⊆ A) :
    pointSet (traceGraph G drawing A) drawing = A := by
  apply Set.Subset.antisymm (pointSet_traceGraph_subset A)
  intro z hzA
  rcases hsub hzA with hzV | hzE
  · exact Or.inl ⟨hzV, hzA⟩
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    by_cases hzVG : z ∈ V(G)
    · exact Or.inl ⟨hzVG, hzA⟩
    · have heA : edgeArc drawing e ⊆ A :=
        habsorb he ⟨z, ⟨hze, hzA, hzVG⟩⟩
      exact Or.inr (Set.mem_iUnion₂_of_mem
        (show e ∈ E(traceGraph G drawing A) by
          rw [edgeSet_eq_setOf_exists_isLink]
          obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
          have harc := hdraw.edge_isArcBetween hxy
          exact ⟨x, y, (traceGraph_isLink A).2
            ⟨heA, hxy, heA harc.left_mem, heA harc.right_mem⟩⟩)
        hze)

/-- A graph vertex lying on a drawn walk is one of the walk's combinatorial vertices. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover_walk (hdraw : IsDrawing G drawing)
    {u v z : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hzV : z ∈ V(G)) (hz : z ∈ edgesCover drawing W) : z ∈ G.walkVertices u W := by
  obtain ⟨e, heW, hze⟩ := mem_edgesCover_iff.1 hz
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (hW.edge_mem heW)
  rcases hdraw.vertex_mem_edgeArc hxy hzV hze with rfl | rfl
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_left⟩
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_right⟩

end Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization}
  {outer dom : Set Plane} {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- An extension edge meeting the interior of the old skeleton is absorbed by that skeleton. -/
theorem trace_absorb (hH : IsSourceExtension R outer dom H Hdraw) :
    ∀ ⦃f⦄, f ∈ E(H) →
      (edgeArc Hdraw f ∩ (R.skeletonSet \ V(H))).Nonempty →
      edgeArc Hdraw f ⊆ R.skeletonSet := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzskel, hznotH⟩ := hmeet
  rcases hzskel with hzV | hzE
  · exact absurd (hH.vertexSet_subset hzV) hznotH
  · obtain ⟨e, heR, hze⟩ := Set.mem_iUnion₂.1 hzE
    have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
    obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
    have hza : z ≠ R.pos a := by
      intro h
      apply hznotH
      rw [h]
      exact hH.vertexSet_subset (by
        rw [R.vertexSet_graph]
        exact ⟨a, hab.left_mem, rfl⟩)
    have hzb : z ≠ R.pos b := by
      intro h
      apply hznotH
      rw [h]
      exact hH.vertexSet_subset (by
        rw [R.vertexSet_graph]
        exact ⟨b, hab.right_mem, rfl⟩)
    exact (hH.edge_subset heS hf ⟨z, hzf, by
      rw [R.cell_edge hab]
      exact ⟨hze, by simp [hza, hzb]⟩, hznotH⟩).trans
        (Graph.edgeArc_subset_pointSet heR)

/-- The extension trace on the old skeleton occupies exactly the old skeleton. -/
theorem trace_pointSet (hH : IsSourceExtension R outer dom H Hdraw) :
    Graph.pointSet (Graph.traceGraph H Hdraw R.skeletonSet) Hdraw = R.skeletonSet :=
  Graph.pointSet_traceGraph_eq hH.isDrawing R.skeletonSet hH.skeletonSet_subset
    (trace_absorb hH)

/-- The trace supported on one old edge occupies that entire edge arc. -/
theorem edge_trace_pointSet (hH : IsSourceExtension R outer dom H Hdraw)
    {e : γ} (he : e ∈ E(S.skel)) :
    Graph.pointSet (Graph.traceGraph H Hdraw (edgeArc R.drawing e)) Hdraw =
      edgeArc R.drawing e := by
  have heR : e ∈ E(R.graph) := by rwa [R.edgeSet_graph]
  refine Graph.pointSet_traceGraph_eq hH.isDrawing _
    ((Graph.edgeArc_subset_pointSet heR).trans hH.skeletonSet_subset) ?_
  intro f hf hmeet
  obtain ⟨z, hzf, hze, hznotH⟩ := hmeet
  obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet he
  have hza : z ≠ R.pos a := by
    intro h
    apply hznotH
    rw [h]
    exact hH.vertexSet_subset (by
      rw [R.vertexSet_graph]
      exact ⟨a, hab.left_mem, rfl⟩)
  have hzb : z ≠ R.pos b := by
    intro h
    apply hznotH
    rw [h]
    exact hH.vertexSet_subset (by
      rw [R.vertexSet_graph]
      exact ⟨b, hab.right_mem, rfl⟩)
  exact hH.edge_subset he hf ⟨z, hzf, by
    rw [R.cell_edge hab]
    exact ⟨hze, by simp [hza, hzb]⟩, hznotH⟩

/-- Every old edge is the drawn carrier of a path in the extension graph. -/
theorem exists_edge_trace (hH : IsSourceExtension R outer dom H Hdraw)
    {e a b : γ} (hab : S.skel.IsLink e a b) :
    ∃ D : List γ, H.IsPath (R.pos a) D (R.pos b) ∧
      Graph.edgesCover Hdraw D = edgeArc R.drawing e := by
  let K := Graph.traceGraph H Hdraw (edgeArc R.drawing e)
  have hKle : K ≤ H := Graph.traceGraph_le _
  letI : H.Finite := hH.finite
  letI : K.Finite := Graph.Finite.of_le hKle
  have hpoint : pointSet K Hdraw = edgeArc R.drawing e :=
    edge_trace_pointSet hH hab.edge_mem
  have haH : R.pos a ∈ V(H) := hH.vertexSet_subset (by
    rw [R.vertexSet_graph]
    exact ⟨a, hab.left_mem, rfl⟩)
  have hbH : R.pos b ∈ V(H) := hH.vertexSet_subset (by
    rw [R.vertexSet_graph]
    exact ⟨b, hab.right_mem, rfl⟩)
  have hOldArc := R.isDrawing.edge_isArcBetween (hab.map R.pos)
  have haK : R.pos a ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haH, hOldArc.left_mem⟩
  have hbK : R.pos b ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbH, hOldArc.right_mem⟩
  have hKconn : K.Connected := Graph.connected_of_isPreconnected_pointSet
    (hH.isDrawing.mono hKle) (hpoint.symm ▸ hOldArc.isArc.isConnected.isPreconnected)
    ⟨R.pos a, haK⟩
  obtain ⟨D, hD⟩ := (hKconn.reaches haK hbK).exists_isPath
  have hDH : H.IsPath (R.pos a) D (R.pos b) := hD.mono hKle
  have hne : R.pos a ≠ R.pos b := R.isDrawing.ne_of_isLink (hab.map R.pos)
  have hPathArc : IsArcBetween (Graph.edgesCover Hdraw D) (R.pos a) (R.pos b) :=
    hH.isDrawing.path_isArcBetween hDH (hDH.ne_nil hne)
  have hcoverSub : Graph.edgesCover Hdraw D ⊆ edgeArc R.drawing e := by
    rw [← hpoint]
    exact Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDH, hPathArc.eq_of_subset_arc hOldArc hOldArc hcoverSub
    (Set.Subset.rfl)⟩

/-- The path tracing an old edge is contained in the trace supported on that edge. -/
theorem pathGraph_edge_trace_le (hH : IsSourceExtension R outer dom H Hdraw)
    {e a b : γ} (hab : S.skel.IsLink e a b) {D : List γ}
    (hD : H.IsPath (R.pos a) D (R.pos b))
    (hcover : Graph.edgesCover Hdraw D = edgeArc R.drawing e) :
    H.pathGraphOf (R.pos a) D ≤
      Graph.traceGraph H Hdraw (edgeArc R.drawing e) := by
  have hne : R.pos a ≠ R.pos b := R.isDrawing.ne_of_isLink (hab.map R.pos)
  have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
      Graph.edgesCover Hdraw D :=
    hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
  have hPle : H.pathGraphOf (R.pos a) D ≤ H := Graph.pathGraphOf_le hD.isWalk
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hPle.vertexSet_mono hz, hcover ▸ hPpoint ▸ (Or.inl hz)⟩
  · intro f x y hlink
    have hfP : f ∈ E(H.pathGraphOf (R.pos a) D) := hlink.edge_mem
    have hfD : f ∈ D := by
      rwa [Graph.pathGraphOf_edgeSet hD.isWalk] at hfP
    have hlinkH : H.IsLink f x y := hPle.isLink_mono hlink
    have hsub : edgeArc Hdraw f ⊆ edgeArc R.drawing e := by
      rw [← hcover]
      exact fun z hz => Graph.mem_edgesCover hfD hz
    have harc := hH.isDrawing.edge_isArcBetween hlinkH
    exact (Graph.traceGraph_isLink _).2
      ⟨hsub, hlinkH, hsub harc.left_mem, hsub harc.right_mem⟩

/-- Every old skeleton vertex belongs to the full skeleton trace. -/
theorem old_vertex_mem_trace (hH : IsSourceExtension R outer dom H Hdraw)
    {a : γ} (ha : a ∈ V(S.skel)) :
    R.pos a ∈ V(Graph.traceGraph H Hdraw R.skeletonSet) := by
  rw [Graph.traceGraph_vertexSet]
  exact ⟨hH.vertexSet_subset (by rw [R.vertexSet_graph]; exact ⟨a, ha, rfl⟩),
    R.pos_mem_skeletonSet ha⟩

/-- An old skeleton walk expands to a reachability witness in the extension trace. -/
theorem reaches_trace_of_isWalk (hH : IsSourceExtension R outer dom H Hdraw)
    {a b : γ} {W : List γ} (hW : S.skel.IsWalk a W b) :
    (Graph.traceGraph H Hdraw R.skeletonSet).Reaches (R.pos a) (R.pos b) := by
  induction hW with
  | nil ha => exact .refl (old_vertex_mem_trace hH ha)
  | @cons a w b e W hlink htail ih =>
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlink
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlink hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlink.edge_mem)))
    have hreach : (H.pathGraphOf (R.pos a) D).Reaches (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk⟩
    exact (hreach.mono hPle).trans ih

/-- Any two old vertices are joined inside the extension trace. -/
theorem old_vertices_reach_trace (hH : IsSourceExtension R outer dom H Hdraw)
    (hR2 : R.graph.IsTwoConnected) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel)) :
    (Graph.traceGraph H Hdraw R.skeletonSet).Reaches (R.pos a) (R.pos b) := by
  have hS2 : S.skel.IsTwoConnected :=
    (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR2
  obtain ⟨W, hW⟩ := hS2.connected.reaches ha hb
  exact reaches_trace_of_isWalk hH hW

/-- Every trace vertex reaches an old skeleton vertex. -/
theorem exists_reaches_old_vertex (hH : IsSourceExtension R outer dom H Hdraw)
    {x : Plane} (hx : x ∈ V(Graph.traceGraph H Hdraw R.skeletonSet)) :
    ∃ a ∈ V(S.skel),
      (Graph.traceGraph H Hdraw R.skeletonSet).Reaches x (R.pos a) := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(R.graph)
  · rw [R.vertexSet_graph] at hxold
    obtain ⟨a, ha, rfl⟩ := hxold
    exact ⟨a, ha, .refl (old_vertex_mem_trace hH ha)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, heR, hxe⟩ := Set.mem_iUnion₂.1 hxE
      have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
      obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
      obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hab
      have hxwalk : x ∈ H.walkVertices (R.pos a) D :=
        hH.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(H.pathGraphOf (R.pos a) D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : H.pathGraphOf (R.pos a) D ≤
          Graph.traceGraph H Hdraw R.skeletonSet :=
        (pathGraph_edge_trace_le hH hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet heR))
      have haP : R.pos a ∈ V(H.pathGraphOf (R.pos a) D) :=
        Graph.mem_vertexSet_pathGraphOf_self
      exact ⟨a, hab.left_mem,
        ((hD.isPathGraph_pathGraphOf.connected.reaches hxP haP).mono hPle)⟩

/-- After deleting a distinct trace vertex, every remaining vertex still reaches an old one. -/
theorem exists_reaches_old_vertex_delete
    (hH : IsSourceExtension R outer dom H Hdraw) {c x : Plane}
    (hx : x ∈ V(Graph.traceGraph H Hdraw R.skeletonSet)) (hxc : x ≠ c) :
    ∃ a ∈ V(S.skel),
      ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {c}).Reaches x (R.pos a) := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(R.graph)
  · rw [R.vertexSet_graph] at hxold
    obtain ⟨a, ha, rfl⟩ := hxold
    exact ⟨a, ha, .refl (Graph.mem_deleteVerts_singleton_of_ne
      (old_vertex_mem_trace hH ha) hxc)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, heR, hxe⟩ := Set.mem_iUnion₂.1 hxE
      have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
      obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
      obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hab
      have hxwalk : x ∈ H.walkVertices (R.pos a) D :=
        hH.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(H.pathGraphOf (R.pos a) D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : H.pathGraphOf (R.pos a) D ≤
          Graph.traceGraph H Hdraw R.skeletonSet :=
        (pathGraph_edge_trace_le hH hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet heR))
      rcases hD.isPathGraph_pathGraphOf.reaches_an_end hxP hxc with hreach | hreach
      · exact ⟨a, hab.left_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩
      · exact ⟨b, hab.right_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩

/-- An old walk avoiding a vertex expands to a trace walk avoiding its realized point. -/
theorem reaches_trace_delete_of_deleteVerts_isWalk
    (hH : IsSourceExtension R outer dom H Hdraw)
    {z a b : γ} {W : List γ}
    (hzS : z ∈ V(S.skel))
    (hW : (S.skel.deleteVerts {z}).IsWalk a W b) :
    ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {R.pos z}).Reaches
      (R.pos a) (R.pos b) := by
  induction hW with
  | nil ha =>
      rw [Graph.mem_deleteVerts_singleton] at ha
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (old_vertex_mem_trace hH ha.1) (fun h => ha.2 (by
          simpa using R.injOn_pos ha.1 hzS h)))
  | @cons a w b e W hlink htail ih =>
    rw [Graph.deleteVerts_isLink] at hlink
    have hlinkS := hlink.1
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlinkS
    have hne : R.pos a ≠ R.pos w := R.isDrawing.ne_of_isLink (hlinkS.map R.pos)
    have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
        Graph.edgesCover Hdraw D :=
      hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hznot : R.pos z ∉ H.walkVertices (R.pos a) D := by
      intro hz
      have hzarc : R.pos z ∈ edgeArc R.drawing e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      have hzV : R.pos z ∈ V(R.graph) := by
        rw [R.vertexSet_graph]
        exact ⟨z, hzS, rfl⟩
      rcases R.isDrawing.vertex_mem_edgeArc (hlinkS.map R.pos) hzV hzarc with hza | hzw
      · have haz : a ≠ z := by simpa using hlink.2.1
        exact haz (R.injOn_pos hlinkS.left_mem hzS hza.symm)
      · have hwz : w ≠ z := by simpa using hlink.2.2
        exact hwz (R.injOn_pos hlinkS.right_mem hzS hzw.symm)
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlinkS hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlinkS.edge_mem)))
    have hreach : ((H.pathGraphOf (R.pos a) D).deleteVerts {R.pos z}).Reaches
        (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hznot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- An old walk avoiding an edge expands to a trace walk avoiding an interior point of it. -/
theorem reaches_trace_delete_of_deleteEdges_isWalk
    (hH : IsSourceExtension R outer dom H Hdraw)
    {c : Plane} (hcold : c ∉ V(R.graph))
    {e₀ : γ} (he₀ : e₀ ∈ E(S.skel)) (hce₀ : c ∈ edgeArc R.drawing e₀)
    {a b : γ} {W : List γ}
    (hW : (S.skel.deleteEdges {e₀}).IsWalk a W b) :
    ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {c}).Reaches
      (R.pos a) (R.pos b) := by
  induction hW with
  | @nil x hx =>
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (old_vertex_mem_trace hH (by simpa using hx)) (fun h => hcold (by
          rw [R.vertexSet_graph]
          exact ⟨x, by simpa using hx, h⟩)))
  | @cons a w b e W hlink htail ih =>
    change S.skel.IsLink e a w ∧ e ∉ ({e₀} : Set γ) at hlink
    have hlinkS := hlink.1
    have hee₀ : e ≠ e₀ := by simpa using hlink.2
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlinkS
    have hne : R.pos a ≠ R.pos w := R.isDrawing.ne_of_isLink (hlinkS.map R.pos)
    have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
        Graph.edgesCover Hdraw D :=
      hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hcnot : c ∉ H.walkVertices (R.pos a) D := by
      intro hc
      have hce : c ∈ edgeArc R.drawing e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      exact hcold (R.isDrawing.edge_inter he₀ hlinkS.edge_mem (Ne.symm hee₀)
        hce₀ hce |>.1)
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlinkS hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlinkS.edge_mem)))
    have hreach : ((H.pathGraphOf (R.pos a) D).deleteVerts {c}).Reaches
        (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hcnot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- The part of an extension graph supported on a 2-connected old skeleton is 2-connected. -/
theorem trace_isTwoConnected
    (hH : IsSourceExtension R outer dom H Hdraw)
    (hR2 : R.graph.IsTwoConnected) :
    (Graph.traceGraph H Hdraw R.skeletonSet).IsTwoConnected := by
  let K := Graph.traceGraph H Hdraw R.skeletonSet
  have hS2 : S.skel.IsTwoConnected :=
    (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR2
  have hVold : V(R.graph) ⊆ V(K) := by
    rw [R.vertexSet_graph]
    rintro x ⟨a, ha, rfl⟩
    exact old_vertex_mem_trace hH ha
  refine {
    hasThreeVertices := hR2.hasThreeVertices.mono hVold
    connected := ?_
    deleteVerts_connected := ?_
  }
  · obtain ⟨a, ha⟩ := hS2.connected.nonempty
    refine Graph.Connected.of_hub (old_vertex_mem_trace hH ha) ?_
    intro x hx
    obtain ⟨b, hb, hxb⟩ := exists_reaches_old_vertex hH hx
    exact (old_vertices_reach_trace hH hR2 ha hb).trans hxb.symm
  · intro c hcK
    obtain ⟨p, hpR, hpc, -⟩ := hR2.hasThreeVertices.exists_ne_ne c c
    have hpK : p ∈ V(K) := hVold hpR
    have hpDel : p ∈ V(K.deleteVerts {c}) :=
      Graph.mem_deleteVerts_singleton_of_ne hpK hpc
    refine Graph.Connected.of_hub hpDel ?_
    intro x hx
    rw [Graph.mem_deleteVerts_singleton] at hx
    obtain ⟨a, ha, hxa⟩ := exists_reaches_old_vertex_delete hH hx.1 hx.2
    obtain ⟨b, hb, hpb⟩ := exists_reaches_old_vertex_delete hH hpK hpc
    have habReach : (K.deleteVerts {c}).Reaches (R.pos a) (R.pos b) := by
      by_cases hcold : c ∈ V(R.graph)
      · rw [R.vertexSet_graph] at hcold
        obtain ⟨z, hzS, hzc⟩ := hcold
        have haDel := hxa.right_mem
        have hbDel := hpb.right_mem
        rw [Graph.mem_deleteVerts_singleton] at haDel hbDel
        have haz : a ≠ z := by
          intro h
          apply haDel.2
          rw [h, hzc]
        have hbz : b ≠ z := by
          intro h
          apply hbDel.2
          rw [h, hzc]
        have haSdel : a ∈ V(S.skel.deleteVerts {z}) :=
          Graph.mem_deleteVerts_singleton_of_ne ha haz
        have hbSdel : b ∈ V(S.skel.deleteVerts {z}) :=
          Graph.mem_deleteVerts_singleton_of_ne hb hbz
        obtain ⟨W, hW⟩ := (hS2.deleteVerts_connected hzS).reaches haSdel hbSdel
        simpa [hzc] using reaches_trace_delete_of_deleteVerts_isWalk hH hzS hW
      · have hcskel : c ∈ R.skeletonSet := by
          rw [Graph.traceGraph_vertexSet] at hcK
          exact hcK.2
        rcases hcskel with hcV | hcE
        · exact absurd hcV hcold
        · obtain ⟨e₀, he₀R, hce₀⟩ := Set.mem_iUnion₂.1 hcE
          have he₀ : e₀ ∈ E(S.skel) := by rwa [R.edgeSet_graph] at he₀R
          obtain ⟨u, v, huv⟩ := S.skel.exists_isLink_of_mem_edgeSet he₀
          have hcyc : S.skel.LiesOnCycle e₀ :=
            (Graph.liesOnCycle_iff_deleteEdges_reaches huv).2 (hS2.no_bridge huv)
          have hdel : (S.skel.deleteEdges {e₀}).Connected :=
            hS2.connected.deleteEdges_singleton hcyc
          have haDel : a ∈ V(S.skel.deleteEdges {e₀}) := by simpa using ha
          have hbDel : b ∈ V(S.skel.deleteEdges {e₀}) := by simpa using hb
          obtain ⟨W, hW⟩ := hdel.reaches haDel hbDel
          exact reaches_trace_delete_of_deleteEdges_isWalk hH hcold he₀ hce₀ hW
    exact hpb.trans (habReach.symm.trans hxa.symm)

/-! ## Traces of arbitrary plane subdivisions

The preceding result is phrased for a realized cell structure because that is the interface
used by finite transfer.  Overlay assembly also needs the same fact for an ordinary plane
graph, notably the anchored square mesh.  The proof only uses the local subdivision data
recorded below; in particular it does not use 2-connectivity of the ambient graph. -/

variable {β δ : Type*} {G : Graph Plane β} {Gdraw : β → ℝ → Plane}
  {K : Graph Plane δ} {Kdraw : δ → ℝ → Plane}

/-- The local data saying that `K` contains an edge subdivision of the drawn plane graph `G`.
Crossings with other parts of `K` are allowed at vertices of `K`. -/
structure IsPlaneSubdivisionExtension (G : Graph Plane β) (Gdraw : β → ℝ → Plane)
    (K : Graph Plane δ) (Kdraw : δ → ℝ → Plane) : Prop where
  /-- The ambient graph is finite. -/
  finite : K.Finite
  /-- The old graph is drawn in the plane. -/
  oldIsDrawing : G.IsDrawing Gdraw
  /-- The ambient graph is drawn in the plane. -/
  isDrawing : K.IsDrawing Kdraw
  /-- Every old vertex is an ambient vertex. -/
  vertexSet_subset : V(G) ⊆ V(K)
  /-- The old carrier lies in the ambient carrier. -/
  pointSet_subset : pointSet G Gdraw ⊆ pointSet K Kdraw
  /-- An ambient edge meeting an old edge away from ambient vertices is contained in that old
  edge. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(G) → ∀ ⦃f⦄, f ∈ E(K) →
    (edgeArc Kdraw f ∩ (edgeArc Gdraw e \ V(K))).Nonempty →
      edgeArc Kdraw f ⊆ edgeArc Gdraw e

namespace IsPlaneSubdivisionExtension

/-- The trace supported on one old edge occupies the entire old edge. -/
theorem edge_trace_pointSet (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} (he : e ∈ E(G)) :
    pointSet (Graph.traceGraph K Kdraw (edgeArc Gdraw e)) Kdraw = edgeArc Gdraw e := by
  refine Graph.pointSet_traceGraph_eq h.isDrawing _
    ((Graph.edgeArc_subset_pointSet he).trans h.pointSet_subset) ?_
  intro f hf hmeet
  exact h.edge_subset he hf hmeet

/-- Every old edge is the carrier of an ambient path. -/
theorem exists_edge_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} {a b : Plane} (hab : G.IsLink e a b) :
    ∃ D : List δ, K.IsPath a D b ∧ edgesCover Kdraw D = edgeArc Gdraw e := by
  let T := Graph.traceGraph K Kdraw (edgeArc Gdraw e)
  have hTK : T ≤ K := Graph.traceGraph_le _
  letI : K.Finite := h.finite
  letI : T.Finite := Graph.Finite.of_le hTK
  have hpoint : pointSet T Kdraw = edgeArc Gdraw e := h.edge_trace_pointSet hab.edge_mem
  have haK : a ∈ V(K) := h.vertexSet_subset hab.left_mem
  have hbK : b ∈ V(K) := h.vertexSet_subset hab.right_mem
  have hOldArc := h.oldIsDrawing.edge_isArcBetween hab
  have haT : a ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haK, hOldArc.left_mem⟩
  have hbT : b ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbK, hOldArc.right_mem⟩
  have hTconn : T.Connected := Graph.connected_of_isPreconnected_pointSet
    (h.isDrawing.mono hTK) (hpoint.symm ▸ hOldArc.isArc.isConnected.isPreconnected) ⟨a, haT⟩
  obtain ⟨D, hD⟩ := (hTconn.reaches haT hbT).exists_isPath
  have hDK : K.IsPath a D b := hD.mono hTK
  have hne : a ≠ b := h.oldIsDrawing.ne_of_isLink hab
  have hPathArc : IsArcBetween (edgesCover Kdraw D) a b :=
    h.isDrawing.path_isArcBetween hDK (hDK.ne_nil hne)
  have hcoverSub : edgesCover Kdraw D ⊆ edgeArc Gdraw e := by
    rw [← hpoint]
    exact Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDK, hPathArc.eq_of_subset_arc hOldArc hOldArc hcoverSub Set.Subset.rfl⟩

/-- The path tracing an old edge lies in the trace supported on that edge. -/
theorem pathGraph_edge_trace_le (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} {a b : Plane} (hab : G.IsLink e a b) {D : List δ}
    (hD : K.IsPath a D b) (hcover : edgesCover Kdraw D = edgeArc Gdraw e) :
    K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (edgeArc Gdraw e) := by
  have hne : a ≠ b := h.oldIsDrawing.ne_of_isLink hab
  have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
    h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
  have hPK : K.pathGraphOf a D ≤ K := Graph.pathGraphOf_le hD.isWalk
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hPK.vertexSet_mono hz, hcover ▸ hPpoint ▸ Or.inl hz⟩
  · intro f x y hlink
    have hfP : f ∈ E(K.pathGraphOf a D) := hlink.edge_mem
    have hfD : f ∈ D := by
      rwa [Graph.pathGraphOf_edgeSet hD.isWalk] at hfP
    have hlinkK : K.IsLink f x y := hPK.isLink_mono hlink
    have hsub : edgeArc Kdraw f ⊆ edgeArc Gdraw e := by
      rw [← hcover]
      exact fun z hz => Graph.mem_edgesCover hfD hz
    have harc := h.isDrawing.edge_isArcBetween hlinkK
    exact (Graph.traceGraph_isLink _).2
      ⟨hsub, hlinkK, hsub harc.left_mem, hsub harc.right_mem⟩

/-- Every old vertex belongs to the full old-carrier trace. -/
theorem old_vertex_mem_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {a : Plane} (ha : a ∈ V(G)) :
    a ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw)) := by
  rw [Graph.traceGraph_vertexSet]
  exact ⟨h.vertexSet_subset ha, Or.inl ha⟩

/-- An old walk expands to reachability in the ambient trace. -/
theorem reaches_trace_of_isWalk (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {a b : Plane} {W : List β} (hW : G.IsWalk a W b) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches a b := by
  induction hW with
  | nil ha => exact .refl (h.old_vertex_mem_trace ha)
  | @cons a w b e W hlink htail ih =>
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlink
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlink hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlink.edge_mem))
    have hreach : (K.pathGraphOf a D).Reaches a w := ⟨D, hD.pathGraphOf.isWalk⟩
    exact (hreach.mono hPle).trans ih

/-- Any two old vertices are joined inside the ambient trace. -/
theorem old_vertices_reach_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    (hG2 : G.IsTwoConnected) {a b : Plane} (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches a b := by
  obtain ⟨W, hW⟩ := hG2.connected.reaches ha hb
  exact h.reaches_trace_of_isWalk hW

/-- Every trace vertex reaches an old vertex. -/
theorem exists_reaches_old_vertex (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {x : Plane} (hx : x ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw))) :
    ∃ a ∈ V(G), (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches x a := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(G)
  · exact ⟨x, hxold, .refl (h.old_vertex_mem_trace hxold)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
      obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hab
      have hxwalk : x ∈ K.walkVertices a D :=
        h.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(K.pathGraphOf a D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
        (h.pathGraph_edge_trace_le hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet he))
      have haP : a ∈ V(K.pathGraphOf a D) := Graph.mem_vertexSet_pathGraphOf_self
      exact ⟨a, hab.left_mem,
        (hD.isPathGraph_pathGraphOf.connected.reaches hxP haP).mono hPle⟩

/-- After deleting a distinct trace vertex, every remaining vertex still reaches an old one. -/
theorem exists_reaches_old_vertex_delete
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw) {c x : Plane}
    (hx : x ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw))) (hxc : x ≠ c) :
    ∃ a ∈ V(G),
      ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {c}).Reaches x a := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(G)
  · exact ⟨x, hxold, .refl (Graph.mem_deleteVerts_singleton_of_ne
      (h.old_vertex_mem_trace hxold) hxc)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
      obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hab
      have hxwalk : x ∈ K.walkVertices a D :=
        h.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(K.pathGraphOf a D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
        (h.pathGraph_edge_trace_le hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet he))
      rcases hD.isPathGraph_pathGraphOf.reaches_an_end hxP hxc with hreach | hreach
      · exact ⟨a, hab.left_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩
      · exact ⟨b, hab.right_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩

/-- An old walk avoiding a vertex expands to a trace walk avoiding that vertex. -/
theorem reaches_trace_delete_of_deleteVerts_isWalk
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {z a b : Plane} {W : List β} (hzG : z ∈ V(G))
    (hW : (G.deleteVerts {z}).IsWalk a W b) :
    ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {z}).Reaches a b := by
  induction hW with
  | nil ha =>
      rw [Graph.mem_deleteVerts_singleton] at ha
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (h.old_vertex_mem_trace ha.1) ha.2)
  | @cons a w b e W hlink htail ih =>
    rw [Graph.deleteVerts_isLink] at hlink
    have hlinkG := hlink.1
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlinkG
    have hne : a ≠ w := h.oldIsDrawing.ne_of_isLink hlinkG
    have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
      h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hznot : z ∉ K.walkVertices a D := by
      intro hz
      have hzarc : z ∈ edgeArc Gdraw e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      rcases h.oldIsDrawing.vertex_mem_edgeArc hlinkG hzG hzarc with hza | hzw
      · exact hlink.2.1 hza.symm
      · exact hlink.2.2 hzw.symm
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlinkG hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlinkG.edge_mem))
    have hreach : ((K.pathGraphOf a D).deleteVerts {z}).Reaches a w :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hznot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- An old walk avoiding an edge expands to a trace walk avoiding an interior point of it. -/
theorem reaches_trace_delete_of_deleteEdges_isWalk
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {c : Plane} (hcold : c ∉ V(G)) {e₀ : β} (he₀ : e₀ ∈ E(G))
    (hce₀ : c ∈ edgeArc Gdraw e₀) {a b : Plane} {W : List β}
    (hW : (G.deleteEdges {e₀}).IsWalk a W b) :
    ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {c}).Reaches a b := by
  induction hW with
  | @nil x hx =>
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (h.old_vertex_mem_trace (by simpa using hx)) (fun hxc => hcold (hxc ▸ by simpa using hx)))
  | @cons a w b e W hlink htail ih =>
    change G.IsLink e a w ∧ e ∉ ({e₀} : Set β) at hlink
    have hlinkG := hlink.1
    have hee₀ : e ≠ e₀ := by simpa using hlink.2
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlinkG
    have hne : a ≠ w := h.oldIsDrawing.ne_of_isLink hlinkG
    have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
      h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hcnot : c ∉ K.walkVertices a D := by
      intro hc
      have hce : c ∈ edgeArc Gdraw e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      exact hcold (h.oldIsDrawing.edge_inter he₀ hlinkG.edge_mem (Ne.symm hee₀)
        hce₀ hce |>.1)
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlinkG hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlinkG.edge_mem))
    have hreach : ((K.pathGraphOf a D).deleteVerts {c}).Reaches a w :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hcnot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- The part of an ambient plane graph supported on a 2-connected old graph is 2-connected.
No connectivity assumption on the ambient graph is needed. -/
theorem trace_isTwoConnected (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    (hG2 : G.IsTwoConnected) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).IsTwoConnected := by
  let T := Graph.traceGraph K Kdraw (pointSet G Gdraw)
  have hVold : V(G) ⊆ V(T) := fun _ hz => h.old_vertex_mem_trace hz
  have hthree : T.HasThreeVertices := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hG2.hasThreeVertices
    exact ⟨a, hVold ha, b, hVold hb, c, hVold hc, hab, hac, hbc⟩
  refine {
    hasThreeVertices := hthree
    connected := ?_
    deleteVerts_connected := ?_
  }
  · obtain ⟨a, ha⟩ := hG2.connected.nonempty
    refine Graph.Connected.of_hub (h.old_vertex_mem_trace ha) ?_
    intro x hx
    obtain ⟨b, hb, hxb⟩ := h.exists_reaches_old_vertex hx
    exact (h.old_vertices_reach_trace hG2 ha hb).trans hxb.symm
  · intro c hcT
    obtain ⟨p, hpG, hpc, -⟩ := hG2.hasThreeVertices.exists_ne_ne c c
    have hpT : p ∈ V(T) := hVold hpG
    have hpDel : p ∈ V(T.deleteVerts {c}) :=
      Graph.mem_deleteVerts_singleton_of_ne hpT hpc
    refine Graph.Connected.of_hub hpDel ?_
    intro x hx
    rw [Graph.mem_deleteVerts_singleton] at hx
    obtain ⟨a, ha, hxa⟩ := h.exists_reaches_old_vertex_delete hx.1 hx.2
    obtain ⟨b, hb, hpb⟩ := h.exists_reaches_old_vertex_delete hpT hpc
    have habReach : (T.deleteVerts {c}).Reaches a b := by
      by_cases hcold : c ∈ V(G)
      · have haDel := hxa.right_mem
        have hbDel := hpb.right_mem
        rw [Graph.mem_deleteVerts_singleton] at haDel hbDel
        have hac : a ≠ c := haDel.2
        have hbc : b ≠ c := hbDel.2
        have haGdel : a ∈ V(G.deleteVerts {c}) :=
          Graph.mem_deleteVerts_singleton_of_ne ha hac
        have hbGdel : b ∈ V(G.deleteVerts {c}) :=
          Graph.mem_deleteVerts_singleton_of_ne hb hbc
        obtain ⟨W, hW⟩ := (hG2.deleteVerts_connected hcold).reaches haGdel hbGdel
        exact h.reaches_trace_delete_of_deleteVerts_isWalk hcold hW
      · have hcpoint : c ∈ pointSet G Gdraw := by
          rw [Graph.traceGraph_vertexSet] at hcT
          exact hcT.2
        rcases hcpoint with hcV | hcE
        · exact absurd hcV hcold
        · obtain ⟨e₀, he₀, hce₀⟩ := Set.mem_iUnion₂.1 hcE
          obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he₀
          have hcyc : G.LiesOnCycle e₀ :=
            (Graph.liesOnCycle_iff_deleteEdges_reaches huv).2 (hG2.no_bridge huv)
          have hdel : (G.deleteEdges {e₀}).Connected :=
            hG2.connected.deleteEdges_singleton hcyc
          have haDel : a ∈ V(G.deleteEdges {e₀}) := by simpa using ha
          have hbDel : b ∈ V(G.deleteEdges {e₀}) := by simpa using hb
          obtain ⟨W, hW⟩ := hdel.reaches haDel hbDel
          exact h.reaches_trace_delete_of_deleteEdges_isWalk hcold he₀ hce₀ hW
    exact hpb.trans (habReach.symm.trans hxa.symm)

end IsPlaneSubdivisionExtension

end Schoenflies

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- Replace every occurrence of a distinguished edge in a walk by its two-edge subdivision. -/
theorem exists_substWalk_raw {edge left right newEdge₁ newEdge₂ u v : γ}
    {W : List γ} (hl : S.skel.IsLink edge left right)
    (h : S.skel.IsWalk u W v) :
    ∃ W', CellStructure.SubstWalk S edge left right newEdge₁ newEdge₂ u W W' := by
  induction h with
  | nil hx => exact ⟨[], .nil _⟩
  | @cons a w b f W hfw _ ih =>
    obtain ⟨W', hW'⟩ := ih
    by_cases hf : f = edge
    · subst hf
      rcases hl.eq_and_eq_or_eq_and_eq hfw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · subst h₁; subst h₂; exact ⟨_, .forward hW'⟩
      · subst h₁; subst h₂; exact ⟨_, .backward hW'⟩
    · exact ⟨_, .other hfw hf hW'⟩

/-- Build subdivision data for an edge from three pairwise distinct fresh cell names. -/
theorem exists_subdivData (hcycles : S.BoundaryCycles)
    {edge left right newVertex newEdge₁ newEdge₂ : γ}
    (hl : S.skel.IsLink edge left right)
    (hv : newVertex ∉ S.cells) (he₁ : newEdge₁ ∉ S.cells)
    (he₂ : newEdge₂ ∉ S.cells) (hv₁ : newVertex ≠ newEdge₁)
    (hv₂ : newVertex ≠ newEdge₂) (he₁₂ : newEdge₁ ≠ newEdge₂) :
    ∃ d : S.SubdivData, d.edge = edge ∧ d.left = left ∧ d.right = right ∧
      d.newVertex = newVertex ∧ d.newEdge₁ = newEdge₁ ∧ d.newEdge₂ = newEdge₂ := by
  classical
  have hex : ∀ F : γ, ∃ W' : List γ, F ∈ S.faces → ∃ u,
      S.skel.IsWalk u (S.boundary F) u ∧
        CellStructure.SubstWalk S edge left right newEdge₁ newEdge₂ u
          (S.boundary F) W' := by
    intro F
    by_cases hF : F ∈ S.faces
    · let c := hcycles.faceCycle F hF
      obtain ⟨W', hW'⟩ := exists_substWalk_raw hl c.isWalk
      exact ⟨W', fun _ => ⟨c.target, c.isWalk, hW'⟩⟩
    · exact ⟨[], fun h => (hF h).elim⟩
  choose newBoundary hnewBoundary using hex
  let d : S.SubdivData := {
    edge := edge
    left := left
    right := right
    newVertex := newVertex
    newEdge₁ := newEdge₁
    newEdge₂ := newEdge₂
    isLink := hl
    newVertex_notMem := hv
    newEdge₁_notMem := he₁
    newEdge₂_notMem := he₂
    newVertex_ne₁ := hv₁
    newVertex_ne₂ := hv₂
    newEdge_ne := he₁₂
    newBoundary := newBoundary
    boundary_subst := by
      intro F hF
      exact hnewBoundary F hF
  }
  exact ⟨d, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace SubdivData

/-- Subdividing one edge of a 2-connected skeleton preserves 2-connectivity. -/
theorem skeleton_isTwoConnected {d : S.SubdivData}
    (hS2 : S.skel.IsTwoConnected) (hlr : d.left ≠ d.right) :
    d.skeleton.IsTwoConnected := by
  have htail : d.skeleton.IsPath d.newVertex [d.newEdge₂] d.right :=
    .single d.isLink_newEdge₂ (fun h => d.newVertex_notMem (h ▸ d.right_mem_cells))
  have hfresh : d.left ∉ d.skeleton.walkVertices d.newVertex [d.newEdge₂] := by
    intro h
    rw [Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil] at h
    rcases h with h | h
    · exact d.newVertex_notMem (h.symm ▸ d.left_mem_cells)
    · exact hlr (by simpa using h)
  have hpath : d.skeleton.IsPath d.left [d.newEdge₁, d.newEdge₂] d.right :=
    .cons d.isLink_newEdge₁ htail hfresh
  let P := d.skeleton.pathGraphOf d.left [d.newEdge₁, d.newEdge₂]
  have hP : P.IsPathGraph d.left [d.newEdge₁, d.newEdge₂] d.right :=
    hpath.isPathGraph_pathGraphOf
  have hdel : S.skel.deleteEdges {d.edge} ≤ d.skeleton := by
    refine ⟨?_, ?_⟩
    · rw [Graph.vertexSet_deleteEdges, d.skeleton_vertexSet]
      exact Set.subset_insert _ _
    · intro e x y hlink
      change S.skel.IsLink e x y ∧ e ∉ ({d.edge} : Set γ) at hlink
      exact d.skeleton_isLink_of_old (by simpa using hlink.2) hlink.1
  have hPle : P ≤ d.skeleton := Graph.pathGraphOf_le hpath.isWalk
  have hcompat : (S.skel.deleteEdges {d.edge}).Compatible P :=
    Graph.Compatible.of_le_le hdel hPle
  have hnew : ∀ x ∈ V(P), x ≠ d.left → x ≠ d.right → x ∉ V(S.skel) := by
    intro x hx hxl hxr hxS
    rw [Graph.pathGraphOf_vertexSet, Graph.walkVertices_cons d.isLink_newEdge₁,
      Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil] at hx
    rcases hx with rfl | rfl | hx
    · exact hxl rfl
    · exact d.newVertex_notMem (S.mem_cells_of_mem_vertexSet hxS)
    · exact hxr (by simpa using hx)
  have hB2 : ((S.skel.deleteEdges {d.edge}).union P).IsTwoConnected :=
    hS2.replace_edge_by_path d.isLink hlr hcompat hP hnew
  have hBle : (S.skel.deleteEdges {d.edge}).union P ≤ d.skeleton :=
    Graph.union_le hdel hPle
  apply hB2.spanning_mono hBle
  intro x hx
  rw [d.skeleton_vertexSet] at hx
  rcases hx with rfl | hx
  · apply Set.mem_union_right
    rw [Graph.pathGraphOf_vertexSet, Graph.walkVertices_cons d.isLink_newEdge₁,
      Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil]
    simp
  · exact Set.mem_union_left _ (by simpa using hx)

/-- A geometric edge subdivision leaves the realized outer set unchanged. -/
theorem outerSet_realize {d : S.SubdivData} {R : S.Realization}
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (d.realize R t ht).outerSet = R.outerSet := by
  by_cases he : d.edge ∈ E(S.outerGraph)
  · have hedge : (⋃ f ∈ E(S.outerGraph), Graph.edgeArc R.drawing f) =
        Graph.edgeArc R.drawing d.edge ∪
          ⋃ f ∈ E(S.outerGraph) \ {d.edge}, Graph.edgeArc R.drawing f := by
      rw [← Set.biUnion_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
    have hnew : (⋃ f ∈ E(d.outer), Graph.edgeArc (d.realizeDrawing R t) f) =
        Graph.edgeArc R.drawing d.edge ∪
          ⋃ f ∈ E(S.outerGraph) \ {d.edge}, Graph.edgeArc R.drawing f := by
      rw [d.outer_edgeSet_of_mem he, Set.biUnion_insert, Set.biUnion_insert,
        Set.iUnion₂_congr (fun f (hf : f ∈ E(S.outerGraph) \ {d.edge}) =>
          d.edgeArc_of_ne (R := R) (t := t)
            (d.ne_newEdge₁_of_mem_cells
              (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf.1)))
            (d.ne_newEdge₂_of_mem_cells
              (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf.1)))),
        ← Set.union_assoc, d.edgeArc_new_union ht]
    have hvertex : d.realizePos R t '' V(d.outer) =
        insert (R.drawing d.edge t) (R.pos '' V(S.outerGraph)) := by
      rw [CellStructure.SubdivData.outer, subdivGraph_vertexSet]
      simp only [d.outer_isLink he, and_true, Set.setOf_eq_eq_singleton,
        Set.image_union, Set.image_singleton, d.realizePos_newVertex]
      rw [Set.union_comm]
      congr 1
      apply Set.image_congr
      intro z hz
      exact d.realizePos_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hz)
    have hM : R.drawing d.edge t ∈ Graph.edgeArc R.drawing d.edge :=
      ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
    change Graph.pointSet (d.outer.map (d.realizePos R t)) (d.realizeDrawing R t) =
      Graph.pointSet (S.outerGraph.map R.pos) R.drawing
    rw [Graph.pointSet, Graph.pointSet, Graph.vertexSet_map, Graph.vertexSet_map,
      Graph.edgeSet_map, Graph.edgeSet_map, hvertex, hnew, hedge, Set.insert_union,
      Set.insert_eq_of_mem (Set.mem_union_right _ (Set.mem_union_left _ hM))]
  · change Graph.pointSet (d.outer.map (d.realizePos R t)) (d.realizeDrawing R t) =
      Graph.pointSet (S.outerGraph.map R.pos) R.drawing
    rw [d.outer_eq he]
    have hgraph : S.outerGraph.map (d.realizePos R t) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => d.realizePos_of_mem_vertexSet
        (S.outerGraph_le.vertexSet_mono hz)
    rw [hgraph]
    apply Graph.pointSet_congr
    intro f hf
    rw [Graph.edgeSet_map] at hf
    have hfc := S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf)
    exact d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
      (d.ne_newEdge₂_of_mem_cells hfc)

/-- An unchanged old edge is outer after subdivision only if it was outer before subdivision. -/
theorem old_notMem_outer {d : S.SubdivData} {f : γ}
    (hfe : f ≠ d.edge) (hnew : f ∉ E(d.outer)) :
    f ∉ E(S.outerGraph) := by
  intro hfO
  by_cases heO : d.edge ∈ E(S.outerGraph)
  · apply hnew
    rw [d.outer_edgeSet_of_mem heO]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hfO, hfe⟩)
  · rw [d.outer_eq heO] at hnew
    exact hnew hfO

/-- If the first half of the subdivided edge is not outer, neither was the original edge. -/
theorem edge_notMem_outer_of_newEdge₁ {d : S.SubdivData}
    (hnew : d.newEdge₁ ∉ E(d.outer)) : d.edge ∉ E(S.outerGraph) := by
  intro heO
  apply hnew
  rw [d.outer_edgeSet_of_mem heO]
  exact Set.mem_insert _ _

/-- If the second half of the subdivided edge is not outer, neither was the original edge. -/
theorem edge_notMem_outer_of_newEdge₂ {d : S.SubdivData}
    (hnew : d.newEdge₂ ∉ E(d.outer)) : d.edge ∉ E(S.outerGraph) := by
  intro heO
  apply hnew
  rw [d.outer_edgeSet_of_mem heO]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-- Realizing an interior edge subdivision preserves weak admissibility. -/
theorem isWeaklyAdmissible_realize {d : S.SubdivData} {R : S.Realization}
    {outer dom : Set Plane} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R.IsWeaklyAdmissible outer dom) :
    (d.realize R t ht).IsWeaklyAdmissible outer dom where
  isTwoConnected := by
    have hS2 : S.skel.IsTwoConnected :=
      (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR.isTwoConnected
    have hlr : d.left ≠ d.right := fun h =>
      R.isDrawing.ne_of_isLink (d.isLink.map R.pos) (congrArg R.pos h)
    exact (d.skeleton_isTwoConnected hS2 hlr).map (d.realize R t ht).injOn_pos
  outerSet_eq := (d.outerSet_realize ht).trans hR.outerSet_eq
  isPolygonal := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    change e ∉ E(d.outer) at houter
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · exact (d.isArcBetween_newEdge₁ ht).isPolygonal_of_subset_arc
        (R.isDrawing.edge_isArcBetween (d.isLink.map R.pos))
        (hR.isPolygonal d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₁ houter))
        (d.edgeArc_newEdge₁_subset ht)
    · exact (d.isArcBetween_newEdge₂ ht).isPolygonal_of_subset_arc
        (R.isDrawing.edge_isArcBetween (d.isLink.map R.pos))
        (hR.isPolygonal d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₂ houter))
        (d.edgeArc_newEdge₂_subset ht)
    · have hfc := S.mem_cells_of_mem_edgeSet heS
      simp only [CellStructure.SubdivData.realize_drawing]
      rw [d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
        (d.ne_newEdge₂_of_mem_cells hfc)]
      exact hR.isPolygonal heS (d.old_notMem_outer (by simpa using hee) houter)
  cell_subset := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    change e ∉ E(d.outer) at houter
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · exact (d.isRefinement_realize ht).cell_subset_edge (Or.inr (Or.inl rfl)) |>.trans
        (hR.cell_subset d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₁ houter))
    · exact (d.isRefinement_realize ht).cell_subset_edge (Or.inr (Or.inr rfl)) |>.trans
        (hR.cell_subset d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₂ houter))
    · rw [CellStructure.SubdivData.realize_cell,
        d.realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet heS)]
      exact hR.cell_subset heS
        (d.old_notMem_outer (by simpa using hee) houter)
  skeletonSet_subset := by
    rw [d.skeletonSet_realize ht]
    exact hR.skeletonSet_subset

end SubdivData

end CellStructure

end Schoenflies

namespace Schoenflies

namespace GeneratedPair

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Subdivide a generated matched pair at corresponding source and target parameters. -/
noncomputable def subdivide
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := P.str.subdivideEdge d
  generated := .subdivideEdge P.generated d
  str_combInvariants := d.combInvariants P.str_combInvariants
  str_boundaryCycles := d.boundaryCycles P.str_boundaryCycles P.str_combInvariants
  src := d.realize P.src t ht
  tgt := d.realize P.tgt (d.targetParam P.homeo t) (d.targetParam_mem_Ioo P.homeo ht)
  homeo := d.realizeHomeo P.homeo ht
  src_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht P.str_combInvariants
      P.src_isCellDecomposition P.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo P.homeo ht)
      P.str_combInvariants P.tgt_isCellDecomposition P.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht P.str_combInvariants
      P.src_isCellDecomposition P.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo P.homeo ht)
      P.str_combInvariants P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.1
  tgtInterior_isOpen := P.tgtInterior_isOpen
  tgtInterior_frontier_subset := by
    rw [d.skeletonSet_realize (d.targetParam_mem_Ioo P.homeo ht)]
    exact P.tgtInterior_frontier_subset
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(d.skeleton) at he
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, -⟩
    · exact (d.isArcBetween_newEdge₁ (d.targetParam_mem_Ioo P.homeo ht)).isPolygonal_of_subset_arc
        (P.tgt.isDrawing.edge_isArcBetween (d.isLink.map P.tgt.pos))
        (P.tgt_isPolygonal d.edge_mem_edgeSet)
        (d.edgeArc_newEdge₁_subset (d.targetParam_mem_Ioo P.homeo ht))
    · exact (d.isArcBetween_newEdge₂ (d.targetParam_mem_Ioo P.homeo ht)).isPolygonal_of_subset_arc
        (P.tgt.isDrawing.edge_isArcBetween (d.isLink.map P.tgt.pos))
        (P.tgt_isPolygonal d.edge_mem_edgeSet)
        (d.edgeArc_newEdge₂_subset (d.targetParam_mem_Ioo P.homeo ht))
    · have hfc := P.str.mem_cells_of_mem_edgeSet heS
      simp only [CellStructure.SubdivData.realize_drawing]
      rw [d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
        (d.ne_newEdge₂_of_mem_cells hfc)]
      exact P.tgt_isPolygonal heS
  src_isWeaklyAdmissible := d.isWeaklyAdmissible_realize ht P.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible := d.isWeaklyAdmissible_realize
    (d.targetParam_mem_Ioo P.homeo ht) P.tgt_isWeaklyAdmissible

/-- The source realization of a subdivided pair is the source subdivision. -/
@[simp] theorem subdivide_src
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (P.subdivide d ht).src = d.realize P.src t ht := rfl

/-- The target realization uses the parameter transported by the skeleton homeomorphism. -/
@[simp] theorem subdivide_tgt
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (P.subdivide d ht).tgt =
      d.realize P.tgt (d.targetParam P.homeo t) (d.targetParam_mem_Ioo P.homeo ht) := rfl

/-- The output of inserting one source skeleton point into a matched generated pair. -/
structure SubdivideAtData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (p : Plane) where
  /-- The pair after the possible subdivision. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- Subdivision does not change the occupied source skeleton. -/
  skeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- Subdivision does not change the occupied target skeleton. -/
  targetSkeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The transported skeleton map is the old map as a point map. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The requested point and every old vertex are vertices of the new source graph. -/
  vertexSet_eq : V(pair.src.graph) = insert p V(P.src.graph)
  /-- The corresponding target point and every old target vertex are vertices as well. -/
  targetVertexSet_eq :
    V(pair.tgt.graph) = insert (P.homeo.toFun p) V(P.tgt.graph)

/-- Every point of the source skeleton can be made a vertex by one matched subdivision. -/
theorem exists_subdivideAtData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {p : Plane}
    (hp : p ∈ P.src.skeletonSet) : Nonempty (SubdivideAtData P p) := by
  classical
  by_cases hpV : p ∈ V(P.src.graph)
  · exact ⟨{
      pair := P
      parent := id
      refines_src := CellStructure.Realization.Refines.refl P.src
      refines_tgt := CellStructure.Realization.Refines.refl P.tgt
      skeletonSet_eq := rfl
      targetSkeletonSet_eq := rfl
      homeo_eqOn := fun _ _ => rfl
      vertexSet_eq := (Set.insert_eq_of_mem hpV).symm
      targetVertexSet_eq := by
        rw [P.src.vertexSet_graph] at hpV
        obtain ⟨a, ha, rfl⟩ := hpV
        rw [P.homeo.pos_apply ha, P.tgt.vertexSet_graph]
        have hmem : P.tgt.pos a ∈ P.tgt.pos '' V(P.str.skel) := ⟨a, ha, rfl⟩
        exact (Set.insert_eq_of_mem hmem).symm
    }⟩
  · rcases hp with hpoldV | hpedge
    · exact absurd hpoldV hpV
    · obtain ⟨e, heR, t, ht, rfl⟩ := Set.mem_iUnion₂.1 hpedge
      have heS : e ∈ E(P.str.skel) := by rwa [P.src.edgeSet_graph] at heR
      obtain ⟨left, right, hlr⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heS
      have ht0 : t ≠ 0 := by
        intro h
        apply hpV
        rw [h]
        exact (P.src.isDrawing.edge_param heR).2.2.left_mem
      have ht1 : t ≠ 1 := by
        intro h
        apply hpV
        rw [h]
        exact (P.src.isDrawing.edge_param heR).2.2.right_mem
      have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      letI : Finite (Fin 3) := inferInstance
      obtain ⟨fresh, hfresh, havoid⟩ :=
        exists_injective_avoiding P.str.cells P.str.finite_cells (Fin 3)
      have h01 : fresh 0 ≠ fresh 1 := fun h => by
        have := hfresh h
        omega
      have h02 : fresh 0 ≠ fresh 2 := fun h => by
        have := hfresh h
        omega
      have h12 : fresh 1 ≠ fresh 2 := fun h => by
        have := hfresh h
        omega
      obtain ⟨d, hdedge, -, -, -, -, -⟩ :=
        CellStructure.exists_subdivData P.str_boundaryCycles hlr
          (havoid 0) (havoid 1) (havoid 2) h01 h02 h12
      let T := P.subdivide d htIoo
      exact ⟨{
        pair := T
        parent := d.parent
        refines_src :=
          (d.realize_isCellDecomposition_and_isFaceJordan htIoo P.str_combInvariants
            P.src_isCellDecomposition P.src_isFaceJordan).2.2
        refines_tgt :=
          (d.realize_isCellDecomposition_and_isFaceJordan
            (d.targetParam_mem_Ioo P.homeo htIoo) P.str_combInvariants
            P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.2
        skeletonSet_eq := d.skeletonSet_realize htIoo
        targetSkeletonSet_eq :=
          d.skeletonSet_realize (d.targetParam_mem_Ioo P.homeo htIoo)
        homeo_eqOn := fun _ _ => rfl
        vertexSet_eq := by
          change V(d.realizeGraph P.src t) = _
          rw [d.realizeGraph_vertexSet, hdedge]
        targetVertexSet_eq := by
          change V(d.realizeGraph P.tgt (d.targetParam P.homeo t)) = _
          rw [d.realizeGraph_vertexSet,
            d.drawing_targetParam P.homeo (Set.Ioo_subset_Icc_self htIoo), hdedge]
      }⟩

/-- The output of inserting a finite set of source skeleton points. -/
structure SubdivideSetData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (s : Set Plane) where
  /-- The pair after all subdivisions. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- Subdivision does not change the occupied source skeleton. -/
  skeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The transported skeleton map agrees with the old one on that unchanged skeleton. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- Every requested point is a vertex of the final source graph. -/
  vertexSet_subset : s ⊆ V(pair.src.graph)

/-- Every finite set of source skeleton points can simultaneously be made vertices. -/
theorem exists_subdivideSetData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {s : Set Plane}
    (hs : s.Finite) (hsub : s ⊆ P.src.skeletonSet) :
    Nonempty (SubdivideSetData P s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨{
        pair := P
        parent := id
        refines_src := CellStructure.Realization.Refines.refl P.src
        refines_tgt := CellStructure.Realization.Refines.refl P.tgt
        skeletonSet_eq := rfl
        homeo_eqOn := fun _ _ => rfl
        vertexSet_subset := Set.empty_subset _
      }⟩
  | @insert a s ha hs ih =>
      have hskeleton : s ⊆ P.src.skeletonSet := fun x hx =>
        hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨w⟩ := ih hskeleton
      have haSkeleton : a ∈ w.pair.src.skeletonSet := by
        rw [w.skeletonSet_eq]
        exact hsub (Set.mem_insert a s)
      obtain ⟨q⟩ := exists_subdivideAtData w.pair haSkeleton
      exact ⟨{
        pair := q.pair
        parent := w.parent ∘ q.parent
        refines_src := q.refines_src.trans w.refines_src
        refines_tgt := q.refines_tgt.trans w.refines_tgt
        skeletonSet_eq := q.skeletonSet_eq.trans w.skeletonSet_eq
        homeo_eqOn := by
          intro x hx
          calc
            q.pair.homeo.toFun x = w.pair.homeo.toFun x :=
              q.homeo_eqOn (by rwa [w.skeletonSet_eq])
            _ = P.homeo.toFun x := w.homeo_eqOn hx
        vertexSet_subset := by
          intro x hx
          rw [q.vertexSet_eq]
          rcases hx with rfl | hx
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (w.vertexSet_subset hx)
      }⟩

end GeneratedPair

end Schoenflies

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Explicit output data for the common-subdivision construction. -/
structure CommonSubdivisionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) where
  /-- The part of `H` supported on the old source skeleton. -/
  graph : Graph Plane γ
  /-- The matched pair after inserting every vertex of `graph`. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite parent map from the subdivided pair to `P`. -/
  parent : γ → γ
  /-- The traced graph remains 2-connected. -/
  graph_isTwoConnected : graph.IsTwoConnected
  /-- The traced graph is a subgraph of the given extension. -/
  graph_le : graph ≤ H
  /-- The refined pair realizes the traced graph and contains all of its vertices. -/
  isPartialTransferOf : IsPartialTransferOf pair P graph Hdraw parent

/-- Construct the traced graph, matched subdivided pair, and their composite parent map. -/
noncomputable def commonSubdivisionData [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    CommonSubdivisionData P H Hdraw := by
  classical
  let K := Graph.traceGraph H Hdraw P.src.skeletonSet
  have hKle : K ≤ H := Graph.traceGraph_le _
  letI : H.Finite := hH.finite
  letI : K.Finite := Graph.Finite.of_le hKle
  have hK2 : K.IsTwoConnected :=
    trace_isTwoConnected hH P.src_isWeaklyAdmissible.isTwoConnected
  have hvertices : V(K) ⊆ P.src.skeletonSet := by
    intro x hx
    rw [Graph.traceGraph_vertexSet] at hx
    exact hx.2
  let w := Classical.choice (GeneratedPair.exists_subdivideSetData P
    (Graph.finite_vertexSet K) hvertices)
  exact {
    graph := K
    pair := w.pair
    parent := w.parent
    graph_isTwoConnected := hK2
    graph_le := hKle
    isPartialTransferOf := {
      refines_src := w.refines_src
      refines_tgt := w.refines_tgt
      sourceSkeletonSet_subset := by rw [w.skeletonSet_eq]
      homeo_eqOn := w.homeo_eqOn
      skeletonSet_eq := w.skeletonSet_eq.trans (trace_pointSet hH).symm
      vertexSet_subset := w.vertexSet_subset
    }
  }

/-- **Step 1 of finite transfer:** construct the common matched subdivision. -/
theorem commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    CommonSubdivision P H Hdraw := by
  let w := commonSubdivisionData hH
  exact ⟨w.graph, w.pair, w.parent, w.graph_isTwoConnected, w.graph_le,
    w.isPartialTransferOf⟩

/-- **`thm:finite-transfer`, direction (a).** -/
theorem finite_transfer_toward_square [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision hH (commonSubdivision hH)

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransferTarget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite transfer, direction (b): toward the Jordan domain

Direction (b) starts with an extension of the **target** realization and reproduces it on the
source side.  This module begins its construction with the target analogue of the common
subdivision from direction (a).  The graph-theoretic extension assumptions are exactly
`Schoenflies.IsSourceExtension`, applied to `P.tgt`: only the side on which the realization lives
changes.

The trace of the target extension supported on the old target skeleton is 2-connected.  Its
finitely many vertices are inserted by `GeneratedPair.exists_subdivideTargetSetData`; each target
point is transported backwards through the skeleton homeomorphism, and the resulting source
parameter is then carried forward by `SubdivData.realizeHomeo`.  Thus the same subdivision is
made on both sides and both refinement maps share one parent map.

The reverse ear bookkeeping is also completed here.  The ambient target path is injectively
renamed, realized as a target crosscut, and then matched to a polygonal source crosscut by
reversing `EarHomeo`.  Off the wild curve, endpoint accessibility is derived from
polygonal-side accessibility.  At a fresh anchor, this module constructs the compact carrier of
closed nonboundary edges and discharges compactness, cell absorption, and coverage before
applying `Schoenflies.polyAccessible_of_stronglyAccessible_in`.  `TargetBoundaryAnchored` and
the compatibility of the evolving skeleton map now supply strong accessibility automatically.
Consequently the only remaining input is `TargetEarFreshCombinatorics`: the prescribed ear
order must say that a wild-boundary endpoint is absent from the current nonboundary carrier and
incident with one unique current source face.

## Blueprint

* `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.TargetCommonSubdivision` — the
  target-to-source analogues of the direction-(a) transfer interfaces.
* `Schoenflies.targetCommonSubdivision` — step 1 of `thm:finite-transfer`(b).
* `Schoenflies.TargetEarStepData`, `Schoenflies.exists_targetSideEarStepData` — the complete
  target-path relabelling and split data for one reverse ear.
* `Schoenflies.TargetEarEndpointAccessibility`,
  `Schoenflies.targetEarStep_of_endpointAccessibility` — the reverse ear construction reduced
  to its exact source-side geometric invariant.
* `Schoenflies.GeneratedPair.sourceNonboundaryGraph`,
  `Schoenflies.GeneratedPair.source_polyAccessible_of_fresh` — the compact source carrier and
  the fresh-anchor accessibility theorem with all cellulation hypotheses discharged.
* `Schoenflies.TargetBoundaryAnchored`, `Schoenflies.TargetEarFreshCombinatorics`,
  `Schoenflies.targetEarFreshInvariant_of_boundaryAnchored` — the fixed anchor geometry split
  cleanly from the remaining prescribed-ear combinatorics.
* `Schoenflies.targetTransferOfEars`,
  `Schoenflies.finite_transfer_toward_source_of_freshInvariant` — the relative-ear induction
  and direction-(b) theorem assuming only that combinatorial invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- An intermediate target-to-source transfer: the target realization occupies the current
subgraph of the target extension, while both sides refine the original pair along one map. -/
structure IsTargetPartialTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the original source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the original target realization along the same map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The evolving source skeleton contains the original source skeleton. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- On the original source skeleton, the evolving skeleton map is still the original map. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The new target skeleton occupies exactly the current target subgraph. -/
  skeletonSet_eq : T.tgt.skeletonSet = pointSet B Hdraw
  /-- Every current target-graph vertex is a 0-cell of the new pair. -/
  vertexSet_subset : V(B) ⊆ V(T.tgt.graph)

/-- The final conclusion of direction (b): a target extension reproduced by an admissible
matched pair on both sides. -/
structure IsTargetTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsTargetPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible. -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-- Complete constructor data for adjoining one target ear to a partial reverse transfer. -/
structure TargetEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  /-- The common abstract face split. -/
  splitData : T.str.SplitData
  /-- The two realizations of its new ear. -/
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  /-- Each realized ear is a crosscut of the corresponding old face. -/
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  /-- The source-to-target matching consumed by `GeneratedPair.split`. -/
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
  /-- Both realized ears have polygonal edges. -/
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  /-- The target ear realizes exactly the ambient target path. -/
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  /-- All vertices of the enlarged target graph occur in the split realization. -/
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

namespace TargetEarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- Assemble the generated pair exposed by one reverse-ear construction. -/
noncomputable def pair (w : TargetEarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.src =
      w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.tgt =
      w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

end TargetEarStepData

/-! ### Locating and realizing the target half of a reverse ear -/

/-- The relative anchoring condition used by reverse ear insertion.  Only genuinely new
ambient edges need to end at prescribed strongly accessible anchors; edges already covering
the original target skeleton are irrelevant to the next ear. -/
def NewTargetBoundaryAnchored {β : Type*}
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (base : Set Plane)
    (H : Graph Plane β) (Hdraw : β → ℝ → Plane) : Prop :=
  ∀ {B : Graph Plane β}, B ≤ H → base ⊆ pointSet B Hdraw →
    ∀ {f : β} {y : Plane}, f ∈ E(H) → f ∉ E(B) → H.Inc f y → y ∈ tgtOuter →
      ¬ edgeArc Hdraw f ⊆ tgtOuter →
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun y)

/-- The relative boundary-incidence condition actually used by reverse ear insertion.  A new
nonouter ambient edge cannot meet, at the distinguished boundary, a nonouter edge already in
the current trace.  Unlike `NonouterIncidenceUniqueAtBoundary`, this permits several old
nonouter edges at an old boundary vertex, which is essential for target-mesh overlays. -/
def NoNewNonouterIncidenceAtBoundary {β : Type*}
    (base : Set Plane) (H : Graph Plane β) (Hdraw : β → ℝ → Plane)
    (outer : Set Plane) : Prop :=
  ∀ {B : Graph Plane β}, B ≤ H → base ⊆ pointSet B Hdraw →
    ∀ {z : Plane} {e f : β}, z ∈ outer → e ∈ E(H) → f ∈ E(B) →
      H.Inc e z → B.Inc f z →
      ¬ edgeArc Hdraw e ⊆ outer → ¬ edgeArc Hdraw f ⊆ outer →
      e ∉ E(B) → False

/-- An edge of a plane graph whose whole carrier is already covered by a subgraph is itself an
edge of that subgraph.  An interior point of the arc cannot be a subgraph vertex, nor lie on a
different subgraph edge, by the drawing intersection axioms. -/
theorem edge_mem_of_edgeArc_subset_pointSet
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
    (hdraw : G.IsDrawing drawing) (hBG : B ≤ G) {e : β} (he : e ∈ E(G))
    (hsub : edgeArc drawing e ⊆ pointSet B drawing) : e ∈ E(B) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have harc := hdraw.edge_isArcBetween hxy
  obtain ⟨p, hpArc, hpEnds⟩ := not_subset.1 harc.not_subset_pair
  rcases hsub hpArc with hpV | hpE
  · rcases hdraw.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpArc with rfl | rfl
    · exact absurd (Or.inl rfl) hpEnds
    · exact absurd (Or.inr rfl) hpEnds
  · obtain ⟨f, hfB, hpf⟩ := Set.mem_iUnion₂.1 hpE
    by_cases hef : e = f
    · exact hef ▸ hfB
    · obtain ⟨hpV, -, -⟩ :=
        hdraw.edge_inter he (hBG.edgeSet_mono hfB) hef hpArc hpf
      rcases hdraw.vertex_mem_edgeArc hxy hpV hpArc with rfl | rfl
      · exact absurd (Or.inl rfl) hpEnds
      · exact absurd (Or.inr rfl) hpEnds

/-- In a plane drawing, an edge carrier cannot be contained in the carrier of a distinct
edge. -/
theorem eq_of_edgeArc_subset
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (hdraw : G.IsDrawing drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hsub : edgeArc drawing e ⊆ edgeArc drawing f) : e = f := by
  by_contra hef
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have harc := hdraw.edge_isArcBetween hxy
  obtain ⟨p, hpArc, hpEnds⟩ := not_subset.1 harc.not_subset_pair
  obtain ⟨hpV, -, -⟩ := hdraw.edge_inter he hf hef hpArc (hsub hpArc)
  rcases hdraw.vertex_mem_edgeArc hxy hpV hpArc with rfl | rfl
  · exact hpEnds (Or.inl rfl)
  · exact hpEnds (Or.inr rfl)

/-- The one-sided constructor data obtained by realizing the ambient target path. -/
structure TargetSideEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a b : Plane) (D : List γ) where
  splitData : T.str.SplitData
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  /-- The two old abstract endpoints retain the orientation of the ambient target path. -/
  target_pos_source : T.tgt.pos splitData.source = a
  target_pos_target : T.tgt.pos splitData.target = b
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

/-! ### The exact geometric obligation on the source side -/

/-- The edge set of the distinguished outer graph is exactly one simple cycle.  Isolated
vertices are intentionally irrelevant: reverse transfer only reads edge incidence. -/
def CellStructure.OuterEdgesFormCycle (S : CellStructure γ) : Prop :=
  ∃ e u v D, S.outerGraph.IsCycleThrough e u v D ∧
    E(S.outerGraph) = {f | f ∈ e :: D}

/-- Source vertices incident with a nonboundary edge.  Outer-only vertices are deliberately
excluded: a fresh anchor must not enter the compact set merely because it is already a vertex
of the outer cycle. -/
def GeneratedPair.sourceNonboundaryVertices
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Set Plane :=
  {x | ∃ e, e ∈ E(T.src.graph) ∧ e ∉ E(T.str.outerGraph) ∧ T.src.graph.Inc e x}

/-- The current source graph with outer edges and outer-only vertices removed.  Its point set is
the compact union of the closed nonboundary edges used in the fresh-anchor argument. -/
def GeneratedPair.sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Graph Plane γ :=
  (T.src.graph.deleteEdges E(T.str.outerGraph)).induce T.sourceNonboundaryVertices

theorem GeneratedPair.sourceNonboundaryGraph_le
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph ≤ T.src.graph := by
  apply (Graph.induce_le ?_).trans Graph.deleteEdges_le
  rintro x ⟨e, -, -, hinc⟩
  exact hinc.vertex_mem

instance GeneratedPair.sourceNonboundaryGraph_finite
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph.Finite :=
  Graph.Finite.of_le T.sourceNonboundaryGraph_le

/-- The source skeleton is the union of its compact nonboundary-edge carrier and its outer
curve. -/
theorem GeneratedPair.skeletonSet_eq_sourceNonboundaryGraph_union
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.src.skeletonSet = pointSet T.sourceNonboundaryGraph T.src.drawing ∪ srcOuter := by
  have hdecomp : T.src.skeletonSet =
      pointSet T.sourceNonboundaryGraph T.src.drawing ∪ T.src.outerSet := by
    apply Set.Subset.antisymm
    · intro x hx
      change x ∈ pointSet T.src.graph T.src.drawing at hx
      rcases hx with hxV | hxE
      · obtain ⟨e, he, hinc⟩ : ∃ e, e ∈ E(T.src.graph) ∧ T.src.graph.Inc e x := by
          obtain ⟨z, hz, hzx, -⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
          obtain ⟨D, hD⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hxV hz
          obtain ⟨e, heD, hinc⟩ :=
            hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
          exact ⟨e, hD.edge_mem heD, hinc⟩
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · apply Or.inr
          apply Graph.vertexSet_subset_pointSet
          have hOle : T.str.outerGraph.map T.src.pos ≤ T.src.graph :=
            T.str.outerGraph_le.map T.src.pos
          exact ((hOle.inc_congr (by rwa [Graph.edgeSet_map])).2 hinc).vertex_mem
        · apply Or.inl
          apply Graph.vertexSet_subset_pointSet
          exact ⟨e, he, heOuter, hinc⟩
      · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · exact Or.inr (Graph.edgeArc_subset_pointSet (by
            rw [Graph.edgeSet_map]
            exact heOuter) hxe)
        · apply Or.inl
          exact Graph.edgeArc_subset_pointSet (by
            obtain ⟨u, v, huv⟩ := T.src.graph.exists_isLink_of_mem_edgeSet he
            exact ⟨u, v, ⟨⟨huv, heOuter⟩,
              ⟨e, he, heOuter, huv.inc_left⟩, ⟨e, he, heOuter, huv.inc_right⟩⟩⟩) hxe
    · exact Set.union_subset
        (Graph.pointSet_mono T.sourceNonboundaryGraph_le)
        T.src.outerSet_subset_skeletonSet
  exact hdecomp.trans (congrArg (pointSet T.sourceNonboundaryGraph T.src.drawing ∪ ·)
    T.src_isWeaklyAdmissible.outerSet_eq)

/-- The two genuinely evolving obligations at a wild-boundary endpoint: no nonboundary edge
has reached it yet, and the next ear's face is its unique incident current source face. -/
def GeneratedPair.SourceEndpointFreshCombinatorics
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (x : Plane) : Prop :=
  x ∈ srcOuter →
    x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing ∧
      ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
        x ∈ closure R → R = T.src.cell F

/-- The remaining prescribed-ear combinatorics after boundary anchoring has supplied strong
accessibility: both outer endpoints are fresh and incident with the selected face alone. -/
def TargetEarFreshCombinatorics [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        T.SourceEndpointFreshCombinatorics w.splitData.face
            (T.src.pos w.splitData.source) ∧
        T.SourceEndpointFreshCombinatorics w.splitData.face
            (T.src.pos w.splitData.target)

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh

The geometric core of Proposition `prop:anchored-square-mesh`, in vocabulary that exists today:
Part II's cellulations, `V_boundary` and fresh points `u(𝒜)` are not built here, so the mesh is
stated as a **finite plane graph with a straight-line drawing**, with the clauses of the
proposition as separate theorems about it.

## The construction

`squareMesh δ fresh anchors` is `meshCount δ` concentric ring frames of radii
`1/N, 2/N, …, 1` inside `Q = [-1,1]²`, together with one full-length radial spoke
`[z, N⁻¹ • z]` at each fresh boundary point `z`. The list of segments is handed to
`overlayGraph` (Lemma 3.7), which subdivides at every crossing; the anchors are added to the
cut points, which is what makes each of them a vertex.

**This is not literally the blueprint's construction, and the difference is deliberate.** The
blueprint has one collar `λ ≤ ‖x‖∞ ≤ 1` plus a rectangular grid filling `λQ`. Here the collar
is repeated `N` times and there is no grid at all: the innermost square `N⁻¹ Q` is a *single*
cell, of diameter `2√2/N < δ`. That removes the "choose fine enough horizontal and vertical
coordinates, including the four corners and all the points `λ z_i`" step entirely, and makes
the whole mesh radial, so that one estimate — `‖tz - sw‖ ≤ t‖z - w‖ + |t - s|‖w‖`, the
blueprint's own — covers every cell. Nothing downstream can tell the difference: the clauses
are the interface.

The blueprint's cyclic ordering of the fresh points is likewise gone. Where it says "choose
`z_0, …, z_{m-1}` in cyclic order so that each boundary arc between consecutive ones has
diameter `< δ/4`", this module takes the order-free consequence as a hypothesis,
`FreshDense fresh δ`: *every connected subset of `S` avoiding all the fresh points has diameter
at most `δ/2`*. A set-level statement needs no ordering, and it is exactly what the blueprint's
own argument (parametrize `S` by a circle, cut it into small arcs, put one fresh point inside
each) produces.

## What is proved, and what is not

The clauses about faces, anchors, edges reaching `S` and connectedness of `|T| ∖ S` are proved
in full. Two gaps, both stated plainly:

* **The outer cycle is proved only as a point set.** `squareMesh_cover_outerEdges` says the
  edges whose segments lie on `S` occupy exactly `S`. That these edges form a **cycle** of the
  graph is *not* proved: it needs the fresh points, the anchors and the four corners put in
  cyclic order along `S`, which is precisely the ordering this construction was designed to
  avoid. A later module wanting the outer cycle must build it.
* **2-connectivity is not proved at all.** It is not present as a hypothesis either — a
  hypothesis restating the goal would be worthless. The route is the blueprint's: the innermost
  ring is a cycle, and each annulus between consecutive rings is added one rectangle at a time
  by `Graph.IsTwoConnected.union`, each added cycle sharing at least two vertices with what is
  already there. Nothing in this module obstructs it.

Connectedness of `|T| ∖ S` needs at least one fresh point (`hz₀ : z₀ ∈ fresh`): with no spokes
the rings are disjoint frames.

## Blueprint

* `ringSet`, `ringPieces`, `spokePiece`, `meshSegments` — the mesh as a list of segments.
* `meshGraph`, `squareMesh` — Proposition "Anchored square mesh", the construction itself.
* `FreshDense` — the order-free form of "consecutive fresh points bound an arc of diameter
  `< δ/4`".
* `squareMesh_face_small` — clause 1: every bounded 2-cell has diameter `< δ`, and lies in `Q`.
* `squareMesh_anchor_mem_vertexSet` — clause 2: every boundary vertex survives.
* `squareMesh_inner_edge_at_fresh`, `squareMesh_unique_inner_edge` — clauses 3 and 4: a new
  internal edge meeting `S` ends at a fresh point, and exactly one such edge is incident with
  each fresh point.
* `squareMesh_cover_outerEdges` — the point-set half of "`S` is the outer cycle" (see above).
* `squareMesh_isConnected_diff` — clause 6: `|T| ∖ S` is connected.
* `radial_diam_bound` — the blueprint's radial estimate, isolated from all graph language.
* `subdivide_covers_source`, `subdivide_end_of_mem` — two general facts about `subdivide` that
  belong in `Schoenflies/Subdivide.lean`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### Rings: the frame of a square about the origin -/

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

/-! ### Spokes -/

/-! ### Two more facts about `subdivide`

Both are general and belong beside the others in `Schoenflies/Subdivide.lean`; they are here
because that module is on `main`.

`subdivide_covers_source` refines `subdivide_cover`: a point of a *named* source piece lies on
a piece of the subdivision *inside that source*. Without the "inside that source" clause one
cannot tell, of a point where two sources cross, which of them the piece through it came from
— and the whole description of the mesh's edges is by their source.

`subdivide_end_of_mem` is the converse of `subdivide_avoids`: a cut point that lies on a source
piece is not merely absent from every interior, it is an **endpoint** of a piece inside that
source. That is what makes a prescribed point a vertex of the overlay graph. -/

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

theorem meshGraph_pointSet (N : ℕ) (fresh anchors : List Plane) :
    Graph.pointSet (meshGraph N fresh anchors) segmentDrawing = cover (meshSegments N fresh) :=
  overlayGraph_pointSet _ _

/-! ### Clause 2: the anchors are vertices on `S` -/

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

/-! ### Clause 1: every bounded face is small

The estimate is the blueprint's, in radial coordinates. A connected set missing the mesh
misses every ring, so its sup norm — continuous, hence with a preconnected image in `ℝ` —
stays inside one open interval `(k/N, (k+1)/N)` between consecutive ring radii. Inside the
innermost square that is already the whole bound; outside it the radial projection
`x ↦ ‖x‖∞⁻¹ • x` maps the set into `S`, connectedly, and away from every fresh point, because
a point projecting to a fresh point lies on that point's spoke. The blueprint's

  `‖x - y‖ ≤ ‖tz - tw‖ + ‖tw - sw‖ < δ/4 + δ/4 + δ/4`

is then `t‖z - w‖ + |t - s|‖w‖`, with `‖z - w‖` controlled by `FreshDense` and `|t - s|` by
one ring thickness. -/

/-- **Clause 1.** Every bounded face of the mesh lies in the open square and has diameter
`< δ`. -/
theorem meshGraph_face_small {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {δ : ℝ} (hδ : 0 < δ)
    (hNδ : 2 * Real.sqrt 2 < δ * N) (hdense : FreshDense fresh δ) {base : Plane}
    (hbase : base ∈ Graph.exterior (meshGraph N fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (meshGraph N fresh anchors) segmentDrawing base)) :
    Graph.face (meshGraph N fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (meshGraph N fresh anchors) segmentDrawing base) < δ := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  set F := Graph.face (meshGraph N fresh anchors) segmentDrawing base with hF
  have hpt : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      = cover (meshSegments N fresh) := meshGraph_pointSet N fresh anchors
  have hsq : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      ⊆ Plane.closedSquare 0 1 := by rw [hpt]; exact cover_meshSegments_subset hN hfresh
  -- the base point is inside the square: outside it the face would be the unbounded one
  have hbM : base ∉ cover (meshSegments N fresh) := by rw [← hpt]; exact hbase
  have hb1 : Plane.supNorm base < 1 := by
    rcases lt_trichotomy (Plane.supNorm base) 1 with h | h | h
    · exact h
    · exact absurd (ringSet_subset_cover hN (one_mem_meshRadii hN) h) hbM
    · exfalso
      have hmem : base ∈ Plane.beyondSquare 1 := by
        rw [Plane.beyondSquare_eq_compl]
        exact fun hc => absurd (mem_closedSquare_zero_one.1 hc) (not_le.2 h)
      exact Graph.not_isBounded_beyondSquare 1
        (hbdd.subset (Graph.beyondSquare_subset_face hsq hmem))
  have hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh) := by
    intro x hx
    have := Graph.face_subset_exterior _ _ _ hx
    rwa [Graph.exterior, hpt, mem_compl_iff] at this
  obtain ⟨hin, hdist⟩ := radial_diam_bound hN hNδ.le hdense
    (Graph.isConnected_face hbase).isPreconnected hdisj (Graph.mem_face hbase) hb1
  refine ⟨fun x hx => mem_openSquare_zero_one.2 (hin x hx), ?_⟩
  have hthin : Real.sqrt 2 / (N : ℝ) < δ / 2 := by
    rw [div_lt_div_iff₀ hNR0 two_pos]; linarith
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (by positivity) hdist) ?_
  linarith

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

theorem squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing
      = cover (meshSegments (meshCount δ) fresh) :=
  meshGraph_pointSet _ _ _

/-- The whole model curve is part of the mesh. -/
theorem modelCurve_subset_squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    modelCurve ⊆ Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing := by
  rw [squareMesh_pointSet, ← ringSet_one]
  exact ringSet_subset_cover (two_le_meshCount δ) (one_mem_meshRadii (two_le_meshCount δ))

/-- **Clause 1.** Every bounded face lies in the open square and has diameter `< δ`. -/
theorem squareMesh_face_small {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {δ : ℝ} (hδ : 0 < δ) (hdense : FreshDense fresh δ) {anchors : List Plane} {base : Plane}
    (hbase : base ∈ Graph.exterior (squareMesh δ fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (squareMesh δ fresh anchors) segmentDrawing base)) :
    Graph.face (squareMesh δ fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (squareMesh δ fresh anchors) segmentDrawing base) < δ :=
  meshGraph_face_small (two_le_meshCount δ) hfresh hδ (meshCount_spec hδ) hdense hbase hbdd

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.chainUnion_succ _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.EarStepData.pair_src _root_.Schoenflies.EarStepData.pair_tgt _root_.Schoenflies.GeneratedPair.split_str _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The inner grid of the anchored square mesh: 2-connectivity and the outer cycle

`Schoenflies/SquareMesh.lean` delivers the geometry of `prop:anchored-square-mesh` — the
diameter bound, the anchors, the inward edges at the fresh points, and connectedness of
`|T| ∖ S` — and leaves two clauses open, both of them combinatorial:

* clause 5, *the skeleton of `T` is 2-connected*, is absent;
* clause 3 is proved only as a point-set equation, never as a **cycle** of the graph.

This module supplies both for the object the blueprint's own proof of the proposition is about:
the **rectangular grid**. See "What this does and does not close" below for exactly what the
integrator still has to do.

## The grid, concretely

Two coordinate functions `xc yc : ℕ → ℝ` and two sizes `m n : ℕ` fix a grid: the vertices are
the `(m+1)(n+1)` points `gridPt xc yc i j = (xc i, yc j)`, the edges are the `m(n+1)`
horizontal steps `gridHEdge` and the `(m+1)n` vertical steps `gridVEdge`. Everything is a
`def` — an existentially quantified grid could not be refined against a second one, which is
what Part II does.

The hypotheses on the coordinates are exactly as strong as each statement needs, and no
stronger: 2-connectivity needs only that **consecutive** coordinates differ, the outer cycle
needs the coordinates **distinct** (`Set.InjOn xc (Set.Iic m)`), and only the drawing — the
clause that makes the grid a plane graph — needs them **increasing**
(`StrictMonoOn xc (Set.Iic m)`).

The graph is `pieceListGraph (gridEdges xc yc m n)`, where `pieceListGraph` is the general
"a list of straight segments, read as a graph" constructor: an edge is a `Piece`, and it links
exactly its two ends. `pieceListGraph` is `overlayGraph` without the subdivision — the vertices
are the ends of the listed segments and nothing is cut — and its point is that
`pieceListGraph l₁ ∪ pieceListGraph l₂ = pieceListGraph (l₁ ++ l₂)` **on the nose**
(`pieceListGraph_union`), so that the blueprint's "add these finitely many cycles one at a
time" is list concatenation and every union is an equation rather than an inclusion.

## 2-connectivity: two nested chains of `lem:union-two-connected`

The blueprint says "the inner grid is 2-connected by the same ear construction used for `K`".
The ear construction is replaced here by two applications of `Graph.IsTwoConnected.union`,
which is shorter and needs no ear at all:

* one **cell** — the boundary of a single rectangle of the grid — is a quadrilateral, and
  `Graph.isTwoConnected_of_quad` proves any quadrilateral 2-connected directly from the
  definition (delete a vertex; the other three are still a path);
* a **strip** (one column of cells) is the union of its cells, consecutive cells sharing the
  horizontal edge between them, hence two vertices;
* the **grid** is the union of its strips, consecutive strips sharing the whole vertical line
  between them, hence again two vertices.

Both chains need at least two vertices in common at every step, so both need `1 ≤ m` and
`1 ≤ n`: a grid with a single row of points is a path and is not 2-connected. That is the
degenerate case, and it is a hypothesis, not an oversight.

## The outer cycle

The boundary walk goes once round the four sides, `gridBoundaryEdge` and `gridBoundaryPt`
naming the `2m + 2n` edges and vertices in order by a four-way `if` on the index. Everything
about the walk is then arithmetic in `ℕ`, which `omega` decides.
`gridGraph_isCycleThrough_boundary` is a `Graph.IsCycleThrough` of the grid graph — the
distinguished outer cycle — and `edgesCover_gridBoundary` computes what it occupies: for
increasing coordinates it is exactly the frame of the bounding rectangle, and for the grid on
`[-1,1]²` that frame is `modelCurve`, i.e. `S` (`edgesCover_gridBoundary_modelCurve`,
`gridGraph_outer_cycle`). That is the cycle `thm:finite-transfer`(b) asks for, in the form it
asks for it.

The grid is also shown to be a **plane graph** (`gridGraph_isDrawing`), so the outer cycle is a
Jordan curve (`gridBoundary_isJordanCurve`) and the whole face machinery applies to it.

## What this does and does not close

**Closed.** Both clauses, for the rectangular grid, from an explicit construction, together
with the drawing that makes the grid a plane graph.

**Not closed.** Neither clause is transported to `Schoenflies.squareMesh`, and the reason is
structural, not a matter of effort: `squareMesh` is `overlayGraph` applied to a list of
segments *and an unspecified list of cut points* obtained from `exists_cut_points` by choice.
Its edges are therefore the pieces of a subdivision nobody can enumerate, so neither "the
edges on `S` form a cycle" nor "the rings are cycles glued along the spokes" is available
without first proving that the subdivision of a segment at a finite point set is a **path** —
a theorem no module on `main` has. The honest statement of the missing collar step is
`Graph.IsTwoConnected.attach_cycles` below: it takes a 2-connected hub `K` and finitely many
2-connected pieces each meeting `K` in two distinct vertices, and concludes for the union.
Instantiating it at `squareMesh` needs the collar rectangles of the mesh as cycles, which is
exactly the enumeration that is missing.

**A degenerate case that would have to be excluded.** `squareMesh δ fresh anchors` is *not*
2-connected when `fresh` has fewer than two distinct points, so the missing theorem cannot be
stated without a hypothesis. With `fresh = []` the mesh is `meshCount δ` pairwise disjoint
concentric ring frames and is not even connected. With one fresh point `z` the spoke at `z` is
the only thing joining the rings, so every vertex of that spoke is a cut vertex: deleting the
one at radius `k/N` separates the rings inside it from the rings outside. Two fresh points are
what make the rings and the two spokes a chain of quadrilaterals, which is the same picture the
grid presents here. The corresponding hypothesis for the grid is `1 ≤ m` and `1 ≤ n`, and it is
carried explicitly by every theorem below that needs it.

## Blueprint

* `prop:anchored-square-mesh`, clause 5, for the inner grid — `gridGraph_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3, as a cycle — `gridGraph_isCycleThrough_boundary`
  together with `edgesCover_gridBoundary`, `edgesCover_gridBoundary_modelCurve` and the
  packaged `gridGraph_outer_cycle`.
* `lem:polygonal-overlay`, the drawing clause, for the grid — `gridGraph_isDrawing`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union`; iterated here as
  `Graph.IsTwoConnected.attach_cycles`, which is the blueprint's "adding these finitely many
  cycles one at a time".
* `pieceListGraph`, `pieceListGraph_union` — the list-of-segments graph, and the fact that its
  unions are concatenations.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### The graph carried by a list of segments

`overlayGraph` subdivides; this does not. When the segments are already in general position —
which for a grid they are, by construction — no subdivision is wanted, and what is gained is
that unions are concatenations.

`Schoenflies/ArcComplement.lean` has the same construction indexed by a `Set Piece`, under the
name `segGraph`, and `pieceListGraph l` is `segGraph {P | P ∈ l}`. The two were written in
parallel and collided at merge; they are kept apart for now because this module's proofs run on
the list and the other's on the set. If a third consumer appears, hoist the set version into
`Schoenflies/OverlayGraph.lean` beside `endSet` and derive this one from it. -/

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-! ### The cell -/

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

/-- **A column of cells is 2-connected.** Consecutive cells share the horizontal edge between
them, hence its two ends. -/
theorem stripGraph_isTwoConnected {xc yc : ℕ → ℝ} {i : ℕ} (hx : xc i ≠ xc (i + 1)) :
    ∀ k : ℕ, (∀ j ≤ k, yc j ≠ yc (j + 1)) →
      (pieceListGraph (stripEdges xc yc i (k + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hy
    rw [stripEdges_one]
    exact cellGraph_isTwoConnected hx (hy 0 le_rfl)
  | succ k ih =>
    intro hy
    -- The edge shared by the new cell and the previous one is the horizontal step at height
    -- `k+1`: the top of cell `(i, k)` and the bottom of cell `(i, k+1)`.
    have hold : gridHEdge xc yc i (k + 1) ∈ stripEdges xc yc i (k + 1) :=
      cellEdges_subset_stripEdges (Nat.lt_succ_self k) (by simp [cellEdges])
    have hnew : gridHEdge xc yc i (k + 1) ∈ cellEdges xc yc i (k + 1) := by simp [cellEdges]
    rw [stripEdges_succ, ← pieceListGraph_union]
    exact (ih fun j hj => hy j (by omega)).union (pieceListGraph_compatible _ _)
      (cellGraph_isTwoConnected hx (hy (k + 1) le_rfl)) (gridPt_ne_of_fst hx)
      (mem_vertexSet_pieceListGraph_left hold) (mem_vertexSet_pieceListGraph_left hnew)
      (mem_vertexSet_pieceListGraph_right hold) (mem_vertexSet_pieceListGraph_right hnew)

/-- **The grid is 2-connected.** Each new column shares with what is already there the whole
vertical line between them — in particular the two ends of its lowest edge.

The two size hypotheses are not decoration: a grid one point wide is a path, and a path is not
2-connected. -/
theorem gridGraph_isTwoConnected_aux {xc yc : ℕ → ℝ} {n : ℕ}
    (hy : ∀ j ≤ n, yc j ≠ yc (j + 1)) :
    ∀ k : ℕ, (∀ i ≤ k, xc i ≠ xc (i + 1)) →
      (pieceListGraph (gridEdges xc yc (k + 1) (n + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hx
    rw [gridEdges_one]
    exact stripGraph_isTwoConnected (hx 0 le_rfl) n hy
  | succ k ih =>
    intro hx
    -- The shared edge is the lowest vertical step of the new column: the right side of cell
    -- `(k, 0)` and the left side of cell `(k+1, 0)`.
    have hold : gridVEdge xc yc (k + 1) 0 ∈ gridEdges xc yc (k + 1) (n + 1) :=
      stripEdges_subset_gridEdges (Nat.lt_succ_self k)
        (cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges]))
    have hnew : gridVEdge xc yc (k + 1) 0 ∈ stripEdges xc yc (k + 1) (n + 1) :=
      cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges])
    rw [gridEdges_succ, ← pieceListGraph_union]
    exact (ih fun i hi => hx i (by omega)).union (pieceListGraph_compatible _ _)
      (stripGraph_isTwoConnected (hx (k + 1) le_rfl) n hy) (gridPt_ne_of_snd (hy 0 (by omega)))
      (mem_vertexSet_pieceListGraph_left hold) (mem_vertexSet_pieceListGraph_left hnew)
      (mem_vertexSet_pieceListGraph_right hold) (mem_vertexSet_pieceListGraph_right hnew)

/-- **`prop:anchored-square-mesh`, clause 5, for the inner grid.** -/
theorem gridGraph_isTwoConnected {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : ∀ i < m, xc i ≠ xc (i + 1)) (hy : ∀ j < n, yc j ≠ yc (j + 1)) :
    (gridGraph xc yc m n).IsTwoConnected := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := ⟨n - 1, by omega⟩
  exact gridGraph_isTwoConnected_aux (fun j hj => hy j (by omega)) k fun i hi => hx i (by omega)

/-! ### Which grid edges exist

Two membership lemmas, both by the same trick: a horizontal edge at height `n` is the *top*
of a cell rather than the bottom of one, and a vertical edge on the line `i = m` is the *right*
side of a cell rather than the left. -/

/-! ### The outer cycle

The boundary of the grid, walked once anticlockwise from the corner `(0,0)`: `m` steps right
along the bottom, `n` up the right side, `m` back along the top, `n` down the left side. The
walk is parametrised by an index `t < 2m + 2n`, and both the vertex and the edge at index `t`
are given by a four-way `if`. Everything about the walk then reduces to arithmetic in `ℕ`,
which `omega` decides; the geometry enters only in `edgesCover_gridBoundary` at the end. -/

/-! ### What the outer cycle occupies

Up to here nothing has been asked of the order of the coordinates. It is asked now: the union
of the boundary edges is the frame of the bounding rectangle only if the coordinates increase,
and the proof is the one-dimensional fact `Set.Icc_union_Icc_eq_Icc` transported along
`Schoenflies.mem_segment_horiz` / `mem_segment_vert`. -/

/-! ### Consecutive intervals -/

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.LocalGrid
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The local source grid, and the missing hypothesis of the anchored square mesh

Two things, and the second is the more important.

## 1. `prop:anchored-square-mesh` clause 5 — which hypothesis repairs it

`docs/ROADMAP.md` records clause 5, *the skeleton of `T` is 2-connected*, as **false** for
`Schoenflies.squareMesh` when the fresh-point set is too small, and names
`Schoenflies.FreshDense` as "the shape the missing hypothesis should take". The first section
of this module checks that, and the answer is **no: `FreshDense` alone does not repair
clause 5.**

* `Schoenflies.freshDense_of_four_sqrt_two_le` — for `4√2 ≤ δ`, `FreshDense fresh δ` holds for
  **every** list `fresh`, the empty one included, because `S` itself has diameter `2√2`. So
  `FreshDense fresh δ` is vacuous at large `δ` and excludes nothing.
* `Schoenflies.freshDense_not_isTwoConnected` — the counterexample made formal: at
  `δ = 4√2` the hypotheses `0 < δ` and `FreshDense [] δ` both hold and
  `squareMesh δ [] anchors` is still not 2-connected.

What does repair it is `FreshDense` **together with a bound on `δ`**:

* `Schoenflies.exists_two_distinct_fresh_of_freshDense` — `FreshDense fresh δ` and `δ < 4`
  force two distinct fresh points. (`4` is not the sharp constant — `4√2` is — but it is the
  one a side of `S`, whose two ends are `2` apart, gives with no work. The blueprint's own
  `δ = ε_n = 2^{-n}` is far below either.)

and two distinct fresh points is exactly the right amount, because *fewer* is always fatal:

* `Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` — a mesh whose fresh points
  are not two distinct points is **never** 2-connected. This closes the case
  `SquareMeshFixed.lean` left open in prose: with exactly one fresh point `z` the mesh is
  connected, but `z` is a cut vertex, because the spoke at `z` is the only edge of the mesh
  that changes the sup norm and every other edge preserves it.

So the correct statement of clause 5 carries the hypothesis `∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w`,
which `FreshDense fresh δ ∧ δ < 4` supplies, and which is necessary as well as sufficient in
the degenerate range.

## 2. `prop:local-grid-attachment` — the grid

The blueprint's proof begins: *"Choose sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction. Begin with the outer
rectangle of the resulting grid `K` … By `lem:subdivision-ear-preserve`, `K` is 2-connected."*

`Schoenflies.localGrid` is that `K`, as a `def`: the uniform `k × k` grid on the closed square
`W` of centre `p` and radius `s`. `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean` supply everything combinatorial about a grid, so what is
added here is the *quantitative* clause the proposition needs — every closed grid rectangle has
diameter `< ε` — together with the instantiation of the general grid lemmas at these
coordinates.

The rest of `prop:local-grid-attachment` — the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases, and the component-joining loop — is **not** here; see the
report.

## Blueprint

* `prop:anchored-square-mesh`, clause 5 — `freshDense_of_four_sqrt_two_le`,
  `freshDense_not_isTwoConnected`, `exists_two_distinct_fresh_of_freshDense`,
  `not_isTwoConnected_meshGraph_of_fresh_subsingleton`,
  `not_isTwoConnected_squareMesh_of_fresh_subsingleton`.
* `prop:local-grid-attachment`, the grid `K` — `localGrid`, `localGrid_isTwoConnected`,
  `localGrid_subdivide_isTwoConnected`, `localGrid_isDrawing`, `localGrid_outer_cycle`.
* `prop:local-grid-attachment`, clause 3 — `dist_le_of_mem_localGridCell` (the closed grid
  rectangle), `dist_lt_of_avoiding_localGrid` (a connected subset of `W` missing the grid),
  `localGridCount`, `localGridCount_spec`, `localGrid_fine`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union` and
  `Graph.IsTwoConnected.ear`; `Graph.IsTwoConnected.of_le_of_vertexSet_subset` is the
  "spanning 2-connected subgraph" form the assembly needs.
-/

open Metric Set
open scoped Graph

/-! ### A spanning 2-connected subgraph makes the whole graph 2-connected

The form in which every assembly out of `lem:union-two-connected` is finished: a chain of
unions produces *some* graph, and what the consumer wants is 2-connectivity of the graph it
started from. As long as the assembled graph is a subgraph that misses no vertex, the two
coincide — extra edges can only help connectivity. -/

namespace Schoenflies

/-! ### Uniform coordinates

`prop:local-grid-attachment` asks for "sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction". Equally spaced ones
serve, and they make the fineness a single division. -/

/-! ### The local grid

`prop:local-grid-attachment` clauses 2 and 3: a rectangular grid on the window `W`, all of
whose closed rectangles are smaller than `ε`. Everything combinatorial about it — that it is
2-connected, that it stays 2-connected after subdivision, that it is a plane graph and that its
boundary is a distinguished cycle — comes from `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean`; the content added here is the fineness. -/

variable {p : Plane} {s ε : ℝ} {k : ℕ}

/-- **`prop:local-grid-attachment`: the grid `K` is 2-connected.** -/
theorem localGrid_isTwoConnected (hs : 0 < s) (hk : 1 ≤ k) :
    (localGrid p s k).IsTwoConnected :=
  gridGraph_isTwoConnected hk hk
    (fun i _ => ne_of_lt ((localGridX_strictMono hs hk) (Nat.lt_succ_self i)))
    (fun j _ => ne_of_lt ((localGridY_strictMono hs hk) (Nat.lt_succ_self j)))

/-! ### Fineness

The one quantitative clause: every closed grid rectangle is smaller than `ε`. Stated twice —
for the closed rectangle itself, which is the blueprint's wording, and for any connected subset
of `W` that avoids the grid, which is the form a face of the overlay arrives in. -/

/-! ### Choosing the mesh

`prop:local-grid-attachment` clause 3 asks for rectangles of diameter `< ε`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GridAttach
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.decidableCrosses _root_.Schoenflies.familySquare_finite _root_.Schoenflies.squareGraph_finite
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.EarStepData.pair_src _root_.Schoenflies.EarStepData.pair_tgt _root_.Schoenflies.GeneratedPair.split_str _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Attaching a local source grid — `prop:local-grid-attachment`

`Schoenflies/LocalGrid.lean` built the grid `K` itself and its quantitative clause 3. This
module is the *rest* of the proposition: the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases of the union argument, and the component-joining loop.

## Blueprint

* `lem:polygonal-overlay`, with the convention of `rem:polygonal-overlay-convention` —
  `Schoenflies.attachPoints`, `Schoenflies.attachGraph`, `Schoenflies.attachGraph_isDrawing`,
  `Schoenflies.attachGraph_pointSet`.
* `lem:subdivision-ear-preserve` — `Graph.SameLinks` and
  `Schoenflies.overlayGraph_isTwoConnected`, the bridge that lets the raw-subdivision
  2-connectivity of `Schoenflies/SquareMeshFixed.lean` reach an overlay graph at all (see the
  next section); `Schoenflies.pieceListGraph_append_crosscut`, the single-ear step.
* `lem:union-two-connected` — `Schoenflies.overlayGraph_append_isTwoConnected` and
  `Schoenflies.attachGraph_isTwoConnected`, the blueprint's three cases in one statement.
* the auxiliary crosscut `E` of the two degenerate cases — `Schoenflies.exists_crosscut`,
  `Schoenflies.frontier_face_subset_pointSet`, `Schoenflies.seg_subset_crosscut`
  ("since `E` contains `J`") and `Schoenflies.two_common_of_crosscut`.
* the component-joining loop — `Schoenflies.isConnected_union_joins` and its cover form
  `Schoenflies.isConnected_cover_diff_of_joins`.
* `prop:local-grid-attachment` itself — `Schoenflies.gridAttachPieces`,
  `Schoenflies.gridAttachGraph`, with clause 1 `gridAttachGraph_isConnected_diff`, clause 2
  `localGrid_subset_gridAttachGraph`, clause 3 `attachGraph_localGridCell_diam`, and
  2-connectivity `gridAttachGraph_isTwoConnected`.

## The bridge that was missing: 2-connectivity of an overlay graph

`Schoenflies/SquareMeshFixed.lean` proves `pieceListGraph_subdivide_isTwoConnected`: the graph
of a **raw** subdivided piece list is 2-connected. `Schoenflies/OverlayGraph.lean` builds the
overlay as `overlayGraph pieces points`, whose edges are the subdivided pieces *oriented and
deduplicated*. Nothing on `main` connects the two, so no overlay graph anywhere in the
development was known to be 2-connected — including `Schoenflies.squareMesh`, whose clause 5
is the subject of the first half of `LocalGrid.lean`.

Orienting renames an edge `(a, b)` to `(b, a)` and deduplication drops repeats, so the two
graphs are not equal and are not isomorphic by an identity on edges. But 2-connectivity does
not see edge *names*: it is a statement about which pairs of vertices are joined. That is what
`Graph.SameLinks` isolates — same vertex set, same joined pairs — and it transfers `Connected`,
`deleteVerts`, and hence `IsTwoConnected` in both directions.

## What is a hypothesis here, and why

Three things the blueprint's proof uses are hypotheses of the assembled theorems rather than
lemmas of this module, and all three are statements about `Γ`, never about the grid.

* `hΓ` of `gridAttachGraph_isTwoConnected` — the skeleton of `Γ`, with the case's crosscut and
  the loop's joining arcs appended and everything subdivided at the crossing points, is still
  2-connected. `Γ` itself is 2-connected by hypothesis of the proposition; the subdivision is
  `lem:subdivision-ear-preserve` (a), which is `pieceListGraph_subdivide_isTwoConnected` for the
  polygonal part and `Graph.IsTwoConnected.replace_edge_by_path` for the arcs of `C`; the ears
  are `lem:subdivision-ear-preserve` (b), which is `Graph.IsTwoConnected.ear`, and
  `pieceListGraph_append_crosscut` is that step for one straight crosscut. It is not proved here
  because this module never sees `Γ`'s drawing — `C` is not drawn by segments, so `Γ` is not a
  `pieceListGraph` and the union argument has to stay combinatorial.
* `hcov` of `gridAttachGraph_isConnected_diff` — that finitely many representatives meet every
  component of `|L| ∖ C`. This is the blueprint's *"since there are only finitely many
  components"*, and it is where the loop's termination lives. Nothing on `main` proves finiteness
  of a component count for a plane set.
* the joining arcs themselves — supplied to `gridAttachGraph_isConnected_diff` as the family
  `Jarc`, with the four properties `lem:polygonal-connected` gives them
  (`Schoenflies.exists_simple_poly_of_isPreconnected` in `Schoenflies/PolygonalCarrier.lean`
  produces a polygonal path inside the open connected `D`, and `D ∩ C = ∅` gives `hJC`).


Neither is a restatement of a goal of this module, and both are true.
-/

open Metric Set
open scoped Graph

/-! ## Graphs that join the same pairs

2-connectivity is invariant under renaming edges, merging parallel edges, and dropping an edge
that duplicates another — none of which a `Graph` isomorphism captures, since the edge type is
fixed. `SameLinks` is the equivalence that does capture them, and it is exactly what the
overlay's orient-and-dedup step needs.

This is general graph theory and belongs in `Schoenflies/Graph/Walk.lean` beside `IsWalk.mono`;
it is here only because it was needed here first. -/

namespace Schoenflies

/-! ## The overlay graph is a piece-list graph

`overlayGraph pieces points` and `pieceListGraph (overlayPieces pieces points)` are the same
structure with the same fields, so the equation is `rfl`. Saying it once lets every lemma of
`Schoenflies/SquareMeshConnected.lean` about `pieceListGraph` — in particular
`pieceListGraph_union`, which turns "glue on another family of segments" into a list append —
apply to overlays. -/

/-! ### Orienting and deduplicating do not change which pairs are joined -/

/-! ## Subdividing an append

The blueprint's `Γ ∪ K` is, at the level of segment lists, a list append, and
`pieceListGraph_union` turns the graph union into that append. Subdivision has to commute with
it, which it does because a subdivision is a `flatMap`. -/

/-! ### A cut point on the drawing is a vertex

`Schoenflies/SimpleArc.lean` proves this for `overlayGraph`; the union argument runs on the raw
subdivision, where the same two facts — `subdivide_cover` and `subdivide_avoids` — give it. -/

/-! ## The union: the case "at least two common vertices"

`lem:union-two-connected`, in the form `prop:local-grid-attachment` uses it. The two families of
segments are overlaid together — one list append, one list of cut points — and the two distinct
common points are supplied as points that lie on *both* families and are cut. -/

/-! ## The crosscut of a face

The two degenerate cases of `prop:local-grid-attachment` — no common vertex, and exactly one —
both build an auxiliary crosscut `E` of a face `F` of `Γ`: *"the component of `ℓ ∩ F` containing
the relative interior of `J` is a bounded open interval in `ℓ`; its closure `E` is a line segment
with two distinct endpoints on `∂F` and interior in `F`. Hence `E` is an ear for `Γ`."*

`Schoenflies.Plane.exists_openSegment_eq_connectedComponentIn` is exactly that component, with
its two endpoints already placed on `frontier F`. What is added here is the clause the blueprint
needs next — *"since `E` contains `J`"* — in the form that makes it usable: **every** connected
piece of `ℓ ∩ F` through the chosen point is swallowed by the crosscut, because a connected
subset of a set lies inside one component of it. -/

variable {F : Set Plane} {a b y : Plane}

/-! ## Attaching the crosscut as an ear

`lem:subdivision-ear-preserve` (b) with the ear a single straight edge: once the crosscut's two
endpoints are vertices — which they are, being cut points of the overlay lying on `Γ` — the
segment joining them is a path graph of length one. -/

/-! ## The component-joining loop

*"If `|L| ∖ C` has more than one component, choose points in two of its components and join them
by a simple polygonal arc in `D` … Each round therefore strictly decreases the number of
components. Since there are only finitely many components, finitely many repetitions produce a
2-connected graph `H_n` for which `|H_n| ∖ C` is connected."*

Counting components and decrementing is one way to run that loop; picking one representative per
component and joining each to a fixed one is another, and it is the one that survives
formalisation, because it replaces "strictly decreases" by a single induction-free statement. The
finiteness the blueprint spends is what supplies the finite list `reps`. -/

/-! ## The construction

`prop:local-grid-attachment` is an existence statement, but its consumer —
`thm:finite-transfer`(a) — reads the graph, its drawing and its 2-connectivity by name. So the
graph is a `def` and every clause is a theorem about it. -/

theorem attachGraph_isDrawing {pieces : List Piece} (hnd : ∀ P ∈ pieces, P.Nondeg)
    (extra : List Plane) : Graph.IsDrawing (attachGraph pieces extra) segmentDrawing :=
  overlayGraph_isDrawing _ _ hnd (attachPoints_endsAreCut _ _) (attachPoints_meetsAreCut _ _)

@[simp] theorem attachGraph_pointSet (pieces : List Piece) (extra : List Plane) :
    Graph.pointSet (attachGraph pieces extra) segmentDrawing = cover pieces :=
  overlayGraph_pointSet _ _

/-! ### Clause 1: the open nonboundary part is connected

The joining loop, transported from sets to the graph. What the graph occupies is
`cover pieces` (`attachGraph_pointSet`), so the whole statement is about covers. -/

/-! ### Clause 2: the graph contains the grid, and clause 3: the grid is fine -/

theorem localGridEdges_nondeg {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    ∀ P ∈ localGridEdges p s k, P.Nondeg := fun _ hP =>
  gridEdges_nondeg ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk hP

/-! ### From the crosscut to two common vertices

*"Since `E` contains `J`, after subdivision `Γ ∪ E` and `K` have at least two common
vertices."* — the step that turns each degenerate case into the main one. Its content is the
swallowing clause of `exists_crosscut`: the grid edge's relative interior is a connected subset
of `ℓ ∩ F` through the chosen point, hence lies inside the crosscut's open part, hence the whole
closed grid edge lies inside the closed crosscut. -/

/-- **The crosscut contains the chosen grid edge.** -/
theorem seg_subset_crosscut {q₀ q₁ : Plane} {J : Piece}
    (hswallow : ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
      S ⊆ openSegment ℝ q₀ q₁)
    (hJline : J.interior ⊆ Plane.line a b ∩ F) (hy : y ∈ J.interior) :
    J.seg ⊆ segment ℝ q₀ q₁ := by
  have h1 : J.interior ⊆ openSegment ℝ q₀ q₁ :=
    hswallow _ (convex_openSegment _ _).isPreconnected hJline hy
  calc J.seg = closure J.interior := (closure_openSegment _ _).symm
    _ ⊆ closure (openSegment ℝ q₀ q₁) := closure_mono h1
    _ = segment ℝ q₀ q₁ := closure_openSegment _ _

/-! ## `prop:local-grid-attachment`, assembled

One graph, and each clause of the proposition a theorem about it. The graph is a `def` and not
an existential: `thm:finite-transfer`(a) takes `H` as an input and reads its drawing, its
2-connectivity and its point set separately. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransferTargetMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Anchored square meshes supply the boundary anchors for reverse finite transfer

`Schoenflies.TargetBoundaryAnchored` is the fixed geometric input isolated from finite-transfer
direction (b): every nonouter target edge ending on the model curve must end at the image of a
strongly accessible source anchor.

The anchored square mesh was built to have exactly this property.  Its clause 4,
`Schoenflies.squareMesh_inner_edge_at_fresh`, says that every mesh edge which meets the model
curve without lying in it meets the curve at one of the prescribed fresh points.  Thus, if the
fresh list consists of target images of strongly accessible source anchors, the whole boundary
condition follows with no ear-order argument.

## Blueprint

* `Schoenflies.targetBoundaryAnchored_squareMesh` — anchored-square-mesh clause 4 discharges the
  strong-accessibility input of reverse finite transfer.
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo` — mesh
  uniqueness and the local two-branch property of the generated outer cycle discharge the
  evolving fresh-incidence input.
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerCycle` — the preceding local
  property follows from one simple-cycle check on the base structure.
* `Schoenflies.isSourceExtension_relabelledSquareMesh_closedSquare` — edge relabelling and all
  fixed mesh clauses reduce the extension interface to the three actual subdivision statements.
* `Schoenflies.finite_transfer_toward_source_relabelledSquareMesh_of_outerCycle` — reverse
  transfer over any infinite abstract cell-name type.
* `Schoenflies.finite_transfer_toward_source_squareMesh` — direction (b) for an anchored square
  mesh, reduced only to the evolving fresh-incidence combinatorics.
* `Schoenflies.finite_transfer_toward_source_squareMesh_of_outerIncidenceAtMostTwo` — the same
  conclusion reduced to propagation of one static outer-cycle invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {S₀ : CellStructure Piece} {srcOuter srcDom tgtDom : Set Plane}

/-- The edges of any finite graph can be injectively renamed into an infinite type while
avoiding a prescribed finite set of names. -/
theorem exists_finiteGraph_edgeRelabeling_avoiding
    {β : Type*} (γ : Type*) [Infinite γ] (H : Graph Plane β) [H.Finite]
    (used : Set γ) (hused : used.Finite) :
    ∃ name : β → γ, InjOn name E(H) ∧ ∀ e ∈ E(H), name e ∉ used := by
  classical
  obtain ⟨freshName, hfreshName, havoid⟩ :=
    exists_injective_avoiding used hused E(H)
  let fallback : γ := Classical.choice (inferInstance : Nonempty γ)
  let name : β → γ := fun e =>
    if he : e ∈ E(H) then freshName ⟨e, he⟩ else fallback
  refine ⟨name, ?_, ?_⟩
  · intro e he g hg heg
    have hnames : freshName (⟨e, he⟩ : E(H)) = freshName ⟨g, hg⟩ := by
      dsimp only [name] at heg
      rw [dif_pos he, dif_pos hg] at heg
      exact heg
    exact congrArg Subtype.val (hfreshName hnames)
  · intro e he
    dsimp only [name]
    rw [dif_pos he]
    exact havoid (⟨e, he⟩ : E(H))

end Schoenflies
end

section
-- module Solutions.Q146_CD.TargetOverlay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Overlaying a target skeleton with the anchored square mesh

A fresh square mesh does not generally contain the current target skeleton: already at stage
zero the target has an arbitrary straight chord which need not be radial or lie on a mesh ring.
The ambient graph for reverse finite transfer must therefore be the polygonal overlay of the
two finite segment families.

`TargetSegmentCover` writes the whole current target skeleton as a finite exact segment cover.
It also remembers which old abstract edge supplied each segment; that provenance is what will
prove the subdivision clause after transverse intersections have been made vertices.

`TargetSegmentCover.meshOverlay` is the combined graph.  It overlays the target cover with the
already-subdivided edges of the anchored mesh, and its cut list contains both the mesh anchors
and every old target vertex.  The basic carrier, drawing, containment, edge-source, and
2-connectivity facts are established here.  The nonouter target-edge carriers form a canonical
finite connected cover of the old open skeleton.  A uniform positive width for this cover,
together with the radial mesh estimate, shows that every sufficiently fine dense mesh meets
every cover piece.  Consequently the combined overlay is a complete source extension at some
positive scale below `4`.  Relative boundary anchoring and no-new-nonouter-incidence are proved
for clean fresh lists and transported through edge relabelling, so the overlay now feeds directly
into reverse finite transfer.  `FreshDenseSelection.lean` constructs the required finite clean
separator list from the dense strongly-accessible boundary points and packages the resulting
reverse-transfer stage.

## Blueprint

* `Schoenflies.TargetSegmentCover` — the finite segment presentation of the current polygonal
  target skeleton.
* `Schoenflies.GeneratedPair.exists_targetSegmentCover` — every generated pair supplies that
  presentation.
* `Schoenflies.TargetSegmentCover.meshOverlay` — the current target skeleton overlaid with the
  anchored square mesh.
* `Schoenflies.TargetSegmentCover.meshOverlay_pointSet` — the combined graph occupies exactly
  the union of the two carriers.
* `Schoenflies.TargetSegmentCover.meshOverlay_isTwoConnected` — the two subdivision traces glue
  along two fresh boundary vertices to make the combined overlay 2-connected.
* `Schoenflies.TargetSegmentCover.noNewNonouterIncidenceAtBoundary_meshOverlay` — clean fresh
  spokes cannot create a second nonouter incidence against the current target trace.
* `Schoenflies.finiteOpenTargetCover` — the nonouter edge carriers, with the model curve
  removed, form a finite connected nontrivial cover of the old open target skeleton.
* `Schoenflies.exists_fine_openTarget_scale` — every generated target has a positive scale
  below `4` at which all pieces of that cover are wider than the mesh.
* `Schoenflies.TargetSegmentCover.exists_scale_isSourceExtension_relabelledMeshOverlay` — at
  that scale, every dense anchored mesh gives the complete relabelled source extension.
* `Schoenflies.TargetSegmentCover.finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle`
  — the accessible clean overlay performs the complete reverse finite transfer.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- A finite exact segment presentation of the target skeleton, with each segment traced back
to an old abstract edge. -/
structure TargetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) where
  /-- The straight segments covering the target skeleton. -/
  pieces : List Piece
  /-- No listed segment is degenerate. -/
  nondeg : ∀ Q ∈ pieces, Q.Nondeg
  /-- The listed segments occupy exactly the target skeleton. -/
  cover_eq : cover pieces = P.tgt.skeletonSet
  /-- Every listed segment came from one old target edge. -/
  source : ∀ Q ∈ pieces, ∃ e ∈ E(P.str.skel), Q.seg ⊆ edgeArc P.tgt.drawing e

namespace GeneratedPair

/-- Every generated pair has a finite segment presentation of its polygonal target skeleton. -/
theorem exists_targetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    Nonempty (TargetSegmentCover P) := by
  letI : Graph.Finite P.tgt.graph :=
    CellStructure.Realization.finite_graph P.tgt
  have hincident : ∀ z ∈ V(P.tgt.graph), ∃ e, P.tgt.graph.Inc e z := by
    intro z hz
    obtain ⟨w, hw, hwz, -⟩ :=
      P.tgt_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne z z
    obtain ⟨D, hD⟩ :=
      (P.tgt_isWeaklyAdmissible.isTwoConnected.connected.reaches hz hw).exists_isPath
    obtain ⟨e, -, hinc⟩ := hD.isWalk.exists_inc_source
      (hD.ne_nil (Ne.symm hwz))
    exact ⟨e, hinc⟩
  have hpoly : ∀ e ∈ E(P.tgt.graph), IsPolygonal (edgeArc P.tgt.drawing e) := by
    intro e he
    apply P.tgt_isPolygonal
    rwa [P.tgt.edgeSet_graph] at he
  obtain ⟨pieces, hnd, hcover, hsource⟩ :=
    P.tgt.isDrawing.exists_segmentCover (G := P.tgt.graph) hpoly hincident
  refine ⟨⟨pieces, hnd, hcover, ?_⟩⟩
  intro Q hQ
  obtain ⟨e, he, hsub⟩ := hsource Q hQ
  exact ⟨e, by rwa [P.tgt.edgeSet_graph] at he, hsub⟩

end GeneratedPair

namespace TargetSegmentCover

variable {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- The already-subdivided edges of the anchored square mesh, listed as straight pieces. -/
noncomputable def squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) : List Piece :=
  (squareMesh delta fresh anchors).edgeFinset.toList

@[simp] theorem mem_squareMeshPieces {delta : ℝ} {fresh anchors : List Plane} {R : Piece} :
    R ∈ squareMeshPieces delta fresh anchors ↔ R ∈ E(squareMesh delta fresh anchors) := by
  simp [squareMeshPieces, Graph.mem_edgeFinset]

/-- Listing the edges loses no carrier: every square-mesh vertex is an end of one of its
edges. -/
theorem cover_squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) :
    cover (squareMeshPieces delta fresh anchors) =
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_cover_iff.1 hx
    exact Or.inr (Set.mem_iUnion₂_of_mem (mem_squareMeshPieces.1 hR) (by
      rwa [edgeArc_segmentDrawing]))
  · intro hx
    rcases hx with hxV | hxE
    · obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hxV
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩
    · obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hxE
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rwa [← edgeArc_segmentDrawing]⟩

/-- The two source families for the combined target overlay. -/
noncomputable def meshPieces (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : List Piece :=
  Q.pieces ++ squareMeshPieces delta fresh anchors

/-- The target skeleton overlaid with the anchored square mesh.  Old vertices and prescribed
mesh anchors are explicitly included in the cut list. -/
noncomputable def meshOverlay (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : Graph Plane Piece :=
  attachGraph (Q.meshPieces delta fresh anchors)
    (anchors ++ P.tgt.graph.vertexFinset.toList)

instance meshOverlay_finite (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : (Q.meshOverlay delta fresh anchors).Finite :=
  attachGraph_finite _ _

/-- Every source segment of the combined overlay is nondegenerate. -/
theorem meshPieces_nondeg (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (delta : ℝ)
    (anchors : List Plane) :
    ∀ R ∈ Q.meshPieces delta fresh anchors, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact meshGraph_edge_nondeg (two_le_meshCount delta) hfresh
      (mem_squareMeshPieces.1 hR)

/-- The combined overlay is a finite straight-line plane graph. -/
theorem meshOverlay_isDrawing (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (Q.meshOverlay delta fresh anchors) segmentDrawing :=
  attachGraph_isDrawing (Q.meshPieces_nondeg hfresh delta anchors) _

/-- The combined overlay occupies exactly the current target skeleton together with the square
mesh. -/
theorem meshOverlay_pointSet (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing =
      P.tgt.skeletonSet ∪
        Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  rw [meshOverlay, attachGraph_pointSet, meshPieces, cover_append, Q.cover_eq,
    cover_squareMeshPieces]

/-- The whole anchored square mesh is contained in the combined overlay. -/
theorem squareMesh_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_right

/-- The sharper edge-source dichotomy used at the boundary: a mesh-sourced overlay edge lies
inside one actual edge of the already-subdivided square mesh. -/
theorem meshOverlay_edge_source_squareMesh (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ E(Q.meshOverlay delta fresh anchors)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ E(squareMesh delta fresh anchors), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · exact Or.inr ⟨A, mem_squareMeshPieces.1 hA, hsub⟩

/-- Two subsegments of one nondegenerate segment that start at the same end are comparable by
inclusion. -/
theorem segments_from_common_end_comparable {z a r s : Plane} (hza : z ≠ a)
    (hr : r ∈ segment ℝ z a) (hs : s ∈ segment ℝ z a) :
    segment ℝ z r ⊆ segment ℝ z s ∨ segment ℝ z s ⊆ segment ℝ z r := by
  rcases le_total (dist z r) (dist z s) with hrs | hsr
  · apply Or.inl
    apply (convex_segment z s).segment_subset (left_mem_segment ℝ z s)
    exact mem_segment_of_dist_le hza (left_mem_segment ℝ z a) hs hr
      (by simp) hrs
  · apply Or.inr
    apply (convex_segment z r).segment_subset (left_mem_segment ℝ z r)
    exact mem_segment_of_dist_le hza (left_mem_segment ℝ z a) hr hs
      (by simp) hsr

/-- Two pieces contained in the same nondegenerate source piece and sharing one of its ends
are comparable.  This is the piece-level form needed to identify two overlay fragments cut
from the unique square-mesh spoke at a fresh boundary point. -/
theorem piece_segments_comparable_of_common_source_end
    {A R S : Piece} {z : Plane} (hA : A.Nondeg)
    (hzA : z = A.1 ∨ z = A.2) (hRA : R.seg ⊆ A.seg) (hSA : S.seg ⊆ A.seg)
    (hzR : z = R.1 ∨ z = R.2) (hzS : z = S.1 ∨ z = S.2) :
    R.seg ⊆ S.seg ∨ S.seg ⊆ R.seg := by
  obtain ⟨a, hAseg, hza⟩ : ∃ a, A.seg = segment ℝ z a ∧ z ≠ a := by
    rcases hzA with hzA | hzA
    · refine ⟨A.2, ?_, ?_⟩
      · simp only [Piece.seg, hzA]
      · intro h
        exact hA (hzA.symm.trans h)
    · refine ⟨A.1, ?_, ?_⟩
      · simp only [Piece.seg, hzA, segment_symm]
      · intro h
        exact hA (h.symm.trans hzA)
  obtain ⟨r, hRseg, hrA⟩ : ∃ r, R.seg = segment ℝ z r ∧ r ∈ A.seg := by
    rcases hzR with hzR | hzR
    · exact ⟨R.2, by simp only [Piece.seg, hzR],
        hRA (right_mem_segment ℝ R.1 R.2)⟩
    · exact ⟨R.1, by simp only [Piece.seg, hzR, segment_symm],
        hRA (left_mem_segment ℝ R.1 R.2)⟩
  obtain ⟨s, hSseg, hsA⟩ : ∃ s, S.seg = segment ℝ z s ∧ s ∈ A.seg := by
    rcases hzS with hzS | hzS
    · exact ⟨S.2, by simp only [Piece.seg, hzS],
        hSA (right_mem_segment ℝ S.1 S.2)⟩
    · exact ⟨S.1, by simp only [Piece.seg, hzS, segment_symm],
        hSA (left_mem_segment ℝ S.1 S.2)⟩
  rw [hRseg, hSseg]
  exact segments_from_common_end_comparable hza (hAseg ▸ hrA) (hAseg ▸ hsA)

/-- Fresh mesh anchors avoid the carriers of all old nonouter target edges.  This is the
finite cleanliness condition which separates a genuinely new spoke from the current target
trace at the distinguished boundary. -/
def FreshAvoidsTargetNonouterEdges
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (fresh : List Plane) : Prop :=
  ∀ z ∈ fresh, ∀ e ∈ E(P.str.skel), e ∉ E(P.str.outerGraph) →
    z ∉ edgeArc P.tgt.drawing e

/-- A nonouter target edge can meet the distinguished boundary only at an old target vertex.
This turns the cleanliness requirement into avoidance of one finite vertex set. -/
theorem mem_targetVertex_of_mem_nonouter_edgeArc_modelCurve
    {e : γ} (he : e ∈ E(P.str.skel)) (heNotOuter : e ∉ E(P.str.outerGraph))
    {z : Plane} (hze : z ∈ edgeArc P.tgt.drawing e) (hz : z ∈ modelCurve) :
    z ∈ V(P.tgt.graph) := by
  have hzOuter : z ∈ P.tgt.outerSet := by
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  rcases hzOuter with hzV | hzE
  · exact (P.str.outerGraph_le.map P.tgt.pos).vertexSet_mono hzV
  · obtain ⟨f, hfOuter, hzf⟩ := Set.mem_iUnion₂.1 hzE
    have hf : f ∈ E(P.str.outerGraph) := by
      rwa [Graph.edgeSet_map] at hfOuter
    have heTgt : e ∈ E(P.tgt.graph) := by rwa [P.tgt.edgeSet_graph]
    have hfTgt : f ∈ E(P.tgt.graph) := by
      rw [P.tgt.edgeSet_graph]
      exact P.str.outerGraph_le.edgeSet_mono hf
    exact (P.tgt.isDrawing.edge_inter heTgt hfTgt
      (fun hef => heNotOuter (hef ▸ hf)) hze hzf).1

/-- Avoiding the finite old target vertex set is sufficient for clean fresh anchors. -/
theorem freshAvoidsTargetNonouterEdges_of_avoids_targetVertices
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (havoid : ∀ z ∈ fresh, z ∉ V(P.tgt.graph)) :
    FreshAvoidsTargetNonouterEdges P fresh := by
  intro z hzFresh e he heNotOuter hze
  exact havoid z hzFresh
    (mem_targetVertex_of_mem_nonouter_edgeArc_modelCurve he heNotOuter hze
      (hfresh z hzFresh))

/-- Incidence with an edge of the target/mesh overlay means being one of the two endpoints of
that piece. -/
theorem meshOverlay_inc_endpoint (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece} {z : Plane}
    (hinc : (Q.meshOverlay delta fresh anchors).Inc R z) :
    z = R.1 ∨ z = R.2 := by
  obtain ⟨w, hw⟩ := hinc
  change (overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList))).IsLink R z w at hw
  rcases (overlayGraph_isLink.1 hw).2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- The relative boundary anchoring of the overlay survives its injective edge renaming. -/
theorem newTargetBoundaryAnchored_relabelledMeshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    NewTargetBoundaryAnchored P P.tgt.skeletonSet
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  intro B hBH hbase d z hd hdnew hinc hz hnot
  obtain ⟨R, hR, rfl⟩ := hd
  obtain ⟨R', hR', hR'name, hR'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name R) z).1 hinc
  have hR'R : R' = R := hname hR' hR hR'name
  subst R'
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hdrawRelabelled := hdraw.relabelEdges hname
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hR'inc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  have hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve := by
    intro hsub
    apply hnot
    rwa [Graph.edgeArc_relabelDrawing hname hR]
  rcases Q.meshOverlay_edge_source_squareMesh hR with hOld | hMesh
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase :
        edgeArc ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
          (name R) ⊆ P.tgt.skeletonSet := by
      rw [Graph.edgeArc_relabelDrawing hname hR, edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hdnew (edge_mem_of_edgeArc_subset_pointSet hdrawRelabelled hBH
      ⟨R, hR, rfl⟩ (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hRnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hinter, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hinter ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    rw [hzw]
    exact hstrong w hwFresh

/-- A quantitative local-width condition on the old open target skeleton.  Every point lies in
a connected subset containing two points farther apart than the proposed mesh scale. -/
def OpenTargetLocallyWiderThan (P : GeneratedPair S₀ srcOuter srcDom modelCurve
    (Plane.closedSquare 0 1)) (delta : ℝ) : Prop :=
  ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
    ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
      IsPreconnected A ∧ z ∈ A ∧
        ∃ x ∈ A, ∃ y ∈ A, delta < dist x y

/-- Finitely many nontrivial connected pieces cover the old open target skeleton.  This is the
purely target-side finiteness datum from which a uniform positive mesh scale is extracted. -/
structure FiniteOpenTargetCover
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) where
  /-- The connected pieces. -/
  pieces : List (Set Plane)
  /-- Every open-skeleton point lies in one listed piece. -/
  covers : ∀ z ∈ P.tgt.skeletonSet \ modelCurve, ∃ A ∈ pieces, z ∈ A
  /-- Every listed piece lies in the old open skeleton. -/
  subset_open : ∀ A ∈ pieces, A ⊆ P.tgt.skeletonSet \ modelCurve
  /-- Every listed piece is connected. -/
  preconnected : ∀ A ∈ pieces, IsPreconnected A
  /-- No listed piece is a singleton. -/
  nontrivial : ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, x ≠ y

/-- The interior of a nondegenerate arc contains two distinct points. -/
theorem IsArcBetween.exists_two_mem_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) :
    ∃ x ∈ A \ {p, q}, ∃ y ∈ A \ {p, q}, x ≠ y := by
  obtain ⟨f, -, hinj, himage, hzero, hone⟩ := h
  let x := f (1 / 3)
  let y := f (2 / 3)
  have hxI : (1 / 3 : ℝ) ∈ unitInterval := by norm_num [unitInterval]
  have hyI : (2 / 3 : ℝ) ∈ unitInterval := by norm_num [unitInterval]
  have hzeroI : (0 : ℝ) ∈ unitInterval := zero_mem_I
  have honeI : (1 : ℝ) ∈ unitInterval := one_mem_I
  have hxA : x ∈ A := by
    rw [← himage]
    exact ⟨1 / 3, hxI, rfl⟩
  have hyA : y ∈ A := by
    rw [← himage]
    exact ⟨2 / 3, hyI, rfl⟩
  have hxEnds : x ∉ ({p, q} : Set Plane) := by
    rintro (hxp | hxq)
    · have hfun : f (1 / 3) = f 0 := by
        calc f (1 / 3) = x := rfl
          _ = p := hxp
          _ = f 0 := hzero.symm
      have : (1 / 3 : ℝ) = 0 := hinj hxI hzeroI hfun
      norm_num at this
    · have hxq' : x = q := by simpa using hxq
      have hfun : f (1 / 3) = f 1 := by
        calc f (1 / 3) = x := rfl
          _ = q := hxq'
          _ = f 1 := hone.symm
      have : (1 / 3 : ℝ) = 1 := hinj hxI honeI hfun
      norm_num at this
  have hyEnds : y ∉ ({p, q} : Set Plane) := by
    rintro (hyp | hyq)
    · have hfun : f (2 / 3) = f 0 := by
        calc f (2 / 3) = y := rfl
          _ = p := hyp
          _ = f 0 := hzero.symm
      have : (2 / 3 : ℝ) = 0 := hinj hyI hzeroI hfun
      norm_num at this
    · have hyq' : y = q := by simpa using hyq
      have hfun : f (2 / 3) = f 1 := by
        calc f (2 / 3) = y := rfl
          _ = q := hyq'
          _ = f 1 := hone.symm
      have : (2 / 3 : ℝ) = 1 := hinj hyI honeI hfun
      norm_num at this
  refine ⟨x, ⟨hxA, hxEnds⟩, y, ⟨hyA, hyEnds⟩, ?_⟩
  intro hxy
  have : (1 / 3 : ℝ) = 2 / 3 := hinj hxI hyI hxy
  norm_num at this

/-- The finite family of nonouter target-edge carriers, with the model curve removed. -/
noncomputable def openTargetEdgePieces
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    List (Set Plane) := by
  classical
  letI : P.str.skel.Finite :=
    ⟨P.str.finite_vertexSet, P.str.finite_edgeSet⟩
  exact (P.str.skel.edgeFinset.filter fun e => e ∉ E(P.str.outerGraph)).toList.map
    fun e => edgeArc P.tgt.drawing e \ modelCurve

@[simp] theorem mem_openTargetEdgePieces
    {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}
    {A : Set Plane} :
    A ∈ openTargetEdgePieces P ↔
      ∃ e ∈ E(P.str.skel), e ∉ E(P.str.outerGraph) ∧
        A = edgeArc P.tgt.drawing e \ modelCurve := by
  letI : P.str.skel.Finite :=
    ⟨P.str.finite_vertexSet, P.str.finite_edgeSet⟩
  simp only [openTargetEdgePieces, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Graph.mem_edgeFinset]
  constructor
  · rintro ⟨e, ⟨he, hnot⟩, hEq⟩
    exact ⟨e, he, hnot, hEq.symm⟩
  · rintro ⟨e, he, hnot, hEq⟩
    exact ⟨e, ⟨he, hnot⟩, hEq.symm⟩

/-- The nonouter edge carriers form a finite connected, nontrivial cover of the whole old open
target skeleton. -/
noncomputable def finiteOpenTargetCover
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    FiniteOpenTargetCover P where
  pieces := openTargetEdgePieces P
  covers := by
    intro z hz
    have edge_mem_open : ∀ {e : γ}, e ∈ E(P.str.skel) →
        e ∉ E(P.str.outerGraph) → z ∈ edgeArc P.tgt.drawing e →
        ∃ A ∈ openTargetEdgePieces P, z ∈ A := by
      intro e he hnot hze
      refine ⟨edgeArc P.tgt.drawing e \ modelCurve,
        mem_openTargetEdgePieces.2 ⟨e, he, hnot, rfl⟩, hze, hz.2⟩
    rcases hz.1 with hzV | hzE
    · rw [P.tgt.vertexSet_graph] at hzV
      obtain ⟨v, hv, rfl⟩ := hzV
      have hvNotOuter : v ∉ V(P.str.outerGraph) := by
        intro hvOuter
        have hmem : P.tgt.pos v ∈ P.tgt.outerSet := Or.inl (by
          rw [Graph.vertexSet_map]
          exact ⟨v, hvOuter, rfl⟩)
        rw [P.tgt_isWeaklyAdmissible.outerSet_eq] at hmem
        exact hz.2 hmem
      obtain ⟨w, hw, hwv, -⟩ :=
        P.tgt_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne
          (P.tgt.pos v) (P.tgt.pos v)
      have hvReal : P.tgt.pos v ∈ V(P.tgt.graph) := by
        rw [P.tgt.vertexSet_graph]
        exact ⟨v, hv, rfl⟩
      obtain ⟨D, hD⟩ :=
        (P.tgt_isWeaklyAdmissible.isTwoConnected.connected.reaches hvReal hw).exists_isPath
      obtain ⟨e, -, hinc⟩ := hD.isWalk.exists_inc_source
        (hD.ne_nil (Ne.symm hwv))
      change (P.str.skel.map P.tgt.pos).Inc e (P.tgt.pos v) at hinc
      rw [Graph.map_inc] at hinc
      obtain ⟨a, hinca, hva⟩ := hinc
      have hav : v = a := P.tgt.injOn_pos hv hinca.vertex_mem hva
      have hincv : P.str.skel.Inc e v := by rwa [hav]
      obtain ⟨b, hab⟩ := hincv
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        have hlinkOuter := isLink_of_le_of_mem_edgeSet P.str.outerGraph_le heOuter hab
        exact hvNotOuter hlinkOuter.left_mem
      apply edge_mem_open hab.edge_mem heNotOuter
      have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
      exact hArc.left_mem
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      have heS : e ∈ E(P.str.skel) := by rwa [P.tgt.edgeSet_graph] at he
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        have hmem : z ∈ P.tgt.outerSet := Or.inr (Set.mem_iUnion₂_of_mem (by
          rw [Graph.edgeSet_map]
          exact heOuter) hze)
        rw [P.tgt_isWeaklyAdmissible.outerSet_eq] at hmem
        exact hz.2 hmem
      exact edge_mem_open heS heNotOuter hze
  subset_open := by
    intro A hA
    obtain ⟨e, he, ⟨-, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    exact Set.sdiff_subset_sdiff_left (Graph.edgeArc_subset_pointSet (by
      rwa [P.tgt.edgeSet_graph]))
  preconnected := by
    intro A hA
    obtain ⟨e, he, ⟨heNotOuter, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
    have hcell : P.tgt.cell e =
        edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} := P.tgt.cell_edge hab
    apply hArc.isPreconnected_diff.subset_closure
    · intro x hx
      have hxCell : x ∈ P.tgt.cell e := by
        rw [hcell]
        exact hx
      exact ⟨hx.1, (P.tgt_isWeaklyAdmissible.cell_subset he heNotOuter hxCell).2⟩
    · rw [Schoenflies.IsArcBetween.closure_diff_eq hArc]
      exact Set.sdiff_subset
  nontrivial := by
    intro A hA
    obtain ⟨e, he, ⟨heNotOuter, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
    obtain ⟨x, hx, y, hy, hxy⟩ := IsArcBetween.exists_two_mem_diff hArc
    have hcell : P.tgt.cell e =
        edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} := P.tgt.cell_edge hab
    have hsub : edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} ⊆
        edgeArc P.tgt.drawing e \ modelCurve := by
      intro u hu
      have huCell : u ∈ P.tgt.cell e := by
        rw [hcell]
        exact hu
      exact ⟨hu.1, (P.tgt_isWeaklyAdmissible.cell_subset he heNotOuter huCell).2⟩
    exact ⟨x, hsub hx, y, hsub hy, hxy⟩

/-- A finite list of nontrivial sets has a uniform positive lower bound on one pairwise
distance chosen from each set. -/
theorem exists_uniform_piece_width (pieces : List (Set Plane))
    (hnontrivial : ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, x ≠ y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, delta < dist x y := by
  induction pieces with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons A pieces ih =>
      have htail : ∀ B ∈ pieces, ∃ x ∈ B, ∃ y ∈ B, x ≠ y :=
        fun B hB => hnontrivial B (List.mem_cons_of_mem A hB)
      obtain ⟨delta, hdelta, hwide⟩ := ih htail
      obtain ⟨x, hx, y, hy, hxy⟩ := hnontrivial A (List.mem_cons_self ..)
      let epsilon := min (delta / 2) (dist x y / 2)
      have hdist : 0 < dist x y := dist_pos.2 hxy
      have hepsilon : 0 < epsilon := by
        dsimp only [epsilon]
        positivity
      refine ⟨epsilon, hepsilon, ?_⟩
      intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · refine ⟨x, hx, y, hy, ?_⟩
        dsimp only [epsilon]
        linarith [min_le_right (delta / 2) (dist x y / 2)]
      · obtain ⟨u, hu, v, hv, huv⟩ := hwide B hB
        refine ⟨u, hu, v, hv, ?_⟩
        dsimp only [epsilon]
        linarith [min_le_left (delta / 2) (dist x y / 2)]

/-- A finite open-target cover supplies a positive scale at which every open-skeleton point
has a connected neighborhood wider than the mesh. -/
theorem FiniteOpenTargetCover.exists_locallyWiderThan
    (C : FiniteOpenTargetCover P) :
    ∃ delta : ℝ, 0 < delta ∧ OpenTargetLocallyWiderThan P delta := by
  obtain ⟨delta, hdelta, hwide⟩ :=
    exists_uniform_piece_width C.pieces C.nontrivial
  refine ⟨delta, hdelta, ?_⟩
  intro z hz
  obtain ⟨A, hA, hzA⟩ := C.covers z hz
  obtain ⟨x, hx, y, hy, hxy⟩ := hwide A hA
  exact ⟨A, C.subset_open A hA, C.preconnected A hA, hzA, x, hx, y, hy, hxy⟩

/-- The local-width condition is preserved when the proposed mesh scale is decreased. -/
theorem OpenTargetLocallyWiderThan.mono
    {delta epsilon : ℝ} (h : OpenTargetLocallyWiderThan P delta)
    (hle : epsilon ≤ delta) : OpenTargetLocallyWiderThan P epsilon := by
  intro z hz
  obtain ⟨A, hA, hconn, hzA, x, hx, y, hy, hxy⟩ := h z hz
  exact ⟨A, hA, hconn, hzA, x, hx, y, hy, lt_of_le_of_lt hle hxy⟩

/-- The locally-wide scale may be chosen below any prescribed positive bound. -/
theorem exists_fine_openTarget_scale_lt
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧ delta < bound ∧
      OpenTargetLocallyWiderThan P delta := by
  obtain ⟨delta, hdelta, hwide⟩ :=
    (finiteOpenTargetCover P).exists_locallyWiderThan
  let epsilon := min delta (min 1 (bound / 2))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  refine ⟨epsilon, hepsilon,
    lt_of_le_of_lt (min_le_of_right_le (min_le_left 1 (bound / 2))) (by norm_num),
    ?_, hwide.mono (min_le_left delta (min 1 (bound / 2)))⟩
  have hle : epsilon ≤ bound / 2 :=
    (min_le_right delta (min 1 (bound / 2))).trans (min_le_right 1 (bound / 2))
  linarith

/-- Fresh cell names for every edge of the combined target overlay, avoiding all names already
used by the current generated structure. -/
theorem exists_meshOverlay_edgeRelabeling
    [Infinite γ] (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) :
    ∃ name : Piece → γ, InjOn name E(Q.meshOverlay delta fresh anchors) ∧
      ∀ e ∈ E(Q.meshOverlay delta fresh anchors), name e ∉ P.str.cells :=
  exists_finiteGraph_edgeRelabeling_avoiding γ (Q.meshOverlay delta fresh anchors)
    P.str.cells P.str.finite_cells

end TargetSegmentCover

end Schoenflies
end

section
-- module Solutions.Q146_CD.FreshDenseSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Selecting a finite dense list of fresh boundary anchors

`FreshDense fresh delta` is the order-free condition used by the anchored square mesh: every
connected subset of the model curve avoiding `fresh` has diameter at most `delta / 2`.

A dense set of eligible anchors contains a finite list with this property.  For each pair of
model-curve points at distance at least `delta / 2`, two eligible anchors separate the pair.
The same anchors separate every nearby pair, because the complementary sides of the associated
cut arcs are open.  The far-pair set is compact, so finitely many such neighborhoods cover it.
Any connected set avoiding all selected anchors must therefore have the required diameter.

## Blueprint

* `Schoenflies.exists_finite_freshDense_of_dense` — a dense eligible subset of the model curve
  supplies a finite `FreshDense` list at every positive scale.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData` — the complete output of one
  reverse overlay-transfer stage, packaged for the stage recursion.
* `Schoenflies.TargetSegmentCover.nonempty_meshOverlayTransferData_inside` — in the standard
  closed Jordan domain, separation and the outer-cycle invariant construct that stage data.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData.diam_targetStar_lt` — the transferred
  target stars have diameter less than twice the selected mesh scale.
-/

open Metric Set Topology
open scoped Graph

namespace Schoenflies

/-- Removing finitely many forbidden points from a relatively dense subset of a Jordan curve
leaves it relatively dense.  The proof works in the curve subtype, which is a nontrivial
connected T₁ space and therefore has no isolated points. -/
theorem IsJordanCurve.subset_closure_sdiff_finite
    {C eligible forbidden : Set Plane} (hC : IsJordanCurve C)
    (heligible : eligible ⊆ C) (hdense : C ⊆ closure eligible)
    (hforbidden : forbidden.Finite) : C ⊆ closure (eligible \ forbidden) := by
  let eligible' : Set C := {x | x.1 ∈ eligible}
  let forbidden' : Set C := {x | x.1 ∈ forbidden}
  have heligibleImage : ((↑) : C → Plane) '' eligible' = eligible := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, heligible hx⟩, hx, rfl⟩
  have heligibleDense : Dense eligible' := by
    rw [Subtype.dense_iff, heligibleImage]
    exact hdense
  have hforbiddenFinite : forbidden'.Finite := by
    apply hforbidden.preimage
    exact Set.injOn_of_injective Subtype.val_injective
  letI : ConnectedSpace C := Subtype.connectedSpace hC.isConnected
  letI : Nontrivial C := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hC.exists_ne
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  have hcleanDense : Dense (eligible' \ forbidden') :=
    heligibleDense.sdiff_finite hforbiddenFinite
  rw [Subtype.dense_iff] at hcleanDense
  have hcleanImage : ((↑) : C → Plane) '' (eligible' \ forbidden') =
      eligible \ forbidden := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyEligible, hyForbidden⟩, rfl⟩
      exact ⟨hyEligible, hyForbidden⟩
    · rintro ⟨hxEligible, hxForbidden⟩
      exact ⟨⟨x, heligible hxEligible⟩, ⟨hxEligible, hxForbidden⟩, rfl⟩
  rwa [hcleanImage] at hcleanDense

/-- A dense eligible subset of the model curve contains a finite list which separates every
pair of model-curve points at distance more than `delta / 2`. -/
theorem exists_finite_freshDense_of_dense {eligible : Set Plane}
    (heligible : eligible ⊆ modelCurve) (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧ FreshDense fresh delta := by
  classical
  let farPairs : Set (Plane × Plane) :=
    modelCurve ×ˢ modelCurve ∩
      {q | delta / 2 ≤ dist q.1 q.2}
  have hfarClosed : IsClosed {q : Plane × Plane | delta / 2 ≤ dist q.1 q.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hfarCompact : IsCompact farPairs :=
    (isCompact_modelCurve.prod isCompact_modelCurve).inter_right hfarClosed
  have hseparate : ∀ q : farPairs,
      ∃ a ∈ eligible, ∃ b ∈ eligible, ∃ A₁ A₂ : Set Plane,
        a ≠ b ∧ IsCutPair modelCurve a b A₁ A₂ ∧
          q.1.1 ∈ A₁ ∧ q.1.1 ∉ A₂ ∧ q.1.2 ∈ A₂ ∧ q.1.2 ∉ A₁ := by
    intro q
    have hqCurve : q.1.1 ∈ modelCurve ∧ q.1.2 ∈ modelCurve := q.2.1
    have hqne : q.1.1 ≠ q.1.2 := by
      intro h
      have hle := q.2.2
      change delta / 2 ≤ dist q.1.1 q.1.2 at hle
      rw [h, dist_self] at hle
      linarith
    exact exists_separating_anchors isJordanCurve_modelCurve heligible hdense
      hqCurve.1 hqCurve.2 hqne
  choose a haEligible b hbEligible A₁ A₂ hab hcut hxA₁ hxA₂ hyA₂ hyA₁ using hseparate
  let U : farPairs → Set (Plane × Plane) := fun q => (A₂ q)ᶜ ×ˢ (A₁ q)ᶜ
  have hUopen : ∀ q, IsOpen (U q) := by
    intro q
    exact hcut q |>.snd.isArc.isClosed.isOpen_compl.prod
      (hcut q |>.fst.isArc.isClosed.isOpen_compl)
  have hfarCover : farPairs ⊆ ⋃ q, U q := by
    intro q hq
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hxA₂ ⟨q, hq⟩, hyA₁ ⟨q, hq⟩⟩
  obtain ⟨indices, hindices⟩ :=
    hfarCompact.elim_finite_subcover U hUopen hfarCover
  let fresh : List Plane := indices.toList.flatMap fun q => [a q, b q]
  refine ⟨fresh, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq, hzq⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzq
    rcases hzq with rfl | rfl
    · exact haEligible q
    · exact hbEligible q
  · intro S hS hSconn x hx y hy
    by_contra hxy
    have hxyFar : delta / 2 ≤ dist x y := le_of_not_ge hxy
    have hpair : (x, y) ∈ farPairs := by
      exact ⟨⟨(hS hx).1, (hS hy).1⟩, hxyFar⟩
    obtain ⟨q, hqIndices, hqU⟩ := Set.mem_iUnion₂.1 (hindices hpair)
    have hqList : q ∈ indices.toList := by simpa using hqIndices
    have haFresh : a q ∈ fresh := by
      apply List.mem_flatMap.2
      exact ⟨q, hqList, by simp⟩
    have hbFresh : b q ∈ fresh := by
      apply List.mem_flatMap.2
      exact ⟨q, hqList, by simp⟩
    have haNotS : a q ∉ S := by
      intro haS
      exact (hS haS).2 haFresh
    have hbNotS : b q ∉ S := by
      intro hbS
      exact (hS hbS).2 hbFresh
    have hScover : S ⊆ (A₂ q)ᶜ ∪ (A₁ q)ᶜ := by
      intro z hzS
      have hzCurve : z ∈ modelCurve := (hS hzS).1
      have hzUnion : z ∈ A₁ q ∪ A₂ q := by
        rw [hcut q |>.union_eq]
        exact hzCurve
      rcases hzUnion with hzA₁ | hzA₂
      · by_cases hzA₂ : z ∈ A₂ q
        · have hzEnds : z ∈ ({a q, b q} : Set Plane) := by
            rw [← hcut q |>.inter_eq]
            exact ⟨hzA₁, hzA₂⟩
          rcases hzEnds with rfl | rfl
          · exact (haNotS hzS).elim
          · exact (hbNotS hzS).elim
        · exact Or.inl hzA₂
      · by_cases hzA₁ : z ∈ A₁ q
        · have hzEnds : z ∈ ({a q, b q} : Set Plane) := by
            rw [← hcut q |>.inter_eq]
            exact ⟨hzA₁, hzA₂⟩
          rcases hzEnds with rfl | rfl
          · exact (haNotS hzS).elim
          · exact (hbNotS hzS).elim
        · exact Or.inr hzA₁
    have hxOpen : x ∈ (A₂ q)ᶜ := hqU.1
    have hyOpen : y ∈ (A₁ q)ᶜ := hqU.2
    obtain ⟨z, hzS, hzA₂, hzA₁⟩ := hSconn
      (A₂ q)ᶜ (A₁ q)ᶜ
      (hcut q |>.snd.isArc.isClosed.isOpen_compl)
      (hcut q |>.fst.isArc.isClosed.isOpen_compl) hScover
      ⟨x, hx, hxOpen⟩ ⟨y, hy, hyOpen⟩
    have hzUnion : z ∈ A₁ q ∪ A₂ q := by
      rw [hcut q |>.union_eq]
      exact (hS hzS).1
    exact hzUnion.elim hzA₁ hzA₂

/-- A finite boundary list is a metric net at scale `delta`.  This explicit consequence is
retained for the boundary-continuity construction; `FreshDense` itself is the order-free
connected-component estimate needed by the target mesh. -/
def FreshNet (fresh : List Plane) (delta : ℝ) : Prop :=
  ∀ x ∈ modelCurve, ∃ z ∈ fresh, dist x z < delta

theorem FreshDense.mono {fresh fresh' : List Plane} {delta : ℝ}
    (h : FreshDense fresh delta) (hsub : ∀ z ∈ fresh, z ∈ fresh') :
    FreshDense fresh' delta := by
  intro A hA hAconn x hx y hy
  apply h A _ hAconn x hx y hy
  intro z hz
  have hz' := hA hz
  exact ⟨hz'.1, fun hzf => hz'.2 (hsub z hzf)⟩

theorem FreshNet.mono {fresh fresh' : List Plane} {delta : ℝ}
    (h : FreshNet fresh delta) (hsub : ∀ z ∈ fresh, z ∈ fresh') :
    FreshNet fresh' delta := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := h x hx
  exact ⟨z, hsub z hz, hzx⟩

/-- A relatively dense eligible subset of the compact model curve supplies a finite metric
net consisting entirely of eligible points. -/
theorem exists_finite_freshNet_of_dense {eligible : Set Plane}
    (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧ FreshNet fresh delta := by
  let U : eligible → Set Plane := fun z => ball (z : Plane) delta
  have hcover : modelCurve ⊆ ⋃ z, U z := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 (hdense hx) delta hdelta
    apply Set.mem_iUnion.2
    refine ⟨⟨z, hz⟩, ?_⟩
    exact mem_ball.2 hzx
  obtain ⟨indices, hindices⟩ :=
    isCompact_modelCurve.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  let fresh : List Plane := indices.toList.map Subtype.val
  refine ⟨fresh, ?_, ?_⟩
  · intro z hz
    change z ∈ indices.toList.map Subtype.val at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact w.property
  · intro x hx
    obtain ⟨z, hzi, hz⟩ := Set.mem_iUnion₂.1 (hindices hx)
    refine ⟨z, ?_, ?_⟩
    · apply List.mem_map.2
      exact ⟨z, by simpa using hzi, rfl⟩
    · exact mem_ball.1 hz

/-- The two finite selections can be combined without losing either property. -/
theorem exists_finite_freshDenseNet_of_dense {eligible : Set Plane}
    (heligible : eligible ⊆ modelCurve) (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧
      FreshDense fresh delta ∧ FreshNet fresh delta := by
  obtain ⟨dense, hdenseMem, hdenseProp⟩ :=
    exists_finite_freshDense_of_dense heligible hdense hdelta
  obtain ⟨net, hnetMem, hnetProp⟩ :=
    exists_finite_freshNet_of_dense hdense hdelta
  refine ⟨dense ++ net, ?_, hdenseProp.mono ?_, hnetProp.mono ?_⟩
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hdenseMem z hz
    · exact hnetMem z hz
  · exact fun z hz => List.mem_append_left _ hz
  · exact fun z hz => List.mem_append_right _ hz

/-! ### Fresh lists for a generated target overlay -/

namespace TargetSegmentCover

variable {S₀ : CellStructure γ} {srcOuter srcDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- Strongly accessible points on the source boundary. -/
def accessibleSourceBoundary
    (_P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    Set Plane :=
  {x | x ∈ srcOuter ∧ StronglyAccessible (srcDom \ srcOuter) x}

/-- Boundary points whose source-side preimages are strongly accessible. -/
def accessibleTargetBoundary
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    Set Plane :=
  {z | z ∈ modelCurve ∧
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)}

/-- Relative density of strongly accessible source-boundary points transports through the
current skeleton homeomorphism to relative density on the model curve. -/
theorem accessibleTargetBoundary_dense_of_source
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (hsource : srcOuter ⊆ closure (accessibleSourceBoundary P)) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) := by
  intro z hzCurve
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  have hzTgtOuter : z ∈ P.tgt.outerSet := by
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hzCurve
  have hzTgtSkeleton : z ∈ P.tgt.skeletonSet :=
    P.tgt.outerSet_subset_skeletonSet hzTgtOuter
  have hxSrcOuterSet : P.homeo.invFun z ∈ P.src.outerSet := by
    rw [← P.homeo.symm.image_outerSet]
    exact ⟨z, hzTgtOuter, rfl⟩
  have hxSrcOuter : P.homeo.invFun z ∈ srcOuter := by
    exact (Set.ext_iff.mp P.src_isWeaklyAdmissible.outerSet_eq _).mp
      hxSrcOuterSet
  have hxSrcSkeleton : P.homeo.invFun z ∈ P.src.skeletonSet :=
    P.src.outerSet_subset_skeletonSet hxSrcOuterSet
  have hright : P.homeo.toFun (P.homeo.invFun z) = z :=
    P.homeo.rightInvOn hzTgtSkeleton
  obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousWithinAt_iff.1
    (P.homeo.continuousOn_toFun _ hxSrcSkeleton) epsilon hepsilon
  obtain ⟨x, hxAccessible, hxdist⟩ :=
    Metric.mem_closure_iff.1 (hsource hxSrcOuter) delta hdelta
  have hxSrcOuterSet' : x ∈ P.src.outerSet := by
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hxAccessible.1
  have hxSrcSkeleton' : x ∈ P.src.skeletonSet :=
    P.src.outerSet_subset_skeletonSet hxSrcOuterSet'
  have hxTgtOuter : P.homeo.toFun x ∈ P.tgt.outerSet := by
    rw [← P.homeo.image_outerSet]
    exact ⟨x, hxSrcOuterSet', rfl⟩
  have hxCurve : P.homeo.toFun x ∈ modelCurve := by
    exact (Set.ext_iff.mp P.tgt_isWeaklyAdmissible.outerSet_eq _).mp
      hxTgtOuter
  have hleft : P.homeo.invFun (P.homeo.toFun x) = x :=
    P.homeo.leftInvOn hxSrcSkeleton'
  refine ⟨P.homeo.toFun x, ⟨hxCurve, ?_⟩, ?_⟩
  · rw [hleft]
    exact hxAccessible.2
  · have := hclose hxSrcSkeleton' (by rwa [dist_comm])
    rwa [hright, dist_comm] at this

/-- In the standard generated-pair setting, tangent density on the source region supplies the
density hypothesis needed by finite fresh-list selection. -/
theorem accessibleTargetBoundary_dense_of_region
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating srcOuter)
    (hregion : IsRegionOf srcOuter (srcDom \ srcOuter)) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) :=
  accessibleTargetBoundary_dense_of_source P (tangent_dense hsep hregion)

/-- For the closed Jordan domain used by the stage tower, the required source region is
literally `inside srcOuter`, so accessible target-boundary density follows from
separation of the source curve. -/
theorem accessibleTargetBoundary_dense_inside
    {C : Set Plane}
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating C) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) := by
  apply accessibleTargetBoundary_dense_of_region P hsep
  rw [union_inside_sdiff]
  exact IsRegionOf.inside C

/-- If accessible target-boundary points are relatively dense, then at every positive scale
there is a finite dense list of accessible points avoiding all old target vertices and hence
all old nonouter target-edge carriers. -/
theorem exists_clean_freshDense_of_accessibleTargetBoundary_dense
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane,
      (∀ z ∈ fresh, z ∈ modelCurve) ∧
      (∀ z ∈ fresh,
        StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) ∧
      FreshAvoidsTargetNonouterEdges P fresh ∧ FreshDense fresh delta ∧
      FreshNet fresh delta := by
  letI : Graph.Finite P.tgt.graph :=
    CellStructure.Realization.finite_graph P.tgt
  have haccessibleSubset : accessibleTargetBoundary P ⊆ modelCurve :=
    fun _ hz => hz.1
  have hcleanDense : modelCurve ⊆
      closure (accessibleTargetBoundary P \ V(P.tgt.graph)) :=
    isJordanCurve_modelCurve.subset_closure_sdiff_finite
      haccessibleSubset haccessible (Graph.finite_vertexSet (G := P.tgt.graph))
  obtain ⟨fresh, hfreshClean, hdense, hnet⟩ := exists_finite_freshDenseNet_of_dense
    (Set.sdiff_subset.trans haccessibleSubset) hcleanDense hdelta
  have hfresh : ∀ z ∈ fresh, z ∈ modelCurve := by
    intro z hz
    exact (hfreshClean z hz).1.1
  have hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z) := by
    intro z hz
    exact (hfreshClean z hz).1.2
  have havoidVertices : ∀ z ∈ fresh, z ∉ V(P.tgt.graph) := by
    intro z hz
    exact (hfreshClean z hz).2
  exact ⟨fresh, hfresh, hstrong,
    freshAvoidsTargetNonouterEdges_of_avoids_targetVertices hfresh havoidVertices,
    hdense, hnet⟩

/-- The complete finite data selected by one reverse overlay-transfer stage.  Packaging the
dependent edge relabelling and its transferred generated pair together makes this construction
directly usable by the stage recursion. -/
structure MeshOverlayTransferData (Q : TargetSegmentCover P) (anchors : List Plane) where
  /-- The positive mesh scale selected for this target. -/
  delta : ℝ
  /-- The finite accessible boundary-anchor list. -/
  fresh : List Plane
  delta_pos : 0 < delta
  delta_lt_four : delta < 4
  fresh_mem : ∀ z ∈ fresh, z ∈ modelCurve
  fresh_accessible : ∀ z ∈ fresh,
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)
  fresh_avoids : FreshAvoidsTargetNonouterEdges P fresh
  fresh_dense : FreshDense fresh delta
  /-- The selected points also form an explicit metric net on the target boundary. -/
  fresh_net : FreshNet fresh delta
  /-- Fresh abstract names for all edges of the finite overlay. -/
  name : Piece → γ
  name_inj : InjOn name E(Q.meshOverlay delta fresh anchors)
  /-- The generated pair after reverse transfer. -/
  pair : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)
  /-- The abstract parent map of the transfer. -/
  parent : γ → γ
  transfer : IsTargetTransferOf pair P
    ((Q.meshOverlay delta fresh anchors).relabelEdges name name_inj)
    ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) parent

namespace MeshOverlayTransferData

variable {Q : TargetSegmentCover P} {anchors : List Plane}

/-- Every target face created by the reverse overlay transfer has diameter below the selected
mesh scale.  The target cell is connected and misses the new skeleton, hence lies in one bounded
face of the contained square mesh; `squareMesh_face_small` supplies the bound. -/
theorem diam_closure_targetFace_lt (w : MeshOverlayTransferData Q anchors)
    {F : γ} (hF : F ∈ w.pair.str.faces) :
    Metric.diam (closure (w.pair.tgt.cell F)) < w.delta := by
  obtain ⟨z, hz⟩ := w.pair.tgt_isFaceJordan.nonempty hF
  have hzOpen : z ∈ Plane.openSquare 0 1 := by
    have hzInterior := w.pair.tgt_face_subset_interior hF hz
    rwa [closedSquare_sdiff_modelCurve] at hzInterior
  have hmeshSkel :
      Graph.pointSet (squareMesh w.delta w.fresh anchors) segmentDrawing ⊆
        w.pair.tgt.skeletonSet := by
    rw [w.transfer.skeletonSet_eq, Graph.pointSet_relabelEdges]
    exact Q.squareMesh_subset_meshOverlay w.delta w.fresh anchors
  have hcellExterior : w.pair.tgt.cell F ⊆
      Graph.exterior (squareMesh w.delta w.fresh anchors) segmentDrawing := by
    intro x hxCell hxMesh
    exact Set.disjoint_left.1
      (w.pair.tgt.disjoint_cell_skeletonSet w.pair.tgt_isCellDecomposition hF)
      hxCell (hmeshSkel hxMesh)
  have hzExterior :
      z ∈ Graph.exterior (squareMesh w.delta w.fresh anchors) segmentDrawing :=
    hcellExterior hz
  have hcellFace : w.pair.tgt.cell F ⊆
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z :=
    (w.pair.tgt_isFaceJordan.isConnected hF).isPreconnected.subset_connectedComponentIn
      hz hcellExterior
  have hfaceCurveCompl :
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z ⊆ modelCurveᶜ := by
    intro x hxFace hxCurve
    exact Graph.face_subset_exterior _ _ _ hxFace
      (modelCurve_subset_squareMesh_pointSet w.delta w.fresh anchors hxCurve)
  have hfaceOpen :
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z ⊆
        Plane.openSquare 0 1 := by
    have hcomp := (Graph.isConnected_face hzExterior).isPreconnected.subset_connectedComponentIn
      (Graph.mem_face hzExterior) hfaceCurveCompl
    rw [modelCurve_eq_frontier,
      connectedComponentIn_compl_frontier_closedSquare hzOpen] at hcomp
    exact hcomp
  have hfaceBounded : Bornology.IsBounded
      (Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z) :=
    (Plane.isBounded_closedSquare 0 1).subset
      (hfaceOpen.trans (Plane.openSquare_subset_closedSquare 0 1))
  have hsmall := squareMesh_face_small w.fresh_mem w.delta_pos w.fresh_dense
    hzExterior hfaceBounded
  calc
    Metric.diam (closure (w.pair.tgt.cell F)) =
        Metric.diam (w.pair.tgt.cell F) := Metric.diam_closure _
    _ ≤ Metric.diam
        (Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z) :=
      Metric.diam_mono hcellFace hfaceBounded
    _ < w.delta := hsmall.2

end MeshOverlayTransferData

end TargetSegmentCover

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.familySquare_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.EarStepData.pair_src _root_.Schoenflies.EarStepData.pair_tgt _root_.Schoenflies.GeneratedPair.split_str _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.attachGraph_pointSet _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The initial matched pair

The entry point of Part II (`prop:initial-pair`). `def:generated-structure` builds every later
stage from this one by two elementary operations, so the construction is exported as **data** —
one abstract `CellStructure`, two `Realization`s of it, and the `SkeletonHomeo` between them —
and not as an existentially packaged bundle. `Schoenflies.initial_pair` at the end is only a
restatement of the blueprint sentence; nothing should be consumed through it.

## The shape of the construction

The blueprint's `u : C → S` is taken as *data*, not produced inside the proof, because every
later stage uses the same `u`. `Schoenflies.IsSetHomeoOn` is the set-level form of it, and
`Schoenflies.exists_isSetHomeoOn_modelCurve` produces one from `lem:jordan-circle`.

The **target** side is completely explicit: six marked points on `S` (four corners, `u(a)` on
the top side and `u(b)` on the bottom side), seven straight edges. The **source** side is the
pushforward of the target's outer cycle along `w = u⁻¹`, plus the polygonal crosscut. That
asymmetry is deliberate: nothing about the six source arcs has to be proved, because `w` is
injective on `S` and each drawing condition transfers.

The nonadjacency hypothesis of `prop:initial-pair` is used in exactly one place,
`Schoenflies.openSegment_chord_supNorm_lt`: `u(a)` and `u(b)` lie on **opposite** sides, so
every interior point of the straight chord has sup norm `< 1`, hence lies in `Q°`.

## What is assumed

Exactly two hypotheses are carried, and only by the theorems that need them. Neither is a
restatement of anything proved here.

* `harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ` — `thm:arc-complement`, the standing
  hypothesis of `thm:jordan` in this library. It is what produces `IsSeparating C`, hence the
  Jordan domain the crosscut runs in, and it is threaded into `thm:general-crosscut` in the
  form that theorem takes.
* `hcollars : Schoenflies.HasArcCollars (inside C) d.crossSet` — blueprint Lemma 1.8 (b) for
  the polygonal crosscut, the standing hypothesis of `lem:crosscut-at-most-two`. It is needed
  on the **source** side only: on the target side the chord is a straight segment, so
  `Schoenflies.hasArcCollars_segment` discharges it outright
  (`InitialData.hasArcCollarsTarget`).

## Blueprint

* `Schoenflies.IsSetHomeoOn`, `Schoenflies.exists_isSetHomeoOn_modelCurve` — `lem:jordan-circle`
  in the set-level form the gluing needs.
* `Schoenflies.InitialCell`, `Schoenflies.initSkel`, `Schoenflies.initOuter`,
  `Schoenflies.faceCells`, `Schoenflies.initBoundary`, `Schoenflies.initSub`,
  `Schoenflies.initialStructure` — the base cell structure the blueprint fixes right after
  `def:generated-structure` (tex 1590–1602): six boundary vertices, six outer edges, the
  crosscut edge, two 2-cells, and the stated base value of `≼_abs`.
* `Schoenflies.outerEdgeUniqueFace_initialStructure` — assertion (vi) of
  `lem:cellulation-invariants` for the base structure.
* `Schoenflies.HexData`, `Schoenflies.HexData.realization` — a realization of that record from
  six points and seven parametrizations, with the geometric side conditions isolated;
  `HexData.arcOf`, `HexData.arcOf_false_isArcBetween`, `HexData.arcOf_inter`,
  `HexData.outerSet_realization`, `HexData.nonboundary_eq`,
  `HexData.isConnected_nonboundary` are the `def:admissible-graph` clauses that follow.
* `Schoenflies.isTwoConnected_initSkel`, `Schoenflies.HexData.isTwoConnected_graph` — the
  2-connectivity clause of `def:admissible-graph`, proved once on the abstract graph and
  transported by `lem:combinatorial-invariance` (a).
* `Schoenflies.targetHex`, `Schoenflies.sourceHex` — the two realizations of
  `prop:initial-pair`.
* `Schoenflies.InitialData` — the data of an initial matched pair, with
  `InitialData.sourceRealization`, `InitialData.targetRealization` and
  `InitialData.skeletonHomeo` (the `g` of `def:matched-pair`: `u` on the outer cycle by
  `InitialData.skeletonHomeo_eq_u`, the parameter-matching homeomorphism `P → [u(a), u(b)]` on
  the crosscut by `InitialData.skeletonHomeo_cross`).
* `Schoenflies.InitialData.isCrosscut`, `.isCutPair`, `.source_cells_cover`,
  `.source_cell_isComponent`, `.source_closure_cell_inter` and their target counterparts —
  `thm:general-crosscut` applied on each side: the two abstract 2-cells are realized by the two
  sides of the crosscut, labelled by which arc of the outer cycle their closure meets.
* `Schoenflies.InitialData.exists_initialData`, `Schoenflies.initial_pair` —
  `prop:initial-pair`.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Set-level homeomorphisms

`lem:jordan-circle` is stated in this library with subtype homeomorphisms `↥C ≃ₜ ↥modelCurve`.
Everything below needs `u` as a map of the plane restricted to `C`, because it has to be glued
to a map defined on the crosscut. `IsSetHomeoOn` is that shape, with the inverse supplied as
data — the same convention as `CellStructure.SkeletonHomeo`. -/

/-! ### The fifteen cells of the initial structure

The blueprint fixes the base value of `≼_abs` immediately after `def:generated-structure`
(tex 1590–1602). Its cells are the six boundary vertices — the four corner preimages together
with `a, b` —, the six open outer edges into which they divide `C`, the crosscut edge `P`, and
the two 2-cells `R₁, R₂`.

The six vertices are indexed **cyclically** by `Fin 6`, in the order they occur along `C`:

    vert 0 = u⁻¹(1,1)   vert 1 = a   vert 2 = u⁻¹(-1,1)
    vert 3 = u⁻¹(-1,-1) vert 4 = b   vert 5 = u⁻¹(1,-1)

so that `a` lies in the corner arc between corners `0` and `1` and `b` in the corner arc
between corners `2` and `3` — the nonadjacency of `prop:initial-pair`, here visible as
`vert 1` and `vert 4` being antipodal in `Fin 6`. `edge i` runs from `vert i` to `vert (i+1)`,
and `chord` from `vert 1` to `vert 4`.

The two boundary edge-paths from `a` to `b` are therefore `B₁ = [edge 1, edge 2, edge 3]`
(through the corners `2, 3`) and `B₂ = [edge 4, edge 5, edge 0]` (through the corners `5, 0`);
both contain corner vertices, as the blueprint observes. `face false` is `R₁` and `face true`
is `R₂`. -/

/-! ### A realization of the initial structure, from six points and seven parametrizations

Both realizations of `prop:initial-pair` have the same shape: six points in cyclic position,
six parametrized arcs joining consecutive ones, and one chord from the second point to the
fifth. `HexData` bundles that shape together with the three geometric side conditions a plane
drawing needs, and `HexData.realization` turns it into a `CellStructure.Realization` of
`initialStructure`. Building it once means the square side and the curve side are checked
against the same list.

The pairwise-meeting conditions are stated in the weakest usable form: two outer arcs meet
only in points that are ends of both, and the chord meets each outer arc only in its own two
ends. Everything `IsDrawing` asks for follows, including "an arc contains no vertex but its
own two ends", which is *derived* rather than assumed (`HexData.mem_outer_iff`). -/


/-! ### The initial skeleton is 2-connected

The first clause of `def:admissible-graph`. It is a fact about the *abstract* graph — a hexagon
with one chord — and `Graph.isTwoConnected_map_iff` carries it to both realizations at once, so
it is proved here and nowhere else. The chord plays no part: the hexagon alone is 2-connected,
because deleting one of its vertices leaves a path. All the cyclic index arithmetic is
`decide`. -/

/-! ### The target realization: the square with one straight chord

The target side of `prop:initial-pair` is completely explicit. The six marked points of `S` are
the four corners together with `u(a) = (α, 1)` in the relative interior of the top side and
`u(b) = (β, -1)` in the relative interior of the bottom side, `|α|, |β| < 1`. **This is the one
place the nonadjacency hypothesis is used**: opposite sides, so the straight chord
`[(α,1), (β,-1)]` has every point other than its ends of sup norm `< 1`, hence in the open
square and off `S`.

All seven edges are straight, so each is pinned by one coordinate and swept by the other, and
the fifteen pairwise intersections are interval arithmetic. `hPiece` and `vPiece` are those two
shapes. -/

variable {α β : ℝ}


/-! ### The source realization: the curve with one polygonal crosscut

The source realization is the pushforward of the target's outer cycle along `w = u⁻¹`, together
with the polygonal crosscut `P` as its seventh edge. Nothing about the six outer arcs has to be
proved again: `w` is injective on `S`, so each of the three drawing conditions transfers.

The crosscut arrives as a parametrization together with the one geometric fact `lem:accessible-
endpoints` supplies — that every point of it other than its two ends lies in `D` — from which
`P ∩ C = {a, b}` follows, and with it the last meeting condition. -/

variable {C : Set Plane}


/-! ### The skeleton homeomorphism

`g` is `u` on `C` and a chosen homeomorphism `P → [u(a), u(b)]` on the crosscut. The chosen
homeomorphism is the one that matches the parameters: `sp t ↦ [u(a), u(b)](t)`. The two
definitions agree at `a` and `b`, which is where `C` and `P` meet, so the pasting lemma applies
to the two closed pieces of the skeleton. -/

/-! ### The initial matched pair, bundled

`InitialData C` is the data `prop:initial-pair` produces before any of its conclusions are
drawn: the boundary homeomorphism `u` with its inverse `w`, the two abscissae `xa, xb` of
`u(a)` and `u(b)` on the two opposite sides, and the polygonal crosscut as a parametrization.
Both realizations, the skeleton homeomorphism, and every conclusion below are functions of
it. -/

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-! #### `a` and `b` are the only points the crosscut shares with the curve -/

/-! #### The map -/

/-! #### Continuity and inversion -/


/-! ### The two 2-cells really are the two sides of the crosscut

`thm:general-crosscut` applied on each side. On the source side the collar hypothesis
`HasArcCollars (inside C) P` is carried, since `P` is an arbitrary polygonal crosscut; on the
target side the chord is straight, so `Schoenflies.hasArcCollars_segment` discharges it
outright. -/

/-! #### The target side -/

/-- The collar hypothesis is not needed on the target side: the chord is a segment. -/
theorem hasArcCollarsTarget : HasArcCollars (inside modelCurve) d.tgt.chordSet := by
  rw [d.tgt_chordSet]
  refine hasArcCollars_segment ?_ (isOpen_inside isJordanCurve_modelCurve.isClosed) ?_ ?_ ?_
  · intro h
    have := (Plane.mk_inj h).2
    norm_num at this
  · exact fun h => inside_subset_compl h (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)
  · exact fun h => inside_subset_compl h (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)
  · rw [← d.tgt_chordSet]; exact d.isCrosscutTarget.sdiff_subset


end InitialData

/-! ### `prop:initial-pair`: an initial matched pair exists

The two open corner arcs the blueprint chooses `a` and `b` from are the relative interiors of
two *opposite* sides of the square, pulled back by `u`. They are relatively open in `C` and
nonempty, so the countable dense set of strongly accessible points of
`prop:countable-strong-access` meets both; `lem:tangent-cone` and `lem:accessible-endpoints`
then supply the polygonal crosscut. -/


end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPairFixed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The complete construction of `prop:initial-pair`

`Schoenflies/InitialPair.lean` builds the initial matched pair but leaves three things that
`def:matched-pair` and `prop:initial-pair` actually assert:

1. **the anchor clause.** The blueprint chooses `a, b ∈ 𝒜`, the fixed countable dense set of
   *strongly accessible* points of `prop:countable-strong-access` (tex 1403–1418). `InitialData`
   records neither the anchor set nor the strong accessibility of `a` and `b`, so nothing
   downstream can build a further crosscut ending at them, and `lem:anchor-density` — which
   needs the anchors of every stage to be points of `𝒜` — has nothing to attach to.
   `Schoenflies.AnchorSet` is `𝒜` as data, `Schoenflies.AnchoredInitialData` is the initial pair
   with the clause recorded, and `Schoenflies.AnchoredInitialData.stronglyAccessible_a` /
   `.exists_access_segment_a` turn it back into the straight access segment `lem:tangent-cone`
   supplies.
2. **the matched labelling.** `InitialData.source_closure_cell_inter` labels the two source
   2-cells by the two boundary arcs `A₁, A₂` of `C`, and `.target_closure_cell_inter` labels the
   two target 2-cells by the two boundary arcs of `S` — independently. Nothing said the two
   labellings correspond, which is the whole content of a *matched* pair.
   `Schoenflies.InitialData.tgt_arcOf_eq_image` (`tgt.arcOf k = u '' src.arcOf k`),
   `.skeletonHomeo_image_arcOf` and `.closure_cell_face_link` supply the link.
3. **`def:admissible-graph` for the target**: "all its edges are polygonal".
   `Schoenflies.InitialData.isPolygonal_tgt_edgeArc` and
   `.isPolygonal_targetRealization_skeletonSet`.

It also carried two hypotheses, `harc` (`thm:arc-complement`) and `hcollars`
(`lem:crosscut-collars`), both of which are now theorems on `main`
(`Schoenflies.arc_complement`, `Schoenflies.IsCrosscut.hasArcCollars`). Every headline result is
restated here after supplying them; the primed names distinguish these strengthened statements.

Finally, `initBoundary` is a raw datum in `CellStructure`, and nothing checked that the two
lists it holds are closed walks of `initSkel` whose cells are exactly `faceCells`. They are:
`Schoenflies.isWalk_initBoundary_false`, `.._true`, and `Schoenflies.mem_faceCells_iff`.

## Blueprint

* `Schoenflies.AnchorSet`, `Schoenflies.nonempty_anchorSet`, `Schoenflies.anchorSet` —
  `prop:countable-strong-access` as the *fixed* set `𝒜` of tex 1418.
* `Schoenflies.AnchoredInitialData`, `Schoenflies.exists_anchoredInitialData`,
  `Schoenflies.anchoredInitialData`, `Schoenflies.initialData` — `prop:initial-pair` including
  the dropped clause "two further points `a, b ∈ 𝒜`", the last one with the canonical anchor
  set supplied.
* `Schoenflies.stronglyAccessible_initialData_a`, `.._b` — the strong accessibility of the two
  chosen points of the canonical pair, which is what the dropped clause was *for*.
* `Schoenflies.AnchoredInitialData.stronglyAccessible_a`, `.stronglyAccessible_b`,
  `.exists_access_segment_a`, `.exists_access_segment_b` — `lem:tangent-cone` at the two
  anchors, the form `lem:accessible-endpoints` consumes at every later stage.
* `Schoenflies.isWalk_initBoundary_false`, `Schoenflies.isWalk_initBoundary_true`,
  `Schoenflies.mem_faceCells_iff`, `Schoenflies.boundaryCycles_initialStructure` — the boundary
  datum of `def:matched-cellulation` really is the simple boundary cycle of each 2-cell and
  carries exactly its strict subcells.
* `Schoenflies.HexData.isPolygonal_arcOf`, `.isPolygonal_outerArcs`,
  `Schoenflies.isPolygonal_modelCurve`, `Schoenflies.InitialData.isPolygonal_tgt_edgeArc`,
  `.isPolygonal_targetRealization_skeletonSet` — the clause "all its edges are polygonal" of
  `def:admissible-graph` for the target realization.
* `Schoenflies.InitialData.src_arcOf_eq_image`, `.tgt_arcOf_eq_image`,
  `.skeletonHomeo_image_arcOf`, `.closure_cell_face_link`, `.closure_cell_face_link_homeo` —
  clause 1 of `def:matched-pair` ("the two distinguished outer cycles correspond") at the level
  of the two boundary arcs, and the correspondence of the two 2-cell labellings.
* `Schoenflies.InitialData.u_src_pos`, `.tgt_pos_corners`, `.u_a_mem_openTop`,
  `.u_b_mem_openBottom` — the geometric content of the `prop:initial-pair` sentence: `C` is
  subdivided at the `u`-preimages of the four corners, and `a, b` lie in two nonadjacent
  corner arcs.
* `Schoenflies.InitialData.source_cells_cover'`, `.source_cell_isComponent'`,
  `.source_closure_cell_inter'`, `.source_cells_ne'`, `.target_cells_cover'`,
  `.target_closure_cell_inter'`, `.target_cell_isComponent`, `.target_cells_ne` —
  `thm:general-crosscut` on both sides, with its hypotheses supplied.
* `Schoenflies.exists_initialData'`, `Schoenflies.initial_pair'` — `prop:initial-pair`, with the
  anchor clause and the matched labelling in the statement.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

/-- **`thm:jordan` in the shape `thm:general-crosscut` consumes.** Every consumer below feeds
this to a lemma whose separating hypothesis is universally quantified over curves.
(`Schoenflies.isSeparating_of_isJordanCurve` is the *polygonal* statement of `Jordan.lean`, and
is a different hypothesis; this is the general one, now a theorem.) -/
theorem forall_isSeparating_of_isJordanCurve : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
  fun _ h => jordan_curve_theorem h

/-! ### Two missing `HexData` facts

The two boundary arcs are part of the outer cycle, and both are polygonal as soon as the six
outer edges are. The second is the clause of `def:admissible-graph` that the target realization
has to satisfy and the source one does not. -/

/-! ### `initBoundary` really is the boundary walk

`CellStructure.boundary` is documented as a raw datum: nothing in the record forces it to walk
anywhere. For `initialStructure` it does. Both lists are *closed* walks of `initSkel`, and the
cells they run through are exactly the `faceCells` that `initSub` declares to be subcells of the
corresponding 2-cell — so the base value of `≼_abs` is not an independent choice. -/

/-! ### The initial face-boundary cycles

The closed-walk facts above are strengthened here to the maintained data needed by
`thm:finite-transfer`: each boundary is a simple cycle of length at least three, and its cells
are exactly the strict subcells of the corresponding face. -/

/-! ### The anchor set `𝒜`

`prop:countable-strong-access` produces a countable dense set of strongly accessible points of
`C`; the blueprint then *fixes* it for the whole construction (tex 1418) and every later stage
draws its new boundary vertices from it. Fixing it means it is data, so it is a structure, and
`prop:initial-pair` takes it as an argument rather than producing its own. -/

variable {C : Set Plane}

/-! ### The initial matched pair, anchored

The clause of `prop:initial-pair` that `InitialData` drops. It is recorded as an extension
rather than as a side theorem so that a consumer holding an initial pair holds the anchoring
too; the integrator merging this file into `InitialPair.lean` should move the two fields into
`InitialData` itself. -/

/-! #### The canonical initial pair

`AnchorSet` is an input because the blueprint fixes `𝒜` once and every later stage draws from
the *same* set. A consumer that has no other constraint on `𝒜` can take `anchorSet hC`: it is a
function of `C` alone (`Nonempty (AnchorSet C)` is a `Prop`, so proof irrelevance makes the
choice independent of the proof supplied), so all its uses agree. -/

/-! ### The two crosscut theorems on the initial pair

`InitialPair.lean` carries `harc` (`thm:arc-complement`) and, on the source side, `hcollars`
(`lem:crosscut-collars`). Both are theorems on `main`: `Schoenflies.arc_complement` and
`Schoenflies.IsCrosscut.hasArcCollars`. Every consumer in Part II should use the primed forms
below and thread nothing. -/

namespace InitialData

variable (d : InitialData C)

/-- The collar hypothesis on the source side, discharged: the crosscut is polygonal. -/
theorem hasArcCollarsSource : HasArcCollars (inside C) d.crossSet :=
  d.isCrosscut.hasArcCollars

/-! ### The matched labelling

`def:matched-pair` clause 1 asks that "the two distinguished outer cycles correspond". On the
initial pair this is not automatic from the abstract structure alone: `arcOf` is read off the
*geometry* of each realization, so the two 2-cell labellings — `source_closure_cell_inter'` and
`target_closure_cell_inter'` — are made independently. They correspond because the source
outer edges are, by construction, the `w`-images of the target ones. -/

/-! ### `def:admissible-graph` for the target: every edge is polygonal -/

end InitialData

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialGenerated
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.GeneratedPair.sourceNonboundaryGraph_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Graph.traceGraph_isLink _root_.Graph.traceGraph_vertexSet _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.GeneratedPair.subdivide_src _root_.Schoenflies.GeneratedPair.subdivide_tgt _root_.Schoenflies.TargetEarStepData.pair_src _root_.Schoenflies.TargetEarStepData.pair_tgt _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.attachGraph_pointSet _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Stage 0: the initial pair as a `GeneratedPair`

`Schoenflies/FiniteTransfer.lean` defines `Schoenflies.GeneratedPair`, the object every stage of
the Schönflies recursion is and that `thm:finite-transfer` consumes and produces. Nothing built
one. This module builds the first: the initial matched pair of `prop:initial-pair`, which is
generated from itself by the empty sequence of elementary operations.

## What has to be shown

The two realizations, the skeleton homeomorphism and weak admissibility are all in
`Schoenflies/InitialPair.lean` and `Schoenflies/InitialPairFixed.lean` already, or one step from
what is there. The work is the two `IsCellDecomposition` fields — assertion (i) of
`lem:cellulation-invariants` — and they are the same work twice, because both realizations have
the same shape: a `HexData` whose six outer arcs form a Jordan curve and whose chord is a
crosscut of it. So assertion (i) is proved **once**, for an arbitrary `HexData` carrying that
crosscut configuration (`Schoenflies.HexData.isCellDecomposition`), and instantiated on each
side. The same is true of weak admissibility (`Schoenflies.HexData.isWeaklyAdmissible`).

The four clauses go as follows.

* `nonempty` — the seven 0-cells are points; the seven open 1-cells are arcs minus their two
  endpoints (`IsArcBetween.nonempty_diff`); the two 2-cells are the two sides of the crosscut,
  nonempty by `thm:general-crosscut`.
* `disjoint` — fifteen cells, but only five kinds of pair. Two vertices are distinct points;
  a vertex misses every open edge it is not an end of (`HexData.mem_outer_iff`,
  `.mem_chord_iff`), and is an end of the ones it does meet; two open edges are disjoint by the
  two meeting conditions of `HexData`; every 1- or 0-cell lies on the skeleton and every 2-cell
  is inside the curve and off the crosscut; and the two 2-cells are the two sides of one
  crosscut.
* `iUnion_eq` — the 0-cells and open 1-cells reassemble the skeleton `C ∪ P`
  (`HexData.iUnion_cellSet`), and the two 2-cells exhaust `D ∖ P`
  (`thm:general-crosscut`), so together they are `C ∪ D`.
* `closure_eq` — a finite case check against `Schoenflies.initSub`, the base value of `≼_abs`
  that the blueprint fixes. The four `initSub_iff_*` lemmas below read it off, and then the only
  topology needed is `closure (A ∖ {p, q}) = A` for an arc (`IsArcBetween.closure_diff`) and the
  closure of a crosscut side (`Schoenflies.crosscut_cell_partition`).

## The input is `InitialData`, not `AnchoredInitialData`

`AnchoredInitialData` adds exactly two fields, `a ∈ 𝒜` and `b ∈ 𝒜`. Nothing in `GeneratedPair`
mentions the anchor set: the anchoring is what lets a *later* stage run a fresh crosscut into `a`
or `b`, and it is read off `AnchoredInitialData.stronglyAccessible_a` at that point. So the pair
is built from `InitialData` — the weaker input — and
`Schoenflies.AnchoredInitialData.generatedPair` is the one-line specialisation for a consumer
holding the anchored form.

## Blueprint

* `Schoenflies.combInvariants_initialStructure` — `lem:cellulation-invariants` (iii), (v), (vi)
  and abstract (viii) for the base structure: the base case of
  `Schoenflies.GeneratedStructure.combInvariants`, which the whole recursion needs.
* `Schoenflies.initSub_iff_vert`, `.._edge`, `.._chord`, `.._face` — the base value of `≼_abs`
  (tex 1590–1602) read as "the subcells of each cell are exactly these".
* `Schoenflies.HexData.isCellDecomposition` — `lem:cellulation-invariants`(i) for either
  realization of `prop:initial-pair`, with `HexData.iUnion_cellSet`,
  `HexData.biUnion_of_three_edges` and `HexData.biUnion_faceCells` as its two reassembly steps.
* `Schoenflies.HexData.isWeaklyAdmissible` — `def:admissible-graph` minus the connectedness
  clause, for either realization.
* `Schoenflies.InitialData.generatedPair`, `Schoenflies.AnchoredInitialData.generatedPair` —
  `def:generated-structure` at stage 0: `prop:initial-pair` is a generated matched cellulation.
* `Schoenflies.HexData.isOpen_cellSet_face`,
  `Schoenflies.InitialData.isOpen_sourceRealization_cell_face`,
  `.isOpen_targetRealization_cell_face` — openness of the two 2-cells: the hypothesis
  `lem:cellulation-invariants`(viii) takes and `IsCellDecomposition` does not record.
* `Schoenflies.infinite_initialCell` — the base case meets the recursion: `thm:finite-transfer`
  needs `[Infinite γ]`, and `InitialCell` supplies it through its spare constructor `aux`.
* `Schoenflies.modelCurve_union_inside` — `S ∪ Int(S) = Q`, the closed target domain.
* `Schoenflies.InitialData.generatedPair_src_isAdmissible`, `.generatedPair_tgt_isAdmissible` —
  the *strong* form of
  `def:admissible-graph` on both sides, which the initial pair does satisfy
  (`rem:intermediate-disconnection` waives it only at intermediate stages).
* `Schoenflies.IsArcBetween.closure_diff` — general; belongs in `Schoenflies/Subarc.lean`.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-! ### An arc is the closure of its interior

General, and stated nowhere on `main`: `Schoenflies/Subarc.lean` has the two endpoint lemmas and
`IsArcBetween.isConnected_diff`, but not the closure identity itself. The integrator should hoist
this next to `IsArcBetween.right_mem_closure_diff`. -/

/-- **An arc is the closure of its interior.** The arc is compact, hence closed, so the closure
of the interior is inside it; conversely the interior is inside its own closure and each of the
two endpoints is a limit of it. -/
theorem IsArcBetween.closure_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine Subset.antisymm (h.isArc.isClosed.closure_subset_iff.2 sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  by_cases hzq : z = q
  · exact hzq ▸ h.right_mem_closure_diff
  exact subset_closure ⟨hz, by rintro (rfl | rfl) <;> simp_all⟩

/-! ### The cells of the initial structure, and `≼_abs`

`initialStructure` declares every one of `InitialCell`'s four *named* constructors a cell. The
fifth, `InitialCell.aux`, is the spare supply of fresh names that `def:generated-structure`
needs and that `thm:finite-transfer` asks for as `[Infinite γ]`; no `aux` name is a cell.

`recOnCells` is the shape every clause of assertion (i) below uses: case analysis on a *cell*,
with the spare names ruled out by the membership hypothesis the clause already carries. -/

theorem mem_cells_initialStructure_of_vert (i : Fin 6) :
    (InitialCell.vert i) ∈ initialStructure.cells := Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cells_initialStructure_of_edge (i : Fin 6) :
    (InitialCell.edge i) ∈ initialStructure.cells := Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cells_initialStructure_of_chord :
    InitialCell.chord ∈ initialStructure.cells := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cells_initialStructure_of_face (k : Bool) :
    (InitialCell.face k) ∈ initialStructure.cells := Or.inr ⟨k, rfl⟩

/-- Every cell of a 2-cell's boundary walk is a cell. -/
theorem mem_cells_of_mem_faceCells {k : Bool} {c : InitialCell} (h : c ∈ faceCells k) :
    c ∈ initialStructure.cells := by
  cases k <;>
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
          | exact mem_cells_initialStructure_of_vert _
          | exact mem_cells_initialStructure_of_edge _
          | exact mem_cells_initialStructure_of_chord

/-! ### The combinatorial invariants at the base

`Schoenflies.GeneratedStructure.combInvariants` propagates `lem:cellulation-invariants` (iii),
(v), (vi) and abstract (viii) along the two elementary operations *given the base case*. This is
the base case. Assertion (vi) is `Schoenflies.outerEdgeUniqueFace_initialStructure`, already on
`main`; the other seven clauses are read off `initSub`. -/

/-- **The combinatorial invariants hold for the initial structure.** The base case of
`Schoenflies.GeneratedStructure.combInvariants`, hence of `GeneratedPair.combInvariants`. -/
theorem combInvariants_initialStructure : initialStructure.CombInvariants where
  sub_mem_left := by
    rintro c d (⟨rfl, hc⟩ | ⟨hd, rfl | rfl⟩ | ⟨k, rfl, hmem⟩)
    · exact hc
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).1)
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).2)
    · exact mem_cells_of_mem_faceCells hmem
  sub_mem_right := by
    rintro c d (⟨-, hd⟩ | ⟨hd, -⟩ | ⟨k, rfl, -⟩)
    · exact hd
    · exact Or.inl (Or.inr hd)
    · exact mem_cells_initialStructure_of_face k
  sub_refl := fun {_} hc => initSub_refl hc
  sub_isLink := by
    rintro f a b ⟨hf, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    exacts [(initSub_ends hf).1, (initSub_ends hf).2]
  face_maximal := by
    rintro F τ ⟨k, rfl⟩ h
    rcases h with ⟨h, -⟩ | ⟨he, hends⟩ | ⟨l, rfl, hmem⟩
    · exact h.symm
    · -- both ends of a 1-cell are 0-cells, and a 2-cell name is neither
      rcases he with ⟨j, rfl⟩ | rfl <;> simp [InitialCell.ends] at hends
    · exact absurd hmem face_notMem_faceCells
  nonboundary_edge := by
    rintro F ⟨k, rfl⟩
    refine ⟨.chord, InitialCell.chord_mem_edges, by simp [InitialCell.outerEdges], ?_⟩
    exact initSub_face (by cases k <;> simp [faceCells])
  mem_face := by
    rintro c hc
    -- every cell appears among the subcells of one of the two 2-cells
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | edge i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | chord => exact ⟨.face false, ⟨_, rfl⟩, initSub_face (by simp [faceCells])⟩
    | face k => exact ⟨.face k, ⟨k, rfl⟩, initSub_refl (mem_cellNames_of_face k)⟩
  outerEdge_unique := outerEdgeUniqueFace_initialStructure

/-! ### The open cells of a `HexData`

Everything assertion (i) needs about the fifteen realized open cells, stated for an arbitrary
`HexData` so that the source and the target realization are served by one proof. Nothing in this
section mentions the crosscut configuration; that enters only for the two 2-cells. -/

namespace HexData

variable (H : HexData)

@[simp] theorem cellSet_vert (i : Fin 6) : H.cellSet (.vert i) = {H.pos i} := rfl

@[simp] theorem cellSet_edge (i : Fin 6) :
    H.cellSet (.edge i) = H.outer i '' I \ {H.pos i, H.pos (i + 1)} := rfl

@[simp] theorem cellSet_chord : H.cellSet .chord = H.chordSet \ {H.pos 1, H.pos 4} := rfl

@[simp] theorem cellSet_face (k : Bool) :
    H.cellSet (.face k) = inside (H.arcOf k ∪ H.chordSet) := rfl

theorem cellSet_edge_subset (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outer i '' I := sdiff_subset

theorem cellSet_edge_subset_outerArcs (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outerArcs :=
  (H.cellSet_edge_subset i).trans (Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i)

theorem cellSet_chord_subset : H.cellSet .chord ⊆ H.chordSet := sdiff_subset

theorem pos_mem_outerArcs (i : Fin 6) : H.pos i ∈ H.outerArcs :=
  Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩

/-- **The 1-cells are nonempty**: an arc has more points than its two endpoints. -/
theorem nonempty_cellSet_edge (i : Fin 6) : (H.cellSet (.edge i)).Nonempty :=
  (H.isArcBetween_outer i).nonempty_diff

theorem nonempty_cellSet_chord : (H.cellSet .chord).Nonempty :=
  H.isArcBetween_chordSet.nonempty_diff

/-- **A closed 1-cell is the drawn edge**: an arc is the closure of its interior. -/
theorem closure_cellSet_edge (i : Fin 6) :
    closure (H.cellSet (.edge i)) = H.outer i '' I :=
  (H.isArcBetween_outer i).closure_diff

theorem closure_cellSet_chord : closure (H.cellSet .chord) = H.chordSet :=
  H.isArcBetween_chordSet.closure_diff

/-- **A 0-cell never lies on an open 1-cell.** A vertex on a drawn outer edge is one of its two
ends (`HexData.mem_outer_iff`), and the open edge is exactly the drawn edge without them. -/
theorem pos_notMem_cellSet_edge (k i : Fin 6) : H.pos k ∉ H.cellSet (.edge i) := by
  rintro ⟨hz, hne⟩
  rcases H.mem_outer_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

theorem pos_notMem_cellSet_chord (k : Fin 6) : H.pos k ∉ H.cellSet .chord := by
  rintro ⟨hz, hne⟩
  rcases H.mem_chord_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

/-- **Two distinct open outer 1-cells are disjoint.** The two edges meet only at points that are
ends of both, and those are removed. -/
theorem disjoint_cellSet_edge {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet (.edge j)) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hne⟩ ⟨hzj, -⟩
  exact hne (H.outer_meet i j hij ⟨hzi, hzj⟩).1

/-- **The open crosscut misses every open outer 1-cell.** -/
theorem disjoint_cellSet_edge_chord (i : Fin 6) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet .chord) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, -⟩ ⟨hzc, hne⟩
  exact hne (H.chord_meet i ⟨hzc, hzi⟩)

/-- A point of a drawn outer edge is on the open edge or is one of its two ends. -/
theorem mem_cellSet_edge_or {i : Fin 6} {z : Plane} (hz : z ∈ H.outer i '' I) :
    z ∈ H.cellSet (.edge i) ∨ z = H.pos i ∨ z = H.pos (i + 1) := by
  by_cases h : z ∈ ({H.pos i, H.pos (i + 1)} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- A point of the crosscut is on the open crosscut or is one of its two ends. -/
theorem mem_cellSet_chord_or {z : Plane} (hz : z ∈ H.chordSet) :
    z ∈ H.cellSet .chord ∨ z = H.pos 1 ∨ z = H.pos 4 := by
  by_cases h : z ∈ ({H.pos 1, H.pos 4} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- **The 0-cells and the open 1-cells reassemble the skeleton `C ∪ P`.** -/
theorem iUnion_cellSet (H : HexData) :
    (⋃ c : InitialCell, H.cellSet c) =
      (H.outerArcs ∪ H.chordSet) ∪ (H.cellSet (.face false) ∪ H.cellSet (.face true)) := by
  refine Subset.antisymm (Set.iUnion_subset fun c => ?_) fun z hz => ?_
  · cases c with
    | vert i =>
      rintro z rfl
      exact Or.inl (Or.inl (H.pos_mem_outerArcs i))
    | edge i => exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset_outerArcs i hz))
    | chord => exact fun z hz => Or.inl (Or.inr (H.cellSet_chord_subset hz))
    | aux n => exact Set.empty_subset _
    | face k =>
      cases k
      exacts [fun z hz => Or.inr (Or.inl hz), fun z hz => Or.inr (Or.inr hz)]
  · rcases hz with (hz | hz) | (hz | hz)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      rcases H.mem_cellSet_edge_or hi with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.edge i, h⟩, Set.mem_iUnion.2 ⟨.vert i, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert (i + 1), rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.chord, h⟩, Set.mem_iUnion.2 ⟨.vert 1, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert 4, rfl⟩]
    · exact Set.mem_iUnion.2 ⟨.face false, hz⟩
    · exact Set.mem_iUnion.2 ⟨.face true, hz⟩

/-- **Three consecutive outer edges and the crosscut reassemble their union.** The two 2-cells of
the initial structure differ only in *which* three outer edges bound them, so the union over the
cells of a boundary walk is computed once, for an arbitrary set `F` of cells presented as the
four vertices, the three edges and the crosscut. -/
theorem biUnion_of_three_edges (H : HexData) (F : Set InitialCell) {i j l : Fin 6}
    (hij : i + 1 = j) (hjl : j + 1 = l)
    (hmem : ∀ c ∈ F, c = .vert i ∨ c = .vert j ∨ c = .vert l ∨ c = .vert (l + 1) ∨
      c = .edge i ∨ c = .edge j ∨ c = .edge l ∨ c = .chord)
    (hvi : InitialCell.vert i ∈ F) (hvj : InitialCell.vert j ∈ F)
    (hvl : InitialCell.vert l ∈ F) (hvl1 : InitialCell.vert (l + 1) ∈ F)
    (hei : InitialCell.edge i ∈ F) (hej : InitialCell.edge j ∈ F)
    (hel : InitialCell.edge l ∈ F) (hch : InitialCell.chord ∈ F)
    (hv1 : InitialCell.vert 1 ∈ F) (hv4 : InitialCell.vert 4 ∈ F) :
    (⋃ c ∈ F, H.cellSet c)
      = (H.outer i '' I ∪ (H.outer j '' I ∪ H.outer l '' I)) ∪ H.chordSet := by
  refine Subset.antisymm (Set.iUnion₂_subset fun c hc => ?_) fun z hz => ?_
  · rcases hmem c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer i))
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer_of_succ hij))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inl (H.pos_mem_outer_of_succ hjl)))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inr (H.pos_succ_mem_outer l)))
    · exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset i hz))
    · exact fun z hz => Or.inl (Or.inr (Or.inl (H.cellSet_edge_subset j hz)))
    · exact fun z hz => Or.inl (Or.inr (Or.inr (H.cellSet_edge_subset l hz)))
    · exact fun z hz => Or.inr (H.cellSet_chord_subset hz)
  · rcases hz with (hz | hz | hz) | hz
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hei, h⟩, Set.mem_iUnion₂.2 ⟨_, hvi, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (i + 1), by rw [hij]; exact hvj, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hej, h⟩, Set.mem_iUnion₂.2 ⟨_, hvj, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (j + 1), by rw [hjl]; exact hvl, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hel, h⟩, Set.mem_iUnion₂.2 ⟨_, hvl, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hvl1, rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hch, h⟩, Set.mem_iUnion₂.2 ⟨_, hv1, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hv4, rfl⟩]

/-- **The cells of a 2-cell's boundary walk reassemble `Aₖ ∪ P`.** The blueprint declares
`faceCells k` to be the subcells of `Rₖ`; geometrically that union is exactly the boundary curve
of `Rₖ`, which is what `closure_eq` has to match at a 2-cell. -/
theorem biUnion_faceCells (H : HexData) (k : Bool) :
    (⋃ c ∈ faceCells k, H.cellSet c) = H.arcOf k ∪ H.chordSet := by
  cases k
  · rw [HexData.arcOf_false]
    refine H.biUnion_of_three_edges _ (i := 1) (j := 2) (l := 3) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
  · rw [HexData.arcOf_true]
    refine H.biUnion_of_three_edges _ (i := 4) (j := 5) (l := 0) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)

/-! ### Assertion (i) and `def:admissible-graph`, for either realization

Both realizations of `prop:initial-pair` are a `HexData` whose six outer arcs form a Jordan curve
and whose chord is a crosscut of it. Everything that distinguishes assertion (i) from bookkeeping
is `thm:general-crosscut`, in the packaged form `Schoenflies.crosscut_cell_partition`: the two
2-cells are open, nonempty, disjoint from each other and from the open crosscut, they exhaust
`D ∖ P` together with it, and the closure of each is itself together with its own boundary
curve. -/

/-- **`lem:cellulation-invariants`(i) for a realization of the initial structure.** The open cells
are nonempty and pairwise disjoint, they cover `C ∪ D`, and every closed cell is the union of its
open subcells for the base value of `≼_abs` the blueprint fixes.

The three hypotheses are exactly `thm:general-crosscut`'s: the chord is a crosscut of the outer
cycle, the two boundary arcs are the two arcs it cuts the outer cycle into, and the crosscut has
collars. On the source side they are `InitialData.isCrosscut`, `.isCutPair` and
`.hasArcCollarsSource`; on the target side `.isCrosscutTarget`, `.isCutPairTarget` and
`.hasArcCollarsTarget`. -/
theorem isCellDecomposition (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true))
    (hcollars : HasArcCollars (inside H.outerArcs) H.chordSet) :
    H.realization.IsCellDecomposition (H.outerArcs ∪ inside H.outerArcs) := by
  obtain ⟨hsplit, hdisj12, hdisj1P, hdisj2P, -, -, hne1, hne2, hcl1, hcl2⟩ :=
    crosscut_cell_partition forall_isSeparating_of_isJordanCurve hcross hcut hcollars
  -- the four facts about the two 2-cells, indexed by the label
  have hface : ∀ k : Bool, H.cellSet (.face k) ⊆ inside H.outerArcs := by
    intro k z hz
    rw [hsplit]
    cases k
    exacts [Or.inl (Or.inl hz), Or.inl (Or.inr hz)]
  have hfaceOuter : ∀ k : Bool, Disjoint (H.cellSet (.face k)) H.outerArcs := by
    intro k
    rw [Set.disjoint_left]
    exact fun z hz hzo => (hface k hz).1 hzo
  have hfaceChord : ∀ k : Bool, Disjoint (H.cellSet (.face k)) (H.cellSet .chord) := by
    intro k; cases k; exacts [hdisj1P, hdisj2P]
  have hfaceNe : ∀ k : Bool, (H.cellSet (.face k)).Nonempty := by
    intro k; cases k; exacts [hne1, hne2]
  have hfaceCl : ∀ k : Bool,
      closure (H.cellSet (.face k)) = H.cellSet (.face k) ∪ (H.arcOf k ∪ H.chordSet) := by
    intro k; cases k; exacts [hcl1, hcl2]
  -- the mixed-dimension disjointness facts, stated once
  have hvertEdge : ∀ k i : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet (.edge i)) := by
    intro k i
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_edge k i h
  have hvertChord : ∀ k : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet .chord) := by
    intro k
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_chord k h
  have hvertFace : ∀ (k : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.vert k)) (H.cellSet (.face l)) := by
    intro k l
    rw [Set.disjoint_left]
    rintro z rfl h
    exact (hface l h).1 (H.pos_mem_outerArcs k)
  have hedgeFace : ∀ (i : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.edge i)) (H.cellSet (.face l)) :=
    fun i l => (hfaceOuter l).symm.mono_left (H.cellSet_edge_subset_outerArcs i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- every open cell is nonempty
    rintro c hc
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i => exact ⟨H.pos i, rfl⟩
    | edge i => exact H.nonempty_cellSet_edge i
    | chord => exact H.nonempty_cellSet_chord
    | face k => exact hfaceNe k
  · -- distinct open cells are disjoint
    rintro c d hc hd hcd
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m =>
        rw [Set.disjoint_left]
        rintro z rfl h
        exact hcd (congrArg InitialCell.vert (H.injective_pos h))
      | edge i => exact hvertEdge k i
      | chord => exact hvertChord k
      | face l => exact hvertFace k l
    | edge i =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertEdge m i).symm
      | edge j => exact H.disjoint_cellSet_edge fun h => hcd (congrArg InitialCell.edge h)
      | chord => exact H.disjoint_cellSet_edge_chord i
      | face l => exact hedgeFace i l
    | chord =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertChord m).symm
      | edge j => exact (H.disjoint_cellSet_edge_chord j).symm
      | chord => exact absurd rfl hcd
      | face l => exact (hfaceChord l).symm
    | face k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertFace m k).symm
      | edge j => exact (hedgeFace j k).symm
      | chord => exact hfaceChord k
      | face l =>
        cases k <;> cases l
        exacts [absurd rfl hcd, hdisj12, hdisj12.symm, absurd rfl hcd]
  · -- the open cells cover `C ∪ D`
    have hall : (⋃ c ∈ initialStructure.cells, H.realization.cell c)
        = ⋃ c : InitialCell, H.cellSet c := by
      refine Subset.antisymm (Set.iUnion₂_subset fun c _ => Set.subset_iUnion _ c)
        (Set.iUnion_subset fun c => ?_)
      match c with
      | .vert i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_vert i)
      | .edge i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_edge i)
      | .chord => exact Set.subset_biUnion_of_mem mem_cells_initialStructure_of_chord
      | .face k => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_face k)
      | .aux n => exact Set.empty_subset _
    rw [hall, H.iUnion_cellSet]
    refine Subset.antisymm (Set.union_subset (Set.union_subset Set.subset_union_left ?_) ?_) ?_
    · intro z hz
      rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      · exact Or.inr (by rw [hsplit]; exact Or.inr h)
      · exact Or.inl (H.pos_mem_outerArcs 1)
      · exact Or.inl (H.pos_mem_outerArcs 4)
    · rintro z (hz | hz)
      exacts [Or.inr (hface false hz), Or.inr (hface true hz)]
    · rintro z (hz | hz)
      · exact Or.inl (Or.inl hz)
      · rw [hsplit] at hz
        rcases hz with (hz | hz) | hz
        exacts [Or.inr (Or.inl hz), Or.inr (Or.inr hz),
          Or.inl (Or.inr (H.cellSet_chord_subset hz))]
  · -- every closed cell is the union of its open subcells
    rintro τ hτ
    have hidx : {c | c ∈ initialStructure.cells ∧ initialStructure.sub c τ}
        = {c | initSub c τ} := by
      ext c
      exact ⟨fun h => h.2, fun h => ⟨combInvariants_initialStructure.sub_mem_left h, h⟩⟩
    rw [hidx]
    cases τ with
    | aux n => exact absurd hτ (aux_notMem_cells n)
    | vert i =>
      have hset : {c | initSub c (.vert i)} = ({InitialCell.vert i} : Set InitialCell) := by
        ext c; exact initSub_iff_vert
      rw [hset, Set.biUnion_singleton]
      exact closure_singleton
    | edge i =>
      have hset : {c | initSub c (.edge i)}
          = ({InitialCell.edge i, .vert i, .vert (i + 1)} : Set InitialCell) := by
        ext c; exact initSub_iff_edge
      rw [hset]
      change closure (H.cellSet (.edge i)) = _
      rw [H.closure_cellSet_edge i]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_edge_subset i
        · rintro z rfl; exact H.pos_mem_outer i
        · rintro z rfl; exact H.pos_succ_mem_outer i
    | chord =>
      have hset : {c | initSub c .chord}
          = ({InitialCell.chord, .vert 1, .vert 4} : Set InitialCell) := by
        ext c; exact initSub_iff_chord
      rw [hset]
      change closure (H.cellSet .chord) = _
      rw [H.closure_cellSet_chord]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_chord_subset
        · rintro z rfl
          exact ⟨0, zero_mem_I, H.chord_zero⟩
        · rintro z rfl
          exact ⟨1, one_mem_I, H.chord_one⟩
    | face k =>
      have hset : {c | initSub c (.face k)} = insert (InitialCell.face k) (faceCells k) := by
        ext c; exact initSub_iff_face
      rw [hset, Set.biUnion_insert]
      change closure (H.cellSet (.face k))
        = H.cellSet (.face k) ∪ ⋃ x ∈ faceCells k, H.cellSet x
      rw [H.biUnion_faceCells k]
      exact hfaceCl k

/-- **Assertion (vii) for the initial hexagonal cellulation.**  Each of its two faces was
defined as the inside of the curve obtained by joining one boundary arc to the crosscut; the
crosscut theorem says that curve is Jordan. -/
theorem isFaceJordan (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true)) :
    H.realization.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change IsJordanCurve (frontier (H.cellSet (.face false)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
      exact hcross.isJordanCurve_union hcut
    · change IsJordanCurve (frontier (H.cellSet (.face true)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]
      exact hcross.isJordanCurve_union hcut.symm
  cell_eq_inside := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change inside (H.arcOf false ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf false ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
    · change inside (H.arcOf true ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf true ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]

/-- **`def:admissible-graph` minus the connectedness clause, for a realization of the initial
structure.** The 2-connectivity is `HexData.isTwoConnected_graph`; the outer cycle is the union
of the six outer arcs by construction; the one nonboundary edge is the crosscut, which is
polygonal and has its interior in the open domain because it is a crosscut.

`rem:intermediate-disconnection` waives connectedness of the open nonboundary part at
intermediate stages only. The initial pair does satisfy it — `HexData.isConnected_nonboundary` —
and `InitialData.generatedPair_isAdmissible` records the strong form. -/
theorem isWeaklyAdmissible (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4)) :
    H.realization.IsWeaklyAdmissible H.outerArcs (H.outerArcs ∪ inside H.outerArcs) where
  isTwoConnected := H.isTwoConnected_graph
  outerSet_eq := H.outerSet_realization
  isPolygonal := by
    rintro e he hne
    -- the only nonboundary 1-cell is the crosscut
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · exact hcross.polygonal
  cell_subset := by
    rintro e he hne
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · intro z hz
      exact ⟨Or.inr (hcross.sdiff_subset hz), (hcross.sdiff_subset hz).1⟩
  skeletonSet_subset := by
    rw [H.skeletonSet_realization]
    refine Set.union_subset Set.subset_union_left fun z hz => ?_
    rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
    · exact Or.inr (hcross.sdiff_subset h)
    · exact Or.inl (H.pos_mem_outerArcs 1)
    · exact Or.inl (H.pos_mem_outerArcs 4)

end HexData

/-! ### The closed square, as a domain

`GeneratedPair` asks for the *closed* target domain. `Schoenflies.inside_modelCurve` identifies
the Jordan domain of `S` with the open square, so the closed domain `S ∪ Int(S)` is literally
`Q = [-1,1]²`. -/

/-- **`S ∪ Int(S) = Q`.** -/
theorem modelCurve_union_inside : modelCurve ∪ inside modelCurve = Plane.closedSquare 0 1 := by
  rw [inside_modelCurve]
  ext x
  rw [Set.mem_union, mem_openSquare_zero_one, mem_closedSquare_zero_one]
  constructor
  · rintro (h | h)
    · exact le_of_eq (h : Plane.supNorm x = 1)
    · exact h.le
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

/-! ### The initial pair is a `GeneratedPair`

Both realizations are instances of the two `HexData` theorems above; all that is left is to
present the hypotheses in the shape they take, which on the source side means rewriting
`d.src.outerArcs` to `C` and on the target side `d.tgt.outerArcs` to `S`. -/

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-- The crosscut configuration on the source side, with the outer cycle named as the `HexData`
sees it. -/
theorem isCrosscut_src : IsCrosscut d.src.outerArcs d.src.chordSet (d.src.pos 1) (d.src.pos 4) := by
  rw [d.src_outerArcs]; exact d.isCrosscut

/-- The crosscut configuration on the target side. -/
theorem isCrosscut_tgt : IsCrosscut d.tgt.outerArcs d.tgt.chordSet (d.tgt.pos 1) (d.tgt.pos 4) := by
  rw [d.tgt_outerArcs]; exact d.isCrosscutTarget

/-- **Assertion (i) on the source side**: the fifteen open cells of `Γ` decompose `C ∪ D`. -/
theorem src_isCellDecomposition : d.sourceRealization.IsCellDecomposition (C ∪ inside C) := by
  have h := d.src.isCellDecomposition d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
    (by rw [d.src_outerArcs]; exact d.hasArcCollarsSource)
  rwa [d.src_outerArcs] at h

/-- **Assertion (i) on the target side**: the fifteen open cells of `Γ'` decompose `Q`. -/
theorem tgt_isCellDecomposition :
    d.targetRealization.IsCellDecomposition (Plane.closedSquare 0 1) := by
  have h := d.tgt.isCellDecomposition d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
    (by rw [d.tgt_outerArcs]; exact d.hasArcCollarsTarget)
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

/-- **`def:admissible-graph` (weak form) on the source side.** -/
theorem src_isWeaklyAdmissible : d.sourceRealization.IsWeaklyAdmissible C (C ∪ inside C) := by
  have h := d.src.isWeaklyAdmissible d.isCrosscut_src
  rwa [d.src_outerArcs] at h

/-- **`def:admissible-graph` (weak form) on the target side.** -/
theorem tgt_isWeaklyAdmissible :
    d.targetRealization.IsWeaklyAdmissible modelCurve (Plane.closedSquare 0 1) := by
  have h := d.tgt.isWeaklyAdmissible d.isCrosscut_tgt
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

/-- **Stage 0 of the Schönflies recursion.** The initial matched pair of `prop:initial-pair` is a
generated matched cellulation: it is generated from `Schoenflies.initialStructure` by the empty
sequence of elementary operations (`GeneratedStructure.base`), its two realizations are the two
realizations of `prop:initial-pair`, and the two cell decompositions are
`lem:cellulation-invariants`(i) on each side.

This is the base case of the whole construction: `thm:finite-transfer` consumes a `GeneratedPair`
and produces one, and this is the first. -/
noncomputable def generatedPair :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) where
  str := initialStructure
  generated := GeneratedStructure.base
  str_combInvariants := combInvariants_initialStructure
  str_boundaryCycles := boundaryCycles_initialStructure
  src := d.sourceRealization
  tgt := d.targetRealization
  homeo := d.skeletonHomeo
  src_isCellDecomposition := d.src_isCellDecomposition
  tgt_isCellDecomposition := d.tgt_isCellDecomposition
  src_isFaceJordan := d.src.isFaceJordan d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
  tgt_isFaceJordan := d.tgt.isFaceJordan d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
  tgtInterior_isOpen := by
    rw [closedSquare_sdiff_modelCurve]
    exact Plane.isOpen_openSquare 0 1
  tgtInterior_frontier_subset := by
    rw [closedSquare_sdiff_modelCurve]
    refine (Plane.frontier_openSquare_subset 0 1).trans ?_
    rw [← modelCurve_eq_frontier, ← d.tgt_isWeaklyAdmissible.outerSet_eq]
    exact d.targetRealization.outerSet_subset_skeletonSet
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(initSkel) at he
    change IsPolygonal (Graph.edgeArc d.tgt.draw e)
    exact d.isPolygonal_tgt_edgeArc he
  src_isWeaklyAdmissible := d.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible := d.tgt_isWeaklyAdmissible

@[simp] theorem generatedPair_str : d.generatedPair.str = initialStructure := rfl

@[simp] theorem generatedPair_src : d.generatedPair.src = d.sourceRealization := rfl

@[simp] theorem generatedPair_tgt : d.generatedPair.tgt = d.targetRealization := rfl

@[simp] theorem generatedPair_homeo : d.generatedPair.homeo = d.skeletonHomeo := rfl

end InitialData

/-! ### The base case meets the recursion

`Schoenflies.finite_transfer_toward_square` and `Schoenflies.EarStep` carry `[Infinite γ]`, and
`FiniteTransfer.lean` argues that without it `EarStep` is *false*: an ear insertion consumes
fresh cell names for the ear's interior vertices, its edges and the two 2-cells the split
creates, so a naming type that the current stage has exhausted refutes it.

The initial structure names fifteen cells. `InitialCell` therefore carries a fifth constructor,
`InitialCell.aux : ℕ → InitialCell`, which is the spare supply and nothing else: no `aux` name is
a cell, every `aux` name has empty open cell, and `initSub` relates none of them — the reflexive
clause of `≼_abs` is restricted to `Schoenflies.cellNames` precisely so that
`CombInvariants.sub_mem_left` and `.sub_mem_right`, which say that `≼_abs` relates cells to
cells, stay true.

The alternative was a relabelling of a `CellStructure` and both of its realizations along an
injection `InitialCell ↪ γ` into an infinite naming type. That is several hundred lines and buys
nothing the spare constructor does not, since the base of `GeneratedStructure` is a parameter and
stage 0 uses only the `base` constructor — no inductive derivation has to be transported. -/

/-! ### The interface, exercised

A machine-checked statement that stage 0 delivers exactly what `thm:finite-transfer` reads off a
`GeneratedPair`: the abstract structure carries the combinatorial invariants, the source and
target realizations are cell decompositions of the two closed domains, and both are admissible in
the strong sense. Nothing below mentions how the pair was built. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.StageTransition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The common output of one transferred stage

Both directions of finite transfer produce the four pieces of data needed between consecutive
matched cellulations: compatible source and target refinements, growth of the realized source
skeleton, and agreement of the new skeleton homeomorphism with the old one.  `StageTransition`
packages that shared output and proves that transitions compose.

## Blueprint

* `Schoenflies.StageTransition` — one step of the quantitative-refinement recursion, stripped of
  the particular ambient graph used to construct it.
* `Schoenflies.IsPartialTransferOf.stageTransition`,
  `Schoenflies.IsTargetPartialTransferOf.stageTransition` — both finite-transfer directions
  expose the same stage interface.
* `Schoenflies.StageTransition.trans` — consecutive transferred refinements compose.
-/

open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The information about consecutive generated pairs consumed by `StageSequence`. -/
structure StageTransition
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (par : γ → γ) : Prop where
  /-- The new source realization refines the preceding source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The target realizations refine along the same abstract parent map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The realized source skeleton grows. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- The new skeleton homeomorphism extends the preceding one. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet

namespace StageTransition

variable {P Q T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {par₁ par₂ : γ → γ}

/-- Consecutive stage transitions compose their parent maps and their nesting data. -/
theorem trans (h₂ : StageTransition T Q par₂) (h₁ : StageTransition Q P par₁) :
    StageTransition T P (par₁ ∘ par₂) where
  refines_src := h₂.refines_src.trans h₁.refines_src
  refines_tgt := h₂.refines_tgt.trans h₁.refines_tgt
  sourceSkeletonSet_subset :=
    h₁.sourceSkeletonSet_subset.trans h₂.sourceSkeletonSet_subset
  homeo_eqOn := by
    intro x hx
    calc
      T.homeo.toFun x = Q.homeo.toFun x :=
        h₂.homeo_eqOn (h₁.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := h₁.homeo_eqOn hx

end StageTransition

/-- Direction (a)'s induction invariant supplies one stage transition. -/
theorem IsPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

/-- The admissible conclusion of direction (a) forgets to the same stage transition. -/
theorem IsTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsPartialTransferOf.stageTransition

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeStages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Quantitative successor stages

The reverse half of the quantitative-refinement recursion is now a closed construction.  From
one generated pair over the closed Jordan domain and one requested positive bound, it selects an
exact finite target-segment cover, a sufficiently fine square-mesh overlay, finitely many clean
accessible boundary anchors, and the reverse finite transfer.  Its target stars are smaller than
the requested bound.

## Blueprint

* `Schoenflies.QuantitativeReverseStage` — all construction data for one reverse quantitative
  successor.
* `Schoenflies.exists_quantitativeReverseStage` — construction from separation
  and the persistent outer-cycle invariant.
* `Schoenflies.QuantitativeReverseStage.transition` — the output is a `StageTransition`.
* `Schoenflies.QuantitativeReverseStage.diam_targetStar_lt_bound` — the uniform half of
  `prop:shrinking-stars` at this successor.
* `Schoenflies.TargetFaceMesh.refine` — subsequent forward transfers preserve the target
  face-mesh estimate.
-/

open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

/-- A uniform mesh bound on the closed target 2-cells of a generated pair. -/
def TargetFaceMesh
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (bound : ℝ) : Prop :=
  ∀ {F : γ}, F ∈ P.str.faces → Metric.diam (closure (P.tgt.cell F)) < bound

namespace TargetFaceMesh

variable {T : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
  {par : γ → γ} {bound : ℝ}

/-- A target face-mesh bound survives any compatible refinement. -/
theorem refine (hmesh : TargetFaceMesh P bound) (href : T.tgt.Refines P.tgt par) :
    TargetFaceMesh T bound := by
  intro F hF
  exact lt_of_le_of_lt
    (href.diam_cell_le P.tgt_isCellDecomposition
      (Plane.isBounded_closedSquare 0 1) (T.str.mem_cells_of_mem_faces hF))
    (hmesh (href.parent_mem_faces hF))

end TargetFaceMesh

/-- The complete output of one quantitatively bounded reverse-transfer successor. -/
structure QuantitativeReverseStage
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (anchors : List Plane) (bound : ℝ) where
  /-- A finite exact segment presentation of the old target skeleton. -/
  cover : TargetSegmentCover P
  /-- The chosen overlay and transferred generated pair. -/
  overlay : TargetSegmentCover.MeshOverlayTransferData cover anchors
  /-- Half the requested bound leaves room for the factor two in the star estimate. -/
  delta_lt_half_bound : overlay.delta < bound / 2

namespace QuantitativeReverseStage

variable {anchors : List Plane} {bound : ℝ}
  (w : QuantitativeReverseStage P anchors bound)

/-- The generated pair at the new successor stage. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.overlay.pair

/-- The stronger face-level estimate retained by later forward refinements. -/
theorem targetFaceMesh : TargetFaceMesh w.pair w.overlay.delta := by
  intro F hF
  exact w.overlay.diam_closure_targetFace_lt hF

end QuantitativeReverseStage

end Schoenflies
end

section
-- module Solutions.Q146_CD.SourceOverlay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite segment overlays on the source side

The outer source curve is deliberately not polygonal, but every nonouter source edge of a
generated pair is polygonal.  This module extracts an exact finite straight-segment cover of
that compact nonboundary carrier and overlays it with the local window grid.  It is the finite
geometric core of the forward half of the quantitative-refinement recursion.

## Blueprint

* `Schoenflies.SourceNonboundarySegmentCover` — an exact finite segment presentation of the
  current source nonboundary skeleton.
* `Schoenflies.GeneratedPair.exists_sourceNonboundarySegmentCover` — every generated pair has
  such a presentation.
* `Schoenflies.SourceNonboundarySegmentCover.localOverlay` — the old compact source core
  overlaid with one fine local grid.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.graph` — the finite inner
  overlay, freshly relabelled and adjoined to the old wild outer graph.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.isSourceExtension` — all
  local source-extension fields, leaving only the two global attachment properties explicit.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.
  isSourceExtension_of_source_connected_two_common` — the global properties follow from the
  carried source-connectedness invariant and two distinct common source/grid vertices.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

namespace Graph

variable {β : Type*} {G H : Graph Plane β} {drawing drawing' : β → ℝ → Plane}

/-- Replacing a drawing by a pointwise equal parametrization on the graph's own edges preserves
all drawing axioms. -/
theorem isDrawing_congr_of_eqOn (h : G.IsDrawing drawing)
    (heq : ∀ {e : β}, e ∈ E(G) → drawing' e = drawing e) :
    G.IsDrawing drawing' where
  edge_param := by
    intro e he
    rw [heq he]
    exact h.edge_param he
  vertex_mem_edgeArc := by
    intro e x y v hxy hv hve
    rw [edgeArc, heq hxy.edge_mem] at hve
    exact h.vertex_mem_edgeArc hxy hv hve
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [edgeArc, heq he] at hpe
    rw [edgeArc, heq hf] at hpf
    exact h.edge_inter he hf hef hpe hpf

/-- Compatible plane drawings whose carriers meet only at common vertices form a plane drawing
on their union. -/
theorem isDrawing_union_of_common_vertices (hG : G.IsDrawing drawing)
    (hH : H.IsDrawing drawing) (hcompat : G.Compatible H)
    (hcross : ∀ {p : Plane}, p ∈ pointSet G drawing → p ∈ pointSet H drawing →
      p ∈ V(G) ∧ p ∈ V(H)) :
    (G.union H).IsDrawing drawing := by
  have hGle : G ≤ G.union H := Graph.left_le_union _ _
  have hHle : H ≤ G.union H := hcompat.right_le_union
  have inc_of_mem (K : Graph Plane β) (hK : K.IsDrawing drawing)
      {e : β} (he : e ∈ E(K)) {p : Plane} (hpV : p ∈ V(K))
      (hpe : p ∈ edgeArc drawing e) : K.Inc e p := by
    obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet he
    rcases hK.vertex_mem_edgeArc hxy hpV hpe with rfl | rfl
    · exact hxy.inc_left
    · exact hxy.inc_right
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases he with he | he
    · obtain ⟨hc, hi, hlink⟩ := hG.edge_param he
      exact ⟨hc, hi, hGle.isLink_mono hlink⟩
    · obtain ⟨hc, hi, hlink⟩ := hH.edge_param he
      exact ⟨hc, hi, hHle.isLink_mono hlink⟩
  · intro e x y v hxy hv hve
    rcases (hcompat.union_isLink).1 hxy with hxyG | hxyH
    · have hvG : v ∈ V(G) := by
        rcases hv with hvG | hvH
        · exact hvG
        · exact (hcross (Graph.edgeArc_subset_pointSet hxyG.edge_mem hve)
            (Graph.vertexSet_subset_pointSet hvH)).1
      exact hG.vertex_mem_edgeArc hxyG hvG hve
    · have hvH : v ∈ V(H) := by
        rcases hv with hvG | hvH
        · exact (hcross (Graph.vertexSet_subset_pointSet hvG)
            (Graph.edgeArc_subset_pointSet hxyH.edge_mem hve)).2
        · exact hvH
      exact hH.vertex_mem_edgeArc hxyH hvH hve
  · intro e f he hf hef p hpe hpf
    rcases he with heG | heH <;> rcases hf with hfG | hfH
    · obtain ⟨hpV, hpeInc, hpfInc⟩ := hG.edge_inter heG hfG hef hpe hpf
      exact ⟨Or.inl hpV, hpeInc.mono hGle, hpfInc.mono hGle⟩
    · obtain ⟨hpVG, hpVH⟩ := hcross
        (Graph.edgeArc_subset_pointSet heG hpe)
        (Graph.edgeArc_subset_pointSet hfH hpf)
      exact ⟨Or.inl hpVG, (inc_of_mem G hG heG hpVG hpe).mono hGle,
        (inc_of_mem H hH hfH hpVH hpf).mono hHle⟩
    · obtain ⟨hpVG, hpVH⟩ := hcross
        (Graph.edgeArc_subset_pointSet hfG hpf)
        (Graph.edgeArc_subset_pointSet heH hpe)
      exact ⟨Or.inl hpVG, (inc_of_mem H hH heH hpVH hpe).mono hHle,
        (inc_of_mem G hG hfG hpVG hpf).mono hGle⟩
    · obtain ⟨hpV, hpeInc, hpfInc⟩ := hH.edge_inter heH hfH hef hpe hpf
      exact ⟨Or.inr hpV, hpeInc.mono hHle, hpfInc.mono hHle⟩

/-- A nonempty walk in a plane drawing has connected geometric carrier. -/
theorem IsDrawing.isConnected_edgesCover_of_isWalk (h : G.IsDrawing drawing)
    {u v : Plane} {W : List β} (hW : G.IsWalk u W v) (hne : W ≠ []) :
    IsConnected (Graph.edgesCover drawing W) := by
  induction hW with
  | nil => exact (hne rfl).elim
  | @cons u w v e W hlink htail ih =>
      rw [Graph.edgesCover_cons]
      by_cases hWnil : W = []
      · subst W
        rw [Graph.edgesCover_nil, Set.union_empty]
        exact (h.edge_isArcBetween hlink).isArc.isConnected
      · apply IsConnected.union
          (Hs := (h.edge_isArcBetween hlink).isArc.isConnected)
          (Ht := ih hWnil)
        refine ⟨w, h.inc_mem_edgeArc hlink.inc_right, ?_⟩
        rw [← h.pointSet_pathGraphOf htail hWnil]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact Graph.mem_walkVertices_self

/-- The point set of a connected plane drawing is connected. -/
theorem IsDrawing.isConnected_pointSet (h : G.IsDrawing drawing) (hG : G.Connected) :
    IsConnected (Graph.pointSet G drawing) := by
  obtain ⟨c, hc⟩ := hG.nonempty
  have bridge : ∀ {u : Plane}, u ∈ V(G) →
      ∃ A : Set Plane, A ⊆ Graph.pointSet G drawing ∧ c ∈ A ∧ u ∈ A ∧ IsConnected A := by
    intro u hu
    by_cases hcu : c = u
    · subst u
      exact ⟨{c}, fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        exact hz ▸ Graph.vertexSet_subset_pointSet hc,
        Set.mem_singleton c, Set.mem_singleton c, isConnected_singleton⟩
    · obtain ⟨W, hW⟩ := hG.reaches hc hu
      have hWne : W ≠ [] := by
        intro hnil
        subst W
        exact hcu hW.eq_of_nil
      have hsubset : Graph.edgesCover drawing W ⊆ Graph.pointSet G drawing := by
        intro z hz
        obtain ⟨e, heW, hze⟩ := Graph.mem_edgesCover_iff.1 hz
        exact Graph.edgeArc_subset_pointSet (hW.edge_mem heW) hze
      have hcW : c ∈ Graph.edgesCover drawing W := by
        rw [← h.pointSet_pathGraphOf hW hWne]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact Graph.mem_walkVertices_self
      have huW : u ∈ Graph.edgesCover drawing W := by
        rw [← h.pointSet_pathGraphOf hW hWne]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact hW.target_mem_walkVertices
      exact ⟨Graph.edgesCover drawing W, hsubset, hcW, huW,
        Schoenflies.Graph.IsDrawing.isConnected_edgesCover_of_isWalk h hW hWne⟩
  refine ⟨⟨c, Graph.vertexSet_subset_pointSet hc⟩, isPreconnected_of_forall c ?_⟩
  intro y hy
  rcases hy with hyV | hyE
  · obtain ⟨A, hA, hcA, hyA, hAconn⟩ := bridge hyV
    exact ⟨A, hA, hcA, hyA, hAconn.isPreconnected⟩
  · obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.1 hyE
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨A, hA, hcA, huA, hAconn⟩ := bridge huv.left_mem
    let B := Graph.edgeArc drawing e
    have hBconn : IsConnected B := (h.edge_isArcBetween huv).isArc.isConnected
    have huB : u ∈ B := h.inc_mem_edgeArc huv.inc_left
    refine ⟨A ∪ B, Set.union_subset hA (Graph.edgeArc_subset_pointSet he),
      Or.inl hcA, Or.inr hye, ?_⟩
    exact (IsConnected.union ⟨u, huA, huB⟩ hAconn hBconn).isPreconnected

end Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

/-- A finite exact straight-segment presentation of the compact nonboundary source skeleton. -/
structure SourceNonboundarySegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) where
  /-- The straight segments covering the nonboundary carrier. -/
  pieces : List Piece
  /-- No listed segment is degenerate. -/
  nondeg : ∀ Q ∈ pieces, Q.Nondeg
  /-- The listed segments occupy exactly the compact nonboundary source graph. -/
  cover_eq : cover pieces =
    Graph.pointSet P.sourceNonboundaryGraph P.src.drawing
  /-- Every listed segment came from one old nonouter source edge. -/
  source : ∀ Q ∈ pieces, ∃ e ∈ E(P.str.skel),
    e ∉ E(P.str.outerGraph) ∧ Q.seg ⊆ edgeArc P.src.drawing e

namespace GeneratedPair

/-- Every generated pair has a finite exact segment presentation of its compact polygonal
nonboundary source skeleton. -/
theorem exists_sourceNonboundarySegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    Nonempty (SourceNonboundarySegmentCover P) := by
  let G := P.sourceNonboundaryGraph
  have hdraw : G.IsDrawing P.src.drawing :=
    P.src.isDrawing.mono P.sourceNonboundaryGraph_le
  have hincident : ∀ z ∈ V(G), ∃ e, G.Inc e z := by
    intro z hz
    change z ∈ P.sourceNonboundaryVertices at hz
    obtain ⟨e, he, heOuter, hinc⟩ := hz
    obtain ⟨w, hlink⟩ := hinc
    have hz' : z ∈ P.sourceNonboundaryVertices :=
      ⟨e, he, heOuter, ⟨w, hlink⟩⟩
    have hw : w ∈ P.sourceNonboundaryVertices :=
      ⟨e, he, heOuter, hlink.inc_right⟩
    have hdeleted :
        (P.src.graph.deleteEdges E(P.str.outerGraph)).IsLink e z w := by
      rw [← Graph.restrict_edgeSet_sdiff_eq_deleteEdges, Graph.restrict_isLink]
      exact ⟨⟨he, heOuter⟩, hlink⟩
    exact ⟨e, w, hdeleted, hz', hw⟩
  have hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc P.src.drawing e) := by
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
      hxy.1.edge_mem
    obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
    have heAbstract : e ∈ E(P.str.skel) := by
      rwa [P.src.edgeSet_graph] at heSrc
    exact P.src_isWeaklyAdmissible.isPolygonal heAbstract heOuter
  obtain ⟨pieces, hnd, hcover, hsource⟩ :=
    hdraw.exists_segmentCover hpoly hincident
  refine ⟨⟨pieces, hnd, hcover, ?_⟩⟩
  intro Q hQ
  obtain ⟨e, heG, hsub⟩ := hsource Q hQ
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet heG
  have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
    hxy.1.edge_mem
  obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
  exact ⟨e, by rwa [P.src.edgeSet_graph] at heSrc, heOuter, hsub⟩

end GeneratedPair

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

/-- The two finite segment families in the source local-grid overlay. -/
noncomputable def localPieces (p : Plane) (s epsilon : ℝ) : List Piece :=
  Q.pieces ++ localGridEdges p s (localGridCount s epsilon)

/-- The compact old source core overlaid with a fine local grid.  Old nonboundary vertices and
any prescribed attachment points are retained as overlay vertices. -/
noncomputable def localOverlay (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : Graph Plane Piece :=
  attachGraph (Q.localPieces p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)

instance localOverlay_finite (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    (Q.localOverlay p s epsilon extra).Finite := attachGraph_finite _ _

/-- Every source segment of the local overlay is nondegenerate. -/
theorem localPieces_nondeg {p : Plane} {s epsilon : ℝ} (hs : 0 < s) :
    ∀ R ∈ Q.localPieces p s epsilon, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact localGridEdges_nondeg hs (one_le_localGridCount s epsilon) R hR

/-- The source local overlay is a finite straight-line plane graph. -/
theorem localOverlay_isDrawing {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    Graph.IsDrawing (Q.localOverlay p s epsilon extra) segmentDrawing :=
  attachGraph_isDrawing (Q.localPieces_nondeg hs) _

/-- The local overlay occupies exactly the old compact source core together with the grid. -/
theorem localOverlay_pointSet (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing =
      Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪
        cover (localGridEdges p s (localGridCount s epsilon)) := by
  rw [localOverlay, attachGraph_pointSet, localPieces, cover_append, Q.cover_eq]

/-- Every vertex of the raw local grid is retained as a vertex of the combined straight-line
overlay. -/
theorem localGridVertices_subset_localOverlay {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (extra : List Plane) :
    V(localGrid p s (localGridCount s epsilon)) ⊆
      V(Q.localOverlay p s epsilon extra) := by
  intro x hx
  rw [localGrid_eq, pieceListGraph_vertexSet] at hx
  simp only [endSet, Set.mem_setOf_eq] at hx
  obtain ⟨R, hR, hxR⟩ := hx
  change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right Q.pieces hR) x hxR
  · exact mem_cover_iff.2 ⟨R, List.mem_append_right Q.pieces hR, by
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-- Away from overlay vertices, an overlay edge meeting a raw local-grid edge is one of its
subdivision pieces. -/
theorem localOverlay_grid_edge_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {R : Piece},
      R ∈ E(Q.localOverlay p s epsilon extra) →
      (edgeArc segmentDrawing R ∩
        (edgeArc segmentDrawing A \ V(Q.localOverlay p s epsilon extra))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  obtain ⟨z, hzR, hzA, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.localPieces p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_right Q.pieces hAList)
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.localOverlay_isDrawing hs extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- Every edge of the source local overlay is a subsegment either of the old nonboundary
source cover or of the local grid. -/
theorem localOverlay_edge_source {p : Plane} {s epsilon : ℝ} {extra : List Plane}
    {R : Piece} (hR : R ∈ E(Q.localOverlay p s epsilon extra)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ localGridEdges p s (localGridCount s epsilon), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · exact Or.inr ⟨A, hA, hsub⟩

/-- Every vertex of the compact old source core is explicitly retained as a vertex of the
local overlay. -/
theorem sourceCoreVertices_subset_localOverlay {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (extra : List Plane) :
    V(P.sourceNonboundaryGraph) ⊆ V(Q.localOverlay p s epsilon extra) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right extra (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [localPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every old nonouter edge belongs to the compact source-core graph. -/
theorem sourceNonboundaryGraph_edge_mem {e : γ} (he : e ∈ E(P.str.skel))
    (heOuter : e ∉ E(P.str.outerGraph)) :
    e ∈ E(P.sourceNonboundaryGraph) := by
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have habSrc := hab.map P.src.pos
  have heSrc : e ∈ E(P.src.graph) := by rwa [P.src.edgeSet_graph]
  have hdeleted : (P.src.graph.deleteEdges E(P.str.outerGraph)).IsLink
      e (P.src.pos a) (P.src.pos b) := by
    rw [← Graph.restrict_edgeSet_sdiff_eq_deleteEdges, Graph.restrict_isLink]
    exact ⟨⟨heSrc, heOuter⟩, habSrc⟩
  have ha : P.src.pos a ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_left⟩
  have hb : P.src.pos b ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_right⟩
  exact ⟨P.src.pos a, P.src.pos b, hdeleted, ha, hb⟩

/-- Away from overlay vertices, an inner-overlay edge meeting an old open nonboundary edge is
one of that edge's subdivision pieces. -/
theorem localOverlay_edge_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → e ∉ E(P.str.outerGraph) → ∀ {R : Piece},
      R ∈ E(Q.localOverlay p s epsilon extra) →
      (edgeArc segmentDrawing R ∩
        (P.src.cell e \ V(Q.localOverlay p s epsilon extra))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc P.src.drawing e := by
  intro e he heOuter R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  have hzCore : z ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing :=
    Graph.edgeArc_subset_pointSet
      (sourceNonboundaryGraph_edge_mem (P := P) he heOuter) hzOldArc
  have hzCover : z ∈ cover Q.pieces := by rwa [Q.cover_eq]
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, hgOuter, hAg⟩ := Q.source A hA
  have hzg : z ∈ edgeArc P.src.drawing g := hAg hzA
  have hznotOldVertex : z ∉ V(P.src.graph) := by
    intro hzV
    rcases P.src.isDrawing.vertex_mem_edgeArc (hab.map P.src.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have heg : e = g := P.src.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ edgeArc P.src.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.localPieces p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.localOverlay_isDrawing hs extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-! ### Containment in the source domain -/

/-- Every grid point with indices in range lies in the local grid's closed square. -/
theorem localGridPoint_mem_closedSquare {p : Plane} {s : ℝ} {k i j : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) (hi : i ≤ k) (hj : j ≤ k) :
    gridPt (localGridX p s k) (localGridY p s k) i j ∈ Plane.closedSquare p s := by
  have hxmono := (localGridX_strictMono (p := p) hs hk).monotone
  have hymono := (localGridY_strictMono (p := p) hs hk).monotone
  rw [Plane.closedSquare_eq_inter]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, gridPt]
  constructor
  · constructor
    · calc
        p 0 - s = localGridX p s k 0 := (localGridX_zero p s k).symm
        _ ≤ localGridX p s k i := hxmono (Nat.zero_le i)
    · calc
        localGridX p s k i ≤ localGridX p s k k := hxmono hi
        _ = p 0 + s := localGridX_last hk
  · constructor
    · calc
        p 1 - s = localGridY p s k 0 := (localGridY_zero p s k).symm
        _ ≤ localGridY p s k j := hymono (Nat.zero_le j)
    · calc
        localGridY p s k j ≤ localGridY p s k k := hymono hj
        _ = p 1 + s := localGridY_last hk

/-- The complete local grid carrier lies in its closed square window. -/
theorem cover_localGridEdges_subset_closedSquare {p : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) :
    cover (localGridEdges p s k) ⊆ Plane.closedSquare p s := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := mem_cover_iff.1 hz
  rcases (mem_gridEdges_iff hk hk).1 hR with
      ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact (Plane.convex_closedSquare p s).segment_subset
      (localGridPoint_mem_closedSquare hs hk (by omega) hj)
      (localGridPoint_mem_closedSquare hs hk (by omega) hj) hzR
  · exact (Plane.convex_closedSquare p s).segment_subset
      (localGridPoint_mem_closedSquare hs hk hi (by omega))
      (localGridPoint_mem_closedSquare hs hk hi (by omega)) hzR

/-- If the closed local window lies in the source domain, then so does the complete finite
inner overlay of the old nonboundary source skeleton with that grid. -/
theorem localOverlay_pointSet_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom) (extra : List Plane) :
    Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing ⊆ srcDom := by
  rw [Q.localOverlay_pointSet]
  apply Set.union_subset
  · exact (Graph.pointSet_mono P.sourceNonboundaryGraph_le).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · exact (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)).trans hwindow

/-- Every edge of the finite inner overlay is polygonal and its nonvertex points lie in the
open source domain.  For an old nonouter edge, weak admissibility puts its open 1-cell in the
interior; if the old arc touches the wild boundary, the touching point is an old core vertex
and hence an overlay vertex.  Grid-sourced edges lie in the chosen interior window. -/
theorem localOverlay_edge_dichotomy {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.localOverlay p s epsilon extra) →
      IsPolygonal (edgeArc segmentDrawing R) ∧
        edgeArc segmentDrawing R \ V(Q.localOverlay p s epsilon extra) ⊆
          srcDom \ srcOuter := by
  intro R hR
  refine ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
  intro x hx
  have hxSeg : x ∈ R.seg := by
    rw [← edgeArc_segmentDrawing]
    exact hx.1
  rcases Q.localOverlay_edge_source hR with hOld | hGrid
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, heNotOuter, hAe⟩ := Q.source A hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hxe : x ∈ edgeArc P.src.drawing e := hAe (hRA hxSeg)
    have hxCell : x ∈ P.src.cell e := by
      rw [P.src.cell_edge hab]
      refine ⟨hxe, ?_⟩
      intro hxEnds
      have habSrc := hab.map P.src.pos
      rcases hxEnds with hxa | hxb
      · apply hx.2
        rw [hxa]
        apply Q.sourceCoreVertices_subset_localOverlay hs extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_left⟩
      · apply hx.2
        rw [hxb]
        apply Q.sourceCoreVertices_subset_localOverlay hs extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_right⟩
    exact P.src_isWeaklyAdmissible.cell_subset he heNotOuter hxCell
  · obtain ⟨A, hA, hRA⟩ := hGrid
    exact hwindow (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩))

/-- The compact nonboundary source carrier meets the wild outer curve only at vertices common
to the nonboundary and outer source graphs. -/
theorem sourceCore_inter_outer_vertices {x : Plane}
    (hxCore : x ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing)
    (hxOuter : x ∈ srcOuter) :
    x ∈ V(P.sourceNonboundaryGraph) ∧
      x ∈ V(P.str.outerGraph.map P.src.pos) := by
  have hxOuterSet : x ∈ P.src.outerSet := by
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hxOuter
  change x ∈ Graph.pointSet (P.str.outerGraph.map P.src.pos) P.src.drawing at hxOuterSet
  have hxCoreV : x ∈ V(P.sourceNonboundaryGraph) := by
    rcases hxCore with hxV | hxE
    · exact hxV
    · obtain ⟨e, heCore, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, habCore⟩ :=
        P.sourceNonboundaryGraph.exists_isLink_of_mem_edgeSet heCore
      have habSrc := P.sourceNonboundaryGraph_le.isLink_mono habCore
      have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
        habCore.1.edge_mem
      obtain ⟨heSrc, heNotOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
      have hxSrcV : x ∈ V(P.src.graph) := by
        rcases hxOuterSet with hxOuterV | hxOuterE
        · exact (P.str.outerGraph_le.map P.src.pos).vertexSet_mono hxOuterV
        · obtain ⟨f, hfOuterGraph, hxf⟩ := Set.mem_iUnion₂.1 hxOuterE
          have hfOuter : f ∈ E(P.str.outerGraph) := by
            rwa [Graph.edgeSet_map] at hfOuterGraph
          have hfSrc : f ∈ E(P.src.graph) := by
            rw [P.src.edgeSet_graph]
            exact P.str.outerGraph_le.edgeSet_mono hfOuter
          have hef : e ≠ f := fun hef => heNotOuter (hef ▸ hfOuter)
          exact (P.src.isDrawing.edge_inter heSrc hfSrc hef hxe hxf).1
      rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxSrcV hxe with hxa | hxb
      · exact hxa.symm ▸ habCore.left_mem
      · exact hxb.symm ▸ habCore.right_mem
  refine ⟨hxCoreV, ?_⟩
  rcases hxOuterSet with hxOuterV | hxOuterE
  · exact hxOuterV
  · obtain ⟨f, hfOuter, hxf⟩ := Set.mem_iUnion₂.1 hxOuterE
    obtain ⟨a, b, habOuter⟩ :=
      (P.str.outerGraph.map P.src.pos).exists_isLink_of_mem_edgeSet hfOuter
    have habSrc := (P.str.outerGraph_le.map P.src.pos).isLink_mono habOuter
    have hxSrcV := P.sourceNonboundaryGraph_le.vertexSet_mono hxCoreV
    rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxSrcV hxf with hxa | hxb
    · exact hxa.symm ▸ habOuter.left_mem
    · exact hxb.symm ▸ habOuter.right_mem

/-! ### Relabelling and adjoining the wild outer graph -/

/-- Fresh abstract edge names for the finite straight-line inner overlay. -/
structure LocalOverlayRelabeling (p : Plane) (s epsilon : ℝ) (extra : List Plane) where
  name : Piece → γ
  name_inj : InjOn name E(Q.localOverlay p s epsilon extra)
  name_fresh : ∀ R ∈ E(Q.localOverlay p s epsilon extra), name R ∉ P.str.cells

/-- An infinite cell-name type supplies a relabelling of the inner overlay disjoint from every
name already used by the current generated structure. -/
theorem exists_localOverlayRelabeling [Infinite γ]
    (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Nonempty (Q.LocalOverlayRelabeling p s epsilon extra) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.localOverlay p s epsilon extra) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace LocalOverlayRelabeling

variable {Q : SourceNonboundarySegmentCover P} {p : Plane} {s epsilon : ℝ}
  {extra : List Plane} (w : Q.LocalOverlayRelabeling p s epsilon extra)

/-- The old outer graph realized on the wild source curve. -/
abbrev outerGraph (_w : Q.LocalOverlayRelabeling p s epsilon extra) : Graph Plane γ :=
  P.str.outerGraph.map P.src.pos

/-- The finite inner overlay after allocation of fresh abstract edge names. -/
noncomputable abbrev innerGraph : Graph Plane γ :=
  (Q.localOverlay p s epsilon extra).relabelEdges w.name w.name_inj

/-- The mixed source extension graph. -/
noncomputable def graph : Graph Plane γ := w.outerGraph.union w.innerGraph

/-- The mixed drawing uses the original parametrizations on the wild outer edges and straight
segments on every freshly named inner edge. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing e

/-- The two edge families are disjoint and therefore compatible. -/
theorem compatible : w.outerGraph.Compatible w.innerGraph := by
  apply Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, Graph.edgeSet_map, Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- On an old outer edge the mixed drawing is the old source drawing. -/
theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    w.drawing e = P.src.drawing e := by simp [drawing, he]

/-- On an inner edge the mixed drawing is the relabelled straight-line drawing. -/
theorem drawing_of_inner {e : γ} (he : e ∈ E(w.innerGraph)) :
    w.drawing e =
      (Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing e := by
  rw [drawing, if_neg]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- The mixed drawing restricts to a plane drawing on the old wild outer graph. -/
theorem outer_isDrawing : w.outerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply w.drawing_of_outer
  rwa [Graph.edgeSet_map] at he

/-- The mixed drawing restricts to a plane drawing on the straight-line inner overlay. -/
theorem inner_isDrawing (hs : 0 < s) : w.innerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.localOverlay_isDrawing hs extra).relabelEdges w.name_inj)
  intro e he
  exact w.drawing_of_inner he

/-- The old outer part of the mixed graph occupies exactly the wild source curve. -/
theorem outer_pointSet : Graph.pointSet w.outerGraph w.drawing = srcOuter := by
  calc
    Graph.pointSet w.outerGraph w.drawing =
        Graph.pointSet w.outerGraph P.src.drawing := by
      apply Graph.pointSet_congr
      intro e he
      simpa only [Graph.edgeArc] using congrArg (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_outer (by rwa [Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

/-- The inner part occupies exactly the finite straight-line local overlay. -/
theorem inner_pointSet :
    Graph.pointSet w.innerGraph w.drawing =
      Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing := by
  calc
    Graph.pointSet w.innerGraph w.drawing =
        Graph.pointSet w.innerGraph
          ((Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing) := by
      apply Graph.pointSet_congr
      intro e he
      simpa only [Graph.edgeArc] using congrArg (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_inner he)
    _ = Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing :=
      Graph.pointSet_relabelEdges w.name_inj

/-- The mixed outer/inner source graph is a plane drawing whenever the local window lies in
the open source domain. -/
theorem graph_isDrawing (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    w.graph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    w.outer_isDrawing (w.inner_isDrawing hs) w.compatible
  intro x hxOuter hxInner
  rw [w.outer_pointSet] at hxOuter
  rw [w.inner_pointSet, Q.localOverlay_pointSet] at hxInner
  rcases hxInner with hxCore | hxGrid
  · obtain ⟨hxCoreV, hxOuterV⟩ :=
      sourceCore_inter_outer_vertices (P := P) hxCore hxOuter
    refine ⟨hxOuterV, ?_⟩
    rw [Graph.vertexSet_relabelEdges]
    exact Q.sourceCoreVertices_subset_localOverlay hs extra hxCoreV
  · have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxGrid
    exact ((hwindow hxWindow).2 hxOuter).elim

/-- The mixed source graph is finite. -/
theorem graph_finite : w.graph.Finite where
  finite_vertexSet := by
    rw [graph, Graph.vertexSet_union, outerGraph, Graph.vertexSet_map,
      Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union (Graph.finite_vertexSet (Q.localOverlay p s epsilon extra))
  finite_edgeSet := by
    rw [graph, Graph.edgeSet_union, outerGraph, Graph.edgeSet_map,
      Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((Graph.finite_edgeSet (Q.localOverlay p s epsilon extra)).image w.name)

/-- The mixed source graph occupies the wild outer curve, the old compact nonboundary
carrier, and the complete local grid. -/
theorem graph_pointSet :
    Graph.pointSet w.graph w.drawing =
      srcOuter ∪ (Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪
        cover (localGridEdges p s (localGridCount s epsilon))) := by
  rw [graph, Graph.pointSet_union, w.outer_pointSet, w.inner_pointSet,
    Q.localOverlay_pointSet]

/-- The complete old source skeleton is retained by the mixed graph. -/
theorem sourceSkeleton_subset_graph :
    P.src.skeletonSet ⊆ Graph.pointSet w.graph w.drawing := by
  rw [P.skeletonSet_eq_sourceNonboundaryGraph_union, w.graph_pointSet]
  intro x hx
  rcases hx with hxCore | hxOuter
  · exact Or.inr (Or.inl hxCore)
  · exact Or.inl hxOuter

/-- Every old source vertex is explicitly retained as a mixed-graph vertex. -/
theorem sourceVertices_subset_graph (hs : 0 < s) :
    V(P.src.graph) ⊆ V(w.graph) := by
  intro x hx
  obtain ⟨z, hz, hzx, -⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
  obtain ⟨D, hD⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hx hz
  obtain ⟨e, heD, hinc⟩ :=
    hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
  have heSrc : e ∈ E(P.src.graph) := hD.edge_mem heD
  by_cases heOuter : e ∈ E(P.str.outerGraph)
  · rw [graph, Graph.vertexSet_union]
    exact Or.inl
      (((P.str.outerGraph_le.map P.src.pos).inc_congr
        (by rwa [Graph.edgeSet_map])).2 hinc).vertex_mem
  · have hxCore : x ∈ V(P.sourceNonboundaryGraph) := by
      change x ∈ P.sourceNonboundaryVertices
      exact ⟨e, heSrc, heOuter, hinc⟩
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by
      rw [Graph.vertexSet_relabelEdges]
      exact Q.sourceCoreVertices_subset_localOverlay hs extra hxCore)

/-- The mixed source graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    Graph.pointSet w.graph w.drawing ⊆ srcDom := by
  rw [graph, Graph.pointSet_union]
  apply Set.union_subset
  · rw [w.outer_pointSet, ← P.src_isWeaklyAdmissible.outerSet_eq]
    exact (Graph.pointSet_mono (P.str.outerGraph_le.map P.src.pos)).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · rw [w.inner_pointSet]
    exact Q.localOverlay_pointSet_subset hs (hwindow.trans sdiff_subset) extra

/-- Every mixed edge is either an old outer edge on the wild curve or a polygonal inner edge
whose nonvertex points lie in the open source domain. -/
theorem graph_edge_dichotomy (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(w.graph) → edgeArc w.drawing e ⊆ srcOuter ∨
      (IsPolygonal (edgeArc w.drawing e) ∧
        edgeArc w.drawing e \ V(w.graph) ⊆ srcDom \ srcOuter) := by
  intro e he
  rcases he with heOuter | heInner
  · exact Or.inl (by
      intro x hx
      rw [← w.outer_pointSet]
      exact Graph.edgeArc_subset_pointSet heOuter hx)
  · obtain ⟨R, hR, rfl⟩ := heInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun f : ℝ → Plane => f '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    obtain ⟨hpoly, hinterior⟩ := Q.localOverlay_edge_dichotomy hs hwindow extra hR
    refine Or.inr ⟨hpoly, ?_⟩
    intro x hx
    apply hinterior
    refine ⟨hx.1, ?_⟩
    intro hxVertex
    apply hx.2
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- An edge of the mixed graph meeting an old open source edge away from mixed vertices is one
of that edge's subdivision pieces. -/
theorem graph_edge_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(w.graph) →
      (edgeArc w.drawing f ∩ (P.src.cell e \ V(w.graph))).Nonempty →
      edgeArc w.drawing f ⊆ edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznotGraph⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hze : z ∈ edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  rcases hf with hfOuter | hfInner
  · have hfAbstract : f ∈ E(P.str.outerGraph) := by
      rwa [Graph.edgeSet_map] at hfOuter
    have hzfSrc : z ∈ edgeArc P.src.drawing f := by
      have hdraw := w.drawing_of_outer hfAbstract
      simpa only [Graph.edgeArc] using
        (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hzf)
    have hznotOld : z ∉ V(P.src.graph) := fun hzOld =>
      hznotGraph (w.sourceVertices_subset_graph hs hzOld)
    have hef : e = f := P.src.isDrawing.unique_edge_at
      (by rw [Graph.edgeSet_map]; exact he)
      (by rw [Graph.edgeSet_map]; exact P.str.outerGraph_le.edgeSet_mono hfAbstract)
      hznotOld hze hzfSrc
    subst f
    have hdraw := w.drawing_of_outer hfAbstract
    rw [Graph.edgeArc, hdraw]
    intro y hy
    exact hy
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    by_cases heOuter : e ∈ E(P.str.outerGraph)
    · exfalso
      have heMixed : e ∈ E(w.graph) := Or.inl (by
        rw [Graph.edgeSet_map]
        exact heOuter)
      have hne : e ≠ w.name R := fun heq =>
        w.name_fresh R hR (heq ▸ P.str.mem_cells_of_mem_edgeSet he)
      have hzeMixed : z ∈ edgeArc w.drawing e := by
        have hdraw := w.drawing_of_outer heOuter
        simpa only [Graph.edgeArc] using
          (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hze)
      have hzVertex :=
        (w.graph_isDrawing hs hwindow).edge_inter heMixed (Or.inr hname) hne
          hzeMixed hzf |>.1
      exact hznotGraph hzVertex
    · rw [harc]
      apply Q.localOverlay_edge_subset hs extra he heOuter hR
      refine ⟨z, harc ▸ hzf, hzCell, ?_⟩
      intro hzLocal
      apply hznotGraph
      rw [graph, Graph.vertexSet_union]
      exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- The mixed graph contains a plane subdivision of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := P.src.isDrawing
  isDrawing := w.graph_isDrawing hs hwindow
  vertexSet_subset := w.sourceVertices_subset_graph hs
  pointSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    have heAbstract : e ∈ E(P.str.skel) := by
      simpa only [P.src.edgeSet_graph] using he
    obtain ⟨z, hzf, hze, hznot⟩ := hmeet
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heAbstract
    apply w.graph_edge_subset hs hwindow heAbstract hf
    refine ⟨z, hzf, ?_, hznot⟩
    rw [P.src.cell_edge hab]
    refine ⟨hze, ?_⟩
    rintro (rfl | rfl)
    · exact hznot (w.sourceVertices_subset_graph hs (hab.map P.src.pos).left_mem)
    · exact hznot (w.sourceVertices_subset_graph hs (hab.map P.src.pos).right_mem)

/-- The trace of the old source skeleton in the mixed graph remains 2-connected. -/
theorem sourceTrace_isTwoConnected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (Graph.traceGraph w.graph w.drawing P.src.skeletonSet).IsTwoConnected :=
  (w.source_isPlaneSubdivisionExtension hs hwindow).trace_isTwoConnected
    P.src_isWeaklyAdmissible.isTwoConnected

/-- Every raw local-grid vertex is retained in the mixed graph. -/
theorem localGridVertices_subset_graph (hs : 0 < s) :
    V(localGrid p s (localGridCount s epsilon)) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, Graph.vertexSet_union]
  exact Or.inr (by
    rw [Graph.vertexSet_relabelEdges]
    exact Q.localGridVertices_subset_localOverlay hs extra hx)

/-- The entire raw local-grid carrier is retained in the mixed graph. -/
theorem localGrid_subset_graph :
    Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      Graph.pointSet w.graph w.drawing := by
  rw [localGrid_eq, pieceListGraph_pointSet, w.graph_pointSet]
  intro x hx
  exact Or.inr (Or.inr hx)

/-- An edge of the mixed graph meeting a raw local-grid edge away from mixed vertices is a
subdivision piece of that grid edge.  An old outer edge cannot meet the grid at all because
the grid window is strictly inside the source domain. -/
theorem graph_grid_edge_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {f : γ},
      f ∈ E(w.graph) →
      (edgeArc w.drawing f ∩
        (edgeArc segmentDrawing A \ V(w.graph))).Nonempty →
      edgeArc w.drawing f ⊆ edgeArc segmentDrawing A := by
  intro A hA f hf hmeet
  obtain ⟨z, hzf, hzA, hznotGraph⟩ := hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hzWindow : z ∈ Plane.closedSquare p s :=
    cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, by rwa [edgeArc_segmentDrawing] at hzA⟩)
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hwindow hzWindow).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.localOverlay_grid_edge_subset hs extra hA hR
    refine ⟨z, harc ▸ hzf, hzA, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- The mixed graph also contains a plane subdivision of the raw local grid. -/
theorem localGrid_isPlaneSubdivisionExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := w.graph_isDrawing hs hwindow
  vertexSet_subset := w.localGridVertices_subset_graph hs
  pointSet_subset := w.localGrid_subset_graph
  edge_subset := by
    intro A hA f hf hmeet
    exact w.graph_grid_edge_subset hs hwindow hA hf hmeet

/-- The local-grid trace inside the mixed graph remains 2-connected. -/
theorem localGridTrace_isTwoConnected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (Graph.traceGraph w.graph w.drawing
      (Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing)).IsTwoConnected :=
  (w.localGrid_isPlaneSubdivisionExtension hs hwindow).trace_isTwoConnected
    (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon))

/-- Two distinct mixed vertices lying on both the old source skeleton and the local grid make
the whole mixed graph 2-connected.  The two plane-subdivision traces are 2-connected and
together contain every mixed vertex. -/
theorem graph_isTwoConnected_of_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing) :
    w.graph.IsTwoConnected := by
  let T := Graph.traceGraph w.graph w.drawing P.src.skeletonSet
  let K := Graph.traceGraph w.graph w.drawing
    (Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
  have hT2 : T.IsTwoConnected := w.sourceTrace_isTwoConnected hs hwindow
  have hK2 : K.IsTwoConnected := w.localGridTrace_isTwoConnected hs hwindow
  have haT : a ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haV, haSource⟩
  have hbT : b ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbV, hbSource⟩
  have haK : a ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haV, haGrid⟩
  have hbK : b ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbV, hbGrid⟩
  have hcompat : T.Compatible K :=
    Graph.Compatible.of_le_le (Graph.traceGraph_le _) (Graph.traceGraph_le _)
  have hU2 : (T.union K).IsTwoConnected :=
    hT2.union hcompat hK2 hab haT haK hbT hbK
  apply hU2.of_le_of_vertexSet_subset
    (Graph.union_le (Graph.traceGraph_le _) (Graph.traceGraph_le _))
  intro x hx
  rw [Graph.vertexSet_union]
  have hxPoint : x ∈ Graph.pointSet w.graph w.drawing :=
    Graph.vertexSet_subset_pointSet hx
  rw [w.graph_pointSet] at hxPoint
  rcases hxPoint with hxOuter | hxCore | hxGrid
  · exact Or.inl (by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inr hxOuter⟩)
  · exact Or.inl (by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inl hxCore⟩)
  · exact Or.inr (by
      rw [Graph.traceGraph_vertexSet, localGrid_eq, pieceListGraph_pointSet]
      exact ⟨hx, hxGrid⟩)

/-- If the old open source skeleton is connected and meets the local grid, then the mixed
carrier remains connected after the wild outer curve is removed. -/
theorem graph_isConnected_diff_of_source_connected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hmeet : ((P.src.skeletonSet \ srcOuter) ∩
      Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing).Nonempty) :
    IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter) := by
  let Kset := Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro x hxK hxOuter
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK
    have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxCover
    exact (hwindow hxWindow).2 hxOuter
  have hcarrier : Graph.pointSet w.graph w.drawing \ srcOuter =
      (P.src.skeletonSet \ srcOuter) ∪ Kset := by
    ext x
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨hxGraph, hxNotOuter⟩
      rw [w.graph_pointSet] at hxGraph
      rcases hxGraph with hxOuter | hxCore | hxGrid
      · exact (hxNotOuter hxOuter).elim
      · exact Or.inl ⟨by
          rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
          exact Or.inl hxCore, hxNotOuter⟩
      · exact Or.inr (by
          simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxGrid)
    · rintro (⟨hxSource, hxNotOuter⟩ | hxK)
      · refine ⟨?_, hxNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
        rw [w.graph_pointSet]
        rcases hxSource with hxCore | hxOuter
        · exact Or.inr (Or.inl hxCore)
        · exact Or.inl hxOuter
      · refine ⟨?_, hKmiss hxK⟩
        rw [w.graph_pointSet]
        exact Or.inr (Or.inr (by
          simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK))
  rw [hcarrier]
  exact IsConnected.union hmeet hsource hKconn

/-- The mixed graph is a complete source extension once its two global attachment properties
are supplied.  All finiteness, drawing, subdivision, containment, and edge-geometry fields are
automatic from the exact source cover and the interior-window hypothesis. -/
theorem isSourceExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (htwo : w.graph.IsTwoConnected)
    (hconnected : IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing where
  finite := w.graph_finite
  isDrawing := w.graph_isDrawing hs hwindow
  isTwoConnected := htwo
  vertexSet_subset := w.sourceVertices_subset_graph hs
  skeletonSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    exact w.graph_edge_subset hs hwindow he hf hmeet
  pointSet_subset := w.graph_pointSet_subset hs hwindow
  edge_dichotomy := by
    intro f hf
    exact w.graph_edge_dichotomy hs hwindow hf
  isConnected := hconnected

/-- With two common source/grid vertices, only connectedness off the wild outer curve remains
to obtain the complete source extension. -/
theorem isSourceExtension_of_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hconnected : IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing :=
  w.isSourceExtension hs hwindow
    (w.graph_isTwoConnected_of_two_common hs hwindow hab haV hbV
      haSource hbSource haGrid hbGrid)
    hconnected

/-- At an admissible stage, two distinct common source/grid vertices give the complete source
extension.  One common point joins the two connected carriers off the boundary; both common
vertices make their 2-connected subdivision traces glue. -/
theorem isSourceExtension_of_source_connected_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected P.src.nonboundary)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing := by
  have hsource' : IsConnected (P.src.skeletonSet \ srcOuter) := by
    rwa [P.src_nonboundary_eq] at hsource
  have haNotOuter : a ∉ srcOuter := by
    intro haOuter
    have haCover : a ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [localGrid_eq, pieceListGraph_pointSet] using haGrid
    have haWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) haCover
    exact (hwindow haWindow).2 haOuter
  apply w.isSourceExtension_of_two_common hs hwindow hab haV hbV
    haSource hbSource haGrid hbGrid
  apply w.graph_isConnected_diff_of_source_connected hs hwindow hsource'
  exact ⟨a, ⟨haSource, haNotOuter⟩, haGrid⟩

end LocalOverlayRelabeling

end SourceNonboundarySegmentCover

end Schoenflies
end

section
-- module Solutions.Q146_CD.SourceAttachment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Auxiliary-crosscut source overlays

A local window can miss the current skeleton, so the raw source/grid overlay need not have the
two common vertices required for 2-connectivity.  The degenerate cases of
`prop:local-grid-attachment` add one polygonal crosscut of the containing face.  This module
builds the corresponding finite straight-line inner overlay while keeping the original wild
outer curve separate.

## Blueprint

* `Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay` — the old compact nonboundary
  carrier, one auxiliary crosscut, and the local grid in a single exact segment overlay.
* `crosscutOverlay_pointSet` — its exact carrier.
* `crosscutOverlay_isDrawing`, `crosscutOverlay_pointSet_subset`, and
  `crosscutOverlay_edge_dichotomy` — the local plane and domain geometry needed by finite
  transfer.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

/-- Every source face of a generated pair lies in the prescribed open source domain. -/
theorem GeneratedPair.src_face_subset_interior {F : γ} (hF : F ∈ P.str.faces) :
    P.src.cell F ⊆ srcDom \ srcOuter := by
  intro x hx
  refine ⟨P.src_isCellDecomposition.cell_subset_domain
    (P.str.mem_cells_of_mem_faces hF) hx, ?_⟩
  intro hxOuter
  have hxSkel : x ∈ P.src.skeletonSet := by
    rw [← P.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
    exact P.src.outerSet_subset_skeletonSet hxOuter
  exact Set.disjoint_left.1
    (P.src.disjoint_cell_skeletonSet P.src_isCellDecomposition hF) hx hxSkel

/-- The geometric output of cutting a bounded source face along the line carrying a selected
grid edge.  The closed crosscut swallows that edge; its open part lies in the face and both ends
lie on the old source skeleton. -/
structure SourceFaceCrosscutData (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (F : γ) (A : Piece) where
  face_mem : F ∈ P.str.faces
  crosscut : Piece
  nondeg : crosscut.Nondeg
  left_mem_frontier : crosscut.1 ∈ frontier (P.src.cell F)
  right_mem_frontier : crosscut.2 ∈ frontier (P.src.cell F)
  left_mem_skeleton : crosscut.1 ∈ P.src.skeletonSet
  right_mem_skeleton : crosscut.2 ∈ P.src.skeletonSet
  interior_subset_face : crosscut.interior ⊆ P.src.cell F
  grid_subset : A.seg ⊆ crosscut.seg

/-- A line through the relative interior of a selected grid edge in a bounded source face
produces the exact auxiliary-crosscut data used by the mixed source overlay. -/
theorem GeneratedPair.exists_sourceFaceCrosscutData {F : γ} {A : Piece}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior) :
    Nonempty (SourceFaceCrosscutData P F A) := by
  obtain ⟨q₀, q₁, hne, hq₀, hq₁, hinterior, -, hswallow⟩ :=
    exists_crosscut hab (P.src_isFaceJordan.isOpen hF) hFbdd (hAline hy)
  have hfrontier :=
    P.src_isCellDecomposition.frontier_cell_subset_skeletonSet P.src_isFaceJordan hF
  exact ⟨{
    face_mem := hF
    crosscut := (q₀, q₁)
    nondeg := hne
    left_mem_frontier := hq₀
    right_mem_frontier := hq₁
    left_mem_skeleton := hfrontier hq₀
    right_mem_skeleton := hfrontier hq₁
    interior_subset_face := hinterior
    grid_subset := seg_subset_crosscut hswallow hAline hy
  }⟩

/-- The exact geometry needed to adjoin a straight crosscut to a source drawing.  Its interior
is disjoint from the wild boundary; an endpoint is allowed on that boundary precisely when it
is already a source vertex (as happens after subdividing the endpoint into the old skeleton). -/
structure SourceCrosscutGeometry
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (J : Piece) : Prop where
  seg_subset_domain : J.seg ⊆ srcDom
  interior_subset : J.interior ⊆ srcDom \ srcOuter
  left_vertex_of_mem_outer : J.1 ∈ srcOuter → J.1 ∈ V(P.src.graph)
  right_vertex_of_mem_outer : J.2 ∈ srcOuter → J.2 ∈ V(P.src.graph)

/-- A source vertex lying on the realized outer set is already a vertex of the mapped outer
graph. -/
theorem GeneratedPair.sourceVertex_mem_outerGraph {x : Plane}
    (hxV : x ∈ V(P.src.graph)) (hxOuter : x ∈ srcOuter) :
    x ∈ V(P.str.outerGraph.map P.src.pos) := by
  rw [← P.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
  rcases hxOuter with hxOuterV | hxOuterE
  · exact hxOuterV
  · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxOuterE
    obtain ⟨a, b, hab⟩ :=
      (P.str.outerGraph.map P.src.pos).exists_isLink_of_mem_edgeSet he
    have habSrc := (P.str.outerGraph_le.map P.src.pos).isLink_mono hab
    rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxV hxe with rfl | rfl
    · exact hab.left_mem
    · exact hab.right_mem

/-- A face crosscut together with the preliminary matched subdivision that makes both of its
endpoints old source vertices.  This is the representation needed when either endpoint lands
in the interior of a wild outer edge. -/
structure RefinedSourceFaceCrosscutData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (A : Piece) where
  crosscutData : SourceFaceCrosscutData P F A
  subdivision : GeneratedPair.SubdivideSetData P
    ({crosscutData.crosscut.1, crosscutData.crosscut.2} : Set Plane)
  geometry : SourceCrosscutGeometry subdivision.pair crosscutData.crosscut

/-- Every source-face crosscut admits a matched preliminary subdivision at its two endpoints.
The construction is harmless when an endpoint was already a vertex and essential when it lies
inside a wild outer edge. -/
theorem SourceFaceCrosscutData.exists_refinement [Infinite γ]
    {F : γ} {A : Piece} (d : SourceFaceCrosscutData P F A) :
    Nonempty (RefinedSourceFaceCrosscutData P F A) := by
  have hendsFinite : ({d.crosscut.1, d.crosscut.2} : Set Plane).Finite :=
    Set.toFinite _
  have hendsSource : ({d.crosscut.1, d.crosscut.2} : Set Plane) ⊆
      P.src.skeletonSet := by
    intro x hx
    rcases hx with rfl | hx
    · exact d.left_mem_skeleton
    · simpa only [Set.mem_singleton_iff] using hx ▸ d.right_mem_skeleton
  obtain ⟨r⟩ := P.exists_subdivideSetData hendsFinite hendsSource
  have hgeom : SourceCrosscutGeometry r.pair d.crosscut := by
    refine {
      seg_subset_domain := ?_
      interior_subset := ?_
      left_vertex_of_mem_outer := fun _ => r.vertexSet_subset
        (Set.mem_insert d.crosscut.1 {d.crosscut.2})
      right_vertex_of_mem_outer := fun _ => r.vertexSet_subset
        (Set.mem_insert_of_mem d.crosscut.1 (Set.mem_singleton d.crosscut.2))
    }
    · intro x hx
      by_cases hxLeft : x = d.crosscut.1
      · exact P.src_isWeaklyAdmissible.skeletonSet_subset
          (hxLeft ▸ d.left_mem_skeleton)
      by_cases hxRight : x = d.crosscut.2
      · exact P.src_isWeaklyAdmissible.skeletonSet_subset
          (hxRight ▸ d.right_mem_skeleton)
      exact (P.src_face_subset_interior d.face_mem
        (d.interior_subset_face
          (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight) hx))).1
    · exact d.interior_subset_face |>.trans (P.src_face_subset_interior d.face_mem)
  exact ⟨{
    crosscutData := d
    subdivision := r
    geometry := hgeom
  }⟩

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

/-- The source pieces after adjoining one auxiliary crosscut and one local grid. -/
noncomputable def crosscutPieces (J : Piece) (p : Plane) (s epsilon : ℝ) : List Piece :=
  (Q.pieces ++ [J]) ++ localGridEdges p s (localGridCount s epsilon)

/-- The finite straight-line overlay of the old compact source core, an auxiliary crosscut,
and the local grid.  Old nonboundary vertices and prescribed points are retained. -/
noncomputable def crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : Graph Plane Piece :=
  attachGraph (Q.crosscutPieces J p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)

instance crosscutOverlay_finite (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : (Q.crosscutOverlay J p s epsilon extra).Finite :=
  attachGraph_finite _ _

/-- Every source piece in the crosscut overlay is nondegenerate. -/
theorem crosscutPieces_nondeg {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) :
    ∀ R ∈ Q.crosscutPieces J p s epsilon, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · rcases List.mem_append.1 hR with hR | hR
    · exact Q.nondeg R hR
    · rw [List.mem_singleton] at hR
      subst R
      exact hJ
  · exact localGridEdges_nondeg hs (one_le_localGridCount s epsilon) R hR

/-- The auxiliary-crosscut overlay is a finite straight-line plane graph. -/
theorem crosscutOverlay_isDrawing {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    Graph.IsDrawing (Q.crosscutOverlay J p s epsilon extra) segmentDrawing :=
  attachGraph_isDrawing (Q.crosscutPieces_nondeg hs hJ) _

/-- The crosscut overlay occupies exactly the old compact source carrier, the auxiliary
segment, and the local grid. -/
theorem crosscutOverlay_pointSet (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing =
      (Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪ J.seg) ∪
        cover (localGridEdges p s (localGridCount s epsilon)) := by
  rw [crosscutOverlay, attachGraph_pointSet, crosscutPieces, cover_append,
    cover_append, Q.cover_eq]
  simp only [cover_cons, cover_nil, Set.union_empty]

/-- Every old compact-core vertex is retained by the auxiliary-crosscut overlay. -/
theorem sourceCoreVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(P.sourceNonboundaryGraph) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right extra (by
      rw [Finset.mem_toList, Graph.mem_vertexFinset]
      exact hx)
  · rw [crosscutPieces, cover_append, cover_append, Q.cover_eq]
    exact Or.inl (Or.inl (Graph.vertexSet_subset_pointSet hx))

/-- Both endpoints of the auxiliary crosscut are overlay vertices. -/
theorem crosscutEnds_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ({J.1, J.2} : Set Plane) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ J
      (List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)))
      x hx
  · exact mem_cover_iff.2 ⟨J,
      List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)), by
        rcases hx with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Every raw local-grid vertex is retained by the auxiliary-crosscut overlay. -/
theorem localGridVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(localGrid p s (localGridCount s epsilon)) ⊆
      V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  rw [localGrid_eq, pieceListGraph_vertexSet] at hx
  simp only [endSet, Set.mem_setOf_eq] at hx
  obtain ⟨R, hR, hxR⟩ := hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right (Q.pieces ++ [J]) hR) x hxR
  · exact mem_cover_iff.2 ⟨R, List.mem_append_right (Q.pieces ++ [J]) hR, by
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-- Every overlay edge is cut from the old compact cover, the auxiliary crosscut, or the local
grid. -/
theorem crosscutOverlay_edge_source {J : Piece} {p : Plane} {s epsilon : ℝ}
    {extra : List Plane} {R : Piece} (hR : R ∈ E(Q.crosscutOverlay J p s epsilon extra)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      R.seg ⊆ J.seg ∨
        ∃ A ∈ localGridEdges p s (localGridCount s epsilon), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hGrid
  · rcases List.mem_append.1 hA with hOld | hCrosscut
    · exact Or.inl ⟨A, hOld, hsub⟩
    · rw [List.mem_singleton] at hCrosscut
      exact Or.inr (Or.inl (hCrosscut ▸ hsub))
  · exact Or.inr (Or.inr ⟨A, hGrid, hsub⟩)

/-- If both the crosscut and the window lie in the open source domain, the entire auxiliary
overlay lies in the closed source domain. -/
theorem crosscutOverlay_pointSet_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJdom : J.seg ⊆ srcDom)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing ⊆ srcDom := by
  rw [Q.crosscutOverlay_pointSet]
  apply Set.union_subset
  · apply Set.union_subset
    · exact (Graph.pointSet_mono P.sourceNonboundaryGraph_le).trans
        P.src_isWeaklyAdmissible.skeletonSet_subset
    · exact hJdom
  · exact (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)).trans (hwindow.trans sdiff_subset)

/-- Every auxiliary-overlay edge is polygonal and has all nonvertex points in the open source
domain. -/
theorem crosscutOverlay_edge_dichotomy {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      IsPolygonal (_root_.Graph.edgeArc segmentDrawing R) ∧
        _root_.Graph.edgeArc segmentDrawing R \ V(Q.crosscutOverlay J p s epsilon extra) ⊆
          srcDom \ srcOuter := by
  intro R hR
  refine ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
  intro x hx
  have hxSeg : x ∈ R.seg := by
    rw [← edgeArc_segmentDrawing]
    exact hx.1
  rcases Q.crosscutOverlay_edge_source hR with hOld | hCrosscut | hGrid
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, heNotOuter, hAe⟩ := Q.source A hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hxe : x ∈ _root_.Graph.edgeArc P.src.drawing e := hAe (hRA hxSeg)
    have hxCell : x ∈ P.src.cell e := by
      rw [P.src.cell_edge hab]
      refine ⟨hxe, ?_⟩
      intro hxEnds
      have habSrc := hab.map P.src.pos
      rcases hxEnds with hxa | hxb
      · apply hx.2
        rw [hxa]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_left⟩
      · apply hx.2
        rw [hxb]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_right⟩
    exact P.src_isWeaklyAdmissible.cell_subset he heNotOuter hxCell
  · have hxLeft : x ≠ J.1 := by
      intro h
      apply hx.2
      rw [h]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert J.1 {J.2})
    have hxRight : x ≠ J.2 := by
      intro h
      apply hx.2
      rw [h]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight)
        (hCrosscut hxSeg))
  · obtain ⟨A, hA, hRA⟩ := hGrid
    exact hwindow (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩))

/-- Away from overlay vertices, an auxiliary-overlay edge meeting an old open nonboundary edge
is one of that edge's subdivision pieces. -/
theorem crosscutOverlay_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → e ∉ E(P.str.outerGraph) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (P.src.cell e \ V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc P.src.drawing e := by
  intro e he heOuter R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ _root_.Graph.edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  have hzCore : z ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing :=
    Graph.edgeArc_subset_pointSet
      (sourceNonboundaryGraph_edge_mem (P := P) he heOuter) hzOldArc
  have hzCover : z ∈ cover Q.pieces := by rwa [Q.cover_eq]
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, -, hAg⟩ := Q.source A hA
  have hzg : z ∈ _root_.Graph.edgeArc P.src.drawing g := hAg hzA
  have hznotOldVertex : z ∉ V(P.src.graph) := by
    intro hzV
    rcases P.src.isDrawing.vertex_mem_edgeArc (hab.map P.src.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have heg : e = g := P.src.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ _root_.Graph.edgeArc P.src.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A)
      (List.mem_append_left _ (List.mem_append_left [J] hA)) hzA
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- Away from overlay vertices, an auxiliary-overlay edge meeting a raw local-grid edge is one
of that edge's subdivision pieces. -/
theorem crosscutOverlay_grid_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (_root_.Graph.edgeArc segmentDrawing A \
          V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  obtain ⟨z, hzR, hzA, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_right (Q.pieces ++ [J]) hAList)
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- Away from overlay vertices, an edge meeting the auxiliary crosscut is one of the
crosscut's subdivision pieces. -/
theorem crosscutOverlay_crosscut_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (_root_.Graph.edgeArc segmentDrawing J \
          V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc segmentDrawing J := by
  intro R hR hmeet
  obtain ⟨z, hzR, hzJ, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'J⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := J)
      (List.mem_append_left _
        (List.mem_append_right Q.pieces (List.mem_singleton_self J)))
      (by rwa [edgeArc_segmentDrawing] at hzJ)
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'J

/-- A single nondegenerate straight segment, with its two ends as vertices, is a plane
drawing. -/
theorem pieceListGraph_single_isDrawing {J : Piece} (hJ : J.Nondeg) :
    _root_.Graph.IsDrawing (pieceListGraph [J]) segmentDrawing where
  edge_param := by
    intro R hR
    rw [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR
    subst R
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hJ, ?_⟩
    simp [segmentDrawing]
  vertex_mem_edgeArc := by
    intro R x y v hR hv _
    rw [pieceListGraph_isLink] at hR
    obtain ⟨hRJ, hxy⟩ := hR
    rw [List.mem_singleton] at hRJ
    subst R
    rw [pieceListGraph_vertexSet] at hv
    obtain ⟨A, hAJ, hvA⟩ := hv
    rw [List.mem_singleton] at hAJ
    subst A
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvA
    · exact hvA.symm
  edge_inter := by
    intro R A hR hA hne
    rw [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR hA
    exact (hne (hR.trans hA.symm)).elim

/-! ### Fresh relabelling and the wild outer graph -/

/-- Fresh abstract edge names for an auxiliary-crosscut inner overlay. -/
structure CrosscutOverlayRelabeling (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) where
  name : Piece → γ
  name_inj : InjOn name E(Q.crosscutOverlay J p s epsilon extra)
  name_fresh : ∀ R ∈ E(Q.crosscutOverlay J p s epsilon extra), name R ∉ P.str.cells

/-- An infinite cell-name type supplies fresh names for the auxiliary-crosscut overlay. -/
theorem exists_crosscutOverlayRelabeling [Infinite γ]
    (J : Piece) (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Nonempty (Q.CrosscutOverlayRelabeling J p s epsilon extra) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.crosscutOverlay J p s epsilon extra) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace CrosscutOverlayRelabeling

variable {Q : SourceNonboundarySegmentCover P} {J : Piece} {p : Plane}
  {s epsilon : ℝ} {extra : List Plane}
  (w : Q.CrosscutOverlayRelabeling J p s epsilon extra)

/-- The old outer graph, still drawn on the wild source curve. -/
abbrev outerGraph (_w : Q.CrosscutOverlayRelabeling J p s epsilon extra) :
    _root_.Graph Plane γ := P.str.outerGraph.map P.src.pos

/-- The freshly relabelled auxiliary-crosscut inner overlay. -/
noncomputable abbrev innerGraph : _root_.Graph Plane γ :=
  (Q.crosscutOverlay J p s epsilon extra).relabelEdges w.name w.name_inj

/-- The mixed crosscut source graph. -/
noncomputable def graph : _root_.Graph Plane γ := w.outerGraph.union w.innerGraph

/-- The mixed drawing keeps the wild outer parametrizations and uses straight segments on all
fresh inner edges. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.crosscutOverlay J p s epsilon extra).relabelDrawing
      w.name segmentDrawing e

/-- Old outer names and freshly allocated inner names are disjoint. -/
theorem compatible : w.outerGraph.Compatible w.innerGraph := by
  apply _root_.Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, _root_.Graph.edgeSet_map, _root_.Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- On an old outer edge the mixed drawing is the old source drawing. -/
theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    w.drawing e = P.src.drawing e := by simp [drawing, he]

/-- On a fresh inner edge the mixed drawing is its relabelled segment drawing. -/
theorem drawing_of_inner {e : γ} (he : e ∈ E(w.innerGraph)) :
    w.drawing e =
      (Q.crosscutOverlay J p s epsilon extra).relabelDrawing
        w.name segmentDrawing e := by
  rw [drawing, if_neg]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- The mixed drawing restricts to a drawing of the old wild outer graph. -/
theorem outer_isDrawing : w.outerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply w.drawing_of_outer
  rwa [_root_.Graph.edgeSet_map] at he

/-- The mixed drawing restricts to the relabelled auxiliary-crosscut inner overlay. -/
theorem inner_isDrawing (hs : 0 < s) (hJ : J.Nondeg) :
    w.innerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.crosscutOverlay_isDrawing hs hJ extra).relabelEdges w.name_inj)
  intro e he
  exact w.drawing_of_inner he

/-- The outer part occupies exactly the wild source curve. -/
theorem outer_pointSet :
    _root_.Graph.pointSet w.outerGraph w.drawing = srcOuter := by
  calc
    _root_.Graph.pointSet w.outerGraph w.drawing =
        _root_.Graph.pointSet w.outerGraph P.src.drawing := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_outer (by rwa [_root_.Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

/-- The inner part occupies exactly the straight-line auxiliary-crosscut overlay. -/
theorem inner_pointSet :
    _root_.Graph.pointSet w.innerGraph w.drawing =
      _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
        segmentDrawing := by
  calc
    _root_.Graph.pointSet w.innerGraph w.drawing =
        _root_.Graph.pointSet w.innerGraph
          ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
            w.name segmentDrawing) := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval) (w.drawing_of_inner he)
    _ = _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
        segmentDrawing :=
      _root_.Graph.pointSet_relabelEdges w.name_inj

/-- The wild outer graph and the auxiliary-crosscut inner overlay form a plane drawing. -/
theorem graph_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    w.graph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    w.outer_isDrawing (w.inner_isDrawing hs hJ) w.compatible
  intro x hxOuter hxInner
  rw [w.outer_pointSet] at hxOuter
  rw [w.inner_pointSet, Q.crosscutOverlay_pointSet] at hxInner
  rcases hxInner with (hxCore | hxCrosscut) | hxGrid
  · obtain ⟨hxCoreV, hxOuterV⟩ :=
      sourceCore_inter_outer_vertices (P := P) hxCore hxOuter
    refine ⟨hxOuterV, ?_⟩
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra hxCoreV
  · by_cases hxLeft : x = J.1
    · subst x
      refine ⟨P.sourceVertex_mem_outerGraph
          (hJgeom.left_vertex_of_mem_outer hxOuter) hxOuter, ?_⟩
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert J.1 {J.2})
    by_cases hxRight : x = J.2
    · subst x
      refine ⟨P.sourceVertex_mem_outerGraph
          (hJgeom.right_vertex_of_mem_outer hxOuter) hxOuter, ?_⟩
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact ((hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight) hxCrosscut)).2
        hxOuter).elim
  · have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxGrid
    exact ((hwindow hxWindow).2 hxOuter).elim

/-- The mixed crosscut source graph is finite. -/
theorem graph_finite : w.graph.Finite where
  finite_vertexSet := by
    rw [graph, _root_.Graph.vertexSet_union, outerGraph, _root_.Graph.vertexSet_map,
      _root_.Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union
      (_root_.Graph.finite_vertexSet (Q.crosscutOverlay J p s epsilon extra))
  finite_edgeSet := by
    rw [graph, _root_.Graph.edgeSet_union, outerGraph, _root_.Graph.edgeSet_map,
      _root_.Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((_root_.Graph.finite_edgeSet
        (Q.crosscutOverlay J p s epsilon extra)).image w.name)

/-- The mixed graph occupies the wild outer curve, old compact core, auxiliary crosscut, and
local grid. -/
theorem graph_pointSet :
    _root_.Graph.pointSet w.graph w.drawing =
      srcOuter ∪ ((
        _root_.Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪ J.seg) ∪
          cover (localGridEdges p s (localGridCount s epsilon))) := by
  rw [graph, _root_.Graph.pointSet_union, w.outer_pointSet, w.inner_pointSet,
    Q.crosscutOverlay_pointSet]

/-- The complete old source skeleton is retained by the mixed crosscut graph. -/
theorem sourceSkeleton_subset_graph :
    P.src.skeletonSet ⊆ _root_.Graph.pointSet w.graph w.drawing := by
  rw [P.skeletonSet_eq_sourceNonboundaryGraph_union, w.graph_pointSet]
  intro x hx
  rcases hx with hxCore | hxOuter
  · exact Or.inr (Or.inl (Or.inl hxCore))
  · exact Or.inl hxOuter

/-- Every old source vertex is retained by the mixed crosscut graph. -/
theorem sourceVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    V(P.src.graph) ⊆ V(w.graph) := by
  intro x hx
  obtain ⟨z, hz, hzx, -⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
  obtain ⟨D, hD⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hx hz
  obtain ⟨e, heD, hinc⟩ :=
    hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
  have heSrc : e ∈ E(P.src.graph) := hD.edge_mem heD
  by_cases heOuter : e ∈ E(P.str.outerGraph)
  · rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inl
      (((P.str.outerGraph_le.map P.src.pos).inc_congr
        (by rwa [_root_.Graph.edgeSet_map])).2 hinc).vertex_mem
  · have hxCore : x ∈ V(P.sourceNonboundaryGraph) := by
      change x ∈ P.sourceNonboundaryVertices
      exact ⟨e, heSrc, heOuter, hinc⟩
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra hxCore)

/-- Both ends of the auxiliary crosscut are vertices of the mixed graph. -/
theorem crosscutEnds_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    ({J.1, J.2} : Set Plane) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra hx)

/-- The mixed crosscut graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet w.graph w.drawing ⊆ srcDom := by
  rw [graph, _root_.Graph.pointSet_union]
  apply Set.union_subset
  · rw [w.outer_pointSet, ← P.src_isWeaklyAdmissible.outerSet_eq]
    exact (_root_.Graph.pointSet_mono (P.str.outerGraph_le.map P.src.pos)).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · rw [w.inner_pointSet]
    exact Q.crosscutOverlay_pointSet_subset hs hJgeom.seg_subset_domain hwindow extra

/-- An edge of the mixed crosscut graph meeting an old open source edge away from mixed
vertices is one of that edge's subdivision pieces. -/
theorem graph_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩ (P.src.cell e \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆ _root_.Graph.edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznotGraph⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hze : z ∈ _root_.Graph.edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  rcases hf with hfOuter | hfInner
  · have hfAbstract : f ∈ E(P.str.outerGraph) := by
      rwa [_root_.Graph.edgeSet_map] at hfOuter
    have hzfSrc : z ∈ _root_.Graph.edgeArc P.src.drawing f := by
      have hdraw := w.drawing_of_outer hfAbstract
      simpa only [_root_.Graph.edgeArc] using
        (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hzf)
    have hznotOld : z ∉ V(P.src.graph) := fun hzOld =>
      hznotGraph (w.sourceVertices_subset_graph hs hJ hzOld)
    have hef : e = f := P.src.isDrawing.unique_edge_at
      (by rw [_root_.Graph.edgeSet_map]; exact he)
      (by
        rw [_root_.Graph.edgeSet_map]
        exact P.str.outerGraph_le.edgeSet_mono hfAbstract)
      hznotOld hze hzfSrc
    subst f
    have hdraw := w.drawing_of_outer hfAbstract
    rw [_root_.Graph.edgeArc, hdraw]
    intro y hy
    exact hy
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    by_cases heOuter : e ∈ E(P.str.outerGraph)
    · exfalso
      have heMixed : e ∈ E(w.graph) := Or.inl (by
        rw [_root_.Graph.edgeSet_map]
        exact heOuter)
      have hne : e ≠ w.name R := fun heq =>
        w.name_fresh R hR (heq ▸ P.str.mem_cells_of_mem_edgeSet he)
      have hzeMixed : z ∈ _root_.Graph.edgeArc w.drawing e := by
        have hdraw := w.drawing_of_outer heOuter
        simpa only [_root_.Graph.edgeArc] using
          (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hze)
      have hzVertex :=
        (w.graph_isDrawing hs hJ hJgeom hwindow).edge_inter
          heMixed (Or.inr hname) hne hzeMixed hzf |>.1
      exact hznotGraph hzVertex
    · rw [harc]
      apply Q.crosscutOverlay_edge_subset hs hJ extra he heOuter hR
      refine ⟨z, harc ▸ hzf, hzCell, ?_⟩
      intro hzLocal
      apply hznotGraph
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The mixed crosscut graph contains a plane subdivision of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := P.src.isDrawing
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := w.sourceVertices_subset_graph hs hJ
  pointSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    have heAbstract : e ∈ E(P.str.skel) := by
      simpa only [P.src.edgeSet_graph] using he
    obtain ⟨z, hzf, hze, hznot⟩ := hmeet
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heAbstract
    apply w.graph_edge_subset hs hJ hJgeom hwindow heAbstract hf
    refine ⟨z, hzf, ?_, hznot⟩
    rw [P.src.cell_edge hab]
    refine ⟨hze, ?_⟩
    rintro (rfl | rfl)
    · exact hznot (w.sourceVertices_subset_graph hs hJ (hab.map P.src.pos).left_mem)
    · exact hznot (w.sourceVertices_subset_graph hs hJ (hab.map P.src.pos).right_mem)

/-- The old-source trace inside the mixed crosscut graph remains 2-connected. -/
theorem sourceTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (_root_.Graph.traceGraph w.graph w.drawing P.src.skeletonSet).IsTwoConnected :=
  (w.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trace_isTwoConnected
    P.src_isWeaklyAdmissible.isTwoConnected

/-- Every raw local-grid vertex is retained by the mixed crosscut graph. -/
theorem localGridVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    V(localGrid p s (localGridCount s epsilon)) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.localGridVertices_subset_crosscutOverlay hs hJ extra hx)

/-- The complete raw local-grid carrier is retained by the mixed crosscut graph. -/
theorem localGrid_subset_graph :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet w.graph w.drawing := by
  rw [localGrid_eq, pieceListGraph_pointSet, w.graph_pointSet]
  intro x hx
  exact Or.inr (Or.inr hx)

/-- A mixed edge meeting a raw grid edge away from mixed vertices is a subdivision piece of
that grid edge. -/
theorem graph_grid_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {f : γ},
      f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩
        (_root_.Graph.edgeArc segmentDrawing A \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆
        _root_.Graph.edgeArc segmentDrawing A := by
  intro A hA f hf hmeet
  obtain ⟨z, hzf, hzA, hznotGraph⟩ := hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hzWindow : z ∈ Plane.closedSquare p s :=
    cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, by rwa [edgeArc_segmentDrawing] at hzA⟩)
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hwindow hzWindow).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.crosscutOverlay_grid_edge_subset hs hJ extra hA hR
    refine ⟨z, harc ▸ hzf, hzA, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- A mixed edge meeting the auxiliary crosscut away from mixed vertices is one of the
crosscut's subdivision pieces. -/
theorem graph_crosscut_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J) :
    ∀ {f : γ}, f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩
        (_root_.Graph.edgeArc segmentDrawing J \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆
        _root_.Graph.edgeArc segmentDrawing J := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzJ, hznotGraph⟩ := hmeet
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    have hzSeg : z ∈ J.seg := by rwa [edgeArc_segmentDrawing] at hzJ
    have hzLeft : z ≠ J.1 := by
      intro h
      apply hznotGraph
      rw [h]
      exact w.crosscutEnds_subset_graph hs hJ (Set.mem_insert J.1 {J.2})
    have hzRight : z ≠ J.2 := by
      intro h
      apply hznotGraph
      rw [h]
      exact w.crosscutEnds_subset_graph hs hJ
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact ((hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hzLeft) (Ne.symm hzRight) hzSeg)).2
        hzOuter).elim
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.crosscutOverlay_crosscut_edge_subset hs hJ extra hR
    refine ⟨z, harc ▸ hzf, hzJ, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The mixed graph contains a plane subdivision of the one-edge auxiliary crosscut. -/
theorem crosscut_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension (pieceListGraph [J]) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := pieceListGraph_single_isDrawing hJ
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := by
    intro x hx
    rw [pieceListGraph_vertexSet] at hx
    simp only [endSet, Set.mem_setOf_eq] at hx
    obtain ⟨R, hR, hxR⟩ := hx
    simp only [List.mem_singleton] at hR
    subst R
    exact w.crosscutEnds_subset_graph hs hJ hxR
  pointSet_subset := by
    rw [pieceListGraph_pointSet]
    intro x hx
    rw [w.graph_pointSet]
    exact Or.inr (Or.inl (Or.inr (by simpa using hx)))
  edge_subset := by
    intro R hR f hf hmeet
    simp only [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR
    subst R
    exact w.graph_crosscut_edge_subset hs hJ hJgeom hf hmeet

/-- The mixed crosscut graph contains a plane subdivision of the raw local grid. -/
theorem localGrid_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := w.localGridVertices_subset_graph hs hJ
  pointSet_subset := w.localGrid_subset_graph
  edge_subset := by
    intro A hA f hf hmeet
    exact w.graph_grid_edge_subset hs hJ hwindow hA hf hmeet

/-- The local-grid trace inside the mixed crosscut graph remains 2-connected. -/
theorem localGridTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (_root_.Graph.traceGraph w.graph w.drawing
      (_root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing)).IsTwoConnected :=
  (w.localGrid_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trace_isTwoConnected
    (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon))

/-- The subdivided auxiliary segment is the exact carrier of a path in the mixed graph. -/
theorem exists_crosscut_trace (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∃ D : List γ, w.graph.IsPath J.1 D J.2 ∧
      _root_.Graph.edgesCover w.drawing D = J.seg := by
  obtain ⟨D, hD, hcover⟩ :=
    (w.crosscut_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).exists_edge_trace
      (pieceListGraph_isLink_self (List.mem_singleton_self J))
  exact ⟨D, hD, by simpa only [edgeArc_segmentDrawing] using hcover⟩

/-- If a nondegenerate raw grid edge lies on the auxiliary segment and both crosscut ends lie
on the old source skeleton, the old trace, crosscut ear, and grid trace span a 2-connected
subgraph.  Consequently the complete mixed graph is 2-connected. -/
theorem graph_isTwoConnected_of_crosscut_grid_edge (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hJsource : J.1 ∈ P.src.skeletonSet ∧ J.2 ∈ P.src.skeletonSet)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    w.graph.IsTwoConnected := by
  obtain ⟨D, hD, hcover⟩ := w.exists_crosscut_trace hs hJ hJgeom hwindow
  let T := _root_.Graph.traceGraph w.graph w.drawing P.src.skeletonSet
  let C := w.graph.pathGraphOf J.1 D
  let K := _root_.Graph.traceGraph w.graph w.drawing
    (_root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
  have hT2 : T.IsTwoConnected :=
    w.sourceTrace_isTwoConnected hs hJ hJgeom hwindow
  have hJ1Graph : J.1 ∈ V(w.graph) :=
    w.crosscutEnds_subset_graph hs hJ (Set.mem_insert J.1 {J.2})
  have hJ2Graph : J.2 ∈ V(w.graph) :=
    w.crosscutEnds_subset_graph hs hJ (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
  have hJ1T : J.1 ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hJ1Graph, hJsource.1⟩
  have hJ2T : J.2 ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hJ2Graph, hJsource.2⟩
  have hTC : T.Compatible C :=
    _root_.Graph.Compatible.of_le_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk)
  have hU2 : (T.union C).IsTwoConnected :=
    hT2.ear hTC hD.isPathGraph_pathGraphOf hJ hJ1T hJ2T
  have hK2 : K.IsTwoConnected :=
    w.localGridTrace_isTwoConnected hs hJ hJgeom hwindow
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hAlink :
      (localGrid p s (localGridCount s epsilon)).IsLink A A.1 A.2 := by
    rw [localGrid_eq]
    exact pieceListGraph_isLink_self hAList
  have hA1Graph : A.1 ∈ V(w.graph) :=
    w.localGridVertices_subset_graph hs hJ hAlink.left_mem
  have hA2Graph : A.2 ∈ V(w.graph) :=
    w.localGridVertices_subset_graph hs hJ hAlink.right_mem
  have hA1J : A.1 ∈ J.seg := hAJ (left_mem_segment ℝ _ _)
  have hA2J : A.2 ∈ J.seg := hAJ (right_mem_segment ℝ _ _)
  have hA1C : A.1 ∈ V(C) := by
    rw [_root_.Graph.pathGraphOf_vertexSet]
    apply (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
      hD.isWalk hA1Graph
    rw [hcover]
    exact hA1J
  have hA2C : A.2 ∈ V(C) := by
    rw [_root_.Graph.pathGraphOf_vertexSet]
    apply (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
      hD.isWalk hA2Graph
    rw [hcover]
    exact hA2J
  have hA1U : A.1 ∈ V(T.union C) := by
    rw [_root_.Graph.vertexSet_union]
    exact Or.inr hA1C
  have hA2U : A.2 ∈ V(T.union C) := by
    rw [_root_.Graph.vertexSet_union]
    exact Or.inr hA2C
  have hA1K : A.1 ∈ V(K) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hA1Graph,
      (_root_.Graph.edgeArc_subset_pointSet hA) (by
        rw [edgeArc_segmentDrawing]
        exact left_mem_segment ℝ _ _)⟩
  have hA2K : A.2 ∈ V(K) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hA2Graph,
      (_root_.Graph.edgeArc_subset_pointSet hA) (by
        rw [edgeArc_segmentDrawing]
        exact right_mem_segment ℝ _ _)⟩
  have hUKcompat : (T.union C).Compatible K :=
    _root_.Graph.Compatible.of_le_le
      (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
        (_root_.Graph.pathGraphOf_le hD.isWalk))
      (_root_.Graph.traceGraph_le _)
  have hAne : A.1 ≠ A.2 :=
    localGridEdges_nondeg hs (one_le_localGridCount s epsilon) A hAList
  have hAll2 : ((T.union C).union K).IsTwoConnected :=
    hU2.union hUKcompat hK2 hAne hA1U hA1K hA2U hA2K
  apply hAll2.of_le_of_vertexSet_subset
    (_root_.Graph.union_le
      (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
        (_root_.Graph.pathGraphOf_le hD.isWalk))
      (_root_.Graph.traceGraph_le _))
  intro x hx
  rw [_root_.Graph.vertexSet_union]
  have hxPoint : x ∈ _root_.Graph.pointSet w.graph w.drawing :=
    _root_.Graph.vertexSet_subset_pointSet hx
  rw [w.graph_pointSet] at hxPoint
  rcases hxPoint with hxOuter | hxRest
  · exact Or.inl (Or.inl (by
      rw [_root_.Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inr hxOuter⟩))
  · rcases hxRest with hxCoreJ | hxGrid
    · rcases hxCoreJ with hxCore | hxJ
      · exact Or.inl (Or.inl (by
          rw [_root_.Graph.traceGraph_vertexSet]
          exact ⟨hx, by
            rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
            exact Or.inl hxCore⟩))
      · exact Or.inl (Or.inr (by
          rw [_root_.Graph.pathGraphOf_vertexSet]
          apply
            (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
              hD.isWalk hx
          rw [hcover]
          exact hxJ))
    · exact Or.inr (by
        rw [_root_.Graph.traceGraph_vertexSet]
        exact ⟨hx, by rwa [localGrid_eq, pieceListGraph_pointSet]⟩)

end CrosscutOverlayRelabeling

end SourceNonboundarySegmentCover

/-- The concrete output required from a local-grid source attachment: a finite source extension
whose carrier contains the complete raw local grid. -/
structure LocalGridSourceExtensionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (p : Plane) (s epsilon : ℝ) where
  graph : _root_.Graph Plane γ
  drawing : γ → ℝ → Plane
  isSourceExtension : IsSourceExtension P.src srcOuter srcDom graph drawing
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet graph drawing

/-- The boundary-touching crosscut construction after its two endpoint subdivisions.  This
packages every global graph property except connectedness after deleting the wild outer curve;
that last property is exactly what the blueprint's finite component-joining loop supplies. -/
structure RefinedCrosscutOverlayData
    {F : γ} {A : Piece} (r : RefinedSourceFaceCrosscutData P F A)
    (p : Plane) (s epsilon : ℝ) where
  cover : SourceNonboundarySegmentCover r.subdivision.pair
  relabeling : cover.CrosscutOverlayRelabeling r.crosscutData.crosscut p s epsilon []
  isDrawing : relabeling.graph.IsDrawing relabeling.drawing
  isTwoConnected : relabeling.graph.IsTwoConnected
  sourceSkeleton_subset :
    r.subdivision.pair.src.skeletonSet ⊆
      _root_.Graph.pointSet relabeling.graph relabeling.drawing
  pointSet_subset :
    _root_.Graph.pointSet relabeling.graph relabeling.drawing ⊆ srcDom
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet relabeling.graph relabeling.drawing

/-- The boundary-touching branch now constructs a plane, 2-connected, domain-contained mixed
overlay after a matched subdivision at the two crosscut endpoints.  The construction also
retains the entire refined source skeleton and the raw local grid. -/
theorem GeneratedPair.exists_refinedCrosscutOverlayData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      RefinedCrosscutOverlayData r p s epsilon) := by
  obtain ⟨d⟩ := P.exists_sourceFaceCrosscutData hF hFbdd hab hAline hy
  obtain ⟨r⟩ := d.exists_refinement
  obtain ⟨Q⟩ := r.subdivision.pair.exists_sourceNonboundarySegmentCover
  obtain ⟨w⟩ := Q.exists_crosscutOverlayRelabeling
    r.crosscutData.crosscut p s epsilon []
  have hJsource :
      r.crosscutData.crosscut.1 ∈ r.subdivision.pair.src.skeletonSet ∧
        r.crosscutData.crosscut.2 ∈ r.subdivision.pair.src.skeletonSet := by
    rw [r.subdivision.skeletonSet_eq]
    exact ⟨r.crosscutData.left_mem_skeleton, r.crosscutData.right_mem_skeleton⟩
  exact ⟨⟨r, {
    cover := Q
    relabeling := w
    isDrawing := w.graph_isDrawing hs r.crosscutData.nondeg r.geometry hwindow
    isTwoConnected := w.graph_isTwoConnected_of_crosscut_grid_edge
      hs r.crosscutData.nondeg r.geometry hwindow hJsource hA r.crosscutData.grid_subset
    sourceSkeleton_subset := w.sourceSkeleton_subset_graph
    pointSet_subset := w.graph_pointSet_subset hs r.geometry hwindow
    localGrid_subset := w.localGrid_subset_graph
  }⟩⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.OverlayExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Extending an existing straight overlay

The final component-joining step of the local-grid construction starts from an already
subdivided straight inner overlay and appends one polygonal joining arc.  Reusing the original
source pieces would lose the old cut points.  Instead, this module lists the *current overlay
edges* as the new source pieces and retains every current vertex as a prescribed cut point.

The resulting overlay is automatically a plane subdivision of the old overlay.  This is the
finite straight-line engine needed before the wild outer graph and the joining ear are glued.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

namespace IsPlaneSubdivisionExtension

variable {β δ κ : Type*}
  {G : Graph Plane β} {Gdraw : β → ℝ → Plane}
  {H : Graph Plane δ} {Hdraw : δ → ℝ → Plane}
  {K : Graph Plane κ} {Kdraw : κ → ℝ → Plane}

/-- Plane subdivision extensions compose.  At a point of an old edge away from final vertices,
the intermediate carrier supplies an intermediate edge; both absorption clauses then apply. -/
theorem trans (hGH : IsPlaneSubdivisionExtension G Gdraw H Hdraw)
    (hHK : IsPlaneSubdivisionExtension H Hdraw K Kdraw) :
    IsPlaneSubdivisionExtension G Gdraw K Kdraw where
  finite := hHK.finite
  oldIsDrawing := hGH.oldIsDrawing
  isDrawing := hHK.isDrawing
  vertexSet_subset := hGH.vertexSet_subset.trans hHK.vertexSet_subset
  pointSet_subset := hGH.pointSet_subset.trans hHK.pointSet_subset
  edge_subset := by
    intro e he f hf hmeet
    obtain ⟨z, hzf, hze, hznotK⟩ := hmeet
    have hzH : z ∈ Graph.pointSet H Hdraw :=
      hGH.pointSet_subset (Graph.edgeArc_subset_pointSet he hze)
    rcases hzH with hzHV | hzHE
    · exact (hznotK (hHK.vertexSet_subset hzHV)).elim
    · obtain ⟨g, hg, hzg⟩ := Set.mem_iUnion₂.1 hzHE
      have hznotH : z ∉ V(H) := fun hzV => hznotK (hHK.vertexSet_subset hzV)
      exact (hHK.edge_subset hg hf ⟨z, hzf, hzg, hznotK⟩).trans
        (hGH.edge_subset he hg ⟨z, hzg, hze, hznotH⟩)

end IsPlaneSubdivisionExtension

/-- The already-subdivided edges of a finite straight overlay, listed as pieces. -/
noncomputable def currentOverlayPieces (pieces : List Piece) (extra : List Plane) : List Piece :=
  (attachGraph pieces extra).edgeFinset.toList

@[simp] theorem mem_currentOverlayPieces {pieces : List Piece} {extra : List Plane} {R : Piece} :
    R ∈ currentOverlayPieces pieces extra ↔ R ∈ E(attachGraph pieces extra) := by
  rw [currentOverlayPieces, Finset.mem_toList, Graph.mem_edgeFinset]

/-- Append further straight pieces to the current overlay edge list. -/
noncomputable def extendedOverlayPieces
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) : List Piece :=
  currentOverlayPieces pieces extra ++ joins

/-- Re-overlay the current straight graph together with the joining pieces, retaining every
old vertex as a cut point. -/
noncomputable def extendOverlay
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) : Graph Plane Piece :=
  attachGraph (extendedOverlayPieces pieces extra joins)
    (attachGraph pieces extra).vertexFinset.toList

instance extendOverlay_finite (pieces : List Piece) (extra : List Plane) (joins : List Piece) :
    (extendOverlay pieces extra joins).Finite := attachGraph_finite _ _

/-- Every current overlay edge is nondegenerate. -/
theorem currentOverlayPieces_nondeg {pieces : List Piece} {extra : List Plane}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) :
    ∀ R ∈ currentOverlayPieces pieces extra, R.Nondeg := by
  intro R hR
  have hRedge : R ∈ E(attachGraph pieces extra) := mem_currentOverlayPieces.1 hR
  change R ∈ overlayPieces pieces (attachPoints pieces extra) at hRedge
  exact overlayPieces_nondeg _ hpieces R hRedge

/-- The edge list of the current overlay has exactly the current overlay's carrier. -/
theorem cover_currentOverlayPieces (pieces : List Piece) (extra : List Plane) :
    cover (currentOverlayPieces pieces extra) =
      Graph.pointSet (attachGraph pieces extra) segmentDrawing := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_cover_iff.1 hx
    exact Graph.edgeArc_subset_pointSet (mem_currentOverlayPieces.1 hR) (by
      rwa [edgeArc_segmentDrawing])
  · intro hx
    rcases hx with hxV | hxE
    · change x ∈ V(overlayGraph pieces (attachPoints pieces extra)) at hxV
      obtain ⟨R, hR, hxR⟩ := hxV
      apply mem_cover_iff.2
      refine ⟨R, mem_currentOverlayPieces.2 hR, ?_⟩
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hxE
      exact mem_cover_iff.2 ⟨R, mem_currentOverlayPieces.2 hR, by
        rwa [edgeArc_segmentDrawing] at hxR⟩

/-- The extended overlay occupies exactly the old carrier together with the joining carrier. -/
theorem extendOverlay_pointSet
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) :
    Graph.pointSet (extendOverlay pieces extra joins) segmentDrawing =
      Graph.pointSet (attachGraph pieces extra) segmentDrawing ∪ cover joins := by
  rw [extendOverlay, attachGraph_pointSet, extendedOverlayPieces, cover_append,
    cover_currentOverlayPieces]

/-- The extended overlay is a finite straight-line plane graph. -/
theorem extendOverlay_isDrawing
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    Graph.IsDrawing (extendOverlay pieces extra joins) segmentDrawing := by
  apply attachGraph_isDrawing
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact currentOverlayPieces_nondeg hpieces R hR
  · exact hjoins R hR

/-- Every old overlay vertex is retained by the extended overlay. -/
theorem attachGraphVertices_subset_extendOverlay
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(attachGraph pieces extra) ⊆ V(extendOverlay pieces extra joins) := by
  intro x hx
  change x ∈ V(overlayGraph (extendedOverlayPieces pieces extra joins)
    (attachPoints (extendedOverlayPieces pieces extra joins)
      (attachGraph pieces extra).vertexFinset.toList))
  apply overlayGraph_mem_vertexSet_of_mem_cover
  · intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · exact currentOverlayPieces_nondeg hpieces R hR
    · exact hjoins R hR
  · apply mem_attachPoints_of_mem
    rw [Finset.mem_toList, Graph.mem_vertexFinset]
    exact hx
  · rw [extendedOverlayPieces, cover_append, cover_currentOverlayPieces]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- A new overlay edge meeting an old straight edge away from new vertices is one of its
subdivision pieces. -/
theorem extendOverlay_edge_subset
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {A : Piece}, A ∈ E(attachGraph pieces extra) → ∀ {R : Piece},
      R ∈ E(extendOverlay pieces extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (Graph.edgeArc segmentDrawing A \ V(extendOverlay pieces extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  obtain ⟨z, hzR, hzA, hznot⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (extendedOverlayPieces pieces extra joins)
        (attachGraph pieces extra).vertexFinset.toList)
      (P₀ := A)
      (List.mem_append_left joins (mem_currentOverlayPieces.2 hA))
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (extendOverlay_isDrawing hpieces hjoins).unique_edge_at
      hR hR' hznot hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- Every edge of the extended overlay is cut either from a current overlay edge or from one
of the newly appended pieces. -/
theorem extendOverlay_edge_source
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    {R : Piece} (hR : R ∈ E(extendOverlay pieces extra joins)) :
    (∃ A ∈ E(attachGraph pieces extra), R.seg ⊆ A.seg) ∨
      ∃ A ∈ joins, R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (extendedOverlayPieces pieces extra joins)
    (attachPoints (extendedOverlayPieces pieces extra joins)
      (attachGraph pieces extra).vertexFinset.toList) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, mem_currentOverlayPieces.1 hA, hsub⟩
  · exact Or.inr ⟨A, hA, hsub⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.SourceJoining
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal joining ears for boundary-touching source crosscuts

When both ends of the auxiliary face crosscut lie on the wild outer curve, deleting that curve
separates the crosscut/grid carrier from the old nonboundary source carrier.  The last step of
`prop:local-grid-attachment` joins those two carriers by a simple polygonal arc in the open
source domain.

This module begins with the finite inner construction: re-overlay the already-subdivided source
core, crosscut, and grid together with the joining segments, retaining every old inner vertex.
`OverlayExtension` then supplies the plane-subdivision certificate automatically.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

namespace Graph

variable {β : Type*} {G A B : _root_.Graph Plane β} {drawing : β → ℝ → Plane}

/-- Two edge-disjoint subgraphs of one plane drawing can meet only at vertices common to both.
This is the converse interface used when an already-plane union is re-subdivided on one side. -/
theorem IsDrawing.common_vertices_of_disjoint_subgraphs (h : G.IsDrawing drawing)
    (hA : A ≤ G) (hB : B ≤ G) (hdisj : Disjoint E(A) E(B))
    {x : Plane} (hxA : x ∈ _root_.Graph.pointSet A drawing)
    (hxB : x ∈ _root_.Graph.pointSet B drawing) :
    x ∈ V(A) ∩ V(B) := by
  rcases hxA with hxAV | hxAE
  · refine ⟨hxAV, ?_⟩
    rcases hxB with hxBV | hxBE
    · exact hxBV
    · obtain ⟨e, heB, hxe⟩ := Set.mem_iUnion₂.1 hxBE
      obtain ⟨u, v, huv⟩ := B.exists_isLink_of_mem_edgeSet heB
      rcases h.vertex_mem_edgeArc (hB.isLink_mono huv) (hA.vertexSet_mono hxAV) hxe with
        rfl | rfl
      · exact huv.left_mem
      · exact huv.right_mem
  · rcases hxB with hxBV | hxBE
    · refine ⟨?_, hxBV⟩
      obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.1 hxAE
      obtain ⟨u, v, huv⟩ := A.exists_isLink_of_mem_edgeSet heA
      rcases h.vertex_mem_edgeArc (hA.isLink_mono huv) (hB.vertexSet_mono hxBV) hxe with
        rfl | rfl
      · exact huv.left_mem
      · exact huv.right_mem
    · obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.1 hxAE
      obtain ⟨f, hfB, hxf⟩ := Set.mem_iUnion₂.1 hxBE
      have hef : e ≠ f := fun hef => Set.disjoint_left.1 hdisj heA (hef ▸ hfB)
      have hinter := h.edge_inter
        (hA.edgeSet_mono heA) (hB.edgeSet_mono hfB) hef hxe hxf
      obtain ⟨a, b, hab⟩ := A.exists_isLink_of_mem_edgeSet heA
      obtain ⟨c, d, hcd⟩ := B.exists_isLink_of_mem_edgeSet hfB
      have hxAV : x ∈ V(A) := by
        rcases h.vertex_mem_edgeArc (hA.isLink_mono hab) hinter.1 hxe with rfl | rfl
        · exact hab.left_mem
        · exact hab.right_mem
      have hxBV : x ∈ V(B) := by
        rcases h.vertex_mem_edgeArc (hB.isLink_mono hcd) hinter.1 hxf with rfl | rfl
        · exact hcd.left_mem
        · exact hcd.right_mem
      exact ⟨hxAV, hxBV⟩

end Graph

/-- The distinct head and last vertices of a polygonal chain are endpoints of segments retained
by `segsOf`, even when the input list contains repeated consecutive vertices. -/
theorem head_getLast_mem_endSet_segsOf {vs : List Plane} (hvs : vs ≠ [])
    (hne : vs.head hvs ≠ vs.getLast hvs) :
    vs.head hvs ∈ endSet (segsOf vs) ∧ vs.getLast hvs ∈ endSet (segsOf vs) := by
  classical
  induction vs with
  | nil => exact (hvs rfl).elim
  | cons u tl ih =>
      match tl with
      | [] => exact (hne rfl).elim
      | v :: rest =>
          rw [segsOf_cons_cons]
          by_cases huv : u = v
          · rw [if_pos huv]
            subst u
            exact ih (List.cons_ne_nil v rest) hne
          · rw [if_neg huv]
            constructor
            · exact ⟨(u, v), List.mem_cons_self, Or.inl rfl⟩
            · by_cases hvlast : v = (v :: rest).getLast (List.cons_ne_nil v rest)
              · exact ⟨(u, v), List.mem_cons_self, Or.inr (by
                  rw [List.getLast_cons (a := u) (List.cons_ne_nil v rest)]
                  exact hvlast.symm)⟩
              · obtain ⟨-, hlast⟩ := ih (List.cons_ne_nil v rest) hvlast
                obtain ⟨A, hA, hxA⟩ := hlast
                exact ⟨A, List.mem_cons_of_mem _ hA, by
                  rw [List.getLast_cons (a := u) (List.cons_ne_nil v rest)]
                  exact hxA⟩

namespace SourceNonboundarySegmentCover

variable {Q : SourceNonboundarySegmentCover P} {J : Piece} {p : Plane}
  {s epsilon : ℝ} {extra : List Plane}

/-- Re-overlay the complete auxiliary-crosscut inner graph together with a list of polygonal
joining segments. -/
noncomputable def joinedCrosscutOverlay
    (Q : SourceNonboundarySegmentCover P) (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) (joins : List Piece) : Graph Plane Piece :=
  extendOverlay (Q.crosscutPieces J p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins

instance joinedCrosscutOverlay_finite
    (Q : SourceNonboundarySegmentCover P) (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) (joins : List Piece) :
    (Q.joinedCrosscutOverlay J p s epsilon extra joins).Finite :=
  extendOverlay_finite _ _ _

/-- The joined inner overlay occupies exactly the old core/crosscut/grid carrier together with
the polygonal joining carrier. -/
theorem joinedCrosscutOverlay_pointSet (Q : SourceNonboundarySegmentCover P)
    (J : Piece) (p : Plane) (s epsilon : ℝ) (extra : List Plane) (joins : List Piece) :
    Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins) segmentDrawing =
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing ∪ cover joins := by
  exact extendOverlay_pointSet _ _ _

/-- The joined inner overlay is a finite straight-line plane graph. -/
theorem joinedCrosscutOverlay_isDrawing
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    Graph.IsDrawing (Q.joinedCrosscutOverlay J p s epsilon extra joins) segmentDrawing :=
  extendOverlay_isDrawing (Q.crosscutPieces_nondeg hs hJ) hjoins

/-- Every vertex of the core/crosscut/grid overlay survives the joining re-overlay. -/
theorem crosscutOverlayVertices_subset_joinedCrosscutOverlay
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(Q.crosscutOverlay J p s epsilon extra) ⊆
      V(Q.joinedCrosscutOverlay J p s epsilon extra joins) :=
  attachGraphVertices_subset_extendOverlay (Q.crosscutPieces_nondeg hs hJ) hjoins

/-- Every old inner edge is absorbed by its subdivision in the joined overlay. -/
theorem joinedCrosscutOverlay_old_edge_subset
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {A : Piece}, A ∈ E(Q.crosscutOverlay J p s epsilon extra) → ∀ {R : Piece},
      R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (Graph.edgeArc segmentDrawing A \
          V(Q.joinedCrosscutOverlay J p s epsilon extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  exact extendOverlay_edge_subset (Q.crosscutPieces_nondeg hs hJ) hjoins hA hR hmeet

/-- A joined-overlay edge meeting the joining carrier away from overlay vertices is absorbed by
that carrier. -/
theorem joinedCrosscutOverlay_join_subset
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {R : Piece}, R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (cover joins \ V(Q.joinedCrosscutOverlay J p s epsilon extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ cover joins := by
  intro R hR hmeet
  obtain ⟨z, hzR, hzJoin, hznot⟩ := hmeet
  obtain ⟨A, hA, hzA⟩ := mem_cover_iff.1 hzJoin
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints
        (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
          (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
        (Q.crosscutOverlay J p s epsilon extra).vertexFinset.toList)
      (P₀ := A)
      (List.mem_append_right
        (currentOverlayPieces (Q.crosscutPieces J p s epsilon)
          (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) hA)
      hzA
  have hzR'Arc : z ∈ Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.joinedCrosscutOverlay_isDrawing hs hJ hjoins).unique_edge_at
      hR hR' hznot hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact fun x hx => mem_cover_iff.2 ⟨A, hA, hR'A hx⟩

/-- Every endpoint of a joining segment is a vertex of the joined inner overlay. -/
theorem joinEnds_subset_joinedCrosscutOverlay
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    endSet joins ⊆ V(Q.joinedCrosscutOverlay J p s epsilon extra joins) := by
  intro x hx
  obtain ⟨A, hA, hxA⟩ := hx
  change x ∈ V(overlayGraph
    (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
    (attachPoints
      (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
      (Q.crosscutOverlay J p s epsilon extra).vertexFinset.toList))
  apply overlayGraph_mem_vertexSet_of_mem_cover
  · intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · exact currentOverlayPieces_nondeg (Q.crosscutPieces_nondeg hs hJ) R hR
    · exact hjoins R hR
  · exact attachPoints_endsAreCut _ _ A
      (List.mem_append_right _ hA) x hxA
  · exact mem_cover_iff.2 ⟨A, List.mem_append_right _ hA, by
      rcases hxA with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-! ### Fresh relabelling and the wild outer graph -/

/-- Fresh abstract edge names for the joined inner overlay. -/
structure JoinedCrosscutOverlayRelabeling
    (w : Q.CrosscutOverlayRelabeling J p s epsilon extra) (joins : List Piece) where
  name : Piece → γ
  name_inj : InjOn name E(Q.joinedCrosscutOverlay J p s epsilon extra joins)
  name_fresh : ∀ R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins),
    name R ∉ P.str.cells

/-- An infinite cell-name type supplies fresh names for the joined overlay. -/
theorem CrosscutOverlayRelabeling.exists_joinedRelabeling [Infinite γ]
    (w : Q.CrosscutOverlayRelabeling J p s epsilon extra) (joins : List Piece) :
    Nonempty (JoinedCrosscutOverlayRelabeling w joins) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.joinedCrosscutOverlay J p s epsilon extra joins) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace JoinedCrosscutOverlayRelabeling

variable {joins : List Piece}
  {w : Q.CrosscutOverlayRelabeling J p s epsilon extra}
  (u : JoinedCrosscutOverlayRelabeling w joins)

/-- The unchanged mapped wild outer graph. -/
abbrev outerGraph (_u : JoinedCrosscutOverlayRelabeling w joins) :
    _root_.Graph Plane γ := P.str.outerGraph.map P.src.pos

/-- The freshly relabelled joined inner overlay. -/
noncomputable abbrev innerGraph : _root_.Graph Plane γ :=
  (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelEdges u.name u.name_inj

/-- The mixed graph after adjoining the polygonal join. -/
noncomputable def graph : _root_.Graph Plane γ := u.outerGraph.union u.innerGraph

/-- The joined drawing keeps the wild outer parametrizations and draws every inner edge as a
straight segment. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
      u.name segmentDrawing e

theorem compatible : u.outerGraph.Compatible u.innerGraph := by
  apply _root_.Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, _root_.Graph.edgeSet_map, _root_.Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact u.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    u.drawing e = P.src.drawing e := by simp [drawing, he]

theorem drawing_of_inner {e : γ} (he : e ∈ E(u.innerGraph)) :
    u.drawing e =
      (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
        u.name segmentDrawing e := by
  rw [drawing, if_neg]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => u.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

theorem outer_isDrawing : u.outerGraph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply u.drawing_of_outer
  rwa [_root_.Graph.edgeSet_map] at he

theorem inner_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    u.innerGraph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.joinedCrosscutOverlay_isDrawing hs hJ hjoins).relabelEdges u.name_inj)
  intro e he
  exact u.drawing_of_inner he

theorem outer_pointSet :
    _root_.Graph.pointSet u.outerGraph u.drawing = srcOuter := by
  calc
    _root_.Graph.pointSet u.outerGraph u.drawing =
        _root_.Graph.pointSet u.outerGraph P.src.drawing := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval)
        (u.drawing_of_outer (by rwa [_root_.Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

theorem inner_pointSet :
    _root_.Graph.pointSet u.innerGraph u.drawing =
      _root_.Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins)
        segmentDrawing := by
  calc
    _root_.Graph.pointSet u.innerGraph u.drawing =
        _root_.Graph.pointSet u.innerGraph
          ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
            u.name segmentDrawing) := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval) (u.drawing_of_inner he)
    _ = _root_.Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins)
        segmentDrawing := _root_.Graph.pointSet_relabelEdges u.name_inj

/-- The joined inner overlay remains plane when every joining segment lies in the open source
domain. -/
theorem graph_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    u.graph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    u.outer_isDrawing (u.inner_isDrawing hs hJ hjoins) u.compatible
  intro x hxOuter hxInner
  rw [u.outer_pointSet] at hxOuter
  rw [u.inner_pointSet, Q.joinedCrosscutOverlay_pointSet] at hxInner
  rcases hxInner with hxOldInner | hxJoin
  · have hxOldOuter : x ∈ _root_.Graph.pointSet w.outerGraph w.drawing := by
      rwa [w.outer_pointSet]
    have hxOldInner' : x ∈ _root_.Graph.pointSet w.innerGraph w.drawing := by
      rwa [w.inner_pointSet]
    have hOldDisjoint : Disjoint E(w.outerGraph) E(w.innerGraph) := by
      rw [Set.disjoint_left, _root_.Graph.edgeSet_map,
        _root_.Graph.edgeSet_relabelEdges]
      intro e heOuter heInner
      obtain ⟨R, hR, hname⟩ := heInner
      rw [← hname] at heOuter
      exact w.name_fresh R hR
        (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))
    have hxOldVertices :=
      Schoenflies.Graph.IsDrawing.common_vertices_of_disjoint_subgraphs
        (w.graph_isDrawing hs hJ hJgeom hwindow)
        (_root_.Graph.left_le_union _ _) w.compatible.right_le_union hOldDisjoint
        hxOldOuter hxOldInner'
    refine ⟨hxOldVertices.1, ?_⟩
    rw [_root_.Graph.vertexSet_relabelEdges] at hxOldVertices ⊢
    exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
      hs hJ hjoins hxOldVertices.2
  · exact ((hjoinsOpen hxJoin).2 hxOuter).elim

/-- The joined mixed graph is finite. -/
theorem graph_finite : u.graph.Finite where
  finite_vertexSet := by
    rw [graph, _root_.Graph.vertexSet_union, outerGraph, _root_.Graph.vertexSet_map,
      _root_.Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union
      (_root_.Graph.finite_vertexSet
        (Q.joinedCrosscutOverlay J p s epsilon extra joins))
  finite_edgeSet := by
    rw [graph, _root_.Graph.edgeSet_union, outerGraph, _root_.Graph.edgeSet_map,
      _root_.Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((_root_.Graph.finite_edgeSet
        (Q.joinedCrosscutOverlay J p s epsilon extra joins)).image u.name)

/-- Exact carrier of the joined mixed graph. -/
theorem graph_pointSet :
    _root_.Graph.pointSet u.graph u.drawing =
      _root_.Graph.pointSet w.graph w.drawing ∪ cover joins := by
  rw [graph, _root_.Graph.pointSet_union, u.outer_pointSet, u.inner_pointSet,
    Q.joinedCrosscutOverlay_pointSet]
  calc
    srcOuter ∪
        (_root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
          segmentDrawing ∪ cover joins) =
        (srcOuter ∪
          _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing) ∪
            cover joins := by ac_rfl
    _ = _root_.Graph.pointSet w.graph w.drawing ∪ cover joins := by
      rw [CrosscutOverlayRelabeling.graph, _root_.Graph.pointSet_union,
        w.outer_pointSet, w.inner_pointSet]

/-- Every vertex of the old mixed crosscut graph survives the joining re-overlay. -/
theorem oldVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(w.graph) ⊆ V(u.graph) := by
  intro x hx
  rw [CrosscutOverlayRelabeling.graph, _root_.Graph.vertexSet_union] at hx
  rw [graph, _root_.Graph.vertexSet_union]
  rcases hx with hxOuter | hxInner
  · exact Or.inl hxOuter
  · exact Or.inr (by
      rw [_root_.Graph.vertexSet_relabelEdges] at hxInner ⊢
      exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
        hs hJ hjoins hxInner)

/-- A new mixed edge meeting an old mixed edge away from new vertices is one of that old edge's
subdivision pieces. -/
theorem old_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(w.graph) → ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩
        (_root_.Graph.edgeArc w.drawing e \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ _root_.Graph.edgeArc w.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hze, hznot⟩ := hmeet
  rcases he with heOuter | heInner
  · have heAbstract : e ∈ E(P.str.outerGraph) := by
      rwa [_root_.Graph.edgeSet_map] at heOuter
    have heNew : e ∈ E(u.graph) := Or.inl heOuter
    have hzeNew : z ∈ _root_.Graph.edgeArc u.drawing e := by
      have hu := u.drawing_of_outer heAbstract
      have hw := w.drawing_of_outer heAbstract
      rw [_root_.Graph.edgeArc, hu]
      rw [_root_.Graph.edgeArc, hw] at hze
      exact hze
    have hef : e = f :=
      (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).unique_edge_at
        heNew hf hznot hzeNew hzf
    subst f
    have hu := u.drawing_of_outer heAbstract
    have hw := w.drawing_of_outer heAbstract
    intro y hy
    rw [_root_.Graph.edgeArc, hu] at hy
    rw [_root_.Graph.edgeArc, hw]
    exact hy
  · obtain ⟨A, hA, rfl⟩ := heInner
    have hAOld : w.name A ∈ E(w.innerGraph) := ⟨A, hA, rfl⟩
    have hOldArc : _root_.Graph.edgeArc w.drawing (w.name A) =
        _root_.Graph.edgeArc segmentDrawing A := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name A) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name A) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (w.drawing_of_inner hAOld)
        _ = _root_.Graph.edgeArc segmentDrawing A :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hA
    rcases hf with hfOuter | hfInner
    · exfalso
      have hzOldOuter : z ∈ _root_.Graph.pointSet w.outerGraph w.drawing := by
        rw [w.outer_pointSet, ← u.outer_pointSet]
        exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
      have hzOldInner : z ∈ _root_.Graph.pointSet w.innerGraph w.drawing :=
        _root_.Graph.edgeArc_subset_pointSet hAOld (hOldArc ▸ hze)
      have hOldDisjoint : Disjoint E(w.outerGraph) E(w.innerGraph) := by
        rw [Set.disjoint_left, _root_.Graph.edgeSet_map,
          _root_.Graph.edgeSet_relabelEdges]
        intro g hgOuter hgInner
        obtain ⟨R, hR, hname⟩ := hgInner
        rw [← hname] at hgOuter
        exact w.name_fresh R hR
          (P.str.mem_cells_of_mem_edgeSet
            (P.str.outerGraph_le.edgeSet_mono hgOuter))
      have hzOldVertex :=
        Schoenflies.Graph.IsDrawing.common_vertices_of_disjoint_subgraphs
          (w.graph_isDrawing hs hJ hJgeom hwindow)
          (_root_.Graph.left_le_union _ _) w.compatible.right_le_union hOldDisjoint
          hzOldOuter hzOldInner |>.2
      apply hznot
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by
        rw [_root_.Graph.vertexSet_relabelEdges] at hzOldVertex ⊢
        exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
          hs hJ hjoins hzOldVertex)
    · obtain ⟨R, hR, rfl⟩ := hfInner
      have hRNew : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
      have hNewArc : _root_.Graph.edgeArc u.drawing (u.name R) =
          _root_.Graph.edgeArc segmentDrawing R := by
        calc
          _root_.Graph.edgeArc u.drawing (u.name R) =
              _root_.Graph.edgeArc
                ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                  u.name segmentDrawing) (u.name R) := by
            simpa only [_root_.Graph.edgeArc] using congrArg
              (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRNew)
          _ = _root_.Graph.edgeArc segmentDrawing R :=
            _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
      rw [hNewArc, hOldArc]
      apply Q.joinedCrosscutOverlay_old_edge_subset hs hJ hjoins hA hR
      refine ⟨z, hNewArc ▸ hzf, hOldArc ▸ hze, ?_⟩
      intro hzLocal
      apply hznot
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The joined mixed graph is a plane subdivision extension of the complete old mixed graph. -/
theorem oldGraph_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension w.graph w.drawing u.graph u.drawing where
  finite := u.graph_finite
  oldIsDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  isDrawing := u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen
  vertexSet_subset := u.oldVertices_subset_graph hs hJ hjoins
  pointSet_subset := by
    rw [u.graph_pointSet]
    exact subset_union_left
  edge_subset := by
    intro e he f hf hmeet
    exact u.old_edge_subset hs hJ hJgeom hwindow hjoins hjoinsOpen he hf hmeet

/-- The exact trace of the old mixed carrier remains 2-connected in the joined graph. -/
theorem oldTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (htwo : w.graph.IsTwoConnected) :
    (_root_.Graph.traceGraph u.graph u.drawing
      (_root_.Graph.pointSet w.graph w.drawing)).IsTwoConnected :=
  (u.oldGraph_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
    |>.trace_isTwoConnected htwo

/-- Every endpoint of a joining segment is a vertex of the joined mixed graph. -/
theorem joinEnds_subset_graph (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    endSet joins ⊆ V(u.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.joinEnds_subset_joinedCrosscutOverlay hs hJ hjoins hx)

/-- The complete polygonal joining carrier lies in the joined mixed graph. -/
theorem joins_subset_graph :
    cover joins ⊆ _root_.Graph.pointSet u.graph u.drawing := by
  rw [u.graph_pointSet]
  exact subset_union_right

/-- A joined mixed edge meeting the polygonal joining carrier away from mixed vertices is
absorbed by that carrier. -/
theorem graph_join_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩ (cover joins \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ cover joins := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzJoin, hznot⟩ := hmeet
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← u.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hjoinsOpen hzJoin).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hRInner : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
    have hArc : _root_.Graph.edgeArc u.drawing (u.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc u.drawing (u.name R) =
            _root_.Graph.edgeArc
              ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                u.name segmentDrawing) (u.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRInner)
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
    rw [hArc]
    apply Q.joinedCrosscutOverlay_join_subset hs hJ hjoins hR
    refine ⟨z, hArc ▸ hzf, hzJoin, ?_⟩
    intro hzLocal
    apply hznot
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The trace supported on the polygonal joining carrier occupies that carrier exactly. -/
theorem joinTrace_pointSet (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet
      (_root_.Graph.traceGraph u.graph u.drawing (cover joins)) u.drawing = cover joins :=
  _root_.Graph.pointSet_traceGraph_eq
    (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen)
    _ u.joins_subset_graph (by
      intro f hf hmeet
      exact u.graph_join_subset hs hJ hjoins hjoinsOpen hf hmeet)

/-- An arc presented by the joining pieces is the exact carrier of a path in the joined mixed
graph. -/
theorem exists_join_trace (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hArc : IsArcBetween (cover joins) x y) :
    ∃ D : List γ, u.graph.IsPath x D y ∧
      _root_.Graph.edgesCover u.drawing D = cover joins := by
  let T := _root_.Graph.traceGraph u.graph u.drawing (cover joins)
  have hTle : T ≤ u.graph := _root_.Graph.traceGraph_le _
  letI : u.graph.Finite := u.graph_finite
  letI : T.Finite := _root_.Graph.Finite.of_le hTle
  have hpoint : _root_.Graph.pointSet T u.drawing = cover joins :=
    u.joinTrace_pointSet hs hJ hJgeom hwindow hjoins hjoinsOpen
  have hxGraph : x ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hxEnd
  have hyGraph : y ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hyEnd
  have hxT : x ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hxGraph, hArc.left_mem⟩
  have hyT : y ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hyGraph, hArc.right_mem⟩
  have hTconn : T.Connected := _root_.Graph.connected_of_isPreconnected_pointSet
    ((u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).mono hTle)
    (hpoint.symm ▸ hArc.isArc.isConnected.isPreconnected) ⟨x, hxT⟩
  obtain ⟨D, hD⟩ := (hTconn.reaches hxT hyT).exists_isPath
  have hDGraph : u.graph.IsPath x D y := hD.mono hTle
  have hPathArc : IsArcBetween (_root_.Graph.edgesCover u.drawing D) x y :=
    (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).path_isArcBetween
      hDGraph (hDGraph.ne_nil hxy)
  have hcoverSub : _root_.Graph.edgesCover u.drawing D ⊆ cover joins := by
    rw [← hpoint]
    exact _root_.Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDGraph,
    hPathArc.eq_of_subset_arc hArc hArc hcoverSub Set.Subset.rfl⟩

/-- Attaching a polygonal joining arc between two old-carrier points makes the entire joined
mixed graph 2-connected. -/
theorem graph_isTwoConnected_of_join (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (hOldTwo : w.graph.IsTwoConnected)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hxOld : x ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hyOld : y ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hArc : IsArcBetween (cover joins) x y) :
    u.graph.IsTwoConnected := by
  obtain ⟨D, hD, hcover⟩ :=
    u.exists_join_trace hs hJ hJgeom hwindow hjoins hjoinsOpen
      hxy hxEnd hyEnd hArc
  let T := _root_.Graph.traceGraph u.graph u.drawing
    (_root_.Graph.pointSet w.graph w.drawing)
  let C := u.graph.pathGraphOf x D
  have hT2 : T.IsTwoConnected :=
    u.oldTrace_isTwoConnected hs hJ hJgeom hwindow hjoins hjoinsOpen hOldTwo
  have hxGraph : x ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hxEnd
  have hyGraph : y ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hyEnd
  have hxT : x ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hxGraph, hxOld⟩
  have hyT : y ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hyGraph, hyOld⟩
  have hTC : T.Compatible C :=
    _root_.Graph.Compatible.of_le_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk)
  have hUnion2 : (T.union C).IsTwoConnected :=
    hT2.ear hTC hD.isPathGraph_pathGraphOf hxy hxT hyT
  apply hUnion2.of_le_of_vertexSet_subset
    (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk))
  intro z hz
  rw [_root_.Graph.vertexSet_union]
  have hzPoint : z ∈ _root_.Graph.pointSet u.graph u.drawing :=
    _root_.Graph.vertexSet_subset_pointSet hz
  rw [u.graph_pointSet] at hzPoint
  rcases hzPoint with hzOld | hzJoin
  · exact Or.inl (by
      rw [_root_.Graph.traceGraph_vertexSet]
      exact ⟨hz, hzOld⟩)
  · exact Or.inr (by
      rw [_root_.Graph.pathGraphOf_vertexSet]
      apply (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen)
        |>.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hz
      rw [hcover]
      exact hzJoin)

/-- The joined graph remains a plane subdivision extension of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing u.graph u.drawing :=
  (w.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trans
    (u.oldGraph_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)

/-- The joined graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet u.graph u.drawing ⊆ srcDom := by
  rw [u.graph_pointSet]
  exact Set.union_subset (w.graph_pointSet_subset hs hJgeom hwindow)
    (hjoinsOpen.trans sdiff_subset)

/-- Every joined inner edge is cut either from an old core/crosscut/grid edge or from one of
the polygonal joining segments. -/
theorem joinedInner_edge_source {R : Piece}
    (hR : R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins)) :
    (∃ A ∈ E(Q.crosscutOverlay J p s epsilon extra), R.seg ⊆ A.seg) ∨
      ∃ A ∈ joins, R.seg ⊆ A.seg := by
  exact extendOverlay_edge_source hR

/-- Every joined mixed edge either lies on the wild outer curve or is polygonal with all
nonvertex points in the open source domain. -/
theorem graph_edge_dichotomy (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(u.graph) → _root_.Graph.edgeArc u.drawing e ⊆ srcOuter ∨
      (IsPolygonal (_root_.Graph.edgeArc u.drawing e) ∧
        _root_.Graph.edgeArc u.drawing e \ V(u.graph) ⊆ srcDom \ srcOuter) := by
  intro e he
  rcases he with heOuter | heInner
  · exact Or.inl (by
      intro x hx
      rw [← u.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet heOuter hx)
  · obtain ⟨R, hR, rfl⟩ := heInner
    have hRInner : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
    have hArc : _root_.Graph.edgeArc u.drawing (u.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc u.drawing (u.name R) =
            _root_.Graph.edgeArc
              ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                u.name segmentDrawing) (u.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRInner)
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
    rw [hArc]
    refine Or.inr ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
    intro x hx
    have hxSeg : x ∈ R.seg := by
      rw [← edgeArc_segmentDrawing]
      exact hx.1
    rcases joinedInner_edge_source (Q := Q) hR with hOld | hJoin
    · obtain ⟨A, hA, hRA⟩ := hOld
      obtain ⟨-, hAopen⟩ :=
        Q.crosscutOverlay_edge_dichotomy hs hJ hJgeom hwindow extra hA
      apply hAopen
      refine ⟨by
        rw [edgeArc_segmentDrawing]
        exact hRA hxSeg, ?_⟩
      intro hxOldVertex
      apply hx.2
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by
        rw [_root_.Graph.vertexSet_relabelEdges]
        exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
          hs hJ hjoins hxOldVertex)
    · obtain ⟨A, hA, hRA⟩ := hJoin
      exact hjoinsOpen (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩)

/-- A joined edge meeting an old source cell away from joined vertices is absorbed by that old
source edge. -/
theorem graph_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩ (P.src.cell e \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ _root_.Graph.edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznot⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have heSrc : e ∈ E(P.src.graph) := by rwa [P.src.edgeSet_graph]
  apply (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen).edge_subset
    heSrc hf
  refine ⟨z, hzf, ?_, hznot⟩
  rw [P.src.cell_edge hab] at hzCell
  exact hzCell.1

/-- A join running from the open crosscut to the old nonboundary source carrier makes the
joined carrier connected after deletion of the wild outer curve. -/
theorem graph_isConnected_diff_of_join (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg)
    {x y : Plane} (hxJ : x ∈ J.interior)
    (hySource : y ∈ P.src.skeletonSet \ srcOuter)
    (hArc : IsArcBetween (cover joins) x y) :
    IsConnected (_root_.Graph.pointSet u.graph u.drawing \ srcOuter) := by
  let Sset := P.src.skeletonSet \ srcOuter
  let Jset := J.seg \ srcOuter
  let Kset := _root_.Graph.pointSet
    (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hJinteriorConn : IsConnected J.interior :=
    (convex_openSegment J.1 J.2).isConnected
      ⟨midpoint ℝ J.1 J.2, midpoint_mem_openSegment J.1 J.2⟩
  have hJconn : IsConnected Jset := by
    apply hJinteriorConn.subset_closure
    · intro z hz
      exact ⟨openSegment_subset_segment ℝ _ _ hz, (hJgeom.interior_subset hz).2⟩
    · change J.seg \ srcOuter ⊆ closure (openSegment ℝ J.1 J.2)
      rw [closure_openSegment]
      exact sdiff_subset
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro z hzK hzOuter
    have hzCover : z ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzK
    have hzWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hzCover
    exact (hwindow hzWindow).2 hzOuter
  have hcarrier : _root_.Graph.pointSet u.graph u.drawing \ srcOuter =
      ((Sset ∪ Jset) ∪ Kset) ∪ cover joins := by
    ext z
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_union, Set.mem_union,
      Set.mem_sdiff, Set.mem_sdiff]
    constructor
    · rintro ⟨hzGraph, hzNotOuter⟩
      rw [u.graph_pointSet, w.graph_pointSet] at hzGraph
      rcases hzGraph with hzOld | hzJoin
      · rcases hzOld with hzOuter | hzRest
        · exact (hzNotOuter hzOuter).elim
        · rcases hzRest with hzCoreJ | hzGrid
          · rcases hzCoreJ with hzCore | hzJ
            · exact Or.inl (Or.inl (Or.inl ⟨by
                rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
                exact Or.inl hzCore, hzNotOuter⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨hzJ, hzNotOuter⟩))
          · exact Or.inl (Or.inr (by
              simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzGrid))
      · exact Or.inr hzJoin
    · rintro (⟨⟨⟨hzSource, hzNotOuter⟩ | ⟨hzJ, hzNotOuter⟩⟩ | hzK⟩ | hzJoin)
      · refine ⟨?_, hzNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hzSource
        rw [u.graph_pointSet, w.graph_pointSet]
        rcases hzSource with hzCore | hzOuter
        · exact Or.inl (Or.inr (Or.inl (Or.inl hzCore)))
        · exact Or.inl (Or.inl hzOuter)
      · exact ⟨by
          rw [u.graph_pointSet, w.graph_pointSet]
          exact Or.inl (Or.inr (Or.inl (Or.inr hzJ))), hzNotOuter⟩
      · exact ⟨by
          rw [u.graph_pointSet, w.graph_pointSet]
          exact Or.inl (Or.inr (Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzK))), hKmiss hzK⟩
      · exact ⟨by rw [u.graph_pointSet]; exact Or.inr hzJoin,
          (hjoinsOpen hzJoin).2⟩
  have hA1K : A.1 ∈ Kset := by
    apply _root_.Graph.edgeArc_subset_pointSet hA
    rw [edgeArc_segmentDrawing]
    exact left_mem_segment ℝ _ _
  have hA1J : A.1 ∈ Jset :=
    ⟨hAJ (left_mem_segment ℝ _ _), hKmiss hA1K⟩
  have hJK : IsConnected (Jset ∪ Kset) :=
    IsConnected.union ⟨A.1, hA1J, hA1K⟩ hJconn hKconn
  have hJoinConn : IsConnected (cover joins) := hArc.isArc.isConnected
  have hSourceJoin : IsConnected (Sset ∪ cover joins) :=
    IsConnected.union ⟨y, hySource, hArc.right_mem⟩ hsource hJoinConn
  have hxJset : x ∈ Jset :=
    ⟨openSegment_subset_segment ℝ _ _ hxJ, (hJgeom.interior_subset hxJ).2⟩
  have hAll : IsConnected ((Sset ∪ cover joins) ∪ (Jset ∪ Kset)) :=
    IsConnected.union ⟨x, Or.inr hArc.left_mem, Or.inl hxJset⟩ hSourceJoin hJK
  rw [hcarrier]
  convert hAll using 1
  all_goals try with_reducible_and_instances rfl
  ac_rfl

/-- The joined construction is a complete source extension. -/
theorem isSourceExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (hOldTwo : w.graph.IsTwoConnected)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hxOld : x ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hyOld : y ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hArc : IsArcBetween (cover joins) x y)
    (hconnected : IsConnected
      (_root_.Graph.pointSet u.graph u.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom u.graph u.drawing where
  finite := u.graph_finite
  isDrawing := u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen
  isTwoConnected := u.graph_isTwoConnected_of_join hs hJ hJgeom hwindow
    hjoins hjoinsOpen hOldTwo hxy hxEnd hyEnd hxOld hyOld hArc
  vertexSet_subset :=
    (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
      |>.vertexSet_subset
  skeletonSet_subset :=
    (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
      |>.pointSet_subset
  edge_subset := by
    intro e he f hf hmeet
    exact u.graph_edge_subset hs hJ hJgeom hwindow hjoins hjoinsOpen he hf hmeet
  pointSet_subset := u.graph_pointSet_subset hs hJgeom hwindow hjoinsOpen
  edge_dichotomy := by
    intro e he
    exact u.graph_edge_dichotomy hs hJ hJgeom hwindow hjoins hjoinsOpen he
  isConnected := hconnected

end JoinedCrosscutOverlayRelabeling

end SourceNonboundarySegmentCover

/-- The complete output of the boundary-crosscut joining construction. -/
structure JoinedLocalGridSourceExtensionData
    {F : γ} {A : Piece} (r : RefinedSourceFaceCrosscutData P F A)
    (p : Plane) (s epsilon : ℝ) where
  oldOverlay : RefinedCrosscutOverlayData r p s epsilon
  joins : List Piece
  joinedRelabeling :
    SourceNonboundarySegmentCover.JoinedCrosscutOverlayRelabeling
      oldOverlay.relabeling joins
  isSourceExtension :
    IsSourceExtension r.subdivision.pair.src srcOuter srcDom
      joinedRelabeling.graph joinedRelabeling.drawing
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet joinedRelabeling.graph joinedRelabeling.drawing

/-- Construct the manuscript's final polygonal component-joining ear.  A midpoint of the open
crosscut and a point of the connected old nonboundary carrier lie in the same open connected
source domain, so polygonal connectedness supplies a simple joining arc.  Re-overlaying its
segments and attaching its exact trace gives a complete local-grid source extension even when
both crosscut endpoints lie on the wild outer curve. -/
theorem RefinedCrosscutOverlayData.exists_joinedLocalGridSourceExtensionData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    {r : RefinedSourceFaceCrosscutData P F A}
    (o : RefinedCrosscutOverlayData r p s epsilon)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hopen : IsOpen (srcDom \ srcOuter))
    (hconn : IsPreconnected (srcDom \ srcOuter))
    (hsource : IsConnected r.subdivision.pair.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (JoinedLocalGridSourceExtensionData r p s epsilon) := by
  let d := r.crosscutData
  let x : Plane := midpoint ℝ d.crosscut.1 d.crosscut.2
  have hxJ : x ∈ d.crosscut.interior := midpoint_mem_openSegment _ _
  have hxOpen : x ∈ srcDom \ srcOuter := r.geometry.interior_subset hxJ
  obtain ⟨y, hyNonboundary⟩ := hsource.nonempty
  have hySource : y ∈ r.subdivision.pair.src.skeletonSet \ srcOuter := by
    rwa [r.subdivision.pair.src_nonboundary_eq] at hyNonboundary
  have hyOpen : y ∈ srcDom \ srcOuter :=
    ⟨r.subdivision.pair.src_isWeaklyAdmissible.skeletonSet_subset hySource.1,
      hySource.2⟩
  have hxy : x ≠ y := by
    intro hxy
    have hxFace : x ∈ P.src.cell F := r.crosscutData.interior_subset_face hxJ
    have hyOldSource : y ∈ P.src.skeletonSet := by
      rw [← r.subdivision.skeletonSet_eq]
      exact hySource.1
    exact Set.disjoint_left.1
      (P.src.disjoint_cell_skeletonSet P.src_isCellDecomposition
        r.crosscutData.face_mem) hxFace (hxy ▸ hyOldSource)
  obtain ⟨vs, hvs, hhead, hlast, hpolyOpen, hpolyArc⟩ :=
    exists_simple_poly_of_isPreconnected hopen hconn hxOpen hyOpen hxy
  let joins := segsOf vs
  have hxPoly : x ∈ poly vs := hpolyArc.left_mem
  have hyPoly : y ∈ poly vs := hpolyArc.right_mem
  have hcover : Schoenflies.cover joins = poly vs :=
    cover_segsOf_eq hxPoly hyPoly hxy
  have hjoins : ∀ R ∈ joins, R.Nondeg := segsOf_nondeg vs
  have hjoinsOpen : Schoenflies.cover joins ⊆ srcDom \ srcOuter := by
    rw [hcover]
    exact hpolyOpen
  have hjoinArc : IsArcBetween (Schoenflies.cover joins) x y := by
    rw [hcover]
    exact hpolyArc
  have hHeadLastNe : vs.head hvs ≠ vs.getLast hvs := by
    rw [hhead, hlast]
    exact hxy
  obtain ⟨hheadEnd, hlastEnd⟩ :=
    head_getLast_mem_endSet_segsOf hvs hHeadLastNe
  have hxEnd : x ∈ endSet joins := by
    rw [← hhead]
    exact hheadEnd
  have hyEnd : y ∈ endSet joins := by
    rw [← hlast]
    exact hlastEnd
  obtain ⟨u⟩ := o.relabeling.exists_joinedRelabeling joins
  have hxOld : x ∈ _root_.Graph.pointSet o.relabeling.graph o.relabeling.drawing := by
    rw [o.relabeling.graph_pointSet]
    exact Or.inr (Or.inl (Or.inr
      (openSegment_subset_segment ℝ _ _ hxJ)))
  have hyOld : y ∈ _root_.Graph.pointSet o.relabeling.graph o.relabeling.drawing :=
    o.relabeling.sourceSkeleton_subset_graph hySource.1
  have hsource' : IsConnected
      (r.subdivision.pair.src.skeletonSet \ srcOuter) := by
    rwa [r.subdivision.pair.src_nonboundary_eq] at hsource
  have hconnected : IsConnected
      (_root_.Graph.pointSet u.graph u.drawing \ srcOuter) :=
    u.graph_isConnected_diff_of_join hs r.geometry hwindow hsource'
      hjoinsOpen hA r.crosscutData.grid_subset hxJ hySource hjoinArc
  exact ⟨{
    oldOverlay := o
    joins := joins
    joinedRelabeling := u
    isSourceExtension :=
      u.isSourceExtension hs r.crosscutData.nondeg r.geometry hwindow
        hjoins hjoinsOpen o.isTwoConnected hxy hxEnd hyEnd hxOld hyOld
        hjoinArc hconnected
    localGrid_subset := o.localGrid_subset.trans (by
      rw [u.graph_pointSet]
      exact subset_union_left)
  }⟩

/-- Complete the boundary-touching local-grid attachment starting only from a bounded source
face and a grid edge whose relative interior lies on a line through that face.  The preliminary
matched subdivision preserves the old source carrier, so connectedness of the original
nonboundary source graph is exactly the connectedness needed by the polygonal joining step. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hopen : IsOpen (srcDom \ srcOuter))
    (hconn : IsPreconnected (srcDom \ srcOuter))
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  obtain ⟨⟨r, o⟩⟩ := P.exists_refinedCrosscutOverlayData
    hF hFbdd hab hAline hy hs hwindow hA
  have hrsource : IsConnected r.subdivision.pair.src.nonboundary := by
    rw [r.subdivision.pair.src_nonboundary_eq, r.subdivision.skeletonSet_eq,
      ← P.src_nonboundary_eq]
    exact hsource
  obtain ⟨j⟩ := o.exists_joinedLocalGridSourceExtensionData
    hs hwindow hopen hconn hrsource hA
  exact ⟨⟨r, j⟩⟩

/-- In the actual Schönflies source domain, the hypotheses needed to draw the final joining
arc are automatic consequences of Jordan separation: the closed domain minus its boundary is
the connected open inside region. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_inside
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  apply P.exists_joinedLocalGridSourceExtensionData hF hFbdd hab hAline hy
    hs hwindow
  · rw [union_inside_sdiff]
    exact hC.isOpen_inside
  · rw [union_inside_sdiff]
    exact hC.isConnected_inside.isPreconnected
  · exact hsource
  · exact hA

/-- Every point in the relative interior of a horizontal grid edge has the row's fixed second
coordinate. -/
theorem gridHEdge_interior_snd {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane}
    (hz : z ∈ (gridHEdge xc yc i j).interior) : z 1 = yc j := by
  change z ∈ openSegment ℝ (gridPt xc yc i j) (gridPt xc yc (i + 1) j) at hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, -, rfl⟩ := hz
  simp [AffineMap.lineMap_apply, gridPt]

/-- The relative interiors of a local grid's bottom and top leftmost edges are disjoint. -/
theorem localGrid_horizontal_extremes_interior_disjoint
    {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    Disjoint
      (gridHEdge (localGridX p s k) (localGridY p s k) 0 0).interior
      (gridHEdge (localGridX p s k) (localGridY p s k) 0 k).interior := by
  rw [Set.disjoint_left]
  intro z hzBottom hzTop
  have hzBottomCoord := gridHEdge_interior_snd hzBottom
  have hzTopCoord := gridHEdge_interior_snd hzTop
  have hrows : localGridY p s k 0 ≠ localGridY p s k k :=
    ne_of_lt ((localGridY_strictMono hs hk) (by omega))
  exact hrows (hzBottomCoord.symm.trans hzTopCoord)

/-- If the complete source/grid intersection has at most one point, at least one of two
opposite horizontal grid edges has relative interior disjoint from the source skeleton. -/
theorem GeneratedPair.exists_localGridEdge_interior_disjoint_of_common_subsingleton
    {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton) :
    ∃ A ∈ E(localGrid p s (localGridCount s epsilon)),
      Disjoint A.interior P.src.skeletonSet := by
  classical
  let k := localGridCount s epsilon
  let A₀ := gridHEdge (localGridX p s k) (localGridY p s k) 0 0
  let A₁ := gridHEdge (localGridX p s k) (localGridY p s k) 0 k
  have hk : 1 ≤ k := one_le_localGridCount s epsilon
  have hA₀List : A₀ ∈ localGridEdges p s k := by
    change A₀ ∈ gridEdges (localGridX p s k) (localGridY p s k) k k
    exact gridHEdge_mem_gridEdges (by omega) (Nat.zero_le k) hk
  have hA₁List : A₁ ∈ localGridEdges p s k := by
    change A₁ ∈ gridEdges (localGridX p s k) (localGridY p s k) k k
    exact gridHEdge_mem_gridEdges (by omega) (le_refl k) hk
  have hA₀ : A₀ ∈ E(localGrid p s k) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA₀List
  have hA₁ : A₁ ∈ E(localGrid p s k) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA₁List
  by_cases hdisj₀ : Disjoint A₀.interior P.src.skeletonSet
  · exact ⟨A₀, hA₀, hdisj₀⟩
  · have hdisj₁ : Disjoint A₁.interior P.src.skeletonSet := by
      by_contra hnot
      rw [Set.disjoint_left] at hdisj₀ hnot
      push Not at hdisj₀ hnot
      obtain ⟨z₀, hz₀Int, hz₀Source⟩ := hdisj₀
      obtain ⟨z₁, hz₁Int, hz₁Source⟩ := hnot
      have hz₀Grid : z₀ ∈ _root_.Graph.pointSet (localGrid p s k) segmentDrawing := by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact mem_cover_iff.2 ⟨A₀, hA₀List,
          openSegment_subset_segment ℝ _ _ hz₀Int⟩
      have hz₁Grid : z₁ ∈ _root_.Graph.pointSet (localGrid p s k) segmentDrawing := by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact mem_cover_iff.2 ⟨A₁, hA₁List,
          openSegment_subset_segment ℝ _ _ hz₁Int⟩
      have hzEq : z₀ = z₁ :=
        hcommon ⟨hz₀Source, hz₀Grid⟩ ⟨hz₁Source, hz₁Grid⟩
      exact Set.disjoint_left.1
        (localGrid_horizontal_extremes_interior_disjoint hs hk)
        hz₀Int (hzEq ▸ hz₁Int)
    exact ⟨A₁, hA₁, hdisj₁⟩

/-- In the two-common-point branch, retaining those points explicitly in the raw source/grid
overlay gives the complete local-grid source extension directly. -/
theorem GeneratedPair.exists_localGridSourceExtensionData_of_common_not_subsingleton
    [Infinite γ] {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected P.src.nonboundary)
    (hcommon : ¬(P.src.skeletonSet ∩
      _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing).Subsingleton) :
    Nonempty (LocalGridSourceExtensionData P p s epsilon) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hcommon
  obtain ⟨Q⟩ := P.exists_sourceNonboundarySegmentCover
  obtain ⟨w⟩ := Q.exists_localOverlayRelabeling p s epsilon [a, b]
  have commonVertex : ∀ {x : Plane}, x ∈ [a, b] →
      x ∈ P.src.skeletonSet →
      x ∈ _root_.Graph.pointSet
        (localGrid p s (localGridCount s epsilon)) segmentDrawing →
      x ∈ V(w.graph) := by
    intro x hxList hxSource hxGrid
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [localGrid_eq, pieceListGraph_pointSet] using hxGrid
    have hxWindow : x ∈ Plane.closedSquare p s :=
      SourceNonboundarySegmentCover.cover_localGridEdges_subset_closedSquare hs
        (one_le_localGridCount s epsilon) hxCover
    have hxNotOuter : x ∉ srcOuter := (hwindow hxWindow).2
    have hxCore : x ∈
        _root_.Graph.pointSet P.sourceNonboundaryGraph P.src.drawing := by
      rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
      exact hxSource.resolve_right hxNotOuter
    change x ∈ V(w.outerGraph.union w.innerGraph)
    rw [_root_.Graph.vertexSet_union]
    refine Or.inr ?_
    rw [_root_.Graph.vertexSet_relabelEdges]
    change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
      (attachPoints (Q.localPieces p s epsilon)
        ([a, b] ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
    apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
    · exact mem_attachPoints_of_mem (List.mem_append_left _ hxList)
    · change x ∈ cover (Q.pieces ++
        localGridEdges p s (localGridCount s epsilon))
      rw [cover_append, Q.cover_eq]
      exact Or.inl hxCore
  have haV : a ∈ V(w.graph) := commonVertex (by simp) ha.1 ha.2
  have hbV : b ∈ V(w.graph) := commonVertex (by simp) hb.1 hb.2
  exact ⟨{
    graph := w.graph
    drawing := w.drawing
    isSourceExtension :=
      w.isSourceExtension_of_source_connected_two_common hs hwindow hsource
        hab haV hbV ha.1 hb.1 ha.2 hb.2
    localGrid_subset := w.localGrid_subset_graph
  }⟩

/-- A raw grid edge whose open segment misses the current source skeleton lies in one bounded
source face.  Thus it supplies all of the face-selection data required by the auxiliary
crosscut and joining construction. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_of_disjoint_edge
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hdisj : Disjoint A.interior P.src.skeletonSet) :
    Nonempty (Σ F : γ, Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hAne : A.Nondeg :=
    localGridEdges_nondeg hs (one_le_localGridCount s epsilon) A hAList
  have hADom : A.interior ⊆ C ∪ inside C := by
    intro z hz
    exact (hwindow (SourceNonboundarySegmentCover.cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, openSegment_subset_segment ℝ _ _ hz⟩))).1
  obtain ⟨F, hF, hAF, -⟩ :=
    P.src_isCellDecomposition.exists_unique_face_subset_cell
      (P.src_isCellDecomposition.cellsAbsorb P.src_isFaceJordan)
      (convex_openSegment A.1 A.2).isPreconnected
      ⟨midpoint ℝ A.1 A.2, midpoint_mem_openSegment A.1 A.2⟩
      hADom hdisj
  have hAline : A.interior ⊆ Plane.line A.1 A.2 ∩ P.src.cell F := by
    intro z hz
    refine ⟨?_, hAF hz⟩
    change z ∈ openSegment ℝ A.1 A.2 at hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact Plane.lineMap_mem_line A.1 A.2 t
  obtain ⟨⟨r, j⟩⟩ := P.exists_joinedLocalGridSourceExtensionData_inside
    hC hF (P.src_isFaceJordan.isBounded hF) hAne hAline
      (midpoint_mem_openSegment A.1 A.2) hs hwindow hsource hA
  exact ⟨⟨F, r, j⟩⟩

/-- The at-most-one-common-point branch automatically supplies a skeleton-disjoint grid edge,
so the completed face-crosscut and joining construction applies without further choices. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_of_common_subsingleton
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton) :
    Nonempty (Σ F : γ, Σ A : Piece,
      Σ r : RefinedSourceFaceCrosscutData P F A,
        JoinedLocalGridSourceExtensionData r p s epsilon) := by
  obtain ⟨A, hA, hdisj⟩ :=
    P.exists_localGridEdge_interior_disjoint_of_common_subsingleton hs hcommon
  obtain ⟨⟨F, r, j⟩⟩ :=
    P.exists_joinedLocalGridSourceExtensionData_of_disjoint_edge
      hC hs hwindow hsource hA hdisj
  exact ⟨⟨F, A, r, j⟩⟩

/-- Exhaustive local-grid attachment.  With two distinct source/grid intersection points the
raw overlay extends the current pair directly.  Otherwise a raw grid edge misses the skeleton
in its relative interior, and a matched endpoint subdivision followed by the crosscut and
polygonal joining ears produces the extension. -/
theorem GeneratedPair.exists_localGridSourceExtensionData_cases
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridSourceExtensionData P p s epsilon) ∨
      Nonempty (Σ F : γ, Σ A : Piece,
        Σ r : RefinedSourceFaceCrosscutData P F A,
          JoinedLocalGridSourceExtensionData r p s epsilon) := by
  classical
  by_cases hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton
  · exact Or.inr
      (P.exists_joinedLocalGridSourceExtensionData_of_common_subsingleton
        hC hs hwindow hsource hcommon)
  · exact Or.inl
      (P.exists_localGridSourceExtensionData_of_common_not_subsingleton
        hs hwindow hsource hcommon)

namespace GeneratedPair.SubdivideSetData

/-- A matched finite source-skeleton subdivision is already a stage transition. -/
theorem stageTransition {s : Set Plane} (r : GeneratedPair.SubdivideSetData P s) :
    StageTransition r.pair P r.parent where
  refines_src := r.refines_src
  refines_tgt := r.refines_tgt
  sourceSkeletonSet_subset := by
    rw [r.skeletonSet_eq]
  homeo_eqOn := r.homeo_eqOn

end GeneratedPair.SubdivideSetData

/-- The uniform stage-level output of local-grid attachment, after running forward finite
transfer.  Both geometric branches now return one generated refinement of the original pair,
with admissibility restored and the complete raw local grid in its source skeleton. -/
structure LocalGridForwardStageData {C : Set Plane}
    (P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom)
    (p : Plane) (s epsilon : ℝ) where
  pair : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom
  parent : γ → γ
  transition : StageTransition pair P parent
  src_isAdmissible : pair.src.IsAdmissible C (C ∪ inside C)
  tgt_isAdmissible : pair.tgt.IsAdmissible tgtOuter tgtDom
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      pair.src.skeletonSet

/-- **Local-grid forward successor.** The source/grid intersection dichotomy,
the auxiliary face crosscut, endpoint subdivisions, polygonal joining ear, and forward finite
transfer are all internal. -/
theorem GeneratedPair.exists_localGridForwardStageData
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridForwardStageData P p s epsilon) := by
  rcases P.exists_localGridSourceExtensionData_cases hC hs hwindow hsource with
    hdirect | hrefined
  · obtain ⟨d⟩ := hdirect
    obtain ⟨T, par, hT⟩ :=
      finite_transfer_toward_square d.isSourceExtension
    exact ⟨{
      pair := T
      parent := par
      transition := hT.stageTransition
      src_isAdmissible := hT.src_isAdmissible
      tgt_isAdmissible := hT.tgt_isAdmissible
      localGrid_subset := by
        rw [hT.skeletonSet_eq]
        exact d.localGrid_subset
    }⟩
  · obtain ⟨⟨F, A, r, j⟩⟩ := hrefined
    obtain ⟨T, par, hT⟩ :=
      finite_transfer_toward_square j.isSourceExtension
    exact ⟨{
      pair := T
      parent := r.subdivision.parent ∘ par
      transition := hT.stageTransition.trans r.subdivision.stageTransition
      src_isAdmissible := hT.src_isAdmissible
      tgt_isAdmissible := hT.tgt_isAdmissible
      localGrid_subset := by
        rw [hT.skeletonSet_eq]
        exact j.localGrid_subset
    }⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.StageTower
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.joinedCrosscutOverlay_finite _root_.Schoenflies.SourceNonboundarySegmentCover.localOverlay_finite _root_.Schoenflies.TargetSegmentCover.meshOverlay_finite _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.extendOverlay_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
attribute [-simp] _root_.Schoenflies.HexData.cellSet_chord _root_.Schoenflies.HexData.cellSet_edge _root_.Schoenflies.HexData.cellSet_face _root_.Schoenflies.HexData.cellSet_vert _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.generatedPair_homeo _root_.Schoenflies.InitialData.generatedPair_src _root_.Schoenflies.InitialData.generatedPair_str _root_.Schoenflies.InitialData.generatedPair_tgt _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.TargetSegmentCover.mem_openTargetEdgePieces _root_.Schoenflies.TargetSegmentCover.mem_squareMeshPieces _root_.Schoenflies.attachGraph_pointSet _root_.Schoenflies.initialStructure_faces _root_.Schoenflies.initialStructure_outerGraph _root_.Schoenflies.initialStructure_skel _root_.Schoenflies.initialStructure_sub _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.mem_currentOverlayPieces _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# From a sequence of transferred stages to a `LimitTower`

Two interfaces in this library were designed from opposite ends and have never met.

* `Schoenflies.GeneratedPair` (`FiniteTransfer.lean`) is what `thm:finite-transfer` consumes and
  produces: one abstract cell structure, its two realizations, the skeleton homeomorphism, the
  two cell decompositions, and weak admissibility on both sides.
* `Schoenflies.CellStructure.LimitTower` (`LimitMap.lean`) is what the limit section consumes:
  the same data indexed by `ℕ`, plus the nesting and the two halves of `prop:shrinking-stars`.

This module joins them. `Schoenflies.StageSequence` is a sequence of `GeneratedPair`s carrying
exactly the extra data the recursion of `quantitative-refinement` produces at each step — the
shared parent map, the growth of the source skeleton, the nesting of the skeleton maps, and the
two shrinking estimates — and `StageSequence.limitTower` turns one into a `LimitTower` for the
concrete source and target of the problem.

Every field is either read off a
`GeneratedPair` or is one of the four recorded facts about the concrete domains. The point of
writing it before the recursion exists is that it pins the interface down: the recursion now has
a single named target, and any mismatch between what `thm:finite-transfer` delivers and what the
limit section demands shows up here rather than at the end. Two such mismatches would otherwise
have been easy to miss, and both check out:

* `LimitTower` wants the *same* parent map on both sides (`srcRefines` and `tgtRefines` along one
  `par n`). `IsPartialTransferOf` delivers exactly that — its `refines_src` and `refines_tgt`
  share `par` — which is `lem:refinement-compatibility`(c).
* `LimitTower` wants the two cell decompositions against *closed* domains `C ∪ D` and `Q`, and
  `GeneratedPair` is parametrized by exactly those two sets.

## The four facts about the concrete domains

`LimitTower` asks for the source domain to be closed and bounded and its interior open, and the
same for the target. On the source side `IsSeparating C` gives all three:
`Schoenflies.isClosed_union_inside`, `Schoenflies.union_inside_sdiff` with
`IsSeparating.isOpen_inside`, and boundedness through `C = frontier (inside C) ⊆ closure (inside C)`
— which is why `isBounded_dom` needs no extra hypothesis, though `LimitMap.lean` warns that it is
not optional (`Metric.diam` is `0` on an unbounded set). On the target side they are the standard
facts about the square.

## Blueprint

* `Schoenflies.StageSequence` — the output of the recursion of the section *Quantitative
  refinement*: the stage-`n` matched cellulations `(Γ_n, Γ'_n)` with their parent maps and the
  two convergence statements of `prop:shrinking-stars`.
* `Schoenflies.StageSequence.limitTower` — the passage to the head of the section *The limit
  homeomorphism of the interiors*, i.e. to `tex 2568`'s "we now forget how the decompositions
  were constructed".
* `Schoenflies.StageSequence.isHomeoOn_F`, `.interior_homeomorphism` —
  **`prop:interior-homeomorphism`** for a stage sequence, which is the third conjunct of
  `Schoenflies.HasLimitHomeomorphism`.
-/

open Bornology Filter Metric Set Topology
open scoped Graph

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

/-! ### The concrete domains

`LimitTower` is stated for arbitrary closed domains; the construction uses two. These are the
facts it asks about them, collected so that `limitTower` below reads as a repackaging. -/

/-- The closed Jordan domain is bounded. `IsSeparating` does not say so directly — it says the
*inside* is bounded — but `C` is the frontier of the inside, hence inside its closure. -/
theorem isBounded_union_inside (hC : IsSeparating C) : IsBounded (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact hC.isBounded_inside.closure

/-- The interior of the closed Jordan domain is open — after the rewriting `LimitTower` needs,
which asks for `IsOpen (dom \ bdry)` rather than `IsOpen (inside C)`. -/
theorem isOpen_union_inside_sdiff (hC : IsSeparating C) : IsOpen ((C ∪ inside C) \ C) := by
  rw [union_inside_sdiff]; exact hC.isOpen_inside

/-- The interior of the closed square is open, in the same shape. -/
theorem isOpen_closedSquare_sdiff_modelCurve :
    IsOpen (Plane.closedSquare 0 1 \ modelCurve) := by
  rw [closedSquare_sdiff_modelCurve]; exact Plane.isOpen_openSquare 0 1

/-! ### A sequence of transferred stages -/

/-- **The output of the recursion of *Quantitative refinement*.**

A sequence of generated matched cellulations of the closed Jordan domain and the closed square,
each refining its predecessor along one parent map shared by the two sides, with growing source
skeletons, nested skeleton maps, and the two convergence statements of `prop:shrinking-stars`.

Every field beyond `stage` and `base` is something the recursion establishes at the step that
produces it; none is a property of a single stage, which is why they cannot live in
`GeneratedPair`. -/
structure StageSequence (γ : Type*) [Nonempty γ] (S₀ : CellStructure γ) (C : Set Plane) where
  /-- The stage-`n` matched cellulation `(Γ_n, Γ'_n)`, with both realizations. -/
  stage : ℕ → GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)
  /-- The parent map from stage `n + 1` to stage `n`, shared by the two sides. -/
  par : ℕ → γ → γ
  /-- Both compatible refinements, source-skeleton growth, and nesting of the skeleton maps. -/
  transition : ∀ n, StageTransition (stage (n + 1)) (stage n) (par n)
  /-- The uniform target mesh, `2 ε_n` of the blueprint. -/
  eps : ℕ → ℝ
  /-- **`prop:shrinking-stars`, the uniform half.** -/
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (stage n).str.cells → diam ((stage n).tgt.star σ) ≤ eps n
  /-- …and the mesh tends to zero. -/
  tendsto_eps : Tendsto eps atTop (nhds 0)
  /-- **`prop:shrinking-stars`, the pointwise half.** -/
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ inside C →
    Tendsto (fun n => diam ((stage n).src.star ((stage n).src.carrier x))) atTop (nhds 0)
  /-- The combinatorial invariants hold at the base of `def:generated-structure`; every stage
  inherits them by `GeneratedPair.combInvariants`. -/
  base : S₀.CombInvariants
  /-- `C` separates the plane — `thm:jordan`, which the caller has. -/
  isSeparating : IsSeparating C

namespace StageSequence

variable (T : StageSequence γ S₀ C)

/-- Consecutive source realizations refine along the recorded parent map. -/
theorem refines_src (n : ℕ) :
    (T.stage (n + 1)).src.Refines (T.stage n).src (T.par n) :=
  (T.transition n).refines_src

/-- The target realizations refine along the same parent map. -/
theorem refines_tgt (n : ℕ) :
    (T.stage (n + 1)).tgt.Refines (T.stage n).tgt (T.par n) :=
  (T.transition n).refines_tgt

/-- The realized source skeletons grow from one stage to the next. -/
theorem skeletonSet_mono (n : ℕ) :
    (T.stage n).src.skeletonSet ⊆ (T.stage (n + 1)).src.skeletonSet :=
  (T.transition n).sourceSkeletonSet_subset

/-- Consecutive skeleton homeomorphisms agree on the preceding source skeleton. -/
theorem skelHomeo_succ (n : ℕ) :
    Set.EqOn (T.stage (n + 1)).homeo.toFun (T.stage n).homeo.toFun
      (T.stage n).src.skeletonSet :=
  (T.transition n).homeo_eqOn

/-- **The tower the limit section consumes.** Every field is read off the stages or is one of
the four facts about the two concrete domains; there is no mathematics here beyond the two
recorded above. -/
def limitTower : CellStructure.LimitTower γ where
  str n := (T.stage n).str
  src n := (T.stage n).src
  tgt n := (T.stage n).tgt
  skelHomeo n := (T.stage n).homeo
  par := T.par
  dom := C ∪ inside C
  bdry := C
  dom' := Plane.closedSquare 0 1
  bdry' := modelCurve
  eps := T.eps
  srcDecomp n := (T.stage n).src_isCellDecomposition
  tgtDecomp n := (T.stage n).tgt_isCellDecomposition
  comb n := (T.stage n).combInvariants T.base
  srcRefines := T.refines_src
  tgtRefines := T.refines_tgt
  srcOuterSet n := (T.stage n).src_isWeaklyAdmissible.outerSet_eq
  tgtOuterSet n := (T.stage n).tgt_isWeaklyAdmissible.outerSet_eq
  isClosed_dom := isClosed_union_inside T.isSeparating
  isClosed_dom' := Plane.isClosed_closedSquare 0 1
  isBounded_dom := isBounded_union_inside T.isSeparating
  isBounded_dom' := Plane.isBounded_closedSquare 0 1
  isOpen_int := isOpen_union_inside_sdiff T.isSeparating
  isOpen_int' := isOpen_closedSquare_sdiff_modelCurve
  skeletonSet_mono := T.skeletonSet_mono
  skelHomeo_succ := T.skelHomeo_succ
  diam_tgtStar_le := T.diam_tgtStar_le
  tendsto_eps := T.tendsto_eps
  tendsto_diam_srcStar := by
    intro x hx
    exact T.tendsto_diam_srcStar (by rwa [union_inside_sdiff] at hx)

@[simp] theorem limitTower_region : T.limitTower.region = inside C := union_inside_sdiff C

@[simp] theorem limitTower_region' : T.limitTower.region' = Plane.openSquare 0 1 :=
  closedSquare_sdiff_modelCurve

end StageSequence

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeForwardStages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Quantitative forward local-grid stages

The local-grid attachment supplies a complete raw grid in the source skeleton.
This module turns that containment into the pointwise source-star estimate used by
`prop:shrinking-stars`, and records that the target face mesh from the preceding reverse stage
survives the forward refinement.
-/

open Metric Set

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

namespace LocalGridForwardStageData

variable {p : Plane} {s epsilon : ℝ}
  (w : LocalGridForwardStageData P p s epsilon)

omit [Nonempty γ] in
/-- A target face-mesh estimate survives the forward local-grid stage. -/
theorem targetFaceMesh {bound : ℝ} (hmesh : TargetFaceMesh P bound) :
    TargetFaceMesh w.pair bound :=
  hmesh.refine w.transition.refines_tgt

end LocalGridForwardStageData

omit [Nonempty γ] in
/-- The window used by quantitative refinement automatically satisfies every geometric
hypothesis of the local-grid forward constructor. -/
theorem GeneratedPair.exists_localGridForwardStageData_window [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon meshEpsilon : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (_hmeshEpsilon : 0 < meshEpsilon)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridForwardStageData P p
      (windowRadius C windowEpsilon p) meshEpsilon) := by
  have hpC : p ∉ C := fun hpC => inside_subset_compl hp hpC
  have hs : 0 < windowRadius C windowEpsilon p :=
    windowRadius_pos hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hpC
  have hwindow : window C windowEpsilon p ⊆ (C ∪ inside C) \ C := by
    intro x hx
    have hxInside := window_subset_inside hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hC hp hwindowEpsilon hx
    exact ⟨Or.inr hxInside, inside_subset_compl hxInside⟩
  exact P.exists_localGridForwardStageData hC hs hwindow hsource

/-- One quantitative forward successor: the local-grid refinement together with
the target face-mesh estimate inherited from the preceding reverse stage. -/
structure QuantitativeForwardStage
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (p : Plane) (windowEpsilon meshEpsilon targetBound : ℝ) where
  forward : LocalGridForwardStageData P p
    (windowRadius C windowEpsilon p) meshEpsilon
  targetFaceMesh : TargetFaceMesh forward.pair targetBound

namespace QuantitativeForwardStage

variable {p : Plane} {windowEpsilon meshEpsilon targetBound : ℝ}
  (w : QuantitativeForwardStage P p windowEpsilon meshEpsilon targetBound)

/-- The generated pair at the forward successor. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.forward.pair

end QuantitativeForwardStage

omit [Nonempty γ] in
/-- Construct a quantitative forward successor from any target face-mesh estimate on the
preceding stage. -/
theorem GeneratedPair.exists_quantitativeForwardStage [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon meshEpsilon targetBound : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (hmeshEpsilon : 0 < meshEpsilon)
    (hsource : IsConnected P.src.nonboundary)
    (hmesh : TargetFaceMesh P targetBound) :
    Nonempty (QuantitativeForwardStage P p windowEpsilon meshEpsilon targetBound) := by
  obtain ⟨w⟩ := P.exists_localGridForwardStageData_window hC hp
    hwindowEpsilon hmeshEpsilon hsource
  exact ⟨{ forward := w, targetFaceMesh := w.targetFaceMesh hmesh }⟩

/-- One complete quantitative successor consists of the uniform reverse target refinement and
the pointwise forward source-grid refinement. -/
structure QuantitativeSuccessor
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (anchors : List Plane) (p : Plane)
    (windowEpsilon sourceBound targetBound : ℝ) where
  reverse : QuantitativeReverseStage P anchors targetBound
  forward : QuantitativeForwardStage reverse.pair p windowEpsilon sourceBound
    reverse.overlay.delta

namespace QuantitativeSuccessor

variable {anchors : List Plane} {p : Plane}
  {windowEpsilon sourceBound targetBound : ℝ}
  (w : QuantitativeSuccessor P anchors p windowEpsilon sourceBound targetBound)

/-- The generated pair at the end of the two half-steps. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.forward.pair

end QuantitativeSuccessor

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeRecursion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The recursive quantitative stage construction

This module iterates the two-sided quantitative successor. Window centres are
read from a recurrent sequence and all three quantitative parameters use a dyadic scale.
-/

open Filter Metric Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- The external choices needed by the quantitative recursion.  `centreBase` will be wrapped
by `recur`, so every one of its values occurs at arbitrarily late stages. -/
structure QuantitativeSchedule (C : Set Plane) where
  centreBase : ℕ → Plane
  centreBase_mem : ∀ n, centreBase n ∈ inside C
  anchors : ℕ → List Plane

namespace QuantitativeSchedule

variable (q : QuantitativeSchedule C)

/-- The recurrent centre used at stage `n`. -/
def centre (n : ℕ) : Plane := recur q.centreBase n

end QuantitativeSchedule

end Schoenflies
end



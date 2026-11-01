-- Prove2me | Definitions.Def_Q146C007
-- name    : Q146C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:16:04.716135+00:00
-- url     : https://prove2.me/theorems/cc3151c5-517e-4d76-919d-70b157dbccda
-- title:
--   Definitions bundle Q146C007 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 759 declarations of OpenAI's Lean: 172 definitions, 32 inductive types or structures, 4 instances and 551 theorems. The definitions and types are `Graph.IsStageOn`, `Graph.Nonboundary`, `Graph.attachEdges`, `Graph.interiorPart`, `OAI.CircleDomainRigidity.AppendingConstructionState.chooseStep`, `OAI.CircleDomainRigidity.AppendingConstructionState.next`, `OAI.CircleDomainRigidity.AppendingSequence.index`, `OAI.CircleDomainRigidity.AppendingSequence.savedTolerance`, `OAI.CircleDomainRigidity.AppendingSequence.scalar`, `OAI.CircleDomainRigidity.AppendingSequence.sphereScalar`, `OAI.CircleDomainRigidity.AppendingSequence.tailIndex`, `OAI.CircleDomainRigidity.AppendingSequence.tailScalar`, `OAI.CircleDomainRigidity.AppendingSequence.tailWitness`, `OAI.CircleDomainRigidity.AppendingSequence.witness`, `OAI.CircleDomainRigidity.CompactRecursiveReduction.baseHitWeight`, `OAI.CircleDomainRigidity.CompatibleLevelBarrier`, `OAI.CircleDomainRigidity.CompatibleLevelBarrier.controlledSize`, `OAI.CircleDomainRigidity.CompatibleLevelBarrier.rebase`, `OAI.CircleDomainRigidity.CoordinateExclusionTest`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.neighborhood`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.presentation`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.reanchor`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.withLevels`, `OAI.CircleDomainRigidity.DiskAvoidingPath`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates.NaturalCompatibility`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates.maskedCoordinate`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates.realSubfamily`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.boundRadius`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.closedGate`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.openGate`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.selectionRadius`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.selectionThreshold`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData.restrictMarks`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateStage.sourceMask`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateStage.targetMask`, `OAI.CircleDomainRigidity.FiniteTransfer.MixedCoordinateStage.realStage`, `OAI.CircleDomainRigidity.FiniteTransfer.MixedModelExhaustion.coordinateIndex`, `OAI.CircleDomainRigidity.FiniteTransfer.MixedModelExhaustion.withRadius`, `OAI.CircleDomainRigidity.FiniteTransfer.RealCoordinateSubfamily` and 164 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundaryAnchors`, `BoundaryContinuity`, `BoundaryContinuity2`, `BoundaryCycles`, `BoundaryCyclesGenerated`, `CellulationInvariants`, `CircleDomains_Modulus_CompatibleLevelBarrier`, `CircleDomains_Modulus_HitNormTopology`, `CircleDomains_Modulus_LevelBarrierRebase`, `CircleDomains_Modulus_MarkedConfigurationNorm`, `CircleDomains_Modulus_RealBarrierProjection`, `CircleDomains_Modulus_RealBarrierTests`, `CircleDomains_Modulus_StableBarrierContours`, `CircleDomains_Probability_MarkedFusionKernel`, `CircleDomains_Probability_MarkedFusionSmallSets`, `CircleDomains_Probability_MarkedHitFusion`, `CircleDomains_Probability_MarkedHitFusionCaps`, `CircleDomains_Probability_MarkedHitFusionLaw`, `CircleDomains_Probability_MarkedHitFusionTree`, `CircleDomains_Probability_MarkedHitLaws`, `CircleDomains_Probability_PathHitLaws`, `CircleDomains_Probability_PathLawMixtures`, `CircleDomains_Probability_RecursiveCodeLaw`, `CircleDomains_Rigidity_CountableMatchedComponents`, `CircleDomains_Rigidity_MaskedStageEnergy`, `CircleDomains_Rigidity_MaskedStokesGeometry`, `CircleDomains_Rigidity_MatchedCommonPoints`, `CircleDomains_Rigidity_MatchedConformalEnds`, `CircleDomains_Rigidity_MatchedRealMaskData`, `CircleDomains_Rigidity_MatchedRoundDisks`, `CircleDomains_Rigidity_MatchedScalarIntervals`, `CircleDomains_Rigidity_MatchedSourceProjection`, `CircleDomains_Rigidity_SelectableMaskedCoordinate`, `CircleDomains_Selection_CoordinateExclusionTest`, `CircleDomains_Selection_GeometricIndexLocal`, `CircleDomains_Selection_GeometricRayIndex`, `CircleDomains_Selection_GradedRealSelection`, `CircleDomains_Selection_JumpBlockCodes`, `CircleDomains_Selection_MarkedAtomicHitTests`, `CircleDomains_Selection_MarkedConfigurations`, `CircleDomains_Selection_MarkedFiniteHitSplit`, `CircleDomains_Selection_MeanExclusionCongruence`, `CircleDomains_Selection_MeanExclusionRadius`, `CircleDomains_Selection_MeanExclusionWitness`, `CircleDomains_Selection_MeanGeometricIndex`, `CircleDomains_Selection_MixedCoordinateStage`, `CircleDomains_Selection_MixedSequenceRetention`, `CircleDomains_Selection_PointDustContourSelection`, `CircleDomains_Selection_ProtrusionGateGeometry`, `CircleDomains_Selection_ProtrusionTestGeometry`, `CircleDomains_Selection_RealAnchorRetention`, `CircleDomains_Selection_RealCoordinateData`, `CircleDomains_Selection_RealCoordinateSubfamily`, `CircleDomains_Selection_RealExclusionWitness`, `CircleDomains_Selection_RealSequenceRetention`, `CircleDomains_Selection_RealStageBands`, `CircleDomains_Selection_RealStageEstimates`, `CircleDomains_Selection_ReanchoredExclusions`, `CircleDomains_Selection_ReanchoredSelection`, `CircleDomains_Selection_RebasedLevelPresentations`, `CircleDomains_Selection_RecursiveReductionBase`, `CircleDomains_Selection_RecursiveTestConstruction`, `CircleDomains_Selection_RecursiveTestHistory`, `CircleDomains_Selection_RelevelledExclusions`, `CircleDomains_Selection_RelevelledSelection`, `CircleDomains_Selection_RestrictedCoordinateMarks`, `CircleDomains_Selection_RestrictedMeanExclusion`, `CircleDomains_Selection_SavedAppendingContours`, `CircleDomains_Selection_ScalarEndCaps`, `CircleDomains_Selection_SeededGradedRealSelection`, `CircleDomains_Selection_SelectedLevelPresentation`, `CircleDomains_Selection_SizedMeanExclusion`, `CircleDomains_Selection_SlackRealExclusion`, `CircleDomains_Selection_TrackedTailSequence`, `CircleDomains_Selection_TrackedTestSequence`, `CircleDomains_Selection_VerticalRayAvoidance`, `CircleDomains_Selection_ZeroRealCoordinate`, `CircleDomains_Sobolev_MarkedConfigurationIntegral`, `CircleDomains_Sobolev_ModelRealEnergy`, `CircleDomains_Sobolev_SmoothMeanPeriodData`, `CircleDomains_Sobolev_SmoothRealSphereMaps`, `CircleDomains_Sobolev_SmoothSphereEquivalence`, `CircleDomains_Sobolev_SphereRealDifferential`, `CircleDomains_Topology_AnchoredJordanLimits`, `CircleDomains_Topology_ClosedComponentCorrespondence`, `CircleDomains_Topology_CompactImageRetention`, `CircleDomains_Topology_CompactifiedDiskRay`, `CircleDomains_Topology_ComponentRelationSelection`, `CircleDomains_Topology_ConformalSphericalMetric`, `CircleDomains_Topology_CrosscutPathSides`, `CircleDomains_Topology_DiskRayCrosscut`, `CircleDomains_Topology_DiskRayLift`, `CircleDomains_Topology_DiskRayProper`, `CircleDomains_Topology_HalfPlanePathSides`, `CircleDomains_Topology_HalfPlaneRay`, `CircleDomains_Topology_MapDiskExclusion`, `CircleDomains_Topology_MarkedClosedHitSplit`, `CircleDomains_Topology_MeanIndexCircle`, `CircleDomains_Topology_PlaneComponentRelation`, `CircleDomains_Topology_RayJordanSides`, `CircleDomains_Topology_RealModelExhaustion`, `CircleDomains_Topology_RegularJordanCollar`, `CircleDomains_Topology_SavedSeparatingFamily`, `CircleDomains_Topology_TwoEndedCollarSplicing`, `CircleDomains_Transfer_CompletedChart`, `CircleDomains_Transfer_ContinuousSourceProjection`, `CircleDomains_Transfer_CountableRealTransfer`, `CircleDomains_Transfer_EnlargedRealModels`, `CircleDomains_Transfer_FilledCoordinates`, `CircleDomains_Transfer_GridCoordinateFilling`, `CircleDomains_Transfer_PointDustModels`, `CircleDomains_Transfer_RealTargetEnds`, `CircleDomains_Transfer_RetainedScalarEstimates`, `CircleDomains_Transfer_RoundOuterCore`, `CircleDomains_Transfer_SmallImageDustContours`, `CircleDomains_Transfer_SourceEndProjection`, `CircleDomains_Uniformization_ActualInverseConvergence`, `CircleDomains_Uniformization_FiniteModelCoordinates`, `CircleDomains_Uniformization_LocalInverseConvergence`, `CircleDomains_Uniformization_TrackedTestLimits`, `CombinatorialInvariance`, `CommonSubdivision`, `Endgame`, `FiniteTransfer`, `GeneratedStructure`, `Graph_PathGraph`, `Graph_Relabel`, `Graph_TwoConnected`, `GridAttach`, `InitialGenerated`, `InitialOuterCycle`, `InitialPair`, `InitialPairFixed`, `Inversion`, `LimitMap`, `LocalGrid`, `MatchedArc`, `MatchedSplit`, `ModelCurve`, `OverlayGraph`, `RealizeSubdiv`, `RefinementStars`, `SkeletonAccess`, `SkeletonLocal`, `SquareMesh`, `SquareMeshConnected`, `SquareMeshFixed`, `SquareMover`, `Windows`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C003`, `Q146C004` and `Q146C005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C009` and `Q146C010`; the statements `OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit`, `OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages`, `OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels`, `OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget` and `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier`; the proofs of `OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential`, `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier` and `OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C003
import Definitions.Def_Q146C004
import Definitions.Def_Q146C005

section
-- module Solutions.Q146_CD.OverlayGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
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

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

instance overlayGraph_finite (pieces : List Piece) (points : List Plane) :
    Graph.Finite (overlayGraph pieces points) where
  finite_vertexSet := finite_endSet _
  finite_edgeSet := (overlayPieces pieces points).finite_toSet

end Schoenflies
end

section
-- module Solutions.Q146_CD.ModelCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses _root_.Schoenflies.overlayGraph_finite
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The model curve, and the parametrization of a Jordan curve by it

The blueprint's model curve is `S = ∂Q`, the boundary of the square `Q = [-1,1]²`, and *not*
the unit circle. That is a deliberate choice: this development is trigonometry-free, so a
traversal of the round circle by an interval is unavailable, whereas `S` is four segments
glued end to end and each segment is an arc by `isArcBetween_segment`. The blueprint says so
explicitly ("Nothing in this document needs the unit circle in place of `S`").

`modelCurve` is defined by the sup norm, `‖x‖∞ = 1`, which is the same square the rest of the
development already speaks about (`Plane.closedSquare 0 1`), and it is cut into its four sides
by `modelCurve_eq_sides`.

## The content of Lemma 3.1

The lemma has three clauses. Only the first is proved here; the other two are already on
`main`, transported along the homeomorphism the first clause supplies:

* *"`γ` induces a homeomorphism from `S` onto `C`"* — `isJordanCurve_modelCurve` together with
  `IsJordanCurve.homeomorph_modelCurve`. The general fact behind it is `IsLoop.exists_homeomorph`:
  a loop is a quotient map of `[0,1]` which identifies exactly `0` with `1`, so *any two* loops
  induce a homeomorphism between their images, matching parameter for parameter.
* *"two distinct points divide `C` into two simple arcs meeting exactly in those points"* — this
  is `IsJordanCurve.two_arcs` in `Schoenflies/TwoArcs.lean`, proved directly on the parameter
  interval, which is strictly stronger than transporting it from `S`.
* *"the relatively open subarcs form a basis of the subspace topology"* — `openArc_isRelOpen`,
  `openArc_subarc_isRelOpen` and `basic_piece_inside_ball` in `Schoenflies/Subarc.lean`.

The route to the homeomorphism is the blueprint's, with the sequence argument replaced by its
point-set content: `t ↦ γ t` is a continuous surjection from the compact `[0,1]` onto the
Hausdorff `C`, hence a closed map, hence a *quotient* map; so a map out of `C` is continuous as
soon as its composite with the parametrization is. That is exactly what the blueprint's
subsequence chase establishes, and it is one line here.

## Blueprint

* `modelCurve` — Lemma 3.1, the model curve `S = ∂Q` with `Q = [-1,1]²`.
* `modelCurve_eq_sides` — the decomposition of `S` into its four sides.
* `modelCurve_eq_frontier` — `S` is literally the topological boundary of `Q`.
* `isJordanCurve_modelCurve` — `S` is a Jordan curve.
* `IsLoop.param_eq_or`, `IsLoop.eq_of_eq` — a loop identifies exactly the two endpoints of the
  parameter interval.
* `IsLoop.exists_homeomorph` — two loops induce a homeomorphism of their images.
* `IsJordanCurve.homeomorph`, `IsJordanCurve.homeomorph_modelCurve`,
  `IsJordanCurve.modelCurve_homeomorph` — Lemma 3.1, first clause.
-/

open Set Topology unitInterval

namespace Schoenflies

/-! ### Segments with a constant coordinate

The four sides of the square are axis-parallel, so each is pinned by one coordinate and swept
by the other. Two lemmas serve all four. -/

/-! ### The model curve and its four sides -/

theorem mem_sideTop {x : Plane} : x ∈ sideTop ↔ x 1 = 1 ∧ |x 0| ≤ 1 := by
  rw [sideTop, cornerNE, cornerNW, mem_segment_horiz, segment_one_neg_one]
  simp [abs_le, and_comm]

theorem mem_sideLeft {x : Plane} : x ∈ sideLeft ↔ x 0 = -1 ∧ |x 1| ≤ 1 := by
  rw [sideLeft, cornerNW, cornerSW, mem_segment_vert, segment_one_neg_one]
  simp [abs_le]

theorem mem_sideBottom {x : Plane} : x ∈ sideBottom ↔ x 1 = -1 ∧ |x 0| ≤ 1 := by
  rw [sideBottom, cornerSW, cornerSE, mem_segment_horiz, segment_neg_one_one]
  simp [abs_le]

theorem mem_sideRight {x : Plane} : x ∈ sideRight ↔ x 0 = 1 ∧ |x 1| ≤ 1 := by
  rw [sideRight, cornerSE, cornerNE, mem_segment_vert, segment_neg_one_one]
  simp [abs_le]

/-- The model curve is the union of the four sides. The sup norm reaches `1` exactly when one
coordinate is `±1` and the other is dominated by it. -/
theorem modelCurve_eq_sides :
    modelCurve = (sideTop ∪ sideLeft) ∪ (sideBottom ∪ sideRight) := by
  ext x
  simp only [modelCurve, mem_setOf_eq, mem_union, mem_sideTop, mem_sideLeft, mem_sideBottom,
    mem_sideRight, Plane.supNorm]
  constructor
  · intro h
    have h0 : |x 0| ≤ 1 := h ▸ le_max_left _ _
    have h1 : |x 1| ≤ 1 := h ▸ le_max_right _ _
    rcases max_choice |x 0| |x 1| with hm | hm
    · -- the first coordinate attains the maximum, so it is `±1`
      have hx : |x 0| = 1 := hm ▸ h
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with h' | h'
      · exact Or.inr (Or.inr ⟨h', h1⟩)
      · exact Or.inl (Or.inr ⟨h', h1⟩)
    · have hx : |x 1| = 1 := hm ▸ h
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with h' | h'
      · exact Or.inl (Or.inl ⟨h', h0⟩)
      · exact Or.inr (Or.inl ⟨h', h0⟩)
  · rintro ((⟨h1, h0⟩ | ⟨h0, h1⟩) | (⟨h1, h0⟩ | ⟨h0, h1⟩))
    · rw [show |x 1| = 1 by rw [h1]; norm_num]
      exact max_eq_right h0
    · rw [show |x 0| = 1 by rw [h0]; norm_num]
      exact max_eq_left h1
    · rw [show |x 1| = 1 by rw [h1]; norm_num]
      exact max_eq_right h0
    · rw [show |x 0| = 1 by rw [h0]; norm_num]
      exact max_eq_left h1

/-! ### The model curve is a Jordan curve -/

/-- Consecutive sides meet only in the corner they share. -/
theorem sideTop_meet_sideLeft : ∀ z ∈ sideTop, z ∈ sideLeft → z = cornerNW := by
  intro z hz hz'
  rw [mem_sideTop] at hz
  rw [mem_sideLeft] at hz'
  ext i
  fin_cases i
  · simpa [cornerNW] using hz'.1
  · simpa [cornerNW] using hz.1

theorem sideBottom_meet_sideRight : ∀ z ∈ sideBottom, z ∈ sideRight → z = cornerSE := by
  intro z hz hz'
  rw [mem_sideBottom] at hz
  rw [mem_sideRight] at hz'
  ext i
  fin_cases i
  · simpa [cornerSE] using hz'.1
  · simpa [cornerSE] using hz.1

/-- The upper half of the model curve: two sides from `(1,1)` to `(-1,-1)`. -/
theorem isArcBetween_upperSides : IsArcBetween (sideTop ∪ sideLeft) cornerNE cornerSW :=
  isArcBetween_sideTop.concatenate isArcBetween_sideLeft sideTop_meet_sideLeft

/-- The lower half of the model curve: two sides back from `(-1,-1)` to `(1,1)`. -/
theorem isArcBetween_lowerSides : IsArcBetween (sideBottom ∪ sideRight) cornerSW cornerNE :=
  isArcBetween_sideBottom.concatenate isArcBetween_sideRight sideBottom_meet_sideRight

/-- The two halves of the model curve meet exactly in the two corners they share: opposite
sides are pinned to opposite values of one coordinate, so they are disjoint. -/
theorem upperSides_meet_lowerSides :
    ∀ z ∈ sideTop ∪ sideLeft, z ∈ sideBottom ∪ sideRight → z = cornerNE ∨ z = cornerSW := by
  rintro z (hz | hz) (hz' | hz')
  · -- top and bottom: `z 1 = 1` and `z 1 = -1`
    rw [mem_sideTop] at hz
    rw [mem_sideBottom] at hz'
    rw [hz.1] at hz'
    norm_num at hz'
  · -- top and right: the corner `(1,1)`
    rw [mem_sideTop] at hz
    rw [mem_sideRight] at hz'
    refine Or.inl ?_
    ext i
    fin_cases i
    · simpa [cornerNE] using hz'.1
    · simpa [cornerNE] using hz.1
  · -- left and bottom: the corner `(-1,-1)`
    rw [mem_sideLeft] at hz
    rw [mem_sideBottom] at hz'
    refine Or.inr ?_
    ext i
    fin_cases i
    · simpa [cornerSW] using hz.1
    · simpa [cornerSW] using hz'.1
  · -- left and right: `z 0 = -1` and `z 0 = 1`
    rw [mem_sideLeft] at hz
    rw [mem_sideRight] at hz'
    rw [hz.1] at hz'
    norm_num at hz'

/-- **The model curve is a Jordan curve.** Four segments glued end to end; no trigonometry
anywhere. -/
theorem isJordanCurve_modelCurve : IsJordanCurve modelCurve := by
  rw [modelCurve_eq_sides]
  exact IsJordanCurve.of_two_arcs isArcBetween_upperSides isArcBetween_lowerSides
    upperSides_meet_lowerSides

theorem isCompact_modelCurve : IsCompact modelCurve :=
  isJordanCurve_modelCurve.isCompact

/-! ### The model curve is the boundary of the square

This is the blueprint's description `S = ∂Q` with `Q = [-1,1]²`, and the check that the sup-norm
definition above is the intended one. The only content is that a point of sup norm exactly `1`
is *not* interior to the square: scaling it out by a factor `1 + δ` leaves the square while
moving an arbitrarily small distance. -/

theorem mem_openSquare_zero_one {x : Plane} :
    x ∈ Plane.openSquare 0 1 ↔ Plane.supNorm x < 1 := by
  simp [Plane.openSquare]

theorem interior_closedSquare_zero_one :
    interior (Plane.closedSquare 0 1) = Plane.openSquare 0 1 := by
  refine subset_antisymm (fun x hx => ?_) ?_
  · rw [mem_openSquare_zero_one]
    rcases lt_or_eq_of_le (mem_closedSquare_zero_one.mp (interior_subset hx)) with h | h
    · exact h
    · exact absurd hx (notMem_interior_closedSquare h)
  · exact (Plane.isOpen_openSquare 0 1).subset_interior_iff.mpr fun x hx =>
      mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le

/-- **The model curve is `∂Q`**, the topological boundary of the closed square `Q = [-1,1]²`. -/
theorem modelCurve_eq_frontier : modelCurve = frontier (Plane.closedSquare 0 1) := by
  rw [(Plane.isClosed_closedSquare 0 1).frontier_eq, interior_closedSquare_zero_one]
  ext x
  simp only [modelCurve, mem_setOf_eq, mem_sdiff, mem_closedSquare_zero_one,
    mem_openSquare_zero_one, not_lt]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/-! ### A loop identifies exactly the ends of the parameter interval -/

/-! ### Lemma 3.1: parametrization by the model curve -/

namespace IsJordanCurve

/-- **Lemma 3.1.** A Jordan curve is homeomorphic to the model curve `S = ∂Q`. -/
theorem homeomorph_modelCurve {C : Set Plane} (hC : IsJordanCurve C) :
    Nonempty (↥C ≃ₜ ↥modelCurve) :=
  hC.homeomorph isJordanCurve_modelCurve

end IsJordanCurve

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses _root_.Schoenflies.overlayGraph_finite
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

/-! ### Shearing the square along one coordinate -/

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

/-! ### Movers of the square -/

namespace IsSquareMover

variable {M N M' N' : Plane → Plane}

/-- Movers compose: `M'` after `M`, undone by `N` after `N'`. -/
theorem comp (h : IsSquareMover c r M N) (h' : IsSquareMover c r M' N') :
    IsSquareMover c r (M' ∘ M) (N ∘ N') where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := by
    constructor
    · intro z hz
      simp only [Function.comp_apply]
      rw [h'.invOn.1 (h.mapsTo hz), h.invOn.1 hz]
    · intro z hz
      simp only [Function.comp_apply]
      rw [h.invOn.2 (h'.mapsTo_inv hz), h'.invOn.2 hz]
  fixes := fun z hz hbd => by
    simp only [Function.comp_apply, h.fixes z hz hbd, h'.fixes z hz hbd]
  fixes_inv := fun z hz hbd => by
    simp only [Function.comp_apply, h'.fixes_inv z hz hbd, h.fixes_inv z hz hbd]

end IsSquareMover

/-! ### Moving an interior point -/

/-! ### The boundary of the square -/

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
-- module Solutions.Q146_CD.Inversion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Inversion in the unit circle, and the density of strongly accessible points

Two consequences of the Jordan curve theorem which have nothing to do with one another beyond
becoming available at the same moment.

## Inversion exchanges the two sides

Inversion about the unit circle centred at `a`,

    I_a(x) = a + (x - a) / ‖x - a‖²,

is the device that turns the *bounded* Schönflies theorem into the unbounded one: it swaps the
two sides of a Jordan curve `C` around any interior point `a`, sending the exterior of `C` onto
the interior of `C^a = I_a(C)` punctured at `a`. So a closed-interior extension for `C^a`,
pushed back through `I_a`, is a closed-*exterior* extension for `C`, which is
`prop:exterior-extension` and the second half of `thm:main`.

The map is Mathlib's `EuclideanGeometry.inversion a 1`, repackaged here as `Schoenflies.invert`
with the three facts the geometry needs: `Schoenflies.dist_invert_center`
(`‖I_a(x) - a‖ = 1/‖x - a‖`), `Schoenflies.invert_involutive`, and continuity away from `a`.
`Schoenflies.invertHomeo` bundles it as a self-homeomorphism of the punctured plane, which is
the form the conjugation `I_b ∘ f ∘ I_a` of `prop:exterior-extension` will want.

The proof of `lem:inversion-sides` is the blueprint's. Put `U = I_a(Ext C) ∪ {a}`. It is

* *open*: away from `a` because `I_a` is a homeomorphism of the punctured plane, and at `a`
  because `C ∪ Int(C)` is bounded, so the complement of a large closed ball `B̄(a, R)` lies in
  `Ext(C)` and inverts onto `B(a, 1/R) ∖ {a}`;
* *bounded*: a ball `B(a, δ)` lies in `Int(C)`, so exterior points stay at distance `≥ δ` from
  `a` and their inverses at distance `≤ 1/δ`;
* *connected*: the continuous image of `Ext(C)`, together with `a`, which is a limit of it
  because `Ext(C)` is unbounded;
* *bounded by `C^a`*: the third region `I_a(Int(C) ∖ {a})` is open, so the frontier of `U` can
  only be `C^a`, and every point of `C^a` is in it because `C = ∂Ext(C)`.

Being open, connected and with frontier disjoint from `(C^a)ᶜ`, `U` is a component of `(C^a)ᶜ`
(`Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`); being bounded, it is
`Int(C^a)`.

## The closed-exterior extension

`prop:exterior-extension` is the short assembly that sits on top of it, stated parametrically
over `prop:pointed-extension`. `Schoenflies.PointedInteriorExtension` is that interface, written
out: the bounded theorem with a prescribed interior point. `Schoenflies/Endgame.lean` derives
it from the closed-interior extension together with `lem:square-point-mover`, and
`Schoenflies/JordanSchoenflies.lean` supplies the square-extension input.

The assembly needs a name for "restricts to a homeomorphism onto", since it composes four of
them; `Schoenflies.IsHomeoOn` is that, in the unbundled `Schoenflies.Plane.IsSquareMover`
style.

## Density of strongly accessible points

`lem:tangent-dense` is three lines on top of `thm:jordan` and `lem:nearest-strong`: a point of
`C` is a limit of points of the region because `C` is the region's frontier, and the nearest
point of `C` to such a point is strongly accessible and no further from `p` than twice the
distance we started with. It is stated here for either region, since nothing in the argument
distinguishes them.

Everything below inherits the standing hypothesis of `thm:jordan` on `main`,

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

threaded verbatim through every statement that consumes
`Schoenflies.IsJordanCurve.isSeparating`. The two density statements, which are about an
abstract `IsSeparating` curve, do not need it.

## Blueprint

* `Schoenflies.invert` and its algebra — the map `I_a` of §"The closed exteriors".
* `Schoenflies.invertHomeo` — "`I_a` is an involutive homeomorphism of `ℝ² ∖ {a}`".
* `Schoenflies.IsJordanCurve.invert_image` — "`C^a` is a Jordan curve", the first sentence of
  the proof of `lem:inversion-sides`.
* `Schoenflies.invert_image_outside`, `Schoenflies.invert_image_outside_union_singleton`,
  `Schoenflies.invert_image_inside_diff`, `Schoenflies.invert_image_union_outside`,
  `Schoenflies.inversion_sides` — `lem:inversion-sides`.
* `Schoenflies.exists_stronglyAccessible_dist_lt`, `Schoenflies.tangent_dense`,
  `Schoenflies.tangent_dense_inside` — `lem:tangent-dense`.
* `Schoenflies.PointedInteriorExtension` — the `prop:pointed-extension` interface, discharged
  by `Schoenflies.pointed_extension` in `Schoenflies/Endgame.lean`.
* `Schoenflies.exterior_extension` — `prop:exterior-extension`, parametrically on that interface.
* `Schoenflies.IsHomeoOn` — no blueprint statement; the language "restricts to a homeomorphism
  of `S` onto `T`" that `prop:exterior-extension` is phrased in.
-/

open Bornology Metric Set

namespace Schoenflies

variable {C Ω : Set Plane} {a p x y : Plane} {ε : ℝ}

/-! ### Inversion about the unit circle centred at a point

`Schoenflies.invert a` is `EuclideanGeometry.inversion a 1`, which Mathlib defines for every
point including the centre, sending `a` to itself. That convention is what makes
`Schoenflies.invert_involutive` hypothesis-free, and it costs nothing: every statement below
that cares about the centre says so. -/

/-- Inversion about the unit circle centred at `a`: `I_a(x) = a + (x - a)/‖x - a‖²`, extended
by `I_a(a) = a` so that it is an involution of the whole plane. -/
noncomputable def invert (a x : Plane) : Plane := EuclideanGeometry.inversion a 1 x

@[simp] theorem invert_center (a : Plane) : invert a a = a :=
  EuclideanGeometry.inversion_self a 1

/-- The defining metric identity: inversion inverts the distance to the centre. -/
theorem dist_invert_center (a x : Plane) : dist (invert a x) a = (dist x a)⁻¹ := by
  rw [invert, EuclideanGeometry.dist_inversion_center]
  simp

theorem invert_invert (a x : Plane) : invert a (invert a x) = x :=
  EuclideanGeometry.inversion_inversion a one_ne_zero x

theorem invert_involutive (a : Plane) : Function.Involutive (invert a) := invert_invert a

theorem invert_injective (a : Plane) : Function.Injective (invert a) :=
  (invert_involutive a).injective

/-- Being an involution, inversion has image and preimage the same operation. This is what
makes openness of an image as cheap as openness of a preimage. -/
theorem invert_image_eq_preimage (a : Plane) (S : Set Plane) :
    invert a '' S = invert a ⁻¹' S :=
  congrFun (invert_involutive a).image_eq_preimage_symm S

@[simp] theorem invert_image_invert_image (a : Plane) (S : Set Plane) :
    invert a '' (invert a '' S) = S := by
  simp [← Set.image_comp, invert_invert]

theorem invert_eq_center_iff : invert a x = a ↔ x = a :=
  EuclideanGeometry.inversion_eq_center one_ne_zero

theorem continuousAt_invert (h : x ≠ a) : ContinuousAt (invert a) x :=
  ContinuousAt.inversion continuousAt_const continuousAt_const continuousAt_id h

theorem continuousOn_invert (a : Plane) : ContinuousOn (invert a) ({a}ᶜ : Set Plane) :=
  fun _ hx => (continuousAt_invert (by simpa using hx)).continuousWithinAt

/-- An open set missing the centre has open image: on the punctured plane, which is itself
open, inversion is a continuous involution, so the image is a preimage. -/
theorem isOpen_invert_image {S : Set Plane} (hS : IsOpen S) (ha : a ∉ S) :
    IsOpen (invert a '' S) := by
  rw [invert_image_eq_preimage]
  refine (continuousOn_invert a).isOpen_preimage isOpen_compl_singleton ?_ hS
  intro z hz
  simp only [mem_compl_iff, mem_singleton_iff]
  rintro rfl
  exact ha (by simpa using hz)

/-- "`I_a` is an involutive homeomorphism of `ℝ² ∖ {a}`", bundled. Its inverse is itself. -/
@[simps! -isSimp apply]
noncomputable def invertHomeo (a : Plane) : ({a}ᶜ : Set Plane) ≃ₜ ({a}ᶜ : Set Plane) where
  toFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  invFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  left_inv z := Subtype.ext (invert_invert a z)
  right_inv z := Subtype.ext (invert_invert a z)
  continuous_toFun := ((continuousOn_invert a).restrict).subtype_mk _
  continuous_invFun := ((continuousOn_invert a).restrict).subtype_mk _

/-! ### The image of a Jordan curve

Inversion is a homeomorphism on a neighbourhood of a curve avoiding the centre, so it carries
loops to loops. -/

/-- The first sentence of the proof of `lem:inversion-sides`: `C^a = I_a(C)` is a Jordan
curve. -/
theorem IsJordanCurve.invert_image (hC : IsJordanCurve C) (ha : a ∉ C) :
    IsJordanCurve (invert a '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  have hmaps : MapsTo f unitInterval ({a}ᶜ : Set Plane) := by
    intro t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact ha ⟨t, ht, rfl⟩
  refine ⟨invert a ∘ f, ⟨(continuousOn_invert a).comp hf.continuousOn hmaps, ?_, ?_⟩, ?_⟩
  · simp only [Function.comp_apply, hf.closes]
  · exact ((invert_injective a).injOn).comp hf.injOn (mapsTo_univ _ _)
  · rw [Set.image_comp]

/-! ### Inversion exchanges the two sides

The whole of `lem:inversion-sides`. The proof is carried in one theorem, because every step
speaks about the same set `U = I_a(Ext C) ∪ {a}`; the consequences that consumers want are
peeled off afterwards. -/

/-- Everything beyond a large enough closed ball about any point is exterior to a separating
curve: the curve and its interior together are bounded. -/
theorem exists_radius_compl_closedBall_subset_outside (hC : IsSeparating C) (a : Plane) :
    ∃ R > 0, (closedBall a R)ᶜ ⊆ outside C := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall a).1
    (hC.isJordanCurve.isCompact.isBounded.union hC.isBounded_inside)
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hz' : z ∉ C ∪ inside C := fun h =>
    hz (closedBall_subset_closedBall (le_max_left _ _) (hr h))
  have hzc : z ∈ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact fun h => hz' (Or.inl h)
  exact hzc.resolve_left fun h => hz' (Or.inr h)

/-- The centre is never on `C^a`, since it is not on `C`. -/
theorem notMem_invert_image (ha : a ∉ C) : a ∉ invert a '' C := by
  rintro ⟨w, hw, hwa⟩
  exact ha (invert_eq_center_iff.1 hwa ▸ hw)

/-! ### Homeomorphisms between subsets of the plane

`prop:exterior-extension` is a composition of four restricted homeomorphisms, so it needs a
name for "`f` restricts to a homeomorphism of `S` onto `T`". `Schoenflies.IsHomeoOn` is that
name, written the way `Schoenflies.Plane.IsSquareMover` writes the same thing: unbundled, with
the inverse named, so that composing two of them composes two honest functions `Plane → Plane`
instead of producing a subtype-valued `Homeomorph` that must be unwrapped at every use.

**This notion is general and belongs in a lower module.** It is here because
`prop:exterior-extension` is the first statement that needs it; the integrator should hoist it
(and check that no concurrent branch introduced a twin). -/

/-- `IsHomeoOn f g S T`: the maps `f` and `g` restrict to mutually inverse continuous
bijections between `S` and `T`. -/
structure IsHomeoOn (f g : Plane → Plane) (S T : Set Plane) : Prop where
  /-- `f` carries `S` into `T` -/
  mapsTo : MapsTo f S T
  /-- `g` carries `T` into `S` -/
  mapsTo_inv : MapsTo g T S
  /-- `f` is continuous on `S` -/
  continuousOn : ContinuousOn f S
  /-- `g` is continuous on `T` -/
  continuousOn_inv : ContinuousOn g T
  /-- the two are mutually inverse there -/
  invOn : InvOn g f S T

namespace IsHomeoOn

variable {f g f' g' : Plane → Plane} {S T U S' T' : Set Plane}

theorem symm (h : IsHomeoOn f g S T) : IsHomeoOn g f T S where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  invOn := h.invOn.symm

theorem bijOn (h : IsHomeoOn f g S T) : BijOn f S T :=
  h.invOn.bijOn h.mapsTo h.mapsTo_inv

theorem injOn (h : IsHomeoOn f g S T) : InjOn f S := h.bijOn.injOn

theorem image_eq (h : IsHomeoOn f g S T) : f '' S = T := h.bijOn.image_eq

/-- Composing two restricted homeomorphisms. -/
theorem comp (h : IsHomeoOn f g S T) (h' : IsHomeoOn f' g' T U) :
    IsHomeoOn (f' ∘ f) (g ∘ g') S U where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := h.invOn.comp h'.invOn h.mapsTo h'.mapsTo_inv

/-- Restricting to a smaller pair of sets, once the two `MapsTo` clauses are known there. -/
theorem mono (h : IsHomeoOn f g S T) (hS : S' ⊆ S) (hT : T' ⊆ T) (hf : MapsTo f S' T')
    (hg : MapsTo g T' S') : IsHomeoOn f g S' T' where
  mapsTo := hf
  mapsTo_inv := hg
  continuousOn := h.continuousOn.mono hS
  continuousOn_inv := h.continuousOn_inv.mono hT
  invOn := h.invOn.mono hS hT

/-- Deleting a matched pair of points. This is the step "`Φ*` restricts to a homeomorphism
after the two points `a, b` are removed" of `prop:exterior-extension`. -/
theorem sdiff_singleton (h : IsHomeoOn f g S T) {u v : Plane} (hu : u ∈ S) (huv : f u = v) :
    IsHomeoOn f g (S \ {u}) (T \ {v}) := by
  refine h.mono Set.sdiff_subset Set.sdiff_subset (fun z hz => ⟨h.mapsTo hz.1, ?_⟩)
    (fun w hw => ⟨h.mapsTo_inv hw.1, ?_⟩)
  · -- `f z = v = f u` would force `z = u` by injectivity.
    intro hmem
    exact hz.2 (mem_singleton_iff.2
      (h.injOn hz.1 hu ((mem_singleton_iff.1 hmem).trans huv.symm)))
  · -- `g w = u` would force `w = f u = v`.
    intro hmem
    refine hw.2 (mem_singleton_iff.2 ?_)
    rw [← huv, ← mem_singleton_iff.1 hmem, h.invOn.2 hw.1]

end IsHomeoOn

/-- Inversion restricts to a homeomorphism of any set missing the centre onto its image. -/
theorem isHomeoOn_invert {S : Set Plane} (ha : a ∉ S) :
    IsHomeoOn (invert a) (invert a) S (invert a '' S) where
  mapsTo := Set.mapsTo_image _ _
  mapsTo_inv := by
    rintro z ⟨w, hw, rfl⟩
    rwa [invert_invert]
  continuousOn := (continuousOn_invert a).mono (Set.subset_compl_singleton_iff.2 ha)
  continuousOn_inv := (continuousOn_invert a).mono
    (Set.subset_compl_singleton_iff.2 (notMem_invert_image ha))
  invOn := ⟨fun z _ => invert_invert a z, fun z _ => invert_invert a z⟩

/-! ### The closed-exterior extension

`prop:exterior-extension`, assuming `prop:pointed-extension`. That is the blueprint's own
citation, and it is the one statement of the endgame that is not yet available: it rests on
`thm:closed-interior-extension` (open) together with `lem:square-point-mover`
(`Schoenflies.Plane.exists_squareMover`, on `main`) and `lem:jordan-circle`
(`Schoenflies.IsJordanCurve.homeomorph`, on `main`).

Everything that inversion contributes is here; discharging
`Schoenflies.PointedInteriorExtension` finishes the exterior half of `thm:main`. -/

/-- **`prop:pointed-extension`**, as a hypothesis: a boundary homeomorphism between two Jordan
curves extends to a homeomorphism of the closed interiors carrying one prescribed interior
point to another.

This is *not* a restatement of `prop:exterior-extension`: it is about the two **interiors**,
which is the bounded theorem, and it is what the blueprint proves from
`thm:closed-interior-extension` and `lem:square-point-mover`. -/
def PointedInteriorExtension : Prop :=
  ∀ (C C' : Set Plane) (f g : Plane → Plane) (a b : Plane),
    IsJordanCurve C → IsJordanCurve C' → IsHomeoOn f g C C' → a ∈ inside C → b ∈ inside C' →
      ∃ F G : Plane → Plane,
        IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C ∧ F a = b

/-! ### Density of strongly accessible points

`lem:tangent-dense`. Nothing here distinguishes the two regions, so the lemma is proved for
either. The hypotheses are those of `Schoenflies.stronglyAccessible_of_isMinOn`: the region
swallows the component of each of its points, and the curve is in its closure — which for a
separating curve is `C = ∂Ω`. -/

/-- The core estimate. If `C` is compact and every point of `C` is a limit of points of `Ω`,
and `Ω` swallows the component in `Cᶜ` of each of its points, then near any `p ∈ C` there is a
strongly accessible point of `C`: pick `q ∈ Ω` within `ε/2` of `p`, and take the point of `C`
nearest to `q`; it is strongly accessible by `lem:nearest-strong` and within `2‖q - p‖` of
`p`. -/
theorem exists_stronglyAccessible_dist_lt (hCcpt : IsCompact C) (hCne : C.Nonempty)
    (hΩC : Ω ⊆ Cᶜ) (hΩmax : ∀ q ∈ Ω, connectedComponentIn Cᶜ q ⊆ Ω) (hCΩ : C ⊆ closure Ω)
    (hp : p ∈ C) (hε : 0 < ε) :
    ∃ b ∈ C, StronglyAccessible Ω b ∧ dist b p < ε := by
  obtain ⟨q, hqΩ, hqp⟩ := Metric.mem_closure_iff.1 (hCΩ hp) (ε / 2) (by linarith)
  -- A nearest point of `C` to `q`; `C` is compact and nonempty.
  obtain ⟨b, hbC, hbmin⟩ :=
    hCcpt.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
  have hmin : ∀ c ∈ C, dist q b ≤ dist q c := fun c hc => isMinOn_iff.1 hbmin c hc
  refine ⟨b, hbC, stronglyAccessible_of_isMinOn (hΩC hqΩ) hbC hmin (hΩmax q hqΩ), ?_⟩
  -- `‖b - p‖ ≤ ‖b - q‖ + ‖q - p‖ ≤ 2‖q - p‖ < ε`.
  have h1 : dist q b ≤ dist q p := hmin p hp
  have h2 : dist b p ≤ dist b q + dist q p := dist_triangle _ _ _
  rw [dist_comm q b] at h1
  rw [dist_comm p q] at hqp
  linarith

/-- **`lem:tangent-dense` (density of strongly accessible points)**, for either region of a
separating Jordan curve: the points of `C` strongly accessible from `Ω` are dense in `C`. -/
theorem tangent_dense (hC : IsSeparating C) (hΩ : IsRegionOf C Ω) :
    C ⊆ closure {b ∈ C | StronglyAccessible Ω b} := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨b, hbC, hbacc, hbp⟩ := exists_stronglyAccessible_dist_lt
    hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty hΩ.subset_compl
    (fun q hq => (hΩ.connectedComponentIn_eq hC hq).le) (hΩ.subset_closure hC) hp hε
  exact ⟨b, ⟨hbC, hbacc⟩, by rwa [dist_comm]⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.mem_vertexSet_induce_component
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

/-- **A 2-connected graph has no bridge**, in the form "deleting an edge leaves its two ends
connected" — the hypothesis of the cycle criterion.

The blueprint's proof names the two components of `G - e` and finds a vertex of one of them
other than its endpoint. This proof routes around instead, and never mentions a component: a
third vertex `w` exists; the graph without `v` still joins `u` to `w`, and the graph without
`u` still joins `w` to `v`; and a walk that survives a vertex deletion cannot have used an
edge there, so neither walk used `e`. A loop needs no argument at all. -/
theorem IsTwoConnected.no_bridge (h : G.IsTwoConnected) (hl : G.IsLink e u v) :
    (G.deleteEdges {e}).Reaches u v := by
  rcases eq_or_ne u v with rfl | huv
  · exact Reaches.refl (by simpa using hl.left_mem)
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  have h₁ : (G.deleteVerts {v}).Reaches u w :=
    (h.deleteVerts_connected' v).reaches (mem_deleteVerts_singleton_of_ne hl.left_mem huv)
      (mem_deleteVerts_singleton_of_ne hw hwv)
  have h₂ : (G.deleteVerts {u}).Reaches w v :=
    (h.deleteVerts_connected' u).reaches (mem_deleteVerts_singleton_of_ne hw hwu)
      (mem_deleteVerts_singleton_of_ne hl.right_mem (Ne.symm huv))
  exact (h₁.deleteEdges_of_deleteVerts hl.inc_right).trans
    (h₂.deleteEdges_of_deleteVerts hl.inc_left)

/-! ### The union of two graphs -/

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses _root_.Schoenflies.overlayGraph_finite
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

namespace Graph

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v x : α} {W : List β}

theorem IsTwoConnected.map (hf : InjOn f V(G)) (h : G.IsTwoConnected) :
    (G.map f).IsTwoConnected where
  hasThreeVertices := h.hasThreeVertices.map hf
  connected := h.connected.map f
  deleteVerts_connected := by
    intro a ha
    simp only [vertexSet_map, Set.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [map_deleteVerts_singleton hf hx]
    exact (h.deleteVerts_connected hx).map f

theorem isTwoConnected_map_iff (hf : InjOn f V(G)) :
    (G.map f).IsTwoConnected ↔ G.IsTwoConnected := by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨a, ha⟩ := h.connected.nonempty
  rw [vertexSet_map] at ha
  obtain ⟨z, hz, -⟩ := ha
  have : Nonempty α := ⟨z⟩
  have himg : InjOn (Function.invFunOn f V(G)) V(G.map f) := by
    rw [vertexSet_map]; exact Function.invFunOn_injOn_image f V(G)
  have := h.map himg
  rwa [map_map_invFunOn hf] at this

/-! ### The point set of a subgraph -/

end Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

namespace CellStructure

variable (S : CellStructure γ)

/-! ### Realizations -/

namespace Realization

variable {S}
variable (R : S.Realization)

/-- The **open nonboundary part** `|Γ| \ C` of def:admissible-graph. -/
def nonboundary : Set Plane := R.skeletonSet \ R.outerSet

end Realization

/-! ### The skeleton homeomorphism -/

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

/-- **The outer cycle corresponds** — part (a) of lem:combinatorial-invariance, at the level of
the two realizations. -/
theorem image_outerSet : g.toFun '' R₁.outerSet = R₂.outerSet :=
  g.image_pointSet_map S.outerGraph_le

end SkeletonHomeo

/-! ### Combinatorial invariance -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_PathGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.vertexSet_union_pathGraphOf
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

/-! ### Constructing a path graph -/

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

/-- The graph spanned by a walk has finitely many vertices, whatever the ambient graph.
Stated as a `Set.Finite` rather than as a `Graph.Finite` instance so that this file does not
have to depend on `Schoenflies/Graph/Degree.lean`; the two halves build one in a line. -/
theorem IsWalk.finite_vertexSet_pathGraphOf (h : G.IsWalk u W v) :
    V(G.pathGraphOf u W).Finite := by
  simpa using h.finite_walkVertices

theorem IsWalk.finite_edgeSet_pathGraphOf (h : G.IsWalk u W v) :
    E(G.pathGraphOf u W).Finite := by
  rw [pathGraphOf_edgeSet h]; exact List.finite_toSet W

end Graph
end

section
-- module Solutions.Q146_CD.BoundaryContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `lem:skeleton-crosscuts`: a crosscut inside one stage of the skeleton

Two anchors lying in a common finite stage are joined by a polygonal crosscut of the Jordan
domain that lies *in that stage's skeleton* (`jordan_schoenflies.tex` 2857-2872). This file
proves the first clause, for the source side.

Everything here concerns **one finite plane graph**: a stage is a
finite plane graph whose point set carries the Jordan curve `C` as its outer boundary
(`Graph.IsStageOn`), and nothing below mentions the sequence of stages that produces it.

The blueprint's proof splits on whether some *nonboundary* edge — one whose arc is not
contained in `C` — has both of its ends on `C`. If one does, its open interior is a whole
component of the open nonboundary part, so it is the only nonboundary edge and is itself the
crosscut. Otherwise every nonboundary edge meeting `C` has its other end inside, and the
interior subgraph `interiorPart` is connected because the half-open attached edges partition
the open nonboundary part into relatively clopen pieces.

## What is here, and what is not

This module was written in one sitting that ended early, and it stops after the source-side
crosscut. The rest of the section — the target crosscut of clause 2,
`lem:crosscut-side-correspondence`, `prop:boundary-continuity`, and the assembly of
`thm:square-extension` — is in `Schoenflies/BoundaryContinuity2.lean`, which imports this one.
An earlier version of this docstring listed those as if they were here; they never were.

## Blueprint

* `Graph.IsStageOn` — a finite plane graph carrying `C` as its outer boundary.
* `Graph.Nonboundary`, `Graph.interiorPart`, `Graph.attachEdges`,
  `Graph.isPreconnected_interiorPart` — the interior subgraph and its connectedness, which is
  the substance of the second case.
* `Graph.IsStageOn.exists_crosscut` — **`lem:skeleton-crosscuts`, clause 1**: the source-side
  polygonal crosscut between two prescribed points of `C` that the stage joins. Clause 2, the
  target crosscut, is in `Schoenflies/BoundaryContinuity2.lean`.
-/

open Metric Set Schoenflies
open scoped _root_.Graph

/-! ## `lem:skeleton-crosscuts`

A stage of the skeleton is a finite plane graph whose point set carries the Jordan curve `C` as
its outer boundary. The blueprint's proof splits on whether some *nonboundary* edge — an edge
whose arc is not contained in `C` — has both of its ends on `C`.

Everything in this section speaks about one finite plane graph and never
about the stages that produce it.
-/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {C D : Set Plane}

/-- An edge is **nonboundary** when its arc is not contained in the outer boundary. -/
def Nonboundary (drawing : β → ℝ → Plane) (C : Set Plane) (e : β) : Prop :=
  ¬ edgeArc drawing e ⊆ C

/-- **One finite stage of the skeleton**, as `lem:skeleton-crosscuts` uses it.

`C` is the outer boundary and `D` the region it bounds. The two substantive clauses are
`edge_split` — every edge either runs inside `C` or has all of its non-endpoint points in `D` —
and `isConnected_diff`, the admissibility hypothesis that the *open nonboundary part*
`|Γ| ∖ C` is connected.

`D` is an arbitrary set disjoint from `C`, not `Schoenflies.inside C`: the proof uses nothing
about it, and the consumer instantiates it with the Jordan domain. -/
structure IsStageOn (G : Graph Plane β) (drawing : β → ℝ → Plane) (C D : Set Plane) : Prop where
  /-- the graph is drawn in the plane -/
  isDrawing : IsDrawing G drawing
  /-- every **nonboundary** edge is drawn as a polygonal arc.

  Only the nonboundary edges: `def:admissible-graph` says "its edges *not contained in `C`* are
  polygonal arcs", and for a source stage that restriction is not a convenience but a necessity.
  The outer edges of a source stage are subarcs of the wild Jordan curve `C`, which is in general
  nowhere polygonal, so a field asking `IsPolygonal` of every edge would make `IsStageOn`
  unsatisfiable for exactly the graphs `lem:skeleton-crosscuts` is about. It was stated that way
  and is repaired here; both proofs below already applied it only to nonboundary edges. -/
  polygonal : ∀ ⦃e⦄, e ∈ E(G) → Nonboundary drawing C e →
    Schoenflies.IsPolygonal (edgeArc drawing e)
  /-- the outer boundary and the region it bounds are disjoint -/
  disjoint : Disjoint C D
  /-- a vertex off the outer boundary lies in the region -/
  vertex_mem : ∀ ⦃v⦄, v ∈ V(G) → v ∉ C → v ∈ D
  /-- an edge either lies on the outer boundary or has its interior in the region -/
  edge_split : ∀ ⦃e x y⦄, G.IsLink e x y →
    edgeArc drawing e ⊆ C ∨ edgeArc drawing e \ {x, y} ⊆ D
  /-- **admissibility**: the open nonboundary part is connected -/
  isConnected_diff : IsConnected (pointSet G drawing \ C)

namespace IsStageOn

theorem notMem_of_mem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ C) : z ∉ D :=
  fun hD => (h.disjoint.ne_of_mem hz hD) rfl

theorem notMem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ D) : z ∉ C :=
  fun hzC => h.notMem_of_mem_curve hzC hz

/-- Off the outer boundary, the point set of the stage lies in the region. This is the reading
of `edge_split` and `vertex_mem` the crosscut extraction needs. -/
theorem pointSet_diff_subset (h : IsStageOn G drawing C D) :
    pointSet G drawing \ C ⊆ D := by
  rintro p ⟨hp, hpC⟩
  rcases hp with hv | hp
  · exact h.vertex_mem hv hpC
  · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 hp
    obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    rcases h.edge_split hl with hsub | hsub
    · exact absurd (hsub hpe) hpC
    · -- `p` is on the edge and off the curve; if it is an end, the end is off the curve too.
      by_cases hpxy : p ∈ ({x, y} : Set Plane)
      · rcases hpxy with rfl | rfl
        · exact h.vertex_mem hl.left_mem hpC
        · exact h.vertex_mem hl.right_mem hpC
      · exact hsub ⟨hpe, hpxy⟩

/-- On a nonboundary edge the outer boundary is met only at the two ends. -/
theorem edgeArc_inter_curve (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) :
    edgeArc drawing e ∩ C ⊆ {x, y} := by
  rcases h.edge_split hl with hsub | hsub
  · exact absurd hsub hnb
  · rintro p ⟨hpe, hpC⟩
    by_contra hp
    exact h.notMem_of_mem_curve hpC (hsub ⟨hpe, hp⟩)

/-- The two ends of an edge lie on its arc. -/
theorem left_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : x ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).left_mem

theorem right_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : y ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).right_mem

/-- A nonboundary edge whose two ends lie in the region runs entirely inside it. -/
theorem edgeArc_subset_of_ends (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) (hx : x ∈ D) (hy : y ∈ D) :
    edgeArc drawing e ⊆ D := by
  intro p hp
  by_cases hpxy : p ∈ ({x, y} : Set Plane)
  · simp only [mem_insert_iff, mem_singleton_iff] at hpxy
    rcases hpxy with rfl | rfl
    · exact hx
    · exact hy
  · rcases h.edge_split hl with hc | hd
    · exact absurd hc hnb
    · exact hd ⟨hp, hpxy⟩

/-! ### Case 1: a nonboundary edge with both ends on the outer boundary

*Its open interior `e°` is a connected component of `X = |Γ| ∖ C`, because an edge interior
meets the rest of the graph only at its endpoints, and those endpoints have been removed. Hence
`X = e°`, and there is then only one nonboundary edge.* -/

/-- **Case 1, first half.** If a nonboundary edge `e` has both ends on `C`, the whole open
nonboundary part lies on `e`.

The proof is `lem:clopen-component` in the closed-set form: `edgeArc e` and the rest of the
drawing are two closed sets covering the point set whose common part misses `X`. -/
theorem diff_subset_edgeArc [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) : pointSet G drawing \ C ⊆ edgeArc drawing e := by
  classical
  -- Everything the drawing occupies apart from the interior of `e`.
  set R : Set Plane := V(G) ∪ ⋃ f ∈ {f | f ∈ E(G) ∧ f ≠ e}, edgeArc drawing f with hRdef
  have hRclosed : IsClosed R := by
    refine (Graph.finite_vertexSet (G := G)).isCompact.isClosed.union ?_
    refine (Set.Finite.isCompact_biUnion ?_
      fun f hf => h.isDrawing.isCompact_edgeArc hf.1).isClosed
    exact (Graph.finite_edgeSet (G := G)).subset fun f hf => hf.1
  have hcover : pointSet G drawing ⊆ edgeArc drawing e ∪ R := by
    rintro p (hv | hp)
    · exact Or.inr (Or.inl hv)
    · obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · exact Or.inl (hfe ▸ hpf)
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨f, ⟨hf, hfe⟩, hpf⟩))
  -- The two closed sets meet only at vertices, and both ends of `e` were removed.
  have hmeet : (pointSet G drawing \ C) ∩ (edgeArc drawing e ∩ R) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨-, hpC⟩, hpe, hpR⟩
    have hpV : p ∈ V(G) := by
      rcases hpR with hv | hp
      · exact hv
      · obtain ⟨f, ⟨hf, hfe⟩, hpf⟩ := mem_iUnion₂.1 hp
        exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hf (Ne.symm hfe) hpe hpf
    rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
    · exact hpC (h1 ▸ hx)
    · exact hpC (h1 ▸ hy)
  intro p hp
  by_contra hpe
  have hne1 : ((pointSet G drawing \ C) ∩ edgeArc drawing e).Nonempty := by
    obtain ⟨z, hze, hzC⟩ := not_subset.1 hnb
    exact ⟨z, ⟨edgeArc_subset_pointSet hl.edge_mem hze, hzC⟩, hze⟩
  have hne2 : ((pointSet G drawing \ C) ∩ R).Nonempty :=
    ⟨p, hp, (hcover hp.1).resolve_left hpe⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (h.isDrawing.isCompact_edgeArc hl.edge_mem).isClosed hRclosed
    (fun z hz => hcover hz.1) hne1 hne2
  rw [hmeet] at hcon
  exact hcon.ne_empty rfl

/-- **Case 1, second half.** With `X` reduced to one edge interior there is only one nonboundary
edge, so the two prescribed boundary points are exactly the ends of `e`. -/
theorem isLink_of_ends_mem [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) {a b : Plane} (hab : a ≠ b)
    (ha : ∃ f, G.Inc f a ∧ Nonboundary drawing C f)
    (hb : ∃ f, G.Inc f b ∧ Nonboundary drawing C f) : G.IsLink e a b := by
  have hsub := h.diff_subset_edgeArc hl hnb hx hy
  -- Any nonboundary edge carries a point of `X`, hence a point of `e` off the vertices.
  have key : ∀ f, f ∈ E(G) → Nonboundary drawing C f → f = e := by
    intro f hfE hf
    obtain ⟨z, hzf, hzC⟩ := not_subset.1 hf
    have hze : z ∈ edgeArc drawing e :=
      hsub ⟨edgeArc_subset_pointSet hfE hzf, hzC⟩
    by_contra hfe
    have hzV : z ∈ V(G) :=
      h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hze hzf
    rcases h.isDrawing.vertex_mem_edgeArc hl hzV hze with h1 | h1
    · exact hzC (h1 ▸ hx)
    · exact hzC (h1 ▸ hy)
  obtain ⟨fa, hfa, hfanb⟩ := ha
  obtain ⟨fb, hfb, hfbnb⟩ := hb
  have hia : G.Inc e a := key fa hfa.edge_mem hfanb ▸ hfa
  have hib : G.Inc e b := key fb hfb.edge_mem hfbnb ▸ hfb
  have h1 := hia.eq_or_eq_of_isLink hl
  have h2 := hib.eq_or_eq_of_isLink hl
  rw [hl.isLink_iff]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hab
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h1.trans h2.symm) hab

end IsStageOn

/-! ### Case 2: the interior subgraph

*Let `Λ` be the finite subgraph consisting of all vertices in `D` and all edges whose two
endpoints lie in `D`, allowing isolated interior vertices.* Only its point set is ever needed,
so `interiorPart` is that set rather than a `Graph`. -/

/-- The point set of the blueprint's interior subgraph `Λ`: the vertices lying in the region,
together with the edges that run entirely inside it. -/
def interiorPart (G : Graph Plane β) (drawing : β → ℝ → Plane) (D : Set Plane) : Set Plane :=
  (V(G) ∩ D) ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ edgeArc drawing e ⊆ D}, edgeArc drawing e

theorem interiorPart_subset : interiorPart G drawing D ⊆ D := by
  rintro p (⟨-, hp⟩ | hp)
  · exact hp
  · obtain ⟨e, ⟨-, hsub⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact hsub hpe

theorem interiorPart_subset_pointSet : interiorPart G drawing D ⊆ pointSet G drawing := by
  rintro p (⟨hp, -⟩ | hp)
  · exact Or.inl hp
  · obtain ⟨e, ⟨heE, -⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact edgeArc_subset_pointSet heE hpe

theorem isClosed_interiorPart [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (interiorPart G drawing D) := by
  refine ((Graph.finite_vertexSet (G := G)).inter_of_left D).isCompact.isClosed.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

/-- The union of a subset of `Λ` with the closed edges meeting it. The blueprint attaches the
*half-open* edges; taking the whole closed edge instead gives a set that is closed in the
plane, and intersecting back with `X = |Γ| ∖ C` recovers the blueprint's set, because the
removed ends are exactly the points of those edges lying on `C`. -/
def attachEdges (G : Graph Plane β) (drawing : β → ℝ → Plane) (S : Set Plane) : Set Plane :=
  S ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ (edgeArc drawing e ∩ S).Nonempty}, edgeArc drawing e

theorem subset_attachEdges {S : Set Plane} : S ⊆ attachEdges G drawing S := subset_union_left

theorem isClosed_attachEdges [G.Finite] (h : IsDrawing G drawing) {S : Set Plane}
    (hS : IsClosed S) : IsClosed (attachEdges G drawing S) := by
  refine hS.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

namespace IsStageOn

variable (hcase : ∀ ⦃e : β⦄ ⦃x y : Plane⦄, G.IsLink e x y → Nonboundary drawing C e →
  x ∈ C → y ∉ C)

/-- A **half edge** — a nonboundary edge with exactly one end on `C` — meets `Λ` only in its
other end. This is what makes the attached pieces of `X` half-open. -/
theorem edgeArc_inter_interiorPart (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hx : x ∈ C) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ {y} := by
  rintro p ⟨hpe, hpL⟩
  have hpD : p ∈ D := interiorPart_subset hpL
  have hpV : p ∈ V(G) := by
    rcases hpL with ⟨hv, -⟩ | hp
    · exact hv
    · obtain ⟨f, ⟨hfE, hfD⟩, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · -- `e` would run inside `D`, yet its end `x` is on `C`
        exact absurd (hfD (hfe ▸ h.left_mem_edgeArc hl)) (h.notMem_of_mem_curve hx)
      · exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hpe hpf
  rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
  · exact absurd (h1 ▸ hpD) (h.notMem_of_mem_curve hx)
  · exact h1

/-- **The selection step.** If `Λ` is split into two disjoint closed pieces `S`, `S'` and an
edge meets `S`, then everything that edge shares with `Λ` lies in `S`.

An edge running inside `D` is connected and contained in `S ∪ S'`, so it lies in one piece; a
half edge meets `Λ` in a single point. -/
theorem edgeArc_inter_interiorPart_subset (h : IsStageOn G drawing C D)
    {S S' : Set Plane} (hSc : IsClosed S) (hS'c : IsClosed S')
    (hunion : S ∪ S' = interiorPart G drawing D) (hinter : S ∩ S' = ∅)
    {e : β} (heE : e ∈ E(G)) (hmeet : (edgeArc drawing e ∩ S).Nonempty) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ S := by
  obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
  obtain ⟨z, hze, hzS⟩ := hmeet
  have hzL : z ∈ interiorPart G drawing D := hunion ▸ Or.inl hzS
  have hzD : z ∈ D := interiorPart_subset hzL
  have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hze) hzD
  by_cases hxC : x ∈ C
  · -- half edge with `C`-end `x`; `Λ` is met only at `y`
    have hy := h.edgeArc_inter_interiorPart hl hxC
    intro p hp
    rw [show p = y from hy hp, ← show z = y from hy ⟨hze, hzL⟩]
    exact hzS
  · by_cases hyC : y ∈ C
    · -- half edge with `C`-end `y`; `Λ` is met only at `x`
      have hx := h.edgeArc_inter_interiorPart hl.symm hyC
      intro p hp
      rw [show p = x from hx hp, ← show z = x from hx ⟨hze, hzL⟩]
      exact hzS
    · -- an interior edge: connected, so it lies in one of the two pieces
      have hxD : x ∈ D := h.vertex_mem hl.left_mem hxC
      have hyD : y ∈ D := h.vertex_mem hl.right_mem hyC
      have heD : edgeArc drawing e ⊆ D := h.edgeArc_subset_of_ends hl hnb hxD hyD
      have heL : edgeArc drawing e ⊆ interiorPart G drawing D :=
        fun p hp => Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, heD⟩, hp⟩)
      have hconn : IsPreconnected (edgeArc drawing e) :=
        ((h.isDrawing.edge_isArcBetween hl).isArc.isConnected).2
      have hsub : edgeArc drawing e ⊆ S := by
        by_contra hcon
        obtain ⟨w, hwe, hwS⟩ := not_subset.1 hcon
        have hwS' : w ∈ S' := by
          have := heL hwe
          rw [← hunion] at this
          exact this.resolve_left hwS
        have := isPreconnected_closed_iff.1 hconn S S' hSc hS'c
          (fun p hp => by rw [← hunion] at heL; exact heL hp) ⟨z, hze, hzS⟩ ⟨w, hwe, hwS'⟩
        obtain ⟨v, -, hv⟩ := this
        rw [hinter] at hv
        exact hv
      exact fun p hp => hsub hp.1

include hcase in
/-- **Case 2, the connectedness of `Λ`.** *For each component `L` of `|Λ|`, the union of `L`
with all half-open edges attached to vertices of `L` is both open and closed in `X`; these sets
partition `X`. Connectedness of `X` therefore implies that `|Λ|` is connected.* -/
theorem isPreconnected_interiorPart [G.Finite] (h : IsStageOn G drawing C D) :
    IsPreconnected (interiorPart G drawing D) := by
  classical
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hmt hmt'
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set S : Set Plane := interiorPart G drawing D ∩ t with hSdef
  set S' : Set Plane := interiorPart G drawing D ∩ t' with hS'def
  have hSc : IsClosed S := (isClosed_interiorPart h.isDrawing).inter ht
  have hS'c : IsClosed S' := (isClosed_interiorPart h.isDrawing).inter ht'
  have hunion : S ∪ S' = interiorPart G drawing D := by
    refine subset_antisymm (fun p hp => hp.elim (fun h' => h'.1) (fun h' => h'.1)) ?_
    intro p hp
    rcases hcov hp with h' | h'
    · exact Or.inl ⟨hp, h'⟩
    · exact Or.inr ⟨hp, h'⟩
  have hinter : S ∩ S' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨hp, hpt⟩, -, hpt'⟩
    rw [eq_empty_iff_forall_notMem] at hempty
    exact hempty p ⟨hp, hpt, hpt'⟩
  have hSsub : S ⊆ interiorPart G drawing D := fun p hp => hp.1
  have hS'sub : S' ⊆ interiorPart G drawing D := fun p hp => hp.1
  -- The two attached pieces are closed, cover `X`, and meet it in disjoint sets.
  have hsel : ∀ R R' : Set Plane, IsClosed R → IsClosed R' → R ∪ R' = interiorPart G drawing D →
      R ∩ R' = ∅ → ∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
      edgeArc drawing e ∩ interiorPart G drawing D ⊆ R :=
    fun R R' hR hR' hu hi e he hm =>
      h.edgeArc_inter_interiorPart_subset hR hR' hu hi he hm
  have hSsel := hsel S S' hSc hS'c hunion hinter
  have hS'sel := hsel S' S hS'c hSc (by rw [union_comm]; exact hunion)
    (by rw [inter_comm]; exact hinter)
  -- `X` is covered by the two attached pieces.
  have hcovX : pointSet G drawing \ C ⊆
      attachEdges G drawing S ∪ attachEdges G drawing S' := by
    rintro p hp
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    rcases hp.1 with hv | hpe
    · have : p ∈ interiorPart G drawing D := Or.inl ⟨hv, hpD⟩
      rw [← hunion] at this
      exact this.elim (fun h' => Or.inl (subset_attachEdges h'))
        (fun h' => Or.inr (subset_attachEdges h'))
    · obtain ⟨e, heE, hpe⟩ := mem_iUnion₂.1 hpe
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
      have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hpe) hpD
      -- Locate an end of `e` inside `Λ`; the edge follows it.
      have hend : ∃ w, w ∈ edgeArc drawing e ∧ w ∈ interiorPart G drawing D := by
        by_cases hxC : x ∈ C
        · have hyC : y ∉ C := hcase hl hnb hxC
          exact ⟨y, h.right_mem_edgeArc hl, Or.inl ⟨hl.right_mem, h.vertex_mem hl.right_mem hyC⟩⟩
        · exact ⟨x, h.left_mem_edgeArc hl, Or.inl ⟨hl.left_mem, h.vertex_mem hl.left_mem hxC⟩⟩
      obtain ⟨w, hwe, hwL⟩ := hend
      rw [← hunion] at hwL
      rcases hwL with hwS | hwS
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
  -- and meets the two of them in disjoint sets.
  have hdisjX : (pointSet G drawing \ C) ∩
      (attachEdges G drawing S ∩ attachEdges G drawing S') = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨hp, hpT, hpT'⟩
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    -- In every case `p` ends up in `Λ`, and then in both `S` and `S'`.
    have hkey : ∀ R R' : Set Plane, R ⊆ interiorPart G drawing D →
        (∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
          edgeArc drawing e ∩ interiorPart G drawing D ⊆ R) →
        p ∈ attachEdges G drawing R → p ∈ attachEdges G drawing R' →
        p ∈ interiorPart G drawing D → p ∈ R := by
      rintro R R' hRsub hRsel (hpR | hpR) - hpL
      · exact hpR
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpR
        exact hRsel e heE hme ⟨hpe, hpL⟩
    have hpL : p ∈ interiorPart G drawing D := by
      rcases hpT with hpS | hpe
      · exact hSsub hpS
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpe
        rcases hpT' with hpS' | hpe'
        · exact hS'sub hpS'
        · obtain ⟨f, ⟨hfE, hmf⟩, hpf⟩ := mem_iUnion₂.1 hpe'
          by_cases hef : e = f
          · -- the same edge meets both pieces, so the two pieces already meet
            obtain ⟨v, hve, hvS⟩ := hme
            have hvL : v ∈ interiorPart G drawing D := hSsub hvS
            have := hS'sel f hfE hmf ⟨hef ▸ hve, hvL⟩
            rw [eq_empty_iff_forall_notMem] at hinter
            exact absurd ⟨hvS, this⟩ (hinter v)
          · have : p ∈ V(G) := h.isDrawing.arcs_meet_at_vertex heE hfE hef hpe hpf
            exact Or.inl ⟨this, hpD⟩
    have h1 := hkey S S' hSsub hSsel hpT hpT' hpL
    have h2 := hkey S' S hS'sub hS'sel hpT' hpT hpL
    rw [eq_empty_iff_forall_notMem] at hinter
    exact hinter p ⟨h1, h2⟩
  obtain ⟨p, hpL, hpt⟩ := hmt
  obtain ⟨q, hqL, hqt'⟩ := hmt'
  have hne1 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S).Nonempty :=
    ⟨p, ⟨interiorPart_subset_pointSet hpL, h.notMem_curve (interiorPart_subset hpL)⟩,
      subset_attachEdges ⟨hpL, hpt⟩⟩
  have hne2 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S').Nonempty :=
    ⟨q, ⟨interiorPart_subset_pointSet hqL, h.notMem_curve (interiorPart_subset hqL)⟩,
      subset_attachEdges ⟨hqL, hqt'⟩⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (isClosed_attachEdges h.isDrawing hSc) (isClosed_attachEdges h.isDrawing hS'c)
    hcovX hne1 hne2
  rw [hdisjX] at hcon
  exact hcon.ne_empty rfl

/-! ### `lem:skeleton-crosscuts` -/

end IsStageOn

end Graph
end

section
-- module Solutions.Q146_CD.Endgame
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
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

/-- A `Homeomorph` between two subsets of the plane can always be presented as an
`IsHomeoOn` between honest self-maps of the plane: extend both by the identity.

This is the bridge from `lem:jordan-circle`, which produces `Nonempty (↥C ≃ₜ ↥S)`, to the
unbundled language everything downstream is written in. -/
theorem exists_isHomeoOn_of_homeomorph {S T : Set Plane} (e : ↥S ≃ₜ ↥T) :
    ∃ f g : Plane → Plane, IsHomeoOn f g S T ∧ ∀ (z : Plane) (hz : z ∈ S),
      f z = (e ⟨z, hz⟩ : Plane) := by
  classical
  refine ⟨fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z,
    fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun z hz => dif_pos hz⟩
  · exact fun z hz => by simp only [dif_pos hz]; exact (e ⟨z, hz⟩).2
  · exact fun w hw => by simp only [dif_pos hw]; exact (e.symm ⟨w, hw⟩).2
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (S.domRestrict fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z) =
        fun z : ↥S => (e z : Plane) := by
      funext z
      simp only [Set.domRestrict_apply, dif_pos z.2]
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (T.domRestrict fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w) =
        fun w : ↥T => (e.symm w : Plane) := by
      funext w
      simp only [Set.domRestrict_apply, dif_pos w.2]
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  · intro z hz
    simp only [dif_pos hz, dif_pos (e ⟨z, hz⟩).2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · intro w hw
    simp only [dif_pos hw, dif_pos (e.symm ⟨w, hw⟩).2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)

namespace IsHomeoOn

variable {f g : Plane → Plane} {S T : Set Plane}

/-- A restricted homeomorphism of the whole plane onto the whole plane *is* a
homeomorphism. This is the last step of `thm:main`. -/
noncomputable def homeomorphOfUniv (h : IsHomeoOn f g univ univ) : Plane ≃ₜ Plane where
  toFun := f
  invFun := g
  left_inv z := h.invOn.1 (mem_univ z)
  right_inv z := h.invOn.2 (mem_univ z)
  continuous_toFun := continuousOn_univ.1 h.continuousOn
  continuous_invFun := continuousOn_univ.1 h.continuousOn_inv

@[simp] theorem homeomorphOfUniv_apply (h : IsHomeoOn f g univ univ) (z : Plane) :
    h.homeomorphOfUniv z = f z := rfl

/-- The inverse of a restricted homeomorphism undoes it on images: if `f` carries `A ⊆ S` onto
`A'`, then `g` carries `A'` back onto `A`. -/
theorem image_inv_eq (h : IsHomeoOn f g S T) {A A' : Set Plane} (hA : A ⊆ S)
    (hA' : f '' A = A') : g '' A' = A := by
  rw [← hA', Set.image_image]
  exact (Set.EqOn.image_eq (fun z hz => h.invOn.1 (hA hz))).trans (Set.image_id A)

end IsHomeoOn

/-- **Matching one part of a partition matches the other.** If `F` is a bijection of `A ∪ B`
onto `T` carrying the disjoint piece `A` onto `A'`, it carries `B` onto `T ∖ A'`.

Used three times below: `Θ` carries `Int(C')` onto `Q ∖ ∂Q`, and each of the interior and the
exterior extension carries a region onto the corresponding region — which is exactly what makes
the two pasted pieces of `thm:main` injective together. -/
theorem image_eq_diff_of_bijOn_union {F : Plane → Plane} {A B T A' : Set Plane}
    (hF : BijOn F (A ∪ B) T) (hA : F '' A = A') (hdisj : Disjoint A B) :
    F '' B = T \ A' := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨z, hzB, rfl⟩
    refine ⟨hF.mapsTo (Or.inr hzB), fun hy => ?_⟩
    rw [← hA] at hy
    obtain ⟨w, hwA, hw⟩ := hy
    exact Set.disjoint_left.1 hdisj hwA (hF.injOn (Or.inl hwA) (Or.inr hzB) hw ▸ hzB)
  · rintro y ⟨hyT, hyA'⟩
    obtain ⟨z, hz, rfl⟩ := hF.surjOn hyT
    have hzB : z ∈ B := hz.resolve_left fun hzA => hyA' (by rw [← hA]; exact ⟨z, hzA, rfl⟩)
    exact ⟨z, hzB, rfl⟩

/-! ### The pasted map

`thm:main` glues the interior and the exterior extension. The glued map is `Set.piecewise`
under a different name, spelled so that the two evaluation lemmas below are the only interface
the proof needs. -/

open Classical in
/-- The map that is `f₁` on `S` and `f₂` off it. The blueprint's "defined by `F_int` on the
closed interior and by `F_ext` on the closed exterior". -/
noncomputable def paste (S : Set Plane) (f₁ f₂ : Plane → Plane) : Plane → Plane :=
  fun z => if z ∈ S then f₁ z else f₂ z

theorem paste_of_mem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∈ S) :
    paste S f₁ f₂ z = f₁ z := by
  classical exact if_pos hz

theorem paste_of_notMem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∉ S) :
    paste S f₁ f₂ z = f₂ z := by
  classical exact if_neg hz

/-! ### The square `Q` and its boundary `S`

The blueprint's `Q = [-1,1]²` is `Plane.closedSquare 0 1` and its boundary `S = ∂Q` is
`modelCurve`, by `modelCurve_eq_frontier`. One consequence is needed: removing the boundary
from the closed square leaves the open square, which is where `lem:square-point-mover` wants
its two points. -/

/-- A mover of the square, read as a restricted homeomorphism. -/
theorem Plane.IsSquareMover.isHomeoOn {c : Plane} {r : ℝ} {M N : Plane → Plane}
    (h : Plane.IsSquareMover c r M N) :
    IsHomeoOn M N (Plane.closedSquare c r) (Plane.closedSquare c r) where
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  invOn := h.invOn

/-! ### `thm:square-extension`, assumed

This is the one statement the module assumes, and the only thing standing between the library
and `thm:main`. It is the last big theorem of the manuscript; its proof occupies the whole of
Part II §§"Strongly accessible boundary points"–"Continuity at the Jordan curve". -/

/-- **`thm:square-extension` (square extension)**, as a hypothesis: for every Jordan curve `C`
and every homeomorphism `u : C → S` there is a homeomorphism `C ∪ Int(C) → Q` extending `u`.

Written in the unbundled `Schoenflies.IsHomeoOn` style: `u` comes with its inverse `v`, and the
conclusion produces the extension `F` together with its inverse `G`. `S` is
`Schoenflies.modelCurve` and `Q` is `Schoenflies.Plane.closedSquare 0 1`. -/
def SquareExtension : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (C ∪ inside C) (Plane.closedSquare 0 1) ∧ EqOn F u C

/-! ### Disjointness of a curve from its two regions

A curve is disjoint from either of its two regions, and adding it and removing it again is the
identity. The pastings below use these constantly. -/

variable {C C' : Set Plane}

theorem disjoint_curve_inside (C : Set Plane) : Disjoint C (inside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem disjoint_curve_outside (C : Set Plane) : Disjoint C (outside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem union_inside_sdiff (C : Set Plane) : (C ∪ inside C) \ C = inside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_inside C)).le

theorem union_outside_sdiff (C : Set Plane) : (C ∪ outside C) \ C = outside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_outside C)).le

/-- An extension of a boundary homeomorphism to the closed interiors carries the interior onto
the interior. The blueprint never says this; the pointed extension and `thm:main` both need
it. -/
theorem image_inside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C')) (hf : EqOn F f C) (hfC : f '' C = C') :
    F '' inside C = inside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_inside C)
  rwa [union_inside_sdiff] at this

/-- The same for the closed exteriors. -/
theorem image_outside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C')) (hf : EqOn F f C)
    (hfC : f '' C = C') : F '' outside C = outside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_outside C)
  rwa [union_outside_sdiff] at this

/-! ### `prop:square-reduction` and `thm:closed-interior-extension`

The blueprint's proof verbatim: choose `h : C' → S` by `lem:jordan-circle`, extend `h ∘ f` and
`h` over the two closed discs by `thm:square-extension`, and take `Ψ⁻¹ ∘ Φ`. -/

/-- **`prop:square-reduction` (reduction to the square).** If every boundary homeomorphism from
a Jordan curve to `S` has a closed-interior extension, then every homeomorphism `f : C → C'`
between Jordan curves extends to a homeomorphism `C ∪ Int(C) → C' ∪ Int(C')`. -/
theorem square_reduction (hsq : SquareExtension) {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C := by
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := hsq C (h ∘ f) (g ∘ k) hC (hfg.comp hhk)
  obtain ⟨Ψ, Ψ', hΨ, hΨeq⟩ := hsq C' h k hC' hhk
  refine ⟨Ψ' ∘ Φ, Φ' ∘ Ψ, hΦ.comp hΨ.symm, fun z hz => ?_⟩
  have h1 : f z ∈ C' := hfg.mapsTo hz
  change Ψ' (Φ z) = f z
  rw [hΦeq hz]
  change Ψ' (h (f z)) = f z
  rw [← hΨeq h1]
  exact hΨ.invOn.1 (Set.mem_union_left _ h1)

/-- **`thm:closed-interior-extension` (closed-interior extension).** Every homeomorphism
`f : C → C'` between Jordan curves extends to a homeomorphism of the closed interiors.

Under the standing assumption `SquareExtension` this is literally `prop:square-reduction`; it
is recorded under its own name because everything downstream cites it by that name. -/
theorem closed_interior_extension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C :=
  square_reduction hsq hC hC' hfg

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

/-- The closed interior of a Jordan curve is closed: it is the closure of the interior. -/
theorem isClosed_union_inside (hC : IsSeparating C) : IsClosed (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact isClosed_closure

/-- The closed exterior of a Jordan curve is closed. -/
theorem isClosed_union_outside (hC : IsSeparating C) : IsClosed (C ∪ outside C) := by
  rw [Set.union_comm, ← (IsRegionOf.outside C).closure_eq hC]
  exact isClosed_closure

/-- The two closed sides cover the plane. -/
theorem union_inside_union_outside (C : Set Plane) :
    (C ∪ inside C) ∪ (C ∪ outside C) = univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : z ∈ C
  · exact Or.inl (Or.inl hz)
  · have hz' : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hz
    exact hz'.imp Or.inr Or.inr

/-- A point outside the closed interior is exterior. -/
theorem mem_outside_of_notMem_union_inside {z : Plane} (hz : z ∉ C ∪ inside C) :
    z ∈ outside C := by
  have hzC : z ∉ C := fun h => hz (Or.inl h)
  have : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
  exact this.resolve_left fun h => hz (Or.inr h)

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryContinuity2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet
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

/-! ### Pushing arcs forward

`lem:crosscut-side-correspondence` labels the target sides by `u(A₁)` and `u(A₂)`, so the two
target arcs have to be produced as images. Nothing here is specific to the square. -/

/-- The image of an arc under a map continuous and injective on a set containing it. -/
theorem IsArcBetween.image_of_injOn {A S : Set Plane} {p q : Plane} {f : Plane → Plane}
    (h : IsArcBetween A p q) (hAS : A ⊆ S) (hcont : ContinuousOn f S) (hinj : InjOn f S) :
    IsArcBetween (f '' A) (f p) (f q) := by
  obtain ⟨g, hg, hgi, hgim, hg0, hg1⟩ := h
  have hmem : ∀ t ∈ unitInterval, g t ∈ S := by
    intro t ht
    exact hAS (hgim ▸ mem_image_of_mem g ht)
  refine ⟨f ∘ g, hcont.comp hg hmem, ?_, ?_, by simp [hg0], by simp [hg1]⟩
  · intro s hs t ht hst
    exact hgi hs ht (hinj (hmem s hs) (hmem t ht) hst)
  · rw [← hgim, image_comp]

/-- The image of a cut pair. -/
theorem IsCutPair.image {f : Plane → Plane} (h : IsCutPair C a b A₁ A₂)
    (hcont : ContinuousOn f C) (hinj : InjOn f C) :
    IsCutPair (f '' C) (f a) (f b) (f '' A₁) (f '' A₂) where
  fst := h.fst.image_of_injOn h.fst_subset hcont hinj
  snd := h.snd.image_of_injOn h.snd_subset hcont hinj
  union_eq := by rw [← image_union, h.union_eq]
  inter_eq := by
    rw [← hinj.image_inter h.fst_subset h.snd_subset, h.inter_eq, image_pair]

/-- The image of a cut pair under a restricted homeomorphism, in the form the target side of
`lem:crosscut-side-correspondence` needs it. -/
theorem IsCutPair.image_of_isHomeoOn {T : Set Plane} (h : IsCutPair C a b A₁ A₂)
    (hu : IsHomeoOn u v C T) : IsCutPair T (u a) (u b) (u '' A₁) (u '' A₂) := by
  have h' := h.image hu.continuousOn hu.injOn
  rwa [hu.image_eq] at h'

/-! ### Anchors that separate

The selection step of `prop:boundary-continuity`. Given two distinct points `p, r` of the curve
and a dense set `𝒜` of anchors, we need anchors `a, b` with `p` and `r` on opposite arcs of `C`
from `a` to `b`. Density produces one anchor on each of the two open arcs of `C` from `p` to
`r`; the separation is then automatic, because an arc from `a` to `b` avoiding `p` and `r`
would be a connected subset of `C ∖ {p, r}` meeting both of its two (relatively open) halves. -/

/-- **A dense set meets the relative interior of either arc of a cut pair.** The one use
`lem:anchor-density` is put to. -/
theorem exists_anchor_mem_arc (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcut : IsCutPair C a b A₁ A₂) : ∃ c ∈ 𝒜, c ∈ A₁ ∧ c ∉ A₂ := by
  -- an arc is more than its two endpoints, and the two endpoints are all that `A₂` shares
  obtain ⟨z, hzA, hz⟩ := not_subset.1 hcut.fst.not_subset_pair
  have hzA2 : z ∉ A₂ := fun h => hz (by rw [← hcut.inter_eq]; exact ⟨hzA, h⟩)
  have hA2closed : IsClosed A₂ := hcut.snd.isArc.isClosed
  obtain ⟨c, hcmem, hc⟩ :=
    mem_closure_iff.1 (hdense (hcut.fst_subset hzA)) _ hA2closed.isOpen_compl hzA2
  have hcC : c ∈ A₁ ∪ A₂ := by rw [hcut.union_eq]; exact hsub hc
  exact ⟨c, hc, hcC.resolve_right hcmem, hcmem⟩

/-- **Two anchors on opposite open arcs separate.** If `a` lies on the open arc `B₁ ∖ {p, r}`
and `b` on the opposite one, then any pair of arcs cutting `C` at `a` and `b` puts `p` and `r`
on different arcs.

The proof is the one separation argument of the section: an arc from `a` to `b` missing both
`p` and `r` is a connected subset of `C ∖ {p, r} = (C ∖ B₂) ∪ (C ∖ B₁)`, a union of two
relatively open pieces, and it meets both — because `a` is in the first and `b` in the
second. -/
theorem IsCutPair.separates (hB : IsCutPair C p r B₁ B₂) (hA : IsCutPair C a b A₁ A₂)
    (ha' : a ∉ B₂) (hb' : b ∉ B₁) :
    (p ∈ A₁ ∧ r ∈ A₂) ∨ (p ∈ A₂ ∧ r ∈ A₁) := by
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  -- no arc of the pair can hold both `p` and `r`
  have key : ∀ A : Set Plane, IsArcBetween A a b → A ⊆ C → p ∉ A → r ∉ A → False := by
    intro A hAarc hAC hpA hrA
    have hcov : A ⊆ B₂ᶜ ∪ B₁ᶜ := by
      intro z hz
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      have : z ∈ ({p, r} : Set Plane) := by rw [← hB.inter_eq]; exact ⟨hcon.2, hcon.1⟩
      rcases this with rfl | rfl
      · exact hpA hz
      · exact hrA hz
    have hempty : ∀ z ∈ A, z ∈ B₂ᶜ → z ∉ B₁ᶜ := by
      intro z hz hz2 hz1
      have : z ∈ B₁ ∪ B₂ := by rw [hB.union_eq]; exact hAC hz
      exact this.elim hz1 hz2
    obtain ⟨z, hzA, hz2, hz1⟩ :=
      hAarc.isArc.isConnected.2 _ _ (hB.snd.isArc.isClosed.isOpen_compl)
        (hB.fst.isArc.isClosed.isOpen_compl) hcov ⟨a, hAarc.left_mem, ha'⟩
        ⟨b, hAarc.right_mem, hb'⟩
    exact hempty z hzA hz2 hz1
  -- `p` and `r` are each on exactly one of the two arcs
  have hpne : p ≠ a ∧ p ≠ b := ⟨fun h => ha' (h ▸ hpB.2), fun h => hb' (h ▸ hpB.1)⟩
  have hrne : r ≠ a ∧ r ≠ b := ⟨fun h => ha' (h ▸ hrB.2), fun h => hb' (h ▸ hrB.1)⟩
  have hone : ∀ z : Plane, z ∈ C → z ≠ a → z ≠ b → (z ∈ A₁ ∧ z ∉ A₂) ∨ (z ∈ A₂ ∧ z ∉ A₁) := by
    intro z hzC hza hzb
    have hboth : ¬ (z ∈ A₁ ∧ z ∈ A₂) := by
      intro h
      have : z ∈ ({a, b} : Set Plane) := by rw [← hA.inter_eq]; exact h
      rcases this with h' | h'
      · exact hza h'
      · exact hzb h'
    have : z ∈ A₁ ∪ A₂ := by rw [hA.union_eq]; exact hzC
    rcases this with h | h
    · exact Or.inl ⟨h, fun h' => hboth ⟨h, h'⟩⟩
    · exact Or.inr ⟨h, fun h' => hboth ⟨h', h⟩⟩
  have hpC : p ∈ C := by rw [← hB.union_eq]; exact Or.inl hpB.1
  have hrC : r ∈ C := by rw [← hB.union_eq]; exact Or.inl hrB.1
  rcases hone p hpC hpne.1 hpne.2 with ⟨hp1, hp2⟩ | ⟨hp2, hp1⟩ <;>
    rcases hone r hrC hrne.1 hrne.2 with ⟨hr1, hr2⟩ | ⟨hr2, hr1⟩
  · exact absurd (key A₂ hA.snd hA.snd_subset hp2 hr2) not_false
  · exact Or.inl ⟨hp1, hr2⟩
  · exact Or.inr ⟨hp2, hr1⟩
  · exact absurd (key A₁ hA.fst hA.fst_subset hp1 hr1) not_false

/-! ### The hypotheses

Two predicates, one for each thing that is still being built. Both are *statements about one
curve*, so a consumer can discharge them curve by curve. -/

/-- **`lem:skeleton-crosscuts` together with `prop:skeleton-agreement`**, as
`lem:crosscut-side-correspondence` consumes them: any two distinct anchors are joined by a
crosscut `P` of `C`, whose image under the limit map is a crosscut `P'` of the open square from
`u a` to `u b`.

The agreement clause is stated on `P ∖ {a, b}`, which by `IsCrosscut.inter_eq` is exactly
`P ∩ Int(C)` — the part of the crosscut on which `F` is defined at all. -/
def HasAnchorCrosscuts (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ ⦃a b : Plane⦄, a ∈ 𝒜 → b ∈ 𝒜 → a ≠ b → ∃ P P' : Set Plane,
    IsCrosscut C P a b ∧ IsCrosscut modelCurve P' (u a) (u b) ∧
      F '' (P \ {a, b}) = P' \ {u a, u b}

/-- **The spokes at the anchors.** At an anchor `c` there are arbitrarily small connected
pieces `J` of the Jordan domain clinging to `c` whose `F`-images cling to `u c`.

This is the germ of the nonboundary edge that `lem:anchor-density` attaches to `c`: `J` is an
initial subarc of that edge with the endpoint `c` removed, and `F '' J` is the corresponding
initial subarc of the target edge, which ends at `u c` because the finite skeleton
homeomorphism sends `c` to `u c`. Nothing else about the spokes is used anywhere. -/
def HasSpokes (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ c ∈ 𝒜, ∀ ε > 0, ∃ J : Set Plane, J ⊆ inside C ∧ IsPreconnected J ∧ J ⊆ ball c ε ∧
    c ∈ closure J ∧ u c ∈ closure (F '' J)

/-! ### Discharging `HasAnchorCrosscuts` from a skeleton homeomorphism

The two steps a consumer has to perform, isolated so that they need not be reinvented: the
image of a crosscut under the finite skeleton homeomorphism is again a crosscut, and the
agreement clause follows from agreement of the limit map with that homeomorphism on the
crosscut. Neither says anything about the square, so both apply to the source and the target
side of any of the stages. -/

/-- **The image of a crosscut is a crosscut.** All that is asked of the map is continuity and
injectivity on a set containing the crosscut, plus the two clauses that are genuinely about the
target configuration: the image is polygonal, and everything but its two endpoints lies in the
target Jordan domain. -/
theorem IsCrosscut.image_of_injOn {C' Sk : Set Plane} {g : Plane → Plane}
    (hP : IsCrosscut C P a b) (hPSk : P ⊆ Sk) (hcont : ContinuousOn g Sk) (hinj : InjOn g Sk)
    (hC' : IsJordanCurve C') (hpoly : IsPolygonal (g '' P)) (ha : g a ∈ C') (hb : g b ∈ C')
    (hint : g '' (P \ {a, b}) ⊆ inside C') : IsCrosscut C' (g '' P) (g a) (g b) := by
  refine ⟨hC', hP.arc.image_of_injOn hPSk hcont hinj, hpoly, ha, hb, ?_⟩
  rintro z ⟨⟨w, hwP, rfl⟩, hz⟩
  refine hint ⟨w, ⟨hwP, ?_⟩, rfl⟩
  rintro (rfl | rfl)
  · exact hz (Or.inl rfl)
  · exact hz (Or.inr rfl)

/-- **The agreement clause of `Schoenflies.HasAnchorCrosscuts`**, from agreement of the limit
map with the skeleton homeomorphism on the part of the crosscut that lies in the domain. -/
theorem image_sdiff_eq_of_eqOn {Sk : Set Plane} {g : Plane → Plane} (hPSk : P ⊆ Sk)
    (hinj : InjOn g Sk) (ha : a ∈ P) (hb : b ∈ P) (hFg : EqOn F g (P \ {a, b})) :
    F '' (P \ {a, b}) = g '' P \ {g a, g b} := by
  rw [hFg.image_eq, (hinj.mono hPSk).image_sdiff_subset (pair_subset ha hb), image_pair]

/-! ### `lem:crosscut-side-correspondence` -/

/-- Removing a crosscut from the Jordan domain is the same as removing its interior: the two
endpoints are on the curve and so are not in the domain to begin with. -/
theorem inside_sdiff_crosscut (h : IsCrosscut C P a b) :
    inside C \ P = inside C \ (P \ {a, b}) := by
  refine Set.ext fun z => ⟨fun hz => ⟨hz.1, fun h' => hz.2 h'.1⟩, fun hz => ⟨hz.1, fun h' => ?_⟩⟩
  have hzab : z ∈ ({a, b} : Set Plane) := by
    by_contra hcon
    exact hz.2 ⟨h', hcon⟩
  rcases hzab with rfl | rfl
  · exact inside_subset_compl hz.1 h.left_mem
  · exact inside_subset_compl hz.1 h.right_mem

/-! ### `prop:boundary-continuity` -/

/-- The blueprint's `F̄`: the limit map on the Jordan domain and the boundary homeomorphism on
the curve. It is `Schoenflies.paste`, which comes with its two evaluation lemmas. -/
noncomputable def extendByBoundary (C : Set Plane) (u F : Plane → Plane) : Plane → Plane :=
  paste C u F

theorem extendByBoundary_of_mem {z : Plane} (hz : z ∈ C) : extendByBoundary C u F z = u z :=
  paste_of_mem hz

theorem extendByBoundary_of_notMem {z : Plane} (hz : z ∉ C) : extendByBoundary C u F z = F z :=
  paste_of_notMem hz

/-! ### `thm:square-extension` -/

/-! ### The assembled hypothesis, and `Schoenflies.SquareExtension` -/

/-- **Everything this section assumes**, for every Jordan curve and every boundary
homeomorphism onto the model square: a dense set of anchors, the limit homeomorphism of the
interiors (`prop:interior-homeomorphism`), the anchor crosscuts with their target images
(`lem:skeleton-crosscuts` and `prop:skeleton-agreement`), and the spokes at the anchors
(`lem:anchor-density`).

`Schoenflies.squareExtension_of_hasLimitHomeomorphism` turns this into
`Schoenflies.SquareExtension`, which is the input required by the final reduction. -/
def HasLimitHomeomorphism : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ (𝒜 : Set Plane) (F F' : Plane → Plane), 𝒜 ⊆ C ∧ C ⊆ closure 𝒜 ∧
      IsHomeoOn F F' (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C 𝒜 u F ∧ HasSpokes C 𝒜 u F

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses _root_.Schoenflies.overlayGraph_finite
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

/-! ### Elementary operation 1: edge subdivision

Blueprint, `def:generated-structure`, operation 1: "the edge `e` is replaced by a new vertex
`v` and two new edges `e₁, e₂`, whose endpoints are `v` together with one old endpoint of `e`
each; the relation `≼_abs` is extended by declaring `v ≼ e₁` and `v ≼ e₂`, each old endpoint of
`e` a subcell of its adjacent new edge, and `v, e₁, e₂` subcells of exactly the old strict
supercells of `e`; all pairs not involving `e` are unchanged." -/

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

/-- The orientation-aware replacement relation specialized to the subdivision data. -/
abbrev SubstWalk : γ → List γ → List γ → Prop :=
  CellStructure.SubstWalk S d.edge d.left d.right d.newEdge₁ d.newEdge₂

variable {d}

theorem notMem_cells_of_mem_newCells {z : γ} (h : z ∈ d.newCells) : z ∉ S.cells := by
  rcases h with rfl | rfl | rfl
  exacts [d.newVertex_notMem, d.newEdge₁_notMem, d.newEdge₂_notMem]

theorem notMem_newCells_of_mem_cells {z : γ} (h : z ∈ S.cells) : z ∉ d.newCells := fun hz =>
  notMem_cells_of_mem_newCells hz h

variable (d)

theorem edge_mem_cells : d.edge ∈ S.cells := S.mem_cells_of_mem_edgeSet d.edge_mem_edgeSet

theorem left_mem_cells : d.left ∈ S.cells := S.mem_cells_of_mem_vertexSet d.isLink.left_mem

theorem right_mem_cells : d.right ∈ S.cells := S.mem_cells_of_mem_vertexSet d.isLink.right_mem

/-- The outer cycle is untouched when the subdivided edge is not outer. -/
theorem outer_eq (he : d.edge ∉ E(S.outerGraph)) : d.outer = S.outerGraph :=
  subdivGraph_eq_self he

/-- The subdivided edge, when it is outer, is outer with its own two endpoints. -/
theorem outer_isLink (he : d.edge ∈ E(S.outerGraph)) :
    S.outerGraph.IsLink d.edge d.left d.right :=
  isLink_of_le_of_mem_edgeSet S.outerGraph_le he d.isLink

theorem outer_edgeSet_of_mem (he : d.edge ∈ E(S.outerGraph)) :
    E(d.outer) = insert d.newEdge₁ (insert d.newEdge₂ (E(S.outerGraph) \ {d.edge})) := by
  ext f
  simp only [outer, subdivGraph_edgeSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.outer_isLink he, and_true]
  tauto

end SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

/-- The cells after a subdivision: the old ones except the subdivided edge, plus the three new
ones. -/
theorem subdivideEdge_cells : (S.subdivideEdge d).cells = (S.cells \ {d.edge}) ∪ d.newCells := by
  ext z
  simp only [cells, subdivideEdge_skel, subdivideEdge_faces, d.skeleton_vertexSet,
    d.skeleton_edgeSet, SubdivData.newCells, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ((hz | hz) | hz)
    · rcases hz with rfl | hz
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨S.mem_cells_of_mem_vertexSet hz,
          S.vertexSet_ne_edgeSet hz d.edge_mem_edgeSet⟩
    · rcases hz with rfl | rfl | ⟨hz, hz'⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl ⟨S.mem_cells_of_mem_edgeSet hz, hz'⟩
    · exact Or.inl ⟨S.mem_cells_of_mem_faces hz, S.faces_ne_edgeSet hz d.edge_mem_edgeSet⟩
  · rintro (⟨hz, hz'⟩ | rfl | rfl | rfl)
    · rcases hz with (hz | hz) | hz
      · exact Or.inl (Or.inl (Or.inr hz))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hz, hz'⟩)))
      · exact Or.inr hz
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))

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

end CellStructure

/-! ### Generated matched cell structures -/

namespace CellStructure

/-! ### The combinatorial invariants

Assertions (iii), (v) and (vi) of `lem:cellulation-invariants`, together with the abstract form
of (viii) and the bookkeeping facts about `≼_abs` that the blueprint's proof uses without
comment (the relation relates cells to cells, it is reflexive, and a vertex is below each edge
it bounds). They are bundled because the induction propagates them together: the preservation
proof of each one reads the others at the previous stage. -/

namespace CombInvariants

/-- The other endpoint of an edge is below it too. -/
theorem sub_isLink' {S : CellStructure γ} (hS : S.CombInvariants) ⦃f a b : γ⦄
    (h : S.skel.IsLink f a b) : S.sub b f := hS.sub_isLink h.symm

end CombInvariants

/-! ### Edge subdivision preserves the combinatorial invariants -/

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

theorem subRel_of_old {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.edge) (hτ : τ ≠ d.edge) (h : S.sub σ τ) : d.subRel σ τ :=
  Or.inl ⟨notMem_newCells_of_mem_cells hσc, notMem_newCells_of_mem_cells hτc, hσ, hτ, h⟩

/-- On old cells other than the subdivided edge, the relation is unchanged: "all pairs not
involving `e` are unchanged". -/
theorem old_subRel_iff {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.edge) (hτ : τ ≠ d.edge) : d.subRel σ τ ↔ S.sub σ τ := by
  refine ⟨fun h => ?_, d.subRel_of_old hσc hτc hσ hτ⟩
  rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -, -⟩
  · exact h
  · exact absurd hσc (notMem_cells_of_mem_newCells h)
  · exact absurd (h ▸ hσc) d.newVertex_notMem
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact absurd hσc (notMem_cells_of_mem_newCells h)

/-- A new cell is below exactly the old strict supercells of the subdivided edge. -/
theorem newCells_subRel_iff {σ τ : γ} (hσ : σ ∈ d.newCells) (hτc : τ ∈ S.cells) :
    d.subRel σ τ ↔ (τ ≠ d.edge ∧ S.sub d.edge τ) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hσ, h.1, h.2⟩))))⟩
  rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h
  · exact absurd hσ h
  · exact absurd (h ▸ hσ) (notMem_newCells_of_mem_cells hτc)
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact h.2

theorem mem_subdivideEdge_cells_of_old {z : γ} (hz : z ∈ S.cells) (hze : z ≠ d.edge) :
    z ∈ (S.subdivideEdge d).cells := by
  rw [subdivideEdge_cells]; exact Or.inl ⟨hz, hze⟩

theorem mem_subdivideEdge_cells_of_new {z : γ} (hz : z ∈ d.newCells) :
    z ∈ (S.subdivideEdge d).cells := by
  rw [subdivideEdge_cells]; exact Or.inr hz

theorem left_ne_edge : d.left ≠ d.edge :=
  S.vertexSet_ne_edgeSet d.isLink.left_mem d.edge_mem_edgeSet

theorem right_ne_edge : d.right ≠ d.edge :=
  S.vertexSet_ne_edgeSet d.isLink.right_mem d.edge_mem_edgeSet

/-- **Edge subdivision preserves the combinatorial invariants**: the induction step of
assertions (iii), (v), (vi) — and of abstract (viii) — over the first constructor. -/
theorem combInvariants (hS : S.CombInvariants) : (S.subdivideEdge d).CombInvariants where
  sub_mem_left := by
    rintro σ τ (⟨-, -, hσ, -, h⟩ | ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h, -, -⟩)
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_left h) hσ
    · exact d.mem_subdivideEdge_cells_of_new h
    · exact d.mem_subdivideEdge_cells_of_new (Or.inl rfl)
    · exact d.mem_subdivideEdge_cells_of_old d.left_mem_cells d.left_ne_edge
    · exact d.mem_subdivideEdge_cells_of_old d.right_mem_cells d.right_ne_edge
    · exact d.mem_subdivideEdge_cells_of_new h
  sub_mem_right := by
    rintro σ τ (⟨-, -, -, hτ, h⟩ | ⟨rfl, h⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, hτ, h⟩)
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_right h) hτ
    · exact d.mem_subdivideEdge_cells_of_new h
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl))
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_right h) hτ
  sub_refl := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσ, hσe⟩ | hσ
    · exact d.subRel_of_old hσ hσ hσe hσe (hS.sub_refl hσ)
    · exact Or.inr (Or.inl ⟨rfl, hσ⟩)
  sub_isLink := by
    intro f a b hl
    rw [subdivideEdge_skel, d.skeleton_isLink] at hl
    rcases hl with ⟨hl, hfe, -, -⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
    · exact d.subRel_of_old (S.mem_cells_of_mem_vertexSet hl.left_mem)
        (S.mem_cells_of_mem_edgeSet hl.edge_mem)
        (S.vertexSet_ne_edgeSet hl.left_mem d.edge_mem_edgeSet) hfe (hS.sub_isLink hl)
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  face_maximal := by
    intro F τ hF h
    rw [subdivideEdge_faces] at hF
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    rcases h with ⟨-, -, -, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
    · exact hS.face_maximal hF h
    · exact h.symm
    · exact absurd (h ▸ hFc) d.newVertex_notMem
    · exact absurd (S.faces_ne_vertexSet hF d.isLink.left_mem) (not_not.2 h)
    · exact absurd (S.faces_ne_vertexSet hF d.isLink.right_mem) (not_not.2 h)
    · exact absurd hFc (notMem_cells_of_mem_newCells h)
  nonboundary_edge := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    obtain ⟨f, hfE, hfO, hfsub⟩ := hS.nonboundary_edge hF
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    by_cases hfe : f = d.edge
    · subst hfe
      refine ⟨d.newEdge₁, ?_, ?_, ?_⟩
      · rw [subdivideEdge_skel, d.skeleton_edgeSet]; exact Set.mem_insert _ _
      · rw [subdivideEdge_outerGraph, d.outer_eq hfO]; exact d.newEdge₁_notMem_outer
      · exact (d.newCells_subRel_iff (Or.inr (Or.inl rfl)) hFc).2 ⟨hFe, hfsub⟩
    · refine ⟨f, ?_, ?_, ?_⟩
      · rw [subdivideEdge_skel, d.skeleton_edgeSet]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hfE, hfe⟩)
      · rw [subdivideEdge_outerGraph]
        rintro (⟨hz, -⟩ | ⟨hz, -⟩)
        · exact hfO hz
        · rcases hz with rfl | rfl
          exacts [d.newEdge₁_notMem (S.mem_cells_of_mem_edgeSet hfE),
            d.newEdge₂_notMem (S.mem_cells_of_mem_edgeSet hfE)]
      · exact d.subRel_of_old (S.mem_cells_of_mem_edgeSet hfE) hFc hfe hFe hfsub
  mem_face := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσ, hσe⟩ | hσ
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face hσ
      exact ⟨F, hF, d.subRel_of_old hσ (S.mem_cells_of_mem_faces hF) hσe
        (S.faces_ne_edgeSet hF d.edge_mem_edgeSet) hsub⟩
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face d.edge_mem_cells
      exact ⟨F, hF, (d.newCells_subRel_iff hσ (S.mem_cells_of_mem_faces hF)).2
        ⟨S.faces_ne_edgeSet hF d.edge_mem_edgeSet, hsub⟩⟩
  outerEdge_unique := by
    intro f hf
    rw [subdivideEdge_outerGraph, outer, subdivGraph_edgeSet] at hf
    rcases hf with ⟨hfO, hfe⟩ | ⟨hfnew, hlink⟩
    · obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hfO
      have hfc : f ∈ S.cells :=
        S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hfO)
      refine ⟨F, ⟨hF, d.subRel_of_old hfc (S.mem_cells_of_mem_faces hF) hfe
        (S.faces_ne_edgeSet hF d.edge_mem_edgeSet) hsub⟩, fun T hT => ?_⟩
      exact huniq T ⟨hT.1, (d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT.1) hfe
        (S.faces_ne_edgeSet hT.1 d.edge_mem_edgeSet)).1 hT.2⟩
    · have hfnew' : f ∈ d.newCells := by
        rcases hfnew with rfl | rfl
        exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
      obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hlink.edge_mem
      refine ⟨F, ⟨hF, (d.newCells_subRel_iff hfnew' (S.mem_cells_of_mem_faces hF)).2
        ⟨S.faces_ne_edgeSet hF d.edge_mem_edgeSet, hsub⟩⟩, fun T hT => ?_⟩
      exact huniq T ⟨hT.1, ((d.newCells_subRel_iff hfnew'
        (S.mem_cells_of_mem_faces hT.1)).1 hT.2).2⟩

/-! #### The parent map of an edge subdivision -/

open scoped Classical in
/-- **The parent map of one edge subdivision** — assertion (iv). The three new cells have the
subdivided edge as parent; every surviving cell is its own parent. -/
noncomputable def parent : γ → γ := fun σ => if σ ∈ d.newCells then d.edge else σ

theorem parent_of_mem_newCells {σ : γ} (h : σ ∈ d.newCells) : d.parent σ = d.edge := by
  rw [parent]; exact if_pos h

theorem parent_of_notMem_newCells {σ : γ} (h : σ ∉ d.newCells) : d.parent σ = σ := by
  rw [parent]; exact if_neg h

theorem parent_of_mem_cells {σ : γ} (h : σ ∈ S.cells) : d.parent σ = σ :=
  d.parent_of_notMem_newCells (notMem_newCells_of_mem_cells h)

/-- **Assertion (iv), the compatibility clause**: `σ ≼ τ` in the refined structure implies
`par σ ≼ par τ` in the old one. -/
theorem sub_parent (hS : S.CombInvariants) {σ τ : γ} (h : (S.subdivideEdge d).sub σ τ) :
    S.sub (d.parent σ) (d.parent τ) := by
  rcases h with ⟨hσ, hτ, -, -, h⟩ | ⟨rfl, hσ⟩ | ⟨rfl, hτ⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hσ, -, h⟩
  · rw [d.parent_of_notMem_newCells hσ, d.parent_of_notMem_newCells hτ]; exact h
  · rw [d.parent_of_mem_newCells hσ]; exact hS.sub_refl d.edge_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl rfl)]
    rcases hτ with rfl | rfl
    · rw [d.parent_of_mem_newCells (Or.inr (Or.inl rfl))]; exact hS.sub_refl d.edge_mem_cells
    · rw [d.parent_of_mem_newCells (Or.inr (Or.inr rfl))]; exact hS.sub_refl d.edge_mem_cells
  · rw [d.parent_of_mem_cells d.left_mem_cells, d.parent_of_mem_newCells (Or.inr (Or.inl rfl))]
    exact hS.sub_isLink d.isLink
  · rw [d.parent_of_mem_cells d.right_mem_cells, d.parent_of_mem_newCells (Or.inr (Or.inr rfl))]
    exact hS.sub_isLink' d.isLink
  · rw [d.parent_of_mem_newCells hσ, d.parent_of_mem_cells (hS.sub_mem_right h)]; exact h

end SubdivData

/-! ### A 2-cell split preserves the combinatorial invariants -/

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

theorem subset_closure (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) (hτ : τ ∈ S.cells)
    (hsub : S.sub σ τ) : R.cell σ ⊆ closure (R.cell τ) := by
  rw [h.closure_eq hτ]
  exact Set.subset_biUnion_of_mem (u := fun ρ => R.cell ρ) (show σ ∈ _ from ⟨hσ, hsub⟩)

/-- **Assertion (viii)**: distinct open 2-cells are never comparable.

The hypothesis is that the lower 2-cell is *open*, which is what assertion (vii) supplies — it
realizes each open 2-cell as the bounded complementary region of a Jordan curve. Given that,
`thm:jordan` is not needed a second time: a nonempty open set inside a closure meets the set. -/
theorem face_eq (h : R.IsCellDecomposition D) {F T : γ} (hF : F ∈ S.faces) (hT : T ∈ S.faces)
    (hopen : IsOpen (R.cell F)) (hsub : R.cell F ⊆ closure (R.cell T)) : F = T := by
  by_contra hne
  obtain ⟨z, hz⟩ := h.nonempty (S.mem_cells_of_mem_faces hF)
  obtain ⟨w, hwF, hwT⟩ := mem_closure_iff.1 (hsub hz) (R.cell F) hopen hz
  exact Set.disjoint_left.1
    (h.disjoint (S.mem_cells_of_mem_faces hF) (S.mem_cells_of_mem_faces hT) hne) hwF hwT

end IsCellDecomposition

end Realization

/-! ### Assertion (i) is preserved by an edge subdivision

The induction step of (i) over the first constructor. It relates two realizations of two
different structures, so it needs a name for "`R'` refines `R` along `d`": that is
`SubdivData.IsRefinement`, whose fields are exactly the blueprint's sentence "the corresponding
point is inserted into the corresponding edge using the edge parametrization", read as a
statement about the resulting open cells and their closures. -/

namespace SubdivData

variable {S : CellStructure γ} {d : S.SubdivData}

/-- **`R'` refines `R` along the subdivision `d`.** Every surviving cell stays where it was;
the old open edge is cut into the two new open edges and the new vertex; and the closure of
each new cell is the new cell together with the cells the update declares below it. -/
structure IsRefinement (d : S.SubdivData) (R : S.Realization)
    (R' : (S.subdivideEdge d).Realization) : Prop where
  /-- Surviving cells are unmoved. -/
  cell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.edge → R'.cell σ = R.cell σ
  /-- The old open edge is cut in three. -/
  cell_edge : R.cell d.edge = R'.cell d.newEdge₁ ∪ R'.cell d.newVertex ∪ R'.cell d.newEdge₂
  /-- The three new open cells are nonempty. -/
  nonempty : ∀ ⦃σ⦄, σ ∈ d.newCells → (R'.cell σ).Nonempty
  /-- …and pairwise disjoint. -/
  disjoint : ∀ ⦃σ τ⦄, σ ∈ d.newCells → τ ∈ d.newCells → σ ≠ τ → Disjoint (R'.cell σ) (R'.cell τ)
  /-- The new vertex is a closed cell. -/
  closure_newVertex : closure (R'.cell d.newVertex) = R'.cell d.newVertex
  /-- The closure of the first new edge is it, the new vertex and the old left endpoint. -/
  closure_newEdge₁ : closure (R'.cell d.newEdge₁) =
    R'.cell d.newEdge₁ ∪ R'.cell d.newVertex ∪ R.cell d.left
  /-- The closure of the second new edge is it, the new vertex and the old right endpoint. -/
  closure_newEdge₂ : closure (R'.cell d.newEdge₂) =
    R'.cell d.newEdge₂ ∪ R'.cell d.newVertex ∪ R.cell d.right

/-- Nothing is below the new vertex but the new vertex. -/
theorem subRel_newVertex_iff (hS : S.CombInvariants) (d : S.SubdivData) {σ : γ} :
    d.subRel σ d.newVertex ↔ σ = d.newVertex := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨h.trans rfl, Or.inl h⟩)⟩
  rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
  · exact absurd (Or.inl rfl) h
  · exact h
  · exact absurd h d.newVertex_ne₁
  · exact absurd h d.newVertex_ne₂
  · exact absurd h d.newVertex_ne₁
  · exact absurd h d.newVertex_ne₂
  · exact absurd (hS.sub_mem_right h) d.newVertex_notMem

/-- The cells below the first new edge are it, the new vertex, and the old left endpoint. -/
theorem subRel_newEdge₁_iff (hS : S.CombInvariants) (d : S.SubdivData) {σ : γ} :
    d.subRel σ d.newEdge₁ ↔ (σ = d.newEdge₁ ∨ σ = d.newVertex ∨ σ = d.left) := by
  constructor
  · intro h
    rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
    · exact absurd (Or.inr (Or.inl rfl)) h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h d.newEdge_ne
    · exact absurd (hS.sub_mem_right h) d.newEdge₁_notMem
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-- The cells below the second new edge are it, the new vertex, and the old right endpoint. -/
theorem subRel_newEdge₂_iff (hS : S.CombInvariants) (d : S.SubdivData) {σ : γ} :
    d.subRel σ d.newEdge₂ ↔ (σ = d.newEdge₂ ∨ σ = d.newVertex ∨ σ = d.right) := by
  constructor
  · intro h
    rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
    · exact absurd (Or.inr (Or.inr rfl)) h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h d.newEdge_ne.symm
    · exact Or.inr (Or.inr h)
    · exact absurd (hS.sub_mem_right h) d.newEdge₂_notMem
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

namespace IsRefinement

variable {R : S.Realization} {R' : (S.subdivideEdge d).Realization} {D : Set Plane}

theorem cell_subset_edge (href : d.IsRefinement R R') {σ : γ} (hσ : σ ∈ d.newCells) :
    R'.cell σ ⊆ R.cell d.edge := by
  rw [href.cell_edge]
  rcases hσ with rfl | rfl | rfl
  · exact fun _ hz => Or.inl (Or.inr hz)
  · exact fun _ hz => Or.inl (Or.inl hz)
  · exact fun _ hz => Or.inr hz

/-- **Assertion (i) is preserved by an edge subdivision.** -/
theorem isCellDecomposition (hS : S.CombInvariants) (href : d.IsRefinement R R')
    (h : R.IsCellDecomposition D) : R'.IsCellDecomposition D where
  nonempty := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, hσe⟩ | hσn
    · rw [href.cell_eq hσc hσe]; exact h.nonempty hσc
    · exact href.nonempty hσn
  disjoint := by
    intro σ τ hσ hτ hne
    rw [subdivideEdge_cells] at hσ hτ
    rcases hσ with ⟨hσc, hσe⟩ | hσn <;> rcases hτ with ⟨hτc, hτe⟩ | hτn
    · rw [href.cell_eq hσc hσe, href.cell_eq hτc hτe]; exact h.disjoint hσc hτc hne
    · rw [href.cell_eq hσc hσe]
      exact (h.disjoint hσc d.edge_mem_cells hσe).mono_right (href.cell_subset_edge hτn)
    · rw [href.cell_eq hτc hτe]
      exact (h.disjoint d.edge_mem_cells hτc (Ne.symm hτe)).mono_left
        (href.cell_subset_edge hσn)
    · exact href.disjoint hσn hτn hne
  iUnion_eq := by
    rw [← h.iUnion_eq]
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨σ, hσ, hz⟩
      rw [subdivideEdge_cells] at hσ
      rcases hσ with ⟨hσc, hσe⟩ | hσn
      · exact ⟨σ, hσc, by rwa [href.cell_eq hσc hσe] at hz⟩
      · exact ⟨d.edge, d.edge_mem_cells, href.cell_subset_edge hσn hz⟩
    · rintro ⟨σ, hσ, hz⟩
      by_cases hσe : σ = d.edge
      · subst hσe
        rw [href.cell_edge] at hz
        rcases hz with hz | hz
        · rcases hz with hz | hz
          · exact ⟨d.newEdge₁, d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl)), hz⟩
          · exact ⟨d.newVertex, d.mem_subdivideEdge_cells_of_new (Or.inl rfl), hz⟩
        · exact ⟨d.newEdge₂, d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl)), hz⟩
      · exact ⟨σ, d.mem_subdivideEdge_cells_of_old hσ hσe, by rwa [href.cell_eq hσ hσe]⟩
  closure_eq := by
    intro τ hτ
    rw [subdivideEdge_cells] at hτ
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    rcases hτ with ⟨hτc, hτe⟩ | hτn
    · -- a surviving cell: the index set gains the new cells exactly when it had `e`
      rw [href.cell_eq hτc hτe, h.closure_eq hτc]
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨σ, ⟨hσc, hσsub⟩, hz⟩
        by_cases hσe : σ = d.edge
        · subst hσe
          rw [href.cell_edge] at hz
          have hnew : ∀ ρ ∈ d.newCells, ((S.subdivideEdge d).sub ρ τ) := fun ρ hρ =>
            (d.newCells_subRel_iff hρ hτc).2 ⟨hτe, hσsub⟩
          rcases hz with hz | hz
          · rcases hz with hz | hz
            · exact ⟨d.newEdge₁, ⟨d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl)),
                hnew _ (Or.inr (Or.inl rfl))⟩, hz⟩
            · exact ⟨d.newVertex, ⟨d.mem_subdivideEdge_cells_of_new (Or.inl rfl),
                hnew _ (Or.inl rfl)⟩, hz⟩
          · exact ⟨d.newEdge₂, ⟨d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl)),
              hnew _ (Or.inr (Or.inr rfl))⟩, hz⟩
        · exact ⟨σ, ⟨d.mem_subdivideEdge_cells_of_old hσc hσe,
            d.subRel_of_old hσc hτc hσe hτe hσsub⟩, by rwa [href.cell_eq hσc hσe]⟩
      · rintro ⟨σ, ⟨hσ, hσsub⟩, hz⟩
        rw [subdivideEdge_cells] at hσ
        rcases hσ with ⟨hσc, hσe⟩ | hσn
        · exact ⟨σ, ⟨hσc, (d.old_subRel_iff hσc hτc hσe hτe).1 hσsub⟩,
            by rwa [href.cell_eq hσc hσe] at hz⟩
        · exact ⟨d.edge, ⟨d.edge_mem_cells, ((d.newCells_subRel_iff hσn hτc).1 hσsub).2⟩,
            href.cell_subset_edge hσn hz⟩
    · -- a new cell: its closure is read off the refinement, and so is the index set
      have hleft : d.left ∈ (S.subdivideEdge d).cells :=
        d.mem_subdivideEdge_cells_of_old d.left_mem_cells d.left_ne_edge
      have hright : d.right ∈ (S.subdivideEdge d).cells :=
        d.mem_subdivideEdge_cells_of_old d.right_mem_cells d.right_ne_edge
      rcases hτn with rfl | rfl | rfl
      · rw [href.closure_newVertex]
        refine ⟨fun hz => ⟨d.newVertex, ⟨d.mem_subdivideEdge_cells_of_new (Or.inl rfl),
          (d.subRel_newVertex_iff hS).2 rfl⟩, hz⟩, ?_⟩
        rintro ⟨σ, ⟨-, hσsub⟩, hz⟩
        rwa [(d.subRel_newVertex_iff hS).1 hσsub] at hz
      · rw [href.closure_newEdge₁, ← href.cell_eq d.left_mem_cells d.left_ne_edge]
        constructor
        · rintro (hz | hz)
          · rcases hz with hz | hz
            · exact ⟨d.newEdge₁, ⟨d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl)),
                (d.subRel_newEdge₁_iff hS).2 (Or.inl rfl)⟩, hz⟩
            · exact ⟨d.newVertex, ⟨d.mem_subdivideEdge_cells_of_new (Or.inl rfl),
                (d.subRel_newEdge₁_iff hS).2 (Or.inr (Or.inl rfl))⟩, hz⟩
          · exact ⟨d.left, ⟨hleft, (d.subRel_newEdge₁_iff hS).2 (Or.inr (Or.inr rfl))⟩, hz⟩
        · rintro ⟨σ, ⟨-, hσsub⟩, hz⟩
          rcases (d.subRel_newEdge₁_iff hS).1 hσsub with rfl | rfl | rfl
          · exact Or.inl (Or.inl hz)
          · exact Or.inl (Or.inr hz)
          · exact Or.inr hz
      · rw [href.closure_newEdge₂, ← href.cell_eq d.right_mem_cells d.right_ne_edge]
        constructor
        · rintro (hz | hz)
          · rcases hz with hz | hz
            · exact ⟨d.newEdge₂, ⟨d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl)),
                (d.subRel_newEdge₂_iff hS).2 (Or.inl rfl)⟩, hz⟩
            · exact ⟨d.newVertex, ⟨d.mem_subdivideEdge_cells_of_new (Or.inl rfl),
                (d.subRel_newEdge₂_iff hS).2 (Or.inr (Or.inl rfl))⟩, hz⟩
          · exact ⟨d.right, ⟨hright, (d.subRel_newEdge₂_iff hS).2 (Or.inr (Or.inr rfl))⟩, hz⟩
        · rintro ⟨σ, ⟨-, hσsub⟩, hz⟩
          rcases (d.subRel_newEdge₂_iff hS).1 hσsub with rfl | rfl | rfl
          · exact Or.inl (Or.inl hz)
          · exact Or.inl (Or.inr hz)
          · exact Or.inr hz

end IsRefinement

end SubdivData

end CellStructure

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The two simple boundary paths obtained by cutting a face cycle at distinct vertices.
Its last two fields are deliberately identical to `SplitData.sub_face` and
`SplitData.paths_meet`, so an ear insertion can copy the data without translation. -/
structure BoundaryPaths (S : CellStructure γ) (F a b : γ) where
  /-- The first boundary path from `a` to `b`. -/
  path₁ : List γ
  /-- The complementary boundary path. -/
  path₂ : List γ
  /-- The first list is a simple path in the skeleton. -/
  isPath₁ : S.skel.IsPath a path₁ b
  /-- The second list is a simple path in the skeleton. -/
  isPath₂ : S.skel.IsPath a path₂ b
  /-- The face and the cells of the two paths are exactly the cells below the face. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ F ↔
    σ = F ∨ σ ∈ S.pathCells a path₁ ∪ S.pathCells a path₂
  /-- The paths meet only at their two endpoints. -/
  paths_meet : S.pathCells a path₁ ∩ S.pathCells a path₂ = {a, b}

namespace BoundaryCycles

variable {S : CellStructure γ}

/-- The chosen simple boundary cycle of a face. -/
noncomputable def faceCycle (h : S.BoundaryCycles) (F : γ) (hF : F ∈ S.faces) :
    S.FaceCycle F :=
  Classical.choice (h.cycle F hF)

end BoundaryCycles

namespace FaceCycle

variable {S : CellStructure γ} {F : γ}

/-- The boundary list is a closed walk, in the orientation recorded by `boundary_eq`. -/
theorem isWalk (h : S.FaceCycle F) : S.skel.IsWalk h.target (S.boundary F) h.target := by
  rw [h.boundary_eq]
  exact .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk

/-- Every cell of the displayed boundary cycle is a strict subcell of its face. -/
theorem sub_of_mem_pathCells (h : S.FaceCycle F) {σ : γ}
    (hσ : σ ∈ S.pathCells h.target (h.edge :: h.walk)) : S.sub σ F :=
  h.sub_face.2 (Or.inr hσ)

/-- Nonempty walks with permuted edge lists have the same path cells. -/
theorem pathCells_eq_of_perm {u₁ v₁ u₂ v₂ : γ} {W₁ W₂ : List γ}
    (h₁ : S.skel.IsWalk u₁ W₁ v₁) (h₂ : S.skel.IsWalk u₂ W₂ v₂)
    (hp : W₁.Perm W₂) (hne₁ : W₁ ≠ []) (hne₂ : W₂ ≠ []) :
    S.pathCells u₁ W₁ = S.pathCells u₂ W₂ := by
  rw [CellStructure.pathCells, CellStructure.pathCells,
    h₁.walkVertices_eq_covered hne₁, h₂.walkVertices_eq_covered hne₂]
  ext σ
  simp only [Set.mem_union, Set.mem_setOf_eq, Graph.mem_coveredVertices_iff]
  constructor
  · rintro (hσ | ⟨e, he, hi⟩)
    · exact Or.inl (hp.mem_iff.1 hσ)
    · exact Or.inr ⟨e, hp.mem_iff.1 he, hi⟩
  · rintro (hσ | ⟨e, he, hi⟩)
    · exact Or.inl (hp.mem_iff.2 hσ)
    · exact Or.inr ⟨e, hp.mem_iff.2 he, hi⟩

/-- A vertex below a cyclic face lies on the complementary path used to present the cycle. -/
theorem mem_walk_of_vertex_sub (h : S.FaceCycle F) {a : γ} (ha : a ∈ V(S.skel))
    (haF : S.sub a F) : a ∈ S.skel.walkVertices h.source h.walk := by
  rcases h.sub_face.1 haF with rfl | haC
  · exact absurd ha (Set.disjoint_left.1 S.disjoint_faces_vertexSet h.face_mem)
  rcases haC with haE | haV
  · have hclosed : S.skel.IsWalk h.target (h.edge :: h.walk) h.target :=
      .cons h.isCycle.isLink.symm h.isCycle.isPath.isWalk
    exact (Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet ha (hclosed.edge_mem haE)).elim
  · rcases Graph.mem_walkVertices_cons h.isCycle.isLink.symm haV with rfl | haW
    · exact h.isCycle.isPath.target_mem_walkVertices
    · exact haW

end FaceCycle

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.RefinementStars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses _root_.Schoenflies.overlayGraph_finite
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

/-- A cell structure has finitely many cells. -/
theorem finite_cells (S : CellStructure γ) : S.cells.Finite :=
  (S.finite_vertexSet.union S.finite_edgeSet).union S.finite_faces

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-! ### Elementary facts about the closed star

`Realization.star` is the `St` of the blueprint and is defined in `CombinatorialInvariance.lean`;
these are the membership and containment lemmas its consumers need. -/

theorem mem_star_iff : y ∈ R.star σ ↔ ∃ τ, S.sub σ τ ∧ y ∈ closure (R.cell τ) := by
  simp only [star, Set.mem_iUnion, mem_supercells, exists_prop]

/-- A closed supercell sits inside the star. -/
theorem closure_cell_subset_star (h : S.sub σ τ) : closure (R.cell τ) ⊆ R.star σ := fun _ hz =>
  mem_star_iff.2 ⟨τ, h, hz⟩

/-- The index set of a star is finite: it consists of cells. -/
theorem finite_supercells (hS : S.CombInvariants) (σ : γ) : (S.supercells σ).Finite :=
  S.finite_cells.subset fun _ hτ => hS.sub_mem_right hτ

/-- A star is a finite union of closed sets, hence closed. -/
theorem isClosed_star (hS : S.CombInvariants) : IsClosed (R.star σ) :=
  (finite_supercells hS σ).isClosed_biUnion fun _ _ => isClosed_closure

/-! ### The carrier of a point

`car_Γ(x)`, the unique open cell containing `x`. It is a total function; off the closed domain
its value is junk, and every lemma below supplies `x ∈ D`. -/

open scoped Classical in
/-- **The carrier** `car_Γ(x)` of a point: the unique cell whose *open* cell contains `x`.
Uniqueness, and the fact that there is one at all for `x` in the closed domain, are assertion (i)
of `lem:cellulation-invariants` — see `IsCellDecomposition.carrier_eq` and
`IsCellDecomposition.mem_cell_carrier`. -/
noncomputable def carrier [Nonempty γ] (R : S.Realization) (x : Plane) : γ :=
  if h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ then h.choose else Classical.arbitrary γ

theorem carrier_spec [Nonempty γ] (R : S.Realization) (x : Plane)
    (h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ) :
    R.carrier x ∈ S.cells ∧ x ∈ R.cell (R.carrier x) := by
  rw [carrier, dif_pos h]
  exact h.choose_spec

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-- A star lies in the closure of the domain, so a bounded domain bounds every star. -/
theorem star_subset_closure_domain (h : R.IsCellDecomposition D) (hS : S.CombInvariants) :
    R.star σ ⊆ closure D := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_mono (h.cell_subset_domain (hS.sub_mem_right hτ)) hyτ

theorem isBounded_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsBounded (R.star σ) :=
  hD.closure.subset (h.star_subset_closure_domain hS)

/-- A star is compact: it is closed, and bounded once the domain is. The limit argument needs
this to intersect a nested sequence of stars. -/
theorem isCompact_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsCompact (R.star σ) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_star hS) (h.isBounded_star hS hD)

end IsCellDecomposition

/-! ### Refinement

The abstract relation "`R'` refines `R` with parent map `par`". It is deliberately not tied to
either elementary operation: the limit argument uses only these three clauses. -/

namespace Refines

variable {S' S'' : CellStructure γ} {R : S.Realization} {R' : S'.Realization}
  {R'' : S''.Realization} {par par' : γ → γ}

/-- Every realization refines itself along the identity: the empty sequence of elementary
refinements. -/
theorem refl (R : S.Realization) : R.Refines R id where
  parent_mem_cells := fun _ hσ => hσ
  parent_mem_faces := fun _ hF => hF
  sub_parent := fun _ _ h => h
  cell_subset := fun _ _ => subset_rfl

/-- **Refinements compose.** This is what turns `lem:refinement-compatibility` from a statement
about one elementary refinement into a statement about "a finite sequence of elementary
refinements": a consumer that builds its stages one operation at a time iterates this. -/
theorem trans (h' : R''.Refines R' par') (h : R'.Refines R par) : R''.Refines R (par ∘ par') where
  parent_mem_cells := fun _ hσ => h.parent_mem_cells (h'.parent_mem_cells hσ)
  parent_mem_faces := fun _ hF => h.parent_mem_faces (h'.parent_mem_faces hF)
  sub_parent := fun _ _ hst => h.sub_parent (h'.sub_parent hst)
  cell_subset := fun _ hσ => (h'.cell_subset hσ).trans (h.cell_subset (h'.parent_mem_cells hσ))

/-- The closed cells refine along with the open ones. -/
theorem closure_cell_subset (h : R'.Refines R par) {σ : γ} (hσ : σ ∈ S'.cells) :
    closure (R'.cell σ) ⊆ closure (R.cell (par σ)) :=
  closure_mono (h.cell_subset hσ)

/-- **`lem:refinement-compatibility`(b)**, the cell-star inclusion: once a star is small it stays
small. -/
theorem star_subset (href : R'.Refines R par) (hS' : S'.CombInvariants) {σ : γ} :
    R'.star σ ⊆ R.star (par σ) := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_cell_subset_star (href.sub_parent hτ)
    (href.closure_cell_subset (hS'.sub_mem_right hτ) hyτ)

end Refines

/-! ### Matched refinements: part (c)

Two realizations of one abstract structure are matched; a *compatible matched refinement* is a
pair of `Refines` instances sharing one parent map. That sharing **is** the blueprint's
"corresponding cells have corresponding parents": the parent map is a map of abstract names, so
there is only ever one of it. The substance is the consequence recorded here. -/

/-! ### Intersection of corresponding stars -/

/-! ### Stars and the face mesh -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ : γ} {x y : Plane} {η : ℝ}

/-- Every closed 2-cell incident with `σ` contains every point of the open cell `σ`. -/
theorem mem_closure_face (h : R.IsCellDecomposition D) {F : γ} (hσ : σ ∈ S.cells)
    (hF : F ∈ S.faces) (hsub : S.sub σ F) (hx : x ∈ R.cell σ) : x ∈ closure (R.cell F) :=
  h.subset_closure hσ (S.mem_cells_of_mem_faces hF) hsub hx

end IsCellDecomposition

namespace Refines

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {D : Set Plane} {η : ℝ}

/-- **`lem:star-face-mesh`(b)**: a new 2-cell is contained in its parent 2-cell, so refinement
cannot increase the diameter of a 2-cell. -/
theorem diam_cell_le (href : R'.Refines R par) (h : R.IsCellDecomposition D) (hD : IsBounded D)
    {F : γ} (hF : F ∈ S'.cells) :
    diam (closure (R'.cell F)) ≤ diam (closure (R.cell (par F))) :=
  diam_mono (href.closure_cell_subset hF)
    ((hD.subset (h.cell_subset_domain (href.parent_mem_cells hF))).closure)

end Refines

/-! ### Finite cell neighborhoods -/

/-- **The finite cell neighbourhood** of `lem:cell-neighborhood`: the complement of the union of
all closed cells that do not contain `x`. It is open, contains `x`, and its points have carriers
above the carrier of `x`. -/
def cellNbhd (R : S.Realization) (x : Plane) : Set Plane :=
  (⋃ τ ∈ {τ | τ ∈ S.cells ∧ x ∉ closure (R.cell τ)}, closure (R.cell τ))ᶜ

theorem isOpen_cellNbhd (R : S.Realization) (x : Plane) : IsOpen (R.cellNbhd x) :=
  ((S.finite_cells.subset fun _ hτ => hτ.1).isClosed_biUnion
    fun _ _ => isClosed_closure).isOpen_compl

theorem mem_cellNbhd_self (R : S.Realization) (x : Plane) : x ∈ R.cellNbhd x := by
  intro hx
  obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.1 hx
  exact hτ.2 hxτ

/-- Every closed cell that meets the neighbourhood contains `x`. -/
theorem mem_closure_of_mem_cellNbhd {R : S.Realization} {x z : Plane} {τ : γ} (hτ : τ ∈ S.cells)
    (hz : z ∈ R.cellNbhd x) (hzτ : z ∈ closure (R.cell τ)) : x ∈ closure (R.cell τ) := by
  by_contra hx
  exact hz (Set.mem_iUnion₂.2 ⟨τ, ⟨hτ, hx⟩, hzτ⟩)

/-! ### Corresponding skeleton points

The second sentence of `lem:refinement-compatibility`(c). A point of the realized skeleton lies
in an open 0-cell or an open 1-cell, and the skeleton homeomorphism carries each of those onto
the open cell of the *same abstract name*; so corresponding skeleton points have carriers that
correspond, with nothing to transport. -/

/-- The two ends of a drawn edge lie on its arc. Needed to cut the two endpoints out of the arc
on both sides of the skeleton homeomorphism at once. -/
theorem pos_pair_subset_edgeArc (R : S.Realization) {e a b : γ} (hl : S.skel.IsLink e a b) :
    ({R.pos a, R.pos b} : Set Plane) ⊆ Graph.edgeArc R.drawing e := by
  obtain ⟨-, -, hlink⟩ := R.isDrawing.edge_param (by rw [Graph.edgeSet_map]; exact hl.edge_mem)
  have h0 : R.drawing e 0 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ zero_mem_I
  have h1 : R.drawing e 1 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ one_mem_I
  have hpair : ({R.pos a, R.pos b} : Set Plane) = {R.drawing e 0, R.drawing e 1} := by
    rcases (hl.map R.pos).eq_and_eq_or_eq_and_eq hlink with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]; exact Set.pair_comm _ _
  rw [hpair]
  rintro z (rfl | rfl)
  exacts [h0, h1]

end Realization

namespace SkeletonHomeo

variable {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane} {σ : γ} {x : Plane}

/-- **The skeleton homeomorphism carries open skeleton cells onto open skeleton cells** of the
same abstract name. For a 0-cell this is `pos_apply`; for a 1-cell it is `edgeArc_image` with the
two endpoints removed from both sides, which is legitimate because `g` is injective on the
skeleton. -/
theorem image_cell (g : SkeletonHomeo R₁ R₂) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) :
    g.toFun '' R₁.cell σ = R₂.cell σ := by
  rcases hσ with hv | he
  · rw [R₁.cell_vertex hv, R₂.cell_vertex hv, Set.image_singleton, g.pos_apply hv]
  · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have harc : Graph.edgeArc R₁.drawing σ ⊆ R₁.skeletonSet :=
      Graph.edgeArc_subset_pointSet (by rw [Realization.edgeSet_graph]; exact he)
    rw [R₁.cell_edge hl, R₂.cell_edge hl,
      (g.injOn.mono harc).image_sdiff_subset (R₁.pos_pair_subset_edgeArc hl),
      g.edgeArc_image he, Set.image_pair, g.pos_apply hl.left_mem, g.pos_apply hl.right_mem]

end SkeletonHomeo

/-! ### The two elementary operations produce refinements

Both operations have the same shape: a single cell `c` is replaced by a set `N` of fresh cells,
and the parent map sends `N` to `c` and fixes everything else. `refines_of_elementary` proves the
geometric clause of `Refines` from that shape alone — the fresh cells must land inside `c`,
because any other cell of the old stage survives and is unmoved, and open cells of one stage are
disjoint. -/

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {c : γ} {N : Set γ} {D : Set Plane}

namespace SubdivData

variable {d : S.SubdivData}

/-- **An edge subdivision is a refinement.** `SubdivData.IsRefinement` already carries everything
the geometric clause needs, so no cell decomposition is required here. -/
theorem IsRefinement.refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.subdivideEdge d).Realization} (href : d.IsRefinement R R') :
    R'.Refines R d.parent where
  parent_mem_cells := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [d.parent_of_mem_cells hσc]; exact hσc
    · rw [d.parent_of_mem_newCells hσN]; exact d.edge_mem_cells
  parent_mem_faces := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hF)]
    exact hF
  sub_parent := fun _ _ h => d.sub_parent hS h
  cell_subset := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, hσe⟩ | hσN
    · rw [d.parent_of_mem_cells hσc, href.cell_eq hσc hσe]
    · rw [d.parent_of_mem_newCells hσN]; exact href.cell_subset_edge hσN

end SubdivData

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

/-! ### Assertion (vii) is preserved by an edge subdivision

"An edge subdivision changes no 2-cell." Literally: the 2-cells of `S.subdivideEdge d` are those
of `S`, and each is an old cell distinct from the subdivided edge, so `SubdivData.IsRefinement`
leaves its open cell exactly where it was. -/

namespace SubdivData

variable {d : S.SubdivData} {R : S.Realization} {R' : (S.subdivideEdge d).Realization} {F : γ}

theorem IsRefinement.cell_face_eq (href : d.IsRefinement R R') (hF : F ∈ S.faces) :
    R'.cell F = R.cell F :=
  href.cell_eq (S.mem_cells_of_mem_faces hF) (S.faces_ne_edgeSet hF d.edge_mem_edgeSet)

/-- **Assertion (vii) is preserved by an edge subdivision.** -/
theorem IsRefinement.isFaceJordan (href : d.IsRefinement R R') (hJ : R.IsFaceJordan) :
    R'.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.isJordanCurve hF
  cell_eq_inside := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.cell_eq_inside hF

/-- **The induction step over the first constructor**, in the shape a consumer building a
sequence of stages wants: one edge subdivision carries (i), (vii) and `Realization.Refines`
forward together. The mirror of `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan`.
-/
theorem IsRefinement.isCellDecomposition_and_isFaceJordan (hS : S.CombInvariants)
    (href : d.IsRefinement R R') {D : Set Plane} (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    R'.IsCellDecomposition D ∧ R'.IsFaceJordan ∧ R'.Refines R d.parent :=
  ⟨href.isCellDecomposition hS h, href.isFaceJordan hJ, href.refines hS⟩

/-! ### The orientation of the boundary-walk update

`CellStructure.subdivideEdge` now takes the replacement boundary lists from `SubdivData`.
`SubstWalk` is a relation rather than a function because the direction of a crossing is
determined by the walk and not by the edge list.  The data carries one corrected list for each
face together with the fact that it replaces a closed old boundary walk. -/

/-- On a stretch that never crosses the subdivided edge, the corrected replacement leaves the
edge list alone. -/
theorem SubstWalk.eq_of_notMem {d : S.SubdivData} {u : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (h : d.edge ∉ W) : W' = W := by
  induction hsub with
  | nil u => rfl
  | forward hs ih => exact absurd (List.mem_cons_self ..) h
  | backward hs ih => exact absurd (List.mem_cons_self ..) h
  | other hl hf hs ih => rw [ih fun hh => h (List.mem_cons_of_mem _ hh)]

end SubdivData

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

/-- A walk avoiding the subdivided edge visits exactly the same vertices in the subdivided
skeleton. -/
theorem walkVertices_eq_of_notMem {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v)
    (he : d.edge ∉ W) : d.skeleton.walkVertices u W = S.skel.walkVertices u W := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hl⟩
    · exact Graph.mem_walkVertices_self
    · rw [d.skeleton_isLink] at hl
      rcases hl with ⟨hl, -, -, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Graph.mem_walkVertices_of_mem_covered ⟨f, hf, y, hl⟩
      · exact (d.newEdge₁_notMem_edgeSet (h.edge_mem hf)).elim
      · exact (d.newEdge₂_notMem_edgeSet (h.edge_mem hf)).elim
  · intro z hz
    rcases Graph.mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, y, hl⟩
    · exact Graph.mem_walkVertices_self
    · apply Graph.mem_walkVertices_of_mem_covered
      refine ⟨f, hf, y, d.skeleton_isLink.2 (Or.inl ⟨hl, ?_, ?_, ?_⟩)⟩
      · exact fun hfe => he (hfe ▸ hf)
      · exact fun hfe => d.newEdge₁_notMem_edgeSet (hfe ▸ hl.edge_mem)
      · exact fun hfe => d.newEdge₂_notMem_edgeSet (hfe ▸ hl.edge_mem)

namespace SubstWalk

variable {d : S.SubdivData} {u v : γ} {W W' : List γ}

/-- Every old visited vertex is still visited after subdivision. -/
theorem old_walkVertices_subset (hsub : d.SubstWalk u W W') :
    S.skel.walkVertices u W ⊆ d.skeleton.walkVertices u W' := by
  induction hsub with
  | nil u => intro z hz; simpa only [Graph.walkVertices_nil] using hz
  | forward hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons d.isLink hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        exact Graph.mem_walkVertices_cons_of_mem hlink₁
          (Graph.mem_walkVertices_cons_of_mem hlink₂ (ih hz))
  | backward hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons d.isLink.symm hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        exact Graph.mem_walkVertices_cons_of_mem hlink₂
          (Graph.mem_walkVertices_cons_of_mem hlink₁ (ih hz))
  | other hl hf hs ih =>
      intro z hz
      rcases Graph.mem_walkVertices_cons hl hz with rfl | hz
      · exact Graph.mem_walkVertices_self
      · have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        exact Graph.mem_walkVertices_cons_of_mem hlink (ih hz)

/-- A subdivision introduces no visited vertex except the named subdivision vertex. -/
theorem new_walkVertices_subset (hsub : d.SubstWalk u W W') {z : γ}
    (hz : z ∈ d.skeleton.walkVertices u W') :
    z = d.newVertex ∨ z ∈ S.skel.walkVertices u W := by
  induction hsub with
  | nil u => exact Or.inr (by simpa only [Graph.walkVertices_nil] using hz)
  | forward hs ih =>
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rcases Graph.mem_walkVertices_cons hlink₁ hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases Graph.mem_walkVertices_cons hlink₂ hz with rfl | hz
        · exact Or.inl rfl
        · rcases ih hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (Graph.mem_walkVertices_cons_of_mem d.isLink hz)
  | backward hs ih =>
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      rcases Graph.mem_walkVertices_cons hlink₂ hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases Graph.mem_walkVertices_cons hlink₁ hz with rfl | hz
        · exact Or.inl rfl
        · rcases ih hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (Graph.mem_walkVertices_cons_of_mem d.isLink.symm hz)
  | other hl hf hs ih =>
      have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
        ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
          fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
      rcases Graph.mem_walkVertices_cons hlink hz with rfl | hz
      · exact Or.inr Graph.mem_walkVertices_self
      · rcases ih hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (Graph.mem_walkVertices_cons_of_mem hl hz)

/-- Replacing one edge of a simple path by its two subdivision edges preserves simplicity. -/
theorem isPath (hsub : d.SubstWalk u W W') (hP : S.skel.IsPath u W v) :
    d.skeleton.IsPath u W' v := by
  induction hsub generalizing v with
  | nil u =>
      cases hP with
      | nil hu =>
          exact .nil (by rw [d.skeleton_vertexSet]; exact Set.mem_insert_of_mem _ hu)
  | forward hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl hP hfresh =>
        have hw : d.right = w := d.isLink.right_unique hl
        subst w
        have heW : d.edge ∉ _ :=
          (List.nodup_cons.1 (Graph.IsPath.nodup (Graph.IsPath.cons hl hP hfresh))).1
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs heW
        rw [hEq] at ih ⊢
        have htail := ih hP
        have hverts := d.walkVertices_eq_of_notMem hP.isWalk heW
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        refine .cons hlink₁ (.cons hlink₂ htail ?_) ?_
        · intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (hP.isWalk.walkVertices_subset hz))
        · intro hz
          rcases Graph.mem_walkVertices_cons hlink₂ hz with hEq | hz
          · exact d.newVertex_notMem (hEq ▸ d.left_mem_cells)
          · apply hfresh
            rw [← hverts]
            exact hz
  | backward hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl hP hfresh =>
        have hw : d.left = w := d.isLink.symm.right_unique hl
        subst w
        have heW : d.edge ∉ _ :=
          (List.nodup_cons.1 (Graph.IsPath.nodup (Graph.IsPath.cons hl hP hfresh))).1
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs heW
        rw [hEq] at ih ⊢
        have htail := ih hP
        have hverts := d.walkVertices_eq_of_notMem hP.isWalk heW
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        refine .cons hlink₂ (.cons hlink₁ htail ?_) ?_
        · intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (hP.isWalk.walkVertices_subset hz))
        · intro hz
          rcases Graph.mem_walkVertices_cons hlink₁ hz with hEq | hz
          · exact d.newVertex_notMem (hEq ▸ d.right_mem_cells)
          · apply hfresh
            rw [← hverts]
            exact hz
  | other hl hf hs ih =>
      cases hP with
      | @cons _ w _ _ _ hl' hP hfresh =>
        have hw : _ = w := hl.right_unique hl'
        subst w
        have htail := ih hP
        have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hf, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        refine .cons hlink htail ?_
        intro hz
        rcases SubdivData.SubstWalk.new_walkVertices_subset hs hz with hEq | hz
        · exact d.newVertex_notMem
            (hEq ▸ S.mem_cells_of_mem_vertexSet hl.left_mem)
        · exact hfresh hz

/-- Every output edge is either one of the two replacement edges or an old input edge. -/
theorem mem_input_of_mem_output (hsub : d.SubstWalk u W W') {x : γ} (hx : x ∈ W') :
    x = d.newEdge₁ ∨ x = d.newEdge₂ ∨ x ∈ W := by
  induction hsub with
  | nil => simp at hx
  | forward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]
  | backward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]
  | other hl hne hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (Or.inr (List.mem_cons_self ..))
      · rcases ih hx with h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (List.mem_cons_of_mem _ h))]

/-- Every surviving old input edge occurs in the output. -/
theorem mem_output_of_mem_input_of_ne (hsub : d.SubstWalk u W W') {x : γ}
    (hx : x ∈ W) (hne : x ≠ d.edge) : x ∈ W' := by
  induction hsub with
  | nil => simp at hx
  | forward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with h | hx
      · exact absurd h hne
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hx))
  | backward hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with h | hx
      · exact absurd h hne
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hx))
  | other hl hfe hs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx)

/-- The removed edge name never occurs in the replacement list. -/
theorem edge_notMem_output (hsub : d.SubstWalk u W W') : d.edge ∉ W' := by
  intro he
  induction hsub with
  | nil => simp at he
  | forward hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | h | he
      · exact d.newEdge₁_notMem (h ▸ d.edge_mem_cells)
      · exact d.newEdge₂_notMem (h ▸ d.edge_mem_cells)
      · exact ih he
  | backward hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | h | he
      · exact d.newEdge₂_notMem (h ▸ d.edge_mem_cells)
      · exact d.newEdge₁_notMem (h ▸ d.edge_mem_cells)
      · exact ih he
  | other hl hne hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | he
      · exact hne h.symm
      · exact ih he

/-- If the old walk crosses the subdivided edge, all three replacement cells occur in the
new path carrier. -/
theorem newCells_subset_pathCells (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    d.newCells ⊆ (S.subdivideEdge d).pathCells u W' := by
  induction hsub with
  | nil => simp at he
  | forward hs ih =>
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inr (Graph.mem_walkVertices_cons_of_mem
          (d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))) Graph.mem_walkVertices_self)
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  | backward hs ih =>
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inr (Graph.mem_walkVertices_cons_of_mem
          (d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩)))
          Graph.mem_walkVertices_self)
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact Or.inl (List.mem_cons_self ..)
  | other hl hne hs ih =>
      simp only [List.mem_cons] at he
      rcases he with h | he
      · exact absurd h.symm hne
      · intro z hz
        rcases ih he hz with hz | hz
        · exact Or.inl (List.mem_cons_of_mem _ hz)
        · have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
            ⟨hl, hne, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
              fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
          exact Or.inr (Graph.mem_walkVertices_cons_of_mem hlink hz)

/-- The exact cell-carrier update performed by an orientation-aware subdivision. -/
theorem pathCells_eq (hsub : d.SubstWalk u W W') (hW : S.skel.IsWalk u W v) :
    (S.subdivideEdge d).pathCells u W' =
      {z | (z ∈ S.pathCells u W ∧ z ≠ d.edge) ∨
        (d.edge ∈ W ∧ z ∈ d.newCells)} := by
  ext z
  by_cases he : d.edge ∈ W
  · constructor
    · rintro (hzOut | hz)
      · rcases hsub.mem_input_of_mem_output hzOut with rfl | rfl | hz
        · exact Or.inr ⟨he, Or.inr (Or.inl rfl)⟩
        · exact Or.inr ⟨he, Or.inr (Or.inr rfl)⟩
        · exact Or.inl ⟨Or.inl hz, fun h => hsub.edge_notMem_output (h ▸ hzOut)⟩
      · rcases hsub.new_walkVertices_subset hz with rfl | hz
        · exact Or.inr ⟨he, Or.inl rfl⟩
        · exact Or.inl ⟨Or.inr hz, fun h => Set.disjoint_left.1
            S.disjoint_vertexSet_edgeSet (hW.walkVertices_subset hz) (h ▸ d.edge_mem_edgeSet)⟩
    · rintro (⟨hz, hze⟩ | ⟨-, hz⟩)
      · rcases hz with hz | hz
        · exact Or.inl (hsub.mem_output_of_mem_input_of_ne hz hze)
        · exact Or.inr (hsub.old_walkVertices_subset hz)
      · exact hsub.newCells_subset_pathCells he hz
  · have hEq := SubdivData.SubstWalk.eq_of_notMem hsub he
    have hvertices := d.walkVertices_eq_of_notMem hW he
    constructor
    · rintro (hz | hz)
      · refine Or.inl ⟨Or.inl ?_, ?_⟩
        · rwa [hEq] at hz
        · intro h
          subst z
          exact hsub.edge_notMem_output hz
      · refine Or.inl ⟨Or.inr ?_, ?_⟩
        · rw [subdivideEdge_skel, hEq, hvertices] at hz
          exact hz
        · intro h
          subst z
          rw [subdivideEdge_skel, hEq, hvertices] at hz
          exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet
            (hW.walkVertices_subset hz) d.edge_mem_edgeSet
    · rintro (⟨hz, -⟩ | ⟨h, -⟩)
      · rcases hz with hz | hz
        · exact Or.inl (hEq.symm ▸ hz)
        · exact Or.inr (by
            rw [subdivideEdge_skel, hEq, hvertices]
            exact hz)
      · exact absurd h he

/-- Substituting an edge in a cyclic boundary list produces another presentation of a simple
cycle, regardless of which admissible start vertex the boundary data selected. -/
theorem exists_isCycleThrough {e a b : γ} {D : List γ}
    (hsub : d.SubstWalk u (e :: D) W') (hW : S.skel.IsWalk u (e :: D) u)
    (hc : S.skel.IsCycleThrough e a b D) :
    ∃ e' a' D', W' = e' :: D' ∧ d.skeleton.IsCycleThrough e' a' u D' := by
  cases hsub with
  | forward hs =>
      cases hW with
      | @cons _ w _ _ _ hl htail =>
        have hw : d.right = w := d.isLink.right_unique hl
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs hc.notMem
        rw [hEq] at htail'
        have hverts := d.walkVertices_eq_of_notMem htailP.isWalk hc.notMem
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        have hfresh : d.newVertex ∉ d.skeleton.walkVertices d.right D := by
          intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (htailP.isWalk.walkVertices_subset hz))
        have hpath : d.skeleton.IsPath d.newVertex (d.newEdge₂ :: D) d.left :=
          .cons hlink₂ htail' hfresh
        have hnot : d.newEdge₁ ∉ d.newEdge₂ :: D := by
          intro hz
          rcases List.mem_cons.1 hz with hz | hz
          · exact d.newEdge_ne hz
          · exact d.newEdge₁_notMem_edgeSet (htailP.edge_mem hz)
        exact ⟨d.newEdge₁, d.newVertex, d.newEdge₂ :: D, by rw [hEq],
          hlink₁.symm, hpath, hnot⟩
  | backward hs =>
      cases hW with
      | @cons _ w _ _ _ hl htail =>
        have hw : d.left = w := d.isLink.symm.right_unique hl
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hEq := SubdivData.SubstWalk.eq_of_notMem hs hc.notMem
        rw [hEq] at htail'
        have hverts := d.walkVertices_eq_of_notMem htailP.isWalk hc.notMem
        have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
          d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
        have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
          d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
        have hfresh : d.newVertex ∉ d.skeleton.walkVertices d.left D := by
          intro hz
          rw [hverts] at hz
          exact d.newVertex_notMem
            (S.mem_cells_of_mem_vertexSet (htailP.isWalk.walkVertices_subset hz))
        have hpath : d.skeleton.IsPath d.newVertex (d.newEdge₁ :: D) d.right :=
          .cons hlink₁ htail' hfresh
        have hnot : d.newEdge₂ ∉ d.newEdge₁ :: D := by
          intro hz
          rcases List.mem_cons.1 hz with hz | hz
          · exact d.newEdge_ne hz.symm
          · exact d.newEdge₂_notMem_edgeSet (htailP.edge_mem hz)
        exact ⟨d.newEdge₂, d.newVertex, d.newEdge₁ :: D, by rw [hEq],
          hlink₂.symm, hpath, hnot⟩
  | other hl hne hs =>
      cases hW with
      | @cons _ w _ _ _ hl' htail =>
        have hw : _ = w := hl.right_unique hl'
        subst w
        have htailP := SubdivData.isPath_of_isWalk_of_isPath hc.isPath htail
        have htail' := SubdivData.SubstWalk.isPath hs htailP
        have hlink : d.skeleton.IsLink _ _ _ := d.skeleton_isLink.2 (Or.inl
          ⟨hl, hne, fun h => d.newEdge₁_notMem_edgeSet (h ▸ hl.edge_mem),
            fun h => d.newEdge₂_notMem_edgeSet (h ▸ hl.edge_mem)⟩)
        refine ⟨e, _, _, rfl, hlink.symm, htail', ?_⟩
        show e ∉ _
        intro he
        rcases SubdivData.SubstWalk.mem_input_of_mem_output hs he with h | h | h
        · exact d.newEdge₁_notMem (h ▸ S.mem_cells_of_mem_edgeSet hl.edge_mem)
        · exact d.newEdge₂_notMem (h ▸ S.mem_cells_of_mem_edgeSet hl.edge_mem)
        · exact hc.notMem h

end SubstWalk

end SubdivData

/-! ### The invariant at every generated stage -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.mem_vertexSet_induce_component
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

/-- Edge relabelling preserves 2-connectivity, including connectedness after deleting any one
vertex. -/
theorem IsTwoConnected.relabelEdges (h : G.IsTwoConnected) (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).IsTwoConnected where
  hasThreeVertices := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h.hasThreeVertices
    exact ⟨a, by simpa, b, by simpa, c, by simpa, hab, hac, hbc⟩
  connected := h.connected.relabelEdges hf
  deleteVerts_connected := by
    intro x hx
    have hxG : x ∈ V(G) := by simpa using hx
    have hdel := h.deleteVerts_connected hxG
    constructor
    · simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hdel.nonempty
    · intro u hu v hv
      have huG : u ∈ V(G.deleteVerts {x}) := by
        simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hu
      have hvG : v ∈ V(G.deleteVerts {x}) := by
        simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hv
      obtain ⟨W, hW⟩ := hdel.reaches huG hvG
      exact ⟨W.map f, hW.relabelEdges_deleteVerts hf⟩

/-! ### Relabelling a drawing -/

end Graph
end

section
-- module Solutions.Q146_CD.MatchedArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
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

/-! ## Matching two named arcs -/

/-- Any two named arcs admit an endpoint-preserving homeomorphism. -/
theorem exists_arcHomeo {A B : Set Plane} {a b c d : Plane}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B c d) :
    Nonempty (ArcHomeo A B a b c d) := by
  classical
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  let fi : Plane → ℝ := Function.invFunOn f I
  let gi : Plane → ℝ := Function.invFunOn g I
  let toFun : Plane → Plane := g ∘ fi
  let invFun : Plane → Plane := f ∘ gi
  have hfiC : ContinuousOn fi A := by
    rw [← hfim]
    exact continuousOn_invFunOn_image' isCompact_I hfc hfi
  have hgiC : ContinuousOn gi B := by
    rw [← hgim]
    exact continuousOn_invFunOn_image' isCompact_I hgc hgi
  have hfiMap : MapsTo fi A I := by
    rw [← hfim]
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn f I (f t) ∈ I
    rw [hfi.leftInvOn_invFunOn ht]
    exact ht
  have hgiMap : MapsTo gi B I := by
    rw [← hgim]
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn g I (g t) ∈ I
    rw [hgi.leftInvOn_invFunOn ht]
    exact ht
  refine ⟨{
    toFun := toFun
    invFun := invFun
    continuousOn_toFun := hgc.comp hfiC hfiMap
    continuousOn_invFun := hfc.comp hgiC hgiMap
    leftInvOn := ?_
    rightInvOn := ?_
    image_eq := ?_
    map_left := ?_
    map_right := ?_
  }⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hfim ▸ hx
    simp [toFun, invFun, fi, gi, hfi.leftInvOn_invFunOn ht,
      hgi.leftInvOn_invFunOn ht]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hgim ▸ hy
    simp [toFun, invFun, fi, gi, hgi.leftInvOn_invFunOn ht,
      hfi.leftInvOn_invFunOn ht]
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hgim ▸ Set.mem_image_of_mem g (hfiMap hx)
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hgim ▸ hy
      refine ⟨f t, hfim ▸ Set.mem_image_of_mem f ht, ?_⟩
      simp [toFun, fi, hfi.leftInvOn_invFunOn ht]
  · rw [← hf0, ← hg0]
    simp [toFun, fi, hfi.leftInvOn_invFunOn zero_mem_I]
  · rw [← hf1, ← hg1]
    simp [toFun, fi, hfi.leftInvOn_invFunOn one_mem_I]

/-! ## Transporting a plane drawing along an arc homeomorphism -/

end Schoenflies

open Schoenflies

namespace Graph

variable {β : Type*} {A B : Set Plane} {a b c d : Plane} {G : Graph Plane β}
  {drawing : β → ℝ → Plane}

theorem pointSet_map_mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) :
    pointSet (G.map m.toFun) (mapDrawing m drawing) = m.toFun '' pointSet G drawing := by
  rw [pointSet, pointSet, Graph.vertexSet_map, Graph.edgeSet_map, Set.image_union,
    Set.image_iUnion₂]
  congr 1
  exact Set.iUnion₂_congr fun e _ => edgeArc_mapDrawing m e

end Graph
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

/-! ## The chosen homeomorphism between the two drawn ears -/

/-! ## The transported map -/

variable {R₁ R₂ : S.Realization} {earPos₁ earPos₂ : γ → Plane}
  {earDraw₁ earDraw₂ : γ → ℝ → Plane}

variable {g : SkeletonHomeo R₁ R₂} {m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂}

variable (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)

include hE₁ hE₂

/-! ## The skeleton homeomorphism across the split -/

/-- **The transported map agrees with `g` on the whole old realized skeleton.**

This is the field `Schoenflies.StageSequence.skelHomeo_succ` at a 2-cell split step: consecutive
skeleton maps agree wherever both are defined. It holds by definition, which is the point of
building the map by extension rather than by rebuilding. -/
theorem splitHomeo_eqOn :
    EqOn (splitHomeo g hE₁ hE₂ m).toFun g.toFun R₁.skeletonSet :=
  splitMap_eqOn_skeletonSet

end SplitData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.SkeletonLocal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Local structure of a polygonal skeleton

Close enough to any of its points, a finite union of segments and points looks like a *star*:
the point itself together with finitely many radial segments leaving it, one per local branch.
This module proves that, and hands the accessibility argument the form it needs.

## What is exported, and why in this shape

The data is `Schoenflies.localDirs S x`, the set of unit vectors `d` such that some initial
segment `[x, x + ε • d]` lies in `S`. It is defined for an arbitrary set, with no choices in
it: nothing about a segment decomposition of `S` enters the definition, so no consumer has to
carry one. "Pairwise distinct directions" is then not a clause to be proved but the meaning of
the word *set*, and the blueprint's real content becomes `localDirs_finite`.

The radius is the one genuinely existential ingredient — there is no canonical `r₀` — so it is
named by a predicate rather than returned inside an `∃`-packaged bundle of properties:

  `Schoenflies.IsLocalRadius S x r` : `0 < r`, and every point within `r` of `x` lies in `S`
  exactly when it is `x` itself or leaves `x` in a local direction.

That single membership criterion is equivalent to the blueprint's picture and implies all of
its parts, each proved here as a lemma about `IsLocalRadius` and hence available at every
radius below the one produced: the closed-disk formula
(`IsLocalRadius.closedBall_inter`), the open disk minus `S` as a *cone* over the complement of
the local rays (`IsLocalRadius.ball_diff_eq_cone`), and the star-shapedness that the
accessibility lemma actually cites (`IsLocalRadius.openSegment_subset_ball_diff`).

## What the consumer (`lem:polygonal-side-accessibility`) needs

That lemma takes `y` in a face `F` inside the disk, and wants a polygonal arc from `x` into
`F`. `IsLocalRadius.openSegment_subset_ball_diff` gives `(x, y) ⊆ B(x, r) \ S` directly, and
`openSegment ℝ x y ∪ {y}` is connected and disjoint from the skeleton — which is everything
the blueprint's "pick the sector containing `y`, then a short segment from `x` into it" is used
for. The decomposition of the punctured disk into its *individual* sectors, one per pair of
cyclically adjacent local directions, is therefore **not** proved here: it needs a cyclic
order on directions, and no consumer needs it. `IsLocalRadius.ball_diff_eq_cone` records the
sectors in aggregate — as one `Plane.cone` over all free directions at once.

## Blueprint

* `Schoenflies.localDirs`, `Schoenflies.localDirs_finite` — the finitely many local branch
  directions at `x` of Lemma "Local structure of a polygonal skeleton"
  (`lem:local-skeleton-structure`).
* `Schoenflies.IsLocalRadius`, `Schoenflies.exists_isLocalRadius`,
  `Schoenflies.IsLocalRadius.closedBall_inter` — the radius `r₀`, and "for every `0 < r ≤ r₀`
  the closed disk meets `|G|` exactly in finitely many straight segments from `x` with
  pairwise distinct directions" (same lemma).
* `Schoenflies.IsLocalRadius.ball_diff_eq_cone` — "consequently `B(x,r) \ |G|` is a finite
  union of open circular sectors" (same lemma), in aggregate form.
* `Schoenflies.IsLocalRadius.openSegment_subset_ball_diff` — the form
  `lem:polygonal-side-accessibility` cites: a short straight segment from `x` towards any
  point of the punctured disk misses the skeleton.
* `Graph.IsDrawing.exists_cover`, `Graph.IsDrawing.exists_isLocalRadius`,
  `Graph.IsDrawing.finite_localDirs` — the same statements for a finite plane graph all of
  whose edges are polygonal.
* `Graph.IsDrawing.openSegment_subset_face` — the access arc of
  `lem:polygonal-side-accessibility`, assembled: a straight segment from `x` to a point of the
  exterior inside a local disk lies, minus `x`, in that point's face.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {S T F : Set Plane} {ps : List Piece} {x y z c d : Plane} {r R ε t : ℝ}

/-! ### Radial segments

`segment ℝ x (x + r • d)` with `d` a unit vector is the closed radius of length `r` leaving
`x` in the direction `d`. Two facts run the whole module: a point lies on it exactly when it
is near enough and points the right way (`mem_radial_iff`), and cutting a longer radius by a
smaller ball leaves the shorter radius (`radial_inter_closedBall`). -/

/-! ### The local directions of a set -/

/-! ### The pieces through a point

Everything is now bookkeeping over a finite list of segments and a finite set of stray points.
`GoodRadius x P r` collects what a radius must avoid on account of one piece: pieces missing
`x` must stay outside the disk, and pieces through `x` must not end inside it. -/

/-! ### The membership criterion -/

theorem IsLocalRadius.pos (h : IsLocalRadius S x r) : 0 < r := h.1

theorem IsLocalRadius.mono (h : IsLocalRadius S x r) (hε : 0 < ε) (hle : ε ≤ r) :
    IsLocalRadius S x ε :=
  ⟨hε, fun z hz => h.2 z (hz.trans hle)⟩

/-! ### A local radius exists

The construction: choose a radius good for every piece and strictly below the distance to
every stray point other than `x`. -/

/-! ### What a local radius gives -/

/-- **The punctured disk is star-shaped about `x`.** This is the form
`lem:polygonal-side-accessibility` cites: a straight segment from `x` towards any point of the
disk that misses `S` misses `S` all the way.

Together with connectedness of `openSegment ℝ x y ∪ {y}` it replaces the blueprint's "pick the
sector containing `y`, then a short segment from `x` into it". -/
theorem IsLocalRadius.openSegment_subset_ball_diff (h : IsLocalRadius S x r) (hy : y ∈ ball x r)
    (hyS : y ∉ S) : openSegment ℝ x y ⊆ ball x r \ S := by
  have hyx : y ≠ x := fun hxy => hyS ((h.2 y (by rw [hxy, dist_self]; exact h.pos.le)).2
    (Or.inl hxy))
  have hdy : Plane.dir (y - x) ∉ localDirs S x := fun hd =>
    hyS ((h.2 y (mem_ball.1 hy).le).2 (Or.inr hd))
  intro w hw
  rw [openSegment_eq_image'] at hw
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw
  have hsub : x + θ • (y - x) - x = θ • (y - x) := by module
  have hne : y - x ≠ 0 := sub_ne_zero.2 hyx
  have hdist : dist (x + θ • (y - x)) x = θ * dist y x := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0, dist_eq_norm]
  have hlt : dist (x + θ • (y - x)) x < r := by
    rw [hdist]
    calc θ * dist y x ≤ 1 * dist y x := by
          have : 0 ≤ dist y x := dist_nonneg
          nlinarith
      _ = dist y x := one_mul _
      _ < r := mem_ball.1 hy
  refine ⟨mem_ball.2 hlt, fun hmem => ?_⟩
  -- The point points in the same direction as `y`, which is not a local direction.
  have hdir : Plane.dir (x + θ • (y - x) - x) = Plane.dir (y - x) := by
    rw [hsub, dir_smul_pos hθ0]
  rcases (h.2 _ hlt.le).1 hmem with hzx | hd
  · -- The point is `x`, so `θ • (y - x) = 0`, impossible.
    have : θ • (y - x) = 0 := by
      have := sub_eq_zero.2 hzx
      rwa [hsub] at this
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' hθ0.ne'
    · exact hne h'
  · exact hdy (hdir ▸ hd)

end Schoenflies

/-! ### Finite polygonal plane graphs -/
end

section
-- module Solutions.Q146_CD.SkeletonAccess
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sector decomposition at every point, and polygonal-side accessibility

Two things are done here. First, the last clause of Lemma "Local structure of a polygonal
skeleton" (`lem:local-skeleton-structure`) is closed: `Schoenflies/SkeletonSectors.lean` proves
it only at a point with **at least two** local branches, and the blueprint states it for every
point. Second, its consumer, Lemma "Polygonal-side accessibility"
(`lem:polygonal-side-accessibility`), is proved.

## 1. The two degenerate points

`Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone` writes the punctured local disk as the
union of the sectors `Plane.cone x (Plane.arcCCW d w) r` between *consecutive* local directions
`d, w`. With fewer than two local directions there is no consecutive pair, and the two missing
configurations are genuinely different sets:

* **one** local direction `d` — the disk slit along the radius in direction `d`, a sector of
  full turn (`Schoenflies.IsLocalRadius.ball_diff_eq_slit`);
* **no** local direction — the punctured disk, `x` being an isolated point of the skeleton
  (`Schoenflies.IsLocalRadius.ball_diff_eq_punctured`).

Both are connected (`Schoenflies.isConnected_ball_diff_radial`,
`Schoenflies.isConnected_ball_diff_singleton`), which is everything the decomposition claims
about a sector, so the blueprint's clause holds at every point with a single sector. Both proofs
cut the set into convex pieces cut out by the sign of `Plane.det` and glue them along explicit
overlaps: no angle, no arctangent, no cyclic order.

The sectors are then named, for every point at once, as what
`Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone` already proves them to be — the
connected components of the punctured disk:

  `Schoenflies.localSectors S x r : Set (Set Plane)`

with `Schoenflies.localSectors_finite`, `Schoenflies.sUnion_localSectors`,
`Schoenflies.localSectors_pairwiseDisjoint`, `Schoenflies.isOpen_of_mem_localSectors` and
`Schoenflies.isConnected_of_mem_localSectors`. In the generic case the members are exactly the
cones (`Schoenflies.cone_mem_localSectors`); in the degenerate cases there is exactly one
member (`Schoenflies.localSectors_eq_of_subsingleton`). A set of sets rather than an indexed
family, because the natural index — a consecutive pair of local directions — does not exist at
the two degenerate points.

## 2. Polygonal-side accessibility

`Graph.exists_access_segment` is the theorem, and it exports the *construction*: a point `y` of
the 2-cell `F`, as close to `x` as prescribed, whose straight segment from `x` lies in `F` apart
from `x` itself. `Graph.polygonal_side_accessibility` packages it as
`Schoenflies.PolyAccessible F x`. The length bound is not in the blueprint statement; the
shrinking-star arguments downstream need it, and it is free.

The blueprint's proof is followed step by step. Shrink the disk at `x` below the distance to the
compact wild curve `C` (`lem:compact-separation`(c)), so that inside it the whole skeleton
`K = |G| ∪ C` is just `|G|`; the punctured disk is then the union of the sectors; the sector
containing `y` is connected and misses `K`, so it lies in a single 2-cell, and that cell is `F`
because the sector meets `F` at `y` (`Graph.localSector_subset_cell` — this is the clause the
audit found missing from `Graph.exists_access_sector`); the straight segment from `x` to `y`
lies in that sector
(`Schoenflies.IsLocalRadius.openSegment_subset_connectedComponentIn`).

The case `x ∉ |G|` — not excluded by the statement, since `x` need only lie on the boundary of
`F` — is the degenerate configuration of part 1: the disk misses the skeleton entirely, is
itself the only sector, and `x` turns out to lie in `F`.

The sector is taken throughout as the connected component of `y` in the punctured disk, so the
*number* of local branches at `x` never enters the accessibility proof. Part 1 is what makes
that component a sector in the blueprint's sense — at a point with one branch or none there is
no consecutive pair of local directions to name it by, and the component is the whole punctured
disk.

## The one hypothesis

`Schoenflies.CellsAbsorb K cells` is `lem:cellulation-invariants`(i), *a connected set disjoint
from the skeleton lies in a single open 2-cell*, in the "meets, hence contained" reading. It is
the only thing assumed; two dischargers are supplied
(`Schoenflies.cellsAbsorb_of_isComponent`, `Schoenflies.cellsAbsorb_of_isComponent_in`), the
second of which covers the target side, where the 2-cells only fill an ambient region `Q` whose
frontier belongs to the skeleton.

## The target side

`Graph.polygonal_side_accessibility_target` and `Graph.polygonal_side_accessibility_square`.
The blueprint keeps a sector from leaking out of the square by applying `thm:polygonal-jordan`
to the square boundary; that is not needed here. The corresponding step is
`Schoenflies.subset_of_isPreconnected_of_frontier_disjoint` — a connected set missing the
frontier of an open set and meeting it lies inside it — together with
`Schoenflies.frontier_openSquare_subset`. Both are elementary, so the target side rests on
nothing beyond the shared hypothesis.

## Blueprint

* `Schoenflies.isConnected_ball_diff_radial`, `Schoenflies.isConnected_ball_diff_singleton`,
  `Schoenflies.IsLocalRadius.ball_diff_eq_slit`,
  `Schoenflies.IsLocalRadius.ball_diff_eq_punctured`,
  `Schoenflies.IsLocalRadius.isConnected_ball_diff_of_subsingleton` — "consequently
  `B(x,r) \ |G|` is a finite union of open circular sectors" of `lem:local-skeleton-structure`,
  at the two points where `Schoenflies/SkeletonSectors.lean` leaves it open.
* `Schoenflies.localSectors` and its API, `Graph.IsDrawing.localSectors_finite`,
  `Graph.IsDrawing.isOpen_of_mem_localSectors` — the same clause for a finite
  plane graph with polygonal edges.
* `Schoenflies.localDirs_union_of_disjoint`, `Schoenflies.IsLocalRadius.union_of_disjoint`,
  `Graph.IsDrawing.exists_isLocalRadius_union` — "shrink the disk at `x` until it also misses
  the compact set `C`; the disk then meets the whole skeleton in the finitely many radial
  segments" of `lem:polygonal-side-accessibility`.
* `Schoenflies.CellsAbsorb`, `Schoenflies.cellsAbsorb_of_isComponent`,
  `Schoenflies.cellsAbsorb_of_isComponent_in` — `lem:cellulation-invariants`(i), assumed, and
  the two ways a cellulation discharges it.
* `Graph.localSector_subset_face`, `Graph.localSector_subset_cell`,
  `Schoenflies.IsLocalRadius.openSegment_subset_connectedComponentIn` — "each sector is
  connected and disjoint from the skeleton, so … lies in a single open 2-cell; and at least one
  sector lies in `F` … a short straight segment from `x` into that sector is a polygonal access
  arc" of `lem:polygonal-side-accessibility`.
* `Graph.exists_access_segment`, `Graph.polygonal_side_accessibility` —
  `lem:polygonal-side-accessibility`, source side.
* `Graph.polygonal_side_accessibility_target`, `Graph.polygonal_side_accessibility_square`,
  `Schoenflies.subset_of_isPreconnected_of_frontier_disjoint`,
  `Schoenflies.frontier_openSquare_subset` — "the analogous assertion holds at every boundary
  point of a target face" of the same lemma.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {S F Q K N : Set Plane} {x y z d : Plane} {r ε : ℝ}

/-! ### Bilinearity conveniences -/

/-! ### Two ways to miss a radius

A point of the disk fails to lie on the radius at `x` in direction `d` for one of two reasons:
it is off the line of `d` altogether, or it is on that line but on the far side. Both are sign
conditions on `Plane.det`, and both are used three times below. -/

/-! ### The disk minus one radius, and the punctured disk

`Schoenflies/SkeletonSectors.lean` decomposes the punctured local disk into the open sectors
between *consecutive* local directions, and that decomposition says nothing when there are fewer
than two directions to be consecutive. The two missing configurations are settled here: with one
local direction the punctured disk is the disk slit along a single radius, and with none it is
the punctured disk itself. Both are connected, which is everything the decomposition claims
about a sector, so the blueprint's clause holds at every point with the number of sectors equal
to one. -/

/-! ### The degenerate local disks

With `Schoenflies.isConnected_ball_diff_radial` and
`Schoenflies.isConnected_ball_diff_singleton` in hand, the two configurations that
`Schoenflies/SkeletonSectors.lean` had to exclude are read off the membership criterion. -/

/-! ### Adding a set the disk misses

The blueprint's "shrink the disk at `x` until it also misses the compact set `C`; the disk then
meets the *whole* skeleton in the finitely many radial segments". Once the disk is clear of `C`,
neither the membership criterion nor the set of local directions can tell `S` from `S ∪ C`. -/

/-! ### The sectors of a local disk, at every point

The blueprint's "`B(x,r) \ |G|` is a finite union of open circular sectors" is delivered here
without the two-branch hypothesis, by naming the sectors as what they are proved to be in
`Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone`: the connected components of the
punctured disk. With at least two branches each component *is* one of the cones
(`Schoenflies.cone_mem_localSectors`); with fewer there is exactly one component, the whole
punctured disk (`Schoenflies.localSectors_eq_of_subsingleton`). -/

/-- **The access sector, with no hypothesis on the number of branches.** The straight segment
from `x` to a point `y` of the punctured disk lies in `y`'s own sector, so the sector is reached
from `x` without leaving it.

The sector is named — it is `connectedComponentIn (ball x r \ S) y`, a member of
`Schoenflies.localSectors` by `Schoenflies.mem_localSectors` — rather than packaged in an `∃`,
so a consumer can speak about it before producing it. -/
theorem IsLocalRadius.openSegment_subset_connectedComponentIn (h : IsLocalRadius S x r)
    (hy : y ∈ ball x r) (hyS : y ∉ S) :
    openSegment ℝ x y ⊆ connectedComponentIn (ball x r \ S) y := by
  -- The half-open segment `(x, y]` is connected, contains `y`, and misses `S`.
  have hTsub : AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 ⊆ ball x r \ S := by
    rintro w ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    rcases eq_or_lt_of_le hθ1 with rfl | hlt
    · rw [AffineMap.lineMap_apply_one]; exact ⟨hy, hyS⟩
    · exact h.openSegment_subset_ball_diff hy hyS
        (by rw [openSegment_eq_image_lineMap]; exact ⟨θ, ⟨hθ0, hlt⟩, rfl⟩)
  have hconn : IsPreconnected (AffineMap.lineMap x y '' Ioc (0 : ℝ) 1) :=
    ((convex_Ioc (0 : ℝ) 1).affine_image (AffineMap.lineMap x y)).isPreconnected
  have hyT : y ∈ AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 :=
    ⟨1, ⟨zero_lt_one, le_refl 1⟩, AffineMap.lineMap_apply_one x y⟩
  refine subset_trans ?_ (hconn.subset_connectedComponentIn hyT hTsub)
  rw [openSegment_eq_image_lineMap]
  exact Set.image_mono Ioo_subset_Ioc_self

/-! ### `lem:cellulation-invariants`(i), as a hypothesis

The only thing assumed in this module. It is *not* a restatement of the goal: it speaks about
the cells of a cellulation, an object that has no Lean definition yet, and it is exactly the
invariant that another module is proving by induction over the two elementary operations. -/

/-- The frontier of an open axis-parallel square lies in the square's boundary. This is how the
hypothesis "the boundary of `Q` is part of the skeleton" is checked on the target side. -/
theorem frontier_openSquare_subset (c : Plane) (s : ℝ) :
    frontier (Plane.openSquare c s) ⊆ Plane.closedSquare c s \ Plane.openSquare c s := by
  have hsub : Plane.openSquare c s ⊆ Plane.closedSquare c s := by
    intro w hw
    simp only [Plane.openSquare, mem_setOf_eq] at hw
    simp only [Plane.closedSquare, mem_setOf_eq]
    exact hw.le
  rw [(Plane.isOpen_openSquare c s).frontier_eq]
  exact Set.sdiff_subset_sdiff_left
    ((Plane.isClosed_closedSquare c s).closure_subset_iff.2 hsub)

end Schoenflies

/-! ## `lem:polygonal-side-accessibility` -/

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {C F K Q : Set Plane} {cells : Set (Set Plane)} {x y : Plane} {r ε : ℝ}

/-! ### The sector decomposition for a finite polygonal plane graph

`lem:local-skeleton-structure`'s last clause, "consequently `B(x,r) \ |G|` is a finite union of
open circular sectors", now holds at *every* point of `|G|`: at a point with at least two local
branches the sectors are the cones of `Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone`, and
at the two degenerate points there is a single one. -/

/-- **The access segment of `lem:polygonal-side-accessibility`, with a prescribed length
bound.** Let `G` be a finite plane graph with polygonal edges, `C` a compact set — the wild
outer curve — and `K = |G| ∪ C` the whole skeleton. Let `F` be an open 2-cell, and `x` a point
at which `F` accumulates, lying off `C`. Then arbitrarily near `x` there is a point `y` of `F`
whose straight segment from `x` lies, apart from `x` itself, inside `F`.

The straight segment is exported rather than the accessibility predicate, because the later
shrinking-star arguments need the access arc to be short; `PolyAccessible` follows in
`Graph.polygonal_side_accessibility`.

The proof is the blueprint's. Shrink the disk at `x` below the distance to `C`, so that inside
it the whole skeleton is `|G|`; then the punctured disk is the union of the sectors of
`Schoenflies.localSectors`, each of them connected and disjoint from the skeleton, and the one
containing `y` lies in a single 2-cell by the assumed `lem:cellulation-invariants`(i). That cell
is `F`, because the sector meets `F` at `y`. When `x` is not on `|G|` at all — which the
statement does not exclude, since `x` need only be a limit of points of `F` — the disk misses
the skeleton entirely and is itself the access region.

The sector is named as the connected component of `y` in the punctured disk, so no hypothesis
on the number of local branches at `x` is needed anywhere. -/
theorem exists_access_segment [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hC : IsCompact C) (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells) (hFK : Disjoint F K)
    (hx : x ∈ closure F) (hxC : x ∉ C) (hε : 0 < ε) :
    ∃ y, y ∈ F ∧ y ≠ x ∧ dist y x < ε ∧ openSegment ℝ x y ⊆ F := by
  -- A disk about `x` missing the wild curve (`lem:compact-separation`(c)).
  obtain ⟨ρ, hρ, hballC⟩ :=
    Schoenflies.Plane.exists_ball_subset_diff isOpen_univ hC ⟨mem_univ x, hxC⟩
  by_cases hxP : x ∈ pointSet G drawing
  · -- `x` is on the polygonal skeleton: shrink to a local radius as well.
    obtain ⟨r₀, hr₀⟩ := h.exists_isLocalRadius hpoly hxP
    have hrpos : 0 < min (min r₀ ρ) ε := lt_min (lt_min hr₀.pos hρ) hε
    have hr : IsLocalRadius (pointSet G drawing) x (min (min r₀ ρ) ε) :=
      hr₀.mono hrpos ((min_le_left _ _).trans (min_le_left _ _))
    -- `x` lies on the skeleton, so it is not in the 2-cell.
    have hxF : x ∉ F := fun hmem =>
      Set.disjoint_left.1 hFK hmem (by rw [hK]; exact Or.inl hxP)
    obtain ⟨y, hyF, hdist⟩ := Metric.mem_closure_iff.1 hx _ hrpos
    have hyx : y ≠ x := fun hh => hxF (hh ▸ hyF)
    have hyball : y ∈ ball x (min (min r₀ ρ) ε) := by rw [mem_ball, dist_comm]; exact hdist
    have hyS : y ∉ pointSet G drawing := fun hmem =>
      Set.disjoint_left.1 hFK hyF (by rw [hK]; exact Or.inl hmem)
    -- The sector of `y`: its component in the punctured disk.
    have hdisjC : Disjoint (ball x (min (min r₀ ρ) ε)) C :=
      Set.disjoint_left.2 fun w hw =>
        (hballC (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw)).2
    have hNF : connectedComponentIn (ball x (min (min r₀ ρ) ε) \ pointSet G drawing) y ⊆ F :=
      localSector_subset_cell hK hcells hF hdisjC hyball hyF hyS
    exact ⟨y, hyF, hyx,
      lt_of_lt_of_le (by rw [dist_comm]; exact hdist) (min_le_right _ _),
      (hr.openSegment_subset_connectedComponentIn hyball hyS).trans hNF⟩
  · -- `x` is off the polygonal skeleton: a whole disk about it misses the skeleton.
    obtain ⟨ρ', hρ', hballP⟩ := Schoenflies.Plane.exists_ball_subset_diff isOpen_univ
      h.isCompact_pointSet ⟨mem_univ x, hxP⟩
    have hrpos : 0 < min (min ρ ρ') ε := lt_min (lt_min hρ hρ') hε
    have hbK : Disjoint (ball x (min (min ρ ρ') ε)) K := by
      rw [Set.disjoint_left]
      intro w hw hwK
      rcases hK ▸ hwK with hwP | hwC
      · exact (hballP (Metric.ball_subset_ball
          ((min_le_left _ _).trans (min_le_right _ _)) hw)).2 hwP
      · exact (hballC (Metric.ball_subset_ball
          ((min_le_left _ _).trans (min_le_left _ _)) hw)).2 hwC
    obtain ⟨w, hwF, hwdist⟩ := Metric.mem_closure_iff.1 hx _ hrpos
    have hsub : ball x (min (min ρ ρ') ε) ⊆ F :=
      hcells _ (convex_ball x _).isPreconnected hbK F hF
        ⟨w, by rw [mem_ball, dist_comm]; exact hwdist, hwF⟩
    -- Any short segment out of `x` will do.
    set d : Plane := Plane.mk 1 0 with hddef
    have hd : Plane.IsDirection d := isDirection_mk_one_zero
    have hsm : x + (min (min ρ ρ') ε / 2) • d - x = (min (min ρ ρ') ε / 2) • d := by module
    have hdd : dist (x + (min (min ρ ρ') ε / 2) • d) x = min (min ρ ρ') ε / 2 := by
      rw [dist_eq_norm, hsm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < min (min ρ ρ') ε / 2), hd.norm, mul_one]
    have hyball : x + (min (min ρ ρ') ε / 2) • d ∈ ball x (min (min ρ ρ') ε) := by
      rw [mem_ball, hdd]; linarith
    have hshort : dist (x + (min (min ρ ρ') ε / 2) • d) x < ε := by
      have h1 : min (min ρ ρ') ε ≤ ε := min_le_right _ _
      rw [hdd]; linarith
    refine ⟨x + (min (min ρ ρ') ε / 2) • d, hsub hyball, ?_, hshort, ?_⟩
    · intro hh
      have h0 : (min (min ρ ρ') ε / 2) • d = 0 := by rw [← hsm, hh, sub_self]
      rcases smul_eq_zero.1 h0 with h' | h'
      · exact absurd h' (by positivity)
      · exact hd.ne_zero h'
    · exact ((openSegment_subset_segment ℝ _ _).trans
        ((convex_ball x _).segment_subset (mem_ball_self hrpos) hyball)).trans hsub

/-- **`lem:polygonal-side-accessibility`, source side.** A boundary point of a 2-cell `F` of a
finite cellulation, lying off the wild outer curve `C`, is polygonally accessible from `F`.

`x ∈ closure F` is assumed rather than `x ∈ frontier F`: the proof never uses `x ∉ F`, and the
weaker hypothesis is what a consumer holding a limit of points of `F` actually has. -/
theorem polygonal_side_accessibility [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hC : IsCompact C) (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells) (hFK : Disjoint F K)
    (hx : x ∈ closure F) (hxC : x ∉ C) :
    PolyAccessible F x := by
  obtain ⟨y, hyF, -, -, hseg⟩ :=
    exists_access_segment h hpoly hC hK hcells hF hFK hx hxC one_pos
  exact PolyAccessible.of_openSegment hyF hseg

/-- **`lem:polygonal-side-accessibility`, target side.** On the target every edge is polygonal,
including every outer edge, so there is no wild set to avoid; but the 2-cells only fill an
ambient region `Q` whose frontier belongs to the skeleton, and a sector at a boundary point of
`Q` may lie outside `Q` and belong to no cell. That is exactly what
`Schoenflies.cellsAbsorb_of_isComponent_in` handles. -/
theorem polygonal_side_accessibility_target [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧
      ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hx : x ∈ closure F) :
    PolyAccessible F x := by
  have hFK : Disjoint F (pointSet G drawing) := by
    obtain ⟨-, z, hz⟩ := hcell F hF
    exact Set.disjoint_left.2 fun w hw => (connectedComponentIn_subset _ _ (hz ▸ hw)).2
  exact polygonal_side_accessibility h hpoly isCompact_empty (union_empty _).symm
    (cellsAbsorb_of_isComponent_in hQ hQK hcell) hF hFK hx (notMem_empty x)

end Graph
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

namespace Realization

variable {S : CellStructure γ}

/-- **An admissible realization** — `def:admissible-graph` in full. -/
structure IsAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop
    extends R.IsWeaklyAdmissible outer dom where
  /-- The open nonboundary part `|Γ| ∖ C` is connected. -/
  isConnected_nonboundary : IsConnected R.nonboundary

end Realization

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

/-- A cell whose open part contains a point off the skeleton is a 2-cell. -/
theorem mem_faces_of_notMem_skeletonSet (R : S.Realization) (hσ : σ ∈ S.cells)
    (hz : z ∈ R.cell σ) (hznot : z ∉ R.skeletonSet) : σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd (cell_subset_skeletonSet hσ hz) hznot
  · exact hσ

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

/-- The open nonboundary part of the source realization, read off the two clauses that pin the
skeleton and the outer cycle. -/
theorem src_nonboundary_eq (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.src.nonboundary = P.src.skeletonSet \ srcOuter := by
  rw [CellStructure.Realization.nonboundary, P.src_isWeaklyAdmissible.outerSet_eq]

/-- **The last paragraph of the proof, source half.** -/
theorem src_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.src.IsAdmissible srcOuter srcDom :=
  { P.src_isWeaklyAdmissible with isConnected_nonboundary := h }

/-! #### The matched split constructor

`RealizeSplit` and `MatchedSplit` construct the two new realizations and their skeleton
homeomorphism.  The definition below is the missing bundle-level constructor: it installs those
objects in a `GeneratedPair` and records the propagated cell-decomposition and Jordan-face
invariants.  Weak admissibility is then derived from the old pair and the two polygonal ear
drawings by `EarCrosscut.isWeaklyAdmissible_realize`. -/

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

section
-- module Solutions.Q146_CD.InitialPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.mem_vertexSet_induce_component _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.skeleton_edgeSet _root_.Schoenflies.CellStructure.SplitData.skeleton_vertexSet _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.CellStructure.SubdivData.skeleton_edgeSet _root_.Schoenflies.CellStructure.SubdivData.skeleton_vertexSet _root_.Schoenflies.CellStructure.splitFace_faces _root_.Schoenflies.CellStructure.splitFace_outerGraph _root_.Schoenflies.CellStructure.splitFace_skel _root_.Schoenflies.CellStructure.splitFace_sub _root_.Schoenflies.CellStructure.subdivideEdge_faces _root_.Schoenflies.CellStructure.subdivideEdge_outerGraph _root_.Schoenflies.CellStructure.subdivideEdge_skel _root_.Schoenflies.CellStructure.subdivideEdge_sub _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero
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

/-- `u` maps `X` homeomorphically onto `Y`, with inverse `w`. -/
structure IsSetHomeoOn (u w : Plane → Plane) (X Y : Set Plane) : Prop where
  /-- The map is continuous on its domain. -/
  continuousOn : ContinuousOn u X
  /-- The inverse is continuous on its domain. -/
  continuousOn_inv : ContinuousOn w Y
  /-- The map sends the domain into the codomain. -/
  mapsTo : MapsTo u X Y
  /-- The inverse sends the codomain into the domain. -/
  mapsTo_inv : MapsTo w Y X
  /-- The inverse undoes the map. -/
  leftInvOn : LeftInvOn w u X
  /-- The map undoes the inverse. -/
  rightInvOn : RightInvOn w u Y

namespace IsSetHomeoOn

variable {u w : Plane → Plane} {X Y : Set Plane}

/-- Running the homeomorphism backwards. -/
theorem symm (h : IsSetHomeoOn u w X Y) : IsSetHomeoOn w u Y X :=
  ⟨h.continuousOn_inv, h.continuousOn, h.mapsTo_inv, h.mapsTo, h.rightInvOn, h.leftInvOn⟩

theorem injOn_inv (h : IsSetHomeoOn u w X Y) : InjOn w Y := h.rightInvOn.injOn

theorem image_eq (h : IsSetHomeoOn u w X Y) : u '' X = Y :=
  Subset.antisymm (image_subset_iff.2 h.mapsTo) fun y hy =>
    ⟨w y, h.mapsTo_inv hy, h.rightInvOn hy⟩

theorem image_inv_eq (h : IsSetHomeoOn u w X Y) : w '' Y = X := h.symm.image_eq

/-- The image of a relatively open subset of the domain is relatively open in the codomain.
This is what makes the two open arcs of `prop:initial-pair` relatively open in `C`, hence able
to meet the countable dense set of strongly accessible points. -/
theorem image_isRelOpen (h : IsSetHomeoOn u w X Y) {U V : Set Plane} (hV : IsOpen V)
    (hU : U = V ∩ X) : ∃ W : Set Plane, IsOpen W ∧ u '' U = W ∩ Y := by
  obtain ⟨W, hWopen, hW⟩ := (_root_.continuousOn_iff'.1 h.continuousOn_inv) V hV
  refine ⟨W, hWopen, ?_⟩
  rw [hU, ← hW]
  ext y
  constructor
  · rintro ⟨x, ⟨hxV, hxX⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, h.leftInvOn hxX], h.mapsTo hxX⟩
  · rintro ⟨hyw, hyY⟩
    exact ⟨w y, ⟨hyw, h.mapsTo_inv hyY⟩, h.rightInvOn hyY⟩

end IsSetHomeoOn

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

/-- **Every outer edge is a subcell of exactly one 2-cell** — assertion (vi) of
`lem:cellulation-invariants` for the base structure, and the hypothesis of
`CellStructure.outerEdge_face_corresponds`. The edges of `B₁` bound `R₁` only and those of
`B₂` bound `R₂` only, which is the whole content. -/
theorem outerEdgeUniqueFace_initialStructure :
    CellStructure.OuterEdgeUniqueFace initialStructure := by
  rintro e ⟨i, rfl⟩
  -- an outer edge is a subcell of a 2-cell exactly when it is listed among its cells
  have hsub : ∀ k : Bool, initSub (InitialCell.edge i) (InitialCell.face k) ↔
      InitialCell.edge i ∈ faceCells k := by
    intro k
    refine ⟨?_, fun h => initSub_face h⟩
    rintro (h | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact hmem
  refine ⟨.face (![true, false, false, false, true, true] i), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [initialStructure_sub, hsub]
    fin_cases i <;> simp [faceCells]
  · rintro T ⟨⟨k, rfl⟩, hT⟩
    rw [initialStructure_sub, hsub] at hT
    have : k = ![true, false, false, false, true, true] i := by
      fin_cases i <;> cases k <;> simp_all [faceCells]
    rw [this]

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

/-- The geometric data of one realization of `initialStructure`. -/
structure HexData where
  /-- Where the six boundary vertices sit, in cyclic order. -/
  pos : Fin 6 → Plane
  /-- The parametrization of the outer edge from `pos i` to `pos (i + 1)`. -/
  outer : Fin 6 → ℝ → Plane
  /-- The parametrization of the crosscut, from `pos 1` to `pos 4`. -/
  chordParam : ℝ → Plane
  /-- The six vertices are distinct. -/
  injective_pos : Function.Injective pos
  /-- Each outer edge is drawn continuously. -/
  continuousOn_outer : ∀ i, ContinuousOn (outer i) I
  /-- Each outer edge is drawn injectively. -/
  injOn_outer : ∀ i, InjOn (outer i) I
  /-- An outer edge starts at its first vertex. -/
  outer_zero : ∀ i, outer i 0 = pos i
  /-- An outer edge ends at the next vertex. -/
  outer_one : ∀ i, outer i 1 = pos (i + 1)
  /-- The crosscut is drawn continuously. -/
  continuousOn_chord : ContinuousOn chordParam I
  /-- The crosscut is drawn injectively. -/
  injOn_chord : InjOn chordParam I
  /-- The crosscut starts at `a`. -/
  chord_zero : chordParam 0 = pos 1
  /-- The crosscut ends at `b`. -/
  chord_one : chordParam 1 = pos 4
  /-- Two distinct outer edges meet only at points that are ends of both. -/
  outer_meet : ∀ i j, i ≠ j → outer i '' I ∩ outer j '' I ⊆
    ({pos i, pos (i + 1)} : Set Plane) ∩ {pos j, pos (j + 1)}
  /-- The crosscut meets each outer edge only at its own two ends. -/
  chord_meet : ∀ i, chordParam '' I ∩ outer i '' I ⊆ ({pos 1, pos 4} : Set Plane)

namespace HexData

variable (H : HexData)

/-- Where each 0-cell sits. Junk on the other cells, which `Realization` never reads. -/
def point : InitialCell → Plane
  | .vert i => H.pos i
  | _ => 0

/-- How each 1-cell is drawn. Junk on the other cells. -/
def draw : InitialCell → ℝ → Plane
  | .edge i => H.outer i
  | .chord => H.chordParam
  | _ => fun _ => 0

/-- The crosscut, as a set. -/
def chordSet : Set Plane := H.chordParam '' I

/-- The two boundary edge-paths from `pos 1` to `pos 4`, as sets: `arcOf false` is `A₁`, the
union of the outer edges `1, 2, 3`, and `arcOf true` is `A₂`, the union of `4, 5, 0`. -/
def arcOf : Bool → Set Plane
  | false => H.outer 1 '' I ∪ (H.outer 2 '' I ∪ H.outer 3 '' I)
  | true => H.outer 4 '' I ∪ (H.outer 5 '' I ∪ H.outer 0 '' I)

/-- The realized outer cycle, as the union of the six outer edges. -/
def outerArcs : Set Plane := ⋃ i : Fin 6, H.outer i '' I

/-- The point set of each open cell.

The 2-cell `face k` is realized by the *side* of the crosscut belonging to `Aₖ`, exactly as the
blueprint prescribes (tex 1590–1602): "the 2-cell `Rᵢ` is realized in the source as the crosscut
side whose closure meets `C` in `Aᵢ`". By `thm:general-crosscut` that side is
`Int(Aᵢ ∪ P)` = `inside (arcOf k ∪ chordSet)`, and taking this as the *definition* makes the
crosscut theorem apply to it with nothing to transport. -/
def cellSet : InitialCell → Set Plane
  | .vert i => {H.pos i}
  | .edge i => H.outer i '' I \ {H.pos i, H.pos (i + 1)}
  | .chord => H.chordParam '' I \ {H.pos 1, H.pos 4}
  | .face k => inside (H.arcOf k ∪ H.chordSet)
  | .aux _ => ∅

@[simp] theorem point_vert (i : Fin 6) : H.point (.vert i) = H.pos i := rfl

@[simp] theorem draw_edge (i : Fin 6) : H.draw (.edge i) = H.outer i := rfl

@[simp] theorem draw_chord : H.draw .chord = H.chordParam := rfl

@[simp] theorem edgeArc_edge (i : Fin 6) :
    Graph.edgeArc H.draw (.edge i) = H.outer i '' I := rfl

@[simp] theorem edgeArc_chord : Graph.edgeArc H.draw .chord = H.chordParam '' I := rfl

theorem pos_mem_outer (i : Fin 6) : H.pos i ∈ H.outer i '' I :=
  ⟨0, zero_mem_I, H.outer_zero i⟩

theorem pos_succ_mem_outer (i : Fin 6) : H.pos (i + 1) ∈ H.outer i '' I :=
  ⟨1, one_mem_I, H.outer_one i⟩

/-- **A vertex lies on an outer edge only if it is one of its two ends.** Not an axiom of
`HexData`: a vertex is an end of *its own* outer edge, so a vertex on a second edge is a point
of two edges, and the meeting condition places it among the ends of both. -/
theorem mem_outer_iff {k i : Fin 6} (h : H.pos k ∈ H.outer i '' I) : k = i ∨ k = i + 1 := by
  by_cases hki : k = i
  · exact Or.inl hki
  have hmeet := H.outer_meet k i hki ⟨H.pos_mem_outer k, h⟩
  rcases hmeet.2 with h' | h'
  · exact Or.inl (H.injective_pos h')
  · exact Or.inr (H.injective_pos h')

/-- **A vertex lies on the crosscut only if it is one of its two ends.** -/
theorem mem_chord_iff {k : Fin 6} (h : H.pos k ∈ H.chordParam '' I) : k = 1 ∨ k = 4 := by
  rcases H.chord_meet k ⟨h, H.pos_mem_outer k⟩ with h' | h'
  · exact Or.inl (H.injective_pos h')
  · exact Or.inr (H.injective_pos h')

theorem injOn_point : InjOn H.point V(initSkel) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact congrArg InitialCell.vert (H.injective_pos hij)

/-- The drawn skeleton: the pushforward of `initSkel` along the six positions. -/
theorem isDrawing : Graph.IsDrawing (initSkel.map H.point) H.draw where
  edge_param := by
    intro e he
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he
    rcases he with ⟨i, rfl⟩ | rfl
    · refine ⟨H.continuousOn_outer i, H.injOn_outer i, ?_⟩
      have : initSkel.IsLink (.edge i) (.vert i) (.vert (i + 1)) :=
        initSkel_isLink_ends (InitialCell.edge_mem_edges i)
      simpa [H.outer_zero i, H.outer_one i] using this.map H.point
    · refine ⟨H.continuousOn_chord, H.injOn_chord, ?_⟩
      have : initSkel.IsLink .chord (.vert 1) (.vert 4) :=
        initSkel_isLink_ends InitialCell.chord_mem_edges
      simpa [H.chord_zero, H.chord_one] using this.map H.point
  vertex_mem_edgeArc := by
    rintro e x y v hl ⟨_, ⟨k, rfl⟩, rfl⟩ hv
    obtain ⟨x', y', hl', rfl, rfl⟩ := hl
    obtain ⟨he, hxy⟩ := hl'
    rcases he with ⟨i, rfl⟩ | rfl
    · rcases H.mem_outer_iff (i := i) (k := k) hv with rfl | rfl <;>
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [InitialCell.ends]
    · rcases H.mem_chord_iff (k := k) hv with rfl | rfl <;>
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [InitialCell.ends]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he hf
    -- both ends of a 1-cell are among the six positions, so it suffices to name the index
    have key : ∀ (c : InitialCell) (k : Fin 6), c ∈ InitialCell.edges →
        H.pos k = H.point c.ends.1 ∨ H.pos k = H.point c.ends.2 →
        (initSkel.map H.point).Inc c (H.pos k) := by
      intro c k hc hk
      rw [Graph.map_inc]
      rcases hk with hk | hk
      · exact ⟨c.ends.1, ⟨c.ends.2, initSkel_isLink_ends hc⟩, hk⟩
      · exact ⟨c.ends.2, ⟨c.ends.1, (initSkel_isLink_ends hc).symm⟩, hk⟩
    have hmem : ∃ k : Fin 6, p = H.pos k ∧ (e = .chord ∨ ∃ i, e = .edge i ∧ (k = i ∨ k = i + 1))
        ∧ (f = .chord ∨ ∃ j, f = .edge j ∧ (k = j ∨ k = j + 1)) := by
      rcases he with ⟨i, rfl⟩ | rfl
      · rcases hf with ⟨j, rfl⟩ | rfl
        · have hij : i ≠ j := fun h => hef (by rw [h])
          obtain ⟨h1, h2⟩ := H.outer_meet i j hij ⟨hpe, hpf⟩
          rcases h1 with rfl | rfl
          · exact ⟨i, rfl, Or.inr ⟨i, rfl, Or.inl rfl⟩, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
          · exact ⟨i + 1, rfl, Or.inr ⟨i, rfl, Or.inr rfl⟩, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
        · rcases H.chord_meet i ⟨hpf, hpe⟩ with rfl | rfl
          · exact ⟨1, rfl, Or.inr ⟨i, rfl, H.mem_outer_iff hpe⟩, Or.inl rfl⟩
          · exact ⟨4, rfl, Or.inr ⟨i, rfl, H.mem_outer_iff hpe⟩, Or.inl rfl⟩
      · rcases hf with ⟨j, rfl⟩ | rfl
        · rcases H.chord_meet j ⟨hpe, hpf⟩ with rfl | rfl
          · exact ⟨1, rfl, Or.inl rfl, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
          · exact ⟨4, rfl, Or.inl rfl, Or.inr ⟨j, rfl, H.mem_outer_iff hpf⟩⟩
        · exact absurd rfl hef
    obtain ⟨k, rfl, hke, hkf⟩ := hmem
    refine ⟨⟨.vert k, ⟨k, rfl⟩, rfl⟩, ?_, ?_⟩
    · rcases hke with rfl | ⟨i, rfl, hk⟩
      · rcases H.mem_chord_iff (k := k) hpe with rfl | rfl
        exacts [key _ _ InitialCell.chord_mem_edges (Or.inl rfl),
          key _ _ InitialCell.chord_mem_edges (Or.inr rfl)]
      · rcases hk with rfl | rfl
        exacts [key _ k (InitialCell.edge_mem_edges k) (Or.inl rfl),
          key _ (i + 1) (InitialCell.edge_mem_edges i) (Or.inr rfl)]
    · rcases hkf with rfl | ⟨j, rfl, hk⟩
      · rcases H.mem_chord_iff (k := k) hpf with rfl | rfl
        exacts [key _ _ InitialCell.chord_mem_edges (Or.inl rfl),
          key _ _ InitialCell.chord_mem_edges (Or.inr rfl)]
      · rcases hk with rfl | rfl
        exacts [key _ k (InitialCell.edge_mem_edges k) (Or.inl rfl),
          key _ (j + 1) (InitialCell.edge_mem_edges j) (Or.inr rfl)]

/-- **The realization of `initialStructure` determined by a `HexData`.** -/
def realization : initialStructure.Realization where
  pos := H.point
  drawing := H.draw
  injOn_pos := H.injOn_point
  isDrawing := H.isDrawing
  cell := H.cellSet
  cell_vertex := by rintro _ ⟨i, rfl⟩; rfl
  cell_edge := by
    rintro e x y ⟨he, hxy⟩
    rcases he with ⟨i, rfl⟩ | rfl <;>
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [cellSet, InitialCell.ends, Set.pair_comm]

@[simp] theorem realization_pos : H.realization.pos = H.point := rfl

@[simp] theorem realization_drawing : H.realization.drawing = H.draw := rfl

@[simp] theorem realization_cell : H.realization.cell = H.cellSet := rfl

/-! #### The realized skeleton and the two boundary arcs -/

theorem pos_ne {i j : Fin 6} (h : i ≠ j) : H.pos i ≠ H.pos j :=
  fun he => h (H.injective_pos he)

theorem outer_meet_pair {i j : Fin 6} (hij : i ≠ j) {z : Plane} (hi : z ∈ H.outer i '' I)
    (hj : z ∈ H.outer j '' I) :
    (z = H.pos i ∨ z = H.pos (i + 1)) ∧ (z = H.pos j ∨ z = H.pos (j + 1)) :=
  H.outer_meet i j hij ⟨hi, hj⟩

/-- Each outer edge is drawn as an arc between consecutive vertices. -/
theorem isArcBetween_outer (i : Fin 6) :
    IsArcBetween (H.outer i '' I) (H.pos i) (H.pos (i + 1)) :=
  ⟨H.outer i, H.continuousOn_outer i, H.injOn_outer i, rfl, H.outer_zero i, H.outer_one i⟩

/-- The crosscut is drawn as an arc from `a` to `b`. -/
theorem isArcBetween_chordSet : IsArcBetween H.chordSet (H.pos 1) (H.pos 4) :=
  ⟨H.chordParam, H.continuousOn_chord, H.injOn_chord, rfl, H.chord_zero, H.chord_one⟩

theorem outerArcs_eq :
    H.outerArcs = H.outer 0 '' I ∪ (H.outer 1 '' I ∪ (H.outer 2 '' I ∪ (H.outer 3 '' I ∪
      (H.outer 4 '' I ∪ H.outer 5 '' I)))) := by
  ext z
  simp only [outerArcs, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> tauto
  · rintro (h | h | h | h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩]

theorem arcOf_union : H.arcOf false ∪ H.arcOf true = H.outerArcs := by
  rw [outerArcs_eq]
  simp only [arcOf]
  ext z
  simp only [Set.mem_union]
  constructor <;> (intro h; tauto)

/-- **`A₁` is an arc from `a` to `b`.** Three consecutive outer edges, glued at the two corner
vertices between them. -/
theorem arcOf_false_isArcBetween : IsArcBetween (H.arcOf false) (H.pos 1) (H.pos 4) := by
  have h23 : IsArcBetween (H.outer 2 '' I ∪ H.outer 3 '' I) (H.pos 2) (H.pos 4) := by
    refine (H.isArcBetween_outer 2).concatenate (H.isArcBetween_outer 3) fun z hz hz' => ?_
    obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 2) (j := 3) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  refine (H.isArcBetween_outer 1).concatenate h23 fun z hz hz' => ?_
  rcases hz' with hz' | hz'
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 1) (j := 2) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 1) (j := 3) (by decide) hz hz'
    rcases h₁ with rfl | rfl <;> rcases h₂ with h | h <;>
      exact absurd h (H.pos_ne (by decide))

/-- **`A₂` is an arc from `b` to `a`.** -/
theorem arcOf_true_isArcBetween : IsArcBetween (H.arcOf true) (H.pos 4) (H.pos 1) := by
  have h50 : IsArcBetween (H.outer 5 '' I ∪ H.outer 0 '' I) (H.pos 5) (H.pos 1) := by
    refine (H.isArcBetween_outer 5).concatenate (H.isArcBetween_outer 0) fun z hz hz' => ?_
    obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 5) (j := 0) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  refine (H.isArcBetween_outer 4).concatenate h50 fun z hz hz' => ?_
  rcases hz' with hz' | hz'
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 4) (j := 5) (by decide) hz hz'
    rcases h₁ with rfl | rfl
    · rcases h₂ with h | h
      exacts [absurd h (H.pos_ne (by decide)), absurd h (H.pos_ne (by decide))]
    · rfl
  · obtain ⟨h₁, h₂⟩ := H.outer_meet_pair (i := 4) (j := 0) (by decide) hz hz'
    rcases h₁ with rfl | rfl <;> rcases h₂ with h | h <;>
      exact absurd h (H.pos_ne (by decide))

/-- **The two boundary arcs meet exactly at `a` and `b`.** Nine pairs of outer edges; six of
them have no vertex in common at all and contribute nothing. -/
theorem arcOf_inter : H.arcOf false ∩ H.arcOf true = ({H.pos 1, H.pos 4} : Set Plane) := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hz, hz'⟩
    simp only [arcOf, Set.mem_union] at hz hz'
    rcases hz with h₁ | h₁ | h₁ <;> rcases hz' with h₂ | h₂ | h₂ <;>
      · obtain ⟨ha, hb⟩ := H.outer_meet_pair (by decide) h₁ h₂
        rcases ha with rfl | rfl <;> rcases hb with h | h <;>
          first
            | exact Or.inl rfl
            | exact Or.inr rfl
            | exact absurd h (H.pos_ne (by decide))
  · rintro z (rfl | rfl)
    · refine ⟨Or.inl (H.pos_mem_outer 1), Or.inr (Or.inr ?_)⟩
      simpa using H.pos_succ_mem_outer 0
    · refine ⟨Or.inr (Or.inr ?_), Or.inl (H.pos_mem_outer 4)⟩
      simpa using H.pos_succ_mem_outer 3

theorem outerSet_realization : H.realization.outerSet = H.outerArcs := by
  change V(initOuter.map H.point) ∪ (⋃ e ∈ E(initOuter.map H.point), Graph.edgeArc H.draw e) = _
  refine Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [Graph.edgeSet_map, edgeSet_initOuter] at he
    obtain ⟨i, rfl⟩ := he
    exact Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i
  · refine Set.iUnion_subset fun i => ?_
    refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.edge i ∈ E(initOuter.map H.point) from ⟨i, rfl⟩)

theorem skeletonSet_realization : H.realization.skeletonSet = H.outerArcs ∪ H.chordSet := by
  change V(initSkel.map H.point) ∪ (⋃ e ∈ E(initSkel.map H.point), Graph.edgeArc H.draw e) = _
  refine Subset.antisymm (Set.union_subset ?_ ?_) (Set.union_subset ?_ ?_)
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Or.inl (Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩)
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [Graph.edgeSet_map, edgeSet_initSkel] at he
    rcases he with ⟨i, rfl⟩ | rfl
    · exact fun z hz => Or.inl (Set.mem_iUnion.2 ⟨i, hz⟩)
    · exact fun z hz => Or.inr hz
  · refine Set.iUnion_subset fun i => ?_
    refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.edge i ∈ E(initSkel.map H.point) from Or.inl ⟨i, rfl⟩)
  · refine Set.subset_union_of_subset_right ?_ _
    exact Set.subset_biUnion_of_mem (u := fun e => Graph.edgeArc H.draw e)
      (show InitialCell.chord ∈ E(initSkel.map H.point) from Or.inr rfl)

end HexData


/-! ### The initial skeleton is 2-connected

The first clause of `def:admissible-graph`. It is a fact about the *abstract* graph — a hexagon
with one chord — and `Graph.isTwoConnected_map_iff` carries it to both realizations at once, so
it is proved here and nowhere else. The chord plays no part: the hexagon alone is 2-connected,
because deleting one of its vertices leaves a path. All the cyclic index arithmetic is
`decide`. -/

theorem stepFull {m m' : Fin 6} (h : m + 1 = m') :
    initSkel.Reaches (.vert m) (.vert m') := by
  subst h
  exact Graph.Reaches.of_isLink (initSkel_isLink_ends (InitialCell.edge_mem_edges m))

/-- The abstract hexagon-with-chord is connected. -/
theorem connected_initSkel : initSkel.Connected := by
  refine Graph.Connected.of_hub (u := .vert 0) ⟨0, rfl⟩ ?_
  rintro _ ⟨j, rfl⟩
  have s01 : initSkel.Reaches (.vert 0) (.vert 1) := stepFull (by decide)
  have s12 : initSkel.Reaches (.vert 1) (.vert 2) := stepFull (by decide)
  have s23 : initSkel.Reaches (.vert 2) (.vert 3) := stepFull (by decide)
  have s34 : initSkel.Reaches (.vert 3) (.vert 4) := stepFull (by decide)
  have s45 : initSkel.Reaches (.vert 4) (.vert 5) := stepFull (by decide)
  fin_cases j
  · exact Graph.Reaches.refl ⟨0, rfl⟩
  · exact s01
  · exact s01.trans s12
  · exact (s01.trans s12).trans s23
  · exact ((s01.trans s12).trans s23).trans s34
  · exact (((s01.trans s12).trans s23).trans s34).trans s45

theorem vert_notMem_del {k n : Fin 6} (hn : n ≠ 0) :
    (InitialCell.vert (k + n)) ∉ ({InitialCell.vert k} : Set InitialCell) := by
  simp only [Set.mem_singleton_iff, InitialCell.vert.injEq]
  exact fun h => hn (fin6_add_eq_self k n h)

theorem stepDel (k : Fin 6) {m m' : Fin 6} (hmm : m + 1 = m') (hm : m ≠ 0)
    (hm' : m' ≠ 0) :
    (initSkel.deleteVerts {InitialCell.vert k}).Reaches (.vert (k + m)) (.vert (k + m')) := by
  have h0 : initSkel.IsLink (InitialCell.edge (k + m)) (.vert (k + m)) (.vert (k + m + 1)) :=
    initSkel_isLink_ends (InitialCell.edge_mem_edges (k + m))
  rw [fin6_add_one k m, hmm] at h0
  refine Graph.Reaches.of_isLink (e := InitialCell.edge (k + m)) ?_
  rw [Graph.deleteVerts_isLink]
  exact ⟨h0, vert_notMem_del hm, vert_notMem_del hm'⟩

/-- Deleting one vertex of the hexagon leaves a path, hence a connected graph. -/
theorem deleteVert_connected_initSkel (k : Fin 6) :
    (initSkel.deleteVerts {InitialCell.vert k}).Connected := by
  have h12 := stepDel k (m := 1) (m' := 2) (by decide) (by decide) (by decide)
  have h23 := stepDel k (m := 2) (m' := 3) (by decide) (by decide) (by decide)
  have h34 := stepDel k (m := 3) (m' := 4) (by decide) (by decide) (by decide)
  have h45 := stepDel k (m := 4) (m' := 5) (by decide) (by decide) (by decide)
  have hhub : (InitialCell.vert (k + 1)) ∈ V(initSkel.deleteVerts {InitialCell.vert k}) :=
    ⟨⟨k + 1, rfl⟩, vert_notMem_del (by decide)⟩
  refine Graph.Connected.of_hub hhub ?_
  rintro _ ⟨⟨j, rfl⟩, hj⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, fin6_add_sub k j⟩
  have hm : m ≠ 0 := by
    rintro rfl
    exact hj (by simp)
  fin_cases m
  · exact absurd rfl hm
  · exact Graph.Reaches.refl hhub
  · exact h12
  · exact h12.trans h23
  · exact (h12.trans h23).trans h34
  · exact ((h12.trans h23).trans h34).trans h45

/-- **The initial skeleton is 2-connected** — the first clause of `def:admissible-graph`. -/
theorem isTwoConnected_initSkel : initSkel.IsTwoConnected where
  hasThreeVertices :=
    ⟨.vert 0, ⟨0, rfl⟩, .vert 1, ⟨1, rfl⟩, .vert 2, ⟨2, rfl⟩, by decide, by decide, by decide⟩
  connected := connected_initSkel
  deleteVerts_connected := by rintro _ ⟨k, rfl⟩; exact deleteVert_connected_initSkel k

/-- **Both drawn skeleta are 2-connected.** By `lem:combinatorial-invariance` (a) there is only
one statement to prove, and it is the abstract one. -/
theorem HexData.isTwoConnected_graph (H : HexData) : (H.realization.graph).IsTwoConnected :=
  (Graph.isTwoConnected_map_iff H.injOn_point).2 isTwoConnected_initSkel

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

namespace Plane

/-- Two plane points agree when their coordinates do. -/
theorem eq_mk {p : Plane} {x y : ℝ} (h0 : p 0 = x) (h1 : p 1 = y) : p = Plane.mk x y := by
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem mk_inj {x y x' y' : ℝ} (h : Plane.mk x y = Plane.mk x' y') : x = x' ∧ y = y' :=
  ⟨congrArg (fun p : Plane => p 0) h, congrArg (fun p : Plane => p 1) h⟩

end Plane

/-- A horizontal piece of the square boundary: second coordinate pinned, first coordinate
sweeping an interval. -/
def hPiece (c lo hi : ℝ) : Set Plane := {p : Plane | p 1 = c ∧ lo ≤ p 0 ∧ p 0 ≤ hi}

/-- A vertical piece of the square boundary. -/
def vPiece (c lo hi : ℝ) : Set Plane := {p : Plane | p 0 = c ∧ lo ≤ p 1 ∧ p 1 ≤ hi}

theorem segment_eq_hPiece (c : ℝ) {lo hi : ℝ} (h : lo ≤ hi) :
    segment ℝ (Plane.mk lo c) (Plane.mk hi c) = hPiece c lo hi := by
  ext p
  rw [mem_segment_horiz, segment_eq_Icc h]
  simp [hPiece, Set.mem_Icc]

theorem segment_eq_vPiece (c : ℝ) {lo hi : ℝ} (h : lo ≤ hi) :
    segment ℝ (Plane.mk c lo) (Plane.mk c hi) = vPiece c lo hi := by
  ext p
  rw [mem_segment_vert, segment_eq_Icc h]
  simp [vPiece, Set.mem_Icc]

theorem hPiece_subset_modelCurve {c lo hi : ℝ} (hc : |c| = 1) (hlo : -1 ≤ lo) (hhi : hi ≤ 1) :
    hPiece c lo hi ⊆ modelCurve := by
  rintro p ⟨h1, h2, h3⟩
  change Plane.supNorm p = 1
  simp only [Plane.supNorm, h1, hc]
  exact max_eq_right (by rw [abs_le]; constructor <;> linarith)

theorem vPiece_subset_modelCurve {c lo hi : ℝ} (hc : |c| = 1) (hlo : -1 ≤ lo) (hhi : hi ≤ 1) :
    vPiece c lo hi ⊆ modelCurve := by
  rintro p ⟨h1, h2, h3⟩
  change Plane.supNorm p = 1
  simp only [Plane.supNorm, h1, hc]
  exact max_eq_left (by rw [abs_le]; constructor <;> linarith)

variable {α β : ℝ}

/-- The six marked points of `S`, in cyclic order: the corner `(1,1)`, `u(a) = (α,1)`, the
corners `(-1,1)` and `(-1,-1)`, `u(b) = (β,-1)`, and the corner `(1,-1)`. -/
def tgtPos (α β : ℝ) : Fin 6 → Plane :=
  ![Plane.mk 1 1, Plane.mk α 1, Plane.mk (-1) 1, Plane.mk (-1) (-1), Plane.mk β (-1),
    Plane.mk 1 (-1)]

/-- The six outer edges of the target, straight. -/
noncomputable def tgtOuter (α β : ℝ) (i : Fin 6) : ℝ → Plane :=
  AffineMap.lineMap (tgtPos α β i) (tgtPos α β (i + 1))

/-- The straight chord `[u(a), u(b)]`. -/
noncomputable def tgtChord (α β : ℝ) : ℝ → Plane :=
  AffineMap.lineMap (tgtPos α β 1) (tgtPos α β 4)

theorem tgtOuter_image (α β : ℝ) (i : Fin 6) :
    tgtOuter α β i '' I = segment ℝ (tgtPos α β i) (tgtPos α β (i + 1)) := by
  rw [segment_eq_image_lineMap]
  rfl

theorem tgtChord_image (α β : ℝ) :
    tgtChord α β '' I = segment ℝ (Plane.mk α 1) (Plane.mk β (-1)) := by
  rw [segment_eq_image_lineMap]
  rfl

/-- The six target arcs, in the pinned-coordinate normal form. -/
theorem segment_tgtPos (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    segment ℝ (tgtPos α β i) (tgtPos α β (i + 1)) =
      ![hPiece 1 α 1, hPiece 1 (-1) α, vPiece (-1) (-1) 1, hPiece (-1) (-1) β, hPiece (-1) β 1,
        vPiece 1 (-1) 1] i := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  fin_cases i
  · change segment ℝ (Plane.mk 1 1) (Plane.mk α 1) = hPiece 1 α 1
    rw [segment_symm, segment_eq_hPiece 1 hα2.le]
  · change segment ℝ (Plane.mk α 1) (Plane.mk (-1) 1) = hPiece 1 (-1) α
    rw [segment_symm, segment_eq_hPiece 1 hα1.le]
  · change segment ℝ (Plane.mk (-1) 1) (Plane.mk (-1) (-1)) = vPiece (-1) (-1) 1
    rw [segment_symm, segment_eq_vPiece (-1) (by norm_num : (-1:ℝ) ≤ 1)]
  · change segment ℝ (Plane.mk (-1) (-1)) (Plane.mk β (-1)) = hPiece (-1) (-1) β
    rw [segment_eq_hPiece (-1) hβ1.le]
  · change segment ℝ (Plane.mk β (-1)) (Plane.mk 1 (-1)) = hPiece (-1) β 1
    rw [segment_eq_hPiece (-1) hβ2.le]
  · change segment ℝ (Plane.mk 1 (-1)) (Plane.mk 1 1) = vPiece 1 (-1) 1
    rw [segment_eq_vPiece 1 (by norm_num : (-1:ℝ) ≤ 1)]

theorem injective_tgtPos (hα : |α| < 1) (hβ : |β| < 1) : Function.Injective (tgtPos α β) := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; obtain ⟨h0, h1⟩ := Plane.mk_inj h; linarith)

theorem tgtOuter_subset_modelCurve (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtOuter α β i '' I ⊆ modelCurve := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  rw [tgtOuter_image, segment_tgtPos hα hβ]
  fin_cases i
  exacts [hPiece_subset_modelCurve (by norm_num) hα1.le le_rfl,
    hPiece_subset_modelCurve (by norm_num) le_rfl hα2.le,
    vPiece_subset_modelCurve (by norm_num) le_rfl le_rfl,
    hPiece_subset_modelCurve (by norm_num) le_rfl hβ2.le,
    hPiece_subset_modelCurve (by norm_num) hβ1.le le_rfl,
    vPiece_subset_modelCurve (by norm_num) le_rfl le_rfl]

/-- **The fifteen pairwise intersections of the six target edges.** Two edges on the same side
of the square overlap in at most the marked point between them; two on adjacent sides meet at
most in the corner they share, and the four cases where a corner is not on the piece in
question are empty because `|α|, |β| < 1`; two on opposite sides never meet. Every one of them
is a comparison of two real intervals. -/
theorem tgtOuter_meet (hα : |α| < 1) (hβ : |β| < 1) (i j : Fin 6) (hij : i ≠ j) :
    tgtOuter α β i '' I ∩ tgtOuter α β j '' I ⊆
      ({tgtPos α β i, tgtPos α β (i + 1)} : Set Plane) ∩
        {tgtPos α β j, tgtPos α β (j + 1)} := by
  have hα' := abs_lt.1 hα
  have hβ' := abs_lt.1 hβ
  obtain ⟨hα1, hα2⟩ := hα'
  obtain ⟨hβ1, hβ2⟩ := hβ'
  simp only [tgtOuter_image, segment_tgtPos hα hβ]
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | · rintro p ⟨⟨e1, e2, e3⟩, f1, f2, f3⟩
          first
            | (exfalso; linarith)
            | exact ⟨Or.inl (Plane.eq_mk (by linarith) (by linarith)),
                Or.inl (Plane.eq_mk (by linarith) (by linarith))⟩
            | exact ⟨Or.inl (Plane.eq_mk (by linarith) (by linarith)),
                Or.inr (Plane.eq_mk (by linarith) (by linarith))⟩
            | exact ⟨Or.inr (Plane.eq_mk (by linarith) (by linarith)),
                Or.inl (Plane.eq_mk (by linarith) (by linarith))⟩

/-- **The straight chord between opposite sides has all its other points in the open square.**
This is the single use of the nonadjacency hypothesis of `prop:initial-pair`. -/
theorem openSegment_chord_supNorm_lt (hα : |α| < 1) (hβ : |β| < 1) :
    ∀ p ∈ openSegment ℝ (Plane.mk α 1) (Plane.mk β (-1)), Plane.supNorm p < 1 := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  rintro p ⟨a, b, ha, hb, hab, rfl⟩
  have h0 : (a • Plane.mk α 1 + b • Plane.mk β (-1)) 0 = a * α + b * β := by
    rw [Plane.smul_add_apply]; simp
  have h1 : (a • Plane.mk α 1 + b • Plane.mk β (-1)) 1 = a - b := by
    rw [Plane.smul_add_apply]; simp <;> ring
  have hb0 : |a * α + b * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hb1 : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [Plane.supNorm, h0, h1]
  exact max_lt hb0 hb1

theorem openSegment_chord_notMem_modelCurve (hα : |α| < 1) (hβ : |β| < 1) :
    ∀ p ∈ openSegment ℝ (Plane.mk α 1) (Plane.mk β (-1)), p ∉ modelCurve := fun p hp hmem =>
  absurd (show Plane.supNorm p = 1 from hmem)
    (ne_of_lt (openSegment_chord_supNorm_lt hα hβ p hp))

/-- The chord meets each outer edge only at its own two ends. -/
theorem tgtChord_meet (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtChord α β '' I ∩ tgtOuter α β i '' I ⊆
      ({tgtPos α β 1, tgtPos α β 4} : Set Plane) := by
  rintro p ⟨hp, hp'⟩
  rw [tgtChord_image, ← insert_endpoints_openSegment] at hp
  rcases hp with rfl | rfl | hp
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (tgtOuter_subset_modelCurve hα hβ i hp')
      (openSegment_chord_notMem_modelCurve hα hβ _ hp)

theorem tgtOuter_image_eq (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtOuter α β i '' I =
      ![hPiece 1 α 1, hPiece 1 (-1) α, vPiece (-1) (-1) 1, hPiece (-1) (-1) β, hPiece (-1) β 1,
        vPiece 1 (-1) 1] i := by
  rw [tgtOuter_image, segment_tgtPos hα hβ]

/-- **The six target edges cover `S`.** Each side of the square is one piece, except the top
and the bottom, which are cut in two at `u(a)` and `u(b)`. -/
theorem iUnion_tgtOuter (hα : |α| < 1) (hβ : |β| < 1) :
    (⋃ i : Fin 6, tgtOuter α β i '' I) = modelCurve := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  refine Subset.antisymm (Set.iUnion_subset (tgtOuter_subset_modelCurve hα hβ)) fun p hp => ?_
  rw [modelCurve_eq_sides] at hp
  rcases hp with (hp | hp) | (hp | hp)
  · rw [mem_sideTop, abs_le] at hp
    obtain ⟨h1, h0⟩ := hp
    rcases le_or_gt α (p 0) with h | h
    · exact Set.mem_iUnion.2 ⟨0, by rw [tgtOuter_image_eq hα hβ 0]; exact ⟨h1, h, h0.2⟩⟩
    · exact Set.mem_iUnion.2 ⟨1, by rw [tgtOuter_image_eq hα hβ 1]; exact ⟨h1, h0.1, h.le⟩⟩
  · rw [mem_sideLeft, abs_le] at hp
    obtain ⟨h0, h1⟩ := hp
    exact Set.mem_iUnion.2 ⟨2, by rw [tgtOuter_image_eq hα hβ 2]; exact ⟨h0, h1.1, h1.2⟩⟩
  · rw [mem_sideBottom, abs_le] at hp
    obtain ⟨h1, h0⟩ := hp
    rcases le_or_gt (p 0) β with h | h
    · exact Set.mem_iUnion.2 ⟨3, by rw [tgtOuter_image_eq hα hβ 3]; exact ⟨h1, h0.1, h⟩⟩
    · exact Set.mem_iUnion.2 ⟨4, by rw [tgtOuter_image_eq hα hβ 4]; exact ⟨h1, h.le, h0.2⟩⟩
  · rw [mem_sideRight, abs_le] at hp
    obtain ⟨h0, h1⟩ := hp
    exact Set.mem_iUnion.2 ⟨5, by rw [tgtOuter_image_eq hα hβ 5]; exact ⟨h0, h1.1, h1.2⟩⟩

theorem tgtPos_mem_modelCurve (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtPos α β i ∈ modelCurve := by
  refine tgtOuter_subset_modelCurve hα hβ i ⟨0, zero_mem_I, ?_⟩
  exact AffineMap.lineMap_apply_zero _ _

theorem tgtPos_succ_ne (hα : |α| < 1) (hβ : |β| < 1) (i : Fin 6) :
    tgtPos α β i ≠ tgtPos α β (i + 1) := by
  have hne : i ≠ i + 1 := by revert i; decide
  exact fun h => hne (injective_tgtPos hα hβ h)

/-- **The target realization of `prop:initial-pair`**: the square `S`, subdivided at its four
corners and at `u(a) = (α,1)`, `u(b) = (β,-1)`, together with the straight chord between the
last two. -/
noncomputable def targetHex (hα : |α| < 1) (hβ : |β| < 1) : HexData where
  pos := tgtPos α β
  outer := tgtOuter α β
  chordParam := tgtChord α β
  injective_pos := injective_tgtPos hα hβ
  continuousOn_outer := fun _ => AffineMap.lineMap_continuous.continuousOn
  injOn_outer := fun i => injOn_lineMap (tgtPos_succ_ne hα hβ i)
  outer_zero := fun i => AffineMap.lineMap_apply_zero _ _
  outer_one := fun i => AffineMap.lineMap_apply_one _ _
  continuousOn_chord := AffineMap.lineMap_continuous.continuousOn
  injOn_chord := injOn_lineMap (by
    intro h
    have := injective_tgtPos hα hβ h
    exact absurd this (by decide))
  chord_zero := AffineMap.lineMap_apply_zero _ _
  chord_one := AffineMap.lineMap_apply_one _ _
  outer_meet := tgtOuter_meet hα hβ
  chord_meet := tgtChord_meet hα hβ

@[simp] theorem targetHex_pos (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).pos = tgtPos α β := rfl

@[simp] theorem targetHex_outer (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).outer = tgtOuter α β := rfl

@[simp] theorem targetHex_chordParam (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).chordParam = tgtChord α β := rfl

/-- **The target outer cycle is exactly `S`.** -/
theorem targetHex_outerArcs (hα : |α| < 1) (hβ : |β| < 1) :
    (targetHex hα hβ).outerArcs = modelCurve := iUnion_tgtOuter hα hβ


/-! ### The source realization: the curve with one polygonal crosscut

The source realization is the pushforward of the target's outer cycle along `w = u⁻¹`, together
with the polygonal crosscut `P` as its seventh edge. Nothing about the six outer arcs has to be
proved again: `w` is injective on `S`, so each of the three drawing conditions transfers.

The crosscut arrives as a parametrization together with the one geometric fact `lem:accessible-
endpoints` supplies — that every point of it other than its two ends lies in `D` — from which
`P ∩ C = {a, b}` follows, and with it the last meeting condition. -/

variable {C : Set Plane}

/-- **The source realization of `prop:initial-pair`**: `C`, subdivided at the `u`-preimages of
the four corners and of `u(a), u(b)`, together with the polygonal crosscut `P` from `a` to
`b`. -/
noncomputable def sourceHex {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) : HexData where
  pos := fun i => w (tgtPos α β i)
  outer := fun i t => w (tgtOuter α β i t)
  chordParam := sp
  injective_pos := fun i j h =>
    injective_tgtPos hα hβ
      (hw.injOn_inv (tgtPos_mem_modelCurve hα hβ i) (tgtPos_mem_modelCurve hα hβ j) h)
  continuousOn_outer := fun i =>
    hw.continuousOn_inv.comp AffineMap.lineMap_continuous.continuousOn
      fun t ht => tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
  injOn_outer := fun i =>
    hw.injOn_inv.comp (injOn_lineMap (tgtPos_succ_ne hα hβ i))
      fun t ht => tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
  outer_zero := fun i => congrArg w (AffineMap.lineMap_apply_zero _ _)
  outer_one := fun i => congrArg w (AffineMap.lineMap_apply_one _ _)
  continuousOn_chord := hspc
  injOn_chord := hspi
  chord_zero := hsp0
  chord_one := hsp1
  outer_meet := by
    rintro i j hij z ⟨⟨s, hs, rfl⟩, t, ht, hzt⟩
    -- the two preimages lie on `S`, where `w` is injective, so they coincide
    have hsm : tgtOuter α β i s ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ i ⟨s, hs, rfl⟩
    have htm : tgtOuter α β j t ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ j ⟨t, ht, rfl⟩
    have heq : tgtOuter α β j t = tgtOuter α β i s := hw.injOn_inv htm hsm hzt
    obtain ⟨h₁, h₂⟩ := tgtOuter_meet hα hβ i j hij ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
    constructor
    · rcases h₁ with h | h
      exacts [Or.inl (congrArg w h), Or.inr (congrArg w h)]
    · rcases h₂ with h | h
      exacts [Or.inl (congrArg w h), Or.inr (congrArg w h)]
  chord_meet := by
    rintro i z ⟨hz, t, ht, rfl⟩
    by_contra hzc
    have hmem : tgtOuter α β i t ∈ modelCurve := tgtOuter_subset_modelCurve hα hβ i ⟨t, ht, rfl⟩
    exact inside_subset_compl (hspin ⟨hz, hzc⟩) (hw.mapsTo_inv hmem)

@[simp] theorem sourceHex_pos {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).pos = fun i => w (tgtPos α β i) := rfl

@[simp] theorem sourceHex_chordParam {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).chordParam = sp := rfl

/-- **The source outer cycle is exactly `C`.** -/
theorem sourceHex_outerArcs {u w : Plane → Plane} {sp : ℝ → Plane}
    (hw : IsSetHomeoOn u w C modelCurve) (hα : |α| < 1) (hβ : |β| < 1)
    (hspc : ContinuousOn sp I) (hspi : InjOn sp I)
    (hsp0 : sp 0 = w (tgtPos α β 1)) (hsp1 : sp 1 = w (tgtPos α β 4))
    (hspin : sp '' I \ {w (tgtPos α β 1), w (tgtPos α β 4)} ⊆ inside C) :
    (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).outerArcs = C := by
  have : (sourceHex hw hα hβ hspc hspi hsp0 hsp1 hspin).outerArcs =
      w '' (⋃ i : Fin 6, tgtOuter α β i '' I) := by
    rw [Set.image_iUnion]
    refine Set.iUnion_congr fun i => ?_
    rw [← Set.image_comp]
    rfl
  rw [this, iUnion_tgtOuter hα hβ, hw.image_inv_eq]


/-! ### The skeleton homeomorphism

`g` is `u` on `C` and a chosen homeomorphism `P → [u(a), u(b)]` on the crosscut. The chosen
homeomorphism is the one that matches the parameters: `sp t ↦ [u(a), u(b)](t)`. The two
definitions agree at `a` and `b`, which is where `C` and `P` meet, so the pasting lemma applies
to the two closed pieces of the skeleton. -/

/-- A continuous injection of a compact set has a continuous inverse on its image. Stated for
the set-level `Function.invFunOn`, which is what a parametrized arc has to be inverted with. -/
theorem continuousOn_invFunOn_image {f : ℝ → Plane} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro F hF
  refine ⟨f '' (F ∩ s), (hs.inter_left hF).image_of_continuousOn (hf.mono inter_subset_right)
    |>.isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hx] at hy
    exact ⟨⟨x, ⟨hy, hx⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨x, ⟨hxF, hxs⟩, rfl⟩, -⟩
    exact ⟨by rw [mem_preimage, hinj.leftInvOn_invFunOn hxs]; exact hxF, ⟨x, hxs, rfl⟩⟩

/-! ### The initial matched pair, bundled

`InitialData C` is the data `prop:initial-pair` produces before any of its conclusions are
drawn: the boundary homeomorphism `u` with its inverse `w`, the two abscissae `xa, xb` of
`u(a)` and `u(b)` on the two opposite sides, and the polygonal crosscut as a parametrization.
Both realizations, the skeleton homeomorphism, and every conclusion below are functions of
it. -/

/-- The data of an initial matched pair over the Jordan curve `C`. -/
structure InitialData (C : Set Plane) where
  /-- The boundary homeomorphism `u : C → S` of the blueprint. -/
  u : Plane → Plane
  /-- Its inverse. -/
  w : Plane → Plane
  /-- `u` maps `C` homeomorphically onto the model curve. -/
  homeo : IsSetHomeoOn u w C modelCurve
  /-- `C` is a Jordan curve. -/
  curve : IsJordanCurve C
  /-- The abscissa of `u(a)` on the top side. -/
  xa : ℝ
  /-- The abscissa of `u(b)` on the bottom side. -/
  xb : ℝ
  /-- `u(a)` is interior to the top side. -/
  abs_xa : |xa| < 1
  /-- `u(b)` is interior to the bottom side — the *opposite* side. -/
  abs_xb : |xb| < 1
  /-- The crosscut, as a parametrization. -/
  cross : ℝ → Plane
  /-- The crosscut is drawn continuously. -/
  continuousOn_cross : ContinuousOn cross I
  /-- The crosscut is simple. -/
  injOn_cross : InjOn cross I
  /-- The crosscut starts at `a`. -/
  cross_zero : cross 0 = w (tgtPos xa xb 1)
  /-- The crosscut ends at `b`. -/
  cross_one : cross 1 = w (tgtPos xa xb 4)
  /-- Every other point of the crosscut is inside `C` — `lem:accessible-endpoints`. -/
  cross_inside : cross '' I \ {w (tgtPos xa xb 1), w (tgtPos xa xb 4)} ⊆ inside C
  /-- The crosscut is polygonal. -/
  polygonal_cross : IsPolygonal (cross '' I)

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-- The first chosen boundary point, `a = u⁻¹(xa, 1)`. -/
def a : Plane := d.w (tgtPos d.xa d.xb 1)

/-- The second chosen boundary point, `b = u⁻¹(xb, -1)`. -/
def b : Plane := d.w (tgtPos d.xa d.xb 4)

/-- The polygonal crosscut `P`, as a set. -/
def crossSet : Set Plane := d.cross '' I

/-- **The source realization data.** -/
noncomputable def src : HexData :=
  sourceHex d.homeo d.abs_xa d.abs_xb d.continuousOn_cross d.injOn_cross d.cross_zero
    d.cross_one d.cross_inside

/-- **The target realization data.** -/
noncomputable def tgt : HexData := targetHex d.abs_xa d.abs_xb

/-- **The source realization of `initialStructure`** — `Γ` of `prop:initial-pair`. -/
noncomputable def sourceRealization : initialStructure.Realization := d.src.realization

/-- **The target realization of `initialStructure`** — `Γ'` of `prop:initial-pair`. -/
noncomputable def targetRealization : initialStructure.Realization := d.tgt.realization

@[simp] theorem src_pos_one : d.src.pos 1 = d.a := rfl

@[simp] theorem src_pos_four : d.src.pos 4 = d.b := rfl

@[simp] theorem src_chordSet : d.src.chordSet = d.crossSet := rfl

@[simp] theorem tgt_pos_one : d.tgt.pos 1 = Plane.mk d.xa 1 := rfl

@[simp] theorem tgt_pos_four : d.tgt.pos 4 = Plane.mk d.xb (-1) := rfl

theorem tgt_chordSet : d.tgt.chordSet = segment ℝ (Plane.mk d.xa 1) (Plane.mk d.xb (-1)) :=
  tgtChord_image d.xa d.xb

theorem src_outerArcs : d.src.outerArcs = C :=
  sourceHex_outerArcs d.homeo d.abs_xa d.abs_xb d.continuousOn_cross d.injOn_cross d.cross_zero
    d.cross_one d.cross_inside

theorem tgt_outerArcs : d.tgt.outerArcs = modelCurve := targetHex_outerArcs d.abs_xa d.abs_xb

theorem a_mem : d.a ∈ C := d.homeo.mapsTo_inv (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)

theorem b_mem : d.b ∈ C := d.homeo.mapsTo_inv (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)

theorem u_a : d.u (d.w (tgtPos d.xa d.xb 1)) = tgtPos d.xa d.xb 1 :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1)

theorem u_b : d.u (d.w (tgtPos d.xa d.xb 4)) = tgtPos d.xa d.xb 4 :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4)

@[simp] theorem u_apply_a : d.u d.a = Plane.mk d.xa 1 := d.u_a

@[simp] theorem u_apply_b : d.u d.b = Plane.mk d.xb (-1) := d.u_b

theorem sourceRealization_skeletonSet : d.sourceRealization.skeletonSet = C ∪ d.crossSet := by
  rw [sourceRealization, HexData.skeletonSet_realization, d.src_outerArcs]
  rfl

theorem targetRealization_skeletonSet :
    d.targetRealization.skeletonSet = modelCurve ∪ d.tgt.chordSet := by
  rw [targetRealization, HexData.skeletonSet_realization, d.tgt_outerArcs]

/-! #### `a` and `b` are the only points the crosscut shares with the curve -/

theorem cross_mem_curve_iff {t : ℝ} (ht : t ∈ I) : d.cross t ∈ C ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    refine inside_subset_compl (d.cross_inside ⟨⟨t, ht, rfl⟩, ?_⟩) hmem
    rintro (h | h)
    · exact hcon.1 (d.injOn_cross ht zero_mem_I (h.trans d.cross_zero.symm))
    · exact hcon.2 (d.injOn_cross ht one_mem_I (h.trans d.cross_one.symm))
  · rintro (rfl | rfl)
    · rw [d.cross_zero]; exact d.a_mem
    · rw [d.cross_one]; exact d.b_mem

/-! #### The map -/

open Classical in
/-- The skeleton map: `u` on the curve, and the parameter-matching homeomorphism from the
crosscut onto the straight chord. -/
noncomputable def skelMap (d : InitialData C) : Plane → Plane :=
  fun x => if x ∈ C then d.u x else tgtChord d.xa d.xb (Function.invFunOn d.cross I x)

open Classical in
/-- Its inverse: `w` on the model curve, and the parameter-matching homeomorphism back. -/
noncomputable def skelInv (d : InitialData C) : Plane → Plane :=
  fun y => if y ∈ modelCurve then d.w y else
    d.cross (Function.invFunOn (tgtChord d.xa d.xb) I y)

theorem skelMap_of_mem {x : Plane} (hx : x ∈ C) : d.skelMap x = d.u x := by
  simp only [skelMap, if_pos hx]

theorem skelInv_of_mem {y : Plane} (hy : y ∈ modelCurve) : d.skelInv y = d.w y := by
  simp only [skelInv, if_pos hy]

/-- **The skeleton map matches parameters on the crosscut.** -/
theorem skelMap_cross {t : ℝ} (ht : t ∈ I) :
    d.skelMap (d.cross t) = tgtChord d.xa d.xb t := by
  by_cases hmem : d.cross t ∈ C
  · rcases (d.cross_mem_curve_iff ht).1 hmem with rfl | rfl
    · rw [d.skelMap_of_mem hmem, d.cross_zero, d.u_a]
      simp [tgtChord]
    · rw [d.skelMap_of_mem hmem, d.cross_one, d.u_b]
      simp [tgtChord]
  · simp only [skelMap, if_neg hmem, d.injOn_cross.leftInvOn_invFunOn ht]

theorem tgtChord_mem_modelCurve_iff {t : ℝ} (ht : t ∈ I) :
    tgtChord d.xa d.xb t ∈ modelCurve ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    refine openSegment_chord_notMem_modelCurve d.abs_xa d.abs_xb _ ?_ hmem
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hcon.1), lt_of_le_of_ne ht.2 hcon.2⟩, rfl⟩
  · rintro (rfl | rfl)
    · simp only [tgtChord, AffineMap.lineMap_apply_zero]
      exact tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1
    · simp only [tgtChord, AffineMap.lineMap_apply_one]
      exact tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4

theorem injOn_tgtChord : InjOn (tgtChord d.xa d.xb) I :=
  d.tgt.injOn_chord

theorem skelInv_tgtChord {t : ℝ} (ht : t ∈ I) :
    d.skelInv (tgtChord d.xa d.xb t) = d.cross t := by
  by_cases hmem : tgtChord d.xa d.xb t ∈ modelCurve
  · rcases (d.tgtChord_mem_modelCurve_iff ht).1 hmem with rfl | rfl
    · rw [d.skelInv_of_mem hmem, d.cross_zero]
      simp [tgtChord]
    · rw [d.skelInv_of_mem hmem, d.cross_one]
      simp [tgtChord]
  · simp only [skelInv, if_neg hmem, d.injOn_tgtChord.leftInvOn_invFunOn ht]

/-! #### Continuity and inversion -/

theorem continuousOn_skelMap : ContinuousOn d.skelMap d.sourceRealization.skeletonSet := by
  rw [d.sourceRealization_skeletonSet]
  refine Plane.continuousOn_union_of_isClosed d.curve.isClosed ?_ ?_ ?_
  · exact (isCompact_I.image_of_continuousOn d.continuousOn_cross).isClosed
  · exact d.homeo.continuousOn.congr fun x hx => d.skelMap_of_mem hx
  · refine ContinuousOn.congr (f := fun x => tgtChord d.xa d.xb
      (Function.invFunOn d.cross I x)) ?_ ?_
    · refine AffineMap.lineMap_continuous.continuousOn.comp
        (continuousOn_invFunOn_image isCompact_I d.continuousOn_cross d.injOn_cross)
        fun x hx => Function.invFunOn_mem (by rcases hx with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
    · rintro x ⟨t, ht, rfl⟩
      simp only [d.skelMap_cross ht, d.injOn_cross.leftInvOn_invFunOn ht]

theorem continuousOn_skelInv : ContinuousOn d.skelInv d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet]
  refine Plane.continuousOn_union_of_isClosed isCompact_modelCurve.isClosed ?_ ?_ ?_
  · rw [d.tgt_chordSet]
    exact (isCompact_segment _ _).isClosed
  · exact d.homeo.continuousOn_inv.congr fun y hy => d.skelInv_of_mem hy
  · rw [d.tgt_chordSet, ← tgtChord_image]
    refine ContinuousOn.congr (f := fun y => d.cross (Function.invFunOn (tgtChord d.xa d.xb) I y))
      ?_ ?_
    · refine d.continuousOn_cross.comp
        (continuousOn_invFunOn_image isCompact_I AffineMap.lineMap_continuous.continuousOn
          d.injOn_tgtChord)
        fun y hy => Function.invFunOn_mem (by rcases hy with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
    · rintro y ⟨t, ht, rfl⟩
      simp only [d.skelInv_tgtChord ht, d.injOn_tgtChord.leftInvOn_invFunOn ht]

theorem leftInvOn_skel :
    LeftInvOn d.skelInv d.skelMap d.sourceRealization.skeletonSet := by
  rw [d.sourceRealization_skeletonSet]
  rintro x (hx | ⟨t, ht, rfl⟩)
  · rw [d.skelMap_of_mem hx, d.skelInv_of_mem (d.homeo.mapsTo hx), d.homeo.leftInvOn hx]
  · rw [d.skelMap_cross ht, d.skelInv_tgtChord ht]

theorem rightInvOn_skel :
    RightInvOn d.skelInv d.skelMap d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet, d.tgt_chordSet, ← tgtChord_image]
  rintro y (hy | ⟨t, ht, rfl⟩)
  · rw [d.skelInv_of_mem hy, d.skelMap_of_mem (d.homeo.mapsTo_inv hy), d.homeo.rightInvOn hy]
  · rw [d.skelInv_tgtChord ht, d.skelMap_cross ht]


/-- **The skeleton homeomorphism `g` of `def:matched-pair`.** It is `u` on the outer cycle
(clause 2), and on the crosscut it is the chosen homeomorphism `P → [u(a), u(b)]` matching
endpoints (clause 3); clause 1 is definitional here, both realizations being realizations of
the one `initialStructure`. -/
noncomputable def skeletonHomeo :
    CellStructure.SkeletonHomeo d.sourceRealization d.targetRealization where
  toFun := d.skelMap
  invFun := d.skelInv
  continuousOn_toFun := d.continuousOn_skelMap
  continuousOn_invFun := d.continuousOn_skelInv
  leftInvOn := d.leftInvOn_skel
  rightInvOn := d.rightInvOn_skel
  pos_apply := by
    rintro _ ⟨i, rfl⟩
    have hm : tgtPos d.xa d.xb i ∈ modelCurve := tgtPos_mem_modelCurve d.abs_xa d.abs_xb i
    change d.skelMap (d.w (tgtPos d.xa d.xb i)) = tgtPos d.xa d.xb i
    rw [d.skelMap_of_mem (d.homeo.mapsTo_inv hm), d.homeo.rightInvOn hm]
  edgeArc_image := by
    intro e he
    replace he : e ∈ InitialCell.edges := he
    rcases he with ⟨i, rfl⟩ | rfl
    · change d.skelMap '' ((fun t => d.w (tgtOuter d.xa d.xb i t)) '' I) =
        tgtOuter d.xa d.xb i '' I
      rw [← Set.image_comp]
      refine Set.image_congr fun t ht => ?_
      have hm : tgtOuter d.xa d.xb i t ∈ modelCurve :=
        tgtOuter_subset_modelCurve d.abs_xa d.abs_xb i ⟨t, ht, rfl⟩
      change d.skelMap (d.w (tgtOuter d.xa d.xb i t)) = tgtOuter d.xa d.xb i t
      rw [d.skelMap_of_mem (d.homeo.mapsTo_inv hm), d.homeo.rightInvOn hm]
    · change d.skelMap '' (d.cross '' I) = tgtChord d.xa d.xb '' I
      rw [← Set.image_comp]
      exact Set.image_congr fun t ht => d.skelMap_cross ht

@[simp] theorem skeletonHomeo_toFun : d.skeletonHomeo.toFun = d.skelMap := rfl

/-- **Clause 2 of `def:matched-pair`: `g = u` on `C`.** -/
theorem skeletonHomeo_eq_u {x : Plane} (hx : x ∈ C) : d.skeletonHomeo.toFun x = d.u x :=
  d.skelMap_of_mem hx


/-! ### The two 2-cells really are the two sides of the crosscut

`thm:general-crosscut` applied on each side. On the source side the collar hypothesis
`HasArcCollars (inside C) P` is carried, since `P` is an arbitrary polygonal crosscut; on the
target side the chord is straight, so `Schoenflies.hasArcCollars_segment` discharges it
outright. -/

/-- **`P` is a crosscut of `D`** — the configuration `thm:general-crosscut` consumes. -/
theorem isCrosscut : IsCrosscut C d.crossSet d.a d.b where
  curve := d.curve
  arc := d.src.isArcBetween_chordSet
  polygonal := d.polygonal_cross
  left_mem := d.a_mem
  right_mem := d.b_mem
  sdiff_subset := d.cross_inside

/-- **`A₁, A₂` are the two arcs of `C` from `a` to `b`.** They are the geometric unions of the
two boundary edge-paths `B₁, B₂` of the abstract structure. -/
theorem isCutPair : IsCutPair C d.a d.b (d.src.arcOf false) (d.src.arcOf true) where
  fst := d.src.arcOf_false_isArcBetween
  snd := d.src.arcOf_true_isArcBetween.reverse
  union_eq := by rw [d.src.arcOf_union, d.src_outerArcs]
  inter_eq := d.src.arcOf_inter

/-! #### The target side -/

/-- The open square is the bounded region of the model curve: it is open, convex and bounded,
and its frontier is contained in `S`. -/
theorem openSquare_subset_inside_modelCurve : Plane.openSquare 0 1 ⊆ inside modelCurve := by
  have hbdd : Bornology.IsBounded (Plane.openSquare 0 1) := by
    refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2)).subset fun x hx => ?_
    have hx1 : Plane.supNorm x < 1 := mem_openSquare_zero_one.1 hx
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have := Plane.norm_le_sqrt_two_mul_supNorm x
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [Plane.supNorm_nonneg x]
  have hsub : Plane.openSquare 0 1 ⊆ modelCurveᶜ := fun x hx hxm =>
    absurd (mem_openSquare_zero_one.1 hx) (by rw [show Plane.supNorm x = 1 from hxm]; norm_num)
  have hfr : frontier (Plane.openSquare 0 1) ∩ modelCurveᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hz'⟩
    refine hz' ?_
    have hzc : z ∈ Plane.closedSquare 0 1 :=
      (Plane.isClosed_closedSquare 0 1).closure_subset
        (closure_mono (fun x hx => mem_closedSquare_zero_one.2
          (mem_openSquare_zero_one.1 hx).le) hz.1)
    have hzo : z ∉ Plane.openSquare 0 1 := by
      rw [(Plane.isOpen_openSquare 0 1).frontier_eq] at hz
      exact hz.2
    exact le_antisymm (mem_closedSquare_zero_one.1 hzc)
      (not_lt.1 fun h => hzo (mem_openSquare_zero_one.2 h))
  intro z hz
  refine ⟨hsub hz, ?_⟩
  rw [Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare 0 1)
    (Plane.convex_openSquare 0 1).isPreconnected hsub hfr hz]
  exact hbdd

/-- **The straight chord is a crosscut of the open square.** -/
theorem isCrosscutTarget :
    IsCrosscut modelCurve (d.tgt.chordSet) (Plane.mk d.xa 1) (Plane.mk d.xb (-1)) where
  curve := isJordanCurve_modelCurve
  arc := d.tgt.isArcBetween_chordSet
  polygonal := by rw [d.tgt_chordSet]; exact isPolygonal_segment _ _
  left_mem := tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1
  right_mem := tgtPos_mem_modelCurve d.abs_xa d.abs_xb 4
  sdiff_subset := by
    rw [d.tgt_chordSet]
    rintro z ⟨hz, hzne⟩
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact absurd (Or.inl rfl) hzne
    · exact absurd (Or.inr rfl) hzne
    · exact openSquare_subset_inside_modelCurve (mem_openSquare_zero_one.2
        (openSegment_chord_supNorm_lt d.abs_xa d.abs_xb _ hz))

/-- **`u(A₁), u(A₂)` are the two arcs of `S` from `u(a)` to `u(b)`.** -/
theorem isCutPairTarget :
    IsCutPair modelCurve (Plane.mk d.xa 1) (Plane.mk d.xb (-1))
      (d.tgt.arcOf false) (d.tgt.arcOf true) where
  fst := d.tgt.arcOf_false_isArcBetween
  snd := d.tgt.arcOf_true_isArcBetween.reverse
  union_eq := by rw [d.tgt.arcOf_union, d.tgt_outerArcs]
  inter_eq := d.tgt.arcOf_inter


end InitialData

/-! ### `prop:initial-pair`: an initial matched pair exists

The two open corner arcs the blueprint chooses `a` and `b` from are the relative interiors of
two *opposite* sides of the square, pulled back by `u`. They are relatively open in `C` and
nonempty, so the countable dense set of strongly accessible points of
`prop:countable-strong-access` meets both; `lem:tangent-cone` and `lem:accessible-endpoints`
then supply the polygonal crosscut. -/

/-- The relative interior of the top side of the square. -/
def openTop : Set Plane := {p : Plane | |p 0| < 1 ∧ 0 < p 1} ∩ modelCurve

/-- The relative interior of the bottom side — the side *opposite* the top one. -/
def openBottom : Set Plane := {p : Plane | |p 0| < 1 ∧ p 1 < 0} ∩ modelCurve

theorem isOpen_topBand : IsOpen {p : Plane | |p 0| < 1 ∧ 0 < p 1} := by
  have h1 : IsOpen {p : Plane | |p 0| < 1} :=
    isOpen_lt (continuous_abs.comp (Plane.continuous_coord 0)) continuous_const
  have h2 : IsOpen {p : Plane | 0 < p 1} := isOpen_lt continuous_const (Plane.continuous_coord 1)
  exact h1.inter h2

theorem isOpen_bottomBand : IsOpen {p : Plane | |p 0| < 1 ∧ p 1 < 0} := by
  have h1 : IsOpen {p : Plane | |p 0| < 1} :=
    isOpen_lt (continuous_abs.comp (Plane.continuous_coord 0)) continuous_const
  have h2 : IsOpen {p : Plane | p 1 < 0} := isOpen_lt (Plane.continuous_coord 1) continuous_const
  exact h1.inter h2

theorem mem_openTop {p : Plane} : p ∈ openTop ↔ p 1 = 1 ∧ |p 0| < 1 := by
  constructor
  · rintro ⟨⟨h0, hpos⟩, hm⟩
    have hmax : max |p 0| |p 1| = 1 := hm
    refine ⟨?_, h0⟩
    rcases max_choice |p 0| |p 1| with h | h
    · exact absurd (h ▸ hmax) (ne_of_lt h0)
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 (h ▸ hmax) with h' | h'
      · exact h'
      · linarith
  · rintro ⟨h1, h0⟩
    refine ⟨⟨h0, by rw [h1]; norm_num⟩, ?_⟩
    change max |p 0| |p 1| = 1
    rw [h1, show |(1:ℝ)| = 1 by norm_num]
    exact max_eq_right h0.le

theorem mem_openBottom {p : Plane} : p ∈ openBottom ↔ p 1 = -1 ∧ |p 0| < 1 := by
  constructor
  · rintro ⟨⟨h0, hneg⟩, hm⟩
    have hmax : max |p 0| |p 1| = 1 := hm
    refine ⟨?_, h0⟩
    rcases max_choice |p 0| |p 1| with h | h
    · exact absurd (h ▸ hmax) (ne_of_lt h0)
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 (h ▸ hmax) with h' | h'
      · linarith
      · exact h'
  · rintro ⟨h1, h0⟩
    refine ⟨⟨h0, by rw [h1]; norm_num⟩, ?_⟩
    change max |p 0| |p 1| = 1
    rw [h1, show |(-1:ℝ)| = 1 by norm_num]
    exact max_eq_right h0.le

theorem openTop_nonempty : (openTop).Nonempty :=
  ⟨Plane.mk 0 1, mem_openTop.2 ⟨rfl, by norm_num⟩⟩

theorem openBottom_nonempty : (openBottom).Nonempty :=
  ⟨Plane.mk 0 (-1), mem_openBottom.2 ⟨rfl, by norm_num⟩⟩

/-- A dense subset of `C` meets every nonempty relatively open subset of `C`. -/
theorem exists_mem_inter_of_dense {C A U W : Set Plane} (hAC : A ⊆ C) (hdense : C ⊆ closure A)
    (hW : IsOpen W) (hU : U = W ∩ C) (hne : U.Nonempty) : (A ∩ U).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  have hzC : z ∈ C := (hU ▸ hz).2
  have hzW : z ∈ W := (hU ▸ hz).1
  obtain ⟨y, hyW, hyA⟩ := _root_.mem_closure_iff.1 (hdense hzC) W hW hzW
  exact ⟨y, hyA, hU ▸ ⟨hyW, hAC hyA⟩⟩


end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPairFixed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos
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

/-! ### Two missing `HexData` facts

The two boundary arcs are part of the outer cycle, and both are polygonal as soon as the six
outer edges are. The second is the clause of `def:admissible-graph` that the target realization
has to satisfy and the source one does not. -/

namespace HexData

variable (H : HexData)

-- Deliberately *not* `@[simp]`: `HexData.arcOf_union`, `.arcOf_inter` and the two labelling
-- theorems are all stated about `arcOf`, and a global unfolding lemma would take `simp` apart
-- underneath them.
theorem arcOf_false :
    H.arcOf false = H.outer 1 '' I ∪ (H.outer 2 '' I ∪ H.outer 3 '' I) := rfl

theorem arcOf_true :
    H.arcOf true = H.outer 4 '' I ∪ (H.outer 5 '' I ∪ H.outer 0 '' I) := rfl

/-- The vertex an outer edge ends at, named. -/
theorem pos_mem_outer_of_succ {i j : Fin 6} (h : i + 1 = j) : H.pos j ∈ H.outer i '' I := by
  subst h; exact H.pos_succ_mem_outer i

end HexData

/-! ### `initBoundary` really is the boundary walk

`CellStructure.boundary` is documented as a raw datum: nothing in the record forces it to walk
anywhere. For `initialStructure` it does. Both lists are *closed* walks of `initSkel`, and the
cells they run through are exactly the `faceCells` that `initSub` declares to be subcells of the
corresponding 2-cell — so the base value of `≼_abs` is not an independent choice. -/

/-- An outer edge links its two consecutive vertices, with the second one named. -/
theorem initSkel_isLink_edge {i j : Fin 6} (h : i + 1 = j) :
    initSkel.IsLink (.edge i) (.vert i) (.vert j) := by
  subst h; exact initSkel_isLink_ends (InitialCell.edge_mem_edges i)

/-- The chord links `a` and `b`. -/
theorem initSkel_isLink_chord : initSkel.IsLink .chord (.vert 1) (.vert 4) :=
  initSkel_isLink_ends InitialCell.chord_mem_edges

/-- Incidence in `initSkel` is membership among the two ends. -/
theorem initSkel_inc_iff {e x : InitialCell} :
    initSkel.Inc e x ↔ e ∈ InitialCell.edges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, hy⟩
    rw [initSkel_isLink] at hy
    rcases hy.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [⟨hy.1, Or.inl rfl⟩, ⟨hy.1, Or.inr rfl⟩]
  · rintro ⟨he, rfl | rfl⟩
    exacts [⟨_, initSkel_isLink_ends he⟩, ⟨_, (initSkel_isLink_ends he).symm⟩]

/-- **The cells of a 2-cell are the cells of its boundary walk.** The base value of `≼_abs`
declares `faceCells k` to be the subcells of `face k`; this says `faceCells k` is exactly the
set of edges the boundary walk takes together with the vertices it visits. -/
theorem mem_faceCells_iff {k : Bool} {c : InitialCell} :
    c ∈ faceCells k ↔
      c ∈ initBoundary (.face k) ∨ ∃ e ∈ initBoundary (.face k), initSkel.Inc e c := by
  have hedge : ∀ i j : Fin 6, i + 1 = j → ∀ x : InitialCell,
      initSkel.Inc (.edge i) x ↔ (x = .vert i ∨ x = .vert j) := by
    rintro i j rfl x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.edge_mem_edges i, h⟩⟩
  have hchord : ∀ x : InitialCell,
      initSkel.Inc .chord x ↔ (x = .vert 1 ∨ x = .vert 4) := by
    intro x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.chord_mem_edges, h⟩⟩
  cases k <;>
    simp only [faceCells, initBoundary, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
      hedge 1 2 (by decide), hedge 2 3 (by decide), hedge 3 4 (by decide),
      hedge 4 5 (by decide), hedge 5 0 (by decide), hedge 0 1 (by decide), hchord] <;>
    tauto

/-! ### The initial face-boundary cycles

The closed-walk facts above are strengthened here to the maintained data needed by
`thm:finite-transfer`: each boundary is a simple cycle of length at least three, and its cells
are exactly the strict subcells of the corresponding face. -/

/-- The complementary part of the first face boundary is a simple path. -/
theorem isPath_initBoundary_false_tail :
    initSkel.IsPath (.vert 2) [.edge 2, .edge 3, .chord] (.vert 1) := by
  refine .cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4))
      (Graph.IsPath.single initSkel_isLink_chord.symm (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

/-- The complementary part of the second face boundary is a simple path. -/
theorem isPath_initBoundary_true_tail :
    initSkel.IsPath (.vert 5) [.edge 5, .edge 0, .chord] (.vert 4) := by
  refine .cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1))
      (Graph.IsPath.single initSkel_isLink_chord (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

/-- The first declared boundary list presents a long simple cycle. -/
theorem isLongCycle_initBoundary_false :
    initSkel.IsLongCycle (.edge 1) (.vert 2) (.vert 1)
      [.edge 2, .edge 3, .chord] (.vert 3) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).symm,
    isPath_initBoundary_false_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

/-- The second declared boundary list presents a long simple cycle. -/
theorem isLongCycle_initBoundary_true :
    initSkel.IsLongCycle (.edge 4) (.vert 5) (.vert 4)
      [.edge 5, .edge 0, .chord] (.vert 0) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).symm,
    isPath_initBoundary_true_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

/-- Incidence below an initial face consists of the face itself and its declared boundary
cells. -/
theorem initSub_face_iff {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, h, hc⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases h; exact Or.inr hc
  · rintro (rfl | hc)
    · exact initSub_refl (Or.inr ⟨k, rfl⟩)
    · exact initSub_face hc

/-- A declared initial boundary has exactly the cells recorded by `faceCells`, once its
starting vertex is known to occur on the boundary. -/
theorem mem_faceCells_iff_mem_pathCells {k : Bool} {u c : InitialCell}
    (hu : ∃ e ∈ initBoundary (.face k), initSkel.Inc e u) :
    c ∈ faceCells k ↔
      c ∈ initialStructure.pathCells u (initBoundary (.face k)) := by
  rw [mem_faceCells_iff]
  simp only [CellStructure.pathCells, Set.mem_union, Set.mem_setOf_eq,
    Graph.mem_walkVertices_iff, Graph.mem_coveredVertices_iff]
  constructor
  · rintro (hc | hc)
    · exact Or.inl hc
    · exact Or.inr (Or.inr hc)
  · rintro (hc | rfl | hc)
    · exact Or.inl hc
    · exact Or.inr hu
    · exact Or.inr hc

/-- The two faces of the initial matched cellulation carry chosen simple boundary cycles. -/
theorem boundaryCycles_initialStructure : initialStructure.BoundaryCycles where
  cycle F hF := by
    obtain ⟨k, rfl⟩ := hF
    cases k
    · refine ⟨
        { face_mem := ⟨false, rfl⟩
          edge := .edge 1
          source := .vert 2
          target := .vert 1
          walk := [.edge 2, .edge 3, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_false.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 1, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).inc_left⟩
    · refine ⟨
        { face_mem := ⟨true, rfl⟩
          edge := .edge 4
          source := .vert 5
          target := .vert 4
          walk := [.edge 5, .edge 0, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_true.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 4, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).inc_left⟩

/-! ### The anchor set `𝒜`

`prop:countable-strong-access` produces a countable dense set of strongly accessible points of
`C`; the blueprint then *fixes* it for the whole construction (tex 1418) and every later stage
draws its new boundary vertices from it. Fixing it means it is data, so it is a structure, and
`prop:initial-pair` takes it as an argument rather than producing its own. -/

variable {C : Set Plane}

/-- **The anchor set `𝒜`** of tex 1403–1418: a countable dense subset of the Jordan curve `C`
every point of which is strongly accessible from the Jordan domain `D`. -/
structure AnchorSet (C : Set Plane) where
  /-- The points of `𝒜`. -/
  carrier : Set Plane
  /-- They lie on the curve. -/
  subset_curve : carrier ⊆ C
  /-- There are countably many. -/
  countable : carrier.Countable
  /-- Each is strongly accessible from the inside — `def:strong-accessibility`. -/
  stronglyAccessible : ∀ p ∈ carrier, StronglyAccessible (inside C) p
  /-- They are dense in the curve. -/
  dense : C ⊆ closure carrier

namespace AnchorSet

variable (A : AnchorSet C)

/-- An anchor is polygonally accessible, the hypothesis `lem:accessible-endpoints` consumes. -/
theorem polyAccessible {p : Plane} (hp : p ∈ A.carrier) : PolyAccessible (inside C) p :=
  (A.stronglyAccessible p hp).polyAccessible

end AnchorSet

/-! ### The initial matched pair, anchored

The clause of `prop:initial-pair` that `InitialData` drops. It is recorded as an extension
rather than as a side theorem so that a consumer holding an initial pair holds the anchoring
too; the integrator merging this file into `InitialPair.lean` should move the two fields into
`InitialData` itself. -/

/-- **The initial matched pair with the anchor clause of `prop:initial-pair`**: the two chosen
boundary points are points of the fixed set `𝒜`. -/
structure AnchoredInitialData (C : Set Plane) (A : AnchorSet C) extends InitialData C where
  /-- `a ∈ 𝒜`. -/
  a_mem_anchors : toInitialData.a ∈ A.carrier
  /-- `b ∈ 𝒜`. -/
  b_mem_anchors : toInitialData.b ∈ A.carrier

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

/-! ### The matched labelling

`def:matched-pair` clause 1 asks that "the two distinguished outer cycles correspond". On the
initial pair this is not automatic from the abstract structure alone: `arcOf` is read off the
*geometry* of each realization, so the two 2-cell labellings — `source_closure_cell_inter'` and
`target_closure_cell_inter'` — are made independently. They correspond because the source
outer edges are, by construction, the `w`-images of the target ones. -/

theorem tgt_outer (i : Fin 6) : d.tgt.outer i = tgtOuter d.xa d.xb i := rfl

/-! ### `def:admissible-graph` for the target: every edge is polygonal -/

/-- Each target outer edge is a straight segment, hence polygonal. -/
theorem isPolygonal_tgt_outer (i : Fin 6) : IsPolygonal (d.tgt.outer i '' I) := by
  rw [d.tgt_outer i, tgtOuter_image]
  exact isPolygonal_segment _ _

/-- **Every edge of the target realization is polygonal** — the clause of
`def:admissible-graph` for an admissible graph in `Q` that `InitialPair.lean` leaves unstated. -/
theorem isPolygonal_tgt_edgeArc {e : InitialCell} (he : e ∈ E(initSkel)) :
    IsPolygonal (Graph.edgeArc d.tgt.draw e) := by
  rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
  · rw [HexData.edgeArc_edge]
    exact d.isPolygonal_tgt_outer i
  · rw [HexData.edgeArc_chord]
    change IsPolygonal d.tgt.chordSet
    rw [d.tgt_chordSet]
    exact isPolygonal_segment _ _

end InitialData

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialGenerated
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-! ### The cells of the initial structure, and `≼_abs`

`initialStructure` declares every one of `InitialCell`'s four *named* constructors a cell. The
fifth, `InitialCell.aux`, is the spare supply of fresh names that `def:generated-structure`
needs and that `thm:finite-transfer` asks for as `[Infinite γ]`; no `aux` name is a cell.

`recOnCells` is the shape every clause of assertion (i) below uses: case analysis on a *cell*,
with the spare names ruled out by the membership hypothesis the clause already carries. -/

/-- The spare names are not cells: `cells` is `vertices ∪ edges ∪ faces`, and each of those is a
range of one of the four named constructors. -/
theorem aux_notMem_cells (n : ℕ) : (InitialCell.aux n) ∉ initialStructure.cells :=
  aux_notMem_cellNames n

/-- The four named constructors are cell names. -/
theorem mem_cellNames_of_vert (i : Fin 6) : (InitialCell.vert i) ∈ cellNames :=
  Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cellNames_of_edge (i : Fin 6) : (InitialCell.edge i) ∈ cellNames :=
  Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cellNames_chord : InitialCell.chord ∈ cellNames := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cellNames_of_face (k : Bool) : (InitialCell.face k) ∈ cellNames := Or.inr ⟨k, rfl⟩

/-- A `face` name is never a 0-cell or a 1-cell. -/
theorem face_notMem_faceCells {k l : Bool} : InitialCell.face k ∉ faceCells l := by
  cases l <;> simp [faceCells]

/-- The subcells of a 0-cell are itself alone. -/
theorem initSub_iff_vert {i : Fin 6} {c : InitialCell} :
    initSub c (.vert i) ↔ c = .vert i := by
  refine ⟨fun h => ?_, fun h => by subst h; exact initSub_refl (mem_cellNames_of_vert i)⟩
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, -⟩
  · exact h
  · exact absurd h (by simp [InitialCell.edges])
  · exact absurd hk (by simp)

/-- The subcells of an outer 1-cell are itself and its two ends. -/
theorem initSub_iff_edge {i : Fin 6} {c : InitialCell} :
    initSub c (.edge i) ↔ c = .edge i ∨ c = .vert i ∨ c = .vert (i + 1) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl (mem_cellNames_of_edge i)
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).1
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).2

/-- The subcells of the crosscut are itself and its two ends. -/
theorem initSub_iff_chord {c : InitialCell} :
    initSub c .chord ↔ c = .chord ∨ c = .vert 1 ∨ c = .vert 4 := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl mem_cellNames_chord
    · exact (initSub_ends InitialCell.chord_mem_edges).1
    · exact (initSub_ends InitialCell.chord_mem_edges).2

/-- The subcells of a 2-cell are itself together with the cells of its boundary walk. -/
theorem initSub_iff_face {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact Or.inr hmem
  · rintro (rfl | h)
    · exact initSub_refl (mem_cellNames_of_face k)
    · exact initSub_face h

/-! ### The combinatorial invariants at the base

`Schoenflies.GeneratedStructure.combInvariants` propagates `lem:cellulation-invariants` (iii),
(v), (vi) and abstract (viii) along the two elementary operations *given the base case*. This is
the base case. Assertion (vi) is `Schoenflies.outerEdgeUniqueFace_initialStructure`, already on
`main`; the other seven clauses are read off `initSub`. -/

/-! ### The open cells of a `HexData`

Everything assertion (i) needs about the fifteen realized open cells, stated for an arbitrary
`HexData` so that the source and the target realization are served by one proof. Nothing in this
section mentions the crosscut configuration; that enters only for the two 2-cells. -/

/-! ### The closed square, as a domain

`GeneratedPair` asks for the *closed* target domain. `Schoenflies.inside_modelCurve` identifies
the Jordan domain of `S` with the open square, so the closed domain `S ∪ Int(S)` is literally
`Q = [-1,1]²`. -/

/-! ### The initial pair is a `GeneratedPair`

Both realizations are instances of the two `HexData` theorems above; all that is left is to
present the hypotheses in the shape they take, which on the source side means rewriting
`d.src.outerArcs` to `C` and on the target side `d.tgt.outerArcs` to `S`. -/

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
-- module Solutions.Q146_CD.RealizeSubdiv
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing an edge subdivision

`Schoenflies/GeneratedStructure.lean` performs the *abstract* edge subdivision
(`CellStructure.subdivideEdge`) and states what it means for a realization of the subdivided
structure to refine a realization of the old one (`SubdivData.IsRefinement`);
`Schoenflies/CellulationInvariants.lean` propagates assertions (i), (iv) and (vii) across such a
refinement. Nothing built such a realization. This module does.

The construction is the blueprint's own sentence — "the corresponding point is inserted into the
corresponding edge using the edge parametrization" — made into data: pick a parameter
`t ∈ (0,1)`, put the new 0-cell at `R.drawing d.edge t`, and draw the two new 1-cells with the
two halves of the old parametrization, each rescaled to `[0,1]`.

## The orientation of the drawn edge

`IsDrawing.edge_param` is deliberately orientation-free: it says
`G.IsLink e (drawing e 0) (drawing e 1)`, so `drawing d.edge 0` may be *either* `pos d.left` or
`pos d.right`. But `d.newEdge₁` runs from `d.left` to `d.newVertex` by definition of
`subdivideEdge`, so which half of the parametrization draws it is not fixed in advance.

Assuming `drawing d.edge 0 = pos d.left` would be a false hypothesis for half of all inputs, and
the caller cannot repair it (swapping `d.left` with `d.right` in the `SubdivData` also swaps the
two new edge *names*, producing a different abstract structure). So the orientation is read off
instead: `SubdivData.leftParam` is the endpoint parameter, `0` or `1`, at which the drawn edge
sits at `d.left`. Every statement below is orientation-free; only the two lemmas
`SubdivData.drawing_leftParam` and `SubdivData.drawing_rightParam` look inside.

Because of that, the construction is phrased with `Schoenflies.subarc` — the general affine
reparametrization already on `main` — rather than with `firstHalf` / `secondHalf`, which are the
two halves in the standard orientation and are recorded here as the named special case.

## No side conditions

`SubdivData.realize` takes no geometric hypothesis beyond `t ∈ Ioo 0 1`. Everything else it
needs — that `d.edge` is drawn, injectively and continuously, between the positions of `d.left`
and `d.right`, and that an interior point of a drawn edge is not a vertex — is already carried by
`CellStructure.Realization`, and is extracted here rather than assumed.

## The transported skeleton homeomorphism is not here, but it exists

**Closed, in `Schoenflies/RealizeSubdivHomeo.lean`** (`SubdivData.realizeHomeo`), on top of
`Schoenflies/ArcMonotone.lean`, which supplies the missing fact named at the end of this
section. What follows is the record of why it could not be done here.

`SkeletonHomeo.realize` is absent from *this* module. Six of its eight fields are immediate —
`skeletonSet_realize` below says the realized 1-skeleton is *literally the same set* after a
subdivision, so the map, its inverse, both continuity clauses and both inverse clauses transport
verbatim, and
`pos_apply` at the new 0-cell is the statement `g.toFun (R₁.drawing d.edge t₁) =
R₂.drawing d.edge t₂` that a caller choosing corresponding parameters supplies anyway.

What is missing is `edgeArc_image` at the two new edges: that `g` carries the *half* arc from
`R₁.pos d.left` to the new source point onto the half arc from `R₂.pos d.left` to the new target
point. This is true but is not implied by the `SkeletonHomeo` data pointwise: it needs the fact
that a homeomorphism between two arcs matching their endpoints is monotone, hence carries
initial subarcs to initial subarcs. That fact was not on `main` when this module was written,
and assuming the two clauses would have been assuming the conclusion, so nothing was stated
here. `Schoenflies/ArcMonotone.lean`
now proves it — `ArcMatch`, `transferParam`, `image_image_uIcc` — and
`Schoenflies/RealizeSubdivHomeo.lean` builds the transported homeomorphism from it, orientation
of the two realizations handled rather than assumed.

## Blueprint

* `def:generated-structure`, operation 1 (edge subdivision) — the geometric half of the
  operation, whose abstract half is `CellStructure.subdivideEdge`.
* `lem:cellulation-invariants` (i) and (iv), the paragraph "Suppose first that an open edge `e`
  is subdivided at a new vertex `v`": `SubdivData.isRefinement_realize` produces exactly the
  hypotheses that `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan` consumes.

Declarations:

* `Schoenflies.uIcc_union_uIcc`, `Schoenflies.uIcc_inter_uIcc` — a parameter interval cut at an
  interior point.
* `Schoenflies.subarc_image_union`, `Schoenflies.subarc_image_inter` — the two subarcs of a cut
  cover the arc and meet exactly at the cut point.
* `Schoenflies.firstHalf`, `Schoenflies.secondHalf` — the two halves of a drawn edge in the
  standard orientation, with their endpoint values, continuity, injectivity, images, meet and
  union.
* `Schoenflies.CellStructure.SubdivData.leftParam` / `rightParam` — the orientation of the drawn
  edge.
* `Schoenflies.CellStructure.SubdivData.realize` — the realization of the subdivided structure.
* `Schoenflies.CellStructure.SubdivData.isRefinement_realize` — it refines the given one.
* `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan` — the
  induction step of `lem:cellulation-invariants` over the first constructor, now constructed
  with all necessary data constructed here.
* `Schoenflies.CellStructure.SubdivData.skeletonSet_realize` — a subdivision does not move the
  realized 1-skeleton.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-! ### Cutting a parameter interval at an interior point -/

variable {a b t : ℝ}

/-! ### The two subarcs of a cut -/

variable {f : ℝ → Plane}

/-- **The closure of an open arc is the closed arc.** General; `Schoenflies/Subarc.lean` has the
two endpoint halves (`IsArcBetween.left_mem_closure_diff` and `…right_mem_closure_diff`) but not
this consequence, and every "closure of a new open edge" computation is this lemma. It belongs
next to those two if a second consumer appears. -/
theorem IsArcBetween.closure_diff_eq {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine subset_antisymm (h.isArc.isClosed.closure_subset_iff.2 sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  · by_cases hzq : z = q
    · exact hzq ▸ h.right_mem_closure_diff
    · exact subset_closure ⟨hz, by simp [hzp, hzq]⟩

/-- The three pieces an open arc is cut into put the arc back together. -/
theorem diff_pair_union_union {A : Set Plane} {p q : Plane} (hp : p ∈ A) (hq : q ∈ A) :
    A \ {p, q} ∪ {q} ∪ {p} = A := by
  ext z
  simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ((⟨h, -, -⟩ | rfl) | rfl)
    exacts [h, hq, hp]
  · intro h
    by_cases h₁ : z = p
    · exact Or.inr h₁
    · by_cases h₂ : z = q
      · exact Or.inl (Or.inr h₂)
      · exact Or.inl (Or.inl ⟨h, h₁, h₂⟩)

/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/

variable {β : Type*} {drawing : β → ℝ → Plane} {e : β}

/-! ### The orientation of the drawn subdivided edge -/

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} (d : S.SubdivData) (R : S.Realization)

/-! ### Freshness of the three new names, in the forms used below -/

/-! ### The links of the subdivided skeleton -/

/-! ### The realization of the subdivided structure -/

variable {d R}

/-! ### The two half arcs -/

/-! ### The two cell-shape fields of a realization -/

section

variable (ht : t ∈ Ioo (0 : ℝ) 1)
include ht

omit ht in
theorem posLeft_mem_edgeArc_newEdge₁ :
    R.pos d.left ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact ⟨_, left_mem_uIcc, rfl⟩

omit ht in
theorem posRight_mem_edgeArc_newEdge₂ :
    R.pos d.right ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact ⟨_, right_mem_uIcc, rfl⟩

omit ht in
theorem newPos_mem_edgeArc_newEdge₁ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁]; exact ⟨t, right_mem_uIcc, rfl⟩

omit ht in
theorem newPos_mem_edgeArc_newEdge₂ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂]; exact ⟨t, left_mem_uIcc, rfl⟩

/-! ### The subdivided drawn skeleton -/

/-! ### Where two edges of the subdivided drawing meet -/

/-! ### The subdivided drawing -/

/-! ### The two new open edges, as arcs -/

/-- The first new edge is drawn as an arc from the position of `d.left` to the new point. -/
theorem isArcBetween_newEdge₁ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (R.pos d.left) (R.drawing d.edge t) := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht) (d.leftParam_ne R ht)

/-- The second new edge is drawn as an arc from the new point to the position of `d.right`. -/
theorem isArcBetween_newEdge₂ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (R.drawing d.edge t) (R.pos d.right) := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R) (Ne.symm (d.rightParam_ne R ht))

end

/-! ### The realization of the subdivided structure -/

variable (ht : t ∈ Ioo (0 : ℝ) 1)

include ht

/-! ### The realization refines the old one -/

theorem closure_realizeCell_newEdge₁ :
    closure (d.realizeCell R t d.newEdge₁) = edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).closure_diff_eq

theorem closure_realizeCell_newEdge₂ :
    closure (d.realizeCell R t d.newEdge₂) = edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).closure_diff_eq

/-- **The old open edge is cut into the two new open edges and the new 0-cell.** -/
theorem realizeCell_edge_eq : R.cell d.edge = d.realizeCell R t d.newEdge₁ ∪
    d.realizeCell R t d.newVertex ∪ d.realizeCell R t d.newEdge₂ := by
  rw [R.cell_edge d.isLink, realizeCell_newEdge₁, realizeCell_newVertex, realizeCell_newEdge₂,
    ← edgeArc_newEdge₁, ← edgeArc_newEdge₂, ← edgeArc_new_union ht]
  ext p
  simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hp | hp, hL, hR⟩
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inl (Or.inl ⟨hp, hL, hM⟩)
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inr ⟨hp, hM, hR⟩
  · rintro ((⟨hp, hL, hM⟩ | rfl) | ⟨hp, hM, hR⟩)
    · exact ⟨Or.inl hp, hL, fun h => posRight_notMem_edgeArc_newEdge₁ ht (h ▸ hp)⟩
    · exact ⟨Or.inl newPos_mem_edgeArc_newEdge₁, d.newPos_ne_pos R ht d.isLink.left_mem,
        d.newPos_ne_pos R ht d.isLink.right_mem⟩
    · exact ⟨Or.inr hp, fun h => posLeft_notMem_edgeArc_newEdge₂ ht (h ▸ hp), hR⟩

theorem nonempty_realizeCell_newEdge₁ : (d.realizeCell R t d.newEdge₁).Nonempty := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).nonempty_diff

theorem nonempty_realizeCell_newEdge₂ : (d.realizeCell R t d.newEdge₂).Nonempty := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).nonempty_diff

omit ht in
theorem disjoint_newEdge₁_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₁, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inr (mem_singleton_iff.1 hq))

omit ht in
theorem disjoint_newEdge₂_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₂) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₂, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inl (mem_singleton_iff.1 hq))

theorem disjoint_newEdge₁_newEdge₂ :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newEdge₂) := by
  refine disjoint_left.2 fun p hp hq => ?_
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁] at hp
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂] at hq
  have : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp.1, hq.1⟩
  exact hp.2 (Or.inr (mem_singleton_iff.1 this))

/-- **The subdivided realization refines the given one** — every field of
`SubdivData.IsRefinement`. With `IsRefinement.isCellDecomposition_and_isFaceJordan` this hands a
consumer `IsCellDecomposition`, `IsFaceJordan` and `Refines` at the new stage. -/
theorem isRefinement_realize : d.IsRefinement R (d.realize R t ht) where
  cell_eq := fun _ hc _ => realizeCell_of_mem_cells hc
  cell_edge := realizeCell_edge_eq ht
  nonempty := by
    rintro c (rfl | rfl | rfl)
    · rw [realize_cell, realizeCell_newVertex]
      exact ⟨R.drawing d.edge t, rfl⟩
    · exact nonempty_realizeCell_newEdge₁ ht
    · exact nonempty_realizeCell_newEdge₂ ht
  disjoint := by
    rintro c τ (rfl | rfl | rfl) (rfl | rfl | rfl) hne
    · exact absurd rfl hne
    · exact (disjoint_newEdge₁_newVertex (t := t)).symm
    · exact (disjoint_newEdge₂_newVertex (t := t)).symm
    · exact disjoint_newEdge₁_newVertex
    · exact absurd rfl hne
    · exact disjoint_newEdge₁_newEdge₂ ht
    · exact disjoint_newEdge₂_newVertex
    · exact (disjoint_newEdge₁_newEdge₂ ht).symm
    · exact absurd rfl hne
  closure_newVertex := by
    simp only [realize_cell]
    rw [realizeCell_newVertex, closure_singleton]
  closure_newEdge₁ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₁ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.left_mem, realizeCell_newEdge₁, ← edgeArc_newEdge₁]
    exact (diff_pair_union_union posLeft_mem_edgeArc_newEdge₁ newPos_mem_edgeArc_newEdge₁).symm
  closure_newEdge₂ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₂ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.right_mem, realizeCell_newEdge₂, ← edgeArc_newEdge₂,
      pair_comm (R.drawing d.edge t) (R.pos d.right)]
    exact (diff_pair_union_union posRight_mem_edgeArc_newEdge₂ newPos_mem_edgeArc_newEdge₂).symm

/-- **The whole induction step over the first constructor, constructed.** One edge subdivision of
a realization satisfying (i) and (vii) produces a realization satisfying (i) and (vii) and
refining it, constructing the refined realization in the conclusion. -/
theorem realize_isCellDecomposition_and_isFaceJordan (hS : S.CombInvariants) {D : Set Plane}
    (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    (d.realize R t ht).IsCellDecomposition D ∧ (d.realize R t ht).IsFaceJordan ∧
      (d.realize R t ht).Refines R d.parent :=
  (isRefinement_realize ht).isCellDecomposition_and_isFaceJordan hS h hJ

/-! ### The subdivision does not move the skeleton

Cutting an edge in two adds a point that was already on the drawing and replaces one arc by two
whose union is that arc. So the realized 1-skeleton is literally the same set — which is what
lets a skeleton homeomorphism be transported across a subdivision without being rebuilt. -/

end SubdivData

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CommonSubdivision
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- Adding edges without adding vertices preserves 2-connectivity. -/
theorem IsTwoConnected.spanning_mono {α δ : Type*} {A B : Graph α δ}
    (hA : A.IsTwoConnected) (hAB : A ≤ B) (hV : V(B) ⊆ V(A)) :
    B.IsTwoConnected where
  hasThreeVertices := hA.hasThreeVertices.mono hAB.vertexSet_mono
  connected := by
    obtain ⟨u, hu⟩ := hA.connected.nonempty
    exact Connected.of_hub (hAB.vertexSet_mono hu) fun x hx =>
      (hA.connected.reaches hu (hV hx)).mono hAB
  deleteVerts_connected := by
    intro x _
    have hdel := deleteVerts_mono hAB ({x} : Set α)
    obtain ⟨u, hu⟩ := (hA.deleteVerts_connected' x).nonempty
    exact Connected.of_hub (hdel.vertexSet_mono hu) fun y hy =>
      ((hA.deleteVerts_connected' x).reaches hu (by
        rw [vertexSet_deleteVerts] at hy ⊢
        exact ⟨hV hy.1, hy.2⟩)).mono hdel

end Graph
end

section
-- module Solutions.Q146_CD.InitialOuterCycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The initial distinguished outer graph is a simple cycle

Reverse finite transfer ultimately needs only the local fact that at most two distinguished
outer edges meet at a vertex. `Schoenflies.GeneratedStructure.outerEdgesFormCycle` propagates
the stronger and more natural invariant that the complete outer edge set is one simple cycle.
This module supplies its base case for the concrete initial hexagon.

## Blueprint

* `Schoenflies.outerEdgesFormCycle_initialStructure` — the distinguished outer graph of the
  initial matched cellulation is its six-edge simple cycle.
-/

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

/-- One oriented side of the initial hexagonal outer graph. -/
theorem initOuter_isLink_edge (i : Fin 6) :
    initOuter.IsLink (.edge i) (.vert i) (.vert (i + 1)) :=
  ⟨⟨i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Incidence in the initial outer graph is membership among an outer edge's two ends. -/
theorem initOuter_inc_iff {e x : InitialCell} :
    initOuter.Inc e x ↔
      e ∈ InitialCell.outerEdges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, he, hxy⟩
    rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨he, Or.inr rfl⟩
  · rintro ⟨⟨i, rfl⟩, rfl | rfl⟩
    · exact (initOuter_isLink_edge i).inc_left
    · exact (initOuter_isLink_edge i).inc_right

/-- The five-edge complementary path to outer edge zero. -/
theorem isPath_initOuter_complement :
    initOuter.IsPath (.vert 0)
      [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1] (.vert 1) := by
  refine .cons (initOuter_isLink_edge 5).symm
    (.cons (initOuter_isLink_edge 4).symm
      (.cons (initOuter_isLink_edge 3).symm
        (.cons (initOuter_isLink_edge 2).symm
          (Graph.IsPath.single (initOuter_isLink_edge 1).symm (by simp)) ?_) ?_) ?_) ?_
  all_goals
    simp [Graph.walkVertices, Graph.coveredVertices,
      initOuter_inc_iff, InitialCell.outerEdges, InitialCell.ends]

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The four sides of the square of radius `r` occupy exactly its frame. -/
theorem cover_ringPieces {r : ℝ} (hr : 0 ≤ r) : cover (ringPieces r) = ringSet r := by
  ext x
  simp only [ringPieces, cover_cons, cover_nil, union_empty, mem_union, Piece.seg,
    mem_segment_horiz, mem_segment_vert, segment_symm_Icc hr, segment_symm_Icc' hr,
    mem_Icc, ringSet, mem_setOf_eq, Plane.supNorm]
  -- On each side one coordinate is pinned to `±r` and the other is confined to `[-r, r]`;
  -- which of the two is pinned is the only difference between the four sides.
  have hleft : ∀ u v : ℝ, |u| = r → |v| ≤ r → max |u| |v| = r := by
    intro u v hu hv; rw [hu]; exact max_eq_left hv
  have hright : ∀ u v : ℝ, |u| ≤ r → |v| = r → max |u| |v| = r := by
    intro u v hu hv; rw [hv]; exact max_eq_right hu
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_neg, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_neg, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
  · intro h
    have h0 : |x 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |x 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |x 0| |x 1| with hm | hm
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inr (Or.inr (Or.inr ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩))
      · exact Or.inr (Or.inl ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩)
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩))

theorem supNorm_smul_of_mem_modelCurve {t : ℝ} (ht : 0 ≤ t) {z : Plane} (hz : z ∈ modelCurve) :
    Plane.supNorm (t • z) = t := by
  rw [Plane.supNorm_smul, abs_of_nonneg ht, show Plane.supNorm z = 1 from hz, mul_one]

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

/-! ### Spokes -/

/-- A spoke meets the model curve exactly at its outer end. -/
theorem spokePiece_inter_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ∩ modelCurve = {z} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxS⟩
    rw [spokePiece_seg hN] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
    have : t = 1 := by
      have hval := supNorm_smul_of_mem_modelCurve h0 hz
      rw [show Plane.supNorm (t • z) = 1 from hxS] at hval
      exact hval.symm
    simp only [this, one_smul]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, hz⟩

/-- A spoke lies inside the closed square. -/
theorem spokePiece_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ⊆ Plane.closedSquare 0 1 := by
  rw [spokePiece_seg hN]
  rintro _ ⟨t, ht, rfl⟩
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  exact mem_closedSquare_zero_one.2 (by rw [supNorm_smul_of_mem_modelCurve h0 hz]; exact ht.2)

theorem spokePiece_nondeg {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).Nondeg := by
  intro h
  have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = (N : ℝ)⁻¹ :=
    supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hz
  rw [show (((N : ℝ)⁻¹) • z) = z from h.symm, show Plane.supNorm z = 1 from hz] at h2
  have := inv_cast_lt_one hN
  linarith

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

/-- Every point of a source piece lies on a piece of the subdivision contained in that
source. -/
theorem subdivide_covers_source (points : List Plane) : ∀ (pieces : List Piece) (P : Piece),
    P ∈ pieces → ∀ x ∈ P.seg,
      ∃ Q ∈ subdivide pieces points, x ∈ Q.seg ∧ Q.seg ⊆ P.seg := by
  induction points with
  | nil => exact fun _ P hP x hx => ⟨P, hP, hx, subset_rfl⟩
  | cons q qs ih =>
    intro pieces P hP x hx
    obtain ⟨P', hP', hxP'⟩ :=
      mem_cover_iff.1 (show x ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hx)
    obtain ⟨Q, hQ, hxQ, hsub⟩ :=
      ih (splitAllAt q pieces) P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) x hxP'
    exact ⟨Q, hQ, hxQ, hsub.trans (splitAt_subset q P P' hP').1⟩

/-- **A cut point on a source piece is an endpoint of a piece of the subdivision inside it.** -/
theorem subdivide_end_of_mem (points : List Plane) : ∀ (pieces : List Piece) (p : Plane),
    p ∈ points → ∀ P ∈ pieces, p ∈ P.seg →
      ∃ Q ∈ subdivide pieces points, Q.seg ⊆ P.seg ∧ (p = Q.1 ∨ p = Q.2) := by
  induction points with
  | nil => intro _ p hp; simp at hp
  | cons q qs ih =>
    intro pieces p hp P hP hmem
    rcases List.mem_cons.1 hp with rfl | hp'
    · -- the cut happens at this step, and later cuts keep the new endpoint an endpoint
      obtain ⟨R, hR, hsub, hend⟩ := splitAt_end_of_mem p P hmem
      exact subdivide_preserves_end qs ⟨R, List.mem_flatMap.2 ⟨P, hP, hR⟩, hsub, hend⟩
    · obtain ⟨P', hP', hpP'⟩ :=
        mem_cover_iff.1 (show p ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hmem)
      obtain ⟨Q, hQ, hsub, hend⟩ :=
        ih (splitAllAt q pieces) p hp' P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) hpP'
      exact ⟨Q, hQ, hsub.trans (splitAt_subset q P P' hP').1, hend⟩

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

theorem MeetsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : MeetsAreCut pieces points) (hsub : points ⊆ points') : MeetsAreCut pieces points' := by
  intro P hP Q hQ hPQ hne
  obtain ⟨u, v, huv, hu, hv⟩ := h P hP Q hQ hPQ hne
  exact ⟨u, v, huv, hsub hu, hsub hv⟩

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

theorem cover_meshSegments {N : ℕ} (hN : 2 ≤ N) (fresh : List Plane) :
    cover (meshSegments N fresh) =
      (⋃ r ∈ meshRadii N, ringSet r) ∪ ⋃ z ∈ fresh, (spokePiece N z).seg := by
  rw [meshSegments, cover_append, cover_flatMap', cover_map]
  congr 1
  exact iUnion₂_congr fun r hr => cover_ringPieces (meshRadii_pos hN hr).le

theorem meshSegments_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) : ∀ P ∈ meshSegments N fresh, P.Nondeg := by
  intro P hP
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · exact ringPieces_nondeg (meshRadii_pos hN hr) P hPr
  · exact spokePiece_nondeg hN (hfresh z hz)

/-- A side of a ring lies on that ring. -/
theorem ringPieces_seg_subset {r : ℝ} (hr : 0 ≤ r) {P : Piece} (hP : P ∈ ringPieces r) :
    P.seg ⊆ ringSet r := by
  rw [← cover_ringPieces hr]
  exact fun x hx => mem_cover_iff.2 ⟨P, hP, hx⟩

/-- Every mesh segment lies inside the closed square. -/
theorem meshSegments_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {P : Piece} (hP : P ∈ meshSegments N fresh) :
    P.seg ⊆ Plane.closedSquare 0 1 := by
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · refine (ringPieces_seg_subset (meshRadii_pos hN hr).le hPr).trans ?_
    exact fun x hx => mem_closedSquare_zero_one.2 (le_of_eq_of_le hx (meshRadii_le_one hN hr))
  · exact spokePiece_subset_closedSquare hN (hfresh z hz)

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

open scoped Classical in
/-- Cut points for the mesh segments, as produced by `exists_cut_points`. -/
noncomputable def meshCutPoints (N : ℕ) (fresh : List Plane) : List Plane :=
  (exists_cut_points (meshSegments N fresh)).choose

theorem meshCutPoints_spec (N : ℕ) (fresh : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshCutPoints N fresh) ∧
      MeetsAreCut (meshSegments N fresh) (meshCutPoints N fresh) :=
  (exists_cut_points (meshSegments N fresh)).choose_spec

/-- The cut points of the mesh: what the overlay needs, plus the prescribed anchors. -/
noncomputable def meshPoints (N : ℕ) (fresh anchors : List Plane) : List Plane :=
  anchors ++ meshCutPoints N fresh

theorem meshPoints_endsAreCut (N : ℕ) (fresh anchors : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).1.mono (List.subset_append_right _ _)

theorem meshPoints_meetsAreCut (N : ℕ) (fresh anchors : List Plane) :
    MeetsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).2.mono (List.subset_append_right _ _)

/-- **The mesh graph.** -/
noncomputable def meshGraph (N : ℕ) (fresh anchors : List Plane) : Graph Plane Piece :=
  overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)

instance meshGraph_finite (N : ℕ) (fresh anchors : List Plane) :
    Graph.Finite (meshGraph N fresh anchors) :=
  overlayGraph_finite _ _

/-- An edge of the mesh graph is a subsegment of a mesh segment. -/
theorem meshGraph_edge_source {N : ℕ} {fresh anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) :
    ∃ R ∈ meshSegments N fresh, P.seg ⊆ R.seg := by
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨R, hR, hsub, -⟩ := subdivide_subset _ _ Q hQ
  exact ⟨R, hR, by rwa [orientPiece_seg]⟩

theorem meshGraph_edge_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) : P.Nondeg :=
  overlayPieces_nondeg _ (meshSegments_nondeg hN hfresh) P hP

theorem meshGraph_mem_vertexSet {N : ℕ} {fresh anchors : List Plane} {v : Plane} :
    v ∈ V(meshGraph N fresh anchors) ↔
      ∃ P ∈ E(meshGraph N fresh anchors), v = P.1 ∨ v = P.2 := Iff.rfl

/-- A fresh point is a cut point: it is an endpoint of its own spoke. -/
theorem fresh_mem_meshPoints {N : ℕ} {fresh : List Plane} (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) : z ∈ meshPoints N fresh anchors :=
  meshPoints_endsAreCut N fresh anchors _ (spokePiece_mem_meshSegments hz) z (Or.inl rfl)

/-! ### Clause 2: the anchors are vertices on `S` -/

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-- The edges of the mesh that lie on the model curve. -/
def outerEdges (N : ℕ) (fresh anchors : List Plane) : Set Piece :=
  {P | P ∈ E(meshGraph N fresh anchors) ∧ P.seg ⊆ modelCurve}

/-- **The outer edges occupy exactly the model curve.** -/
theorem cover_outerEdges {N : ℕ} (hN : 2 ≤ N) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges N fresh anchors, P.seg = modelCurve := by
  refine subset_antisymm (iUnion₂_subset fun P hP => hP.2) fun x hx => ?_
  obtain ⟨R, hR, hxR⟩ :=
    mem_cover_iff.1 (show x ∈ cover (ringPieces 1) by rw [cover_ringPieces zero_le_one]; exact hx)
  obtain ⟨Q, hQ, hxQ, hsub⟩ := subdivide_covers_source (meshPoints N fresh anchors)
    (meshSegments N fresh) R (outer_ringPieces_mem hN hR) x hxR
  refine mem_iUnion₂.2 ⟨orientPiece Q, ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, ?_⟩, ?_⟩
  · rw [orientPiece_seg]
    exact hsub.trans (ringPieces_seg_subset zero_le_one hR)
  · rwa [orientPiece_seg]

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

/-- **An edge that meets `S` but does not lie on it is a piece of a spoke**, and it meets `S`
exactly at that spoke's fresh point, which is one of its endpoints. -/
theorem meshGraph_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hP
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨z, hz, rfl⟩
  · exfalso
    have hseg : P.seg ⊆ ringSet r :=
      hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    by_cases h1 : r = 1
    · exact hnot (by rw [← ringSet_one, ← h1]; exact hseg)
    · obtain ⟨x, hxP, hxS⟩ := hmeet
      have hmem : x ∈ ringSet r ∩ modelCurve := ⟨hseg hxP, hxS⟩
      rw [ringSet_disjoint_modelCurve h1] at hmem
      exact hmem
  · have hle : P.seg ∩ modelCurve ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact inter_subset_inter_left _ hsub
    obtain ⟨x, hxP, hxS⟩ := hmeet
    have hxz : x = z := hle ⟨hxP, hxS⟩
    subst hxz
    refine ⟨x, hz, subset_antisymm hle (singleton_subset_iff.2 ⟨hxP, hxS⟩), ?_, hsub⟩
    -- `x` is a cut point, so it cannot be interior to an edge
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids (meshSegments_nondeg hN hfresh) x
      (fresh_mem_meshPoints anchors hz) P hP
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-- **Existence** for clause 4: a fresh point does carry an edge leaving `S`. -/
theorem exists_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ w ∈ fresh, w ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃ P ∈ E(meshGraph N fresh anchors),
      (z = P.1 ∨ z = P.2) ∧ ¬ P.seg ⊆ modelCurve ∧ P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨Q, hQ, hsub, hend⟩ := subdivide_end_of_mem (meshPoints N fresh anchors)
    (meshSegments N fresh) z (fresh_mem_meshPoints anchors hz) (spokePiece N z)
    (spokePiece_mem_meshSegments hz) (left_mem_segment ℝ _ _)
  have hnd : Q.Nondeg :=
    subdivide_ne (meshPoints N fresh anchors) (meshSegments_nondeg hN hfresh) Q hQ
  refine ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend, ?_, ?_⟩
  · rw [orientPiece_seg]
    intro hcon
    -- an edge inside `S` and inside the spoke would be inside `{z}`, hence degenerate
    have hsing : Q.seg ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact subset_inter hsub hcon
    exact hnd ((hsing (left_mem_segment ℝ _ _)).trans (hsing (right_mem_segment ℝ _ _)).symm)
  · rw [orientPiece_seg]; exact hsub

/-- **Uniqueness** for clause 4: exactly one edge leaves `S` at a fresh point. -/
theorem inner_edge_at_fresh_unique {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {z : Plane} (hz : z ∈ fresh)
    {P Q : Piece} (hP : P ∈ E(meshGraph N fresh anchors)) (hendP : z = P.1 ∨ z = P.2)
    (hnotP : ¬ P.seg ⊆ modelCurve) (hQ : Q ∈ E(meshGraph N fresh anchors))
    (hendQ : z = Q.1 ∨ z = Q.2) (hnotQ : ¬ Q.seg ⊆ modelCurve) : P = Q := by
  have hzS : z ∈ modelCurve := hfresh z hz
  -- each of the two edges lies on the spoke at `z`
  have spoke_of : ∀ R : Piece, R ∈ E(meshGraph N fresh anchors) → (z = R.1 ∨ z = R.2) →
      ¬ R.seg ⊆ modelCurve → R.seg ⊆ (spokePiece N z).seg := by
    intro R hR hendR hnotR
    have hzR : z ∈ R.seg := by
      rcases hendR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    obtain ⟨w, hw, hmeetw, -, hsubw⟩ :=
      meshGraph_inner_edge_at_fresh hN hfresh hR ⟨z, hzR, hzS⟩ hnotR
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hmeetw ▸ (show z ∈ R.seg ∩ modelCurve from ⟨hzR, hzS⟩)
      exact this
    rwa [← hzw] at hsubw
  obtain ⟨tP, hltP, hintP⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hP) (spoke_of P hP hendP hnotP) hendP
  obtain ⟨tQ, hltQ, hintQ⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hQ) (spoke_of Q hQ hendQ hnotQ) hendQ
  by_contra hne
  -- both interiors contain every multiple `s • z` with `max tP tQ < s < 1`
  set s : ℝ := (max tP tQ + 1) / 2 with hs
  have hs1 : s < 1 := by
    rw [hs]
    rcases max_cases tP tQ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  have hsP : tP < s := by
    rw [hs]; have : tP ≤ max tP tQ := le_max_left _ _
    have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_left tP tQ]
  have hsQ : tQ < s := by
    rw [hs]; have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_right tP tQ]
  refine overlayPieces_disjoint_interiors (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors) hP hQ hne
    (x := s • z) ?_ ?_
  · rw [hintP]; exact ⟨s, ⟨hsP, hs1⟩, rfl⟩
  · rw [hintQ]; exact ⟨s, ⟨hsQ, hs1⟩, rfl⟩

/-- **Clause 4.** Exactly one edge of the mesh leaves `S` at each fresh point. -/
theorem unique_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(meshGraph N fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve := by
  obtain ⟨P, hP, hend, hnot, -⟩ := exists_inner_edge_at_fresh hN hfresh anchors hz
  exact ⟨P, ⟨hP, hend, hnot⟩, fun Q hQ =>
    inner_edge_at_fresh_unique hN hfresh hz hQ.1 hQ.2.1 hQ.2.2 hP hend hnot⟩

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

theorem continuous_supNorm : Continuous Plane.supNorm :=
  (continuous_abs.comp (Plane.continuous_coord 0)).max
    (continuous_abs.comp (Plane.continuous_coord 1))

theorem supNorm_sub_le (x y : Plane) :
    Plane.supNorm (x - y) ≤ Plane.supNorm x + Plane.supNorm y := by
  have h := Plane.supDist_triangle x 0 y
  rw [Plane.supDist_zero, Plane.supDist_comm 0 y, Plane.supDist_zero] at h
  exact h

theorem ringSet_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ringSet r ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_left _ (mem_iUnion₂.2 ⟨r, hr, hx⟩)

theorem spokePiece_seg_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {z : Plane}
    (hz : z ∈ fresh) : (spokePiece N z).seg ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_right _ (mem_iUnion₂.2 ⟨z, hz, hx⟩)

/-- **The radial estimate.** A connected set missing the mesh stays inside the open square and
has diameter at most `δ/2 + √2/N`. -/
theorem radial_diam_bound {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {δ : ℝ}
    (hNδ : 2 * Real.sqrt 2 ≤ δ * N) (hdense : FreshDense fresh δ)
    {F : Set Plane} (hconn : IsPreconnected F)
    (hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh))
    {base : Plane} (hb : base ∈ F) (hbase : Plane.supNorm base < 1) :
    (∀ x ∈ F, Plane.supNorm x < 1) ∧
      ∀ x ∈ F, ∀ y ∈ F, dist x y ≤ δ / 2 + Real.sqrt 2 / N := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- no point of `F` sits on a ring
  have hring : ∀ r ∈ meshRadii N, ∀ x ∈ F, Plane.supNorm x ≠ r := fun r hr x hx he =>
    hdisj x hx (ringSet_subset_cover hN hr he)
  have himg : IsPreconnected (Plane.supNorm '' F) :=
    hconn.image _ continuous_supNorm.continuousOn
  -- the ring index of the base point
  set c : ℝ := Plane.supNorm base with hc
  have hc0 : 0 ≤ c := Plane.supNorm_nonneg _
  have hcN : 0 ≤ c * (N : ℝ) := mul_nonneg hc0 hNR0.le
  set k : ℕ := ⌊c * (N : ℝ)⌋₊ with hk
  have hkle : (k : ℝ) ≤ c * N := Nat.floor_le hcN
  have hklt : c * (N : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hkN : k < N := by
    rw [hk, Nat.floor_lt hcN]
    calc c * (N : ℝ) < 1 * N := by exact mul_lt_mul_of_pos_right hbase hNR0
      _ = N := one_mul _
  set a : ℝ := (k : ℝ) / N with ha
  set b : ℝ := ((k : ℝ) + 1) / N with hbdef
  have hac : a ≤ c := by rw [ha, div_le_iff₀ hNR0]; exact hkle
  have hcb : c < b := by rw [hbdef, lt_div_iff₀ hNR0]; exact hklt
  have hbmem : b ∈ meshRadii N := mem_meshRadii.2 ⟨k, hkN, rfl⟩
  have hb1 : b ≤ 1 := meshRadii_le_one hN hbmem
  have hba : b - a = 1 / (N : ℝ) := by rw [ha, hbdef, div_sub_div_same]; ring_nf
  -- the sup norm on `F` stays inside `[a, b)`
  have hup : ∀ x ∈ F, Plane.supNorm x < b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hyb⟩ :=
      himg.Icc_subset ⟨base, hb, rfl⟩ ⟨x, hx, rfl⟩ (mem_Icc.2 ⟨hcb.le, hcon⟩)
    exact hring b hbmem y hy hyb
  have hlow : ∀ x ∈ F, a ≤ Plane.supNorm x := by
    intro x hx
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [ha, hk0]; simpa using Plane.supNorm_nonneg x
    · have hamem : a ∈ meshRadii N := by
        refine mem_meshRadii.2 ⟨k - 1, by omega, ?_⟩
        rw [ha]
        congr 1
        rw [Nat.cast_sub hk1, Nat.cast_one]
        ring
      have hac' : a < c := lt_of_le_of_ne hac fun he => hring a hamem base hb he.symm
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hya⟩ :=
        himg.Icc_subset ⟨x, hx, rfl⟩ ⟨base, hb, rfl⟩ (mem_Icc.2 ⟨hcon.le, hac'.le⟩)
      exact hring a hamem y hy hya
  refine ⟨fun x hx => lt_of_lt_of_le (hup x hx) hb1, ?_⟩
  -- one ring thickness is at most `δ/2`
  have hthin : Real.sqrt 2 / (N : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hNR0 two_pos]
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- the innermost square: both points are within `1/N` of the origin
    have hsmall : ∀ x ∈ F, Plane.supNorm x < 1 / (N : ℝ) := by
      intro x hx
      have := hup x hx
      rwa [hbdef, hk0, Nat.cast_zero, zero_add] at this
    intro x hx y hy
    calc dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := dist_le_sqrt_two_mul_supNorm x y
      _ ≤ Real.sqrt 2 * (Plane.supNorm x + Plane.supNorm y) :=
          mul_le_mul_of_nonneg_left (supNorm_sub_le x y) hsqrt.le
      _ ≤ Real.sqrt 2 * (1 / (N : ℝ) + 1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add (hsmall x hx).le (hsmall y hy).le) hsqrt.le
      _ = Real.sqrt 2 / N + Real.sqrt 2 / N := by ring
      _ ≤ δ / 2 + Real.sqrt 2 / N := by linarith
  · -- the annulus between two rings: project radially onto `S`
    have hainv : (N : ℝ)⁻¹ ≤ a := by
      rw [ha, inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      exact_mod_cast hk1
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) hainv
    have hpos : ∀ x ∈ F, 0 < Plane.supNorm x := fun x hx => lt_of_lt_of_le hapos (hlow x hx)
    set g : Plane → Plane := fun x => (Plane.supNorm x)⁻¹ • x with hg
    have hrecov : ∀ x ∈ F, Plane.supNorm x • g x = x := by
      intro x hx
      rw [hg]
      simp only [smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt (hpos x hx)), one_smul]
    have hgS : ∀ x ∈ F, g x ∈ modelCurve := by
      intro x hx
      change Plane.supNorm ((Plane.supNorm x)⁻¹ • x) = 1
      rw [Plane.supNorm_smul, abs_of_nonneg (inv_nonneg.2 (Plane.supNorm_nonneg x))]
      exact inv_mul_cancel₀ (ne_of_gt (hpos x hx))
    have hgcont : ContinuousOn g F :=
      ContinuousOn.smul (continuous_supNorm.continuousOn.inv₀ fun x hx => ne_of_gt (hpos x hx))
        continuousOn_id
    have hgavoid : ∀ x ∈ F, g x ∈ modelCurve \ {w : Plane | w ∈ fresh} := by
      intro x hx
      refine ⟨hgS x hx, fun hmem => hdisj x hx ?_⟩
      -- `x` lies on the spoke at `g x`
      refine spokePiece_seg_subset_cover hN hmem ?_
      rw [spokePiece_seg hN]
      exact ⟨Plane.supNorm x, ⟨le_trans hainv (hlow x hx),
        le_trans (hup x hx).le hb1⟩, hrecov x hx⟩
    have hgdist : ∀ x ∈ F, ∀ y ∈ F, dist (g x) (g y) ≤ δ / 2 := fun x hx y hy =>
      hdense (g '' F) (by rintro _ ⟨w, hw, rfl⟩; exact hgavoid w hw) (hconn.image g hgcont)
        (g x) ⟨x, hx, rfl⟩ (g y) ⟨y, hy, rfl⟩
    intro x hx y hy
    have hsplit : x - y = Plane.supNorm x • (g x - g y)
        + (Plane.supNorm x - Plane.supNorm y) • g y := by
      rw [smul_sub, sub_smul, hrecov x hx, hrecov y hy]
      abel
    have hnormy : ‖g y‖ ≤ Real.sqrt 2 := by
      have := Plane.norm_le_sqrt_two_mul_supNorm (g y)
      rwa [show Plane.supNorm (g y) = 1 from hgS y hy, mul_one] at this
    have hts : |Plane.supNorm x - Plane.supNorm y| ≤ 1 / (N : ℝ) := by
      rw [← hba]
      exact abs_le.2 ⟨by linarith [hlow x hx, hup y hy], by linarith [hup x hx, hlow y hy]⟩
    have hx1 : Plane.supNorm x ≤ 1 := le_of_lt (lt_of_lt_of_le (hup x hx) hb1)
    calc dist x y = ‖Plane.supNorm x • (g x - g y)
          + (Plane.supNorm x - Plane.supNorm y) • g y‖ := by rw [dist_eq_norm, hsplit]
      _ ≤ ‖Plane.supNorm x • (g x - g y)‖
          + ‖(Plane.supNorm x - Plane.supNorm y) • g y‖ := norm_add_le _ _
      _ = Plane.supNorm x * ‖g x - g y‖
          + |Plane.supNorm x - Plane.supNorm y| * ‖g y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Plane.supNorm_nonneg x)]
      _ ≤ 1 * (δ / 2) + 1 / (N : ℝ) * Real.sqrt 2 := by
          refine add_le_add (mul_le_mul hx1 ?_ (norm_nonneg _) zero_le_one)
            (mul_le_mul hts hnormy (norm_nonneg _) (by positivity))
          rw [← dist_eq_norm]
          exact hgdist x hx y hy
      _ = δ / 2 + Real.sqrt 2 / N := by ring

/-- The mesh occupies a subset of the closed square. -/
theorem cover_meshSegments_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) :
    cover (meshSegments N fresh) ⊆ Plane.closedSquare 0 1 := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  exact meshSegments_subset_closedSquare hN hfresh hP hxP

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

theorem halfSpoke_disjoint_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    ∀ x ∈ halfSpoke N z, x ∉ modelCurve := by
  rintro _ ⟨t, ht, rfl⟩ hmem
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  have : t = 1 := by
    have hval := supNorm_smul_of_mem_modelCurve h0 hz
    rw [show Plane.supNorm (t • z) = 1 from hmem] at hval
    exact hval.symm
  exact absurd this (ne_of_lt ht.2)

/-- The frame of a square is connected: four segments in a cycle, meeting at the corners. -/
theorem isConnected_ringSet {r : ℝ} (hr : 0 ≤ r) : IsConnected (ringSet r) := by
  have hseg : ∀ u v : Plane, IsConnected (segment ℝ u v) := fun u v =>
    (convex_segment u v).isConnected ⟨u, left_mem_segment ℝ _ _⟩
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, union_empty]
  have hCD : IsConnected (segment ℝ (Plane.mk (-r) (-r)) (Plane.mk r (-r))
      ∪ segment ℝ (Plane.mk r (-r)) (Plane.mk r r)) :=
    (hseg _ _).union ⟨Plane.mk r (-r), right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩ (hseg _ _)
  have hBCD := (hseg (Plane.mk (-r) r) (Plane.mk (-r) (-r))).union
    ⟨Plane.mk (-r) (-r), right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hCD
  exact (hseg (Plane.mk r r) (Plane.mk (-r) r)).union
    ⟨Plane.mk (-r) r, right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hBCD

/-- **Clause 5.** The mesh with `S` removed is connected. -/
theorem isConnected_cover_diff_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {z₀ : Plane} (hz₀ : z₀ ∈ fresh) :
    IsConnected (cover (meshSegments N fresh) \ modelCurve) := by
  have hinvpos := inv_cast_pos hN
  have hinvlt := inv_cast_lt_one hN
  set p : Plane := ((N : ℝ)⁻¹) • z₀ with hp
  have hpring : p ∈ ringSet ((N : ℝ)⁻¹) :=
    supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z₀ hz₀)
  have hphalf : p ∈ halfSpoke N z₀ := smul_mem_halfSpoke le_rfl hinvlt z₀
  have hinvmem : ((N : ℝ)⁻¹) ∈ meshRadii N := inv_mem_meshRadii hN
  -- the two building blocks, and the fact that they miss `S`
  have hringsub : ∀ r ∈ meshRadii N, r ≠ 1 →
      ringSet r ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro r hr hr1 x hx
    exact ⟨ringSet_subset_cover hN hr hx, fun hc => hr1 (hx.symm.trans hc)⟩
  have hhalfsub : ∀ z ∈ fresh, halfSpoke N z ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro z hz x hx
    exact ⟨spokePiece_seg_subset_cover hN hz (halfSpoke_subset hN z hx),
      halfSpoke_disjoint_modelCurve hN (hfresh z hz) x hx⟩
  refine ⟨⟨p, hhalfsub z₀ hz₀ hphalf⟩, isPreconnected_of_forall p ?_⟩
  intro y hy
  obtain ⟨hyM, hyS⟩ := hy
  rw [cover_meshSegments hN] at hyM
  rcases hyM with hyr | hyz
  · -- `y` is on a ring, which is not the outer one, and the ring meets the spoke at `z₀`
    obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.1 hyr
    have hr1 : r ≠ 1 := fun h => hyS (by rw [← ringSet_one, ← h]; exact hyr)
    have hrpos : 0 < r := meshRadii_pos hN hr
    have hrlt : r < 1 := lt_of_le_of_ne (meshRadii_le_one hN hr) hr1
    have hrinv : ((N : ℝ)⁻¹) ≤ r := by
      obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
      have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    refine ⟨ringSet r ∪ halfSpoke N z₀, union_subset (hringsub r hr hr1) (hhalfsub z₀ hz₀),
      Or.inr hphalf, Or.inl hyr, ?_⟩
    exact ((isConnected_ringSet hrpos.le).union
      ⟨r • z₀, supNorm_smul_of_mem_modelCurve hrpos.le (hfresh z₀ hz₀),
        smul_mem_halfSpoke hrinv hrlt z₀⟩ (isConnected_halfSpoke hN z₀)).isPreconnected
  · -- `y` is on a spoke, below `S`, and the spoke meets the innermost ring
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 hyz
    rw [spokePiece_seg hN] at hyz
    obtain ⟨t, ht, rfl⟩ := hyz
    have h0 : (0 : ℝ) ≤ t := le_trans hinvpos.le ht.1
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 fun h => hyS (by
      rw [← ringSet_one]
      exact (supNorm_smul_of_mem_modelCurve h0 (hfresh z hz)).trans h)
    refine ⟨halfSpoke N z ∪ ringSet ((N : ℝ)⁻¹),
      union_subset (hhalfsub z hz) (hringsub _ hinvmem (ne_of_lt hinvlt)),
      Or.inr hpring, Or.inl (smul_mem_halfSpoke ht.1 ht1 z), ?_⟩
    exact ((isConnected_halfSpoke hN z).union
      ⟨((N : ℝ)⁻¹) • z, smul_mem_halfSpoke le_rfl hinvlt z,
        supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z hz)⟩
      (isConnected_ringSet hinvpos.le)).isPreconnected

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

/-- **The anchored square mesh**: `meshCount δ` concentric ring frames inside `Q = [-1,1]²`,
one radial spoke at each fresh boundary point, and the anchors inserted as extra vertices of
the outer ring. -/
noncomputable def squareMesh (δ : ℝ) (fresh anchors : List Plane) : Graph Plane Piece :=
  meshGraph (meshCount δ) fresh anchors

instance squareMesh_finite (δ : ℝ) (fresh anchors : List Plane) :
    Graph.Finite (squareMesh δ fresh anchors) := meshGraph_finite _ _ _

/-- **Clause 3.** The edges lying on `S` occupy exactly `S`. -/
theorem squareMesh_cover_outerEdges (δ : ℝ) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges (meshCount δ) fresh anchors, P.seg = modelCurve :=
  cover_outerEdges (two_le_meshCount δ) fresh anchors

/-- **Clause 4, first half.** An edge meeting `S` without lying on it meets it in a single
fresh point, which is one of its endpoints. -/
theorem squareMesh_inner_edge_at_fresh {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(squareMesh δ fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece (meshCount δ) z).seg :=
  meshGraph_inner_edge_at_fresh (two_le_meshCount δ) hfresh hP hmeet hnot

/-- **Clause 4, second half.** Exactly one edge leaves `S` at each fresh point. -/
theorem squareMesh_unique_inner_edge {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(squareMesh δ fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve :=
  unique_inner_edge_at_fresh (two_le_meshCount δ) hfresh anchors hz

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-! ### A quadrilateral is 2-connected

The base case of both chains below. The blueprint reaches it through the ear decomposition
(`lem:subdivision-ear-preserve` applied to a cycle); here it is read straight off the
definition of `Graph.IsTwoConnected`, because a four-vertex graph is small enough that
"delete one vertex and the rest is still connected" is four applications of one lemma. -/

/-- **A four-cycle is 2-connected.** No hypothesis on `G` beyond the four edges, the four
distinct vertices, and the fact that there are no other vertices. -/
theorem isTwoConnected_of_quad {e₁ e₂ e₃ e₄ : β} {a b c d : α}
    (h₁ : G.IsLink e₁ a b) (h₂ : G.IsLink e₂ b c) (h₃ : G.IsLink e₃ c d) (h₄ : G.IsLink e₄ d a)
    (hV : ∀ v ∈ V(G), v = a ∨ v = b ∨ v = c ∨ v = d)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) (hac : a ≠ c) (hbd : b ≠ d) :
    G.IsTwoConnected := by
  -- Deleting a vertex keeps every link neither of whose ends was the one deleted.
  have dl : ∀ {f : β} {u v x : α}, G.IsLink f u v → u ≠ x → v ≠ x →
      (G.deleteVerts {x}).IsLink f u v := by
    intro f u v x h hu hv
    exact (deleteVerts_isLink _ _).2 ⟨h, by simpa using hu, by simpa using hv⟩
  -- After a deletion the three survivors form a path `p — q — r`; `q` is the hub.
  have main : ∀ (x p q r : α) (f g : β), G.IsLink f p q → G.IsLink g q r →
      p ≠ x → q ≠ x → r ≠ x → (∀ v ∈ V(G), v = x ∨ v = p ∨ v = q ∨ v = r) →
      (G.deleteVerts {x}).Connected := by
    intro x p q r f g hf hg hp hq hr hcov
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hf.right_mem hq) ?_
    intro v hv
    obtain ⟨hvG, hvx⟩ := mem_deleteVerts_singleton.1 hv
    rcases hcov v hvG with rfl | rfl | rfl | rfl
    · exact absurd rfl hvx
    · exact (Reaches.of_isLink (dl hf hp hq)).symm
    · exact Reaches.refl (mem_deleteVerts_singleton_of_ne hf.right_mem hq)
    · exact Reaches.of_isLink (dl hg hq hr)
  refine ⟨⟨a, h₁.left_mem, b, h₁.right_mem, c, h₂.right_mem, hab, hac, hbc⟩, ?_, ?_⟩
  · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
    rcases hV v hv with rfl | rfl | rfl | rfl
    · exact Reaches.refl h₁.left_mem
    · exact Reaches.of_isLink h₁
    · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
    · exact (Reaches.of_isLink h₄).symm
  · intro x _
    rcases em (x = a) with rfl | hxa
    · exact main x b c d e₂ e₃ h₂ h₃ (Ne.symm hab) (Ne.symm hac) hda
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = b) with rfl | hxb
    · exact main x c d a e₃ e₄ h₃ h₄ (Ne.symm hbc) (Ne.symm hbd) hab
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = c) with rfl | hxc
    · exact main x d a b e₄ e₁ h₄ h₁ (Ne.symm hcd) hac hbc
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = d) with rfl | hxd
    · exact main x a b c e₁ e₂ h₁ h₂ (Ne.symm hda) hbd hcd
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    · -- Deleting a vertex the graph does not have changes nothing.
      refine Connected.deleteVerts_singleton_of_notMem ?_ fun hx ↦ ?_
      · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
        rcases hV v hv with rfl | rfl | rfl | rfl
        · exact Reaches.refl h₁.left_mem
        · exact Reaches.of_isLink h₁
        · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
        · exact (Reaches.of_isLink h₄).symm
      · rcases hV x hx with rfl | rfl | rfl | rfl
        exacts [hxa rfl, hxb rfl, hxc rfl, hxd rfl]

/-! ### Attaching finitely many pieces to a 2-connected hub

`prop:anchored-square-mesh`: *"The boundary of every collar rectangle is a cycle sharing with
the inner grid at least the two endpoints of its inner boundary arc. Adding these finitely many
cycles one at a time and applying `lem:union-two-connected` proves that the full mesh is
2-connected."*

`Graph.chainUnion_isTwoConnected` (`Schoenflies/OuterChain.lean`) iterates the same lemma along
a chain in which **consecutive** members meet. Here every piece meets the **hub**, which is
what the collar rectangles do — each meets the inner grid, but two collar rectangles on
opposite sides of the square meet nothing of each other. The two statements are independent;
the integrator may want them beside each other. -/

/-! ### A march along indices is a path

The boundary walk of the grid is a march: vertices `p s, p (s+1), …` joined by edges
`q s, q (s+1), …`. The freshness clause of `Graph.IsPath` is then exactly the injectivity of
`p` on the index range, because an edge of the chain is incident with nothing but its own two
ends (`Graph.Inc.eq_or_eq_of_isLink`). -/

end Graph

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

/-- **The union of two segment graphs is the segment graph of the concatenation.** This is the
whole reason for `pieceListGraph`: it turns "glue one more cycle on" into an equation. -/
theorem pieceListGraph_union (l l' : List Piece) :
    (pieceListGraph l).union (pieceListGraph l') = pieceListGraph (l ++ l') := by
  refine Graph.eq_of_le_of_subset_subset
    (Graph.union_le (pieceListGraph_mono (List.subset_append_left _ _))
      (pieceListGraph_mono (List.subset_append_right _ _))) ?_ ?_
  · rw [pieceListGraph_vertexSet, endSet_append, Graph.vertexSet_union]
    exact subset_rfl
  · rintro P hP
    rcases List.mem_append.1 hP with h | h
    exacts [Or.inl h, Or.inr h]

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-! ### The cell -/

/-- **One cell of the grid is 2-connected.** Its boundary is a quadrilateral, so this is
`Graph.isTwoConnected_of_quad` with the four corners named. Only the two consecutive-coordinate
inequalities are used. -/
theorem cellGraph_isTwoConnected {xc yc : ℕ → ℝ} {i j : ℕ} (hx : xc i ≠ xc (i + 1))
    (hy : yc j ≠ yc (j + 1)) : (pieceListGraph (cellEdges xc yc i j)).IsTwoConnected := by
  have h₁ : gridHEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₂ : gridVEdge xc yc (i + 1) j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₃ : gridHEdge xc yc i (j + 1) ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₄ : gridVEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  refine Graph.isTwoConnected_of_quad (a := gridPt xc yc i j) (b := gridPt xc yc (i + 1) j)
    (c := gridPt xc yc (i + 1) (j + 1)) (d := gridPt xc yc i (j + 1))
    (pieceListGraph_isLink_self h₁) (pieceListGraph_isLink_self h₂)
    (pieceListGraph_isLink_self h₃).symm (pieceListGraph_isLink_self h₄).symm ?_
    (gridPt_ne_of_fst hx) (gridPt_ne_of_snd hy) (gridPt_ne_of_fst (Ne.symm hx))
    (gridPt_ne_of_snd (Ne.symm hy)) (gridPt_ne_of_fst hx) (gridPt_ne_of_fst (Ne.symm hx))
  rintro v ⟨P, hP, hv⟩
  simp only [cellEdges, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl <;>
    simp only [gridHEdge, gridVEdge] <;> tauto

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

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

/-- A run of horizontal grid edges occupies the whole horizontal segment. -/
theorem iUnion_gridHEdge_seg {xc yc : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (j : ℕ) :
    (⋃ i ∈ Set.Iio m, (gridHEdge xc yc i j).seg)
      = segment ℝ (gridPt xc yc 0 j) (gridPt xc yc m j) := by
  have h0m : xc 0 ≤ xc m := chain_le_of_le hmono 0 m (by omega) le_rfl
  ext z
  simp only [gridHEdge, gridPt, Piece.seg, Set.mem_iUnion, Set.mem_Iio, exists_prop,
    mem_segment_horiz]
  constructor
  · rintro ⟨i, hi, hz1, hz0⟩
    refine ⟨hz1, ?_⟩
    rw [segment_eq_Icc (hmono i hi)] at hz0
    rw [segment_eq_Icc h0m]
    exact Set.Icc_subset_Icc (chain_le_of_le hmono 0 i (by omega) (by omega))
      (chain_le_of_le hmono (i + 1) m (by omega) (by omega)) hz0
  · rintro ⟨hz1, hz0⟩
    rw [segment_eq_Icc h0m, ← iUnion_Icc_chain m hm hmono] at hz0
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hz0
    obtain ⟨i, hi, hz⟩ := hz0
    exact ⟨i, hi, hz1, by rw [segment_eq_Icc (hmono i hi)]; exact hz⟩

/-- A run of vertical grid edges occupies the whole vertical segment. -/
theorem iUnion_gridVEdge_seg {xc yc : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hmono : ∀ j, j < n → yc j ≤ yc (j + 1)) (i : ℕ) :
    (⋃ j ∈ Set.Iio n, (gridVEdge xc yc i j).seg)
      = segment ℝ (gridPt xc yc i 0) (gridPt xc yc i n) := by
  have h0n : yc 0 ≤ yc n := chain_le_of_le hmono 0 n (by omega) le_rfl
  ext z
  simp only [gridVEdge, gridPt, Piece.seg, Set.mem_iUnion, Set.mem_Iio, exists_prop,
    mem_segment_vert]
  constructor
  · rintro ⟨j, hj, hz0, hz1⟩
    refine ⟨hz0, ?_⟩
    rw [segment_eq_Icc (hmono j hj)] at hz1
    rw [segment_eq_Icc h0n]
    exact Set.Icc_subset_Icc (chain_le_of_le hmono 0 j (by omega) (by omega))
      (chain_le_of_le hmono (j + 1) n (by omega) (by omega)) hz1
  · rintro ⟨hz0, hz1⟩
    rw [segment_eq_Icc h0n, ← iUnion_Icc_chain n hn hmono] at hz1
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hz1
    obtain ⟨j, hj, hz⟩ := hz1
    exact ⟨j, hj, hz0, by rw [segment_eq_Icc (hmono j hj)]; exact hz⟩

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

theorem mem_gridHEdge_seg_iff {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane} :
    z ∈ (gridHEdge xc yc i j).seg ↔ z 1 = yc j ∧ z 0 ∈ segment ℝ (xc i) (xc (i + 1)) :=
  mem_segment_horiz

theorem mem_gridVEdge_seg_iff {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane} :
    z ∈ (gridVEdge xc yc i j).seg ↔ z 0 = xc i ∧ z 1 ∈ segment ℝ (yc j) (yc (j + 1)) :=
  mem_segment_vert

variable {xc yc : ℕ → ℝ} {m n : ℕ}

/-- A grid point on a grid edge is one of that edge's two ends. -/
theorem end_of_gridPt_mem_seg (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece}
    (hP : P ∈ gridEdges xc yc m n) {a b : ℕ} (ha : a ≤ m) (hb : b ≤ n)
    (hmem : gridPt xc yc a b ∈ P.seg) : gridPt xc yc a b = P.1 ∨ gridPt xc yc a b = P.2 := by
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hmem
    simp only [gridPt, Plane.mk_one, Plane.mk_zero] at hz1 hz0
    obtain rfl : b = j := hys.injOn hb hj hz1
    rw [segment_eq_Icc (coord_le_of_idx_le hxs (by omega) (by omega) (by omega))] at hz0
    rcases idx_of_coord_mem hxs ha (by omega) hz0.1 hz0.2 with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hmem
    simp only [gridPt, Plane.mk_one, Plane.mk_zero] at hz1 hz0
    obtain rfl : a = i := hxs.injOn ha hi hz0
    rw [segment_eq_Icc (coord_le_of_idx_le hys (by omega) (by omega) (by omega))] at hz1
    rcases idx_of_coord_mem hys hb (by omega) hz1.1 hz1.2 with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]

/-- **A point on two grid edges is a grid point on both.** The heart of the drawing clause:
two grid segments cross only where a coordinate of one is pinned by the other. -/
theorem gridPt_of_mem_two_edges (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) {P Q : Piece}
    (hP : P ∈ gridEdges xc yc m n) (hQ : Q ∈ gridEdges xc yc m n) (hPQ : P ≠ Q) {z : Plane}
    (hzP : z ∈ P.seg) (hzQ : z ∈ Q.seg) :
    ∃ a ≤ m, ∃ b ≤ n, z = gridPt xc yc a b := by
  -- an equal-direction pair: two rows or two columns, meeting at one shared coordinate
  have same : ∀ (f : ℕ → ℝ) (N i i' : ℕ), StrictMonoOn f (Set.Iic N) → i + 1 ≤ N → i' + 1 ≤ N →
      i ≠ i' → ∀ c : ℝ, c ∈ segment ℝ (f i) (f (i + 1)) → c ∈ segment ℝ (f i') (f (i' + 1)) →
      ∃ k ≤ N, c = f k := by
    intro f N i i' hf hi hi' hne c hc hc'
    rw [segment_eq_Icc (coord_le_of_idx_le hf (by omega) (by omega) (by omega))] at hc
    rw [segment_eq_Icc (coord_le_of_idx_le hf (by omega) (by omega) (by omega))] at hc'
    rcases lt_or_gt_of_ne hne with h | h
    · -- `i` is to the left: the two intervals can only touch at `f (i+1)`
      refine ⟨i + 1, hi, le_antisymm hc.2 ?_⟩
      exact le_trans (coord_le_of_idx_le hf (by omega) (by omega) (by omega)) hc'.1
    · refine ⟨i, by omega, le_antisymm ?_ hc.1⟩
      exact le_trans hc'.2 (coord_le_of_idx_le hf (by omega) (by omega) (by omega))
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩ <;>
    rcases (mem_gridEdges_iff hm hn).1 hQ with ⟨i', hi', j', hj', rfl⟩ | ⟨i', hi', j', hj', rfl⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hzP
    obtain ⟨hz1', hz0'⟩ := mem_gridHEdge_seg_iff.1 hzQ
    obtain rfl : j = j' := hys.injOn hj hj' (hz1 ▸ hz1')
    have hii : i ≠ i' := by rintro rfl; exact hPQ rfl
    obtain ⟨k, hk, hck⟩ := same xc m i i' hxs (by omega) (by omega) hii _ hz0 hz0'
    exact ⟨k, hk, j, hj, plane_eq_of_coords (by simpa [gridPt] using hck)
      (by simpa [gridPt] using hz1)⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hzP
    obtain ⟨hz0', hz1'⟩ := mem_gridVEdge_seg_iff.1 hzQ
    exact ⟨i', hi', j, hj, plane_eq_of_coords (by simpa [gridPt] using hz0')
      (by simpa [gridPt] using hz1)⟩
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hzP
    obtain ⟨hz1', hz0'⟩ := mem_gridHEdge_seg_iff.1 hzQ
    exact ⟨i, hi, j', hj', plane_eq_of_coords (by simpa [gridPt] using hz0)
      (by simpa [gridPt] using hz1')⟩
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hzP
    obtain ⟨hz0', hz1'⟩ := mem_gridVEdge_seg_iff.1 hzQ
    obtain rfl : i = i' := hxs.injOn hi hi' (hz0 ▸ hz0')
    have hjj : j ≠ j' := by rintro rfl; exact hPQ rfl
    obtain ⟨k, hk, hck⟩ := same yc n j j' hys (by omega) (by omega) hjj _ hz1 hz1'
    exact ⟨i, hi, k, hk, plane_eq_of_coords (by simpa [gridPt] using hz0)
      (by simpa [gridPt] using hck)⟩

/-- **The grid is a plane graph**, drawn with straight edges. -/
theorem gridGraph_isDrawing (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Graph.IsDrawing (gridGraph xc yc m n) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    have hne : P.Nondeg := gridEdges_nondeg hxs hys hm hn hP
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact pieceListGraph_isLink_self hP
  · rintro P x y v ⟨hP, hxy⟩ hv hvarc
    rw [edgeArc_segmentDrawing] at hvarc
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_vertexSet_gridGraph_iff hm hn).1 hv
    have hend := end_of_gridPt_mem_seg hxs hys hm hn hP ha hb hvarc
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · intro P Q hP hQ hPQ p hpP hpQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    obtain ⟨a, ha, b, hb, rfl⟩ := gridPt_of_mem_two_edges hxs hys hm hn hP hQ hPQ hpP hpQ
    have hvert : gridPt xc yc a b ∈ V(gridGraph xc yc m n) :=
      (mem_vertexSet_gridGraph_iff hm hn).2 ⟨a, ha, b, hb, rfl⟩
    exact ⟨hvert, pieceListGraph_inc hP (end_of_gridPt_mem_seg hxs hys hm hn hP ha hb hpP),
      pieceListGraph_inc hQ (end_of_gridPt_mem_seg hxs hys hm hn hQ ha hb hpQ)⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshFixed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh: the three gaps an audit found

`Schoenflies/SquareMesh.lean` and `Schoenflies/SquareMeshConnected.lean` deliver
`prop:anchored-square-mesh` between them. An adversarial audit of the second found three real
gaps; this module closes what can be closed and states, as explicit hypotheses, what cannot.

## Gap 3 — the dropped subdivision step

The blueprint proves the inner grid 2-connected "by the same ear construction used for `K`,
together with `lem:subdivision-ear-preserve`". `SquareMeshConnected.gridGraph_isTwoConnected`
supplies the ear half (as a chain of `Graph.IsTwoConnected.union`s) and **drops the
subdivision half entirely** — yet the mesh subdivides the grid, at the four corners of the
inner square, at every point `λ zᵢ`, and at every crossing the overlay finds. A grid that is
2-connected before subdivision and unproved after it is of no use to the proposition.

`pieceListGraph_subdivide_isTwoConnected` is the missing half, in the vocabulary of
`Schoenflies/Subdivide.lean`: subdividing a list of segments whose graph is 2-connected, at
any list of points that cut it *cleanly* (`CleanCut`: each point interior to at most one
segment, and interior to none once it is an end of one), leaves the graph 2-connected. It is
`Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a) — iterated,
with the two-edge replacement path built by `isPathGraph_pair`.

For a grid the cleanliness hypothesis is **free**: two distinct grid edges meet only at a grid
point, and a grid point interior to a grid edge does not exist. So
`gridGraph_subdivide_isTwoConnected` has no hypothesis on the points at all.

## Gap 2 — the outer cycle was instantiated at the wrong square

`SquareMeshConnected.edgesCover_gridBoundary_modelCurve` pins the grid to `xc 0 = -1`,
`xc m = 1`, `yc 0 = -1`, `yc n = 1`: a grid spanning **all** of `Q`, whose boundary cycle is
`S`. The audit says such a grid cannot be the mesh, and it is right. The obstruction is
`gridGraph_full_square_aligned_ends` below: for `0 < i < m` the two grid points `(xc i, -1)`
and `(xc i, 1)` both lie on `S` and both carry an internal edge — the vertical edges at the
bottom and top of the column `i` — neither of which lies on `S`. Clause 3 of the proposition
then demands that *both* be fresh points of `u(𝒜)`, and clause 2 demands a grid line through
every old boundary vertex, which manufactures such a pair on the opposite side. Nothing about
`u(𝒜)` supplies pairs of points with a common coordinate: it is merely dense. The theorem is
true; the *instantiation* is wrong.

The blueprint's grid fills the **inner** square `λQ`, `λ < 1`, which touches `S` nowhere;
`edgesCover_gridBoundary_ringSet` is the corrected statement — the boundary cycle of a grid on
`[-r, r]²` occupies `ringSet r` — and `gridGraph_inner_cycle` packages it with the
disjointness from `S` that makes the freshness clauses vacuous for the grid.

## Gap 1 — nothing was proved about `squareMesh` itself

`squareMesh δ fresh anchors` is `overlayGraph` applied to the mesh segments and to a list of
cut points obtained from `exists_cut_points` **by choice**. Its edges are the pieces of a
subdivision nobody can enumerate, so no clause about *its* combinatorics follows from the grid
results, which are about a different graph.

One general fact about `overlayGraph` is missing, and it is stated here as the explicit
hypothesis `SubdividesToPath`: *the overlay edges lying inside a source segment are exactly the
edges of a path of the overlay from one end of that segment to the other.* That is a statement
about `Schoenflies.overlayGraph` and `Schoenflies.subdivide` alone — believed, and
dischargeable, since the pieces of the subdivision of a segment have pairwise disjoint interiors
and cover it, so the distance from one end orders them into a chain. It is not a restatement of
any goal here: the whole content below is the *assembly*, which the hypothesis does not contain.

From it:

* `meshGraph_outer_cycle` / `squareMesh_outer_cycle_of_subdividesToPath` — clause 3 **as a
  cycle**, for the mesh
  itself. The four sides of the outer ring are four overlay paths; three concatenations
  (`Graph.IsPath.append_of_disjoint`) glue them into one path once round `S`, and the first step
  of the *reversed* fourth side is peeled off to close the cycle. The result is a
  `Graph.IsLongCycle` of the mesh whose edges occupy exactly `modelCurve`.
* `squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath` — hence the outer ring is a
  2-connected subgraph
  of the mesh, which is the first step of the blueprint's assembly of clause 5.

**Full 2-connectivity of `squareMesh` is NOT proved here, and is not assumed either.** What
remains is the rest of that assembly: the inner rings as cycles (the same argument, with
`ringPieces r` in place of `ringPieces 1`), the crossing points `r • z` as vertices (which needs
the `MeetsAreCut` clause of `meshPoints`), and then each spoke segment between consecutive rings
attached as an ear — for which one also needs the two arcs of an already-built cycle between two
of its vertices. None of that is short.

The degeneracy the audit asked about is settled, with a proof rather than an assertion:
`not_isTwoConnected_squareMesh_of_fresh_nil`. With no fresh point the mesh is
`meshCount δ ≥ 2` disjoint concentric frames and is not even connected, so clause 5 is **false**
as stated for `squareMesh δ [] anchors`. With exactly one fresh point it is connected but every
interior vertex of the single spoke is a cut vertex; that case is discussed in the section
docstring and not formalised. Every statement of clause 5 for the mesh must therefore carry a
hypothesis giving two distinct fresh points.

## Blueprint

* `lem:subdivision-ear-preserve` — `isPathGraph_pair`, `pieceListGraph_splitAllAt_eq`,
  `pieceListGraph_splitAllAt_isTwoConnected`, `pieceListGraph_subdivide_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 5 for the inner grid, **after** subdivision —
  `gridGraph_subdivide_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3 for the inner grid at the right radius —
  `edgesCover_gridBoundary_ringSet`, `gridGraph_inner_cycle`.
* `prop:anchored-square-mesh`, clauses 3 and 4, the obstruction to a grid on all of `Q` —
  `gridGraph_full_square_aligned_ends`.
* `prop:anchored-square-mesh`, clause 3 as a cycle, for the mesh — `SubdividesToPath`,
  `meshGraph_outer_cycle`, `squareMesh_outer_cycle_of_subdividesToPath`.
* `prop:anchored-square-mesh`, clause 5, the first step for the mesh and the degenerate case —
  `squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath`,
  `not_isTwoConnected_squareMesh_of_fresh_nil`.
* `lem:union-two-connected` is *not* used here; the assembly that would use it is the part left
  open.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A two-edge path graph

The replacement path of a single subdivision: one new vertex `q` between the two ends of the
segment being cut. `Graph.IsTwoConnected.replace_edge_by_path` takes a path of any length, so
this is the only shape needed. -/

/-! ### Cutting a list of segments cleanly

`splitAllAt q l` cuts **every** piece of `l` that has `q` in its interior. To read the result
as one subdivision of one edge — which is what `lem:subdivision-ear-preserve` is about — the
point must be interior to at most one piece; and to keep the replacement path's middle vertex
new, the point must not already be an end. A point that is interior to no piece cuts nothing
at all, and is harmless. -/

/-! ### The inner grid, subdivided

For a grid the cleanliness hypothesis costs nothing. Two distinct grid edges meet only at a
grid point (`gridPt_of_mem_two_edges`), a grid point on a grid edge is an end of it
(`end_of_gridPt_mem_seg`), and an end of a nondegenerate segment is not interior to it. So
*every* point cuts the grid cleanly, and the subdivision theorem applies with no hypothesis on
the cut points at all. -/

variable {xc yc : ℕ → ℝ} {m n : ℕ}

/-! ### The outer cycle of the inner grid, at the right radius

`SquareMeshConnected.edgesCover_gridBoundary_modelCurve` is the `r = 1` case of the theorem
below, and `r = 1` is exactly the case the mesh cannot use. See the module docstring, and
`gridGraph_full_square_aligned_ends` for the obstruction made explicit. -/

/-! ### Why the grid may not span all of `Q`

The audit's second finding, made explicit. -/

/-! ### The mesh needs at least two fresh points

The audit asks whether the plan for clause 5 is false when the fresh set is small. It is, and
this section proves the extreme case rather than asserting it: with no fresh point there is no
spoke, the mesh is `meshCount δ ≥ 2` pairwise disjoint concentric frames, and the graph is not
even connected.

The invariant is the sup norm. Every mesh segment other than a spoke lies on one ring, so with
`fresh = []` both ends of every edge have the same sup norm and a walk cannot change it. The
corner of the outer ring has sup norm `1`, the corner of the innermost ring has `N⁻¹ ≠ 1`.

**With exactly one fresh point `z` the mesh is connected but still not 2-connected**: the spoke
at `z` is the only thing joining the rings, so each of its interior vertices — the crossing
points `(k/N) • z` for `0 < k < N` — is a cut vertex, separating the rings inside it from the
rings outside. That case is *not* formalised here; it needs the crossing points to be vertices,
which needs the `MeetsAreCut` clause of the mesh's cut points, and then a separation argument.
It is recorded so that no consumer states clause 5 for `squareMesh` without a hypothesis
guaranteeing two distinct fresh points. -/

/-- An end of a source segment of the mesh is a vertex of the mesh graph. -/
theorem end_mem_vertexSet_meshGraph {N : ℕ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ meshSegments N fresh) {z : Plane} (hz : z = R.1 ∨ z = R.2) :
    z ∈ V(meshGraph N fresh anchors) := by
  obtain ⟨Q, hQ, -, hend⟩ :=
    subdivide_preserves_end (meshPoints N fresh anchors) ⟨R, hR, subset_rfl, hz⟩
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend⟩

end Schoenflies

/-! ### Concatenating two paths

`Schoenflies/Graph/Walk.lean` has `Graph.IsWalk.append` and no path analogue, because nothing
before this needed one. The general lemma is here; the integrator should hoist it. -/

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-- **Two paths that meet only at the vertex they share concatenate to a path.** -/
theorem IsPath.append_of_disjoint : ∀ {u v : α} {W₁ : List β}, G.IsPath u W₁ v →
    ∀ {w : α} {W₂ : List β}, G.IsPath v W₂ w →
      (∀ x ∈ G.walkVertices u W₁, x ∈ G.walkVertices v W₂ → x = v) →
      G.IsPath u (W₁ ++ W₂) w := by
  intro u v W₁ h₁
  induction h₁ with
  | nil hx => intro w W₂ h₂ _; simpa using h₂
  | @cons u₀ w₀ v₀ e W hl hW hfresh ih =>
    intro w W₂ h₂ hdisj
    refine IsPath.cons hl (ih h₂ fun x hx hx2 =>
      hdisj x (mem_walkVertices_cons_of_mem hl hx) hx2) ?_
    intro hmem
    rw [walkVertices] at hmem
    simp only [List.append_eq, coveredVertices_append, Set.mem_insert_iff,
      Set.mem_union] at hmem
    rcases hmem with hu | hcov
    · exact hfresh (hu ▸ mem_walkVertices_self)
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · -- the second path returns to the source of the first, so the first path is closed
      have : u₀ = v₀ :=
        hdisj u₀ mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact absurd (IsPath.eq_nil_of_eq (this ▸ IsPath.cons hl hW hfresh)) (by simp)

end Graph

namespace Schoenflies

/-! ### The subdivision hypothesis

The one general fact about `overlayGraph` that `Schoenflies/SquareMeshConnected.lean` names as
missing, stated as a `Prop` so that the axiom audit stays a real guarantee and the defect shows
up at the consumer. It is *believed*: the pieces of the subdivision of a nondegenerate segment
have pairwise disjoint interiors and cover it, so the distance from `P.1` orders them into a
chain running from `P.1` to `P.2`. Nothing about the mesh appears in it. -/

/-- The edges of an overlay path along `P` occupy all of `P`. -/
theorem edgesCover_eq_seg {pieces : List Piece} {points : List Plane} {P : Piece}
    (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)) :
    Graph.edgesCover segmentDrawing W = P.seg := by
  refine subset_antisymm ?_ ?_
  · intro z hz
    obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact ((hW Q).1 hQ).2 hzQ
  · intro z hz
    obtain ⟨Q, hQ, hzQ, hsub⟩ := subdivide_covers_source points pieces P hP z hz
    refine Graph.mem_edgesCover ((hW (orientPiece Q)).2
      ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩) ?_
    rw [edgeArc_segmentDrawing, orientPiece_seg]
    exact hzQ

/-! ### The four sides of the outer ring

Names for the four sides of `ringPieces 1` and the six pairwise intersections. Two opposite
sides are disjoint; two adjacent ones meet in their common corner. Everything is
`mem_segment_horiz` / `mem_segment_vert` and `plane_eq_of_coords`. -/

theorem mem_sideT {x : Plane} (h : x ∈ sideT.seg) : x 1 = 1 := (mem_segment_horiz.1 h).1
theorem mem_sideB {x : Plane} (h : x ∈ sideB.seg) : x 1 = -1 := (mem_segment_horiz.1 h).1

theorem sideT_disjoint_sideB {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideB.seg) : False := by
  have := (mem_sideT h).symm.trans (mem_sideB h'); norm_num at this

/-- The four sides occupy `S`. -/
theorem sides_cover : sideT.seg ∪ sideL.seg ∪ sideB.seg ∪ sideR.seg = modelCurve := by
  rw [← ringSet_one, ← cover_ringPieces zero_le_one]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, sideT, sideL, sideB, sideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem side_seg_subset_modelCurve {P : Piece}
    (h : P = sideT ∨ P = sideL ∨ P = sideB ∨ P = sideR) : P.seg ⊆ modelCurve := by
  rw [← sides_cover]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

/-! ### The outer cycle of the mesh

The four sides of the outer ring are four overlay paths; three concatenations glue them into
one path once round `S`, and the last edge of the fourth is peeled off to close the cycle.
Peeling is why the fourth side is reversed: `Graph.IsPath` is built at the *source* end, so its
first step is the one that can be split off, and the first step of the reversed side is the
last edge of the side. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.LocalGrid
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.relabelDrawing_apply _root_.Schoenflies.ArcStrip.collar_left _root_.Schoenflies.ArcStrip.collar_nbhd _root_.Schoenflies.ArcStrip.collar_right _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_apply _root_.Schoenflies.Plane.IsSquareMover.homeomorph_symm_apply _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.Plane.setCoord_self _root_.Schoenflies.Plane.sqNE_one _root_.Schoenflies.Plane.sqNE_zero _root_.Schoenflies.Plane.sqNW_one _root_.Schoenflies.Plane.sqNW_zero _root_.Schoenflies.Plane.sqSE_one _root_.Schoenflies.Plane.sqSE_zero _root_.Schoenflies.Plane.sqSW_one _root_.Schoenflies.Plane.sqSW_zero _root_.Schoenflies.PreArc.deleteVertex_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segGraph_edgeSet _root_.Schoenflies.segGraph_isLink _root_.Schoenflies.segGraph_vertexSet _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.squarePolygon_vertex_one _root_.Schoenflies.squarePolygon_vertex_three _root_.Schoenflies.squarePolygon_vertex_two _root_.Schoenflies.squarePolygon_vertex_zero _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

namespace Schoenflies

/-! ### The diameter of `S`

`S = modelCurve` is the frame of `[-1,1]²`, so any two of its points are at sup distance at
most `2` and hence at Euclidean distance at most `2√2`. That single bound is what makes
`FreshDense fresh δ` vacuous once `δ ≥ 4√2`. -/

/-! ### What does repair clause 5

A side of `S` is a connected subset of `S` whose two ends are `2` apart. If no two fresh points
are distinct then some side avoids all of them — a single point cannot lie on both the top and
the bottom side — and `FreshDense fresh δ` applied to that side forces `4 ≤ δ`. -/

/-- A single point cannot lie on both horizontal sides of `S`, so one of them avoids a
one-point set. -/
theorem exists_side_avoiding (fresh : List Plane) (hsub : ∀ z ∈ fresh, ∀ w ∈ fresh, z = w) :
    ∃ P : Piece, (P = sideT ∨ P = sideB) ∧ ∀ z ∈ fresh, z ∉ P.seg := by
  by_cases hex : ∃ z, z ∈ fresh
  · obtain ⟨z, hz⟩ := hex
    by_cases hzT : z ∈ sideT.seg
    · refine ⟨sideB, Or.inr rfl, fun w hw hwB => ?_⟩
      have : w = z := hsub w hw z hz
      subst this
      exact sideT_disjoint_sideB hzT hwB
    · exact ⟨sideT, Or.inl rfl, fun w hw hwT => hzT (by rwa [← hsub w hw z hz])⟩
  · push Not at hex
    exact ⟨sideT, Or.inl rfl, fun z hz _ => absurd hz (hex z)⟩

/-- **`FreshDense` with a small `δ` gives two distinct fresh points.** This is the hypothesis
`prop:anchored-square-mesh` clause 5 actually needs, and the blueprint supplies it: its
`δ = ε_n = 2^{-n}` is well below `4`. -/
theorem exists_two_distinct_fresh_of_freshDense {fresh : List Plane} {δ : ℝ}
    (hdense : FreshDense fresh δ) (hδ : δ < 4) : ∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hP, havoid⟩ := exists_side_avoiding fresh hcon
  have hseg : P.seg ⊆ modelCurve \ {x | x ∈ fresh} := by
    intro x hx
    refine ⟨side_seg_subset_modelCurve ?_ hx, fun hmem => havoid x hmem hx⟩
    rcases hP with rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))]
  have := hdense P.seg hseg (convex_segment P.1 P.2).isPreconnected
    P.1 (left_mem_segment ℝ _ _) P.2 (right_mem_segment ℝ _ _)
  have := two_le_dist_side hP
  linarith

/-! ### Fewer than two distinct fresh points is always fatal

`SquareMeshFixed.not_isTwoConnected_squareMesh_of_fresh_nil` settles `fresh = []` by showing
the mesh disconnected. The remaining degenerate case — exactly one fresh point — is settled
here, and by the same invariant.

Every edge of the mesh is a subsegment of a source segment, and a source segment is either a
side of a ring, on which the sup norm is constant, or the spoke at a fresh point `z`, along
which the only point of sup norm `1` is `z` itself. So once `z` is deleted, **no** edge of the
mesh joins a vertex of sup norm `1` to a vertex of smaller sup norm: `z` is a cut vertex. -/

end Schoenflies

/-! ### A spanning 2-connected subgraph makes the whole graph 2-connected

The form in which every assembly out of `lem:union-two-connected` is finished: a chain of
unions produces *some* graph, and what the consumer wants is 2-connectivity of the graph it
started from. As long as the assembled graph is a subgraph that misses no vertex, the two
coincide — extra edges can only help connectivity. -/

namespace Graph

variable {α β : Type*} {H K : Graph α β}

/-- **2-connectivity passes up to a graph with the same vertices.** -/
theorem IsTwoConnected.of_le_of_vertexSet_subset (hH : H.IsTwoConnected) (hHK : H ≤ K)
    (hV : V(K) ⊆ V(H)) : K.IsTwoConnected where
  hasThreeVertices := hH.hasThreeVertices.mono hHK.vertexSet_mono
  connected := hH.connected.of_spanning_le hHK hV
  deleteVerts_connected := fun x _ =>
    (hH.deleteVerts_connected' x).of_spanning_le (deleteVerts_mono hHK _) (by
      simp only [vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hV)

end Graph

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

/-- **The grid is a plane graph**, drawn with straight edges. -/
theorem localGrid_isDrawing (hs : 0 < s) (hk : 1 ≤ k) :
    Graph.IsDrawing (localGrid p s k) segmentDrawing :=
  gridGraph_isDrawing ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk

/-! ### Fineness

The one quantitative clause: every closed grid rectangle is smaller than `ε`. Stated twice —
for the closed rectangle itself, which is the blueprint's wording, and for any connected subset
of `W` that avoids the grid, which is the form a face of the overlay arrives in. -/

/-- The grid line at index `i` is part of the grid: a point of `W` whose first coordinate is a
grid coordinate lies on the grid. -/
theorem mem_cover_of_coord_eq (hs : 0 < s) (hk : 1 ≤ k) {z : Plane} {i : ℕ} (hi : i ≤ k)
    (hz : z ∈ Plane.closedSquare p s) (hz0 : z 0 = localGridX p s k i) :
    z ∈ cover (localGridEdges p s k) := by
  have hymono : ∀ j, j < k → localGridY p s k j ≤ localGridY p s k (j + 1) :=
    fun j _ => (localGridY_strictMono hs hk).monotone (Nat.le_succ j)
  have hbounds := Plane.closedSquare_eq_inter p s ▸ hz
  obtain ⟨-, h3, h4⟩ : _ ∧ (p 1 - s ≤ z 1) ∧ (z 1 ≤ p 1 + s) := hbounds
  have hmem : z ∈ segment ℝ (gridPt (localGridX p s k) (localGridY p s k) i 0)
      (gridPt (localGridX p s k) (localGridY p s k) i k) := by
    refine mem_segment_vert.2 ⟨hz0, ?_⟩
    rw [segment_eq_Icc ((localGridY_strictMono hs hk).monotone (Nat.zero_le k))]
    rw [localGridY_zero, localGridY_last hk]
    exact ⟨h3, h4⟩
  rw [← iUnion_gridVEdge_seg hk hymono i] at hmem
  simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hmem
  obtain ⟨j, hj, hzj⟩ := hmem
  exact mem_cover_iff.2 ⟨_, gridVEdge_mem_gridEdges hi hj hk, hzj⟩

/-- The same for the second coordinate. -/
theorem mem_cover_of_coord_eq' (hs : 0 < s) (hk : 1 ≤ k) {z : Plane} {j : ℕ} (hj : j ≤ k)
    (hz : z ∈ Plane.closedSquare p s) (hz1 : z 1 = localGridY p s k j) :
    z ∈ cover (localGridEdges p s k) := by
  have hxmono : ∀ i, i < k → localGridX p s k i ≤ localGridX p s k (i + 1) :=
    fun i _ => (localGridX_strictMono hs hk).monotone (Nat.le_succ i)
  have hbounds := Plane.closedSquare_eq_inter p s ▸ hz
  obtain ⟨⟨h1, h2⟩, -⟩ : ((p 0 - s ≤ z 0) ∧ (z 0 ≤ p 0 + s)) ∧ _ := hbounds
  have hmem : z ∈ segment ℝ (gridPt (localGridX p s k) (localGridY p s k) 0 j)
      (gridPt (localGridX p s k) (localGridY p s k) k j) := by
    refine mem_segment_horiz.2 ⟨hz1, ?_⟩
    rw [segment_eq_Icc ((localGridX_strictMono hs hk).monotone (Nat.zero_le k))]
    rw [localGridX_zero, localGridX_last hk]
    exact ⟨h1, h2⟩
  rw [← iUnion_gridHEdge_seg hk hxmono j] at hmem
  simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hmem
  obtain ⟨i, hi, hzi⟩ := hmem
  exact mem_cover_iff.2 ⟨_, gridHEdge_mem_gridEdges hi hj hk, hzi⟩

/-- **`prop:local-grid-attachment` clause 3, in the form the overlay consumes.** A connected
subset of the window `W` that avoids the grid has diameter less than `√2 · (2s/k)`: it is
trapped inside one open grid rectangle, coordinate by coordinate. -/
theorem dist_lt_of_avoiding_localGrid (hs : 0 < s) (hk : 1 ≤ k) {F : Set Plane}
    (hF : IsPreconnected F) (hFW : F ⊆ Plane.closedSquare p s)
    (havoid : ∀ z ∈ F, z ∉ cover (localGridEdges p s k)) {x y : Plane}
    (hx : x ∈ F) (hy : y ∈ F) : dist x y < Real.sqrt 2 * (2 * s / k) := by
  have hstep := localGrid_step_pos hs hk
  have hcoord : ∀ (m : Fin 2) (a : ℝ), (∀ i ≤ k, uniformCoord a (2 * s / k) i ∉
      ((fun z : Plane => z m) '' F)) →
      (∀ z ∈ F, a ≤ z m ∧ z m ≤ a + k * (2 * s / k)) →
      |x m - y m| < 2 * s / k := by
    intro m a havd hbd
    refine abs_sub_lt_of_avoiding hstep (hF.image _ (Plane.continuous_coord m).continuousOn)
      ?_ havd ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_Icc.2 (hbd z hz)
  have hbdX : ∀ z ∈ F, (p 0 - s) ≤ z 0 ∧ z 0 ≤ (p 0 - s) + k * (2 * s / k) := by
    intro z hz
    have hbounds := Plane.closedSquare_eq_inter p s ▸ hFW hz
    obtain ⟨⟨h1, h2⟩, -⟩ : ((p 0 - s ≤ z 0) ∧ (z 0 ≤ p 0 + s)) ∧ _ := hbounds
    refine ⟨h1, ?_⟩
    have := localGridX_last (p := p) (s := s) hk
    simp only [localGridX, uniformCoord] at this
    linarith
  have hbdY : ∀ z ∈ F, (p 1 - s) ≤ z 1 ∧ z 1 ≤ (p 1 - s) + k * (2 * s / k) := by
    intro z hz
    have hbounds := Plane.closedSquare_eq_inter p s ▸ hFW hz
    obtain ⟨-, h3, h4⟩ : _ ∧ (p 1 - s ≤ z 1) ∧ (z 1 ≤ p 1 + s) := hbounds
    refine ⟨h3, ?_⟩
    have := localGridY_last (p := p) (s := s) hk
    simp only [localGridY, uniformCoord] at this
    linarith
  refine dist_lt_of_supNorm_bounds (hcoord 0 (p 0 - s) ?_ hbdX) (hcoord 1 (p 1 - s) ?_ hbdY)
  · rintro i hi ⟨z, hz, hzeq⟩
    exact havoid z hz (mem_cover_of_coord_eq hs hk hi (hFW hz)
      (by simpa [localGridX] using hzeq))
  · rintro j hj ⟨z, hz, hzeq⟩
    exact havoid z hz (mem_cover_of_coord_eq' hs hk hj (hFW hz)
      (by simpa [localGridY] using hzeq))

/-! ### Choosing the mesh

`prop:local-grid-attachment` clause 3 asks for rectangles of diameter `< ε`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GridAttach
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
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

/-- Cut points for a family of segments, together with prescribed extra points that are to
become vertices whatever else happens. Enlarging the list produced by `exists_cut_points` is
harmless (`EndsAreCut.mono`, `MeetsAreCut.mono`) and is what makes the two common vertices of
`lem:union-two-connected` available. -/
noncomputable def attachPoints (pieces : List Piece) (extra : List Plane) : List Plane :=
  extra ++ (exists_cut_points pieces).choose

theorem mem_attachPoints_of_mem {pieces : List Piece} {extra : List Plane} {x : Plane}
    (hx : x ∈ extra) : x ∈ attachPoints pieces extra := List.mem_append_left _ hx

theorem attachPoints_endsAreCut (pieces : List Piece) (extra : List Plane) :
    EndsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.1.mono (List.subset_append_right _ _)

theorem attachPoints_meetsAreCut (pieces : List Piece) (extra : List Plane) :
    MeetsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.2.mono (List.subset_append_right _ _)

/-- **The overlay of `lem:polygonal-overlay`, with the convention of
`rem:polygonal-overlay-convention`**: every intersection of the listed segments is a vertex, and
so is every prescribed extra point. -/
noncomputable def attachGraph (pieces : List Piece) (extra : List Plane) : Graph Plane Piece :=
  overlayGraph pieces (attachPoints pieces extra)

instance attachGraph_finite (pieces : List Piece) (extra : List Plane) :
    Graph.Finite (attachGraph pieces extra) := overlayGraph_finite _ _

/-! ### Clause 1: the open nonboundary part is connected

The joining loop, transported from sets to the graph. What the graph occupies is
`cover pieces` (`attachGraph_pointSet`), so the whole statement is about covers. -/

/-! ### Clause 2: the graph contains the grid, and clause 3: the grid is fine -/

/-! ### From the crosscut to two common vertices

*"Since `E` contains `J`, after subdivision `Γ ∪ E` and `K` have at least two common
vertices."* — the step that turns each degenerate case into the main one. Its content is the
swallowing clause of `exists_crosscut`: the grid edge's relative interior is a connected subset
of `ℓ ∩ F` through the chosen point, hence lies inside the crosscut's open part, hence the whole
closed grid edge lies inside the closed crosscut. -/

/-! ## `prop:local-grid-attachment`, assembled

One graph, and each clause of the proposition a theorem about it. The graph is a `def` and not
an existential: `thm:finite-transfer`(a) takes `H` as an input and reads its drawing, its
2-connectivity and its point set separately. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.LimitMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite _root_.Schoenflies.meshGraph_finite _root_.Schoenflies.squareMesh_finite
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The limit homeomorphism of the interiors

The blueprint opens this section with a sentence that is an instruction to the formalizer: "We
now forget how the decompositions were constructed and use only their nesting, matching, and
shrinking properties." This module takes it literally. `LimitTower` is a structure recording
exactly those properties — a sequence of matched cell structures with two realizations each, a
`Realization.Refines` instance between consecutive stages on each side sharing one parent map,
nested skeleton homeomorphisms, and the two shrinking hypotheses of `prop:shrinking-stars` — and
everything from the definition of `F` to `prop:interior-homeomorphism` is proved against it.
Nothing below mentions a mesh, a grid, or a constructor. The still-open construction has to
produce one `LimitTower`; none of the analysis waits for it.

## What is *not* a field

Three things the task list expected to appear as hypotheses turned out to be derivable and are
therefore proved here rather than assumed.

* **`lem:outer-incidence`.** `docs/ROADMAP.md` records it as done in `CombinatorialInvariance.lean`
  under `outerEdge_face_corresponds`; that is a different statement (assertion (vi) of
  `lem:cellulation-invariants`, transported). The real `lem:outer-incidence` — `closure σ` meets
  `C` iff some outer cell is a subcell of `σ` iff `closure σ'` meets `S` — is proved below as
  `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and, for stars,
  `LimitTower.star_meets_bdry_iff`. The one geometric input it needs is
  `Realization.outerSet_eq_iUnion_cell`: the realized outer cycle is exactly the union of the
  open cells of the outer cells, which is a consequence of the two `Realization` clauses
  `cell_vertex` and `cell_edge` and holds for any subcomplex.
* **Assertion (vii) of `lem:cellulation-invariants`** (every 2-cell boundary a Jordan curve with
  the open cell its bounded region). The limit argument was expected to need it, through
  assertion (viii). It does not: the only use is "a 2-cell is not a proper subcell of a 2-cell",
  and that is `CombInvariants.face_maximal`, which is already an inductive invariant on `main`.
  There is therefore no field for (vii) and no dependency on it.
* **`prop:target-skeleton-dense`.** The blueprint's surjectivity proof goes through the density
  of the target skeleton and a compactness argument in `C ∪ D`. That is not needed: the sets
  `⋂ₙ St_{Γₙ}(car_{Γ'ₙ}(y))` — the *source* stars of the *target* carriers of `y` — are a nested
  sequence of nonempty compacts, and any point of their intersection is already a preimage of
  `y`. `prop:target-skeleton-dense` is proved anyway, because the boundary-continuity module
  cites it, but it is not on the critical path to `prop:F-surjective`.

## The two shrinking hypotheses are not symmetric

`prop:shrinking-stars` gives *pointwise* convergence of the source star diameters and *uniform*
convergence of the target ones. The asymmetry is real and is used: `F` is defined, and continuous,
on the whole closed domain (only the uniform bound enters), whereas injectivity and the continuity
of the inverse hold on the open region (they need the pointwise bound at a point of `D`).

One hypothesis that the blueprint does not state is carried throughout: the closed domains are
bounded. It is not optional — `Metric.diam` is `0` on an unbounded set, so without it the star
diameter bounds are false rather than weak — and it is trivially true for a closed Jordan domain.

## Blueprint

All of the following live in `Schoenflies.CellStructure`.

* `LimitTower` — the abstraction of the head of the section: "we now forget how the
  decompositions were constructed and use only their nesting, matching, and shrinking
  properties".
* The definition of `F` (tex "The limit homeomorphism of the interiors") —
  `LimitTower.F`, with `LimitTower.iInter_tgtStar_eq` its characterisation
  (`lem:nested-compact` applied to the nested stars `LimitTower.tgtStar`),
  `LimitTower.F_mem_tgtStar` and `LimitTower.eq_F_of_mem_iInter`.
* `lem:outer-incidence` — `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and
  `Realization.IsCellDecomposition.star_meets_outer_iff`, with the matched form the limit
  argument cites, `LimitTower.star_meets_bdry_iff`. Their geometric input is
  `Realization.outerSet_eq_iUnion_cell`.
* `prop:skeleton-agreement` — `LimitTower.F_eq_skelHomeo`.
* `prop:F-continuous` — `LimitTower.continuousOn_F`, on the *closed* domain.
* `prop:image-interior` — `LimitTower.F_mem_region'`.
* `prop:F-injective` — `LimitTower.injOn_F`.
* `prop:target-skeleton-dense` — `LimitTower.exists_mem_tgt_skeletonSet`.
* `prop:F-surjective` — `LimitTower.exists_mem_region_F_eq`, through `LimitTower.preStar` and
  `LimitTower.F_eq_of_mem_iInter_preStar`.
* `lem:exact-cell-correspondence` — `LimitTower.image_cell`, with the corollary the inverse
  argument actually uses, `LimitTower.tgt_carrier_F`.
* `prop:inverse-continuous` — `LimitTower.continuousOn_inv`, on the explicit inverse
  `LimitTower.inv`.
* `prop:interior-homeomorphism` — `LimitTower.isHomeoOn_F` and, with the skeleton clause,
  `LimitTower.interior_homeomorphism`; in the `Schoenflies.IsHomeoOn` shape that `Endgame.lean`
  and the boundary-continuity module consume.
* `lem:cell-neighborhood` is used, not restated: it is
  `Realization.IsCellDecomposition.sub_carrier_of_mem_cellNbhd` in `RefinementStars.lean`, and
  the cross-realization form the limit map needs is
  `LimitTower.tgtStar_subset_of_mem_cellNbhd`.
-/

open Set Metric Bornology Filter
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ### The realized skeleton and outer cycle, cell by cell

`Realization.skeletonSet` and `Realization.outerSet` are defined as point sets of drawn graphs.
The limit argument needs them as unions of *open cells*, because that is the form in which they
interact with `IsCellDecomposition`: "the carrier of any point of `C` is an outer cell" is the
first sentence of the blueprint's proof of `lem:outer-incidence`, and it is exactly this
rewriting. -/

/-- Every outer cell is a cell. -/
theorem outerCells_subset_cells : S.outerCells ⊆ S.cells := by
  rintro κ (hv | he)
  · exact S.mem_cells_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hv)
  · exact S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono he)

/-- A cell that is neither a 0-cell nor a 1-cell of the skeleton is a 2-cell — the three
collections exhaust `cells`. -/
theorem mem_faces_of_notMem_skel {σ : γ} (hσ : σ ∈ S.cells) (h : σ ∉ V(S.skel) ∪ E(S.skel)) :
    σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd hσ h
  · exact hσ

/-- A proper subcell of a 2-cell is a 0- or 1-cell: nothing but the 2-cell itself is a 2-cell
below it. -/
theorem mem_skel_of_sub_face (hS : S.CombInvariants) {σ F : γ}
    (hσ : σ ∈ S.cells) (hsub : S.sub σ F) (hne : σ ≠ F) : σ ∈ V(S.skel) ∪ E(S.skel) := by
  rcases hσ with hσ | hσ
  · exact hσ
  · exact absurd (hS.face_maximal hσ hsub).symm hne

/-- A 2-cell is never an outer cell: outer cells are 0- and 1-cells of the skeleton. -/
theorem notMem_outerCells_of_mem_faces {F : γ} (hF : F ∈ S.faces) : F ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.faces_ne_vertexSet hF (S.outerGraph_le.vertexSet_mono hv) rfl
  · exact S.faces_ne_edgeSet hF (S.outerGraph_le.edgeSet_mono he) rfl

namespace Realization

variable (R : S.Realization)

/-- The realized point set of a subcomplex of the skeleton is the union of the open cells of its
0- and 1-cells. A drawn edge is its open cell together with the two 0-cells at its ends, and
those ends belong to the subcomplex whenever the edge does. -/
theorem pointSet_map_eq_iUnion_cell {H : Graph γ γ} (hH : H ≤ S.skel) :
    Graph.pointSet (H.map R.pos) R.drawing = ⋃ κ ∈ V(H) ∪ E(H), R.cell κ := by
  refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun κ hκ => ?_)
  · rcases hz with hz | hz
    · -- a drawn 0-cell
      rw [Graph.vertexSet_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Set.mem_biUnion (Or.inl hv)
        (by rw [R.cell_vertex (hH.vertexSet_mono hv)]; rfl)
    · -- a point of a drawn 1-cell: either interior to it, or one of its two ends
      rw [Graph.edgeSet_map] at hz
      obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      by_cases hend : z ∈ ({R.pos a, R.pos b} : Set Plane)
      · rcases hend with rfl | rfl
        · exact Set.mem_biUnion (Or.inl hl.left_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.left_mem)]; rfl)
        · exact Set.mem_biUnion (Or.inl hl.right_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.right_mem)]; rfl)
      · exact Set.mem_biUnion (Or.inr he) (by rw [R.cell_edge (hl.mono hH)]; exact ⟨hze, hend⟩)
  · rcases hκ with hv | he
    · rw [R.cell_vertex (hH.vertexSet_mono hv)]
      exact Set.singleton_subset_iff.2 (Graph.vertexSet_subset_pointSet
        (by rw [Graph.vertexSet_map]; exact ⟨κ, hv, rfl⟩))
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      rw [R.cell_edge (hl.mono hH)]
      exact Set.Subset.trans Set.sdiff_subset
        (Graph.edgeArc_subset_pointSet (by rw [Graph.edgeSet_map]; exact he))

/-- **The realized 1-skeleton is the union of the open 0- and 1-cells.** -/
theorem skeletonSet_eq_iUnion_cell :
    R.skeletonSet = ⋃ κ ∈ V(S.skel) ∪ E(S.skel), R.cell κ :=
  R.pointSet_map_eq_iUnion_cell le_rfl

/-- **The realized outer cycle is the union of the open outer cells.** This is the sentence "`C`
is exactly the union of the outer vertices and the open outer edges" at the head of the
blueprint's proof of `lem:outer-incidence`. -/
theorem outerSet_eq_iUnion_cell : R.outerSet = ⋃ κ ∈ S.outerCells, R.cell κ :=
  R.pointSet_map_eq_iUnion_cell S.outerGraph_le

variable {R}

theorem cell_subset_outerSet {κ : γ} (hκ : κ ∈ S.outerCells) : R.cell κ ⊆ R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell]; exact Set.subset_biUnion_of_mem hκ

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ : γ} {x : Plane}

/-- Off the outer cycle, the open cell of a cell that is not an outer cell. Open cells are
disjoint and the outer cycle is the union of the outer ones, so a cell's open part misses the
outer cycle exactly when the cell is not outer. -/
theorem cell_disjoint_outerSet (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hout : σ ∉ S.outerCells) : Disjoint (R.cell σ) R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell, Set.disjoint_iUnion₂_right]
  intro κ hκ
  exact h.disjoint hσ (outerCells_subset_cells hκ) (fun hcon => hout (hcon ▸ hκ))

/-- An open cell is disjoint from the union of the open cells of any collection of cells not
containing it. This is how `IsCellDecomposition` sees the realized skeleton and the realized
outer cycle, once those have been rewritten as unions of open cells. -/
theorem cell_disjoint_biUnion (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) {K : Set γ}
    (hK : K ⊆ S.cells) (hnot : σ ∉ K) : Disjoint (R.cell σ) (⋃ κ ∈ K, R.cell κ) := by
  rw [Set.disjoint_iUnion₂_right]
  exact fun κ hκ => h.disjoint hσ (hK hκ) fun hcon => hnot (hcon ▸ hκ)

/-- **An open 2-cell never meets the realized skeleton.** -/
theorem cell_disjoint_skeletonSet (h : R.IsCellDecomposition D) {F : γ} (hF : F ∈ S.faces) :
    Disjoint (R.cell F) R.skeletonSet := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine h.cell_disjoint_biUnion (S.mem_cells_of_mem_faces hF) (fun κ hκ => ?_) ?_
  · rcases hκ with hv | he
    exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]
  · rintro (hv | he)
    exacts [S.faces_ne_vertexSet hF hv rfl, S.faces_ne_edgeSet hF he rfl]

/-- The realized skeleton lies in the closed domain. -/
theorem skeletonSet_subset_domain (h : R.IsCellDecomposition D) : R.skeletonSet ⊆ D := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine Set.iUnion₂_subset fun κ hκ => h.cell_subset_domain ?_
  rcases hκ with hv | he
  exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]

end IsCellDecomposition

end Realization

/-! ### The tower of matched cellulations

Every field below is an obligation on whoever eventually constructs the sequence of
decompositions, and there is nothing here that the limit argument does not use. -/

/-- **The nesting, matching and shrinking properties of a sequence of matched cellulations**, and
nothing else. The blueprint's "we now forget how the decompositions were constructed" is this
structure.

`str n` is the stage-`n` abstract matched cell structure; `src n` and `tgt n` are its two
realizations, in the closed Jordan domain `dom` and in the closed square `dom'`; `skelHomeo n` is
the stage-`n` skeleton homeomorphism `g_n`. Consecutive stages are related by a pair of
`Realization.Refines` instances **sharing one parent map** `par n` — that sharing is
`lem:refinement-compatibility`(c), "corresponding cells have corresponding parents", under the
representation of `CombinatorialInvariance.lean`, where cells are abstract names.

The shrinking clauses are `prop:shrinking-stars`, and they are deliberately asymmetric, exactly
as the blueprint states them: the *target* star diameters are bounded uniformly by a null
sequence `eps`, while the *source* star diameters are only assumed to tend to zero pointwise, and
only at points of the open region. -/
structure LimitTower (γ : Type*) [Nonempty γ] where
  /-- The stage-`n` abstract matched cell structure. -/
  str : ℕ → CellStructure γ
  /-- The source realization, in the closed Jordan domain. -/
  src : ∀ n, (str n).Realization
  /-- The target realization, in the closed square. -/
  tgt : ∀ n, (str n).Realization
  /-- The stage-`n` skeleton homeomorphism `g_n`. -/
  skelHomeo : ∀ n, SkeletonHomeo (src n) (tgt n)
  /-- The composite parent map from stage `n + 1` to stage `n`, shared by the two sides. -/
  par : ℕ → γ → γ
  /-- The closed source domain `C ∪ D`. -/
  dom : Set Plane
  /-- The source outer curve `C`. -/
  bdry : Set Plane
  /-- The closed target domain `Q`. -/
  dom' : Set Plane
  /-- The target outer curve `S`. -/
  bdry' : Set Plane
  /-- The uniform target mesh: `2 ε_n` of the blueprint. -/
  eps : ℕ → ℝ
  /-- **Assertions (i) and (ii)** on the source side. -/
  srcDecomp : ∀ n, (src n).IsCellDecomposition dom
  /-- **Assertions (i) and (ii)** on the target side. -/
  tgtDecomp : ∀ n, (tgt n).IsCellDecomposition dom'
  /-- **Assertions (iii), (v), (vi)** and the rest of the combinatorial invariants. -/
  comb : ∀ n, (str n).CombInvariants
  /-- Consecutive source stages refine, along `par n`. -/
  srcRefines : ∀ n, (src (n + 1)).Refines (src n) (par n)
  /-- Consecutive target stages refine, along the *same* `par n`. -/
  tgtRefines : ∀ n, (tgt (n + 1)).Refines (tgt n) (par n)
  /-- The realized source outer cycle is `C`, at every stage. -/
  srcOuterSet : ∀ n, (src n).outerSet = bdry
  /-- The realized target outer cycle is `S`, at every stage. -/
  tgtOuterSet : ∀ n, (tgt n).outerSet = bdry'
  /-- `C ∪ D` is closed. -/
  isClosed_dom : IsClosed dom
  /-- `Q` is closed. -/
  isClosed_dom' : IsClosed dom'
  /-- `C ∪ D` is bounded. Not in the blueprint, and not optional: `Metric.diam` is `0` on an
  unbounded set. -/
  isBounded_dom : IsBounded dom
  /-- `Q` is bounded, for the same reason. -/
  isBounded_dom' : IsBounded dom'
  /-- `D = Int(C)` is open. -/
  isOpen_int : IsOpen (dom \ bdry)
  /-- `Q°` is open. -/
  isOpen_int' : IsOpen (dom' \ bdry')
  /-- The realized source skeletons grow. -/
  skeletonSet_mono : ∀ n, (src n).skeletonSet ⊆ (src (n + 1)).skeletonSet
  /-- **The skeleton maps are nested**: "an edge subdivision leaves the skeleton map unchanged as
  a point map, and a 2-cell split extends it by the chosen homeomorphism on the new ear". -/
  skelHomeo_succ : ∀ n,
    Set.EqOn (skelHomeo (n + 1)).toFun (skelHomeo n).toFun (src n).skeletonSet
  /-- **`prop:shrinking-stars`, the uniform half**: every stage-`n` target star has diameter at
  most `eps n`. -/
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (str n).cells → diam ((tgt n).star σ) ≤ eps n
  /-- …and `eps` is a null sequence. -/
  tendsto_eps : Tendsto eps atTop (nhds 0)
  /-- **`prop:shrinking-stars`, the pointwise half**: at every point of the open region the
  source star diameters tend to zero. -/
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ dom \ bdry →
    Tendsto (fun n => diam ((src n).star ((src n).carrier x))) atTop (nhds 0)

namespace LimitTower

variable [Nonempty γ] (L : LimitTower γ) {x y z : Plane} {m n : ℕ} {σ : γ}

/-- The open source region `D = Int(C)`. -/
def region : Set Plane := L.dom \ L.bdry

/-- The open target region `Q°`. -/
def region' : Set Plane := L.dom' \ L.bdry'

/-- `St_{Γ'_n}(σ'_n(x))`, written `T_n(x)` in the blueprint: the closed target star of the cell
corresponding to the source carrier of `x`. -/
def tgtStar (n : ℕ) (x : Plane) : Set Plane := (L.tgt n).star ((L.src n).carrier x)

/-- `St_{Γ_n}(x)`, the closed source star of the source carrier of `x`. -/
def srcStar (n : ℕ) (x : Plane) : Set Plane := (L.src n).star ((L.src n).carrier x)

variable {L}

theorem region_subset_dom : L.region ⊆ L.dom := Set.sdiff_subset

theorem region'_subset_dom' : L.region' ⊆ L.dom' := Set.sdiff_subset

theorem isOpen_region (L : LimitTower γ) : IsOpen L.region := L.isOpen_int

theorem isOpen_region' (L : LimitTower γ) : IsOpen L.region' := L.isOpen_int'

theorem tgtStar_eq (n : ℕ) (x : Plane) :
    L.tgtStar n x = (L.tgt n).star ((L.src n).carrier x) := rfl

/-! #### Stars of the tower -/

theorem srcStar_subset_dom (n : ℕ) (σ : γ) : (L.src n).star σ ⊆ L.dom :=
  ((L.srcDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom.closure_subset

theorem tgtStar_subset_dom' (n : ℕ) (σ : γ) : (L.tgt n).star σ ⊆ L.dom' :=
  ((L.tgtDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom'.closure_subset

theorem isBounded_tgt_star (n : ℕ) (σ : γ) : IsBounded ((L.tgt n).star σ) :=
  (L.tgtDecomp n).isBounded_star (L.comb n) L.isBounded_dom'

theorem isBounded_src_star (n : ℕ) (σ : γ) : IsBounded ((L.src n).star σ) :=
  (L.srcDecomp n).isBounded_star (L.comb n) L.isBounded_dom

theorem isBounded_srcStar (n : ℕ) (x : Plane) : IsBounded (L.srcStar n x) :=
  isBounded_src_star n _

theorem tendsto_diam_srcStar_point (hx : x ∈ L.region) :
    Tendsto (fun n => diam (L.srcStar n x)) atTop (nhds 0) :=
  L.tendsto_diam_srcStar hx

theorem isCompact_tgtStar (n : ℕ) (x : Plane) : IsCompact (L.tgtStar n x) :=
  (L.tgtDecomp n).isCompact_star (L.comb n) L.isBounded_dom'

/-! #### The limit map -/

open scoped Classical in
/-- **The limit map `F`**: the unique point of `⋂ₙ T_n(x)`. Junk off the closed domain; every
lemma about it carries `x ∈ L.dom`. -/
noncomputable def F (L : LimitTower γ) (x : Plane) : Plane :=
  if h : ∃ p, ⋂ n, L.tgtStar n x = {p} then h.choose else 0

/-! #### Agreement with the finite skeleton maps

The skeleton maps are nested, so `g_n = g_N` on `G_N` for every `n ≥ N`; at each such stage the
skeleton map carries the carrier of `x` onto the corresponding target cell, which sits inside
`T_n(x)`. The intersection of the `T_n(x)` is the single point `F x`. -/

theorem skeletonSet_mono_le (hmn : m ≤ n) : (L.src m).skeletonSet ⊆ (L.src n).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (L.skeletonSet_mono n)

/-- **The skeleton maps are nested**: `g_n = g_m` on `G_m` whenever `m ≤ n`. -/
theorem skelHomeo_eqOn (hmn : m ≤ n) :
    Set.EqOn (L.skelHomeo n).toFun (L.skelHomeo m).toFun (L.src m).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ n hmn ih =>
    intro w hw
    rw [L.skelHomeo_succ n (skeletonSet_mono_le hmn hw), ih hw]

/-! #### Continuity -/

/-! #### The image lies in the interior -/

/-! #### Injectivity -/

/-! #### Density of the target skeleton -/

/-- An open cell that is not an outer cell lies in the open region: open cells are disjoint and
`S` is the union of the open outer ones. -/
theorem tgt_cell_subset_region' (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.tgt n).cell σ ⊆ L.region' := by
  intro w hw
  refine ⟨(L.tgtDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.tgtOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_outerSet hσ hout) hw hb

/-! #### Surjectivity

The blueprint reaches `y` through the density of the target skeleton and a compactness argument
in `C ∪ D`. The route taken here is shorter and needs neither: the *source* stars of the
*target* carriers of `y` are themselves a nested sequence of nonempty compacts, and every point
of their intersection is already a preimage of `y`. -/

/-- `St_{Γ_n}(car_{Γ'_n}(y))`: the source star of the target carrier of `y`. This is the set the
blueprint calls `K`, read at every stage instead of at one. -/
def preStar (L : LimitTower γ) (n : ℕ) (y : Plane) : Set Plane :=
  (L.src n).star ((L.tgt n).carrier y)

theorem isCompact_preStar (n : ℕ) (y : Plane) : IsCompact (L.preStar n y) :=
  (L.srcDecomp n).isCompact_star (L.comb n) L.isBounded_dom

/-! #### Exact cell correspondence -/

/-- The source counterpart of `tgt_cell_subset_region'`. -/
theorem src_cell_subset_region (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.src n).cell σ ⊆ L.region := by
  intro w hw
  refine ⟨(L.srcDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.srcOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_outerSet hσ hout) hw hb

/-! #### The inverse, and the interior homeomorphism -/

open scoped Classical in
/-- **The inverse of `F`**, as an explicit function `Plane → Plane` rather than a bundled
`Homeomorph`: a chosen preimage in `D`. Surjectivity makes the choice possible and injectivity
makes it irrelevant. `Endgame.lean` consumes the pair `(F, inv)` in the `IsHomeoOn` shape, which
needs the inverse named. -/
noncomputable def inv (L : LimitTower γ) (y : Plane) : Plane :=
  if h : ∃ x, x ∈ L.region ∧ L.F x = y then h.choose else 0

theorem inv_spec (h : ∃ x, x ∈ L.region ∧ L.F x = y) :
    L.inv y ∈ L.region ∧ L.F (L.inv y) = y := by
  rw [inv, dif_pos h]
  exact h.choose_spec

end LimitTower

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Windows
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.attachGraph_finite
attribute [-simp] _root_.Graph.relabelDrawing_apply _root_.Schoenflies.CellStructure.Realization.cellUnion_empty _root_.Schoenflies.CellStructure.Realization.cellUnion_singleton _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_invFun _root_.Schoenflies.CellStructure.SplitData.EarHomeo.symm_toFun _root_.Schoenflies.CellStructure.SplitData.edgeSet_earGraph _root_.Schoenflies.CellStructure.SplitData.realize_cell _root_.Schoenflies.CellStructure.SplitData.realize_drawing _root_.Schoenflies.CellStructure.SplitData.realize_pos _root_.Schoenflies.CellStructure.SplitData.splitHomeo_invFun _root_.Schoenflies.CellStructure.SplitData.splitHomeo_toFun _root_.Schoenflies.CellStructure.SplitData.vertexSet_earGraph _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ _root_.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_invFun _root_.Schoenflies.CellStructure.SubdivData.realizeHomeo_toFun _root_.Schoenflies.CellStructure.SubdivData.realizePos_newVertex _root_.Schoenflies.CellStructure.SubdivData.realize_cell _root_.Schoenflies.CellStructure.SubdivData.realize_drawing _root_.Schoenflies.CellStructure.SubdivData.realize_pos _root_.Schoenflies.HexData.draw_chord _root_.Schoenflies.HexData.draw_edge _root_.Schoenflies.HexData.edgeArc_chord _root_.Schoenflies.HexData.edgeArc_edge _root_.Schoenflies.HexData.point_vert _root_.Schoenflies.HexData.realization_cell _root_.Schoenflies.HexData.realization_drawing _root_.Schoenflies.HexData.realization_pos _root_.Schoenflies.InitialData.skeletonHomeo_toFun _root_.Schoenflies.InitialData.src_chordSet _root_.Schoenflies.InitialData.src_pos_four _root_.Schoenflies.InitialData.src_pos_one _root_.Schoenflies.InitialData.tgt_pos_four _root_.Schoenflies.InitialData.tgt_pos_one _root_.Schoenflies.InitialData.u_apply_a _root_.Schoenflies.InitialData.u_apply_b _root_.Schoenflies.IsHomeoOn.homeomorphOfUniv_apply _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.invert_center _root_.Schoenflies.invert_image_invert_image _root_.Schoenflies.localGridX_zero _root_.Schoenflies.localGridY_zero _root_.Schoenflies.pieceListGraph_isLink _root_.Schoenflies.pieceListGraph_mem_edgeSet _root_.Schoenflies.pieceListGraph_vertexSet _root_.Schoenflies.sourceHex_chordParam _root_.Schoenflies.sourceHex_pos _root_.Schoenflies.targetHex_chordParam _root_.Schoenflies.targetHex_outer _root_.Schoenflies.targetHex_pos
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The local windows `W_n(p)` of the stage recursion

The paragraph of `jordan_schoenflies.tex` between `thm:finite-transfer` and
`prop:local-grid-attachment` fixes, for each `p ∈ D` and each `n`,

```
r(p)   = dist_∞(p, C),
s_n(p) = r(p) - min(r(p)/2, ε_n),
W_n(p) = { x : ‖x - p‖_∞ ≤ s_n(p) },
```

and records `0 < s_n(p) < r(p)`, `r(p) - s_n(p) ≤ ε_n`, and `W_n(p) ⊆ D`. Those four lines and
the arithmetic that `prop:shrinking-stars` performs on them are all this module contains. It is
entirely metric: no cell structure, no graph, nothing from Part II. That is deliberate — the
window bookkeeping is the one part of the quantitative refinement that can be finished before
the recursion it serves exists, and getting the constants wrong later, inside a proof that also
has to manage cellulations, is expensive.

## Why an ℓ^∞ distance-to-a-set had to be built

`Plane` carries the Euclidean metric, so `Metric.infDist` is the *Euclidean* distance to a set
and `Schoenflies.Plane.supDist` is a bare two-argument function with no set version.
`Schoenflies.supRadius` is the ℓ^∞ distance to a compact set, defined as the infimum of the
attained values. Everything the blueprint uses of it is here: it is attained
(`exists_supRadius_eq`), it is positive off the set (`supRadius_pos`), it is 1-Lipschitz in the
ℓ^∞ metric (`supRadius_le_add`, `abs_supRadius_sub_le`) — *"the distance-to-`C` function is
1-Lipschitz in the ℓ^∞ metric"* — and the open ℓ^∞ ball of radius `r(p)` about a point of the
Jordan domain lies in the Jordan domain (`openSquare_supRadius_subset_inside`), which is the
blueprint's *"since `C = ∂D`, the open axis-parallel square of radius `r(p)` centred at `p`
lies in `D`"*.

The last one is not proved through `C = ∂D` but through the component characterisation: the
square is convex, hence connected, and misses `C` by the very definition of `r(p)`, so it lies
in the connected component of `Cᶜ` containing `p` — which is `inside C` by `thm:jordan`.

## What `prop:shrinking-stars` extracts from this

`Schoenflies.mem_openWindow_of_supDist_lt` is the whole first half of that proof's arithmetic,
with the blueprint's constants:

> Fix `x ∈ D` and put `d = dist_∞(x, C) > 0`. Choose `b ∈ B` with `‖b - x‖_∞ < d/8` … Since
> `r(·)` is 1-Lipschitz, `r(b) ≥ r(x) - ‖b - x‖_∞ > 7d/8`. Consequently
> `s_n(b) ≥ r(b) - ε_n > 3d/4`. Because `‖b - x‖_∞ < d/8`, the point `x` lies in the interior
> of `W_n(b)`.

Nothing here mentions the enumeration `b_1, b_2, …` of `B = ℚ² ∩ D` or the sequence
`ε_n = 2^{-n}`; `windowRadius` takes `ε` as a parameter, so the recursion may pick the sequence.
`Schoenflies.exists_mem_rat_supDist_lt` is the one fact about `B` the proof uses — that a dense
subset of the plane supplies a `b` as close to `x` as asked, inside `D`.

## Blueprint

* `Schoenflies.supRadius`, `.exists_supRadius_eq`, `.supRadius_le`, `.supRadius_nonneg`,
  `.supRadius_pos`, `.notMem_of_supDist_lt_supRadius` — `r(p) = dist_∞(p, C)`.
* `Schoenflies.supRadius_le_add`, `.abs_supRadius_sub_le` — *"the distance-to-`C` function is
  1-Lipschitz in the ℓ^∞ metric"*.
* `Schoenflies.openSquare_supRadius_subset_inside` — *"since `C = ∂D`, the open axis-parallel
  square of radius `r(p)` centred at `p` lies in `D`"*.
* `Schoenflies.windowRadius`, `Schoenflies.window`, `Schoenflies.openWindow` — `s_n(p)`,
  `W_n(p)`, and its interior.
* `Schoenflies.windowRadius_pos`, `.windowRadius_lt_supRadius`, `.sub_windowRadius_le`,
  `.window_subset_inside` — the three displayed inequalities and `W_n(p) ⊆ D`.
* `Schoenflies.mem_openWindow_of_supDist_lt` — the arithmetic of `prop:shrinking-stars`.
* `Schoenflies.exists_mem_rat_supDist_lt` — the only property of `B = ℚ² ∩ D` used.
* `Schoenflies.recur`, `.exists_le_recur_eq` — *"a sequence in which every point of `B` occurs
  infinitely often"*, and the consequence `prop:shrinking-stars` uses.
* `Schoenflies.tendsto_two_pow_neg`, `.two_pow_neg_pos` — `ε_n = 2^{-n}`.
-/

open Filter Metric Set

namespace Schoenflies

variable {C U : Set Plane} {p q x b : Plane} {r ε δ : ℝ}

/-! ### One missing fact about `supDist`

`Schoenflies/Square.lean` has the ℓ^∞ norm, the ℓ^∞ distance, the triangle inequality and the
two comparisons with the Euclidean norm, but not that `supDist` separates points. It is needed
once below, to see that `r(p) > 0` off a compact set. **It belongs in `Square.lean`**; it is
here because this is its first use. -/

/-- The ℓ^∞ distance separates points. -/
theorem Plane.eq_of_supDist_eq_zero (h : Plane.supDist p q = 0) : p = q := by
  have hle : ‖p - q‖ ≤ Real.sqrt 2 * Plane.supNorm (p - q) := Plane.norm_le_sqrt_two_mul_supNorm _
  rw [show Plane.supNorm (p - q) = Plane.supDist p q from rfl, h, mul_zero] at hle
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hle (norm_nonneg _)))

/-! ### The ℓ^∞ distance to a compact set -/

/-- **`r(p) = dist_∞(p, C)`**, the ℓ^∞ distance from a point to a set.

Defined as the infimum of the attained values rather than through `Metric.infDist`, which is
the *Euclidean* distance: `Plane` carries the Euclidean metric and the blueprint's windows are
axis-parallel squares. On a compact nonempty set the infimum is attained
(`exists_supRadius_eq`), which is all that is ever used. -/
noncomputable def supRadius (C : Set Plane) (p : Plane) : ℝ := sInf (Plane.supDist p '' C)

theorem supDist_continuousOn (p : Plane) : Continuous (Plane.supDist p) :=
  continuous_supNorm.comp (continuous_const.sub continuous_id)

/-- The ℓ^∞ distance to a nonempty compact set is attained. -/
theorem exists_supRadius_eq (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) :
    ∃ q ∈ C, supRadius C p = Plane.supDist p q ∧
      ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := by
  obtain ⟨q, hqC, hmin⟩ := hC.exists_isMinOn hCne (supDist_continuousOn p).continuousOn
  have hle : ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := fun z hz => isMinOn_iff.1 hmin z hz
  refine ⟨q, hqC, ?_, hle⟩
  refine IsLeast.csInf_eq ⟨⟨q, hqC, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hle z hz

/-- Every point of the set is at least `r(p)` away, in the ℓ^∞ metric. -/
theorem supRadius_le (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) (hq : q ∈ C) :
    supRadius C p ≤ Plane.supDist p q := by
  obtain ⟨z, -, heq, hmin⟩ := exists_supRadius_eq hC hCne p
  rw [heq]; exact hmin q hq

/-- Off a compact set the ℓ^∞ distance to it is positive. -/
theorem supRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < supRadius C p := by
  obtain ⟨q, hqC, heq, -⟩ := exists_supRadius_eq hC hCne p
  rw [heq]
  rcases (Plane.supDist_nonneg p q).lt_or_eq with h | h
  · exact h
  · exact absurd (Plane.eq_of_supDist_eq_zero h.symm ▸ hqC) hp

/-- A point strictly nearer than `r(p)` is off the set: this is the definition read backwards,
and it is what makes the window miss `C`. -/
theorem notMem_of_supDist_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty)
    (h : Plane.supDist x p < supRadius C p) : x ∉ C := by
  intro hx
  exact absurd (supRadius_le hC hCne p hx) (not_le.2 (by rwa [Plane.supDist_comm p x]))

/-! ### 1-Lipschitz

*"The distance-to-`C` function is 1-Lipschitz in the ℓ^∞ metric."* Only the one-sided form is
used — `r(b) ≥ r(x) - ‖b - x‖_∞` — but both are recorded. -/

/-- `r(p) ≤ r(q) + ‖p - q‖_∞`. -/
theorem supRadius_le_add (hC : IsCompact C) (hCne : C.Nonempty) (p q : Plane) :
    supRadius C p ≤ supRadius C q + Plane.supDist p q := by
  obtain ⟨z, hzC, heq, -⟩ := exists_supRadius_eq hC hCne q
  refine (supRadius_le hC hCne p hzC).trans ?_
  rw [heq, add_comm]
  exact Plane.supDist_triangle p q z

/-! ### The square of radius `r(p)` lies in the domain -/

/-- **"The open axis-parallel square of radius `r(p)` centred at `p` lies in `D`."** The square
is convex, hence connected; it misses `C` because every one of its points is nearer to `p` than
`r(p)`; and it contains `p`. So it lies in the connected component of `Cᶜ` through `p`, which
is `inside C` by `thm:jordan`. -/
theorem openSquare_supRadius_subset_inside (hC : IsCompact C) (hCne : C.Nonempty)
    (hsep : IsSeparating C) (hp : p ∈ inside C) :
    Plane.openSquare p (supRadius C p) ⊆ inside C := by
  have hmiss : Plane.openSquare p (supRadius C p) ⊆ Cᶜ := fun x hx =>
    notMem_of_supDist_lt_supRadius hC hCne hx
  have hmem : p ∈ Plane.openSquare p (supRadius C p) := by
    have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
    simpa [Plane.openSquare, Plane.supDist_self] using supRadius_pos hC hCne hpC
  have := (Plane.convex_openSquare p (supRadius C p)).isPreconnected.subset_connectedComponentIn
    hmem hmiss
  rwa [hsep.connectedComponentIn_eq_inside hp] at this

/-! ### The windows

`windowRadius ε p` is the blueprint's `s_n(p)` with `ε_n` a parameter: the recursion chooses the
sequence, and nothing here needs to know that it is `2^{-n}`. -/

/-- **`s_n(p) = r(p) - min(r(p)/2, ε_n)`.** -/
noncomputable def windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) : ℝ :=
  supRadius C p - min (supRadius C p / 2) ε

/-- **`W_n(p)`**, the closed window. -/
noncomputable def window (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.closedSquare p (windowRadius C ε p)

/-- The interior of the window, which is where `lem:grid-star-estimate` places its point. -/
noncomputable def openWindow (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.openSquare p (windowRadius C ε p)

/-- **`0 < s_n(p)`.** -/
theorem windowRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < windowRadius C ε p := by
  have hr := supRadius_pos hC hCne hp
  have : min (supRadius C p / 2) ε ≤ supRadius C p / 2 := min_le_left _ _
  rw [windowRadius]; linarith

/-- **`s_n(p) < r(p)`.** -/
theorem windowRadius_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C)
    (hε : 0 < ε) : windowRadius C ε p < supRadius C p := by
  have hr := supRadius_pos hC hCne hp
  have : 0 < min (supRadius C p / 2) ε := lt_min (by linarith) hε
  rw [windowRadius]; linarith

/-- **`r(p) - s_n(p) ≤ ε_n`.** -/
theorem sub_windowRadius_le (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - windowRadius C ε p ≤ ε := by
  rw [windowRadius]
  simp

/-- The lower bound `s_n(p) ≥ r(p) - ε_n`, which is the form `prop:shrinking-stars` uses. -/
theorem le_windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - ε ≤ windowRadius C ε p := by
  have := sub_windowRadius_le C ε p; linarith

/-- **`W_n(p) ⊆ D`**: the closed window sits strictly inside the square of radius `r(p)`. -/
theorem window_subset_inside (hC : IsCompact C) (hCne : C.Nonempty) (hsep : IsSeparating C)
    (hp : p ∈ inside C) (hε : 0 < ε) : window C ε p ⊆ inside C := by
  have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
  refine subset_trans (fun x hx => ?_) (openSquare_supRadius_subset_inside hC hCne hsep hp)
  exact lt_of_le_of_lt hx (windowRadius_lt_supRadius hC hCne hpC hε)

/-! ### The arithmetic of `prop:shrinking-stars` -/

/-- **The window-catching estimate.** If `b` is within `d/8` of `x` in the ℓ^∞ metric and the
mesh parameter `ε` is below `d/8`, where `d = dist_∞(x, C)`, then `x` lies in the *interior* of
the window `W(b)`.

This is the displayed chain of the proof of `prop:shrinking-stars`: `r(b) > 7d/8` by
1-Lipschitzness, hence `s(b) ≥ r(b) - ε > 3d/4`, and `‖b - x‖_∞ < d/8 < 3d/4`. -/
theorem mem_openWindow_of_supDist_lt (hC : IsCompact C) (hCne : C.Nonempty)
    (hbx : Plane.supDist b x < supRadius C x / 8) (hε : ε < supRadius C x / 8) :
    x ∈ openWindow C ε b := by
  set d := supRadius C x with hd
  -- `r(b) ≥ r(x) - ‖b - x‖_∞ > 7d/8`.
  have hlip : d ≤ supRadius C b + Plane.supDist x b := supRadius_le_add hC hCne x b
  rw [Plane.supDist_comm x b] at hlip
  have hrb : 7 * d / 8 < supRadius C b := by linarith
  -- `s(b) ≥ r(b) - ε > 7d/8 - d/8 = 3d/4`.
  have hsb : 3 * d / 4 < windowRadius C ε b :=
    lt_of_lt_of_le (by linarith) (le_windowRadius C ε b)
  -- and `x` is within `d/8` of `b`.
  have hxb : Plane.supDist x b < d / 8 := by rwa [Plane.supDist_comm x b]
  have hdpos : 0 < d := by linarith [Plane.supDist_nonneg b x]
  exact lt_trans hxb (by linarith)

/-! ### The two sequences the recursion fixes

*"Choose a sequence `b_1, b_2, …` in which every point of `B` occurs infinitely often, and put
`ε_n = 2^{-n}`."* Both are here, each with the one property `prop:shrinking-stars` uses: every
value of the enumeration recurs at arbitrarily large indices, and the mesh sequence is null. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.BoundaryAnchors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Boundary anchors retained by the quantitative recursion

Every reverse quantitative stage selects a finite metric net of accessible points on the model
curve.  This module takes their countable union, proves it dense, transports it through the
prescribed boundary homeomorphism, and records the finite-stage witness for every transported
source anchor.

## Blueprint

This discharges `lem:anchor-density` and constructs the `HasAnchorCrosscuts` and `HasSpokes`
inputs used in `prop:boundary-continuity`.
-/

open Filter Metric Set
open scoped Graph

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- The corresponding lifting statement for a simple path. -/
theorem Graph.IsPath.exists_lift_map
    {α α' β : Type*} {G : Graph α β} {f : α → α'}
    (hf : Set.InjOn f V(G)) {u : α} (hu : u ∈ V(G))
    {W : List β} {y : α'} (h : (G.map f).IsPath (f u) W y) :
    ∃ v : α, G.IsPath u W v ∧ f v = y := by
  induction W generalizing u y with
  | nil =>
      have hy : f u = y := h.isWalk.eq_of_nil
      exact ⟨u, Graph.IsPath.nil hu, hy⟩
  | cons e W ih =>
      cases h with
      | @cons _ w _ _ _ hlink htail hfresh =>
          obtain ⟨u₀, w₀, hlink₀, hu₀, hw₀⟩ := hlink
          have huu₀ : u₀ = u := hf hlink₀.left_mem hu hu₀
          subst u₀
          subst w
          obtain ⟨v, hv, hfv⟩ := ih hlink₀.right_mem htail
          refine ⟨v, Graph.IsPath.cons hlink₀ hv ?_, hfv⟩
          intro huTail
          apply hfresh
          rw [Graph.walkVertices_map]
          exact ⟨u, huTail, rfl⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed path-hit relations and the joint upper semicontinuity of their probabilities.
The time interval is compact, so projection of the closed incidence relation is closed.
Weak convergence and the existing Portmanteau theorem then apply to the product with
the moving point mass. This supplies the actual hit function used in law fusion. -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

section Paths

variable {X : Type*} [MetricSpace X]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem pathHitProbability_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, X) × X =>
      pathHitProbability p.1 p.2) :=
  closed_section_probability_upperSemicontinuous isClosed_pathHitSet

theorem measurable_pathHitProbability_point (μ : ProbabilityMeasure C(PathTime, X)) :
    Measurable (pathHitProbability μ) :=
  (pathHitProbability_upperSemicontinuous.comp
    (continuous_const.prodMk continuous_id)).measurable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] in
theorem pathHitProbability_le_one (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitProbability μ x ≤ 1 := prob_le_one

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLawMixtures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel mixtures of actual path laws. Hit probabilities obey the mixture identity;
their finite nonnegative weighted bounds pass to arbitrary probability mixtures.
The dual finite bounds imply square summability and countable positive support. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]

section Paths

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem pathHitReal_le_one (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitReal μ x ≤ 1 := by
  simpa only [pathHitReal, ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (pathHitProbability_le_one μ x)

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HitNormTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued hit norms, their dual finite tests, and uniform strict inequalities
over compact configuration spaces. These are the topological estimates used in
the finite split of path-law fusion. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

section Paths

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem pathHitReal_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, X) × X =>
      pathHitReal p.1 p.2) := by
  intro p c hc
  have hfinite : pathHitProbability p.1 p.2 ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one _ _) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have he := pathHitProbability_upperSemicontinuous p (ENNReal.ofReal c)
    ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hc)
  exact he.mono fun _ h => ENNReal.toReal_lt_of_lt_ofReal h

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FilledCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous smooth coordinate fillings

Compact connected collars are chosen inside the supplied real-branch
domains and away from all inactive lattices. A single sufficiently small
width makes every inactive staircase constant there. Rank-one collar
extensions then patch into the retained coordinates across all the
pairwise disjoint filling disks. No lifting theorem is assumed.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem realJordanInterior_geometry (H : ℂ ≃ₜ ℂ) :
    IsOpen (realJordanInterior H) ∧
      IsCompact (frontier (realJordanInterior H)) ∧
      IsConnected (frontier (realJordanInterior H)) := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  have hfront : frontier (realJordanInterior H) = e '' frontier (jordanInterior H) :=
    (e.image_frontier _).symm
  refine ⟨e.isOpenMap _ (jordanInterior_isOpen H), ?_, ?_⟩
  · rw [hfront]
    exact ((isCompact_closure_jordanInterior H).of_isClosed_subset
      isClosed_frontier frontier_subset_closure).image e.continuous
  · rw [hfront]
    exact (isConnected_frontier_jordanInterior H).image e e.continuous.continuousOn

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous lift of each actual terminal arc to angular and logarithmic
coordinates. The angular origin is the representative of the arc start. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def diskRayAngle (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) : ℝ :=
  realCirclePathLift (initialArcAngles puncturedArgument γ hi he t.val t.property) 1

theorem diskRayAngle_eq_increment (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) :
    diskRayAngle γ hi he t = circleRepresentative (normalizedArgument (γ 0)) +
      circlePathIncrement (initialArcAngles puncturedArgument γ hi he t.val t.property) := by
  have h0 : realCirclePathLift (initialArcAngles puncturedArgument γ hi he t.val t.property) 0 =
      circleRepresentative (normalizedArgument (γ 0)) := by
    rw [realCirclePathLift, (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero]
    simp only [initialArcAngles, ContinuousMap.coe_mk, zero_mul, puncturedArgument]
  unfold diskRayAngle circlePathIncrement
  rw [h0]
  ring

theorem continuous_diskRayAngle (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Continuous (diskRayAngle γ hi he) := by
  let A : DiskRayTime → C(unitInterval, UnitAddCircle) := fun t =>
    initialArcAngles puncturedArgument γ hi he t.val t.property
  have hA : Continuous A := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply puncturedArgument.continuous.comp
    apply Continuous.subtype_mk
    exact γ.continuous.comp (continuous_snd.mul (continuous_subtype_val.comp continuous_fst))
  have hc := (continuous_const (y := circleRepresentative (normalizedArgument (γ 0)))).add
    (continuous_circlePathIncrement.comp hA)
  exact hc.congr (fun t => (diskRayAngle_eq_increment γ hi he t).symm)

theorem diskRayAngle_projects (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) :
    (diskRayAngle γ hi he t : UnitAddCircle) = normalizedArgument (γ t.val) := by
  simpa only [diskRayAngle, initialArcAngles, puncturedArgument, ContinuousMap.coe_mk, one_mul] using
    realCirclePathLift_projects (initialArcAngles puncturedArgument γ hi he t.val t.property) 1

theorem diskRay_nonzero (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) : γ t.val ≠ 0 := by
  intro h
  have ht := hi (h.trans he.symm)
  exact (ne_of_lt t.property) ht

def diskRayDepth (γ : C(PathTime, ℂ)) (t : DiskRayTime) : ℝ := -Real.log ‖γ t.val‖

theorem continuous_diskRayDepth (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Continuous (diskRayDepth γ) :=
  ((γ.continuous.comp continuous_subtype_val).norm.log
    (fun t => norm_ne_zero_iff.mpr (diskRay_nonzero γ hi he t))).neg

def diskRayLift (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    C(DiskRayTime, ℝ × ℝ) :=
  ⟨fun t => (diskRayAngle γ hi he t, diskRayDepth γ t),
    (continuous_diskRayAngle γ hi he).prodMk (continuous_diskRayDepth γ hi he)⟩

theorem diskRayLift_injective (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Injective (diskRayLift γ hi he) := by
  intro s t h
  apply Subtype.ext
  apply hi
  apply Complex.ext_norm_arg
  · have hd : Real.log ‖γ s.val‖ = Real.log ‖γ t.val‖ :=
      neg_injective (congrArg Prod.snd h)
    have hexp := congrArg Real.exp hd
    simpa only [Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he s)),
      Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he t))] using hexp
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    exact (diskRayAngle_projects γ hi he s).symm.trans
      ((congrArg (fun x : ℝ => (x : UnitAddCircle)) (congrArg Prod.fst h)).trans
        (diskRayAngle_projects γ hi he t))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayProper
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform properness and angular bounds on every bounded-depth strip
for the lifted compact disk-arc family. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_depth_escape
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (Y : ℝ) :
    ∃ c : PathTime, 0 < c ∧ c < 1 ∧
      ∀ γ ∈ K, ∀ t : DiskRayTime, c ≤ t.val → Y < diskRayDepth γ t := by
  obtain ⟨c, hc0, hc1, htail⟩ := compact_disk_rays_uniform_tail K hK
    (fun γ hγ => (hKS hγ).2.2.1) (Real.exp_pos (-Y))
  refine ⟨c, hc0, hc1, fun γ hγ t ht => ?_⟩
  have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ (hKS hγ).1 (hKS hγ).2.2.1 t)
  have hh : Real.log ‖γ t.val‖ < -Y := (Real.log_lt_iff_lt_exp hp).mpr (htail γ hγ t.val ht)
  change Y < -Real.log ‖γ t.val‖
  linarith

theorem diskRayDepth_nonneg {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet)
    (t : DiskRayTime) : 0 ≤ diskRayDepth γ t := by
  have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t)
  have hle := (Real.log_le_iff_le_exp hp).mpr
    (show ‖γ t.val‖ ≤ Real.exp 0 by simpa only [Real.exp_zero] using diskTerminalArc_norm_le hγ t.val)
  exact neg_nonneg.mpr hle

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactifiedDiskRay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proper lifted ray compactifies to a disk crosscut. The endpoint at
infinity is added using the quantitative Cayley estimate. -/

open Set Function Filter Metric
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

def diskRayComplex (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    C(DiskRayTime, ℂ) :=
  ⟨fun t => (diskRayAngle γ hi he t : ℂ) + (diskRayDepth γ t : ℂ) * Complex.I,
    ((Complex.continuous_ofReal.comp (continuous_diskRayAngle γ hi he)).add
      ((Complex.continuous_ofReal.comp (continuous_diskRayDepth γ hi he)).mul continuous_const))⟩

@[simp] theorem diskRayComplex_im (γ : C(PathTime, ℂ)) (hi : Injective γ)
    (he : γ ⊤ = 0) (t : DiskRayTime) :
    (diskRayComplex γ hi he t).im = diskRayDepth γ t := by
  simp [diskRayComplex]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayCrosscut
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactified lifted ray is a simple crosscut of the closed disk. -/

open Set Function
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem diskRayComplex_injective (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Injective (diskRayComplex γ hi he) := by
  intro s t h
  apply diskRayLift_injective γ hi he
  apply Prod.ext
  · simpa [diskRayComplex, diskRayLift] using congrArg Complex.re h
  · simpa only [diskRayLift, ContinuousMap.coe_mk, diskRayComplex_im] using congrArg Complex.im h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneRay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactification of the integer translates of a lifted ray. The curve
escapes in height, so the added endpoint is the single boundary point 1. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

structure HalfPlaneRay where
  curve : C(DiskRayTime, ℂ)
  injective : Injective curve
  nonneg : ∀ t, 0 ≤ (curve t).im
  start : (curve ⟨0, bot_lt_top⟩).im = 0
  positive : ∀ t : DiskRayTime, 0 < t.val → 0 < (curve t).im
  escape : ∀ Y : ℝ, ∃ c : PathTime, c < 1 ∧ ∀ t : DiskRayTime, c ≤ t.val → Y < (curve t).im

def HalfPlaneRay.compactify (R : HalfPlaneRay) (t : PathTime) : ℂ :=
  if ht : t < ⊤ then halfPlaneDisk (R.curve ⟨t, ht⟩) else 1

@[simp] theorem HalfPlaneRay.compactify_top (R : HalfPlaneRay) : R.compactify ⊤ = 1 := by
  simp only [HalfPlaneRay.compactify, lt_self_iff_false, dite_false]

theorem HalfPlaneRay.continuousOn_compactify (R : HalfPlaneRay) :
    ContinuousOn R.compactify (Iio ⊤) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := continuousOn_halfPlaneDisk.comp_continuous R.curve.continuous R.nonneg
  apply hc.congr
  intro t
  change halfPlaneDisk (R.curve t) = R.compactify t.val
  simp only [HalfPlaneRay.compactify, dite_eq_left t.property]

theorem HalfPlaneRay.continuousAt_compactify_top (R : HalfPlaneRay) :
    ContinuousAt R.compactify ⊤ := by
  rw [ContinuousAt, R.compactify_top]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c, hc, htail⟩ := R.escape (2 / ε)
  filter_upwards [Ioi_mem_nhds (show c < (⊤ : PathTime) from hc)] with t ht
  by_cases htt : t < ⊤
  · rw [HalfPlaneRay.compactify, dite_eq_left htt]
    have hy := htail ⟨t, htt⟩ ht.le
    apply (halfPlaneDisk_dist_one_le (R.nonneg ⟨t, htt⟩)).trans_lt
    apply (div_lt_iff₀ (show 0 < (R.curve ⟨t, htt⟩).im + 1 by linarith [R.nonneg ⟨t, htt⟩])).mpr
    have hy' : 2 < (R.curve ⟨t, htt⟩).im * ε := (div_lt_iff₀ hε).mp hy
    nlinarith
  · simp only [HalfPlaneRay.compactify, htt, dite_false, dist_self, hε]

theorem HalfPlaneRay.continuous_compactify (R : HalfPlaneRay) : Continuous R.compactify := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t < ⊤
  · exact R.continuousOn_compactify.continuousAt (isOpen_Iio.mem_nhds ht)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    exact R.continuousAt_compactify_top

theorem HalfPlaneRay.compactify_injective (R : HalfPlaneRay) : Injective R.compactify := by
  intro s t h
  by_cases hs : s < ⊤
  · by_cases ht : t < ⊤
    · rw [HalfPlaneRay.compactify, dite_eq_left hs, HalfPlaneRay.compactify, dite_eq_left ht] at h
      exact congrArg Subtype.val (R.injective (halfPlaneDisk_injOn (R.nonneg _) (R.nonneg _) h))
    · rw [HalfPlaneRay.compactify, dite_eq_left hs, HalfPlaneRay.compactify, dite_eq_right ht] at h
      exact (halfPlaneDisk_ne_one (R.nonneg _) h).elim
  · by_cases ht : t < ⊤
    · rw [HalfPlaneRay.compactify, dite_eq_right hs, HalfPlaneRay.compactify, dite_eq_left ht] at h
      exact (halfPlaneDisk_ne_one (R.nonneg _) h.symm).elim
    · exact (top_le_iff.mp (not_lt.mp hs)).trans (top_le_iff.mp (not_lt.mp ht)).symm

def HalfPlaneRay.crosscut (R : HalfPlaneRay) : Path (R.compactify 0) 1 where
  toFun := R.compactify
  continuous_toFun := R.continuous_compactify
  source' := rfl
  target' := R.compactify_top

theorem HalfPlaneRay.crosscut_start_norm (R : HalfPlaneRay) : ‖R.compactify 0‖ = 1 := by
  have ht : (0 : PathTime) < ⊤ := bot_lt_top
  rw [HalfPlaneRay.compactify, dite_eq_left ht]
  exact halfPlaneDisk_norm_eq R.start

theorem HalfPlaneRay.crosscut_start_ne (R : HalfPlaneRay) : R.compactify 0 ≠ 1 := by
  rw [← R.compactify_top]
  exact fun h => zero_ne_one (R.compactify_injective h)

theorem HalfPlaneRay.crosscut_interior (R : HalfPlaneRay) (t : PathTime)
    (ht : t ∈ Ioo 0 1) : ‖R.crosscut t‖ < 1 := by
  change ‖R.compactify t‖ < 1
  have ht' : t < ⊤ := ht.2
  rw [HalfPlaneRay.compactify, dite_eq_left ht']
  exact halfPlaneDisk_norm_lt (R.positive ⟨t, ht.2⟩ ht.1)

theorem HalfPlaneRay.exists_schoenflies (R : HalfPlaneRay) (hsch : PlanarSchoenflies) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath (R.crosscut.trans
        (boundaryClosingArc _ R.crosscut_start_norm))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) :=
  exists_schoenflies_of_disk_crosscut hsch R.crosscut R.compactify_injective
    R.crosscut_interior R.crosscut_start_norm R.crosscut_start_ne

def translatedHalfPlaneRay (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (k : ℤ) : HalfPlaneRay where
  curve := ⟨fun t => diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ),
    (diskRayComplex γ hγ.1 hγ.2.2.1).continuous.add continuous_const⟩
  injective := fun _ _ h => diskRayComplex_injective γ hγ.1 hγ.2.2.1 (add_right_cancel h)
  nonneg := by
    intro t
    simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im] using diskRayDepth_nonneg hγ t
  start := by
    simp only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im,
      diskRayDepth]
    rw [hγ.2.1, Real.log_one, neg_zero]
  positive := by
    intro t ht
    simp only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im]
    have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t)
    have hlt := Real.log_lt_log hp (hγ.2.2.2 t.val ⟨ht, t.property⟩)
    rw [Real.log_one] at hlt
    exact neg_pos.mpr hlt
  escape := by
    intro Y
    obtain ⟨c, _, hc, hh⟩ := compact_disk_rays_depth_escape {γ} isCompact_singleton
      (by simpa only [singleton_subset_iff] using hγ) Y
    refine ⟨c, hc, fun t ht => ?_⟩
    simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im]
      using hh γ (mem_singleton γ) t ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RayJordanSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side functions for all integer translates of a lifted ray. Boundary
order is the ordinary order on the real boundary of the half-plane. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

def IsJordan (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) : Prop :=
  frontier (jordanInterior H) = range R.crosscut ∪ range (boundaryClosingArc _ R.crosscut_start_norm)

theorem exists_jordan (R : HalfPlaneRay) (hsch : PlanarSchoenflies) :
    ∃ H : ℂ ≃ₜ ℂ, R.IsJordan H := by
  obtain ⟨H, hH⟩ := R.exists_schoenflies hsch
  refine ⟨H, ?_⟩
  unfold IsJordan
  rw [frontier_jordanInterior_eq_circle_range H _ hH]
  have hr := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.surjective.range_comp
    (circleOfClosedPath (R.crosscut.trans (boundaryClosingArc _ R.crosscut_start_norm)))
  rw [show (fun z : Circle => circleOfClosedPath (R.crosscut.trans
      (boundaryClosingArc _ R.crosscut_start_norm))
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)) =
      (circleOfClosedPath (R.crosscut.trans (boundaryClosingArc _ R.crosscut_start_norm))) ∘
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm from rfl,
    hr, circleOfClosedPath_range, Path.trans_range]

abbrev CutDomain (R : HalfPlaneRay) := {z : ℂ // z ∈ Metric.closedBall 0 1 \ range R.crosscut}

def side (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (z : R.CutDomain) : Bool :=
  if z.val ∈ closure (jordanInterior H) then false else true

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalRayAvoidance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common angular strip bound makes all sufficiently far translates
miss each vertical segment to the real boundary. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem vertical_im_nonneg (x y : ℝ) (hy : 0 ≤ y) (t : PathTime) :
    0 ≤ ((x : ℂ) + ((t : ℝ) * y : ℝ) * Complex.I).im := by
  simpa using mul_nonneg t.property.1 hy

def verticalCayleyPath (x y : ℝ) (hy : 0 ≤ y) : C(PathTime, ℂ) :=
  ⟨fun t => halfPlaneDisk ((x : ℂ) + ((t : ℝ) * y : ℝ) * Complex.I),
    continuousOn_halfPlaneDisk.comp_continuous
      (continuous_const.add ((Complex.continuous_ofReal.comp
        (continuous_subtype_val.mul_const y)).mul continuous_const))
      (vertical_im_nonneg x y hy)⟩

@[simp] theorem verticalCayleyPath_zero (x y : ℝ) (hy : 0 ≤ y) :
    verticalCayleyPath x y hy 0 = halfPlaneDisk x := by simp [verticalCayleyPath]

@[simp] theorem verticalCayleyPath_one (x y : ℝ) (hy : 0 ≤ y) :
    verticalCayleyPath x y hy 1 = halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) := by
  simp [verticalCayleyPath]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricRayIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual greatest-translate index. Compact strip bounds prove that
the defining set is nonempty and bounded above, uniformly over the arc law. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def rayJordan (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) : ℂ ≃ₜ ℂ :=
  Classical.choose ((translatedHalfPlaneRay γ hγ k).exists_jordan hsch)

def rayRightIndices (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) : Set ℤ :=
  {k | halfPlaneDisk z ∉ closure (jordanInterior (rayJordan hsch γ hγ k))}

def geometricRayIndex (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) : ℤ := sSup (rayRightIndices hsch γ hγ z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutPathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side membership is characterized by a path avoiding the crosscut to
the corresponding explicit real-boundary point. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def DiskAvoidingPath (p : C(PathTime, ℂ)) (z w : ℂ) : Prop :=
  ∃ δ : C(PathTime, ℂ), δ 0 = z ∧ δ 1 = w ∧
    ∀ t, δ t ∈ Metric.closedBall 0 1 \ range p

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexLocal
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local constancy of the greatest-translate index follows from the common
finite strip bound and local constancy of each of the finitely many relevant sides. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

abbrev RayIndexDomain (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :=
  {z : ℂ // 0 ≤ z.im ∧ ∀ k : ℤ, halfPlaneDisk z ∉ range (translatedHalfPlaneRay γ hγ k).crosscut}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanGeometricIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the actual geometric index of a compact arc law. Uniform
bounds come from the ray geometry, rather than a domination hypothesis. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def meanGeometricIndex (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) : ℝ :=
  ∫ γ : K, (geometricRayIndex hsch γ.val (hKS γ.property) z.val : ℝ) ∂(η : Measure K)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlanePathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The side path test in the original half-plane coordinates. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def HalfPlaneAvoidingPath (R : HalfPlaneRay) (z w : ℂ) : Prop :=
  ∃ δ : C(PathTime, ℂ), δ 0 = z ∧ δ 1 = w ∧
    ∀ t, 0 ≤ (δ t).im ∧ δ t ∉ range R.curve

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanIndexCircle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean index descends through the logarithmic cover to a
circle-valued coordinate. Every continuous local lift represents the
same coordinate; no choice of branch is part of the resulting map. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def diskMeanCircle (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (w : ℂ) : UnitAddCircle :=
  if h : ∃ z : ClosedUpperHalfPlane, diskRayProjection z.val = w then
    (meanGeometricIndex hsch K hKS η (Classical.choose h) : UnitAddCircle) else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPeriodData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single constructed mean-period coordinate retains its real atlas,
closed masked levels, vanishing correction, and actual smooth physical
representative. The analytic and topological data come from one law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

structure SmoothMeanPeriodData
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (G U S M : Set Sphere) (b : Sphere) (π : Sphere → Sphere) where
  Index : Type
  countableIndex : Countable Index
  patch : Index → Set Sphere
  angle : Index → ℝ
  bound : Index → ℝ
  branch : Index → Sphere → ℝ
  error : Sphere → ℝ
  physical : ℂ → UnitAddCircle
  euclidean : EuclideanPlane → UnitAddCircle
  physical_eq : physical = euclidean ∘ complexPlaneCoordinates.symm
  cover : S ⊆ ⋃ i, patch i
  patch_open : ∀ i, IsOpen (patch i)
  patch_closure : ∀ i, closure (patch i) ⊆ S
  log_continuous : ∀ i, ContinuousOn
    (fun x => logarithmicCutChart (angle i) (F x)) (closure (patch i))
  bounded : ∀ i x, |branch i x| ≤ bound i
  continuous : ∀ i, ContinuousOn (branch i) (U ∩ patch i)
  branch_value : ∀ i x, x ∈ patch i → branch i x =
    meanGeometricIndex hsch K hKS η
      (upperHalfPlaneClamp (logarithmicCutChart (angle i) (F x))) + error x
  transition : ∀ i j x, x ∈ patch i → x ∈ patch j →
    ∃ k : ℤ, branch j =ᶠ[𝓝[U] x] fun y => branch i y + k
  closed : IsClosed (periodBandGraph U M b patch branch)
  domain_value : ∀ x ∈ U, ∀ θ : UnitAddCircle,
    (x, θ) ∈ periodBandGraph U M b patch branch ↔
      x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) + (error x : UnitAddCircle) = θ
  error_continuous : ContinuousOn error (U ∩ S)
  error_bound : ∀ x, |error x| ≤ 1
  error_vanishes : ∀ x ∈ Uᶜ, Tendsto error (𝓝 x) (𝓝 0)
  physical_smooth : FiniteTransfer.SmoothCircleOn physical
    (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S)
  physical_value : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
    physical z = diskMeanCircle hsch K hKS η (F (π (z : Sphere))) +
      (error (π (z : Sphere)) : UnitAddCircle)
  physical_energy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
    (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
    ENNReal.ofReal ‖FiniteTransfer.circleFDeriv physical z‖ ^ 2) < ∞
  branch_smooth : ∀ i, ContDiffOn ℝ 1 (fun z : ℂ => branch i (π (z : Sphere)))
    (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' patch i)
  branch_energy : ∀ i, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
    (fun z : ℂ => π (z : Sphere)) ⁻¹' patch i,
    ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => branch i (π (z : Sphere))) z‖ ^ 2) < ∞

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompatibleLevelBarrier
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real barrier in the endpoint problem, with its actual physical
representative, countable enlarged flags, and finite-torus compatibility. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

structure CompatibleLevelBarrier (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (previous : PriorLevelFamily d.physicalDomain π) (flags EStar : Set Sphere)
    (regions : ℕ → Set Sphere) (f : d.quotientDomain → Sphere) (W₁ : Set Sphere) where
  coordinate : PhysicalRealCoordinate d π
  level : ℕ
  penalty : Set Sphere
  penalty_open : IsOpen penalty
  penalty_inside : closure penalty ⊆ d.quotientDomain
  penalty_disjoint : Disjoint d.anchor (closure penalty)
  penalty_avoids : ∀x : d.quotientDomain, x.val ∈ closure penalty → f x ∉ W₁
  zero : ∀x ∈ EStar, coordinate.quotient x = 0
  one : ∀x ∈ closure (regions level) ∩ d.quotientDomain, coordinate.quotient x = 1
  exclusions : Set Sphere
  exclusions_countable : exclusions.Countable
  prior_flags : flags ⊆ exclusions
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑'s, weight s ^ 2) < ∞
  weight_support : support weight ⊆ exclusions
  band_bound : ∀s ∈ d.dust, ENNReal.ofReal
    (limsup coordinate.quotient (𝓝[d.quotientDomain] s) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] s)) ≤ weight s
  compatible : ∀n labels, (volume.prod (Measure.pi (fun _ : Fin (n + 1) =>
    (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ exclusions)
      (circleBandGraph d.quotientDomain coordinate.quotient)
      (fun i => previous.graph i) labels) = 0

namespace CompatibleLevelBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : PriorLevelFamily d.physicalDomain π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

def controlledSize (B : CompatibleLevelBarrier d π previous flags EStar regions f W₁) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∫x in FiniteTransfer.realChartDomain d.physicalDomain \
    (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' B.penalty,
      FiniteTransfer.gradientEnergy B.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) +
    countingSquareNorm B.weight

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LevelBarrierRebase
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Earlier-law constraints change the base-code space, but do not change
the geometric barrier problem. Rebase its actual coordinate and size. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

def CompatibleLevelBarrier.rebase {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {previous : PriorLevelFamily d.physicalDomain π} {next : PriorLevelFamily e.physicalDomain π}
    {flags EStar : Set Sphere} {regions : ℕ → Set Sphere}
    {f : d.quotientDomain → Sphere} {g : e.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleLevelBarrier d π previous flags EStar regions f W)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hE : e.anchor = d.anchor) (hB : e.dust = d.dust)
    (hprev : ∀ i, next.graph i = previous.graph i)
    (hfg : ∀ x : e.quotientDomain, g x = f ⟨x.val, hU ▸ x.property⟩) :
    CompatibleLevelBarrier e π next flags EStar regions g W where
  coordinate := R.coordinate.rebase hG hU
  level := R.level
  penalty := R.penalty
  penalty_open := R.penalty_open
  penalty_inside := by simpa only [hU] using R.penalty_inside
  penalty_disjoint := by simpa only [hE] using R.penalty_disjoint
  penalty_avoids := by
    intro x hx
    rw [hfg x]
    exact R.penalty_avoids ⟨x.val, hU ▸ x.property⟩ hx
  zero := R.zero
  one := by simpa only [PhysicalRealCoordinate.rebase, hU] using R.one
  exclusions := R.exclusions
  exclusions_countable := R.exclusions_countable
  prior_flags := R.prior_flags
  weight := R.weight
  weight_finite := R.weight_finite
  weight_support := R.weight_support
  band_bound := by
    intro s hs
    change ENNReal.ofReal (limsup R.coordinate.quotient (𝓝[e.quotientDomain] s) -
      liminf R.coordinate.quotient (𝓝[e.quotientDomain] s)) ≤ R.weight s
    rw [hU]
    exact R.band_bound s (hB ▸ hs)
  compatible := by
    intro n labels
    simpa only [PhysicalRealCoordinate.rebase, hU, hB, hprev] using R.compatible n labels

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Path hits tested on a compact subset of the ambient path space.  The
continuous map is the inclusion of the dust in the application; no path is
required to lie in that subset. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y))

theorem pathHitProbability_le_one (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    pathHitProbability ι μ x ≤ 1 :=
  CircleDomainRigidity.pathHitProbability_le_one μ (ι x)

theorem pathHitReal_nonneg (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    0 ≤ pathHitReal ι μ x := ENNReal.toReal_nonneg

theorem pathHitReal_le_one (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    pathHitReal ι μ x ≤ 1 :=
  CircleDomainRigidity.pathHitReal_le_one μ (ι x)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)]

theorem measurable_pathHitProbability_point (μ : ProbabilityMeasure C(PathTime, Y)) :
    Measurable (pathHitProbability ι μ) :=
  (CircleDomainRigidity.measurable_pathHitProbability_point μ).comp ι.continuous.measurable

omit [MeasurableSpace X] [BorelSpace X] in
theorem pathHitReal_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, Y) × X =>
      pathHitReal ι p.1 p.2) :=
  CircleDomainRigidity.pathHitReal_upperSemicontinuous.comp
    (continuous_fst.prodMk (ι.continuous.comp continuous_snd))

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedConfigurations
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureMeanConfigurationMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated configurations lie in the dust test space, while their hit
probabilities come from paths in the ambient space. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)] (ι : C(X, Y))

theorem weightedConfigurationHits_nonneg (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) :
    0 ≤ weightedConfigurationHits ι law z p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _)

theorem weightedConfigurationHits_le_card (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) :
    weightedConfigurationHits ι law z p ≤ n := by
  calc
    ∑ i, (p.val.2 i : ℝ) * pathHitReal ι (law z) (p.val.1 i) ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_mul (p.val.2 i).property.2 (pathHitReal_le_one ι _ _)
        (pathHitReal_nonneg ι _ _) (by norm_num)).trans_eq (one_mul 1)
    _ = n := by simp

variable [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, Y)] [TopologicalSpace Z]

theorem weightedConfigurationHits_upperSemicontinuous
    {law : Z → ProbabilityMeasure C(PathTime, Y)} (hlaw : Continuous law) (n : ℕ) (r : ℝ) :
    UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      weightedConfigurationHits ι law q.1 q.2) := by
  apply upperSemicontinuous_sum
  intro i _
  have hw : Continuous (fun q : Z × HitConfiguration X n r => (q.2.val.2 i : ℝ)) :=
    by fun_prop
  have hh : UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      pathHitReal ι (law q.1) (q.2.val.1 i)) :=
    (pathHitReal_upperSemicontinuous ι).comp
      ((hlaw.comp continuous_fst).prodMk (by fun_prop))
  exact upperSemicontinuous_nonnegative_mul hw.upperSemicontinuous hh
    (fun q => (q.2.val.2 i).property.1) (fun _ => pathHitReal_nonneg ι _ _)

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MarkedConfigurationNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureMeanConfigurationMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Testing all sizes and reciprocal separation scales is sufficient to control
the full square norm of the point-hit probabilities. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y)) (μ : ProbabilityMeasure C(PathTime, Y)) {B : ℝ}

/-- The square norm is tested only on the marked compact space. -/
def HasHitNormBound (B : ℝ) : Prop :=
  ∀ F : Finset X, ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ B ^ 2

/-- This hypothesis runs over a countable list of compact configuration spaces. -/
def HasConfigurationBounds (B : ℝ) : Prop :=
  ∀ n m : ℕ, ∀ p : HitConfiguration X n (1 / ((m : ℝ) + 1)),
    weightedConfigurationHits ι (fun _ : Unit => μ) () p ≤ B

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereRealDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite real chart of a metric-conformal sphere map

This identifies the actual real derivative matrix of the finite-chart
map with the complex chart derivative used in metric conformality.
-/

open Set Filter Matrix
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem sphereRealMap_injOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : InjOn f U)
    {s : Set (ℝ × ℝ)}
    (hs : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    InjOn (sphereRealMap f) s := by
  intro x hx y hy hxy
  have hcoord := Complex.equivRealProdCLM.injective hxy
  have hvalues : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) =
      f ((Complex.equivRealProdCLM.symm y : ℂ) : Sphere) := by
    have hc := congrArg ((↑) : ℂ → Sphere) hcoord
    exact (CannonMobius.coe_coordinate (hfinite x hx)).symm.trans
      (hc.trans (CannonMobius.coe_coordinate (hfinite y hy)))
  exact Complex.equivRealProdCLM.symm.injective
    (OnePoint.coe_injective (hf (hs x hx) (hs y hy) hvalues))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothSphereEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth equivalences on sphere regions

Both directions and their actual inverse identities are retained, so a
coordinate can be transported by composing with the constructed inverse.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereEquivalence.symm
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V) :
    IsSmoothSphereEquivalence fi f V U :=
  ⟨h.smooth_inv, h.mapsTo_inv, h.smooth, h.mapsTo, h.right_inv, h.left_inv⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CompletedChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual completed region in the finite real chart

These identifications pass the spherical disk completion to the real
coordinates used by the energy estimates, preserving the original core
and the exact open extension domain.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isClosed_real_completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) :
    IsClosed (realChartDomain (completedRegion T)) :=
  isClosed_realChartDomain (isOpen_sphericalDiskUnion T).isClosed_compl

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRealSphereMaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth finite charts of sphere equivalences fixing infinity

The two genuine inverses induce smooth inverse maps in finite real
coordinates. Their restriction to any open source region is open,
which supplies the domain of each transported masked coordinate.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem IsSmoothSphereAt.contDiffAt_sphereRealMap
    {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsSmoothSphereAt f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    ContDiffAt ℝ ∞ (sphereRealMap f) x := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hd : ContDiffAt ℝ ∞ (sphereLocalMap f p) (Complex.equivRealProdCLM.symm x) := by
    simpa only [p, chart_coe_self] using hf.2
  have hc := Complex.equivRealProdCLM.contDiff.contDiffAt.comp x
    (hd.comp x Complex.equivRealProdCLM.symm.contDiff.contDiffAt)
  have heq : sphereRealMap f =
      Complex.equivRealProdCLM ∘ sphereLocalMap f p ∘ Complex.equivRealProdCLM.symm := by
    funext y
    simp only [sphereRealMap, sphereLocalMap, p, chart, chartSymm,
      OnePoint.coe_ne_infty, ite_false, if_false, hfinite, Function.comp_apply]
  simpa only [heq] using hc

theorem sphereRealMap_mem
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : MapsTo f U V)
    {x : ℝ × ℝ} (hx : x ∈ realChartDomain U)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    sphereRealMap f x ∈ realChartDomain V := by
  change ((Complex.equivRealProdCLM.symm (sphereRealMap f x) : ℂ) : Sphere) ∈ V
  simpa only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply,
    coe_finiteCoord hfinite] using hf hx

theorem sphereRealMap_left_inverse
    {f fi : Sphere → Sphere} {U : Set Sphere}
    (hl : ∀ p ∈ U, fi (f p) = p)
    {x : ℝ × ℝ} (hx : x ∈ realChartDomain U)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    sphereRealMap fi (sphereRealMap f x) = x := by
  simp only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply,
    coe_finiteCoord hfinite, hl _ hx, finiteCoord_coe,
    ContinuousLinearEquiv.apply_symm_apply]

theorem isOpen_realChartDomain {U : Set Sphere} (hU : IsOpen U) : IsOpen (realChartDomain U) :=
  hU.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

namespace IsSmoothSphereEquivalence

variable {f fi : Sphere → Sphere} {U V : Set Sphere}
variable (h : IsSmoothSphereEquivalence f fi U V)
variable (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)

include h hU hfix

theorem inverse_fixes_infty : fi OnePoint.infty = OnePoint.infty := by
  simpa only [hfix] using h.left_inv OnePoint.infty hU

theorem infty_mem_target : OnePoint.infty ∈ V := hfix ▸ h.mapsTo hU

theorem finite_inv {z : ℂ} (hz : (z : Sphere) ∈ V) : fi (z : Sphere) ≠ OnePoint.infty :=
  finite_image_of_fixes_infty h.symm.bijOn.injOn (h.infty_mem_target hU hfix)
    (h.inverse_fixes_infty hU hfix) hz

theorem real_bijOn : BijOn (sphereRealMap f) (realChartDomain U) (realChartDomain V) := by
  refine ⟨fun x hx => sphereRealMap_mem h.mapsTo hx (h.finite_forward hU hfix hx),
    sphereRealMap_injOn h.bijOn.injOn (fun _ hx => hx)
      (fun _ hx => h.finite_forward hU hfix hx), ?_⟩
  intro y hy
  have hyfin := h.finite_inv hU hfix hy
  exact ⟨sphereRealMap fi y, sphereRealMap_mem h.mapsTo_inv hy hyfin,
    sphereRealMap_left_inverse h.right_inv hy hyfin⟩

theorem real_left_inv {x : ℝ × ℝ} (hx : x ∈ realChartDomain U) :
    sphereRealMap fi (sphereRealMap f x) = x :=
  sphereRealMap_left_inverse h.left_inv hx (h.finite_forward hU hfix hx)

theorem real_right_inv {y : ℝ × ℝ} (hy : y ∈ realChartDomain V) :
    sphereRealMap f (sphereRealMap fi y) = y :=
  sphereRealMap_left_inverse h.right_inv hy (h.finite_inv hU hfix hy)

theorem real_smooth {x : ℝ × ℝ} (hx : x ∈ realChartDomain U) :
    ContDiffAt ℝ ∞ (sphereRealMap f) x :=
  (h.smooth _ hx).contDiffAt_sphereRealMap (h.finite_forward hU hfix hx)

theorem real_smooth_inv {y : ℝ × ℝ} (hy : y ∈ realChartDomain V) :
    ContDiffAt ℝ ∞ (sphereRealMap fi) y :=
  (h.smooth_inv _ hy).contDiffAt_sphereRealMap (h.finite_inv hU hfix hy)

theorem real_image_eq {O : Set (ℝ × ℝ)} (hO : O ⊆ realChartDomain U) :
    sphereRealMap f '' O = realChartDomain V ∩ (sphereRealMap fi) ⁻¹' O := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(h.real_bijOn hU hfix).mapsTo (hO hx), by
      change sphereRealMap fi (sphereRealMap f x) ∈ O
      rwa [h.real_left_inv hU hfix (hO hx)]⟩
  · rintro ⟨hy, hiy⟩
    exact ⟨sphereRealMap fi y, hiy, h.real_right_inv hU hfix hy⟩

theorem isOpen_real_image (hV : IsOpen V) {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hOU : O ⊆ realChartDomain U) : IsOpen (sphereRealMap f '' O) := by
  rw [h.real_image_eq hU hfix hOU]
  exact (show ContinuousOn (sphereRealMap fi) (realChartDomain V) from
    fun y hy => (h.real_smooth_inv hU hfix hy).continuousAt.continuousWithinAt).isOpen_inter_preimage
      (isOpen_realChartDomain hV) hO

end IsSmoothSphereEquivalence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridCoordinateFilling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth coordinate fillings from the actual boundary grids

The contour theorem gives one possible active label at each boundary.
The reciprocal-grid calculation turns its avoidance conclusions into
inactive-lattice avoidance for the actual local real branches. Thus the
smooth filling theorem applies at all sufficiently small widths.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem frontier_realJordanInterior (H : ℂ ≃ₜ ℂ) :
    frontier (realJordanInterior H) =
      Complex.equivRealProdCLM '' frontier (jordanInterior H) := by
  exact (Complex.equivRealProdCLM.toHomeomorph.image_frontier _).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteModelCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates on the actual finite circle model

The circle domain, its smooth inverse and the target coordinates are
constructed from the finite metric completion. Every measurable piece
of a source mask has exactly the same Dirichlet energy on its image.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem openCompletedRegion_subset_completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) :
    openCompletedRegion T ⊆ completedRegion T := by
  intro p hp hbad
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
  exact hp (mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealStageEstimates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic and geometric consequences of an actual real transfer stage. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}

namespace RealTransferStage

variable (M : RealTransferStage G π σ u a b Flag O K₀ ε)

theorem prescribed_core_conformal : IsConformalOn M.forward (sphericalCore K₀) :=
  M.conformal_core.mono (sphericalCore_mono (M.core_contains.trans interior_subset))

theorem functions_smooth_source (l : Fin n) :
    ContDiffOn ℝ ∞ (M.functions l) (realChartDomain (openCompletedRegion M.terminals.H)) :=
  (M.functions_smooth l).mono
    ((preimage_mono (openCompletedRegion_subset_completedRegion M.terminals.H)).trans
      M.extension_contains)

theorem functions_integrable_source (l : Fin n) :
    IntegrableOn (gradientEnergy (M.functions l) M.metric)
      (realChartDomain (openCompletedRegion M.terminals.H)) :=
  (M.integrable l).mono_set
    (preimage_mono (openCompletedRegion_subset_completedRegion M.terminals.H))

theorem source_energy_lt (l : Fin n) :
    (∫ x in realChartDomain (openCompletedRegion M.terminals.H),
      gradientEnergy (M.functions l) M.metric x) <
    (∫ x in realChartDomain G,
      gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε := by
  have h := M.source_energy l ∅ MeasurableSet.empty (empty_subset _)
  simp only [sdiff_empty] at h
  apply lt_of_le_of_lt _ h
  exact setIntegral_mono_set (M.integrable l)
    (ae_of_all _ (fun x => gradientEnergy_nonneg _ M.metric_pos x))
    (Eventually.of_forall fun x hx => openCompletedRegion_subset_completedRegion M.terminals.H hx)

theorem retained_on_core (l : Fin n) : EqOn (M.functions l) (u l) M.core := by
  intro x hx
  exact (M.retained.self_of_nhdsSet x hx) l

theorem terminal_frontier_extension (i : M.indices) :
    frontier (realJordanInterior (M.terminals.H i)) ⊆ M.extension := by
  rw [frontier_realJordanInterior]
  rintro x ⟨z, hz, rfl⟩
  apply M.extension_contains
  change (z : Sphere) ∈ completedRegion M.terminals.H
  intro hbad
  obtain ⟨j, w, hw, heq⟩ := mem_iUnion.mp hbad
  have hwz : w = z := OnePoint.coe_injective heq
  subst w
  by_cases hij : i = j
  · subst j
    exact Set.disjoint_left.mp
      (disjoint_frontier_iff_isOpen.mpr (jordanInterior_isOpen (M.terminals.H i))) hz hw
  · exact Set.disjoint_left.mp (M.terminals.disjoint_closures hij)
      (frontier_subset_closure hz) (subset_closure hw)

end RealTransferStage

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CountableRealTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countably many real tests and mandatory marked ends

Every finite prefix is transferred by the actual assembled construction.
An increasing sequence of finite mandatory sets puts each fixed mark in
all sufficiently late models. Prescribed neighborhoods and source cores
are retained at each stage.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def CountableRealCoordinates.NaturalCompatibility {S : Type*}
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) : Prop :=
  ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure ((π '' Gᶜ) \ range σ) (circleBandGraph d.source (d.coordinate j))
        (fun k => circleBandGraph d.source (d.coordinate k)) labels) = 0

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RealModelExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exhausting real transfer models

The prescribed source sets and the common exterior are constructed from
the domain. Thus the normal-family hypotheses follow from the actual
finite transfers, rather than being extra assumptions on their maps.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem core_conformal (n : ℕ) : IsConformalOn (M.stages n).forward (M.cores n) := by
  apply (M.stages n).prescribed_core_conformal.mono
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact infty_mem_sphericalCore _
  | coe z => simpa only [coe_mem_sphericalCore, realChartDomain, mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply] using hp

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnchoredJordanLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interior stability of Jordan fills with an interior anchor

Uniformly converging Jordan contours retain every compact part of the
limiting interior if one convergent sequence of interior points is
known. A smaller connected Jordan disk joins that anchor to the compact
set, and avoids all approximating boundaries. This uses no winding-number
assumption.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_compact_subset_jordanInterior_of_anchor
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {z : ℂ} {zn : ℕ → ℂ} (hz : z ∈ jordanInterior H)
    (hzn : Tendsto zn atTop (𝓝 z))
    (hanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (J n))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆ jordanInterior (J n) := by
  let S := H.symm '' (K ∪ {z})
  have hS : IsCompact S := (hK.union isCompact_singleton).image H.symm.continuous
  have hSball : S ⊆ ball (0 : ℂ) 1 := by
    rintro x ⟨w, hw, rfl⟩
    have hwH : w ∈ jordanInterior H := hw.elim (fun h => hKH h) (fun h => mem_singleton_iff.mp h ▸ hz)
    obtain ⟨t, ht, rfl⟩ := hwH
    simpa only [H.symm_apply_apply] using ht
  obtain ⟨r, ⟨hr, hr1⟩, hSr⟩ := exists_pos_lt_subset_ball zero_lt_one hS.isClosed hSball
  let D := dilatedJordan H r hr
  let C := closure (jordanInterior D)
  have hD : jordanInterior D = H '' ball (0 : ℂ) r := jordanInterior_dilated H hr
  have hC : C = H '' closedBall (0 : ℂ) r := by
    dsimp only [C]
    rw [hD, ← H.image_closure, closure_ball 0 hr.ne']
  have hKC : K ⊆ C := by
    intro x hx
    apply subset_closure
    rw [hD]
    exact ⟨H.symm x, hSr ⟨x, Or.inl hx, rfl⟩, H.apply_symm_apply x⟩
  have hzD : z ∈ jordanInterior D := by
    rw [hD]
    exact ⟨H.symm z, hSr ⟨z, Or.inr rfl, rfl⟩, H.apply_symm_apply z⟩
  have hCH : C ⊆ jordanInterior H := by
    rw [hC]
    apply image_mono
    exact closedBall_subset_ball hr1
  have hCcompact : IsCompact C := isCompact_closure_jordanInterior D
  have hCconn : IsPreconnected C := (isConnected_jordanInterior D).isPreconnected.closure
  have hγC : range γ ⊆ Cᶜ := by
    rw [hfront]
    intro x hx hxC
    have hxH := hCH hxC
    have hnot : x ∉ jordanInterior H := by
      simpa only [(jordanInterior_isOpen H).interior_eq] using hx.2
    exact hnot hxH
  obtain ⟨δ, hδ, hδC⟩ := (isCompact_range hγ).exists_thickening_subset_open
    hCcompact.isClosed.isOpen_compl hγC
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  have hznD : ∀ᶠ n in atTop, zn n ∈ jordanInterior D :=
    hzn ((jordanInterior_isOpen D).mem_nhds hzD)
  filter_upwards [hclose, hfrontn, hznD, hanchor] with n hn hnfront hnD hnanchor
  have hnC : frontier (jordanInterior (J n)) ⊆ Cᶜ := by
    rw [← hnfront]
    rintro x ⟨t, rfl⟩
    apply hδC
    exact mem_thickening_iff.mpr ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩
  have hCJ : C ⊆ jordanInterior (J n) := by
    apply hCconn.subset_of_closure_inter_subset (jordanInterior_isOpen (J n))
      ⟨zn n, subset_closure hnD, hnanchor⟩
    rintro x ⟨hxcl, hxC⟩
    by_contra hxJ
    have hxf : x ∈ frontier (jordanInterior (J n)) := by
      rw [frontier, (jordanInterior_isOpen (J n)).interior_eq]
      exact ⟨hxcl, hxJ⟩
    exact hnC hxf hxC
  exact hKC.trans hCJ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealSequenceRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retention of actual tests and their crossing segments along model subsequences. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_test_eq {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (l : ℕ) :
    ∀ᶠ n in atTop, ∀ z : ℂ, (z : Sphere) ∈ K →
      (M.stages n).functions (prefixIndex l n) (Complex.equivRealProdCLM z) =
        d.physical l (Complex.equivRealProdCLM z) := by
  filter_upwards [M.eventually_core_contains hK hKG, prefixIndex_eq l] with n hn hl
  intro z hz
  have hcore : Complex.equivRealProdCLM z ∈ (M.stages n).core := by
    apply interior_subset ((M.stages n).core_contains ?_)
    simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hn hz
  have h := (M.stages n).retained_on_core (prefixIndex l n) hcore
  simpa only [hl] using h

end CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection payment for a retained real barrier

The test is specified by its actual values on two source contours and
their matched target contours. All finite-model crossings and analytic
estimates are supplied by the constructed sequence.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RetainedRealBarrier {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (F : ℂ → ℂ) (l : ℕ) where
  inner : SmoothJordanCore G
  outer : SmoothJordanCore G
  inner_index : Fin inner.count
  outer_index : Fin outer.count
  value_one : ∀ z ∈ frontier (jordanInterior (inner.disk inner_index)),
    d.physical l (Complex.equivRealProdCLM z) = 1
  value_zero : ∀ z ∈ frontier (jordanInterior (outer.disk outer_index)),
    d.physical l (Complex.equivRealProdCLM z) = 0
  target_inner : ℂ ≃ₜ ℂ
  target_outer : ℂ ≃ₜ ℂ
  inner_image : extendAtInfinity F ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior (inner.disk inner_index))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior target_inner)
  outer_image : extendAtInfinity F ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior (outer.disk outer_index))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior target_outer)
  inner_side : extendAtInfinity F ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (inner.disk inner_index))) =
    (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior target_inner)
  outer_side : extendAtInfinity F ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (outer.disk outer_index))) =
    (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior target_outer)
  nested : closure (jordanInterior target_inner) ⊆ jordanInterior target_outer

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure UngatedRealTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) where
  coordinate : PhysicalRealCoordinate d π
  region : Set Sphere
  region_open : IsOpen region
  zero : ∀ x ∈ EStar, coordinate.quotient x = 0
  one : ∀ x ∈ region ∩ d.quotientDomain, coordinate.quotient x = 1
  exclusions : Set Sphere
  exclusions_countable : exclusions.Countable
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑' x, weight x ^ 2) < ∞
  weight_support : support weight ⊆ exclusions
  band_bound : ∀ x ∈ d.dust, ENNReal.ofReal
    (limsup coordinate.quotient (𝓝[d.quotientDomain] x) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] x)) ≤ weight x

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def size (c : UngatedRealTest d π EStar) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
    FiniteTransfer.gradientEnergy c.coordinate.physical
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) + countingSquareNorm c.weight

def CompatibleWith (c : UngatedRealTest d π EStar)
    (A : Set (UngatedRealTest d π EStar)) : Prop :=
  (∀ a ∈ A, a.exclusions ∩ d.dust ⊆ c.exclusions) ∧
  ∀ (n : ℕ) (q : Fin n → UngatedRealTest d π EStar), (∀ i, q i ∈ A) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.exclusions)
        (circleBandGraph d.quotientDomain c.coordinate.quotient)
        (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient) id) = 0

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelRealEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover ordinary real Dirichlet estimates from the same masked
circle metric. The full-mask barriers retain their real gradient energy. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {J I A : Type*} {n N : ℕ} {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ}
  {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
  {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
  {θ : Fin n → ℝ} {ε : ℝ} {Q : MaskedModelData T H G K M f χ N θ ε}
  {ι : A → Fin n} {r : A → (ℝ × ℝ) → ℝ}

theorem ModelRealSubfamily.gradient_eq (W : ModelRealSubfamily Q ι r)
    (hG : IsOpen G) (j : A) {x : ℝ × ℝ}
    (hx : x ∈ G ∪ ⋃ i, realJordanInterior (H i)) :
    circleGradient (Q.functions (ι j)) x = planarGradient (W.functions j) x := by
  have he : Q.functions (ι j) = fun y => (W.functions j y : UnitAddCircle) :=
    funext (fun y => (W.projection j y).symm)
  rw [he]
  exact circleGradient_coe_eq_planarGradient
    (hG.union (isOpen_iUnion fun i => (realJordanInterior_geometry (H i)).1)) (W.filled.1 j) hx

theorem ModelRealSubfamily.source_energy (W : ModelRealSubfamily Q ι r)
    (hG : IsOpen G) (hRM : ∀ j, M (ι j) = univ)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (j : A) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ x in realChartDomain (completedRegion T) \ E, gradientEnergy (W.functions j) Q.metric x) <
      (∫ x in G \ E, gradientEnergy (r j) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  have hF : (∫ x in realChartDomain (completedRegion T) \ E,
      gradientEnergy (W.functions j) Q.metric x) =
      ∫ x in realChartDomain (completedRegion T) \ E,
        fieldEnergy (circleGradient (Q.functions (ι j))) Q.metric x := by
    apply setIntegral_congr_fun ((isClosed_real_completedRegion T).measurableSet.diff hE)
    intro x hx
    change covectorEnergy _ _ = covectorEnergy _ _
    rw [W.gradient_eq hG j (W.extension_contains hx.1)]
  have hf : (∫ x in G \ E, fieldEnergy (circleGradient (f (ι j)))
      (fun x => sphericalMetricFactor x • 1) x) =
      ∫ x in G \ E, gradientEnergy (r j) (fun x => sphericalMetricFactor x • 1) x := by
    apply setIntegral_congr_fun (hG.measurableSet.diff hE)
    intro x hx
    have he : f (ι j) = fun y => (r j y : UnitAddCircle) := funext (fun y => (hrproj j y).symm)
    change covectorEnergy _ _ = covectorEnergy _ _
    rw [he, circleGradient_coe_eq_planarGradient hG (hr j) hx.1]
  have h := Q.localized (ι j) E hE hEK
  rw [hRM j, inter_univ, inter_univ, hf, ← hF] at h
  exact h

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MixedCoordinateStage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mixed stage retains both its period data and a real stage with the
same map, inverse, metric, terminals and core. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n m : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {C : Fin n → MaskedCoordinateData G U π σ} {ι : Fin m → Fin n} {r : Fin m → (ℝ × ℝ) → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}

def MixedCoordinateStage.realStage
    (T : MixedCoordinateStage C ι r Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hRM : ∀ j, (C (ι j)).mask = univ)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) (realChartDomain G))
    (hr2 : ∀ j, MemLp (planarGradient (r j)) 2 (volume.restrict (realChartDomain G)))
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = (C (ι j)).physical x) :
    RealTransferStage G π σ r (fun j => (C (ι j)).lower) (fun j => (C (ι j)).upper)
      Flag O K₀ ε := by
  classical
  letI : Fintype T.indices := T.indices_finite.fintype
  refine {
    indices := T.indices
    finite_indices := T.indices_finite
    flags := T.flags
    terminals := T.terminals
    core := T.core
    core_closed := T.core_closed
    core_contains := T.core_contains
    core_source := T.core_source
    core_cocompact := T.core_cocompact
    core_model := T.core_model
    functions := T.real.functions
    extension := realChartDomain G ∪ ⋃ i, realJordanInterior (T.filling i)
    extension_open := (isOpen_realChartDomain hG).union
      (isOpen_iUnion fun i => (realJordanInterior_geometry (T.filling i)).1)
    extension_contains := T.real.extension_contains
    functions_smooth := T.real.filled.1
    retained := T.real.retained
    radius := T.model.radius
    radius_pos := T.model.radius_pos
    metric := T.model.metric
    metric_smooth := T.model.metric_smooth
    metric_pos := T.model.metric_pos
    metric_core := T.model.metric_core
    metric_far := T.model.metric_far
    source_energy := fun j E hE hEK => T.real.source_energy (isOpen_realChartDomain hG)
      (fun j => by simp only [hRM, physicalMask, preimage_univ, realChartDomain]) hr hrproj j hE hEK
    excess := T.real_excess
    oscillation := ?_
    domain := T.model.domain
    forward := T.model.forward
    inverse := T.model.inverse
    circle_domain := T.model.circle_domain
    equivalence := T.model.equivalence
    conformal_core := T.model.conformal_core
    principal := T.model.principal
    metric_conformal := T.real.metric_conformal
    integrable := ?_
    transported_smooth := fun j => (T.real.transported j).1 }
  · intro j
    rw [tsum_fintype]
    apply (CircleDomainRigidity.sqrt_sum_sq_le_band_add_excess
      (fun s : T.indices => terminalOscillation (T.terminals.H s) (T.real.functions j))
      (fun s : T.indices => (C (ι j)).upper s - (C (ι j)).lower s)
      (fun _ => Metric.diam_nonneg) (fun s => (C (ι j)).width_nonneg s)).trans_lt
    apply add_lt_add_of_le_of_lt
    · exact CircleDomainRigidity.finite_label_band_norm_le (fun s : T.indices => (s : S))
        Subtype.val_injective (fun s => (C (ι j)).upper s - (C (ι j)).lower s)
        (C (ι j)).width_summable
    · simpa only [tsum_fintype] using T.real_excess j
  · intro j
    exact integrableOn_gradientEnergy_with_cofinite_core
      ((isOpen_realChartDomain hG).union (isOpen_iUnion fun i =>
        (realJordanInterior_geometry (T.filling i)).1))
      (isClosed_real_completedRegion T.terminals.H) T.real.extension_contains
      T.core_closed T.core_cocompact T.core_source (T.real.filled.1 j)
      (integrable_gradientEnergy_spherical_of_memLp (hr2 j))
      (T.real.retained.mono fun _ hx => hx j) T.model.metric_smooth.continuous
      T.model.metric_pos T.model.metric_core

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealCoordinateSubfamily
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real coordinates retained inside a finite masked family. -/

open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure RealCoordinateSubfamily {S A L : Type*} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : L → MaskedCoordinateData G U π σ)
    (ι : A → L) where
  physical : A → (ℝ × ℝ) → ℝ
  quotient : A → Sphere → ℝ
  bound : A → ℝ
  bounded : ∀ j x, x ∈ U → |quotient j x| ≤ bound j
  full_mask : ∀ j, (C (ι j)).mask = univ
  smooth : ∀ j, ContDiffOn ℝ ∞ (physical j) (realChartDomain G)
  energy : ∀ j, MemLp (planarGradient (physical j)) 2 (volume.restrict (realChartDomain G))
  pullback : ∀ j x, x ∈ realChartDomain G →
    quotient j (π (Complex.equivRealProdCLM.symm x : Sphere)) = physical j x
  projection : ∀ j x, (physical j x : UnitAddCircle) = (C (ι j)).physical x
  width : ∀ j s, limsup (quotient j) (𝓝[U] (σ s)) -
    liminf (quotient j) (𝓝[U] (σ s)) ≤ (C (ι j)).upper s - (C (ι j)).lower s

def RealCoordinateSubfamily.reindex
    {S A L B D : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : L → MaskedCoordinateData G U π σ} {ι : A → L}
    (R : RealCoordinateSubfamily C ι) (label : B → L) (realIndex : D → A)
    (slot : D → B) (hlabel : ∀ j, label (slot j) = ι (realIndex j)) :
    RealCoordinateSubfamily (fun l => C (label l)) slot where
  physical j := R.physical (realIndex j)
  quotient j := R.quotient (realIndex j)
  bound j := R.bound (realIndex j)
  bounded j := R.bounded (realIndex j)
  full_mask j := by simpa only [hlabel] using R.full_mask (realIndex j)
  smooth j := R.smooth (realIndex j)
  energy j := R.energy (realIndex j)
  pullback j := R.pullback (realIndex j)
  projection j := by simpa only [hlabel] using R.projection (realIndex j)
  width j := by simpa only [hlabel] using R.width (realIndex j)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealCoordinateData
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Place the existing real barrier coordinates into the masked family
without changing their graph, physical function, or band endpoints. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}

theorem CountableRealCoordinates.boundary_limits
    (d : CountableRealCoordinates G π σ) (l : ℕ) (s : S) :
    d.lower l s = liminf (d.coordinate l) (𝓝[d.source] (σ s)) ∧
      d.upper l s = limsup (d.coordinate l) (𝓝[d.source] (σ s)) := by
  have he := (d.band l s).symm.trans
    (intervalFiberHull_clusterGraph_eq_boundary_band (d.coordinate_bounded l) (d.labels_closure s))
  exact (Icc_eq_Icc_iff (sub_nonneg.mp (d.width_nonneg l s))).mp he

def CountableRealCoordinates.maskedCoordinate
    (d : CountableRealCoordinates G π σ) (hG : IsOpen G) (s₀ : S) (l : ℕ) :
    MaskedCoordinateData G d.source π σ := by
  classical
  let q : Sphere → ℝ := d.source.indicator (d.coordinate l)
  have hq (x : Sphere) (hx : x ∈ d.source) : q x = d.coordinate l x := indicator_of_mem hx _
  have hbound (x : Sphere) : |q x| ≤ |d.bound l| := by
    by_cases hx : x ∈ d.source
    · rw [hq x hx]
      exact (d.coordinate_bounded l x hx).trans (le_abs_self _)
    · simpa only [q, indicator_of_notMem hx, abs_zero] using abs_nonneg (d.bound l)
  have hpull (x : ℝ × ℝ) (hx : x ∈ realChartDomain G) :
      q (π (Complex.equivRealProdCLM.symm x : Sphere)) = d.physical l x := by
    rw [hq _ (d.source_map _ hx)]
    exact (d.pullback l _ hx).symm.trans
      (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  refine {
    graph := circleBandGraph d.source (d.coordinate l)
    graph_closed := (isCompact_circleBandGraph (d.coordinate_bounded l)).isClosed
    mask := univ
    mask_closed := isClosed_univ
    mask_frontier := by simp
    singular := s₀
    Index := Unit
    patch := fun _ => univ
    patch_open := fun _ => isOpen_univ
    cover := by
      intro x _
      exact mem_iUnion.mpr ⟨(), mem_univ _⟩
    branch := fun _ => q
    bound := fun _ => |d.bound l|
    branch_bounded := fun _ => hbound
    physical := fun x => (d.physical l x : UnitAddCircle)
    measurable := (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp (d.physical_measurable l)
    gradient_measurable := measurable_circleGradient
      ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp (d.physical_measurable l))
    smooth := ?_
    energy := ?_
    physical_graph := ?_
    branch_smooth := ?_
    branch_projection := ?_
    lower := d.lower l
    upper := d.upper l
    width_nonneg := d.width_nonneg l
    width_summable := d.width_summable l
    marked_fiber := ?_
    marked_branch := ?_
    free_fiber := ?_ }
  · simpa only [physicalMask, preimage_univ, realChartDomain, interior_univ, inter_univ] using
      smoothCircleOn_coe (isOpen_realChartDomain hG) (d.physical_smooth l)
  · simp only [physicalMask, preimage_univ, realChartDomain, Measure.restrict_univ]
    apply (d.physical_energy l).ae_eq
    filter_upwards [ae_restrict_mem (isOpen_realChartDomain hG).measurableSet] with x hx
    exact (circleGradient_coe_eq_planarGradient (isOpen_realChartDomain hG)
      (d.physical_smooth l) hx).symm
  · intro x hx
    apply (circleBandGraph_on_open d.source_open (d.coordinate_continuous l)
      (d.source_map _ hx.1)).mpr
    congr 1
    exact (d.pullback l _ hx.1).symm.trans
      (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  · intro i
    apply ((d.physical_smooth l).mono inter_subset_left).congr
    intro x hx
    exact hpull x hx.1
  · intro i x hx
    exact congrArg (fun r : ℝ => (r : UnitAddCircle)) (hpull x hx.1)
  · intro s t ht
    obtain ⟨⟨x, a⟩, ha, he⟩ := ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨a, (d.band l s ▸ ha), rfl⟩
  · intro s _ _
    have heq : q =ᶠ[𝓝[d.source] (σ s)] d.coordinate l := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hq x hx
    refine ⟨(), mem_univ _, ?_, ?_⟩
    · exact (d.boundary_limits l s).1.trans (liminf_congr heq).symm
    · exact (d.boundary_limits l s).2.trans (limsup_congr heq).symm
  · intro x hx hfree t ht u hu
    obtain ⟨a, ha⟩ := d.free_trace x hx hfree l
    obtain ⟨⟨y, b⟩, hb, he⟩ := ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨⟨y, c⟩, hc, he⟩ := hu
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hb' : b = a := mem_singleton_iff.mp (ha ▸ hb)
    have hc' : c = a := mem_singleton_iff.mp (ha ▸ hc)
    exact congrArg (fun r : ℝ => (r : UnitAddCircle)) (hb'.trans hc'.symm)

def CountableRealCoordinates.realSubfamily
    (d : CountableRealCoordinates G π σ) (hG : IsOpen G) (s₀ : S) :
    RealCoordinateSubfamily (d.maskedCoordinate hG s₀) id where
  physical := d.physical
  quotient := d.coordinate
  bound := d.bound
  bounded := d.coordinate_bounded
  full_mask := fun _ => rfl
  smooth := d.physical_smooth
  energy := d.physical_energy
  pullback l x hx := (d.pullback l _ hx).symm.trans
    (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  projection := fun _ _ => rfl
  width l s := by
    change limsup (d.coordinate l) (𝓝[d.source] (σ s)) -
      liminf (d.coordinate l) (𝓝[d.source] (σ s)) ≤ d.upper l s - d.lower l s
    rw [← (d.boundary_limits l s).1, ← (d.boundary_limits l s).2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealStageBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Changing only the presentation of equal terminal widths preserves
all geometric and analytic data of a real stage. -/

open Set Filter
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def RealTransferStage.withBands
    {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {r : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
    (T : RealTransferStage G π σ r a b Flag O K₀ ε)
    (a' b' : Fin n → S → ℝ) (heq : ∀ l s, b l s - a l s = b' l s - a' l s) :
    RealTransferStage G π σ r a' b' Flag O K₀ ε :=
  { T with
    excess := fun l => by simpa only [heq] using T.excess l
    oscillation := fun l => by simpa only [heq] using T.oscillation l }

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_EnlargedRealModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarge the common exterior radius without changing the actual finite
models or their transferred coordinates. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}

def RealModelExhaustion.withRadius (M : RealModelExhaustion d O ε)
    (R : ℝ) (hR : M.radius ≤ R) : RealModelExhaustion d O ε where
  radius := R
  radius_pos := M.radius_pos.trans_le hR
  plane := M.plane
  plane_open := M.plane_open
  plane_connected := M.plane_connected
  plane_monotone := M.plane_monotone
  cores := M.cores
  core_compact := M.core_compact
  core_source := M.core_source
  plane_core := M.plane_core
  exhausts := M.exhausts
  exterior_core := fun n =>
    (compl_subset_compl.mpr (image_mono (ball_subset_ball hR))).trans (M.exterior_core n)
  exterior_plane := by
    intro z hz
    apply M.exterior_plane
    change 2 * M.radius ≤ ‖z‖
    exact (mul_le_mul_of_nonneg_left hR (by norm_num)).trans hz
  flags := M.flags
  flags_finite := M.flags_finite
  flags_monotone := M.flags_monotone
  stages := M.stages
  indices_nonempty := M.indices_nonempty
  marks := M.marks

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MixedSequenceRetention
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed coordinate is eventually retained, with its actual
values and differential, on every compact source set of the common
model sequence. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

def coordinateIndex (c : C) (n : ℕ) : Fin (M.size n) := by
  classical
  exact if h : c ∈ range (M.label n) then Classical.choose h
    else M.slot n ⟨0, Nat.succ_pos n⟩

def withRadius (R : ℝ) (hR : M.real.radius ≤ R) :
    MixedModelExhaustion d data retained O ε ρ :=
  { M with real := M.real.withRadius R hR }

end MixedModelExhaustion
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inward collars for regular Jordan boundaries.

Published input: J. M. Lee, Introduction to Smooth Manifolds, second edition
(2013), Theorem 9.25, pp.222--223 (Collar Neighborhood Theorem), together with
its regular-domain interpretation in Proposition5.47, p.121. The formulation
below is the compact planar Jordan-boundary specialization: parametrize the
boundary circle (Milnor's compact one-manifold classification), take inward
collar slices, and use their bounded Jordan sides (planar Schoenflies).
It is a specialization/corollary, not a verbatim transcription of Theorem9.25.
The continuous-tangent clause retains the C¹ dependence of its smooth
collar embedding and is used only for the uniform boundary variation bound.
The regular-level hypothesis is retained explicitly.
https://thunv.wordpress.com/wp-content/uploads/2015/09/graduate-texts-in-mathematics-vol-218-john-m-lee-introduction-to-smooth-manifolds-springer-2013.pdf
DOI: 10.1007/978-1-4419-9982-5.
-/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

structure RegularJordanInwardCollar (H : ℂ ≃ₜ ℂ) where
  width : ℝ
  width_pos : 0 < width
  curve : ℝ → ℝ → ℂ
  disk : ℝ → ℂ ≃ₜ ℂ
  disk_zero : disk 0 = H
  continuous : ContinuousOn (fun p : ℝ × ℝ => curve p.1 p.2) (Icc 0 width ×ˢ univ)
  tangent_continuous : ContinuousOn (fun p : ℝ × ℝ => deriv (curve p.1) p.2)
    (Icc 0 width ×ˢ univ)
  parametrization : ∀ ρ ∈ Icc 0 width, PositiveJordanParametrization (disk ρ) (curve ρ)
  inward : ∀ ρ ∈ Ioc 0 width, closure (jordanInterior (disk ρ)) ⊆ jordanInterior H
  retains_compact : ∀ K : Set ℂ, IsCompact K → K ⊆ jordanInterior H →
    ∃ η > 0, η ≤ width ∧ ∀ ρ ∈ Ioc 0 η, K ⊆ jordanInterior (disk ρ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedStageEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and full masked energy on the actual finite model.
The geometric facts retained from construction justify comparison of
ordinary integrals on all later subregions. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {C : Fin n → MaskedCoordinateData G U π σ} {Flag : Set S} {O : S → Set Sphere}
  {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}

def MaskedCoordinateStage.sourceMask
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) : Set (ℝ × ℝ) :=
  realChartDomain (openCompletedRegion T.terminals.H) ∩ interior (physicalMask π (C l).mask)

def MaskedCoordinateStage.targetMask
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) : Set (ℝ × ℝ) :=
  sphereRealMap T.model.forward '' T.sourceMask l

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedStokesGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All finite geometric inputs to the masked Stokes bound are constructed
from a retained physical collar and the actual terminal assignment. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure StokesCollarGeometry
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n)
    (s : T.indices) (H : ℂ ≃ₜ ℂ)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain) where
  center : T.indices → ℂ
  radius : T.indices → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  disks : ∀ i, connectedComponentIn T.model.domainᶜ (a.point i) =
    ((↑) : ℂ → Sphere) '' closedBall (center i) (radius i)
  disjoint : Pairwise (Disjoint on fun i => closedBall (center i) (radius i))
  exterior : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ i, closedBall (center i) (radius i))ᶜ
  target : ℂ ≃ₜ ℂ
  boundary : T.model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior target)
  count : ℕ
  label : Fin count → T.indices
  injective : Injective label
  base : Fin count
  distinguished : label base = s
  inside : ∀ j, closedBall (center (label j)) (radius (label j)) ⊆ jordanInterior target
  mask : ∀ j, σ (label j) ∈ (C l).mask
  region : closure (jordanInterior target) \ ⋃ j, closedBall (center (label j)) (radius (label j)) ⊆
    Complex.equivRealProdCLM ⁻¹' T.targetMask l

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedCoordinateMarks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable selected family uses only countably many nonzero bands.
Restricting to these marks preserves the actual graph, physical function
and masks; every discarded marked fiber is already a singleton. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def MaskedCoordinateData.restrictMarks
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (A : Set S) (hsing : C.singular ∈ A)
    (hsupport : ∀ s, C.upper s - C.lower s ≠ 0 → s ∈ A) :
    MaskedCoordinateData G U π (fun s : A => σ s.val) where
  graph := C.graph
  graph_closed := C.graph_closed
  mask := C.mask
  mask_closed := C.mask_closed
  mask_frontier := C.mask_frontier
  singular := ⟨C.singular, hsing⟩
  Index := C.Index
  patch := C.patch
  patch_open := C.patch_open
  cover := C.cover
  branch := C.branch
  bound := C.bound
  branch_bounded := C.branch_bounded
  physical := C.physical
  measurable := C.measurable
  gradient_measurable := C.gradient_measurable
  smooth := C.smooth
  energy := C.energy
  physical_graph := C.physical_graph
  branch_smooth := C.branch_smooth
  branch_projection := C.branch_projection
  lower := fun s => C.lower s.val
  upper := fun s => C.upper s.val
  width_nonneg := fun s => C.width_nonneg s
  width_summable := C.width_summable.subtype (· ∈ A)
  marked_fiber := fun s => C.marked_fiber s
  marked_branch := fun s => C.marked_branch s
  free_fiber := by
    intro x hx hxrange
    by_cases hxo : x ∈ range σ
    · obtain ⟨s, rfl⟩ := hxo
      have hsA : s ∉ A := by
        intro hs
        exact hxrange ⟨⟨s, hs⟩, rfl⟩
      have hz : C.upper s - C.lower s = 0 := by
        by_contra h
        exact hsA (hsupport s h)
      have hband := C.marked_fiber s
      rw [sub_eq_zero.mp hz, Icc_self, image_singleton] at hband
      intro a ha b hb
      exact (mem_singleton_iff.mp (hband ha)).trans (mem_singleton_iff.mp (hband hb)).symm
    · exact C.free_fiber x hx hxo

 theorem MaskedCoordinateData.restrictMarks_sourceStokesBudget_le
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (A : Set S) (hsing : C.singular ∈ A)
    (hsupport : ∀ s, C.upper s - C.lower s ≠ 0 → s ∈ A)
    {R : ℝ} (hR : 0 ≤ R) :
    (C.restrictMarks A hsing hsupport).sourceStokesBudget R ≤ C.sourceStokesBudget R := by
  let D := C.restrictMarks A hsing hsupport
  let e : {t : A // t ≠ D.singular} → {s : S // s ≠ C.singular} :=
    fun t => ⟨t.val.val, fun h => t.property (Subtype.ext h)⟩
  have he : Injective e := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : {s : S // s ≠ C.singular} => s.val) h
  have hs : (∑' t : {t : A // t ≠ D.singular}, (D.upper t - D.lower t) ^ 2) ≤
      ∑' s : {s : S // s ≠ C.singular}, (C.upper s - C.lower s) ^ 2 := by
    exact (D.width_summable.subtype (· ≠ D.singular)).tsum_le_tsum_of_inj e he
      (fun _ _ => sq_nonneg _) (fun _ => le_rfl)
      (C.width_summable.subtype (· ≠ C.singular))
  unfold sourceStokesBudget
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs)
  positivity

 def RealCoordinateSubfamily.restrictMarks
    {L J S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : L → MaskedCoordinateData G U π σ} {ι : J → L}
    (R : RealCoordinateSubfamily C ι) (A : Set S)
    (hsing : ∀ l, (C l).singular ∈ A)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A) :
    RealCoordinateSubfamily (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι where
  physical := R.physical
  quotient := R.quotient
  bound := R.bound
  bounded := R.bounded
  full_mask := R.full_mask
  smooth := R.smooth
  energy := R.energy
  pullback := R.pullback
  projection := R.projection
  width := fun j s => R.width j s.val

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedLevelPresentation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations of selected real and mean coordinates, retaining
their functions, compact laws, and the data for subsequent code-law bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_24
structure RealCoordinatePresentation (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) where
  coordinate : PhysicalRealCoordinate d π
  graph_eq : C.graph = circleBandGraph d.quotientDomain coordinate.quotient
  mask_eq_univ : C.mask = univ
  physical_eq : ∀ x, (coordinate.physical x : UnitAddCircle) = C.physical x
  band_width : ∀ s, C.upper s - C.lower s =
    limsup coordinate.quotient (𝓝[d.quotientDomain] s.val) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] s.val)
  compactSupport : Set ℂ
  isCompact_support : IsCompact compactSupport
  zero_off : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ compactSupport →
    coordinate.quotient (π (z : Sphere)) = 0
  zero_infty : OnePoint.infty ∈ d.physicalDomain → coordinate.quotient (π OnePoint.infty) = 0

structure MeanCoordinatePresentation (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) where
  arcs : Set C(PathTime, Sphere)
  diskArcs : Set C(PathTime, ℂ)
  compact_diskArcs : IsCompact diskArcs
  terminal_diskArcs : diskArcs ⊆ diskTerminalArcSet
  law : ProbabilityMeasure arcs
  map : C(Sphere, ℂ)
  arcMap : arcs → diskArcs
  measurable_arcMap : Measurable arcMap
  arcMap_eq : ∀ γ : arcs, (arcMap γ).val = map.comp γ.val
  neighborhood : Set Sphere
  mask : Set Sphere
  open_neighborhood : IsOpen neighborhood
  closed_mask : IsClosed mask
  excludes_infty : π OnePoint.infty ∉ mask
  boundary_domain : mask \ interior mask ⊆ d.quotientDomain
  singular : Sphere
  singular_eq : (C.singular : Sphere) = singular
  singular_dust : singular ∈ d.dust
  singular_mask : singular ∈ mask
  singular_outside : singular ∉ neighborhood
  punctured_mask : mask \ {singular} ⊆ neighborhood
  nonzero : ∀ x ∈ neighborhood, map x ≠ 0
  unit_bound : ∀ x ∈ neighborhood, ‖map x‖ ≤ 1
  strict_bound : ∀ x ∈ mask \ d.quotientDomain, ‖map x‖ < 1
  injective_arcs : ∀ γ : arcs, InjOn map (range γ.val ∪ neighborhood)
  mean : SmoothMeanPeriodData hsch diskArcs terminal_diskArcs (law.map measurable_arcMap.aemeasurable) map
    d.physicalDomain d.quotientDomain neighborhood mask singular π
  graph_eq : C.graph = periodBandGraph d.quotientDomain mask singular mean.patch mean.branch

abbrev SelectedLevelPresentation (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) :=
  Sum (RealCoordinatePresentation d π C) (MeanCoordinatePresentation hsch d π C)


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rc4c60f_1 : BorelSpace Sphere := ⟨rfl⟩
structure SelectableMaskedCoordinate (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) where
  coordinate : MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val)
  flags : Set Sphere
  flags_countable : flags.Countable
  flags_dust : flags ⊆ d.dust
  weight_support : support coordinate.dustWeight ⊆ flags
  singular_marked : (coordinate.singular : Sphere) ∈ flags
  domain_unique : ∀ x ∈ d.quotientDomain,
    {t : UnitAddCircle | (x, t) ∈ coordinate.graph}.Subsingleton
  weighted : ∀ (g : Sphere → ℝ≥0∞), Measurable g →
    (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞ →
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in d.physicalDomain ∩ π ⁻¹' {x | (x, θ) ∈ coordinate.graph},
        g p ∂(μH[1] : Measure Sphere)) < ∞

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ZeroRealCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A zero coordinate occupies unused selection slots. Its new-level failure
event is contained in the single zero circle level, hence has zero measure. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

def PhysicalRealCoordinate.zero (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) :
    PhysicalRealCoordinate d π where
  quotient := fun _ => 0
  quotient_continuous := continuousOn_const
  quotient_unit := fun _ => ⟨le_rfl, zero_le_one⟩
  physical := fun _ => 0
  physical_measurable := measurable_const
  physical_smooth := contDiffOn_const
  physical_energy := by
    have he : FiniteTransfer.planarGradient (fun _ : ℝ × ℝ => (0 : ℝ)) = 0 := by
      funext x
      simp [FiniteTransfer.planarGradient]
    rw [he]
    exact MemLp.zero
  pullback := fun _ _ => rfl

def UngatedRealTest.zeroTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) : UngatedRealTest d π EStar where
  coordinate := PhysicalRealCoordinate.zero d π
  region := ∅
  region_open := isOpen_empty
  zero := fun _ _ => rfl
  one := fun _ hx => hx.1.elim
  exclusions := ∅
  exclusions_countable := countable_empty
  weight := fun _ => 0
  weight_finite := by simp
  weight_support := by simp
  band_bound := by
    intro x hx
    simp only [PhysicalRealCoordinate.zero]
    by_cases h : NeBot (𝓝[d.quotientDomain] x)
    · let := h
      simp
    · have he : 𝓝[d.quotientDomain] x = ⊥ := not_neBot.mp h
      simp only [he, limsup_eq, liminf_eq, eventually_bot, ofPred_true]
      rw [Real.sInf_of_not_bddBelow not_bddBelow_univ,
        Real.sSup_of_not_bddAbove not_bddAbove_univ]
      norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MapDiskExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-circuit exclusions in the compact-open space of maps and disks.
The circuit restriction is continuous, so these are the open sets used by
countable selection, not just open sets of boundary traces. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def circuitRestriction {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (p : MapDiskData G) : BoundaryPairData := (p.1.comp γ, p.2)

 def mapDiskExclusion {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (v : ℝ → ℝ) (budget : ℝ) : Set (MapDiskData G) :=
  circuitRestriction γ ⁻¹' boundaryExclusionSet v budget

 def sourceCircuit {G : Set Sphere} (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hG : ∀ t, (γ t : Sphere) ∈ G) : C(PathTime, FiniteSource G) :=
  ⟨fun t => ⟨γ t, hG t⟩, (hγ.comp continuous_subtype_val).subtype_mk _⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GradedRealSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable selection of the constructed ungated tests, at every reciprocal
accuracy. Compatibility retains every earlier test and its exceptional set. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure GradedRealTest (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (EStar : Set Sphere) extends UngatedRealTest d π EStar where
  grade : ℕ
  small : toUngatedRealTest.size < ENNReal.ofReal (1 / ((grade : ℝ) + 1))

namespace GradedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def Allowed (A : Set (GradedRealTest d π EStar)) (c : GradedRealTest d π EStar) : Prop :=
  c.toUngatedRealTest.CompatibleWith
    (insert (UngatedRealTest.zeroTest d π EStar) (toUngatedRealTest '' A))

end GradedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved outputs retained at one stage of the endpoint-law recursion.
The candidate includes actual densities and quantitative mark budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

abbrev anchor_eq := L.geometry.anchor_eq

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TwoEndedCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the two actual collar tails and a selected actual middle
fragment using the common limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def HasShortCollarJoining (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (C T : Set X) : Prop :=
  ∀z ∈ C, ∀ε : ℝ≥0∞, 0 < ε → ∃U : Set X, U ∈ 𝓝 z ∧
    ∀a ∈ U ∩ C, ∀b ∈ U ∩ C, ∃ρ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧ ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧
        range ρ.1.val ⊆ T ∧ physicalTollCost d g m ρ.1 ≤ ε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite chains grouped into true-path blocks separated by
old jumps. The finite code records old disk labels and new-jump counts. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

structure IsJumpBlockCode (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) : Prop where
  allowed : ∀b j, AllowedTaggedPath d ν N ((Z.paths b j).1.val, (Z.paths b j).2)
  start : ∀b, (Z.paths b 0).1.val ⊥ ∈ blockAnchors F H O P b.castSucc ∩ d.quotientDomain
  finish : ∀b, (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
    blockAnchors F H O P b.succ ∩ d.quotientDomain
  left : ∀b i, (Z.paths b i.castSucc).1.val ⊤ ∈ Z.disks b i
  right : ∀b i, (Z.paths b i.succ).1.val ⊥ ∈ Z.disks b i
  meets : ∀b i, (Z.disks b i ∩ B).Nonempty

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedFusionSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sigma-ideal of path-law candidates failing a prescribed countable/atomless
test. A finite atomless measure dominating any countable list of such tests is
constructed from the existing finite-measure representative of an s-finite measure. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  (ι : C(X, Y))

theorem PassesHitTests.mono {C : ℝ} {μ : ProbabilityMeasure C(PathTime, Y)}
    {D E : Set X} {ν ρ : Measure X} (h : PassesHitTests ι C μ D ν)
    (hED : E ⊆ D) (hρν : ρ ≪ ν) : PassesHitTests ι C μ E ρ := by
  refine ⟨fun F hF => h.1 F (hF.trans hED), ?_⟩
  apply (lintegral_eq_zero_iff (measurable_pathHitProbability_point ι μ)).mpr
  exact hρν.ae_le ((lintegral_eq_zero_iff (measurable_pathHitProbability_point ι μ)).mp h.2)

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
theorem HitTestSmall.mono {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A B : Set Z} (hB : HitTestSmall ι law C B) (hAB : A ⊆ B) : HitTestSmall ι law C A := by
  obtain ⟨D, hD, ν, hν, hnull, hfail⟩ := hB
  exact ⟨D, hD, ν, hν, hnull, fun z hz => hfail z (hAB hz)⟩

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
theorem hitTestSmall_empty (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ) :
    HitTestSmall ι law C ∅ :=
  ⟨∅, countable_empty, 0, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ⟨by simp⟩, by simp⟩

theorem hitTestSmall_iUnion {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A : ℕ → Set Z} (hA : ∀ n, HitTestSmall ι law C (A n)) :
    HitTestSmall ι law C (⋃ n, A n) := by
  classical
  choose D hD ν hν hnull hfail using hA
  let (n : ℕ) : IsFiniteMeasure (ν n) := hν n
  let (n : ℕ) : NullSingletonClass (ν n) := hnull n
  obtain ⟨ρ, hρ, hnullρ, hdom⟩ := exists_finite_atomless_dominating ν
  refine ⟨⋃ n, D n, countable_iUnion hD, ρ, hρ, hnullρ, ?_⟩
  intro z hz hpass
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  exact hfail n z hn (PassesHitTests.mono ι hpass (subset_iUnion D n) (hdom n))

theorem HitTestSmall.union {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    {A B : Set Z} (hA : HitTestSmall ι law C A) (hB : HitTestSmall ι law C B) :
    HitTestSmall ι law C (A ∪ B) := by
  classical
  have h := hitTestSmall_iUnion ι (A := fun n : ℕ => if n = 0 then A else B)
    (fun n => by split <;> assumption)
  apply HitTestSmall.mono ι h
  intro z hz
  rcases hz with hz | hz
  · exact mem_iUnion.mpr ⟨0, by simpa using hz⟩
  · exact mem_iUnion.mpr ⟨1, by simpa using hz⟩

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedFusionKernel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing all basis neighborhoods whose intersection with a closed candidate
set is test-small leaves a closed nonsmall kernel. Every neighborhood of every
remaining point meets the kernel nonsmally, as needed by the finite fusion split. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
  [TopologicalSpace Z] [SecondCountableTopology Z]

omit [SecondCountableTopology X] in
theorem exists_closed_hit_test_kernel
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ)
    {A : Set Z} (hA : IsClosed A) (hAn : ¬HitTestSmall ι law C A) :
    ∃ K : Set Z, K ⊆ A ∧ IsClosed K ∧ ¬HitTestSmall ι law C K ∧
      K.Nonempty ∧ ∀ z ∈ K, ∀ V : Set Z, IsOpen V → z ∈ V →
        ¬HitTestSmall ι law C (K ∩ V) := by
  classical
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis Z
  let V : ℕ → Set Z := fun n => if HitTestSmall ι law C (A ∩ B n) then B n else ∅
  let U : Set Z := ⋃ n, V n
  let K : Set Z := A \ U
  have hVo (n : ℕ) : IsOpen (V n) := by
    dsimp only [V]
    split
    · exact hB.isOpen (mem_range_self n)
    · exact isOpen_empty
  have hUo : IsOpen U := isOpen_iUnion hVo
  have hdel : HitTestSmall ι law C (A ∩ U) := by
    rw [show A ∩ U = ⋃ n, A ∩ V n from inter_iUnion A V]
    apply hitTestSmall_iUnion ι
    intro n
    dsimp only [V]
    split
    · assumption
    · simpa using hitTestSmall_empty ι law C
  have hKsub : K ⊆ A := sdiff_subset
  have hKn : ¬HitTestSmall ι law C K := by
    intro hK
    apply hAn
    apply HitTestSmall.mono ι (HitTestSmall.union ι hK hdel)
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inr ⟨hz, hzU⟩
    · exact Or.inl ⟨hz, hzU⟩
  have hKne : K.Nonempty := by
    by_contra h
    exact hKn ((not_nonempty_iff_eq_empty.mp h).symm ▸ hitTestSmall_empty ι law C)
  refine ⟨K, hKsub, hA.sdiff hUo, hKn, hKne, ?_⟩
  intro z hz W hWo hzW hsmall
  have hAW : HitTestSmall ι law C (A ∩ W) := by
    apply HitTestSmall.mono ι (HitTestSmall.union ι hsmall hdel)
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inr ⟨hy.1, hyU⟩
    · exact Or.inl ⟨⟨hy.1, hyU⟩, hy.2⟩
  obtain ⟨B', hB', hzB', hB'W⟩ := hB.exists_subset_of_mem_open hzW hWo
  obtain ⟨n, rfl⟩ := hB'
  have hn : HitTestSmall ι law C (A ∩ B n) :=
    HitTestSmall.mono ι hAW (inter_subset_inter_right _ hB'W)
  apply hz.2
  exact mem_iUnion.mpr ⟨n, by simpa only [V, ite_eq_left hn] using hzB'⟩

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedAtomicHitTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable and atomless tests control integration against any finite measure
whose point masses have square norm at most one. This supplies the test-measure
step in finite law splitting; the atomless remainder is the restriction away
from the actual positive point masses. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  (ι : C(X, Y))

omit [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, Y)] in
theorem PassesHitTests.lintegral_le_of_atomic_square_bound
    {ν : Measure X} [IsFiniteMeasure ν] {μ : ProbabilityMeasure C(PathTime, Y)}
    {C : ℝ} (hC : 0 ≤ C) (hν : HasAtomicSquareBound ν)
    (htest : PassesHitTests ι C μ (positiveAtoms ν) (ν.restrict (positiveAtoms ν)ᶜ)) :
    ∫⁻ x, pathHitProbability ι μ x ∂ν ≤ ENNReal.ofReal C := by
  classical
  let D := positiveAtoms ν
  have hD : D.Countable := countable_positiveAtoms ν
  rw [← lintegral_add_compl _ hD.measurableSet, htest.2, add_zero,
    lintegral_countable _ hD, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  have hF : (↑(F.image (fun x : D => (x : X))) : Set X) ⊆ D := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have heq (a : X → ℝ) :
      ∑ x ∈ F.image (fun x : D => (x : X)), a x = ∑ x ∈ F, a x.val :=
    Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)
  have hp : (∑ x ∈ F, pathHitReal ι μ x.val ^ 2) ≤ C ^ 2 := by
    simpa only [heq] using htest.1 _ hF
  have ha : (∑ x ∈ F, (ν {x.val}).toReal ^ 2) ≤ 1 := by
    simpa only [heq] using hν (F.image (fun x : D => (x : X)))
  have hpr : Real.sqrt (∑ x ∈ F, pathHitReal ι μ x.val ^ 2) ≤ C :=
    Real.sqrt_le_iff.mpr ⟨hC, hp⟩
  have har : Real.sqrt (∑ x ∈ F, (ν {x.val}).toReal ^ 2) ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using ha⟩
  have hsum : (∑ x ∈ F, pathHitReal ι μ x.val * (ν {x.val}).toReal) ≤ C := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt F
      (fun x : D => pathHitReal ι μ x.val) (fun x : D => (ν {x.val}).toReal)
    exact hcs.trans ((mul_le_mul hpr har (Real.sqrt_nonneg _) hC).trans_eq (mul_one C))
  calc
    ∑ x ∈ F, pathHitProbability ι μ x.val * ν {x.val} =
        ENNReal.ofReal (∑ x ∈ F, pathHitReal ι μ x.val * (ν {x.val}).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
        mul_nonneg (pathHitReal_nonneg ι _ _) ENNReal.toReal_nonneg)]
      apply Finset.sum_congr rfl
      intro x _
      rw [ENNReal.ofReal_mul (pathHitReal_nonneg ι _ _)]
      rw [pathHitReal, ENNReal.ofReal_toReal (ne_of_lt
        (lt_of_le_of_lt (pathHitProbability_le_one ι _ _) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hsum

theorem exists_test_law_for_atomic_measure
    {Z : Type*} (law : Z → ProbabilityMeasure C(PathTime, Y))
    {A : Set Z} {C : ℝ} (hC : 0 ≤ C) (hA : ¬HitTestSmall ι law C A)
    (ν : Measure X) [IsFiniteMeasure ν] (hν : HasAtomicSquareBound ν) :
    ∃ z ∈ A, ∫ x, pathHitReal ι (law z) x ∂ν ≤ C := by
  classical
  have hnull := nullSingleton_restrict_compl_positiveAtoms ν
  obtain ⟨z, hz, htest⟩ : ∃ z ∈ A,
      PassesHitTests ι C (law z) (positiveAtoms ν) (ν.restrict (positiveAtoms ν)ᶜ) := by
    by_contra h
    apply hA
    refine ⟨positiveAtoms ν, countable_positiveAtoms ν,
      ν.restrict (positiveAtoms ν)ᶜ, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), hnull, ?_⟩
    intro z hz hpass
    exact h ⟨z, hz, hpass⟩
  have hi := PassesHitTests.lintegral_le_of_atomic_square_bound ι hC hν htest
  have he := integral_toReal (μ := ν) (measurable_pathHitProbability_point ι (law z)).aemeasurable
    (Eventually.of_forall fun x => lt_of_le_of_lt
      (pathHitProbability_le_one ι (law z) x) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨z, hz, ?_⟩
  change (∫ x, (pathHitProbability ι (law z) x).toReal ∂ν) ≤ C
  rw [he]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hi

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MarkedConfigurationIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hit integrals against the actual mean configuration measure are precisely
the expected weighted hit counts. This identifies the two sides of the finite
split without replacing the configuration measure by abstract test data. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  {n : ℕ} {r : ℝ} (ι : C(X, Y))

theorem integral_meanConfigurationMeasure_hit
    (P : ProbabilityMeasure (HitConfiguration X n r)) (μ : ProbabilityMeasure C(PathTime, Y)) :
    ∫ x, pathHitReal ι μ x ∂meanConfigurationMeasure P =
      ∫ p, ∑ i, (p.val.2 i : ℝ) * pathHitReal ι μ (p.val.1 i)
        ∂(P : Measure (HitConfiguration X n r)) := by
  let v : HitConfiguration X n r → ℝ := fun p =>
    ∑ i, (p.val.2 i : ℝ) * pathHitReal ι μ (p.val.1 i)
  have hv0 (p : HitConfiguration X n r) : 0 ≤ v p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _)
  have hvm : Measurable v := by
    apply Finset.measurable_sum
    intro i _
    exact (by fun_prop : Continuous (fun p : HitConfiguration X n r => (p.val.2 i : ℝ))).measurable.mul
      (((measurable_pathHitProbability_point ι μ).comp
        (by fun_prop : Continuous (fun p : HitConfiguration X n r => p.val.1 i)).measurable).ennreal_toReal)
  have hpoint (p : HitConfiguration X n r) :
      (∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * pathHitProbability ι μ (p.val.1 i)) =
        ENNReal.ofReal (v p) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (p.val.2 i).property.1, pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one ι _ _) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))]
  calc
    ∫ x, pathHitReal ι μ x ∂meanConfigurationMeasure P =
        (∫⁻ x, pathHitProbability ι μ x ∂meanConfigurationMeasure P).toReal :=
      integral_toReal (measurable_pathHitProbability_point ι μ).aemeasurable
        (Eventually.of_forall fun x => lt_of_le_of_lt (pathHitProbability_le_one ι _ _) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    _ = (∫⁻ p, ENNReal.ofReal (v p) ∂(P : Measure (HitConfiguration X n r))).toReal := by
      rw [lintegral_meanConfigurationMeasure P (measurable_pathHitProbability_point ι μ)]
      simp_rw [hpoint]
    _ = ∫ p, v p ∂(P : Measure (HitConfiguration X n r)) := by
      have he := integral_toReal (μ := (P : Measure (HitConfiguration X n r)))
        hvm.ennreal_ofReal.aemeasurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
      simpa only [ENNReal.toReal_ofReal (hv0 _)] using he.symm

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedFiniteHitSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite split for separated hit configurations. Nonsmallness supplies
a candidate against the mean configuration measure; its atomic norm bound
and the hit-integral identity give the compact-law split. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

theorem exists_finite_hit_configuration_split
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
    [TopologicalSpace Z] (law : Z → ProbabilityMeasure C(PathTime, Y))
    (hlaw : Continuous law) {A : Set Z} {C ε r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hr : 0 < r) (n : ℕ) [Nonempty (HitConfiguration X n r)]
    (hA : ¬HitTestSmall ι law C A) :
    ∃ (k : ℕ) (z : Fin k → Z) (w : Fin k → ℝ),
      (∀ i, z i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ p : HitConfiguration X n r, ∑ i, w i * weightedConfigurationHits ι law (z i) p ≤ C + ε := by
  have hfixed (z : Z) : UpperSemicontinuous (weightedConfigurationHits ι law z : HitConfiguration X n r → ℝ) :=
    (weightedConfigurationHits_upperSemicontinuous ι hlaw n r).comp
      (continuous_const.prodMk continuous_id)
  apply exists_finite_compact_law_split (fun z p => weightedConfigurationHits ι law z p) A
    (fun z _ => hfixed z) (fun z _ p => weightedConfigurationHits_nonneg ι law z p)
    (M := (n : ℝ) + 1) (by positivity)
    (fun z _ p => (weightedConfigurationHits_le_card ι law z p).trans (by linarith)) hε
  intro P
  obtain ⟨z, hz, hb⟩ := exists_test_law_for_atomic_measure ι law hC hA
    (meanConfigurationMeasure P) (meanConfigurationMeasure_hasAtomicSquareBound hr P)
  refine ⟨z, hz, ?_⟩
  rwa [integral_meanConfigurationMeasure_hit ι P (law z)] at hb

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MarkedClosedHitSplit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite fusion split with closed nonsmall children. The weighted estimate
holds for every simultaneous choice from the children; their diameters can be
prescribed arbitrarily small. -/

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

theorem exists_closed_nonsmall_hit_split
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
    [MetricSpace Z] [SecondCountableTopology Z]
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (hlaw : Continuous law)
    {A : Set Z} (hAclosed : IsClosed A) {C ε η r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (n : ℕ) [Nonempty (HitConfiguration X n r)] (hA : ¬HitTestSmall ι law C A) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (D : Fin k → Set Z),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, IsClosed (D i) ∧ D i ⊆ A ∧ ¬HitTestSmall ι law C (D i) ∧
        ∀ x ∈ D i, ∀ y ∈ D i, dist x y ≤ η) ∧
      ∀ z : Fin k → Z, (∀ i, z i ∈ D i) →
        ∀ p : HitConfiguration X n r,
          ∑ i, w i * weightedConfigurationHits ι law (z i) p < C + ε := by
  obtain ⟨K, hKA, hKclosed, hKn, _, hKlocal⟩ :=
    exists_closed_hit_test_kernel ι law C hAclosed hA
  obtain ⟨k, z, w, hzK, hw, hw1, hbound⟩ :=
    exists_finite_hit_configuration_split ι law hlaw hC (by positivity : 0 < ε / 2) hr n hKn
  let F : (Fin k → Z) × HitConfiguration X n r → ℝ := fun q =>
    ∑ i, w i * weightedConfigurationHits ι law (q.1 i) q.2
  have hF : UpperSemicontinuous F := by
    apply upperSemicontinuous_sum
    intro i _
    have hc : Continuous (fun q : (Fin k → Z) × HitConfiguration X n r =>
        (q.1 i, q.2)) :=
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
    have hi := (weightedConfigurationHits_upperSemicontinuous ι hlaw n r).comp hc
    exact upperSemicontinuous_nonnegative_mul upperSemicontinuous_const hi
      (fun _ => hw i) (fun _ => weightedConfigurationHits_nonneg ι law _ _)
  have hU : IsOpen {y : Fin k → Z | ∀ p, F (y, p) < C + ε} :=
    isOpen_forall_compact_upper_bound hF (C + ε)
  have hzU : z ∈ {y : Fin k → Z | ∀ p, F (y, p) < C + ε} := by
    intro p
    exact lt_of_le_of_lt (hbound p) (by linarith)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hzU
  let δ := min (ρ / 2) (η / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let D : Fin k → Set Z := fun i => K ∩ closedBall (z i) δ
  refine ⟨k, w, D, hw, hw1, ?_, ?_⟩
  · intro i
    refine ⟨hKclosed.inter isClosed_closedBall, inter_subset_left.trans hKA, ?_, ?_⟩
    · intro hs
      apply hKlocal (z i) (hzK i) (ball (z i) δ) isOpen_ball (mem_ball_self hδ)
      exact HitTestSmall.mono ι hs (inter_subset_inter_right K ball_subset_closedBall)
    · intro x hx y hy
      have hxδ := mem_closedBall.mp hx.2
      have hyδ := mem_closedBall.mp hy.2
      have hdη : δ ≤ η / 2 := min_le_right _ _
      have ht := dist_triangle x (z i) y
      rw [dist_comm (z i) y] at ht
      linarith
  · intro y hy p
    have hdist : dist y z ≤ δ := (dist_pi_le_iff hδ.le).mpr fun i => mem_closedBall.mp (hy i).2
    have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ)
    exact hρU (mem_ball.mpr (hdist.trans_lt hδρ)) p

/-- Empty configuration spaces impose no test, but still admit a small closed child. -/
theorem exists_closed_nonsmall_hit_split_all
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
    [MetricSpace Z] [SecondCountableTopology Z]
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (hlaw : Continuous law)
    {A : Set Z} (hAclosed : IsClosed A) {C ε η r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (n : ℕ) (hA : ¬HitTestSmall ι law C A) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (D : Fin k → Set Z),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, IsClosed (D i) ∧ D i ⊆ A ∧ ¬HitTestSmall ι law C (D i) ∧
        ∀ x ∈ D i, ∀ y ∈ D i, dist x y ≤ η) ∧
      ∀ z : Fin k → Z, (∀ i, z i ∈ D i) →
        ∀ p : HitConfiguration X n r,
          ∑ i, w i * weightedConfigurationHits ι law (z i) p < C + ε := by
  classical
  cases isEmpty_or_nonempty (HitConfiguration X n r) with
  | inr hn => exact exists_closed_nonsmall_hit_split ι law hlaw hAclosed hC hε hη hr n hA
  | inl hn =>
    obtain ⟨K, hKA, hKclosed, _, ⟨z, hz⟩, hKlocal⟩ :=
      exists_closed_hit_test_kernel ι law C hAclosed hA
    let D := K ∩ closedBall z (η / 2)
    have hD : ¬HitTestSmall ι law C D := by
      intro hs
      apply hKlocal z hz (ball z (η / 2)) isOpen_ball (mem_ball_self (by positivity))
      exact HitTestSmall.mono ι hs (inter_subset_inter_right K ball_subset_closedBall)
    refine ⟨1, fun _ => 1, fun _ => D, by simp, by simp, ?_, ?_⟩
    · intro i
      refine ⟨hKclosed.inter isClosed_closedBall, inter_subset_left.trans hKA, hD, ?_⟩
      intro x hx y hy
      have hx' := mem_closedBall.mp hx.2
      have hy' := mem_closedBall.mp hy.2
      have ht := dist_triangle x z y
      rw [dist_comm z y] at ht
      linarith
    · intro y hy p
      exact isEmptyElim p

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionTree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nested tree of nonsmall closed candidates. Every vertex carries
its finite probability split, and every infinite address has a continuous limit
inside every ancestor. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
  [MetricSpace Z] [SecondCountableTopology Z]
  (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ)

namespace ClosedHitCandidate

variable {ι law C}

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem nonempty (A : ClosedHitCandidate ι law C) : A.carrier.Nonempty := by
  by_contra h
  exact A.nonsmall ((not_nonempty_iff_eq_empty.mp h).symm ▸ hitTestSmall_empty ι law C)

end ClosedHitCandidate

variable {law C}

theorem nonempty_hitFusionSplit [CompactSpace X]
    (hlaw : Continuous law) (hC : 0 ≤ C) (A : ClosedHitCandidate ι law C)
    (n : ℕ) {r ε η : ℝ} (hr : 0 < r) (hε : 0 < ε) (hη : 0 < η) :
    Nonempty (HitFusionSplit ι law C A n r ε η) := by
  obtain ⟨k, w, D, hw, hw1, hD, hb⟩ := exists_closed_nonsmall_hit_split_all ι law hlaw
    A.closed hC hε hη hr n A.nonsmall
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    simp at hw1
  exact ⟨⟨k, hk, w, hw, hw1, fun i => ⟨D i, (hD i).1, (hD i).2.2.1⟩,
    fun i => (hD i).2.1, fun i => (hD i).2.2.2, hb⟩⟩

variable (ns : ℕ → ℕ) (rs : ℕ → ℝ) (ε : ℝ)
  (split : ∀ d (A : ClosedHitCandidate ι law C),
    HitFusionSplit ι law C A (ns d) (rs d) ε (1 / ((d : ℝ) + 1)))
  (root : ClosedHitCandidate ι law C)

def hitFusionScheme : ClosedFusionScheme Z where
  carrier l := (hitFusionNode ι ns rs ε split root l).carrier
  closed l := (hitFusionNode ι ns rs ε split root l).closed
  nonempty l := (hitFusionNode ι ns rs ε split root l).nonempty
  child_subset l _a := (split l.length (hitFusionNode ι ns rs ε split root l)).child_subset _
  child_dist l _a := (split l.length (hitFusionNode ι ns rs ε split root l)).child_dist _

namespace HitFusionData

variable {ι}

variable (T : HitFusionData (ι := ι) (law := law) (C := C))

def scheme : ClosedFusionScheme Z :=
  hitFusionScheme ι T.sizes T.separations T.error T.split T.initial

end HitFusionData

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionCaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform upper bounds on a closed child control every continuation of a
fusion branch. The weighted sum of these bounds is the original split bound. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity.MarkedHit
namespace HitFusionSplit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] {ι : C(X, Y)}
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
  {A : ClosedHitCandidate ι law C} {n : ℕ} {r ε η : ℝ}
  (S : HitFusionSplit ι law C A n r ε η)

def hitCap (a : ℕ) (p : HitConfiguration X n r) : ℝ :=
  sSup ((fun z => weightedConfigurationHits ι law z p) '' (S.child (S.index a)).carrier)

end HitFusionSplit
end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The law on the nested tree and its continuous limiting mixture. Every
scheduled configuration bound survives all subsequent refinements. -/

open Set Filter MeasureTheory ProbabilityTheory Preorder
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit
namespace HitFusionData

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] {ι : C(X, Y)}
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
  (T : HitFusionData (ι := ι) (law := law) (C := C))

def step (l : List ℕ) : ProbabilityMeasure ℕ :=
  finiteChoiceLaw (T.splitAt l).count (T.splitAt l).weight (T.splitAt l).weight_nonneg (T.splitAt l).weight_sum

def childCap {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ) (p : HitConfiguration X n r) : ℝ :=
  sSup ((fun z => weightedConfigurationHits ι law z p) '' (T.node (a :: l)).carrier)

variable [CompleteSpace Z]

def endpoint (x : ℕ → ℕ) : Z := T.scheme.limit (FusionTrajectory.branch x)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem continuous_endpoint : Continuous T.endpoint :=
  T.scheme.continuous_limit.comp (by unfold FusionTrajectory.branch; fun_prop)

def addressLaw : ProbabilityMeasure (ℕ → ℕ) :=
  ⟨FusionTrajectory.measure T.step, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end HitFusionData
end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fusion of a nonsmall closed family of path laws into a law with finite
point-hit square norm. All finite splitting and branch laws are constructed. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
  [MetricSpace Z] [SecondCountableTopology Z] [CompleteSpace Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}

namespace HitFusionData

variable {ι}

variable (T : HitFusionData (ι := ι) (law := law) (C := C)) (hlaw : Continuous law)

def fusedLaw : ProbabilityMeasure C(PathTime, Y) :=
  probabilityMixture T.addressLaw (law ∘ T.endpoint) (measurable_of_continuous_probability (hlaw.comp T.continuous_endpoint))

end HitFusionData


def standardHitFusion (hlaw : Continuous law) (hC : 0 ≤ C)
    (root : ClosedHitCandidate ι law C) (ε : ℝ) (hε : 0 < ε) :
    HitFusionData (ι := ι) (law := law) (C := C) where
  sizes d := (Nat.unpair d).1
  separations d := 1 / (((Nat.unpair d).2 : ℝ) + 1)
  error := ε
  initial := root
  split d A := Classical.choice (nonempty_hitFusionSplit ι hlaw hC A (Nat.unpair d).1
    (by positivity) hε (by positivity))

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealTargetEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full corresponding target ends and their collapse by actual source tests. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem plane_inside (n : ℕ) : E.plane ⊆ jordanInterior (L.contours n (E.address n)) := by
  intro z hz
  have hc : (z : Sphere) ∈ ⋂ j, closedTerminalCap (L.contours j (E.address j)) := E.target ▸ hz
  exact OnePoint.coe_injective.mem_set_image.mp
    (E.nested n (mem_iInter.mp hc (n + 1)))

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactImageRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact subsets of an embedded source disk's limiting image remain in the actual images
under locally uniform convergence of the finite open embeddings. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_compact_subset_image_jordan_disk
    (hsch : PlanarSchoenflies)
    {G : Set ℂ} (hG : IsOpen G) {f : ℂ → ℂ} (hf : ContinuousOn f G)
    (hfo : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hfi : InjOn f G)
    (Gn : ℕ → Set ℂ) (hGn : ∀ n, IsOpen (Gn n)) (fn : ℕ → ℂ → ℂ)
    (hfn : ∀ n, ContinuousOn (fn n) (Gn n))
    (hfno : ∀ n S, IsOpen S → S ⊆ Gn n → IsOpen (fn n '' S))
    (hfni : ∀ n, InjOn (fn n) (Gn n))
    (hlim : TendstoLocallyUniformlyOn fn f atTop G)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ G)
    (hretain : ∀ᶠ n in atTop, closure (jordanInterior H) ⊆ Gn n)
    {K : Set ℂ} (hK : IsCompact K) (hKf : K ⊆ f '' jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆ fn n '' jordanInterior H := by
  classical
  obtain ⟨J, hJ, _, hJfront⟩ := exists_jordan_image_disk hsch hG hf hfo hfi H hHG
  have hex (n : ℕ) : ∃ Jn : ℂ ≃ₜ ℂ, closure (jordanInterior H) ⊆ Gn n →
      fn n '' jordanInterior H = jordanInterior Jn ∧
      frontier (jordanInterior Jn) = fn n '' frontier (jordanInterior H) := by
    by_cases hn : closure (jordanInterior H) ⊆ Gn n
    · obtain ⟨Jn, hJn, _, hJnf⟩ :=
        exists_jordan_image_disk hsch (hGn n) (hfn n) (hfno n) (hfni n) H hn
      exact ⟨Jn, fun _ => ⟨hJn, hJnf⟩⟩
    · exact ⟨J, fun h => (hn h).elim⟩
  choose Jn hJn using hex
  let γ : Circle → ℂ := fun t => f (H t)
  let γn : ℕ → Circle → ℂ := fun n t => fn n (H t)
  have hcircle (t : Circle) : H (t : ℂ) ∈ G := by
    apply hHG
    rw [closure_jordanInterior]
    exact ⟨t, by simpa using (Circle.norm_coe t).le, rfl⟩
  have hcurve : Continuous (fun t : Circle => H (t : ℂ)) :=
    H.continuous.comp continuous_subtype_val
  have hγ : Continuous γ := hf.comp_continuous hcurve hcircle
  have hrange : range (fun t : Circle => H (t : ℂ)) = frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hγfront : range γ = frontier (jordanInterior J) := by
    rw [hJfront, ← hrange, ← range_comp]
    rfl
  have hγnfront : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Jn n)) := by
    filter_upwards [hretain] with n hn
    rw [(hJn n hn).2, ← hrange, ← range_comp]
    rfl
  have hγlim : TendstoUniformly γn γ atTop := by
    apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp (fun t : Circle => H (t : ℂ)) (fun t _ => hcircle t) hcurve.continuousOn
  have hxH : H 0 ∈ jordanInterior H := ⟨0, by simp, rfl⟩
  have hxG := hHG (subset_closure hxH)
  have hxJ : f (H 0) ∈ jordanInterior J := hJ ▸ mem_image_of_mem f hxH
  have hxJn : ∀ᶠ n in atTop, fn n (H 0) ∈ jordanInterior (Jn n) := by
    filter_upwards [hretain] with n hn
    rw [← (hJn n hn).1]
    exact mem_image_of_mem _ hxH
  have hp := eventually_compact_subset_jordanInterior_of_anchor J Jn γ γn
    hγ hγfront hγnfront hγlim hxJ (hlim.tendsto_at hxG) hxJn hK (hJ ▸ hKf)
  filter_upwards [hp, hretain] with n hn hr
  rwa [← (hJn n hr).1] at hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealAnchorRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source anchor's fixed zero plateau is retained on a compact target anchor in the actual
finite models. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem eventually_compact_subset_anchor_image
    (hsch : PlanarSchoenflies) (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    {K : Set ℂ} (hK : IsCompact K) (hKA : K ⊆ A.function '' jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆
      (fun z : ℂ => finiteCoord ((M.stages (A.subsequence n)).forward z)) '' jordanInterior H := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hF := A.plane_open_embedding hG
  let Gn (n : ℕ) : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
    openCompletedRegion (M.stages (A.subsequence n)).terminals.H
  have hdata (n : ℕ) := (M.stages (A.subsequence n)).equivalence.finite_open_embedding
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
    (M.stages (A.subsequence n)).circle_domain.1
  apply eventually_compact_subset_image_jordan_disk hsch (hG.preimage OnePoint.continuous_coe)
    hF.1 hF.2.1 hF.2.2 Gn
    (fun n => (isOpen_openCompletedRegion (M.stages (A.subsequence n)).terminals.H).preimage
      OnePoint.continuous_coe)
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).forward z))
    (fun n => (hdata n).1) (fun n => (hdata n).2.1) (fun n => (hdata n).2.2)
    A.converges H hHG ?_ hK hKA
  have hsourceG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  filter_upwards [A.strict.tendsto_atTop (M.eventually_model_contains
    ((isCompact_closure_jordanInterior H).image OnePoint.continuous_coe) hsourceG)] with n hn
  exact fun z hz => hn (mem_image_of_mem _ hz)

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionTestGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed source anchors, bounded target regions and positive transverse widths constructed
from a genuine protrusion of an assigned marked component. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure LocalEndTestGeometry {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere}
    {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    (E : RealTargetEnd A q) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  continuum : Set ℂ
  compact : IsCompact continuum
  in_component : continuum ⊆ E.plane
  in_region : continuum ⊆ closedBall center radius
  sourceAnchor : ℂ ≃ₜ ℂ
  source_inside : closure (jordanInterior sourceAnchor) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G
  anchorCenter : ℂ
  anchorRadius : ℝ
  anchorRadius_pos : 0 < anchorRadius
  anchor_image : closedBall anchorCenter anchorRadius ⊆ A.function '' jordanInterior sourceAnchor
  anchor_region : closedBall anchorCenter anchorRadius ⊆ closedBall center radius
  direction : Circle
  lower : ℝ
  upper : ℝ
  width_pos : lower < upper
  projection : Icc lower upper ⊆
    (fun z => ((rotation direction).symm z).im) '' continuum ∩
      Ioo (((rotation direction).symm anchorCenter).im - anchorRadius)
        (((rotation direction).symm anchorCenter).im + anchorRadius)

namespace LocalEndTestGeometry

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

def boundRadius : ℝ := max (3 * M.radius) (T.radius + ‖T.center‖)

end LocalEndTestGeometry

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SlackRealExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strictly larger comparison radius gives an open radius interval in
the countable selection space while retaining the same real barrier test. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 def selectionRadius : ℝ := T.boundRadius + 1

 def selectionThreshold : ℝ := (T.upper - T.lower) /
   ((Real.sqrt Real.pi + 2) * T.selectionRadius)

end CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealExclusionWitness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real barrier test retains its actual presentation, band weight,
open map neighborhood, and the proved radius-dependent exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure RealExclusionWitness (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) where
  presentation : RealCoordinatePresentation base π C
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑' x, weight x ^ 2) < ∞
  band_bound : ∀ x ∈ base.dust, ENNReal.ofReal
    (limsup presentation.coordinate.quotient (𝓝[base.quotientDomain] x) -
      liminf presentation.coordinate.quotient (𝓝[base.quotientDomain] x)) ≤ weight x
  radius : ℝ
  neighborhood : Set C(FiniteSource base.physicalDomain, ℂ)
  isOpen_neighborhood : IsOpen neighborhood
  excludes : ∀ {S : Type} {π' : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates base.physicalDomain π' σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε) (A : AssignedRealModelLimit M) (l : ℕ)
    (hG : IsOpen base.physicalDomain),
    Tendsto ε atTop (𝓝 0) → 3 * M.radius ≤ radius →
    d.physical l = presentation.coordinate.physical →
    Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) ≤ (countingSquareNorm weight).toReal →
    finiteSourceMap A.function (A.plane_open_embedding hG).1 ∉ neighborhood

namespace RealExclusionWitness
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}
  (W : RealExclusionWitness base π C)

 def sizedNeighborhood : Set (MapDiskData base.physicalDomain × ℝ) :=
    (W.neighborhood ×ˢ univ) ×ˢ Iio (W.radius / 3)

end RealExclusionWitness

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionWitness
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constructed mean test retains its actual source curve, mask containment,
singular fiber containment, and the open neighborhood it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure MeanExclusionWitness {T : Type*} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : T → Sphere} (N : MaskedCoordinateData G U π σ)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ) where
  disk : ℂ ≃ₜ ℂ
  curve : ℝ → ℂ
  regular : PositiveJordanParametrization disk curve
  boundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior disk) ⊆ G
  mask : realChartDomain (closedTerminalCap disk) ⊆ interior (physicalMask π N.mask)
  fiber : π ⁻¹' {σ N.singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior disk
  lift : ℝ → ℝ
  smooth_lift : ContDiff ℝ (⊤ : ℕ∞) lift
  projects : ∀ t, (lift t : UnitAddCircle) = N.physical (Complex.equivRealProdCLM (curve t))
  member : (finiteSourceMap F₀ hF₀, c, r) ∈ mapDiskExclusion
    (sourceCircuit curve regular.smooth.continuous
      (fun t => boundary (mem_image_of_mem _ (regular.mem_frontier t)))) lift (N.sourceStokesBudget R)

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def neighborhood : Set (MapDiskData G) := mapDiskExclusion
    (sourceCircuit W.curve W.regular.smooth.continuous
      (fun t => W.boundary (mem_image_of_mem _ (W.regular.mem_frontier t))))
    W.lift (N.sourceStokesBudget R)

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting to the common countable marks preserves a mean exclusion.
Its source budget can only decrease, so the original open neighborhood
remains excluded by a mixed limit retaining that coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def restrictMarks (A : Set T) (hsing : N.singular ∈ A)
    (hsupport : ∀ s, N.upper s - N.lower s ≠ 0 → s ∈ A) (hR : 0 ≤ R) :
    MeanExclusionWitness (N.restrictMarks A hsing hsupport) F₀ hF₀ c r R where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := (N.restrictMarks_sourceStokesBudget_le A hsing hsupport hR).trans_lt W.member

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionRadius
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed mean exclusion remains valid for every smaller target-radius
budget. This permits an open radius interval in the common selection space. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem FiniteTransfer.MaskedCoordinateData.sourceStokesBudget_mono
    {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (N : MaskedCoordinateData G U π σ) : Monotone N.sourceStokesBudget := by
  intro R R' hR
  unfold MaskedCoordinateData.sourceStokesBudget
  gcongr

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def smallerRadius {R' : ℝ} (hR : R' ≤ R) : MeanExclusionWitness N F₀ hF₀ c r R' where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := (N.sourceStokesBudget_mono hR).trans_lt W.member

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SizedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Record the exterior model radius in the same second countable test
space. An open radius interval retains the quantitative Stokes exclusion
under subsequent common-model selection. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def sizedNeighborhood (B : ℝ) : Set (MapDiskData G × ℝ) :=
  W.neighborhood ×ˢ Ioo B (R / 5)

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CoordinateExclusionTest
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and mean tests use one common map--disk--radius space. The mark
index is kept discrete, so each selected test retains the component it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure MeanExclusionTest (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (π : Sphere → Sphere)
    (C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (p : base.dust) (B : ℝ) where
  presentation : MeanCoordinatePresentation hsch base π C
  function : ℂ → ℂ
  continuousOn : ContinuousOn function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)
  center : ℂ
  radius : ℝ≥0
  budgetRadius : ℝ
  witness : MeanExclusionWitness C function continuousOn center radius budgetRadius
  singular : C.singular = p
  source_bound : ∀ z ∈ frontier (jordanInterior witness.disk), ‖z‖ ≤ 4 * B

local instance localInst_rc4c60f_2 : BorelSpace Sphere := ⟨rfl⟩
structure CoordinateExclusionTest (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (π : Sphere → Sphere) (B₀ : Set base.dust) (B : ℝ) where
  mark : B₀
  coordinate : SelectableMaskedCoordinate base π
  witness : Sum (RealExclusionWitness base π coordinate.coordinate)
    (MeanExclusionTest hsch base π coordinate.coordinate mark.val B)

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {π : Sphere → Sphere} {B₀ : Set base.dust} {B : ℝ}
  (T : CoordinateExclusionTest hsch base π B₀ B)

 def presentation : SelectedLevelPresentation hsch base π T.coordinate.coordinate :=
  T.witness.elim (fun W => Sum.inl W.presentation) (fun W => Sum.inr W.presentation)

 def neighborhood : Set (B₀ × (MapDiskData base.physicalDomain × ℝ)) :=
    {T.mark} ×ˢ T.witness.elim (fun W => W.sizedNeighborhood)
      (fun W => W.witness.sizedNeighborhood B)

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveReductionBase
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact recursive law in the original base presentation. The fallback
point and the equivalent restricted homeomorphism have no effect on physical costs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 def baseHitWeight (s : base.dust) : ℝ≥0∞ :=
    if s.val ≠ L.data.target then pathHitProbability (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) s.val else 0

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionCongruence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The open exclusion depends only on the source map on its domain.
A measurable extension outside that domain does not change the test. -/
open Set Function
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness

 def congr_map {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ F₁ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)}
    {hF₁ : ContinuousOn F₁ (((↑) : ℂ → Sphere) ⁻¹' G)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ} (W : MeanExclusionWitness N F₀ hF₀ c r R)
    (hEq : EqOn F₀ F₁ (((↑) : ℂ → Sphere) ⁻¹' G)) :
    MeanExclusionWitness N F₁ hF₁ c r R where
  disk := W.disk
  curve := W.curve
  regular := W.regular
  boundary := W.boundary
  mask := W.mask
  fiber := W.fiber
  lift := W.lift
  smooth_lift := W.smooth_lift
  projects := W.projects
  member := by
    have hmaps : finiteSourceMap F₀ hF₀ = finiteSourceMap F₁ hF₁ := by
      ext x
      exact hEq x.property
    rw [← hmaps]
    exact W.member

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionGateGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual protrusion balls give the two target gates and a uniform
positive distance from the marked disk. The normalized source map stays
outside that disk throughout its physical domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 def closedGate : Set Sphere := ((↑) : ℂ → Sphere) '' closedBall T.center T.radius
 def openGate : Set Sphere := ((↑) : ℂ → Sphere) '' ball T.center (2 * T.radius)

end LocalEndTestGeometry

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RebasedLevelPresentations
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a target or prior law changes the code space, but preserves the
actual selected coordinates and their real/mean presentations. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

namespace SmoothMeanPeriodData
variable (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ))
  (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
  {G U G' U' S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_25
def rebaseDomain (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (hG : G' = G) (hU : U' = U) :
    SmoothMeanPeriodData hsch K hKS η F G' U' S M b π := by
  subst G'; subst U'
  exact Q

 theorem graph_rebaseDomain (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (hG : G' = G) (hU : U' = U) :
    periodBandGraph U' M b (Q.rebaseDomain hsch K hKS η F hG hU).patch
      (Q.rebaseDomain hsch K hKS η F hG hU).branch =
      periodBandGraph U M b Q.patch Q.branch := by
  subst G'; subst U'
  rfl
end SmoothMeanPeriodData

variable [MeasurableSpace C(PathTime, Sphere)]
variable {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val)}

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_25
def RealCoordinatePresentation.rebase (R : RealCoordinatePresentation d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    RealCoordinatePresentation e π (C.rebaseDust hG hU hB) where
  coordinate := R.coordinate.rebase hG hU
  graph_eq := by
    rw [C.graph_rebaseDust]
    simpa only [PhysicalRealCoordinate.rebase, hU] using R.graph_eq
  mask_eq_univ := (C.mask_rebaseDust hG hU hB).trans R.mask_eq_univ
  physical_eq := by
    intro x
    rw [C.physical_rebaseDust]
    exact R.physical_eq x
  band_width := by
    intro s
    rw [C.width_rebaseDust]
    simpa only [PhysicalRealCoordinate.rebase, hU] using
      R.band_width ⟨s.val, hB ▸ s.property⟩
  compactSupport := R.compactSupport
  isCompact_support := R.isCompact_support
  zero_off := fun z hz hk => R.zero_off z (hG ▸ hz) hk
  zero_infty := fun hi => R.zero_infty (hG ▸ hi)

 def MeanCoordinatePresentation.rebase {hsch : PlanarSchoenflies}
    (R : MeanCoordinatePresentation hsch d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    MeanCoordinatePresentation hsch e π (C.rebaseDust hG hU hB) where
  arcs := R.arcs
  diskArcs := R.diskArcs
  compact_diskArcs := R.compact_diskArcs
  terminal_diskArcs := R.terminal_diskArcs
  law := R.law
  map := R.map
  arcMap := R.arcMap
  measurable_arcMap := R.measurable_arcMap
  arcMap_eq := R.arcMap_eq
  neighborhood := R.neighborhood
  mask := R.mask
  open_neighborhood := R.open_neighborhood
  closed_mask := R.closed_mask
  excludes_infty := R.excludes_infty
  boundary_domain := by simpa only [hU] using R.boundary_domain
  singular := R.singular
  singular_eq := (C.singular_rebaseDust hG hU hB).trans R.singular_eq
  singular_dust := hB.symm ▸ R.singular_dust
  singular_mask := R.singular_mask
  singular_outside := R.singular_outside
  punctured_mask := R.punctured_mask
  nonzero := R.nonzero
  unit_bound := R.unit_bound
  strict_bound := by simpa only [hU] using R.strict_bound
  injective_arcs := R.injective_arcs
  mean := R.mean.rebaseDomain hsch R.diskArcs R.terminal_diskArcs (R.law.map R.measurable_arcMap.aemeasurable)
    R.map hG hU
  graph_eq := by
    rw [C.graph_rebaseDust, SmoothMeanPeriodData.graph_rebaseDomain]
    exact R.graph_eq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReanchoredSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local endpoint anchor does not change a selected coordinate, its
presentation, flags, or compatibility. This permits the protrusion anchor
to be chosen after the preceding countable coordinate family. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 def reanchor (c : SelectableMaskedCoordinate d π) (E : Set Sphere) :
    SelectableMaskedCoordinate { d with anchor := E } π where
  coordinate := c.coordinate
  flags := c.flags
  flags_countable := c.flags_countable
  flags_dust := c.flags_dust
  weight_support := c.weight_support
  singular_marked := c.singular_marked
  domain_unique := c.domain_unique
  weighted := c.weighted

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReanchoredExclusions
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local endpoint anchor changes neither an exclusion neighborhood nor
its retained coordinate. Transport back to the original selection base. -/
open Set Function MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

 def RealExclusionWitness.reanchor (W : RealExclusionWitness base π C) (E : Set Sphere) :
    RealExclusionWitness {base with anchor := E} π C where
  presentation := W.presentation.rebase (e := {base with anchor := E}) rfl rfl rfl
  weight := W.weight
  weight_finite := W.weight_finite
  band_bound := W.band_bound
  radius := W.radius
  neighborhood := W.neighborhood
  isOpen_neighborhood := W.isOpen_neighborhood
  excludes := W.excludes

 def MeanExclusionTest.reanchor {hsch : PlanarSchoenflies} {p : base.dust} {B : ℝ}
    (W : MeanExclusionTest hsch base π C p B) (E : Set Sphere) :
    MeanExclusionTest hsch {base with anchor := E} π C p B where
  presentation := W.presentation.rebase (e := {base with anchor := E}) rfl rfl rfl
  function := W.function
  continuousOn := W.continuousOn
  center := W.center
  radius := W.radius
  budgetRadius := W.budgetRadius
  witness := W.witness
  singular := W.singular
  source_bound := W.source_bound

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {B₀ : Set base.dust} {B : ℝ}

def reanchor (T : CoordinateExclusionTest hsch base π B₀ B) (E : Set Sphere) :
    CoordinateExclusionTest hsch {base with anchor := E} π B₀ B where
  mark := T.mark
  coordinate := T.coordinate.reanchor E
  witness := T.witness.map (fun W => W.reanchor E) (fun W => W.reanchor E)

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RelevelledSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Installing the preceding selected level graphs in a path code leaves
coordinates, flags, physical weights, and compatibility unchanged. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 def withLevels (c : SelectableMaskedCoordinate d π) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    SelectableMaskedCoordinate { d with levels := H, levelWeights := w } π where
  coordinate := c.coordinate
  flags := c.flags
  flags_countable := c.flags_countable
  flags_dust := c.flags_dust
  weight_support := c.weight_support
  singular_marked := c.singular_marked
  domain_unique := c.domain_unique
  weighted := c.weighted

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RelevelledExclusions
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing the path code's level metadata changes neither a test's
physical coordinate nor its open exclusion. -/
open Set Function MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

 def RealExclusionWitness.withLevels (W : RealExclusionWitness base π C) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    RealExclusionWitness {base with levels := H, levelWeights := w} π C where
  presentation := W.presentation.rebase (e := {base with levels := H, levelWeights := w}) rfl rfl rfl
  weight := W.weight
  weight_finite := W.weight_finite
  band_bound := W.band_bound
  radius := W.radius
  neighborhood := W.neighborhood
  isOpen_neighborhood := W.isOpen_neighborhood
  excludes := W.excludes

 def MeanExclusionTest.withLevels {hsch : PlanarSchoenflies} {p : base.dust} {B : ℝ}
    (W : MeanExclusionTest hsch base π C p B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    MeanExclusionTest hsch {base with levels := H, levelWeights := w} π C p B where
  presentation := W.presentation.rebase (e := {base with levels := H, levelWeights := w}) rfl rfl rfl
  function := W.function
  continuousOn := W.continuousOn
  center := W.center
  radius := W.radius
  budgetRadius := W.budgetRadius
  witness := W.witness
  singular := W.singular
  source_bound := W.source_bound

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {B₀ : Set base.dust} {B : ℝ}

def withLevels (T : CoordinateExclusionTest hsch base π B₀ B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    CoordinateExclusionTest hsch {base with levels := H, levelWeights := w} π B₀ B where
  mark := T.mark
  coordinate := T.coordinate.withLevels H w
  witness := T.witness.map (fun W => W.withLevels H w) (fun W => W.withLevels H w)

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RoundOuterCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed round outer zero contour is an actual smooth source core. -/

open Set Function Filter Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem roundOuterJordan_interior (R : ℝ) (hR : 0 < R) :
    jordanInterior (roundOuterJordan R hR) = ball 0 R := by
  simpa only [roundOuterJordan, Homeomorph.refl_apply, id_eq, image_id'] using
    jordanInterior_dilated (Homeomorph.refl ℂ) hR

abbrev roundOuterCore {G : Set Sphere} (R : ℝ) (hR : 0 < R)
    (hRG : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) : SmoothJordanCore G where
  count := 1
  disk := fun _ => roundOuterJordan R hR
  curve := fun _ t => (R : ℂ) * (t : ℂ)
  disjoint := fun i j hij => (hij (Subsingleton.elim _ _)).elim
  subset_domain := by
    simpa only [closedJordanCore, roundOuterJordan_interior, iUnion_const] using hRG
  smooth := fun _ => by
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
    have hlin : ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ (fun z : ℂ => (R : ℂ) * z) :=
      (contDiff_const.mul contDiff_id).contMDiff
    exact hlin.comp contMDiff_coe_sphere
  embedding := fun _ =>
    (roundOuterJordan R hR).isEmbedding.comp (show Topology.IsEmbedding ((↑) : Circle → ℂ) from
      Topology.IsEmbedding.subtypeVal)
  boundary := fun _ => by
    rw [frontier_jordanInterior]
    change (roundOuterJordan R hR) '' sphere 0 1 = range (fun t : Circle => roundOuterJordan R hR t)
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩

namespace FiniteTransfer.RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem outer_region_subset_source :
    (((↑) : ℂ → Sphere) '' ball 0 (2 * M.radius))ᶜ ⊆ G :=
  (compl_subset_compl.mpr (image_mono (ball_subset_ball (by linarith [M.radius_pos])))).trans
    ((M.exterior_core 0).trans (M.core_source 0))

abbrev outerCore : SmoothJordanCore G :=
  roundOuterCore (2 * M.radius) (mul_pos (by norm_num) M.radius_pos) M.outer_region_subset_source

end FiniteTransfer.RealModelExhaustion

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConformalSphericalMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.chart_infty_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary conformality supplies the metric-conformality predicate for
the unchanged spherical background, including the infinity chart. -/
open Set Function Filter
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsConformalAt.isMetricConformalAt_of_scalar
    {f : Sphere → Sphere} {p : Sphere} (hf : IsConformalAt f p)
    {g : (ℝ × ℝ) → PlanarMetric} {c : ℝ} (hc : 0 < c)
    (hg : sphereChartMetric g p = c • (1 : PlanarMetric)) :
    IsMetricConformalAt g f p := by
  obtain ⟨hcont, a, ha, had⟩ := hf
  have hd := had.hasFDerivAt.restrictScalars ℝ
  change HasFDerivAt (sphereLocalMap f p) _ (chart p p) at hd
  have h1 : fderiv ℝ (sphereLocalMap f p) (chart p p) 1 = a := by
    rw [hd.fderiv]
    simp
  have hI : fderiv ℝ (sphereLocalMap f p) (chart p p) Complex.I = Complex.I * a := by
    rw [hd.fderiv]
    simp [smul_eq_mul]
  refine ⟨hcont, hd.differentiableAt, (a.re ^ 2 + a.im ^ 2) / c,
    div_pos (complex_column_norm_pos ha) hc, ?_, ?_, ?_, ?_⟩
  · rw [h1, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply]
    exact (div_mul_cancel₀ _ hc.ne').symm
  · rw [hI, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
    rw [div_mul_cancel₀ _ hc.ne']
    ring
  · rw [h1, hI, hg]
    norm_num [Matrix.smul_apply, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
    ring
  · rw [h1, hI]
    simpa only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add, neg_mul, sub_neg_eq_add, ← pow_two] using
      complex_column_norm_pos ha

 theorem IsConformalAt.isMetricConformalAt_spherical
    {f : Sphere → Sphere} {p : Sphere} (hf : IsConformalAt f p) :
    IsMetricConformalAt (fun z => sphericalMetricFactor z • 1) f p := by
  cases p using OnePoint.rec with
  | infty =>
    exact hf.isMetricConformalAt_of_scalar (by norm_num : (0 : ℝ) < 4)
      (by simp [sphereChartMetric])
  | coe z =>
    exact hf.isMetricConformalAt_of_scalar (sphericalMetricFactor_pos (Complex.equivRealProdCLM z))
      (by simp [sphereChartMetric, finiteCoord])

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededGradedRealSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graded selection retaining a prescribed family of real tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace GradedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

def AllowedWith (S : Set (UngatedRealTest d π EStar))
    (A : Set (GradedRealTest d π EStar)) (c : GradedRealTest d π EStar) : Prop :=
  c.toUngatedRealTest.CompatibleWith (S ∪ toUngatedRealTest '' A)

end GradedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedScalarEstimates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy and terminal oscillation estimates for the unchanged scalar tests
on the actual finite stages of the selected circle model. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_37
theorem FiniteTransfer.CountableRealCoordinates.width_zero_of_continuous
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (l : ℕ) (hc : Continuous (d.coordinate l)) (s : S) :
    d.upper l s - d.lower l s = 0 := by
  have hle : d.lower l s ≤ d.upper l s := sub_nonneg.mp (d.width_nonneg l s)
  have hlo : (σ s, d.lower l s) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l)) := by
    have h : d.lower l s ∈ {t | (σ s, t) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l))} :=
      (d.band l s).symm ▸ (show d.lower l s ∈ Icc (d.lower l s) (d.upper l s) from ⟨le_rfl, hle⟩)
    exact h
  have hhi : (σ s, d.upper l s) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l)) := by
    have h : d.upper l s ∈ {t | (σ s, t) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l))} :=
      (d.band l s).symm ▸ (show d.upper l s ∈ Icc (d.lower l s) (d.upper l s) from ⟨hle, le_rfl⟩)
    exact h
  rw [intervalFiberHull_value_of_continuousAt hc.continuousAt hhi,
    intervalFiberHull_value_of_continuousAt hc.continuousAt hlo, sub_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LocalInverseConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally uniform open embeddings have pointwise convergent actual
inverses on the limiting image. The small source disks are constructed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem inverse_tendsto_of_locally_uniform_open_embeddings
    (hsch : PlanarSchoenflies)
    {G : Set ℂ} (hG : IsOpen G) {f : ℂ → ℂ} (hf : ContinuousOn f G)
    (hfo : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hfi : InjOn f G)
    (Gn : ℕ → Set ℂ) (hGn : ∀ n, IsOpen (Gn n)) (fn gn : ℕ → ℂ → ℂ)
    (hfn : ∀ n, ContinuousOn (fn n) (Gn n))
    (hfno : ∀ n S, IsOpen S → S ⊆ Gn n → IsOpen (fn n '' S))
    (hfni : ∀ n, InjOn (fn n) (Gn n))
    (hleft : ∀ n x, x ∈ Gn n → gn n (fn n x) = x)
    (hlim : TendstoLocallyUniformlyOn fn f atTop G)
    (hretain : ∀ K : Set ℂ, IsCompact K → K ⊆ G → ∀ᶠ n in atTop, K ⊆ Gn n)
    {x : ℂ} (hx : x ∈ G) : Tendsto (fun n => gn n (f x)) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hG.mem_nhds hx)
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hδr : δ ≤ r := min_le_left _ _
  have hδε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let H := roundJordanAt x δ hδ
  have hHG : closure (jordanInterior H) ⊆ G := by
    rw [show H = roundJordanAt x δ hδ from rfl, roundJordanAt_closure]
    exact (closedBall_subset_closedBall hδr).trans hrG
  have hxH : x ∈ jordanInterior H := by
    rw [show H = roundJordanAt x δ hδ from rfl, roundJordanAt_interior]
    exact mem_ball_self hδ
  have hsub := eventually_compact_subset_image_jordan_disk hsch hG hf hfo hfi Gn hGn fn
    hfn hfno hfni hlim H hHG
    (hretain _ (isCompact_closure_jordanInterior H) hHG) isCompact_singleton
    (singleton_subset_iff.mpr (mem_image_of_mem f hxH))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsub.and (hretain _ (isCompact_closure_jordanInterior H) hHG))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz, he⟩ := (hN n hn).1 (mem_singleton (f x))
  have hzG := (hN n hn).2 (subset_closure hz)
  rw [← he, hleft n z hzG]
  have hzδ : dist z x < δ := by
    simpa only [H, roundJordanAt_interior, mem_ball] using hz
  exact hzδ.trans hδε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ActualInverseConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse convergence for the actual normalized finite transfer stages. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem inverse_tendsto (hsch : PlanarSchoenflies) (hG : IsOpen G)
    {x : ℂ} (hx : (x : Sphere) ∈ G) :
    Tendsto (fun n => finiteCoord ((M.stages (A.subsequence n)).inverse (A.function x)))
      atTop (𝓝 x) := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hf := A.plane_open_embedding hG
  let Gn (n : ℕ) : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
    openCompletedRegion (M.stages (A.subsequence n)).terminals.H
  have hd (n : ℕ) := (M.stages (A.subsequence n)).equivalence.finite_open_embedding
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
    (M.stages (A.subsequence n)).circle_domain.1
  apply inverse_tendsto_of_locally_uniform_open_embeddings hsch
    (hG.preimage OnePoint.continuous_coe) hf.1 hf.2.1 hf.2.2 Gn
    (fun n => (isOpen_openCompletedRegion (M.stages (A.subsequence n)).terminals.H).preimage
      OnePoint.continuous_coe)
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).forward z))
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).inverse z))
    (fun n => (hd n).1) (fun n => (hd n).2.1) (fun n => (hd n).2.2)
    ?_ A.converges ?_ hx
  · intro n z hz
    rw [coe_finiteCoord ((M.stages (A.subsequence n)).equivalence.finite_forward
      (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1 hz),
      (M.stages (A.subsequence n)).equivalence.left_inv _ hz, finiteCoord_coe]
  · intro K hK hKG
    have hsub : ((↑) : ℂ → Sphere) '' K ⊆ G := by
      rintro _ ⟨z, hz, rfl⟩
      exact hKG hz
    filter_upwards [A.strict.tendsto_atTop (M.eventually_model_contains
      (hK.image OnePoint.continuous_coe) hsub)] with n hn
    exact fun z hz => hn (mem_image_of_mem _ hz)

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarEndCaps
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched source caps shrink to their complementary
component. Continuous component-constant tests therefore have arbitrarily
small ranges on all sufficiently late caps. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

 theorem eventually_source_values {u : Sphere → ℝ} (hu : Continuous u)
    (hc : ∀ p ∈ connectedComponentIn Gᶜ q, u p = u q)
    {a b : ℝ} (ha : a < u q) (hb : u q < b) :
    ∀ᶠ n in atTop, ∀ p ∈ closedTerminalCap ((L.cores n).disk (E.address n)),
      u p ∈ Ioo a b := by
  apply E.eventually_source_cap_subset (isOpen_Ioo.preimage hu)
  intro p hp
  change u p ∈ Ioo a b
  rw [hc p hp]
  exact ⟨ha, hb⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceEndProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual projection from the limiting sphere to the source quotient,
using the inverse on the domain and the matched end on its complement. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}

namespace RealTargetEnd
variable {L : AssignedRealModelLimit M} {q q' : Sphere}
  (E : RealTargetEnd L q)

 theorem projection_in_source_cap (hG : IsOpen G) (π : Sphere → Sphere) (n : ℕ)
    {p : Sphere} (hp : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (E.address n))) :
    ∃ x ∈ closedTerminalCap ((L.cores n).disk (E.address n)),
      L.sourceProjection hG π p = π x := by
  by_cases hpG : p ∈ extendAtInfinity L.function '' G
  · have ht : p ∈ extendAtInfinity L.function ''
        (G ∩ ((↑) : ℂ → Sphere) '' jordanInterior ((L.cores n).disk (E.address n))) := by
      rw [L.side]
      exact ⟨hpG, hp⟩
    obtain ⟨x, hx, he⟩ := ht
    refine ⟨x, ?_, ?_⟩
    · exact image_mono subset_closure hx.2
    · rw [← he, L.sourceProjection_on_image hG π hx.1]
  · let A := L.chosenSourceEnd hG p hpG
    refine ⟨A.source, E.source_in_cap_of_target_interior A.matching A.outside n ?_, ?_⟩
    · rwa [A.point_eq]
    · exact L.sourceProjection_off_image hG π hpG

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ContinuousSourceProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested matched caps prove continuity of the source quotient projection
at every complementary point, including nondegenerate target components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}
namespace AssignedRealModelLimit
variable (L : AssignedRealModelLimit M)

 theorem sourceProjection_continuous (hG : IsOpen G)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → π p = π q) :
    Continuous (L.sourceProjection hG π) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ extendAtInfinity L.function '' G
  · obtain ⟨x, hx, rfl⟩ := hp
    have hi := continuousAt_conformal_invFunOn L.conformal.1 hG L.conformal.bijOn.injOn hx
    have hcont := hπ.continuousAt.comp hi
    have hval : L.sourceProjection hG π (extendAtInfinity L.function x) =
        π (invFunOn (extendAtInfinity L.function) G (extendAtInfinity L.function x)) := by
      simp only [sourceProjection, dite_eq_left (mem_image_of_mem _ hx)]
    change Tendsto (L.sourceProjection hG π) (𝓝 (extendAtInfinity L.function x))
      (𝓝 (L.sourceProjection hG π (extendAtInfinity L.function x)))
    rw [hval]
    apply hcont.congr'
    have hV := L.conformal.1.isOpen_image hG hG (Subset.refl G)
    filter_upwards [hV.mem_nhds (mem_image_of_mem _ hx)] with z hz
    simp only [sourceProjection, dite_eq_left hz, comp_apply]
  · let A := L.chosenSourceEnd hG p hp
    have hval : L.sourceProjection hG π p = π A.source := L.sourceProjection_off_image hG π hp
    change Tendsto (L.sourceProjection hG π) (𝓝 p) (𝓝 (L.sourceProjection hG π p))
    rw [hval]
    apply tendsto_nhds.mpr
    intro V hV hpV
    have hsub : connectedComponentIn Gᶜ A.source ⊆ π ⁻¹' V := by
      intro x hx
      change π x ∈ V
      rw [hc A.source x hx]
      exact hpV
    obtain ⟨n, hn⟩ := (A.matching.eventually_source_cap_subset (hV.preimage hπ) hsub).exists
    have hpCap : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (A.matching.address n)) := by
      have ht := A.matching.nested n
        (mem_iInter.mp (A.matching.target ▸ mem_connectedComponentIn A.matching.outside) (n + 1))
      exact (congrArg (fun t : Sphere => t ∈ ((↑) : ℂ → Sphere) ''
        jordanInterior (L.contours n (A.matching.address n))) A.point_eq).mp ht
    have hOpen := OnePoint.isOpen_image_coe.mpr
      (jordanInterior_isOpen (L.contours n (A.matching.address n)))
    filter_upwards [hOpen.mem_nhds hpCap] with z hz
    obtain ⟨x, hx, hproj⟩ := A.matching.projection_in_source_cap hG π n hz
    change L.sourceProjection hG π z ∈ V
    rw [hproj]
    exact hn hx

end AssignedRealModelLimit
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedSourceProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed projection takes the prescribed source value on the
whole corresponding complementary component and covers the source quotient. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M}

 theorem RealTargetEnd.sourceProjection_eq {q : Sphere} (E : RealTargetEnd L q)
    (hG : IsOpen G) (π : Sphere → Sphere)
    (hc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → π p = π q)
    {p : Sphere} (hp : p ∈ connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point) :
    L.sourceProjection hG π p = π q := by
  have hout : p ∉ extendAtInfinity L.function '' G := connectedComponentIn_subset _ _ hp
  let A := L.chosenSourceEnd hG p hout
  have hsource : A.source ∈ connectedComponentIn Gᶜ q := by
    rw [E.source]
    apply mem_iInter.mpr
    intro n
    apply E.source_in_cap_of_target_interior A.matching A.outside n
    have ht := E.nested n (mem_iInter.mp (E.target ▸ hp) (n + 1))
    exact (congrArg (fun t : Sphere => t ∈ ((↑) : ℂ → Sphere) ''
      jordanInterior (L.contours n (E.address n))) A.point_eq).mpr ht
  exact (L.sourceProjection_off_image hG π hout).trans (hc q A.source hsource)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PointDustModels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source data and a common exterior zero anchor for a finite family of
compact tests on a point-complement sphere domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_68_rc4c60f_1 : BorelSpace Sphere := ⟨rfl⟩
omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem point_component_eq_of_totallyDisconnected
    {G : Set Sphere} (hTD : IsTotallyDisconnected Gᶜ)
    (q p : Sphere) (hp : p ∈ connectedComponentIn Gᶜ q) : p = q := by
  have hq : q ∈ Gᶜ := connectedComponentIn_nonempty_iff.mp ⟨p, hp⟩
  exact hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn
    hp (mem_connectedComponentIn hq)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PointDustContourSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing subordinate contour construction on a point-complement
source, with its identity quotient made explicit. -/
open Set Function Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem exists_point_dust_subordinate_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G W : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hW : IsOpen W) (hBW : Gᶜ ⊆ W)
    (Q : {z : Sphere // z ∈ Gᶜ} → Set Sphere)
    (hQ : ∀ a, IsOpen (Q a)) (haQ : ∀ a, a.val ∈ Q a) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      ∀ i, closure (jordanInterior (J i)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (J i)), (z : Sphere) ∈ G) ∧
        ∃ a : {z : Sphere // z ∈ Gᶜ}, closure (jordanInterior (J i)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' Q a := by
  have hr : ∀ z w : Sphere, id z = id w ↔ z = w ∨
      (z ∈ Gᶜ ∧ w ∈ connectedComponentIn Gᶜ z) := by
    intro z w
    constructor
    · exact Or.inl
    · rintro (he | he)
      · exact he
      · exact (point_component_eq_of_totallyDisconnected hTD z w he.2).symm
  obtain ⟨n,J,γ,hcover,_,hdata⟩ := exists_subordinate_smooth_physical_dust_cover
    hsard hsch G id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id
    (B := Gᶜ) (A := Gᶜ) (W := W) hr hG.isClosed_compl hTD hG.isClosed_compl.isCompact
    (subset_refl _) (by rw [sdiff_self]; exact isClosed_empty) hW hBW
    (not_not.mpr hinf) (fun _ hx => hx) Q hQ haQ
  refine ⟨n,J,γ,hcover,?_⟩
  intro i
  obtain ⟨hi,hs,he,hfront,ha,hsub⟩ := hdata i
  exact ⟨hi,hs,he,hfront,fun z hz => (ha z hz).1,hsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SmallImageDustContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inner contours can be selected where the two actual compact
source coordinates remain uniformly close to a single dust trace. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem exists_small_image_dust_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (p q : EuclideanPlane → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hps : HasCompactSupport p) (hqs : HasCompactSupport q)
    {D r : ℝ} (hBD : ∀ z : ℂ, (z : Sphere) ∉ G → z ∈ ball 0 D) (hr : 0 < r) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ) (b : Fin n → Sphere),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 D) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      ∀ i z, z ∈ closure (jordanInterior (J i)) →
        ‖planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z))-
          planePair (sphereFromPlaneFunction p (b i)) (sphereFromPlaneFunction q (b i))‖ < r := by
  have hpc := continuous_sphereFromPlaneFunction hp hps
  have hqc := continuous_sphereFromPlaneFunction hq hqs
  let P := fun z => planePair (sphereFromPlaneFunction p z) (sphereFromPlaneFunction q z)
  have hP : Continuous P := continuous_planePair hpc hqc
  let W : Set Sphere := ((↑) : ℂ → Sphere) '' ball 0 D
  have hBW : Gᶜ ⊆ W := by
    intro z hz
    cases z using OnePoint.rec with
    | infty => exact (hz hinf).elim
    | coe z => exact ⟨z,hBD z hz,rfl⟩
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr isOpen_ball
  let Q : {z : Sphere // z ∈ Gᶜ} → Set Sphere :=
    fun a => P ⁻¹' ball (P a.val) r
  have hQ (a : {z : Sphere // z ∈ Gᶜ}) : IsOpen (Q a) :=
    isOpen_ball.preimage hP
  have haQ (a : {z : Sphere // z ∈ Gᶜ}) : a.val ∈ Q a := by
    change dist (P a.val) (P a.val) < r
    simpa only [dist_self] using hr
  obtain ⟨n,J,γ,hcover,hdata⟩ := exists_point_dust_subordinate_contours
    (G := G) (W := W) hsard hsch hG hinf hTD hW hBW Q hQ haQ
  have hcover' : {z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i) :=
    fun _ hz => hcover hz
  have hcenter (i : Fin n) : ∃ b : Sphere, b ∈ Gᶜ ∧ ∀ z ∈ closure (jordanInterior (J i)),
      ‖P (z : Sphere)-P b‖ < r := by
    obtain ⟨b,hb⟩ := (hdata i).2.2.2.2.2
    refine ⟨b,b.property,?_⟩
    intro z hz
    have hh := hb hz
    change dist (P (z : Sphere)) (P b) < r at hh
    simpa only [dist_eq_norm] using hh
  choose b hb hclose using hcenter
  refine ⟨n,J,γ,b,hcover',hb,?_,?_,?_⟩
  · intro i z hz
    obtain ⟨w,hw,he⟩ := (hdata i).1 hz
    exact OnePoint.coe_injective he ▸ hw
  · intro i
    refine ⟨(hdata i).2.1,(hdata i).2.2.1,(hdata i).2.2.2.1,?_⟩
    intro z hz
    exact (hdata i).2.2.2.2.1 z ((hdata i).2.2.2.1 ▸ hz)
  · intro i z hz
    simpa only [P, sphereFromPlaneFunction_coe] using hclose i z hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_StableBarrierContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the actual inner Jordan contours together with open plateau
neighborhoods and a common strict stability margin for later tests. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem exists_stable_barrier_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (p q : EuclideanPlane → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hps : HasCompactSupport p) (hqs : HasCompactSupport q)
    (Φ : EuclideanPlane → ℝ) {r D : ℝ} (hr : 0 < r)
    (hplateau : ∀ y, ‖y‖ ≤ r → Φ y = 1)
    (hBD : ∀ z : ℂ, (z : Sphere) ∉ G → z ∈ ball 0 D) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ)
      (b : Fin n → Sphere) (V : Fin n → Set ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 D) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      (∀ i, IsOpen (V i) ∧ closure (jordanInterior (J i)) ⊆ V i ∧
        ∀ A' : ℂ → EuclideanPlane,
          (∀ z ∈ V i, ‖A' z-planePair (p (complexPlaneCoordinates.symm z))
            (q (complexPlaneCoordinates.symm z))‖ < r/4) →
          ∀ z ∈ V i, Φ (A' z-planePair (sphereFromPlaneFunction p (b i))
            (sphereFromPlaneFunction q (b i))) = 1) := by
  obtain ⟨n,J,γ,b,hcover,hb,hD,hγ,hclose⟩ := exists_small_image_dust_contours
    hsard hsch hG hinf hTD p q hp hq hps hqs hBD (half_pos hr)
  let A := fun z : ℂ => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z))
  have hA : Continuous A := continuous_planePair
    (hp.comp complexPlaneCoordinates.symm.continuous) (hq.comp complexPlaneCoordinates.symm.continuous)
  have hv (i : Fin n) := saved_barrier_one_on_neighborhood A hA
    (planePair (sphereFromPlaneFunction p (b i)) (sphereFromPlaneFunction q (b i)))
    Φ (closure (jordanInterior (J i))) hr hplateau (fun z hz => (hclose i z hz).le)
  choose V hVo hJV hVs using hv
  exact ⟨n,J,γ,b,V,hcover,hb,hD,hγ,fun i => ⟨hVo i,hJV i,hVs i⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedConformalEnds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matched Jordan ends for a fixed conformal equivalence, independently
of the finite-model representation used to construct that equivalence. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure MatchedConformalEnds (G : Set Sphere) (f : Sphere → Sphere) where
  cores : ℕ → SmoothJordanCore G
  disks : (n : ℕ) → Fin (cores n).count → ℂ ≃ₜ ℂ
  strict : ∀ n, (cores n).carrier ⊆ interior (cores (n+1)).carrier
  cover : (⋃ n, interior (cores n).carrier) = G
  disjoint : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (disks n i)))
  complement : ∀ n, (f '' (cores n).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (disks n i)
  boundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores n).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (disks n i))
  side : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores n).disk i))) =
    f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (disks n i))

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 structure EndAt (p : Sphere) where
  source : Sphere
  outside : source ∈ Gᶜ
  address : (n : ℕ) → Fin (D.cores n).count
  source_eq : connectedComponentIn Gᶜ source =
    ⋂ n, closedTerminalCap ((D.cores n).disk (address n))
  target_eq : connectedComponentIn (f '' G)ᶜ p =
    ⋂ n, closedTerminalCap (D.disks n (address n))
  source_nested : ∀ n, closedTerminalCap ((D.cores (n+1)).disk (address (n+1))) ⊆
    ((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk (address n))

 def endAt (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (p : Sphere) (hp : p ∈ (f '' G)ᶜ) : D.EndAt p :=
  Classical.choice (show Nonempty (D.EndAt p) from by
    obtain ⟨b,q,hq,hs,ht,hn⟩ := corresponding_source_end_of_target hG hf.1 hf.bijOn.injOn
      D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hp
    exact ⟨⟨q,hq,b,hs,ht,hn⟩⟩)

 def projection (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (p : Sphere) : Sphere := by
  classical
  exact if hp : p ∈ f '' G then invFunOn f G p else (D.endAt hG hf p hp).source

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedComponentCorrespondence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed correspondence on the full spheres. On the domain it is
the conformal map; over a complementary component its fiber is the
whole matching component. This includes disk-to-point and point-to-disk
matches, where a continuous single-valued extension need not exist. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def relationStage (n : ℕ) : Set (Sphere × Sphere) :=
  (fun q => (q,f q)) '' (D.cores n).carrier ∪
    ⋃ i, closedTerminalCap ((D.cores n).disk i) ×ˢ closedTerminalCap (D.disks n i)

 def componentRelation (q p : Sphere) : Prop := (q,p) ∈ ⋂ n, D.relationStage n

 theorem relationStage_iff (n : ℕ) (q p : Sphere) : (q,p) ∈ D.relationStage n ↔
    (q ∈ (D.cores n).carrier ∧ p = f q) ∨
      ∃ i, q ∈ closedTerminalCap ((D.cores n).disk i) ∧ p ∈ closedTerminalCap (D.disks n i) := by
  constructor
  · rintro (⟨x,hx,hpair⟩ | h)
    · have he : x = q := congrArg Prod.fst hpair
      subst x
      exact Or.inl ⟨hx,(congrArg Prod.snd hpair).symm⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact Or.inr ⟨i,hi.1,hi.2⟩
  · rintro (⟨hq,rfl⟩ | ⟨i,hq,hp⟩)
    · exact Or.inl ⟨q,hq,rfl⟩
    · exact Or.inr (mem_iUnion.mpr ⟨i,hq,hp⟩)

 theorem componentRelation_graph (_hf : IsConformalEquivalence f G (f '' G))
    {q : Sphere} (hq : q ∈ G) : D.componentRelation q (f q) := by
  apply mem_iInter.mpr
  intro n
  apply (D.relationStage_iff n q (f q)).mpr
  by_cases hn : q ∈ (D.cores n).carrier
  · exact Or.inl ⟨hn,rfl⟩
  · have hqU : q ∈ ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk i) := by
      exact not_not.mp hn
    obtain ⟨i,hi⟩ := mem_iUnion.mp hqU
    have hfi : f q ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk i))) :=
      ⟨q,⟨hq,hi⟩,rfl⟩
    rw [D.side] at hfi
    exact Or.inr ⟨i,(image_mono subset_closure) hi,(image_mono subset_closure) hfi.2⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentRelationSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selections from the matched component correspondence. They
agree with the conformal map on the domain, are constant on each omitted
component, and are continuous at every singleton target fiber. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def targetFiber (q : Sphere) : Set Sphere := {p | D.componentRelation q p}

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableMatchedComponents
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional component pairs in the trace argument are countable:
one side has nonempty interior. Common point pairs remain unrestricted. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def IsMatchedComponentPair (P : Set Sphere × Set Sphere) : Prop :=
  IsComplementaryComponent G P.1 ∧ IsComplementaryComponent (f '' G) P.2 ∧
    ∀ q ∈ P.1, D.targetFiber q = P.2

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRoundDisks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual round disk parameters for the countable exceptional matched
component pairs. Both radius-square sums follow from their geometry. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def IndexedMatchedPair := {P : Set Sphere × Set Sphere // D.IsMatchedComponentPair P ∧
    ((interior P.1).Nonempty ∨ (interior P.2).Nonempty)}

 structure MatchedRoundDisks where
  sourceCenter : D.IndexedMatchedPair → ℂ
  targetCenter : D.IndexedMatchedPair → ℂ
  sourceRadius : D.IndexedMatchedPair → ℝ
  targetRadius : D.IndexedMatchedPair → ℝ
  source_nonneg : ∀ j, 0 ≤ sourceRadius j
  target_nonneg : ∀ j, 0 ≤ targetRadius j
  source_eq : ∀ j, j.val.1 = ((↑) : ℂ → Sphere) '' closedBall (sourceCenter j) (sourceRadius j)
  target_eq : ∀ j, j.val.2 = ((↑) : ℂ → Sphere) '' closedBall (targetCenter j) (targetRadius j)
  source_disjoint : Pairwise (Disjoint on fun j => closedBall (sourceCenter j) (sourceRadius j))
  target_disjoint : Pairwise (Disjoint on fun j => closedBall (targetCenter j) (targetRadius j))
  source_summable : Summable (fun j => sourceRadius j^2)
  target_summable : Summable (fun j => targetRadius j^2)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedScalarIntervals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual intervals for the matched disks. Their lengths are square
summable and their centers represent values of the closed correspondence.
Unused natural codes are harmless shrinking intervals at one fixed fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

variable [Encodable D.IndexedMatchedPair]

 def MatchedRoundDisks.traceCenter (E : D.MatchedRoundDisks) : ℕ → ℂ :=
  traceEnumeration E.sourceCenter 0

 def MatchedRoundDisks.traceRadius (E : D.MatchedRoundDisks) : ℕ → ℝ :=
  traceEnumeration E.sourceRadius 0

 def MatchedRoundDisks.traceTargetRadius (E : D.MatchedRoundDisks) : ℕ → ℝ :=
  traceEnumeration E.targetRadius 0

 def MatchedRoundDisks.traceWidth (E : D.MatchedRoundDisks) (L : ℝ≥0) (n : ℕ) : ℝ :=
  L*E.traceTargetRadius n+traceExtraRadius n

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneComponentRelation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed matched correspondence in the finite source chart. Every
point has a singleton fiber or belongs to one of the actual indexed disks. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def planeRelation (z : ℂ) (p : Sphere) : Prop := D.componentRelation (z : Sphere) p

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Data of the actual scalar masks used in the axial trace argument.
All fields are constructed from the matched disks and the planar maximal input. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 def maskDomain (G : Set Sphere) (W : D.IndexedMatchedPair → Set ℂ) : Set Sphere :=
  G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedCommonPoints
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common point set uses the full matched component family. The
single unused-code center may be omitted during local compression and
restored at the end, since a singleton has null scalar image. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def commonPointPlane : Set ℂ :=
  {z | (z : Sphere) ∈ Gᶜ ∧ ∀ j : D.IndexedMatchedPair, (z : Sphere) ∉ j.val.1}

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SavedAppendingContours
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed pair yields actual smooth inner contours, translated
barriers and open neighborhoods with strict inner and outer margins. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem AppendingPairData.exists_saved_contours
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ)
      (b : Fin n → Sphere) (V : Fin n → Set ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 (64*a)) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      (∀ i, IsOpen (V i) ∧ closure (jordanInterior (J i)) ⊆ V i ∧
        ∀ A' : ℂ → EuclideanPlane,
          (∀ z ∈ V i, ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z))
            (D.q (complexPlaneCoordinates.symm z))‖ < D.radius/8) →
          ∀ z ∈ V i, D.barrier (A' z-planePair (sphereFromPlaneFunction D.p (b i))
            (sphereFromPlaneFunction D.q (b i))) = 1) ∧
      (∀ i (A' : ℂ → EuclideanPlane),
        (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
          ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z))
            (D.q (complexPlaneCoordinates.symm z))‖ < a/2) →
        ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
          D.barrier (A' z-planePair (sphereFromPlaneFunction D.p (b i))
            (sphereFromPlaneFunction D.q (b i))) = 0) ∧
      (∀ i, ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => D.barrier
        (planePair (D.p x) (D.q x)-planePair (sphereFromPlaneFunction D.p (b i))
          (sphereFromPlaneFunction D.q (b i))))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η) := by
  have hplateau : ∀ y : EuclideanPlane, ‖y‖ ≤ D.radius/2 → D.barrier y = 1 := by
    intro y hy
    exact D.barrier_one y (mem_ball_zero_iff.mpr (hy.trans_lt (half_lt_self D.radius_pos)))
  obtain ⟨n,J,γ,b,V,hcover,hb,hJD,hγ,hV⟩ := exists_stable_barrier_contours hsard hsch
    hG hinf hTD D.p D.q D.p_continuous D.q_continuous D.p_compact D.q_compact
    D.barrier (half_pos D.radius_pos) hplateau
    (fun z hz => (ball_subset_ball (show a ≤ 64*a by linarith)) (hBa hz))
  refine ⟨n,J,γ,b,V,hcover,hb,hJD,hγ,?_,?_,fun i => D.small_energy _⟩
  · intro i
    refine ⟨(hV i).1,(hV i).2.1,?_⟩
    intro A' hA
    apply (hV i).2.2 A'
    simpa only [show D.radius/2/4 = D.radius/8 by ring] using hA
  · intro i A' hchange z hz hz63 hz65
    have hc := D.trace_bound (b i) (hb i)
    have hz63' : 63*a ≤ ‖complexPlaneCoordinates.symm z‖ := by
      simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z),
        complexPlaneCoordinates.apply_symm_apply] using hz63
    have hz65' : ‖complexPlaneCoordinates.symm z‖ ≤ 65*a := by
      simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z),
        complexPlaneCoordinates.apply_symm_apply] using hz65
    have hm := D.outer_margin (complexPlaneCoordinates.symm z)
      (show complexPlaneCoordinates.symm z ∈ physicalPlaneDomain G from by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere,
          complexPlaneCoordinates.apply_symm_apply] using hz)
      hz63' hz65' _ hc
    have hc' := hchange z hz hz63 hz65
    have ht : ‖planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))-
        planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i))‖ ≤
      ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))‖+
      ‖A' z-planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i))‖ := by
      have h := norm_add_le
        (planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))-A' z)
        (A' z-planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i)))
      simpa only [sub_add_sub_cancel, norm_sub_rev _ (A' z)] using h
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hlt := mem_ball_zero_iff.mp (D.barrier_support hs)
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SavedSeparatingFamily
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A saved finite family includes a common positive tolerance for both
exact contour values and strict Sobolev energy bounds. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem AppendingPairData.exists_saved_family
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a) :
    Nonempty (SavedSeparatingFamily G a η D.p D.q D.p_witness D.q_witness) := by
  obtain ⟨n,J,γ,b,V,hcover,hb,hJ,hγ,hV,houter,_⟩ :=
    D.exists_saved_contours hsard hsch hG hinf hTD ha hBa
  let c := fun i : Fin n => planePair (sphereFromPlaneFunction D.p (b i))
    (sphereFromPlaneFunction D.q (b i))
  obtain ⟨t,ht,henergy⟩ := D.exists_energy_tolerance hG c
  let τ := min (D.radius/8) (min (a/2) t)/2
  have hmin : 0 < min (D.radius/8) (min (a/2) t) :=
    lt_min (div_pos D.radius_pos (by norm_num)) (lt_min (half_pos ha) ht)
  have hτ : 0 < τ := half_pos hmin
  have hτr : τ < D.radius/8 := (half_lt_self hmin).trans_le
    (min_le_left _ _)
  have hτa : τ < a/2 := (half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hτt : τ ≤ t := ((half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))).le
  refine ⟨{
    count := n, jordan := J, curve := γ, neighborhood := V
    barrier := fun i => translatedPhysicalBarrier D.barrier (c i)
    cover := hcover, inside := hJ, regular := hγ
    open_neighborhood := fun i => (hV i).1
    contains := fun i => (hV i).2.1
    smooth := fun i => D.barrier_smooth.comp (contDiff_id.sub contDiff_const)
    compact := ?_, unit := fun i x => D.barrier_unit (x-c i)
    tolerance := τ, tolerance_pos := hτ, stable := ?_ }⟩
  · intro i
    have he : translatedPhysicalBarrier D.barrier (c i) = D.barrier ∘ Homeomorph.addRight (-c i) := by
      funext x
      change D.barrier (x-c i) = D.barrier (x+-c i)
      rw [sub_eq_add_neg]
    rw [he]
    exact D.barrier_compact.comp_homeomorph _
  · intro p q hp hq Wp Wq hclose hpE hqE i
    refine ⟨?_,?_,?_⟩
    · exact (hV i).2.2 (fun z => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z)))
        (fun z _ => (hclose _).trans_lt hτr)
    · exact houter i (fun z => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z)))
        (fun z _ _ _ => (hclose _).trans_lt hτa)
    · exact henergy i p q hp hq Wp Wq (fun z _ => (hclose z).trans hτt)
        (hpE.trans hτt) (hqE.trans hτt)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveTestConstruction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterate the constructed finite appending theorem, choosing each error
below every saved tolerance in the finite history. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

namespace AppendingConstructionState
variable {G : Set Sphere} {a ε : ℝ}

 def chooseStep (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (s : AppendingConstructionState G) (n : ℕ) :
    SavedAppendingStep a s.family (recursiveTestBudget ε n s.tolerances) (1/((n:ℝ)+1)) := by
  let D := Classical.choice (hsupply s.family (recursiveTestBudget ε n s.tolerances)
    (1/((n:ℝ)+1)) (recursiveTestBudget_pos hε n s.positive) (by positivity))
  exact ⟨D,Classical.choice (D.exists_saved_family hsard hsch hG hinf hTD ha hBa)⟩

 def next (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (s : AppendingConstructionState G) (n : ℕ) : AppendingConstructionState G :=
  let step := s.chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n
  { family := step.data.toTestFamily
    tolerances := step.saved.tolerance :: s.tolerances
    positive := fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact step.saved.tolerance_pos
      · exact s.positive t ht }

end AppendingConstructionState

 def appendingStates {G : Set Sphere} {a ε : ℝ}
    (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (T : FiniteCompactTests G) : ℕ → AppendingConstructionState G
  | 0 => ⟨T,[],fun _ ht => by simp at ht⟩
  | n+1 => (appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T n).next
      hsupply hsard hsch hG hinf hTD ha hBa hε n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrackedTestSequence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Follow each old scalar through every actual appending stage. The
coordinate indices shift by two, and both errors retain the chosen budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)

local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 def index (i : Fin T.count) : (n : ℕ) → Fin (states n).family.count
  | 0 => i
  | n+1 => (index i n).succ.succ

local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T

 def scalar (i : Fin T.count) (n : ℕ) : EuclideanPlane → ℝ :=
  (states n).family.test (idx i n)

 def witness (i : Fin T.count) (n : ℕ) :
    DeGiorgi.MemW1pWitness 2 (scalar hsupply hsard hsch hG hinf hTD ha hBa hε T i n)
      (physicalPlaneDomain G) := (states n).family.witness (idx i n)

local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem scalar_continuous (i : Fin T.count) (n : ℕ) : Continuous (f i n) :=
  (states n).family.continuous _

 theorem scalar_compact (i : Fin T.count) (n : ℕ) : HasCompactSupport (f i n) :=
  (states n).family.compact _

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveTestHistory
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every saved tolerance stays in the actual finite history. Thus each
later test change is bounded by its geometric share of that tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 def savedTolerance (n : ℕ) : ℝ :=
  ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).saved.tolerance

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrackedTailSequence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Track a scalar from any saved stage, with cumulative uniform and
Sobolev-gradient errors controlled by the actual later budgets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 def tailIndex (k : ℕ) (i : Fin (states k).family.count) :
    (n : ℕ) → Fin (states (k+n)).family.count
  | 0 => i
  | n+1 => (tailIndex k i n).succ.succ

local notation "idx" => tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T

 def tailScalar (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) : EuclideanPlane → ℝ :=
  (states (k+n)).family.test (idx k i n)

 def tailWitness (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    DeGiorgi.MemW1pWitness 2 (tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T k i n)
      (physicalPlaneDomain G) := (states (k+n)).family.witness (idx k i n)

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_TrackedTestLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual old coordinates have continuous sphere limits and strong
L2 gradient limits. Both stay within the total recursive error budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T

 def sphereScalar (i : Fin T.count) (n : ℕ) : C(Sphere,ℝ) :=
  ⟨sphereFromPlaneFunction (f i n), continuous_sphereFromPlaneFunction
    (scalar_continuous hsupply hsard hsch hG hinf hTD ha hBa hε T i n)
    (scalar_compact hsupply hsard hsch hG hinf hTD ha hBa hε T i n)⟩

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end



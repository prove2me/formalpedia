-- Prove2me | Definitions.Def_Q146C004
-- name    : Q146C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:08:04.173584+00:00
-- url     : https://prove2.me/theorems/a0191640-864c-44a2-8bff-bf7d294db389
-- title:
--   Definitions bundle Q146C004 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 797 declarations of OpenAI's Lean: 197 definitions, 40 inductive types or structures, 7 instances and 553 theorems. The definitions and types are `Graph.IsLongCycle`, `Graph.OuterOnPairs`, `Graph.attachUnion`, `OAI.CircleDomainRigidity.AppendingPairData.toTestFamily`, `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.BlockDisksFrom`, `OAI.CircleDomainRigidity.BlockPathsInDomain`, `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.BoundaryPairData`, `OAI.CircleDomainRigidity.CenteredTerminalFamily`, `OAI.CircleDomainRigidity.CenteredTerminalFamily.punctured`, `OAI.CircleDomainRigidity.CircleDomainRemovabilityRigidity`, `OAI.CircleDomainRigidity.CodeLawCandidate`, `OAI.CircleDomainRigidity.CompactBarrierData`, `OAI.CircleDomainRigidity.CompactRecursiveReduction`, `OAI.CircleDomainRigidity.CompactRegularLevelFlow.returnSubgroup`, `OAI.CircleDomainRigidity.CompactScalarCircleModel`, `OAI.CircleDomainRigidity.CompactScalarCircleModel.linearDifference`, `OAI.CircleDomainRigidity.CompactScalarCircleModel.toCompactScalarModel`, `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection`, `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.restrictWorking`, `OAI.CircleDomainRigidity.CompactScalarModel.coefficientSet`, `OAI.CircleDomainRigidity.CompactScalarModel.compactHeightSource`, `OAI.CircleDomainRigidity.CompactScalarModel.compactPrioritySource`, `OAI.CircleDomainRigidity.CompactScalarModel.heightSection`, `OAI.CircleDomainRigidity.CompactScalarModel.horizontalSection`, `OAI.CircleDomainRigidity.CompactScalarModel.pairBarrier`, `OAI.CircleDomainRigidity.CompactScalarPullback`, `OAI.CircleDomainRigidity.CompatibleRealBarrier`, `OAI.CircleDomainRigidity.CompatibleRealBarrier.controlledSize`, `OAI.CircleDomainRigidity.CompatibleRealBarrier.rebase`, `OAI.CircleDomainRigidity.ComplexPlaneL2`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.ControlledHeight`, `OAI.CircleDomainRigidity.CostAdmissible`, `OAI.CircleDomainRigidity.DyadicInside`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.ExactTraceTest`, `OAI.CircleDomainRigidity.FiniteAppendingSupply`, `OAI.CircleDomainRigidity.FiniteCircleUniformization` and 197 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Accessible`, `AccessibleJoin`, `BoundaryCyclesGenerated`, `CircleDomains_Modulus_BarrierRebase`, `CircleDomains_Modulus_CompactBarrierData`, `CircleDomains_Modulus_CompatibleRealBarrier`, `CircleDomains_Modulus_ConformalNormalization`, `CircleDomains_Modulus_ConstrainedCostCodes`, `CircleDomains_Modulus_DyadicTimeLength`, `CircleDomains_Modulus_InterleavedCollarCost`, `CircleDomains_Modulus_LaurentNormalization`, `CircleDomains_Modulus_MobiusNormalization`, `CircleDomains_Modulus_ModelPairBarrier`, `CircleDomains_Modulus_NormalizedMetricUniformization`, `CircleDomains_Modulus_PathLengthLocality`, `CircleDomains_Modulus_PhysicalCompactLength`, `CircleDomains_Modulus_PhysicalDyadicLength`, `CircleDomains_Modulus_PhysicalLengthCharacterization`, `CircleDomains_Modulus_PhysicalLengthRestriction`, `CircleDomains_Modulus_PhysicalTimeLength`, `CircleDomains_Modulus_PrincipalNormalization`, `CircleDomains_Modulus_RealSourceBarriers`, `CircleDomains_Modulus_RetaggedCost`, `CircleDomains_Modulus_SavedBarrierMargins`, `CircleDomains_Probability_AffinePhysicalTimeMeasure`, `CircleDomains_Probability_AtomicVisitMeasure`, `CircleDomains_Probability_CenteredArcLaw`, `CircleDomains_Probability_CenteredTerminalLaw`, `CircleDomains_Probability_CodeHitMeasures`, `CircleDomains_Probability_CodeLawCandidates`, `CircleDomains_Probability_CodeLawMeasures`, `CircleDomains_Probability_CodePathLaws`, `CircleDomains_Probability_CompactArcLaw`, `CircleDomains_Probability_DiskStartLaw`, `CircleDomains_Probability_DyadicMeasurePartition`, `CircleDomains_Probability_DyadicPhysicalOccupation`, `CircleDomains_Probability_MarkedFusionSmallSets`, `CircleDomains_Probability_MarkedHitFusionTree`, `CircleDomains_Probability_MarkedHitLaws`, `CircleDomains_Probability_MonotoneDyadicMass`, `CircleDomains_Probability_PathCostMeasure`, `CircleDomains_Probability_PathHitLaws`, `CircleDomains_Probability_PathLawMixtures`, `CircleDomains_Probability_PathOccupation`, `CircleDomains_Probability_PathPortionMeasure`, `CircleDomains_Probability_PhysicalOccupationAdd`, `CircleDomains_Probability_PhysicalOccupationCode`, `CircleDomains_Probability_PriorLawPresentation`, `CircleDomains_Probability_RectifiableOccupationCode`, `CircleDomains_Probability_RecursiveCodeLaw`, `CircleDomains_Probability_TagTupleMeasure`, `CircleDomains_Reflection_CompactReflectionCoefficient`, `CircleDomains_Rigidity_AssembledMaskedModel`, `CircleDomains_Rigidity_ConductivityContraction`, `CircleDomains_Rigidity_ExactTraceTests`, `CircleDomains_Rigidity_MaskedCoordinateData`, `CircleDomains_Rigidity_MaskedCoordinateStage`, `CircleDomains_Rigidity_MaskedLevelData`, `CircleDomains_Rigidity_MaskedModelData`, `CircleDomains_Rigidity_MatchedEndChains`, `CircleDomains_Rigidity_ModelPointTrace`, `CircleDomains_Rigidity_PrincipalScalarSolver`, `CircleDomains_Selection_AffinePhysicalRestriction`, `CircleDomains_Selection_AffineTagRestriction`, `CircleDomains_Selection_BlockCodeInvariants`, `CircleDomains_Selection_ControlledHeight`, `CircleDomains_Selection_DisjointDustContours`, `CircleDomains_Selection_DustPriorContacts`, `CircleDomains_Selection_DyadicPartition`, `CircleDomains_Selection_DyadicTimes`, `CircleDomains_Selection_FiniteJumpSystems`, `CircleDomains_Selection_FiniteMarkedTrapping`, `CircleDomains_Selection_JumpBlockCodes`, `CircleDomains_Selection_JumpBlockCountBound`, `CircleDomains_Selection_JumpChainEdges`, `CircleDomains_Selection_LevelFlowCoordinate`, `CircleDomains_Selection_MarkedConfigurations`, `CircleDomains_Selection_MixedCoordinateStage`, `CircleDomains_Selection_OuterContours`, `CircleDomains_Selection_PeriodBandGraph`, `CircleDomains_Selection_PhysicalDyadicMonotone`, `CircleDomains_Selection_PhysicalRealCoordinate`, `CircleDomains_Selection_PhysicalSubpaths`, `CircleDomains_Selection_PhysicalTerminals`, `CircleDomains_Selection_PreterminalVisits`, `CircleDomains_Selection_PriorLevelFamily`, `CircleDomains_Selection_RealAnchorRetention`, `CircleDomains_Selection_RealSequenceRetention`, `CircleDomains_Selection_RealStageEstimates`, `CircleDomains_Selection_RebasedLevelPresentations`, `CircleDomains_Selection_RecursiveTestConstruction`, `CircleDomains_Selection_RegularContours`, `CircleDomains_Selection_RegularLevelFlow`, `CircleDomains_Selection_RegularLevelFlowOrbit`, `CircleDomains_Selection_RegularLevelLeastPeriod`, `CircleDomains_Selection_RegularLevelPeriodicParametrization`, `CircleDomains_Selection_RegularLevelReturn`, `CircleDomains_Selection_RestrictedFlattenedSelection`, `CircleDomains_Selection_ScalarEndCaps`, `CircleDomains_Selection_SinglePieceBlock`, `CircleDomains_Selection_SubordinateDustCover`, `CircleDomains_Selection_TaggedPhysicalRestriction`, `CircleDomains_Selection_VisitCounts`, `CircleDomains_Sobolev_AppendingEnergyTolerance`, `CircleDomains_Sobolev_LipschitzIntervalPaths`, `CircleDomains_Sobolev_ModelLocalEnergy`, `CircleDomains_Sobolev_ModelScalarEnergy`, `CircleDomains_Sobolev_SmoothContours`, `CircleDomains_Sobolev_SmoothJordanExhaustion`, `CircleDomains_Sobolev_SmoothJordanNeighborhoods`, `CircleDomains_Sobolev_SmoothMeanBandWeight`, `CircleDomains_Sobolev_SmoothMeanGraphGeometry`, `CircleDomains_Sobolev_SmoothPlaneSobolev`, `CircleDomains_Sobolev_SmoothRealSphereMaps`, `CircleDomains_Sobolev_SmoothSphereCharts`, `CircleDomains_Sobolev_SmoothSphereEquivalence`, `CircleDomains_Sobolev_SphereRealDifferential`, `CircleDomains_Sobolev_SphericalAreaLocalization`, `CircleDomains_Sobolev_WeakHeightIdentification`, `CircleDomains_Topology_AffinePathTime`, `CircleDomains_Topology_AssignedCollarExclusion`, `CircleDomains_Topology_BasePathCodes`, `CircleDomains_Topology_BoundaryClosingArc`, `CircleDomains_Topology_BoundaryPairNeighborhood`, `CircleDomains_Topology_BoundedRoundDisks`, `CircleDomains_Topology_CircleMobiusImage`, `CircleDomains_Topology_ClippedPaths`, `CircleDomains_Topology_ClosedJordanCore`, `CircleDomains_Topology_CompactArcWinding`, `CircleDomains_Topology_CompactCoreRetention`, `CircleDomains_Topology_CompactDiskRayBounds`, `CircleDomains_Topology_CompactRegularLevelContours`, `CircleDomains_Topology_CompactScalarCircleModelData`, `CircleDomains_Topology_CompactScalarModelFromCircle`, `CircleDomains_Topology_CutoffCore`, `CircleDomains_Topology_DyadicOpenCover`, `CircleDomains_Topology_ExteriorSeparation`, `CircleDomains_Topology_FiniteCircleGreen`, `CircleDomains_Topology_FiniteCompactTests`, `CircleDomains_Topology_FiniteJordanModelInput`, `CircleDomains_Topology_FinitePlaneEmbedding`, `CircleDomains_Topology_ImageCoreBoundary`, `CircleDomains_Topology_ImageCoreJordan`, `CircleDomains_Topology_JordanDiskImages`, `CircleDomains_Topology_JordanEndComponents`, `CircleDomains_Topology_JordanExteriors`, `CircleDomains_Topology_JordanFillLimits`, `CircleDomains_Topology_MapDiskExclusion`, `CircleDomains_Topology_MixedModelExhaustion`, `CircleDomains_Topology_NestedEndComponents`, `CircleDomains_Topology_PathEndpoints`, `CircleDomains_Topology_PathGates`, `CircleDomains_Topology_PathSelectionInput`, `CircleDomains_Topology_PathTags`, `CircleDomains_Topology_PathTolls`, `CircleDomains_Topology_PhysicalCollarCoordinates`, `CircleDomains_Topology_ProjectionJordanCap`, `CircleDomains_Topology_QuotientCollarJordan`, `CircleDomains_Topology_RealModelExhaustion`, `CircleDomains_Topology_RecursiveCompactReduction`, `CircleDomains_Topology_RegularLevelCompactOrbit`, `CircleDomains_Topology_RegularLevelOpenOrbit`, `CircleDomains_Topology_RetainedJordanSides`, `CircleDomains_Topology_SaturatedDisks`, `CircleDomains_Topology_SavedSeparatingFamily`, `CircleDomains_Topology_SimpleLoopCircle`, `CircleDomains_Topology_SubarcIntersectionCount`, `CircleDomains_Topology_TerminalArcSet`, `CircleDomains_Topology_TwoArcSimpleLoop`, `CircleDomains_Transfer_CompletedChart`, `CircleDomains_Transfer_CountableRealTransfer`, `CircleDomains_Transfer_FilledCoordinates`, `CircleDomains_Transfer_MixedMarkedModels`, `CircleDomains_Transfer_ModelAppendedPairs`, `CircleDomains_Transfer_ModelFlattenedSelection`, `CircleDomains_Transfer_ModelHeightDescent`, `CircleDomains_Transfer_ModelRealSubfamily`, `CircleDomains_Transfer_RealEndCorrespondence`, `CircleDomains_Transfer_RealMarkedModels`, `CircleDomains_Transfer_RealTargetEnds`, `CircleDomains_Transfer_RealTransferStage`, `CircleDomains_Transfer_ScalarModelLinearRecovery`, `CircleDomains_Transfer_SourceAnchor`, `CircleDomains_Transfer_SourceEndProjection`, `CircleDomains_Transfer_SourceTargetEnds`, `CircleDomains_Transfer_TerminalTransfer`, `CircleDomains_Uniformization_Conformal`, `CircleDomains_Uniformization_ConformalComposition`, `CircleDomains_Uniformization_ConformalFiniteEmbedding`, `CircleDomains_Uniformization_ConformalInverse`, `CircleDomains_Uniformization_ConformalLocalInverse`, `CircleDomains_Uniformization_FiniteCompletion`, `CircleDomains_Uniformization_FiniteCompletionUniformization`, `CircleDomains_Uniformization_FiniteLiftConformal`, `CircleDomains_Uniformization_FiniteModelEnds`, `CircleDomains_Uniformization_FiniteUniformization`, `CircleDomains_Uniformization_JordanCircularizationSequence`, `CircleDomains_Uniformization_JordanExteriorDiskChart`, `CircleDomains_Uniformization_JordanExteriorDiskMap`, `CircleDomains_Uniformization_LimitConformality`, `CircleDomains_Uniformization_MetricConformality`, `CircleDomains_Uniformization_MixedAssignedLimit`, `CircleDomains_Uniformization_MixedLimitRealProjection`, `CircleDomains_Uniformization_MobiusConformal`, `CircleDomains_Uniformization_MontelProof`, `CircleDomains_Uniformization_PrincipalJordanCircleMap`, `CircleDomains_Uniformization_RiemannDiskExtremal`, `CircleDomains_Uniformization_RiemannDiskMap`, `CircleDomains_Uniformization_ScalarModelCoefficients`, `CombinatorialInvariance`, `CrosscutAtMostTwo`, `CrosscutCells`, `Curve`, `FaceCycles`, `FaceCyclesLand`, `FaceCyclesProof`, `FreshAccess`, `GeneralCrosscut`, `GeneratedStructure`, `Graph_Component`, `Graph_Cycle`, `Graph_CycleJordan`, `Graph_Degree`, `Graph_Ear`, `Graph_OuterFace`, `Graph_PathGraph`, `Graph_Relabel`, `Graph_Tree`, `Graph_TwoConnected`, `Graph_Walk`, `GridAttach`, `InitialPair`, `JordanSeparates`, `KLS_Sobolev_Witnesses`, `Line`, `LocalGrid`, `MatchedArc`, `ModelCurve`, `OuterChain`, `OverlayGraph`, `ParitySplitting`, `Plane`, `Polygonal`, `PolygonalCrosscut`, `PrePolygonArc`, `SimpleArc`, `SkeletonAccess`, `SkeletonLocal`, `SquareCycle`, `SquareMesh`, `SquareMeshConnected`, `SquareMeshFixed`, `SquareMover`, `Strip`, `Subarc`, `TwoArcs`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C000`, `Q146C001` and `Q146C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C006`, `Q146C007` and `Q146C008`; the statements `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests` and `OAI.CircleDomainRigidity.finiteJordanModelUniformization`; the proofs of `OAI.CircleDomainRigidity.planarSobolevCoarea` and `OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C000
import Definitions.Def_Q146C001
import Definitions.Def_Q146C002

section
-- module Solutions.Q146_CD.Plane
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The plane, and the compactness toolkit

The plane is `EuclideanSpace ℝ (Fin 2)`. This module fixes that choice, supplies the
orientation form `det` and the right-angle rotation `perp` used to keep track of the two
sides of a polygonal curve, and collects the elementary consequences of compactness and
connectedness that the rest of the development uses without comment.

## Blueprint

* `det`, `perp` — Appendix C, item 1.
* `Plane.notMem_of_mem_segment_of_isMinOn` — Lemma 1.3 (nearest-point segment).
* `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff`
  — Lemma 1.4 (a), (b), (c) (compact separation).
* `Plane.eq_singleton_iInter_of_diam_tendsto_zero` — Lemma 1.6 (nested compact singleton).
* `Plane.connectedComponentIn_eq_of_frontier_disjoint` — Lemma 1.7 (recognizing a component).

Lemma 1.5 (closure and diameter) is `Metric.diam_closure` in Mathlib.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### The orientation form and the right-angle rotation -/

/-! ### Compactness -/

variable {K L U V : Set Plane} {x a y : Plane}

/-- Lemma 1.4 (c) (compact separation). A point of an open set off a compact set has a ball
inside the difference. -/
theorem exists_ball_subset_diff (hU : IsOpen U) (hK : IsCompact K) (hx : x ∈ U \ K) :
    ∃ ρ > 0, ball x ρ ⊆ U \ K := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx.1
  obtain ⟨s, hs, hsK⟩ :=
    (isCompact_singleton (x := x)).exists_thickening_subset_open hK.isClosed.isOpen_compl
      (by simpa using hx.2)
  refine ⟨min r s, lt_min hr hs, fun z hz => ⟨hrU (ball_subset_ball (min_le_left _ _) hz), ?_⟩⟩
  exact hsK (mem_thickening_iff.2 ⟨x, rfl, lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _)⟩)

/-- Lemma 1.6 (nested compact singleton). A decreasing sequence of nonempty compact sets whose
diameters tend to `0` has a single point in its intersection. -/
theorem eq_singleton_iInter_of_diam_tendsto_zero {K : ℕ → Set Plane}
    (hne : ∀ n, (K n).Nonempty) (hK : ∀ n, IsCompact (K n)) (hmono : Antitone K)
    (hdiam : Filter.Tendsto (fun n => diam (K n)) Filter.atTop (nhds 0)) :
    ∃ p, ⋂ n, K n = {p} := by
  have hnonempty : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => hmono (Nat.le_succ n)) hne (hK 0) (fun n => (hK n).isClosed)
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨p, subset_antisymm (fun q hq => ?_) (by simpa using hp)⟩
  -- Any two points of the intersection are within `diam (K n)` of each other, for every `n`.
  rw [mem_singleton_iff]
  have hbdd : ∀ n, dist q p ≤ diam (K n) := fun n =>
    dist_le_diam_of_mem (hK n).isBounded (mem_iInter.1 hq n) (mem_iInter.1 hp n)
  have : dist q p ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdiam hbdd
  exact dist_le_zero.1 this

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Accessible
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Strongly accessible boundary points

A point `p` of the boundary of a region `D` is *strongly accessible* when an open disk
contained in `D` is tangent to the boundary at `p`. Ordinary accessibility (some arc in `D`
ending at `p`) is too weak for the iterative construction: what is wanted at `p` is a definite
wedge of straight segments running into `D`, which can then be shrunk to avoid any compact set
already built.

This module supplies that wedge. The tangent disk `B(q, r)` at `p` is turned into the open
cone `accessCone p v s` of points seen from `p` in a direction within 60 degrees of
`v = (q - p)/r` and at distance less than `s`; the content of Lemma 8.4 is that this cone lies
in the disk as soon as `s ≤ r`, and hence in `D`.

## Blueprint

* `Schoenflies.StronglyAccessible` — Definition 8.1 (strong accessibility).
* `Schoenflies.stronglyAccessible_of_isMinOn` — Lemma 8.2 (nearest points are strongly
  accessible).
* `Schoenflies.tangent_cone` — Lemma 8.4 (tangent-disk cone), in the literal form of the
  blueprint; `Schoenflies.accessCone_subset_ball` is the same estimate packaged as the
  inclusion of a truncated cone, which is the form the consumers use.
* `Schoenflies.exists_countable_dense_stronglyAccessible` — Proposition 8.5 (countable dense
  strong-access set).

Lemma 8.3 (density of strongly accessible points) is not formalized here: its proof runs
through `C = ∂D`, i.e. through the Jordan curve theorem, which is not yet available. Its role
is played by Proposition 8.5, which is stated with `C ⊆ closure D` as a hypothesis.
-/

open Metric Set

namespace Schoenflies

variable {C D E : Set Plane} {p q v w : Plane} {r s s' t : ℝ}

/-! ### Strong accessibility -/

/-- Definition 8.1 (strong accessibility). A point `p` is *strongly accessible* from `D` when
some open disk of positive radius contained in `D` is tangent to `p`, that is, has `p` on its
boundary circle. -/
def StronglyAccessible (D : Set Plane) (p : Plane) : Prop :=
  ∃ (q : Plane) (r : ℝ), 0 < r ∧ dist q p = r ∧ ball q r ⊆ D

/-- Lemma 8.2 (nearest points are strongly accessible). If `a ∈ C` is nearest to a point `q`
off `C`, then the ball of radius `dist q a` around `q` misses `C`; being connected it stays
inside the connected component of `q` in the complement of `C`, so any set `D` containing that
component contains a disk tangent to `C` at `a`.

The hypothesis is phrased as `connectedComponentIn Cᶜ q ⊆ D` rather than as `D` being that
component, so that it can be discharged by an inclusion when `D` is known only up to
containment. No closedness of `C` is needed. -/
theorem stronglyAccessible_of_isMinOn {a : Plane} (hq : q ∉ C) (ha : a ∈ C)
    (hmin : ∀ b ∈ C, dist q a ≤ dist q b) (hD : connectedComponentIn Cᶜ q ⊆ D) :
    StronglyAccessible D a := by
  have hpos : 0 < dist q a := dist_pos.2 fun h => hq (h ▸ ha)
  refine ⟨q, dist q a, hpos, rfl, ?_⟩
  -- Every point strictly nearer to `q` than `a` is off `C`, by minimality.
  have hball : ball q (dist q a) ⊆ Cᶜ := by
    intro z hz hzC
    rw [mem_ball, dist_comm] at hz
    exact absurd (hmin z hzC) (not_le.2 hz)
  -- A ball is connected, so it lies in the component of its centre.
  exact ((convex_ball q (dist q a)).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hpos) hball).trans hD

/-! ### The cone of access directions -/

/-- The open cone of straight access segments at `p` around the unit direction `v`, truncated
at radius `s`: the points seen from `p` in a direction `w` with `⟪v, w⟫ > 1/2` and at distance
less than `s`. Writing the condition as `‖x - p‖ / 2 < ⟪v, x - p⟫` avoids normalizing `x - p`,
and makes the openness of the cone immediate. -/
def accessCone (p v : Plane) (s : ℝ) : Set Plane :=
  {x | ‖x - p‖ < s ∧ ‖x - p‖ / 2 < inner ℝ v (x - p)}

theorem accessCone_subset_ball_self : accessCone p v s ⊆ ball p s := fun x hx => by
  rw [mem_ball, dist_eq_norm]; exact hx.1

theorem accessCone_mono (hs : s ≤ s') : accessCone p v s ⊆ accessCone p v s' :=
  fun _ hx => ⟨hx.1.trans_le hs, hx.2⟩

/-- Membership in the cone in the form used by the blueprint: a unit direction `w` making an
angle of less than 60 degrees with `v`, and a distance `t` below the truncation radius. -/
theorem mem_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (ht : 0 < t) (hts : t < s) :
    p + t • w ∈ accessCone p v s := by
  have hsub : p + t • w - p = t • w := by module
  have hnorm : ‖p + t • w - p‖ = t := by
    rw [hsub, norm_smul, hw, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  refine ⟨by rw [hnorm]; exact hts, ?_⟩
  rw [hnorm, hsub, real_inner_smul_right]
  nlinarith

/-- The cone at `p` around the direction `v` is nonempty for every positive truncation radius:
the direction `v` itself is admissible. -/
theorem accessCone_nonempty (hv : ‖v‖ = 1) (hs : 0 < s) : (accessCone p v s).Nonempty := by
  refine ⟨p + (s / 2) • v, mem_accessCone hv ?_ (by linarith) (by linarith)⟩
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

/-- An open segment leaving `p` in an admissible direction lies in the cone. -/
theorem openSegment_subset_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (hs : 0 < s) :
    openSegment ℝ p (p + s • w) ⊆ accessCone p v s := by
  rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
  have hα' : α = 1 - β := by linarith
  subst hα'
  have hx : (1 - β) • p + β • (p + s • w) = p + (β * s) • w := by module
  rw [hx]
  exact mem_accessCone hw hcone (by positivity) (by nlinarith)

/-! ### The tangent-disk cone -/

/-- Lemma 8.4 (tangent-disk cone), in the form the construction uses. If the disk `B(q, r)` is
tangent at `p`, then the whole truncated cone around `v = (q - p)/r` of any radius `s ≤ r` lies
inside that disk.

The estimate behind it is the blueprint's: for `x` in the cone, with `d = ‖x - p‖`,
`‖x - q‖² = d² - 2⟪x - p, q - p⟫ + r² < d² - rd + r² = r² + d(d - r) < r²`. -/
theorem accessCone_subset_ball (hr : 0 < r) (hpq : ‖q - p‖ = r) (hs : s ≤ r) :
    accessCone p (r⁻¹ • (q - p)) s ⊆ ball q r := by
  rintro x ⟨hlt, hcone⟩
  set d := ‖x - p‖ with hd
  set I := inner ℝ (q - p) (x - p) with hI
  -- Clear the normalization: the cone condition is `r * d / 2 < ⟪q - p, x - p⟫`.
  rw [real_inner_smul_left] at hcone
  have hmul : r * (d / 2) < r * (r⁻¹ * I) := by
    exact mul_lt_mul_of_pos_left hcone hr
  have hcancel : r * (r⁻¹ * I) = I := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hcancel] at hmul
  -- The cone condition forces `x ≠ p`, since `I ≤ r * d` by Cauchy–Schwarz.
  have hcs : I ≤ r * d := by
    have := real_inner_le_norm (q - p) (x - p)
    rwa [hpq] at this
  have hd0 : 0 < d := by nlinarith [norm_nonneg (x - p)]
  have hdr : d < r := hlt.trans_le hs
  -- The estimate.
  have hxq : x - q = (x - p) - (q - p) := by module
  have key : ‖x - q‖ ^ 2 < r ^ 2 := by
    rw [hxq, norm_sub_sq_real, hpq, real_inner_comm]
    nlinarith
  rw [mem_ball, dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hr.le key

/-- A strongly accessible point has a nonempty open cone of straight access segments into `D`,
and the cone may be truncated at any radius below the radius of the tangent disk — which is how
the construction makes it avoid a compact set already built. -/
theorem StronglyAccessible.exists_cone (h : StronglyAccessible D p) :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone p v s ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  have hpq : ‖q - p‖ = r := by rw [← dist_eq_norm]; exact hd
  refine ⟨r⁻¹ • (q - p), ?_, r, hr, fun s hs => (accessCone_subset_ball hr hpq hs).trans hball⟩
  rw [norm_smul, hpq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']

/-- A strongly accessible point is the endpoint of a straight access segment: the open segment
from `p` to the centre of the tangent disk lies in `D`. -/
theorem StronglyAccessible.openSegment_subset (h : StronglyAccessible D p) :
    ∃ z ∈ D, p ≠ z ∧ openSegment ℝ p z ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  refine ⟨q, hball (mem_ball_self hr), ?_, ?_⟩
  · intro hpq
    rw [← hpq, dist_self] at hd
    exact absurd hd.symm hr.ne'
  · rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hα' : α = 1 - β := by linarith
    subst hα'
    refine hball ?_
    have hx : (1 - β) • p + β • q - q = (1 - β) • (p - q) := by module
    rw [mem_ball, dist_eq_norm, hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      ← dist_eq_norm, dist_comm, hd]
    nlinarith

/-! ### A countable dense set of strongly accessible points -/

/-- Proposition 8.5 (countable dense strong-access set). For every rational point of `D` pick a
nearest point of `C`; the chosen points are countably many, all strongly accessible, and dense
in `C`, since a point of `C` is approximated by points of `D` and the nearest point of `C` to
such a `q` is at most `dist q p` from `q`, hence at most `2 * dist q p` from `p`.

The hypothesis `C ⊆ closure D` replaces the blueprint's appeal to `C = ∂D` (Theorem 6.1);
`hDmax` says `D` swallows the connected component in `Cᶜ` of each of its points, which holds
when `D` is such a component. -/
theorem exists_countable_dense_stronglyAccessible (hC : IsCompact C) (hCne : C.Nonempty)
    (hDopen : IsOpen D) (hDC : D ⊆ Cᶜ) (hDmax : ∀ q ∈ D, connectedComponentIn Cᶜ q ⊆ D)
    (hCD : C ⊆ closure D) :
    ∃ A ⊆ C, A.Countable ∧ (∀ a ∈ A, StronglyAccessible D a) ∧ C ⊆ closure A := by
  -- A countable dense subset of the plane, cut down to `D`.
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Plane
  -- A nearest point of `C` to each point of the plane.
  have hnear : ∀ x : Plane, ∃ a, a ∈ C ∧ ∀ b ∈ C, dist x a ≤ dist x b := by
    intro x
    obtain ⟨a, haC, hmin⟩ :=
      hC.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
    exact ⟨a, haC, fun b hb => isMinOn_iff.1 hmin b hb⟩
  choose f hfC hfmin using hnear
  refine ⟨f '' (S ∩ D), ?_, (hScount.mono inter_subset_left).image f, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hfC x
  · rintro _ ⟨x, hx, rfl⟩
    exact stronglyAccessible_of_isMinOn (hDC hx.2) (hfC x) (hfmin x) (hDmax x hx.2)
  · -- Density.
    intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- A point of `D` within `ε/2` of `p` …
    obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.1 (hCD hp) (ε / 2) (by linarith)
    -- … and, `D` being open, a point of `S ∩ D` still within `ε/2` of `p`.
    obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hDopen y hyD
    obtain ⟨z, hzS, hz⟩ := hSdense.exists_dist_lt y (lt_min hδ (by linarith : 0 < ε / 2 - dist p y))
    have hzD : z ∈ D := hδD (by rw [mem_ball, dist_comm]; exact hz.trans_le (min_le_left _ _))
    have hpz : dist p z < ε / 2 := by
      have := (dist_triangle p y z).trans_lt
        (by linarith [hz.trans_le (min_le_right δ (ε / 2 - dist p y))] :
          dist p y + dist y z < ε / 2)
      exact this
    -- The chosen nearest point to `z` is at most `dist z p` from `z`.
    refine ⟨f z, ⟨z, ⟨hzS, hzD⟩, rfl⟩, ?_⟩
    have h1 : dist z (f z) ≤ dist z p := hfmin z p hp
    have h2 : dist p (f z) ≤ dist p z + dist z (f z) := dist_triangle _ _ _
    rw [dist_comm z p] at h1
    linarith

end Schoenflies
end

section
-- module Solutions.Q146_CD.Curve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-! ### The unit interval, as a subset of `ℝ` -/

/-! ### Elementary properties -/

namespace IsJordanCurve

variable {C : Set Plane}

theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

end IsJordanCurve

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Walk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet _root_.Graph.pathGraphOf_isLink _root_.Graph.pathGraphOf_vertexSet _root_.Graph.vertexSet_union_pathGraphOf
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

/-! ### The vertices an edge list touches -/

theorem mem_coveredVertices (he : e ∈ W) (hx : G.Inc e x) : x ∈ G.coveredVertices W :=
  ⟨e, he, hx⟩

/-! ### Walks -/

theorem IsWalk.edgeSet_subset (h : G.IsWalk u W v) : ∀ e ∈ W, e ∈ E(G) := fun _ he ↦ h.edge_mem he

/-- A walk that starts inside a set of vertices and ends outside it crosses the boundary
along one of its own edges. -/
theorem IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

/-! ### Paths -/

/-- A path's step never departs from where it arrives: the freshness clause already says so,
because a walk always visits its own source. -/
theorem IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

/-- **A path never takes a loop.** This is why nothing in this file has to assume the graph is
loopless: a step along a loop would depart from the vertex it arrives at, which the freshness
clause forbids. -/
theorem IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      -- `hloop : G.IsLink e x x` shares an edge with `hl : G.IsLink e u w`, so `u = w`.
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

/-! ### Reachability -/

theorem Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

/-! ### Connectedness -/

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Cycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

/-- Conversely, a walk in the deletion could not have used a deleted name. -/
theorem IsWalk.notMem_of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) (hf : f ∈ W) :
    f ∉ F :=
  (mem_edgeSet_deleteEdges_iff.1 (h.edge_mem hf)).2

theorem IsPath.of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) : G.IsPath u W v :=
  h.mono deleteEdges_le

theorem IsPath.notMem_of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) (hf : f ∈ W) :
    f ∉ F :=
  h.isWalk.notMem_of_deleteEdges hf

/-! ### Cycles -/

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-- **An edge whose deletion leaves its ends joined lies on a cycle.** The route that
survives is a walk of the deletion, hence contains a path of the deletion, and a path of the
deletion cannot have used the name that was deleted. -/
theorem LiesOnCycle.of_deleteEdges_reaches (hl : G.IsLink e u v)
    (h : (G.deleteEdges {e}).Reaches u v) : G.LiesOnCycle e := by
  obtain ⟨D, hD⟩ := h.exists_isPath
  exact ⟨u, v, D, hl, hD.of_deleteEdges, fun hmem ↦ hD.notMem_of_deleteEdges hmem rfl⟩

/-- **The cycle criterion**: an edge lies on a cycle if and only if deleting it does not
disconnect its endpoints. -/
theorem liesOnCycle_iff_deleteEdges_reaches (hl : G.IsLink e u v) :
    G.LiesOnCycle e ↔ (G.deleteEdges {e}).Reaches u v :=
  ⟨LiesOnCycle.deleteEdges_reaches hl, LiesOnCycle.of_deleteEdges_reaches hl⟩

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-! ### Acyclicity -/

/-! ### Bridges -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Degree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Degree and the handshake lemma

Degree counting on Mathlib's multigraph `Graph α β`, for graphs with finitely many vertices
and finitely many edges.

## Carrying finiteness

`V(G)` and `E(G)` are `Set α` and `Set β`, not types, so finiteness has to be carried
somehow. The choice made here — and inherited by every later graph module — is a
`Prop`-valued class

```
class Graph.Finite (G : Graph α β) : Prop
```

bundling `V(G).Finite` and `E(G).Finite`, with `G.vertexFinset` and `G.edgeFinset` derived
from it. The reasons:

* It is a `Prop`, so it is proof irrelevant. `G.vertexFinset` and `G.degree` therefore do not
  depend on *which* finiteness proof is in scope, and two lemmas proved with different
  instances still compose. A bundled `Finset`-valued structure would not have that property:
  it duplicates the `vertexSet` data and forces a `↑G.vertexFinset = V(G)` side condition at
  every call site.
* It is a class, so it is silent at the call site — the statements below read like ordinary
  graph theory instead of dragging two `Set.Finite` hypotheses through every signature. The
  price is that a subgraph does not get an instance for free; `Graph.Finite.of_le` produces
  one, and `haveI` installs it locally. That is the right trade: in this development
  finiteness is a standing assumption on the ambient graph and subgraphs are formed
  constantly.
* `Finite ↥V(G)` and `Finite ↥E(G)` instances are provided too, so Mathlib's own machinery
  (`Set.Finite.subset`, `Set.toFinite`, ...) fires without help.

Counts are `Set.ncard`. `Set.ncard` is total — it is `0` on an infinite set — so `G.degree`
is defined for every graph and needs no instance argument; finiteness enters only where a
theorem actually needs it.

## Degree

`G.degree x` is the number of *edge ends* at `x`:

```
G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard
```

A non-loop edge at `x` is counted once, by the first summand. A loop at `x` is counted
twice, once by each summand. This is the definition the handshake lemma needs, and it agrees
with `SimpleGraph.degree` on loopless graphs.

## Blueprint

* `Graph.sum_degree_eq_two_mul_ncard_edgeSet` — "the degree sum is twice the number of
  edges", the counting step in the proof of Lemma `lem:three-leaf-tree` (Trees with three
  leaves). The whole content is `Graph.ncard_inc_add_ncard_isLoopAt`: an edge has exactly two
  ends.
* `Graph.IsLeaf` — "the vertices of degree one are the leaves", same lemma.

## Namespace

Everything lives in the root `Graph` namespace rather than in `Schoenflies`, so that dot
notation `G.degree`, `G.IsLeaf`, `G.vertexFinset` works on a `G : Graph α β`. Later graph
modules should do the same.
-/

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-! ### Finiteness -/

instance instFiniteElemVertexSetOfFinite [G.Finite] : _root_.Finite V(G) := Set.finite_coe_iff.2 (finite_vertexSet G)

instance instFiniteElemEdgeSetOfFinite [G.Finite] : _root_.Finite E(G) := Set.finite_coe_iff.2 (finite_edgeSet G)

/-! ### Incidence sets, unfolded -/

/-! ### Degree -/

/-! ### An edge has exactly two ends

This is the entire content of the handshake lemma: summed over the vertices, the number of
ends an edge has there is two, whether the edge is a loop (two ends at one vertex) or not
(one end at each of two vertices).
-/

/-! ### The handshake lemma -/

/-! ### Leaves -/

end Graph
end

section
-- module Solutions.Q146_CD.Polygonal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric Set

namespace Schoenflies

theorem isPolygonal_segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[a, b], (poly_pair a b).symm⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_CycleJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

theorem IsDrawing.not_isLoopAt (h : IsDrawing G drawing) (e : β) (u : Plane) :
    ¬ G.IsLoopAt e u :=
  fun hloop ↦ h.ne_of_isLink hloop rfl

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-! ### The realisation of a cycle -/

end Graph
end

section
-- module Solutions.Q146_CD.OverlayGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- An end of an edge is a vertex. -/
theorem overlayGraph_inc (hP : P ∈ overlayPieces pieces points) (h : v = P.1 ∨ v = P.2) :
    (overlayGraph pieces points).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SimpleArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- Prepending a vertex to a nonempty list adds the segment to its head. -/
theorem poly_cons_of_ne_nil {vs : List Plane} (h : vs ≠ []) (u : Plane) :
    poly (u :: vs) = segment ℝ u (vs.head h) ∪ poly vs := by
  match vs, h with
  | _ :: _, _ => rfl

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-- **The realisation of a nonempty walk of the overlay graph is the carrier of a vertex
list**, running from the walk's source to its target.

The list is returned rather than an unnamed polygonal set: the consumers of Lemma 1.1 that
overlay the arc with something else need its vertices. -/
theorem exists_poly_eq_edgesCover {u v : Plane} {W : List Piece}
    (hW : (overlayGraph pieces points).IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = u ∧ vs.getLast h = v ∧
      poly vs = Graph.edgesCover segmentDrawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    -- The edge's arc is the segment from the source to the waypoint, in whichever order the
    -- edge names its ends.
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing]
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    rcases eq_or_ne W [] with rfl | hWne
    · have hwv : w = v := hW.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_⟩
      rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := ih hWne
      refine ⟨u :: vs, by simp, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · rw [poly_cons_of_ne_nil hvs, hhead, hpoly, Graph.edgesCover_cons, hedge]

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-- Both ends of an edge reach the same vertices. -/
theorem overlayGraph_reaches_end {P : Piece} (hP : P ∈ overlayPieces pieces points)
    (hz : x = P.1 ∨ x = P.2) :
    (overlayGraph pieces points).Reaches a P.1 ↔ (overlayGraph pieces points).Reaches a x := by
  have hlink : (overlayGraph pieces points).IsLink P P.1 P.2 :=
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  rcases hz with rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h => h.trans (Graph.Reaches.of_isLink hlink),
      fun h => h.trans (Graph.Reaches.of_isLink hlink).symm⟩

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

/-- A preconnected set with two distinct points absorbs finitely many stray points: it cannot
be a closed set together with finitely many extra points, since each extra point would be
clopen in it. -/
theorem subset_of_finite_diff {U C : Set Plane} (hU : IsPreconnected U) (hC : IsClosed C)
    (hfin : (U \ C).Finite) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : U ⊆ C := by
  intro z hz
  by_contra hzC
  -- `D` meets `U` in exactly `U \ {z}`, and it is closed.
  set D : Set Plane := C ∪ ((U \ C) \ {z}) with hD
  have hDclosed : IsClosed D := hC.union ((hfin.subset Set.sdiff_subset).isClosed)
  have hzD : z ∉ D := fun h => h.elim hzC fun h' => h'.2 rfl
  have hmemD : ∀ w ∈ U, w ≠ z → w ∈ D := fun w hw hwz =>
    (em (w ∈ C)).elim Or.inl fun h => Or.inr ⟨⟨hw, h⟩, hwz⟩
  -- `{z}` is clopen in `U`, so `U = {z}` — which two distinct points forbid.
  obtain ⟨w, hwU, hwD, hwz⟩ := hU Dᶜ ({z} : Set Plane)ᶜ hDclosed.isOpen_compl
    isClosed_singleton.isOpen_compl
    (fun w hw => (em (w = z)).elim (fun h => Or.inl (h ▸ hzD)) fun h => Or.inr h)
    ⟨z, hz, hzD⟩
    ((em (a = z)).elim (fun h => ⟨b, hb, fun hbz => hab (h.trans (mem_singleton_iff.1 hbz).symm)⟩)
      fun h => ⟨a, ha, h⟩)
  exact hwD (hmemD w hwU hwz)

end Schoenflies
end

section
-- module Solutions.Q146_CD.AccessibleJoin
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- `a` is **polygonally accessible from `Ω`**: some polygonal chain starts at `a`, ends at a
point of `Ω`, and has all of its points except `a` inside `Ω`.

Stated for a chain rather than for a simple arc; see the module docstring. -/
def PolyAccessible (Ω : Set Plane) (a : Plane) : Prop :=
  ∃ (vs : List Plane) (h : vs ≠ []), vs.head h = a ∧ vs.getLast h ∈ Ω ∧ poly vs \ {a} ⊆ Ω

/-- A straight access segment gives accessibility. This is the form the construction meets:
`z` is an interior point seen from `a` along a segment that only touches the boundary at `a`. -/
theorem PolyAccessible.of_openSegment (hz : z ∈ Ω) (hseg : openSegment ℝ a z ⊆ Ω) :
    PolyAccessible Ω a := by
  refine ⟨[a, z], by simp, rfl, by simpa using hz, ?_⟩
  rw [poly_pair]
  rintro x ⟨hxseg, hxa⟩
  rw [mem_singleton_iff] at hxa
  -- Off the near endpoint, a point of the segment is either the far endpoint or interior to it.
  rcases eq_or_ne x z with rfl | hxz
  · exact hz
  · exact hseg (mem_openSegment_of_ne_left_right (Ne.symm hxa) (Ne.symm hxz) hxseg)

/-- **A strongly accessible point is polygonally accessible.** The straight segment to the
centre of the tangent disk is the access arc. -/
theorem StronglyAccessible.polyAccessible (h : StronglyAccessible Ω a) : PolyAccessible Ω a := by
  obtain ⟨z, hz, -, hseg⟩ := h.openSegment_subset
  exact PolyAccessible.of_openSegment hz hseg

/-! ### `lem:finite-polygonal-union` over a finite family

`Schoenflies.exists_simple_poly_of_union` takes the union as a `List (Set Plane)`. A skeleton
arrives as a finite *set* of edges, so the list is pure friction at the call site. This
paragraph removes it; it belongs in `Schoenflies/SimpleArc.lean`. -/

/-! ### `lem:skeleton-crosscuts`: the extraction step

The blueprint's proof of `lem:skeleton-crosscuts` builds, from a finite stage of the skeleton, a
connected finite union `Y = e_a ∪ |Λ| ∪ e_b` of polygonal arcs with `Y ∩ C = {a, b}`, and then
says: *subdivide `Y` at its finitely many vertices; the resulting finite graph is connected, so
it contains a simple graph path `P` from `a` to `b`, as in the proof of
`lem:finite-polygonal-union`; this path meets `C` only at its endpoints and is therefore a
polygonal crosscut.* That last step is what this paragraph is. The construction of `Y` from the
skeleton needs the stage machinery and is not here. -/

/-! ### `lem:accessible-endpoints` -/

end Schoenflies

/-! ### The extraction on the point set of a finite polygonal plane graph

A skeleton stage arrives as a plane graph, and what the crosscut is extracted from is its point
set. Splitting that into "one singleton per vertex, one arc per edge" is the only step between
`Schoenflies.exists_simple_poly_of_biUnion_finite` and the graph, so it is done once here.

Following the convention of `Schoenflies/Graph/*`, these live in the root `Graph` namespace. -/
end

section
-- module Solutions.Q146_CD.Graph_OuterFace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- A closed axis-parallel square is bounded: it sits inside a Euclidean ball of radius
`√2 · r`, by the norm comparison. -/
theorem isBounded_closedSquare (r : ℝ) :
    Bornology.IsBounded (Schoenflies.Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Schoenflies.Plane.supNorm x ≤ r := by
    simpa [Schoenflies.Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r := by
    refine le_trans (Schoenflies.Plane.norm_le_sqrt_two_mul_supNorm x) ?_
    exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2)
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- Outside a square containing the drawing, every point is in the exterior. -/
theorem beyondSquare_subset_exterior {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) :
    Schoenflies.Plane.beyondSquare r ⊆ exterior G drawing := by
  rw [Schoenflies.Plane.beyondSquare_eq_compl]
  exact compl_subset_compl.2 hr

/-- The outside of a containing square lies wholly inside one face — the face through any of
its points. This is the working form of "there is an outer face". -/
theorem beyondSquare_subset_face {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) {base : Plane}
    (hbase : base ∈ Schoenflies.Plane.beyondSquare r) :
    Schoenflies.Plane.beyondSquare r ⊆ face G drawing base :=
  (Schoenflies.Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
    hbase (beyondSquare_subset_exterior hr)

/-- The outside of a square is unbounded: it contains points of every size. -/
theorem not_isBounded_beyondSquare (r : ℝ) :
    ¬ Bornology.IsBounded (Schoenflies.Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Schoenflies.Plane.exists_closedSquare_of_isBounded hb
  -- A point beyond both radii is in the outside but not in the square that was claimed to
  -- contain it.
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by
    have := le_max_right (max r s) 0; simp only [ht] <;> linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht] <;> linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht] <;> linarith
  -- `Plane.mk t 0` has first coordinate `t` definitionally, so `show` states the real goal.
  have hmem : Schoenflies.Plane.mk t 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin := hs hmem
  simp only [Schoenflies.Plane.closedSquare, mem_setOf_eq, Schoenflies.Plane.supDist_zero,
    Schoenflies.Plane.supNorm, max_le_iff] at hin
  have h1 : |t| ≤ s := hin.1
  rw [abs_of_nonneg ht0] at h1
  linarith

end Graph
end

section
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.IsCycleThrough.cycleGraph_vertexSet _root_.Graph.pathGraphOf_isLink _root_.Graph.pathGraphOf_vertexSet _root_.Graph.vertexSet_union_pathGraphOf
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

/-- **A walk that never visits `x` survives the deletion of `x`.** Its edges need no separate
argument: the two ends of an edge the walk takes are vertices the walk visits. -/
theorem IsWalk.deleteVerts_singleton (h : G.IsWalk u W v) (hx : x ∉ G.walkVertices u W) :
    (G.deleteVerts {x}).IsWalk u W v := by
  have hux : u ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_self)
  refine h.anti deleteVerts_le (mem_deleteVerts_singleton_of_ne h.left_mem hux) fun g hg ↦ ?_
  obtain ⟨c, d, hcd⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  have hc : c ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_left⟩)
  have hd : d ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_right⟩)
  rw [edgeSet_deleteVerts]
  exact ⟨c, d, hcd, by simpa using hc, by simpa using hd⟩

/-- **A walk in `G - x` never takes an edge at `x`** — there are none left to take. -/
theorem IsWalk.notMem_of_inc_of_deleteVerts (h : (G.deleteVerts {x}).IsWalk u W v)
    (hx : G.Inc e x) : e ∉ W := by
  intro he
  have hmem := h.edge_mem he
  rw [edgeSet_deleteVerts] at hmem
  obtain ⟨c, d, hcd, hc, hd⟩ := hmem
  obtain ⟨y, hy⟩ := hx
  rcases hy.left_eq_or_eq hcd with rfl | rfl
  exacts [hc rfl, hd rfl]

/-- The bridge between the two deletions: a walk that routes around a vertex `x` cannot have
used an edge incident to `x`, so it is still there after that edge is deleted. -/
theorem Reaches.deleteEdges_of_deleteVerts (h : (G.deleteVerts {x}).Reaches u v)
    (hx : G.Inc e x) : (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨P, hP⟩ := h
  have he : e ∉ P := hP.notMem_of_inc_of_deleteVerts hx
  exact ⟨P, (hP.mono deleteVerts_le).deleteEdges fun g hg hgF ↦ he (mem_singleton_iff.1 hgF ▸ hg)⟩

/-! ### Cut vertices -/

/-! ### At least three vertices -/

/-! ### Two-connectivity -/

/-! ### The union of two graphs -/

end Graph
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

/-! ### The subgraph induced on a component -/

/-! ### Shortest walks and shortest paths -/

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

/-- A walk of `G - S` visits only vertices of `G` outside `S` — computed in `G`, which is the
form the freshness clause of a path of `G` reads. -/
theorem IsWalk.walkVertices_subset_of_deleteVerts (h : (G.deleteVerts S).IsWalk u W v) :
    G.walkVertices u W ⊆ V(G) \ S := by
  intro z hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨g, hg, hinc⟩
  · simpa using h.left_mem
  -- An edge of the walk survives the deletion, so both of its ends do.
  have hgE := h.edge_mem hg
  rw [edgeSet_deleteVerts] at hgE
  obtain ⟨s, t, hst, hs, ht⟩ := hgE
  rcases hinc.eq_or_eq_of_isLink hst with rfl | rfl
  exacts [⟨hst.left_mem, hs⟩, ⟨hst.right_mem, ht⟩]

/-! ### The two neighbours of a component, and the path through it -/

/-- Reading off the vertices of a walk with one edge appended at the far end. Purely about
lists; used to check the freshness clause when a path inside a component is capped with an
edge back into `S`. -/
theorem mem_walkVertices_append_singleton (hy : y ∈ G.walkVertices u (W ++ [e])) :
    y ∈ G.walkVertices u W ∨ G.Inc e y := by
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with h | ⟨g, hg, hinc⟩
  · exact Or.inl (mem_walkVertices_of_mem_covered h)
  · obtain rfl : g = e := by simpa using hg
    exact Or.inr hinc

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

/-- Pushing the visited set down an inclusion: a subgraph's edges have ends the big graph's
edges have too. This is the direction the freshness clause of a path travels in, and the
whole content of `Graph.IsPath.anti`. -/
theorem coveredVertices_anti (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨e, he, y, hy⟩ ↦ ⟨e, he, y, hy.mono hHG⟩

/-! ### Reaching an end of a path after a deletion -/

/-! ### A graph that is a path -/

/-! ### Constructing a path graph -/

theorem mem_vertexSet_pathGraphOf_self : u ∈ V(G.pathGraphOf u W) := mem_walkVertices_self

/-- The spanned subgraph visits the same vertices as the ambient graph does along `W`: its
edges are the same edges, joining the same pairs. No walk is needed — an end of an edge of
`W` is visited by definition, so it survives the induced subgraph. -/
theorem coveredVertices_pathGraphOf :
    (G.pathGraphOf u W).coveredVertices W = G.coveredVertices W := by
  refine Set.Subset.antisymm (fun z ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, (pathGraphOf_isLink.1 hy).2.1⟩)
    fun z ⟨f, hf, y, hy⟩ ↦ ?_
  · exact ⟨f, hf, y, pathGraphOf_isLink.2 ⟨hf, hy,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_left⟩,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_right⟩⟩⟩

theorem walkVertices_pathGraphOf :
    (G.pathGraphOf u W).walkVertices u W = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_pathGraphOf]

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Ear
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- **One edge swapped for any route between its ends.** If every edge of `G` other than `e`
links the same pair in `H`, and whatever `e` links in `G` is joined in `H` by some other
means, then `H` reaches whatever `G` reaches: a walk that took `e` takes the replacement route
instead.

The premise about `e` is universally quantified over its ends rather than stated for a named
pair, so that it is *vacuous* when `e` is not an edge of `G` — which is the case a vertex
deletion produces, and the reason this is the shape that gets used. -/
theorem Reaches.reroute (hV : V(G) ⊆ V(H))
    (hE : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → H.IsLink g p q)
    (hends : ∀ ⦃p q⦄, G.IsLink e p q → H.Reaches p q)
    (h : G.Reaches s t) : H.Reaches s t := by
  obtain ⟨R, hR⟩ := h
  induction hR with
  | nil hx => exact Reaches.refl (hV hx)
  | @cons p w q g R hl _ ih =>
    -- Either this step took the replaced edge, or it survives verbatim.
    refine Reaches.trans ?_ ih
    by_cases hg : g = e
    · exact hends (hg ▸ hl)
    · exact Reaches.of_isLink (hE hl hg)

/-- **The form a subdivision needs.** A walk of `G - c` transfers to any graph holding the
surviving edges, provided the replaced edge's ends are joined there *or* that edge was
incident to the deleted vertex — in which case no walk of `G - c` could have taken it, and the
`hends` premise of `Graph.Reaches.reroute` is vacuous.

That disjunction is the blueprint's three-way case analysis: route along the replacement,
route around the old graph, or do not route at all. -/
theorem Reaches.across_edge_replacement (hV : V(G.deleteVerts {c}) ⊆ V(H))
    (hl : G.IsLink e u v)
    (hE : ∀ ⦃g p q⦄, (G.deleteVerts {c}).IsLink g p q → g ≠ e → H.IsLink g p q)
    (routed : H.Reaches u v ∨ G.Inc e c)
    (h : (G.deleteVerts {c}).Reaches s t) : H.Reaches s t := by
  refine Reaches.reroute (e := e) hV hE (fun p q hpq ↦ ?_) h
  rw [deleteVerts_isLink] at hpq
  obtain ⟨hpq, hp, hq⟩ := hpq
  have hpc : p ≠ c := fun hh ↦ hp (by simp [hh])
  have hqc : q ≠ c := fun hh ↦ hq (by simp [hh])
  rcases routed with hr | ⟨w, hw⟩
  · -- The ends are joined in `H`; the step ran between them, one way or the other.
    rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hr, hr.symm]
  · -- The edge met the deleted vertex, so `G - c` does not have it: nothing to prove.
    rcases hw.left_eq_or_eq hpq with hh | hh
    exacts [(hpc hh.symm).elim, (hqc hh.symm).elim]

/-! ### Attaching an ear -/

/-! ### Replacing an edge by a path -/

/-! ### Finding an ear -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Tree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A walk that gets anywhere leaves along an edge at its source. -/
theorem IsWalk.exists_inc_source (h : G.IsWalk u W v) (hW : W ≠ []) : ∃ e ∈ W, G.Inc e u := by
  cases h with
  | nil => exact absurd rfl hW
  | cons hl _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-- An edge of a path incident with the path's source is the one the path departs along. -/
theorem IsPath.eq_head_of_inc_source (h : G.IsPath u (e :: W) v) (hf : f ∈ e :: W)
    (hinc : G.Inc f u) : f = e := by
  cases h with
  | cons hl hW hfresh =>
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hfresh

/-- **A path has at most one edge at its source.** -/
theorem IsPath.inc_source_unique (h : G.IsPath u P v) (hf : f ∈ P) (he : e ∈ P)
    (hfi : G.Inc f u) (hei : G.Inc e u) : f = e := by
  cases P with
  | nil => simp at hf
  | cons a t => rw [h.eq_head_of_inc_source hf hfi, h.eq_head_of_inc_source he hei]

/-! ### A longest path -/

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
-- module Solutions.Q146_CD.Subarc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

variable {a b : ℝ}

/-! ### Subarcs -/

variable {f : ℝ → Plane}

/-! ### The arc without its endpoints -/

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-! ### A parametrisation is an open map onto its arc -/

/-! ### The subarc basis -/

/-- **Every neighbourhood of a point of the arc contains the image of an open subinterval
around its parameter.** With `image_isRelOpen`, which says those images are relatively open,
this makes them a basis of the arc's subspace topology.

The piece is the parameter interval cut by an interval around the parameter, which is
half-open exactly when the point is an endpoint. -/
theorem basic_piece_inside_ball (hc : ContinuousOn f I) {x : Plane} (hx : x ∈ f '' I)
    {r : ℝ} (hr : 0 < r) :
    ∃ c d : ℝ, x ∈ f '' (Ioo c d ∩ I) ∧ f '' (Ioo c d ∩ I) ⊆ Metric.ball x r := by
  obtain ⟨s, hs, rfl⟩ := hx
  -- Continuity at the parameter turns the prescribed radius into a parameter radius.
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc s hs) r hr
  refine ⟨s - δ, s + δ, ⟨s, ⟨⟨by linarith, by linarith⟩, hs⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht, htI⟩, rfl⟩
  have : dist t s < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact Metric.mem_ball.mpr (hclose htI this)

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-- A cycle with at least three vertices — the blueprint's "cycle of length at least three".
The third vertex is named rather than counted, because that is what both consumers want. -/
structure IsLongCycle (G : Graph α β) (e : β) (u v : α) (D : List β) (w : α) : Prop where
  /-- The edge and the detour form a cycle. -/
  isCycle : G.IsCycleThrough e u v D
  /-- The detour visits a third vertex … -/
  mem : w ∈ G.walkVertices u D
  /-- … distinct from the source of the edge … -/
  ne_left : w ≠ u
  /-- … and from its target. -/
  ne_right : w ≠ v

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem isPath : G.IsPath u D v := h.isCycle.isPath

end IsLongCycle

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

/-- **A path graph grows with its edge list.** General, and not in
`Schoenflies/Graph/PathGraph.lean`; the integrator may want to hoist it. -/
theorem pathGraphOf_mono (h : W ⊆ D) : G.pathGraphOf u W ≤ G.pathGraphOf u D where
  vertexSet_mono := by
    simpa only [pathGraphOf_vertexSet] using walkVertices_mono (u := u) h
  isLink_mono := by
    intro f x y hl
    obtain ⟨hf, hxy, hx, hy⟩ := pathGraphOf_isLink.1 hl
    exact pathGraphOf_isLink.2
      ⟨h hf, hxy, walkVertices_mono h hx, walkVertices_mono h hy⟩

/-- The detour spans a path subgraph of the cycle. -/
theorem pathGraphOf_le_cycleGraph : G.pathGraphOf u D ≤ G.cycleGraph u e D :=
  pathGraphOf_mono (List.subset_append_left _ _)

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem mem_cycleGraph : w ∈ V(G.cycleGraph u e D) := by
  rw [h.isCycle.cycleGraph_vertexSet]; exact h.mem

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

/-- **An edge of a path incident to its source is the path's first edge**, in the form that
decomposes the path — `Graph.IsPath.eq_head_of_inc_source` says the same about a list already
known to be a cons, and is what does the work here. -/
theorem IsPath.eq_cons_of_inc_left (h : G.IsPath u D v) (hg : g ∈ D) (hinc : G.Inc g u) :
    ∃ w T, D = g :: T ∧ G.IsLink g u w ∧ G.IsPath w T v := by
  cases D with
  | nil => simp at hg
  | cons a T =>
    obtain rfl : g = a := h.eq_head_of_inc_source hg hinc
    cases h with
    | cons hl hT _ => exact ⟨_, T, rfl, hl, hT⟩

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutCells
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

open Bornology Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

theorem mem_inside_iff : x ∈ inside C ↔ x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x) := Iff.rfl

/-! ### Definition 2.4: a separating Jordan curve -/

namespace IsSeparating

/-- The inside is bounded: it is connected and lies inside the complement, hence inside the
component of any of its points, which is bounded by definition of `inside`. -/
theorem isBounded_inside (h : IsSeparating C) : IsBounded (Schoenflies.inside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_inside.nonempty
  exact hz.2.subset
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hz inside_subset_compl)

/-- The outside is unbounded: it contains an unbounded component. -/
theorem not_isBounded_outside (h : IsSeparating C) : ¬ IsBounded (Schoenflies.outside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_outside.nonempty
  exact fun hb => hz.2 (hb.subset (connectedComponentIn_subset_outside hz))

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-! ### Lemma 2.5: absorption -/

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-- The two curves of Lemma 2.6 are Jordan curves: an arc from `p` to `q` and a second arc from
`p` to `q` meeting it only at those two points glue to a Jordan curve. -/
theorem isJordanCurve_union (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hmeet : ∀ z ∈ A, z ∈ P → z = p ∨ z = q) : IsJordanCurve (A ∪ P) :=
  IsJordanCurve.of_two_arcs hA hP.reverse hmeet

/-- Lemma 2.6 (b), arc side: the two arcs of `C` from `p` to `q` are distinct, because they
meet only at `p` and `q` while neither is just `{p, q}`. -/
theorem arcs_ne (hmeet : A₁ ∩ A₂ ⊆ {p, q}) (hA : ¬ A₁ ⊆ {p, q}) : A₁ ≠ A₂ := by
  rintro rfl
  exact hA fun z hz => hmeet ⟨hz, hz⟩

/-! ### Lemma 2.6, bundled -/

/-- **Lemma 2.6 (crosscut cells).** Let `C` be a separating curve with regions `Ω` and `Ω'`,
let `A₁, A₂ ⊆ C` be the two arcs cut out by a crosscut `P` which meets `C` only in points of
both arcs, and suppose the two curves `Jᵢ = Aᵢ ∪ P` are separating. Let `Wᵢ` be the region of
`ℝ² ∖ Jᵢ` containing `Ω'` and `Vᵢ` the other one. Then

* (a) each `Vᵢ` is a connected component of `Ω ∖ P`;
* (b) `V₁ ≠ V₂`;
* (c) `closure Vᵢ ∩ C = Aᵢ`.

The blueprint proves (b) from the boundaries; here it falls straight out of (c), since
`V₁ = V₂` would make `A₁ = A₂`. -/
theorem crosscut_cells (hC : IsSeparating C)
    (hJ₁ : IsSeparating (A₁ ∪ P)) (hJ₂ : IsSeparating (A₂ ∪ P))
    (hA₁ : A₁ ⊆ C) (hA₂ : A₂ ⊆ C) (hP₁ : P ∩ C ⊆ A₁) (hP₂ : P ∩ C ⊆ A₂) (hne : A₁ ≠ A₂)
    (hΩ : IsRegionPair C Ω Ω')
    {W₁ V₁ W₂ V₂ : Set Plane}
    (hWV₁ : IsRegionPair (A₁ ∪ P) W₁ V₁) (hΩW₁ : Ω' ⊆ W₁)
    (hWV₂ : IsRegionPair (A₂ ∪ P) W₂ V₂) (hΩW₂ : Ω' ⊆ W₂) :
    (V₁ ⊆ Ω \ P ∧ ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (V₂ ⊆ Ω \ P ∧ ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      V₁ ≠ V₂ ∧ closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  -- The two inclusions that replace the arc hypotheses.
  have hPJ : ∀ A : Set Plane, P ⊆ A ∪ P := fun A => Set.subset_union_right
  have hJCP : ∀ {A : Set Plane}, A ⊆ C → A ∪ P ⊆ C ∪ P := fun hA =>
    Set.union_subset_union_left P hA
  -- (c): `(Aᵢ ∪ P) ∩ C = Aᵢ`, since `Aᵢ ⊆ C` and `P ∩ C ⊆ Aᵢ`.
  have hinter : ∀ {A : Set Plane}, A ⊆ C → P ∩ C ⊆ A → (A ∪ P) ∩ C = A := by
    intro A hAC hPC
    refine Set.Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hAC hz⟩
    rintro z ⟨hz | hz, hzC⟩
    · exact hz
    · exact hPC ⟨hz, hzC⟩
  have hc₁ : closure V₁ ∩ C = A₁ := by
    rw [closure_cell_inter_curve hC hJ₁ hΩ.right hWV₁ hΩW₁]; exact hinter hA₁ hP₁
  have hc₂ : closure V₂ ∩ C = A₂ := by
    rw [closure_cell_inter_curve hC hJ₂ hΩ.right hWV₂ hΩW₂]; exact hinter hA₂ hP₂
  refine ⟨⟨cell_subset_region_diff hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁),
      cell_isComponent hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁) (hJCP hA₁)⟩,
    ⟨cell_subset_region_diff hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂),
      cell_isComponent hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂) (hJCP hA₂)⟩, ?_, hc₁, hc₂⟩
  -- (b): equal cells would have equal closures, hence equal arcs.
  rintro rfl
  exact hne (hc₁.symm.trans hc₂)

end Schoenflies
end

section
-- module Solutions.Q146_CD.Strip
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two-sided polygonal strips

This module builds the *collar* of Lemma 1.8: an open neighbourhood `N` of a simple closed
polygon `P` whose complement in `N` splits into two connected open sets, the two local sides.

The blueprint's construction is "a small closed disk about every vertex, a thin rectangular
block about every edge, chosen so that consecutive blocks overlap and nonadjacent closures are
disjoint". The blocks here are

* `Plane.cone v A R` — the open sector of radius `R` about a vertex `v` cut out by an arc `A`
  of directions, and
* `Plane.strip a u t₁ t₂ s₁ s₂` — the open rectangle around a directed edge, written in the
  edge's own coordinates `t = ⟪u, x - a⟫` (along) and `s = det u (x - a)` (across).

Everything about the *side matching at a vertex* comes from `Schoenflies/Direction.lean`
through the orientation form; no angle is named. The one new direction fact needed here is the
sign-free repackaging `Plane.germs_split'`: the blueprint's `germs_split` assumes
`0 < det r₁ r₂`, but a polygon turns both ways, and it turns out that *which* named arc carries
the left germs does not depend on the sense of the turn — it is always `arcCCW r₂ r₁`. Only the
side of the smallness hypothesis moves.

## The constants

The blueprint says "the blocks may be chosen so that consecutive edge and vertex blocks overlap
in the prescribed small rectangles around the radial segments, while the closures of all
nonadjacent blocks are disjoint" without naming the constants. `Schoenflies.StripData` names
them: a cone radius `R`, a trim `lam` by which each edge block stops short of its endpoints, and
a half-width `rho`. They should be chosen in this order (this is the recipe the unproved
`exists_stripData` has to follow):

1. `R` from the vertex separations, from the distance of each vertex to the nonincident edges
   (with a factor `2` of slack, spent in `dist_core_vertex`), and from the prescribed open set;
2. `lam := R / 5`, which makes `2 * lam < R` (the cones reach past the ends of the blocks they
   must overlap) and `4 * lam < ‖edge‖` (the blocks are nonempty);
3. `rho` from the distance of each trimmed edge to the other edges, and from the *germ
   threshold* `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex — this last is the
   quantitative form of "make the strips narrow enough that this side matching holds in every
   vertex disk", and it is the only inequality in the list that is not a separation of compact
   sets.

## Blueprint

* `Plane.germs_split'` — the sign-free vertex matching inside Lemma 1.8.
* `Schoenflies.ClosedPolygon` — a simple closed polygonal curve presented by its cyclic vertex
  list.
* `Schoenflies.StripData` — the choice of constants, as a hypothesis.
* `Schoenflies.StripData.sideL`, `.sideR`, `.nbhd`, `.sideL_disjoint_sideR` — the two labelled
  sides of the collar, and that they are disjoint.

## Where the rest of Lemma 1.8 lives

This module builds the apparatus and proves the hard half: the germ matching at a corner and
the disjointness of the two labelled sides. The other two obligations are discharged next door,
and were split out only because they were built concurrently:

* `Schoenflies/StripConstants.lean` — `exists_stripData` and `exists_stripData_subset`, which
  produce the constants, the latter with the collar inside a prescribed open set.
* `Schoenflies/StripConnected.lean` — that each side is connected, and
  `nbhd \ carrier = sideL ∪ sideR`.

`Schoenflies.polygonal_collar` in `Schoenflies/Compose.lean` is the three composed into the
blueprint's Lemma 1.8 (a). `ClosedPolygon.collar` below is a *definition*, not the theorem.

What is still missing from Lemma 1.8 as a whole: the **local two-sidedness** clause (every
sufficiently small disk about a point of the curve meets the complement in exactly two
components, one in each side), and part **(b)**, the arc case.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {u w d r₁ r₂ a x : Plane} {r t s c ρ : ℝ}

/-! ### A sign-free vertex matching

`Plane.germs_split` fixes the orientation with `0 < det r₁ r₂`. A polygon turns both ways, so
the collar needs the statement without that hypothesis. The content of the repackaging is that
the *conclusion* does not move: the two left germs always land on `arcCCW r₂ r₁` and the two
right germs on `arcCCW r₁ r₂`. What moves is which pair needs the smallness hypothesis, so the
sign-free form simply imposes it on both, with absolute values. -/

/-! ### The two arcs, without a sign hypothesis -/

/-! ### Vertex sectors

The "small closed disk about a vertex" of the blueprint is replaced by an open *sector*: the
part of a ball about the vertex lying in a prescribed arc of directions. The two sectors cut out
by the two arcs are exactly the two components of the ball minus the two incident radial
segments, which is what makes the labelling at a vertex well defined. -/

/-! ### Edge blocks

The block around a directed edge is described in the edge's own frame: `coordAlong` is the
progress along the edge and `coordAcross` the signed distance to its line. Both are affine, so
the block is an intersection of four open half-planes — open and convex at a glance. -/

theorem mem_strip_param (hu : IsDirection u) (a : Plane) {t s t₁ t₂ s₁ s₂ : ℝ} :
    a + t • u + s • perp u ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < t ∧ t < t₂ ∧ s₁ < s ∧ s < s₂ := by
  rw [mem_strip_iff, coordAlong_param hu, coordAcross_param hu]

end Plane

/-! ## Simple closed polygons

A polygon is presented by its cyclic vertex list. Indexing by `ZMod (m + 3)` builds in both the
cyclic successor and the requirement that there are at least three vertices, and it makes
`NeZero` available without a side hypothesis. -/

open Plane

/-! ## The constants

`StripData` is the blueprint's "choose the blocks so that consecutive ones overlap and
nonadjacent closures are disjoint", with every constant named. The three numbers are a cone
radius `R`, a trim `lam` and a half-width `rho`; the separation hypotheses are exactly the
instances of Lemma 1.4 (b) that the construction consumes, and `germ` is the vertex-matching
threshold. Producing them is the unproved `exists_stripData`; see the Status section. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.ParitySplitting
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Parity splitting: a crosscut adds the two crossing counts

Lemma 2.7. A crosscut `P` of a simple closed polygon `C` cuts it into two arcs `A₁, A₂`, and
the two closed curves `Jᵢ = Aᵢ ∪ P` satisfy `π_C = π_{J₁} + π_{J₂}` off `C ∪ P`. The blueprint
calls this identity "the whole of the polygonal crosscut theorem": Lemma 2.6 exhibits two cells
of `Ω ∖ P`, and this is what says there are no others.

## Where the split is made, and why

The crossing count of `Schoenflies/Parity.lean` is a function of a `List Piece`, not of a set,
and not of a `ClosedPolygon`. Two edge lists with the same carrier can have different parity —
a list that traverses one segment twice is the obvious example — so the identity cannot be
stated for the sets `Aᵢ ∪ P`. It is stated, and proved, for **edge lists**:

    the edge list of `C` is `A₁ ++ A₂`, that of `Jᵢ` is `Aᵢ ++ K`,

where `K` is the edge list of the crosscut. Then `π_{J₁} + π_{J₂} = π_{A₁} + π_{A₂} + 2 π_K`
and the crosscut's contribution cancels mod `2`. That is `parity_split`, and it needs no
geometry at all — no simplicity, no direction, no separation. Everything the blueprint's
picture contributes is in the *hypothesis* that the lists decompose that way.

Two mismatches between "the edge list of `Jᵢ` is `Aᵢ` together with `K`" and literal list
equality have to be absorbed, because a consumer building `Jᵢ` as a `ClosedPolygon` controls
neither:

* the edges come in some cyclic order of that polygon's own choosing, and
* one of the two curves must traverse the crosscut backwards, so its pieces are the *reversed*
  pairs.

`SameEdges` is the equivalence that forgives exactly these two: a permutation of the lists
after each piece has been put in canonical order by `Schoenflies.orientPiece`. Parity, carrier,
closedness and non-levelness are all invariant under it (`SameEdges.parity_eq`,
`SameEdges.cover_eq`, `SameEdges.isChainFrom`, `SameEdges.hgt_ne`), so a consumer may hand over
its edge list in whatever order and orientation it happens to have —
`sameEdges_of_perm_reverse_swap` absorbs both mismatches in one step.

Nothing is assumed about the *sets*: `ClosedPolygon.carrier_eq_of_sameEdges` derives
`Jᵢ.carrier = Aᵢ ∪ P` from the edge lists alone, so the geometric hypothesis a consumer has to
discharge is only ever combinatorial.

## The construction

`ClosedPolygon.arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and
runs forward through `k` edges — the object the split produces, exported as an object rather
than hidden behind an existential. Its two governing facts are

* `ClosedPolygon.arcPieces_split_perm`: `arcPieces C a k ++ arcPieces C (a + k) (m + 3 - k)` is
  a permutation of `C.pieces` — the arcs really do partition the edges; and
* `ClosedPolygon.isChainFrom_arcPieces`: the arc's mod-`2` boundary is its two end vertices,
  which is what makes `Aᵢ ++ K` a *closed* chain and hence eligible for every parity theorem.

`IsChainFrom` is the open-path companion of `Schoenflies.IsClosedChain`, stated by the same
duality; `IsChainFrom.isClosedChain_append` is the one-line reason that an arc and a crosscut
with the same two ends close up. `pathPieces` turns a polyline into such a chain, which is how
the crosscut itself is normally presented.

The endpoints of the crosscut are taken to be **vertices** of `C`; the blueprint's opening
move, "subdivide `C` at `p` and `q`", is what puts them there, and is `parity_subdivide`
(Lemma 2.1) applied before any of this. Nothing below re-proves it. A consumer whose crosscut
lands in the interiors of edges rewrites with `parity_subdivide` first and then applies
`parity_split` to the subdivided list, whose hypotheses are about lists and not about polygons;
what such a consumer must supply for itself is the decomposition of the *subdivided* list into
two arcs, which `arcPieces` does not provide — `arcPieces` splits `C.pieces` at vertices.

## Blueprint

* `SameEdges`, `IsChainFrom`, `pathPieces`, `ClosedPolygon.arcPieces` — the definition of the
  split. "After the subdivision the edge set of `C` is the disjoint union of the edge sets of
  `A₁` and `A₂`, and the edge set of `Jᵢ` is that of `Aᵢ` together with that of `P`."
* `parity_split`, `ClosedPolygon.parity_splitting` — Lemma 2.7, equation (2.2)
  `π_C = π_{J₁} + π_{J₂}`.
* `ClosedPolygon.crosscut_inside_exactly_one`, `ClosedPolygon.crosscut_outside_agree` — the
  "Consequently" of Lemma 2.7, which is where Theorem 2.3 enters: a point of `Int(C)` off `P`
  lies inside exactly one of `J₁, J₂`, and a point of `Ext(C)` off `P` lies inside both or
  inside neither.
* `ClosedPolygon.parity_eq_one_iff` — the two halves of the last sentence of Theorem 2.3, read
  as a single criterion.
* `ClosedPolygon.carrier_eq_of_sameEdges`, `ClosedPolygon.notMem_carrier_of_sameEdges` — the
  bridge back to the sets: `Jᵢ` occupies `Aᵢ ∪ P`, so "off `C` and off `P`" is "off `Jᵢ`".

One lemma here strengthens one on `main`: `mark_swap'` drops the non-levelness hypothesis of
`Schoenflies.mark_swap`, because a level edge is crossed from nowhere and so contributes `0`
under either name. Its home is `Schoenflies/Parity.lean`.
-/

open Metric Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

/-! ## Edge lists up to order and orientation

Parity, carrier and closedness are all functions of the *multiset of unoriented* edges. This
section says so, so that a consumer may present the edge list of a curve in any order and with
either name for each edge. -/

/-! ## Chains with two ends

`Schoenflies.IsClosedChain` says the mod-`2` boundary of an edge list vanishes. An arc and a
crosscut are not closed; each has a boundary, namely its two ends, and closing them up is the
statement that the two boundaries agree. Stated by the same duality as `IsClosedChain`, so that
the two definitions compose with nothing but `List.sum_append`. -/

/-- `L` is a **chain from `p` to `q`**: its mod-`2` boundary is `p` together with `q`. Stated by
duality, exactly as `Schoenflies.IsClosedChain` is. -/
def IsChainFrom (L : List Piece) (p q : Plane) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map fun P => f P.1 + f P.2).sum = f p + f q

/-- A chain whose two ends coincide is a closed chain, and conversely. -/
theorem isChainFrom_self_iff : IsChainFrom L p p ↔ IsClosedChain L := by
  constructor <;> intro h f
  · rw [h f]; exact add_self_zmod_two _
  · rw [h f]; exact (add_self_zmod_two _).symm

theorem isChainFrom_nil (p : Plane) : IsChainFrom [] p p := fun f => by
  simp [(add_self_zmod_two (f p)).symm]

/-- Chains compose end to end. -/
theorem IsChainFrom.append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ q r) :
    IsChainFrom (L₁ ++ L₂) p r := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  linear_combination add_self_zmod_two (f q)

/-- **Two chains with the same two ends close up.** This is the whole reason `Aᵢ ∪ P` is a
closed curve as far as the crossing count is concerned. -/
theorem IsChainFrom.isClosedChain_append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ p q) :
    IsClosedChain (L₁ ++ L₂) := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  exact add_self_zmod_two _

/-! ### The edges of a polyline

How a crosscut is normally presented: a list of points. `pathPieces` reads off its edges, and
`isChainFrom_pathPieces` says its boundary is the two ends of the list. -/

/-! ## The two arcs of a polygon

`arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and runs forward
through `k` edges. Its two ends are vertices `a` and `a + k`, and for `k ≤ m + 3` the two arcs
`arcPieces C a k` and `arcPieces C (a + k) (m + 3 - k)` between them use each edge of `C`
exactly once. -/

/-! ## The identity

Everything above was the definition. The identity itself is one line of `ZMod 2` arithmetic:
the crosscut is counted once in each of `π_{J₁}` and `π_{J₂}`, so its contribution cancels. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolygonalCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Theorem 2.8: two-sided polygonal crosscuts

A crosscut `P` of a simple closed polygon `C` cuts one of the two regions of `ℝ² ∖ C` into
exactly two, bounded by the two curves `Jᵢ = Aᵢ ∪ P`; and `ℝ² ∖ (C ∪ P)` then has exactly three
regions, with boundaries `C, J₁, J₂`.

## One theorem, not two

The blueprint splits the statement into case (a), the crosscut inside `C`, and case (b), the
crosscut outside. The two cases differ only in *which* region of `ℝ² ∖ Jᵢ` is the new cell: in
case (a) it is `Int(Jᵢ)` for both `i`, while in case (b) it is `Ext(J₁)` for one index and
`Int(J₂)` for the other, and which is which is not determined by the data. What *is* uniform is
the description "the region of `ℝ² ∖ Jᵢ` on the far side from a point `y` of the region of
`ℝ² ∖ C` that the crosscut does not enter". So the whole theorem is proved once, for

    farRegion J y  =  the region of `ℝ² ∖ J` that does not contain `y`,

and the two cases of the blueprint are then read off by identifying `farRegion` with `inside`
or with `outside` (`IsSeparating.farRegion_eq_inside`, `…_eq_outside`). A reference point `y`
in the untouched region is the one extra datum this costs, and it is exactly the datum the
blueprint hides in the phrase "let `Ω` be the region containing `P ∖ {p, q}`".

## Exhaustion is pure parity, in both cases at once

Lemma 2.6 (`Schoenflies.crosscut_cells`) already exhibits the two cells as components of
`Ω ∖ P`. All that Theorem 2.8 adds is that there are no others, and the blueprint reads this
off Lemma 2.7. Here the reading is uniform. Write `πJ` for the crossing count of a curve `J`.
For points `x, y` off `J` — Theorem 2.3 —

    `x` and `y` lie in different regions of `ℝ² ∖ J`  ↔  `πJ(x) ≠ πJ(y)`,

which is `ClosedPolygon.parity_ne_iff_mem_farRegion`. Lemma 2.7 gives
`πJ₁ + πJ₂ = πC` at every point, so subtracting the identity at `y` from the identity at `x`
turns "`x` is separated from `y` by `C`" into "`x` is separated from `y` by exactly one of
`J₁, J₂`" — `IsPolygonalCrosscut.separates_xor`, whose entire proof is sixteen cases of `ZMod 2`
arithmetic. No case distinction on inside/outside is made anywhere.

## The hypotheses, bundled

`IsPolygonalCrosscut C J₁ J₂ K a k y` collects the seven hypotheses of the theorem: the two
curves of the split carry the right edges (`Schoenflies.SameEdges`, from Lemma 2.7), the
crosscut meets `C` only in points common to both arcs, and the reference point `y` lies off `C`
in a region the crosscut does not enter. It is closed under swapping the two arcs
(`IsPolygonalCrosscut.symm`), which is why every statement below is proved for index `1` only.

Realizing `J₁` and `J₂` as `ClosedPolygon`s is the consumer's job, exactly as in Lemma 2.7 —
see the note there about the `corner` field. Nothing in this file inspects `corner`.

## Blueprint

* `farRegion`, `IsSeparating.isRegionPair_farRegion`, `IsSeparating.farRegion_eq_inside`,
  `IsSeparating.farRegion_eq_outside` — the blueprint's `Ω`, `Ω†`, `Vᵢ` and `Wᵢ` named as
  functions of a reference point instead of by an existential.
* `ClosedPolygon.arc` — the arcs `A₁, A₂` of Theorem 2.8, as sets; `…vertex_mem_arc`,
  `…vertex_add_mem_arc`, `…endpoints_subset_arc`, `…endpoints_subset_arc'` — the two cut
  vertices lie on both arcs, which is what "the crosscut meets `C` only in its endpoints" has
  to say to be usable.
* `ClosedPolygon.parity_ne_iff_mem_farRegion` — Theorem 2.3 read as a separation criterion.
* `IsPolygonalCrosscut` — the hypotheses of Theorem 2.8; `IsPolygonalCrosscut.of_endpoints` is
  the constructor a consumer should use, and `IsPolygonalCrosscut.symm` swaps the two arcs.
* `IsPolygonalCrosscut.separates_xor` — Lemma 2.7's "consequently", in the uniform form.
* `IsPolygonalCrosscut.region_eq`, `…cells_disjoint`, `…cells_ne`, `…cell_isComponent₁/₂`,
  `…frontier_cell₁/₂`, `…closure_cell_inter₁/₂` — the two cells of `Ω ∖ P`.
* `IsPolygonalCrosscut.inside_diff_eq` — Theorem 2.8(a).
* `IsPolygonalCrosscut.outside_diff_eq`, `…inside_exactly_one` — Theorem 2.8(b).
* `IsPolygonalCrosscut.compl_eq`, `…isComponent`, `…near_isComponent`,
  `…cell_isComponent_compl₁/₂`, `…cell_ne_near₁/₂`, `…frontier_near` — "in either case
  `ℝ² ∖ (C ∪ P)` has exactly three regions, with boundaries `C, J₁, J₂`".
* `polygonal_crosscut` — Theorem 2.8, bundled.
-/

open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

/-! ## The region on the far side of a point

The blueprint names the four regions in play — `Ω`, `Ω†`, `Wᵢ`, `Vᵢ` — by their relation to one
another: `Ω†` is the region of `ℝ² ∖ C` the crosscut does not enter, and `Vᵢ` is the region of
`ℝ² ∖ Jᵢ` on the other side of `Jᵢ` from `Ω†`. Fixing a point `y ∈ Ω†` turns all four into
functions of the data. -/

theorem IsSeparating.isRegionOf_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionOf C (farRegion C y) := (hC.isRegionPair_farRegion hy).right

/-! ## The three regions of `ℝ² ∖ (C ∪ P)`, abstractly

Lemma 2.6 places the two cells inside `Ω ∖ P`; the last paragraph of the proof of Theorem 2.8
places all three regions inside `ℝ² ∖ (C ∪ P)`, and the argument is the same each time: an open
connected set whose frontier misses the ambient open set is a component of it (Lemma 1.7). -/

/-! ## The arcs of a polygon, and parity as a separation criterion -/

/-! ## The hypotheses of Theorem 2.8 -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.TwoArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- Two parameters short of the finish carrying the same point are equal. This is `IsLoop.injOn`
with the half-open interval spelled as "in `[0,1]` and not `1`", which is the form every use
below produces. -/
theorem injective_before_finish (hf : IsLoop f) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (h : f u = f v) : u = v :=
  hf.injOn ⟨hu.1, hu.2.lt_of_ne hu1⟩ ⟨hv.1, hv.2.lt_of_ne hv1⟩ h

/-- **Every point of the curve has a parameter short of the finish.** A parameter at the finish
is replaced by the start, which carries the same point. This is the only use the closing
condition gets. -/
theorem parameter_before_finish (hf : IsLoop f) {p : Plane} (hp : p ∈ f '' I) :
    ∃ u ∈ I, u ≠ 1 ∧ f u = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  rcases eq_or_ne u 1 with rfl | hu1
  · exact ⟨0, zero_mem_I, one_ne_zero.symm, hf.closes⟩
  · exact ⟨u, hu, hu1, rfl⟩

/-- The start and the finish are the same point of the curve; recorded in the direction the
proofs below read it. -/
theorem finish_eq_start (hf : IsLoop f) : f 1 = f 0 := hf.closes.symm

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

/-- Injectivity on the front piece: no parameter of `[0, s]` is the finish, because `s` is
not. -/
theorem injective_on_front (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) : InjOn f (Icc 0 s) := by
  have hs' : s < 1 := hs.2.lt_of_ne hs1
  intro u hu v hv h
  exact hf.injective_before_finish (front_subset_I hs hu) (front_subset_I hs hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 hs')) (ne_of_lt (lt_of_le_of_lt hv.2 hs')) h

/-- Injectivity on the middle piece: no parameter of `[s, t]` is the finish, because `t` is
not. -/
theorem injective_on_middle (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1) :
    InjOn f (Icc s t) := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  intro u hu v hv h
  exact hf.injective_before_finish (middle_subset_I hs ht hu) (middle_subset_I hs ht hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 ht')) (ne_of_lt (lt_of_le_of_lt hv.2 ht')) h

/-- On the back piece the finish is the *only* parameter carrying `f 1`. A second one would be
the start, by injectivity off the finish and the closing condition — but the start lies
strictly before `t`. -/
theorem back_at_finish (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) {w : ℝ} (hw : w ∈ Icc t 1)
    (h : f w = f 1) : w = 1 := by
  by_contra hw1
  have : w = 0 :=
    hf.injective_before_finish (back_subset_I ht hw) zero_mem_I hw1 one_ne_zero.symm
      (h.trans hf.finish_eq_start)
  exact absurd (this ▸ hw.1) (not_le.mpr ht0)

/-- Injectivity on the back piece. Unlike the other two this piece contains the finish, so
injectivity off the finish is not enough on its own; `back_at_finish` supplies the rest. -/
theorem injective_on_back (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) : InjOn f (Icc t 1) := by
  intro u hu v hv h
  rcases eq_or_ne u 1 with rfl | hu1
  · exact (hf.back_at_finish ht ht0 hv h.symm).symm
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hf.back_at_finish ht ht0 hu h
    · exact hf.injective_before_finish (back_subset_I ht hu) (back_subset_I ht hv) hu1 hv1 h

/-! ### The three pieces are arcs -/

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-- The back and front pieces meet only where the loop closes up. A point on both comes from a
parameter at or past `t` and from one at or before `s`; two distinct parameters short of the
finish cannot carry the same point, and `t ≤ s` is false, so the back parameter is the
finish. -/
theorem back_meet_front (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1) (hst : s < t)
    {z : Plane} (hzb : z ∈ f '' Icc t 1) (hzf : z ∈ f '' Icc 0 s) : z = f 1 := by
  obtain ⟨b, hb, rfl⟩ := hzb
  obtain ⟨a, ha, hab⟩ := hzf
  have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
  rcases eq_or_ne b 1 with rfl | hb1
  · rfl
  · -- Otherwise both parameters are short of the finish, so they coincide — impossible,
    -- since one is at least `t` and the other at most `s < t`.
    have : b = a :=
      hf.injective_before_finish (back_subset_I ht hb) (front_subset_I hs ha) hb1 ha1 hab.symm
    exact absurd (this ▸ hb.1) (not_le.mpr (lt_of_le_of_lt ha.2 hst))

/-! ### Covering, and where the pieces meet -/

/-- The loop's images of the middle and of the outside cover the curve. -/
theorem pieces_cover (hs : s ∈ I) (ht : t ∈ I) :
    f '' Icc s t ∪ (f '' Icc 0 s ∪ f '' Icc t 1) = f '' I := by
  rw [parameters_split hs ht, image_union, image_union]

/-- **The two pieces meet in exactly the two cut points.**

Three cases, one for each way an outside parameter can be placed. The one that matters is the
outside parameter being the finish: it carries the same point as the start, so the middle
parameter is the start, which forces `s` to be it. That case is why the argument needs a loop
rather than an arc. -/
theorem pieces_meet_at_ends (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    f '' Icc s t ∩ (f '' Icc 0 s ∪ f '' Icc t 1) = {f s, f t} := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  apply Subset.antisymm
  · rintro z ⟨⟨m, hm, rfl⟩, hzout⟩
    have hmI : m ∈ I := middle_subset_I hs ht hm
    have hm1 : m ≠ 1 := ne_of_lt (lt_of_le_of_lt hm.2 ht')
    rcases hzout with ⟨a, ha, hazm⟩ | ⟨b, hb, hbzm⟩
    · -- A front parameter: it is at most `s`, and the middle parameter is at least `s`.
      have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
      have : m = a :=
        hf.injective_before_finish hmI (front_subset_I hs ha) hm1 ha1 hazm.symm
      rw [le_antisymm (this ▸ ha.2) hm.1]
      exact mem_insert _ _
    · rcases eq_or_ne b 1 with rfl | hb1
      · -- The far end carries the same point as the start, and the start is short of the
        -- finish, so the middle parameter is the start — which forces `s` to be it.
        have : m = 0 :=
          hf.injective_before_finish hmI zero_mem_I hm1 one_ne_zero.symm
            (hbzm.symm.trans hf.finish_eq_start)
        have hs0 : s = 0 := le_antisymm (this ▸ hm.1) hs.1
        rw [hs0, ← this]
        exact mem_insert _ _
      · -- Otherwise the outside parameter is at least `t`, and the middle one is at most `t`.
        have : m = b :=
          hf.injective_before_finish hmI (back_subset_I ht hb) hm1 hb1 hbzm.symm
        rw [le_antisymm hm.2 (this ▸ hb.1)]
        exact mem_insert_of_mem _ rfl
  · rintro z (rfl | rfl)
    · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩⟩
    · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, Or.inr ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩⟩

/-! ### The two arcs, at chosen parameters -/

end IsLoop

/-! ### The theorem -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCyclesProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil
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

/-! ## Concatenating polylines -/

/-- **Appending two vertex lists joins their carriers by one segment.** The segment runs from
the last vertex of the first list to the first vertex of the second, and is degenerate — hence
contributes nothing — exactly when the two lists already share that vertex. -/
theorem poly_append_join : ∀ {as : List Plane} (h₁ : as ≠ []) {bs : List Plane} (h₂ : bs ≠ []),
    poly (as ++ bs) = poly as ∪ segment ℝ (as.getLast h₁) (bs.head h₂) ∪ poly bs
  | [], h₁, _, _ => absurd rfl h₁
  | [x], _, bs, h₂ => by
    rw [List.singleton_append, poly_cons_of_ne_nil h₂, poly_singleton,
      List.getLast_singleton]
    rw [Set.union_assoc, Set.singleton_union]
    exact (Set.insert_eq_self.2
      (Set.mem_union_left _ (left_mem_segment ℝ x (bs.head h₂)))).symm
  | x :: y :: as, _, bs, h₂ => by
    have hne : (y :: as) ≠ [] := List.cons_ne_nil _ _
    rw [List.cons_append, poly_cons_of_ne_nil (by simp), poly_cons_cons,
      poly_append_join hne h₂, List.head_append_of_ne_nil hne,
      List.getLast_cons hne]
    ac_rfl

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-! ## A polygonal arc is a polyline running from one end to the other -/

end Schoenflies

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

/-- The source of a nonempty walk is an end of its first edge, so a nonempty walk visits no
vertex its edges do not cover. -/
theorem IsWalk.walkVertices_eq_covered (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices u W = G.coveredVertices W := by
  refine Set.insert_eq_self.2 ?_
  cases h with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_coveredVertices List.mem_cons_self hl.inc_left

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

/-! ### Splicing an ear onto an arc

The blueprint's "the crosscut replaces `F` by exactly two regions, both bounded by cycles": the
two new cycles are the two arcs of the old one, each closed up by the ear. This is the
combinatorial construction of one of them. -/

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-! ## What a subgraph spanned by a walk occupies -/

/-! ## The conclusion of `lem:face-cycles`, at one face -/

namespace IsFaceCycle

variable {e : β} {u v : Plane} {D : List β}

/-- **"In particular, every bounded face is the interior of its boundary cycle."** The other
region of a separating curve is the unbounded one. -/
theorem eq_inside_of_isBounded (h : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = inside (edgesCover drawing (e :: D)) := by
  rcases h.isRegionOf with hin | hout
  · exact hin
  · exact absurd (hout ▸ hbdd) h.isSeparating.not_isBounded_outside

end IsFaceCycle

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-! ### The point set of a subgraph -/

variable {δ : Type*} {H K : Graph Plane δ} {drawing : δ → ℝ → Plane}

theorem pointSet_mono (h : H ≤ K) : pointSet H drawing ⊆ pointSet K drawing :=
  Set.union_subset_union h.vertexSet_mono
    (Set.biUnion_subset_biUnion_left h.edgeSet_mono)

end Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

namespace CellStructure

variable (S : CellStructure γ)

/-- The cells of the distinguished outer cycle: its vertices and its edges. -/
def outerCells : Set γ := V(S.outerGraph) ∪ E(S.outerGraph)

/-- The supercells of a cell: the index set of its closed star. -/
def supercells (σ : γ) : Set γ := {τ | S.sub σ τ}

theorem mem_supercells {σ τ : γ} : τ ∈ S.supercells σ ↔ S.sub σ τ := Iff.rfl

/-! ### Realizations -/

namespace Realization

variable {S}
variable (R : S.Realization)

/-- The closed star of a cell: the union of the closures of its supercells. The index set is
abstract; only the summands are geometric. -/
def star (σ : γ) : Set Plane := ⋃ τ ∈ S.supercells σ, closure (R.cell τ)

/-- An open 0-cell or 1-cell is part of the realized skeleton: a 0-cell is realized by a drawn
vertex, a 1-cell by part of a drawn edge.

Hoisted here because `Schoenflies/LimitMap.lean` and `Schoenflies/FiniteTransfer.lean` each
proved it independently and the duplicate gate caught the collision — two alpha-equivalent
`Prop`s pass Lean's import checker under proof irrelevance, so a clean build would not have. -/
theorem cell_subset_skeletonSet {R : S.Realization} {κ : γ}
    (hκ : κ ∈ V(S.skel) ∪ E(S.skel)) : R.cell κ ⊆ R.skeletonSet := by
  rcases hκ with hv | he
  · rw [R.cell_vertex hv]
    exact Set.singleton_subset_iff.2 (vertexSet_subset_pointSet
      (by rw [Realization.vertexSet_graph]; exact ⟨κ, hv, rfl⟩))
  · obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
    rw [R.cell_edge hl]
    exact Set.sdiff_subset.trans (edgeArc_subset_pointSet
      (by rw [Realization.edgeSet_graph]; exact he))

end Realization

/-! ### The skeleton homeomorphism -/

/-! ### Combinatorial invariance -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CrosscutAtMostTwo
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- The points of an open set that are in neither of two prescribed components form an open
set: each such point drags its whole component with it, and a component of an open subset of
the plane is open. -/
theorem isOpen_notMem_two_components {S : Set Plane} (hS : IsOpen S) (zL zR : Plane) :
    IsOpen {y | y ∈ S ∧ y ∉ connectedComponentIn S zL ∧ y ∉ connectedComponentIn S zR} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyS, hyL, hyR⟩
  refine ⟨connectedComponentIn S y, ?_, Plane.isOpen_connectedComponentIn hS,
    mem_connectedComponentIn hyS⟩
  intro w hw
  -- Two components are equal or disjoint: if `w` were in one of the two named components, that
  -- component would *be* the component of `y`, and `y` would be in it.
  have hcw : connectedComponentIn S y = connectedComponentIn S w := connectedComponentIn_eq hw
  refine ⟨connectedComponentIn_subset S y hw, fun hwL => hyL ?_, fun hwR => hyR ?_⟩
  · rw [show connectedComponentIn S zL = connectedComponentIn S y from
      (connectedComponentIn_eq hwL).trans hcw.symm]
    exact mem_connectedComponentIn hyS
  · rw [show connectedComponentIn S zR = connectedComponentIn S y from
      (connectedComponentIn_eq hwR).trans hcw.symm]
    exact mem_connectedComponentIn hyS

/-- **The clopen step, and the whole of "at most two sides" once a collar is available.** If
every point of `P` inside the region `D` has a neighbourhood inside `D` whose complement of `P`
is covered by the components of two fixed points `z_L, z_R`, then all of `D ∖ P` is covered by
those two components.

The set `T` of points of `D ∖ P` in neither component is open; the union `U` of the two
components with all the good neighbourhoods is open, contains `P ∩ D` and meets `D`; the two
are disjoint and cover `D`. Connectedness of `D` kills `T`. -/
theorem covered_by_two_of_local (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hPclosed : IsClosed P) {zL zR : Plane} (hzL : zL ∈ D \ P)
    (hloc : ∀ w ∈ D ∩ P, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR)
    {x : Plane} (hx : x ∈ D \ P) :
    x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  by_contra hcon
  push Not at hcon
  have hSopen : IsOpen (D \ P) := hDopen.sdiff hPclosed
  -- `W` gathers every open piece of `D` that the hypothesis certifies.
  have hWopen : IsOpen (⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    isOpen_sUnion fun _ hV => hV.1
  have hUopen : IsOpen (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    ((Plane.isOpen_connectedComponentIn hSopen).union
      (Plane.isOpen_connectedComponentIn hSopen)).union hWopen
  have hTopen := isOpen_notMem_two_components hSopen zL zR
  -- `U` and `T` are disjoint: a point of `T` is off `P`, so if it were in `W` it would be in
  -- one of the two components, and it is in neither by definition.
  have hdisj : ∀ y, y ∈ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR} →
      y ∈ {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} → False := by
    rintro y (hy | hy) ⟨hyS, hyL, hyR⟩
    · exact hy.elim hyL hyR
    · obtain ⟨V, hV, hyV⟩ := hy
      exact (hV.2.2 ⟨hyV, hyS.2⟩).elim hyL hyR
  -- and they cover `D`: a point of `D` on `P` is inside one of the certified pieces.
  have hcover : D ⊆ (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) ∪
      {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} := by
    intro y hyD
    by_cases hyP : y ∈ P
    · obtain ⟨V, hVopen, hyV, hVD, hVsub⟩ := hloc y ⟨hyD, hyP⟩
      exact Or.inl (Or.inr ⟨V, ⟨hVopen, hVD, hVsub⟩, hyV⟩)
    · by_cases hyL : y ∈ connectedComponentIn (D \ P) zL
      · exact Or.inl (Or.inl (Or.inl hyL))
      by_cases hyR : y ∈ connectedComponentIn (D \ P) zR
      · exact Or.inl (Or.inl (Or.inr hyR))
      exact Or.inr ⟨⟨hyD, hyP⟩, hyL, hyR⟩
  obtain ⟨y, hyD, hyU, hyT⟩ := hDconn _ _ hUopen hTopen hcover
    ⟨zL, hzL.1, Or.inl (Or.inl (mem_connectedComponentIn hzL))⟩
    ⟨x, hx.1, hx, hcon.1, hcon.2⟩
  exact hdisj y hyU hyT

/-! ### Lemma "At most two sides" -/

/-- **"At most two", read off two components already known to be distinct.** This is the form
Theorem "Crosscut theorem" cites: the crosscut-cells lemma hands it two *distinct* components of
`D ∖ P`, and this says there is nothing else.

Stated for an arbitrary set `S`, since it is pure component bookkeeping: if everything is
covered by the components of `z_L, z_R` and `v₁, v₂` have different components, then those two
components are the two, in one order or the other. -/
theorem covered_by_two_components_of_ne {S : Set Plane} {zL zR v₁ v₂ : Plane}
    (h : ∀ x ∈ S, x ∈ connectedComponentIn S zL ∨ x ∈ connectedComponentIn S zR)
    (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    (hne : connectedComponentIn S v₁ ≠ connectedComponentIn S v₂) :
    ∀ x ∈ S, x ∈ connectedComponentIn S v₁ ∨ x ∈ connectedComponentIn S v₂ := by
  intro x hx
  rcases h v₁ h₁ with hv₁ | hv₁ <;> rcases h v₂ h₂ with hv₂ | hv₂
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne
  · rcases h x hx with hxx | hxx
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
  · rcases h x hx with hxx | hxx
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne

/-! ### The collar hypothesis is not vacuous: a straight crosscut

The collar of a *straight* crosscut is a rectangle, and the free-standing frame toolkit of
`Schoenflies/Strip.lean` — `coordAlong`, `coordAcross`, `strip`, `isOpen_strip`, `convex_strip`,
`dist_foot`, `frame_decomp` — builds it directly, with no cyclic vertex family in sight. So
`HasArcCollars` is discharged outright in the simplest crosscut configuration, and
`segment_crosscut_at_most_two` below is a hypothesis-free instance of the lemma.

This is the shape a general discharger has to reproduce along a chain of edges: it is exactly
the blueprint's edge block, and what is missing is the vertex disks between consecutive blocks
and the end cross-sections. -/

namespace Plane

/-- A nondegenerate segment has a unit direction and a length: `L • u = b - a` with `‖u‖ = 1`.

Stated as an existential so that the direction and the length are *opaque* to the consumer.
Writing them as `dir (b - a)` and `‖b - a‖` makes every subsequent rewrite of `b` reach inside
them, which is exactly the friction the strip apparatus avoids by carrying `tang` and `len` as
fields. -/
theorem exists_direction_length {a b : Plane} (hab : a ≠ b) :
    ∃ (u : Plane) (L : ℝ), 0 < L ∧ IsDirection u ∧ L • u = b - a := by
  have hne : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hL : (0 : ℝ) < ‖b - a‖ := norm_pos_iff.2 hne
  exact ⟨dir (b - a), ‖b - a‖, hL, isDirection_dir hne, by
    rw [dir, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]⟩

/-- **A nondegenerate segment, read in the frame of its own direction.** Its points are the ones
at signed distance zero whose progress along the direction lies between `0` and the length.

This is the segment analogue of `ClosedPolygon.mem_edge_iff`, which is stated for an edge of a
closed polygon and so is unavailable for a lone segment. -/
theorem mem_segment_iff_coord {a b u x : Plane} {L : ℝ} (hL : 0 < L) (hu : IsDirection u)
    (hLu : L • u = b - a) :
    x ∈ segment ℝ a b ↔ coordAcross a u x = 0 ∧ coordAlong a u x ∈ Icc 0 L := by
  constructor
  · intro hx
    rw [segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    have hrw : a + θ • (b - a) = a + (θ * L) • u + (0 : ℝ) • perp u := by
      rw [mul_smul, hLu]; module
    dsimp only
    rw [hrw, coordAlong_param hu, coordAcross_param hu]
    exact ⟨rfl, mul_nonneg hθ.1 hL.le, by nlinarith [hθ.2, hL.le]⟩
  · rintro ⟨h0, hc⟩
    rw [segment_eq_image']
    refine ⟨coordAlong a u x / L, ⟨div_nonneg hc.1 hL.le, (div_le_one hL).2 hc.2⟩, ?_⟩
    dsimp only
    rw [← hLu, smul_smul, div_mul_cancel₀ _ hL.ne']
    nth_rewrite 2 [frame_decomp hu a x]
    rw [h0]
    module

/-- A point at signed distance zero is the point of the line with its own progress. -/
theorem eq_foot_of_coordAcross_eq_zero {a u x : Plane} (hu : IsDirection u)
    (h0 : coordAcross a u x = 0) : x = a + (coordAlong a u x) • u := by
  nth_rewrite 1 [frame_decomp hu a x]
  rw [h0]
  module

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.GeneralCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- An arc between two points is not just those two points: the midpoint parameter carries a
third point of it, because the parametrisation is injective. -/
theorem IsArcBetween.not_subset_pair (h : IsArcBetween A p q) : ¬ A ⊆ ({p, q} : Set Plane) := by
  obtain ⟨f, -, hi, rfl, rfl, rfl⟩ := h
  intro hsub
  have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
  have hmem := hsub (mem_image_of_mem f hhalf)
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with h' | h'
  · exact absurd (hi hhalf zero_mem_I h') (by norm_num)
  · exact absurd (hi hhalf one_mem_I h') (by norm_num)

/-! ### The configuration

Two bundles of hypotheses. `IsCrosscut C P p q` is the blueprint's "`P` is a simple polygonal
arc with distinct endpoints `p, q ∈ C` and all other points in `D = Int(C)`"; distinctness of
`p` and `q` is *not* a field, since an arc between two points always has them distinct.
`IsCutPair C p q A₁ A₂` is "`A₁, A₂` are the two arcs of `C` from `p` to `q`". The two are kept
apart because the arcs are a *choice* — swapping them is a symmetry of the whole theorem, and
`IsCutPair.symm` is what makes every statement below need proving only once. -/

/-- **The crosscut configuration.** A Jordan curve `C` and a simple polygonal arc `P` from
`p ∈ C` to `q ∈ C` whose remaining points all lie in the Jordan domain `inside C`. -/
structure IsCrosscut (C P : Set Plane) (p q : Plane) : Prop where
  /-- `C` is a Jordan curve. -/
  curve : IsJordanCurve C
  /-- `P` is a simple arc from `p` to `q`. -/
  arc : IsArcBetween P p q
  /-- `P` is polygonal. -/
  polygonal : IsPolygonal P
  /-- The first endpoint is on the curve. -/
  left_mem : p ∈ C
  /-- The second endpoint is on the curve. -/
  right_mem : q ∈ C
  /-- Every other point of the crosscut is inside the curve. -/
  sdiff_subset : P \ {p, q} ⊆ inside C

/-- **The two arcs of `C` from `p` to `q`**, as in `lem:jordan-circle`: two arcs between the
same two points which cover the curve and meet in exactly those two points. -/
structure IsCutPair (C : Set Plane) (p q : Plane) (A₁ A₂ : Set Plane) : Prop where
  /-- The first piece is an arc from `p` to `q`. -/
  fst : IsArcBetween A₁ p q
  /-- The second piece is an arc from `p` to `q`. -/
  snd : IsArcBetween A₂ p q
  /-- The two pieces cover the curve. -/
  union_eq : A₁ ∪ A₂ = C
  /-- The two pieces meet exactly at the two cut points. -/
  inter_eq : A₁ ∩ A₂ = {p, q}

namespace IsCutPair

/-- Swapping the two arcs. Every conclusion of this module is proved for `A₁` and obtained for
`A₂` by composing with this. -/
theorem symm (h : IsCutPair C p q A₁ A₂) : IsCutPair C p q A₂ A₁ :=
  ⟨h.snd, h.fst, by rw [union_comm]; exact h.union_eq, by rw [inter_comm]; exact h.inter_eq⟩

theorem fst_subset (h : IsCutPair C p q A₁ A₂) : A₁ ⊆ C := by
  rw [← h.union_eq]; exact subset_union_left

theorem snd_subset (h : IsCutPair C p q A₁ A₂) : A₂ ⊆ C := h.symm.fst_subset

/-- The two arcs are distinct: they meet only at `p` and `q`, and neither is just `{p, q}`. -/
theorem ne (h : IsCutPair C p q A₁ A₂) : A₁ ≠ A₂ :=
  arcs_ne h.inter_eq.subset h.fst.not_subset_pair

end IsCutPair

/-! ### Elementary consequences of the configuration

Nothing here needs `thm:jordan`: these are the set-theoretic facts that turn "the crosscut runs
inside the curve" into the hypotheses `Schoenflies.crosscut_cells` takes. -/

namespace IsCrosscut

theorem left_notMem_inside (h : IsCrosscut C P p q) : p ∉ inside C := fun hp =>
  inside_subset_compl hp h.left_mem

theorem right_notMem_inside (h : IsCrosscut C P p q) : q ∉ inside C := fun hq =>
  inside_subset_compl hq h.right_mem

/-- **The crosscut meets the curve exactly at its two endpoints.** Everything else on the
crosscut is inside the curve, hence off it. -/
theorem inter_eq (h : IsCrosscut C P p q) : P ∩ C = {p, q} := by
  refine Subset.antisymm (fun z hz => ?_) (pair_subset ⟨h.arc.left_mem, h.left_mem⟩
    ⟨h.arc.right_mem, h.right_mem⟩)
  by_contra hzpq
  exact inside_subset_compl (h.sdiff_subset ⟨hz.1, hzpq⟩) hz.2

/-- **The crosscut misses the outside of the curve entirely**: its endpoints are on the curve
and everything else is inside. This is the sentence the three-region half opens with. -/
theorem disjoint_outside (h : IsCrosscut C P p q) : Disjoint P (outside C) := by
  rw [disjoint_left]
  intro z hzP hzO
  by_cases hz : z ∈ ({p, q} : Set Plane)
  · rcases hz with rfl | rfl
    exacts [hzO.1 h.left_mem, hzO.1 h.right_mem]
  · exact disjoint_left.1 disjoint_inside_outside (h.sdiff_subset ⟨hzP, hz⟩) hzO

/-- `P ∩ C ⊆ A₁`: the crosscut meets the curve only in the two points that lie on *both* arcs.
This is the hypothesis `hP₁` of `Schoenflies.crosscut_cells`. -/
theorem inter_subset_arc (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    P ∩ C ⊆ A₁ := by
  rw [h.inter_eq]
  exact pair_subset hcut.fst.left_mem hcut.fst.right_mem

/-- `(A₁ ∪ P) ∩ C = A₁`: the curve `J₁` of the blueprint meets `C` exactly in the arc it was
built from. This is what turns clause (c) of `Schoenflies.crosscut_cells` into the labelling
lemma. -/
theorem arc_union_inter (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    (A₁ ∪ P) ∩ C = A₁ := by
  refine Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hcut.fst_subset hz⟩
  rintro z ⟨hz | hz, hzC⟩
  · exact hz
  · exact h.inter_subset_arc hcut ⟨hz, hzC⟩

/-- **`J₁ = A₁ ∪ P` is a Jordan curve.** The arc and the crosscut are two arcs from `p` to `q`
meeting only at those two points. -/
theorem isJordanCurve_union (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    IsJordanCurve (A₁ ∪ P) := by
  refine _root_.Schoenflies.isJordanCurve_union hcut.fst h.arc fun z hzA hzP => ?_
  have hz : z ∈ ({p, q} : Set Plane) := h.inter_eq ▸ ⟨hzP, hcut.fst_subset hzA⟩
  simpa using hz

/-! ### The two separating curves, and where the outside of `C` sits

This is the paragraph of the blueprint proof that pins the roles of `Wᵢ` and `Vᵢ`:
`Ω† = Ext(C)` is connected, unbounded and disjoint from `Jᵢ`, hence lies in `Ext(Jᵢ)`. -/

theorem isSeparating_curve (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) : IsSeparating C :=
  hjordan C h.curve

theorem isSeparating_union (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsSeparating (A₁ ∪ P) :=
  hjordan _ (h.isJordanCurve_union hcut)

/-- **`Ext(C) ⊆ Ext(A ∪ P)`.** The outside of `C` is connected and misses `A ∪ P`, so it lies in
one component of the complement of `A ∪ P`; being unbounded, that component is unbounded, which
is what `Schoenflies.outside` records.

Stated for an arbitrary `A ⊆ C`, since that is all the argument uses. -/
theorem outside_subset_outside_union
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hA : A ⊆ C) : outside C ⊆ outside (A ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  have hsub : outside C ⊆ (A ∪ P)ᶜ := by
    rintro z hz (hzA | hzP)
    · exact hz.1 (hA hzA)
    · exact disjoint_left.1 h.disjoint_outside hzP hz
  intro z hz
  refine ⟨hsub hz, fun hb => hsep.not_isBounded_outside (hb.subset ?_)⟩
  exact hsep.isConnected_outside.isPreconnected.subset_connectedComponentIn hz hsub

/-- The pair `(Ext(C), Int(C))` in the shape `Schoenflies.crosscut_cells` takes for `(Ω, Ω')`,
with `Ω = Int(C)` the region the crosscut runs in. -/
theorem isRegionPair_curve (C : Set Plane) : IsRegionPair C (inside C) (outside C) :=
  Or.inl ⟨rfl, rfl⟩

/-- The pair `(Wᵢ, Vᵢ) = (Ext(Jᵢ), Int(Jᵢ))`. -/
theorem isRegionPair_union (J : Set Plane) : IsRegionPair J (outside J) (inside J) :=
  Or.inr ⟨rfl, rfl⟩

/-! ### The first half: `Int(A₁ ∪ P)` is a component of `Int(C) ∖ P` with closure meeting `C`
in `A₁`

Three applications of `Schoenflies.crosscut_cells`, one clause each. Everything is stated for the
arc `A₁`; `IsCutPair.symm` supplies the `A₂` instance. -/

/-- **`Int(A₁ ∪ P) ⊆ Int(C) ∖ P`.** Clause (a) of `lem:crosscut-cells`, first half. -/
theorem side_subset (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ⊆ inside C \ P :=
  cell_subset_region_diff (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right

/-- **`Int(A₁ ∪ P)` is a connected component of `Int(C) ∖ P`.** Clause (a) of
`lem:crosscut-cells`. -/
theorem side_isComponent (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    ∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) :=
  cell_isComponent (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right
    (union_subset_union_left P hcut.fst_subset)

/-- **The labelling lemma: the closure of the side meets `C` exactly in its own arc.** Clause
(c) of `lem:crosscut-cells`. This is what makes `A ↦ inside (A ∪ P)` the correspondence
`lem:crosscut-side-correspondence` asks for, and it is what distinguishes the two sides. -/
theorem closure_side_inter (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) ∩ C = A₁ := by
  rw [closure_cell_inter_curve (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (IsRegionOf.outside C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset)]
  exact h.arc_union_inter hcut

/-- **The two sides are distinct.** Equal sides would have equal closures, hence equal arcs. -/
theorem side_ne (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) := by
  intro heq
  have h₁ := h.closure_side_inter hjordan hcut
  have h₂ := h.closure_side_inter hjordan hcut.symm
  rw [heq] at h₁
  exact hcut.ne (h₁.symm.trans h₂)

theorem side_nonempty (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : (inside (A₁ ∪ P)).Nonempty :=
  (h.isSeparating_union hjordan hcut).isConnected_inside.nonempty

theorem isOpen_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsOpen (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isOpen_inside

/-- **The boundary of the side is its own Jordan curve `A₁ ∪ P`.** -/
theorem frontier_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    frontier (inside (A₁ ∪ P)) = A₁ ∪ P :=
  (h.isSeparating_union hjordan hcut).frontier_inside

/-- The closure of the side is the side together with its boundary curve. Paired with
`closure_side_inter` this is the form `lem:crosscut-side-correspondence` reads the closure in. -/
theorem closure_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) :=
  (IsRegionOf.inside (A₁ ∪ P)).closure_eq (h.isSeparating_union hjordan hcut)

/-- The two sides are disjoint: they are distinct components of the same set. -/
theorem disjoint_sides (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) := by
  rw [disjoint_left]
  intro z hz₁ hz₂
  exact h.side_ne hjordan hcut
    ((h.side_isComponent hjordan hcut z hz₁).symm.trans
      (h.side_isComponent hjordan hcut.symm z hz₂))

/-! ### The second half: there are no other components

`Schoenflies.crosscut_components_exhaust` applied to the two sides, which the previous section
has just shown to be distinct components. -/

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- A graph that does not carry the subdivided edge is untouched. -/
theorem subdivGraph_eq_self {hne h₁ h₂} (he : e ∉ E(H)) :
    subdivGraph H e x y v e₁ e₂ hne h₁ h₂ = H := by
  have hno : ¬ H.IsLink e x y := fun h => he h.edge_mem
  refine Graph.ext ?_ fun f a b => ?_
  · simp [hno]
  · simp only [subdivGraph_isLink, hno, and_false, false_and, or_false]
    refine ⟨fun hl => hl.1, fun hl => ⟨hl, ?_, ?_, ?_⟩⟩
    exacts [fun h => he (h ▸ hl.edge_mem), fun h => h₁ (h ▸ hl.edge_mem),
      fun h => h₂ (h ▸ hl.edge_mem)]

/-! ### The cells of an abstract structure -/

namespace CellStructure

variable (S : CellStructure γ)

theorem vertexSet_ne_edgeSet {z w : γ} (hz : z ∈ V(S.skel)) (hw : w ∈ E(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz (h ▸ hw)

theorem faces_ne_vertexSet {z w : γ} (hz : z ∈ S.faces) (hw : w ∈ V(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_faces_vertexSet hz (h ▸ hw)

theorem faces_ne_edgeSet {z w : γ} (hz : z ∈ S.faces) (hw : w ∈ E(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_faces_edgeSet hz (h ▸ hw)

/-! ### Elementary operation 1: edge subdivision

Blueprint, `def:generated-structure`, operation 1: "the edge `e` is replaced by a new vertex
`v` and two new edges `e₁, e₂`, whose endpoints are `v` together with one old endpoint of `e`
each; the relation `≼_abs` is extended by declaring `v ≼ e₁` and `v ≼ e₂`, each old endpoint of
`e` a subcell of its adjacent new edge, and `v, e₁, e₂` subcells of exactly the old strict
supercells of `e`; all pairs not involving `e` are unchanged." -/

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

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- The crosscut meets the Jordan domain exactly in its own interior points. -/
theorem IsCrosscut.inside_inter (h : IsCrosscut C P p q) : inside C ∩ P = P \ {p, q} := by
  refine Set.Subset.antisymm (fun z hz => ⟨hz.2, fun hzpq => ?_⟩) fun z hz =>
    ⟨h.sdiff_subset hz, hz.1⟩
  rcases hzpq with rfl | rfl
  exacts [inside_subset_compl hz.1 h.left_mem, inside_subset_compl hz.1 h.right_mem]

/-- Each side misses the crosscut. -/
theorem IsCrosscut.disjoint_side_crosscut
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (inside (A₁ ∪ P)) (P \ {p, q}) :=
  Set.disjoint_left.2 fun _ hz hz' => (h.side_subset hjordan hcut hz).2 hz'.1

end Schoenflies
end

section
-- module Solutions.Q146_CD.PrePolygonArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- **An arc is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPieces a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPieces a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-! ## The arcs as sets -/

/-- An arc is compact: it is a finite union of segments. -/
theorem isCompact_arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : IsCompact (P.arc a k) :=
  isCompact_cover _

/-- An interior point of the first edge of an arc: a point of the arc that is neither cut
vertex, which is what says the arc is more than its two ends. -/
theorem arc_not_subset_endpoints (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : ¬ P.arc a k ⊆ ({P.vertex a, P.vertex (a + k)} : Set Plane) := by
  intro hsub
  set x : Plane := (1 / 2 : ℝ) • P.vertex a + (1 / 2 : ℝ) • P.vertex (a + 1) with hxdef
  have hxo : x ∈ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxarc : x ∈ P.arc a k :=
    mem_arc_iff.2 ⟨0, hk1, by
      rw [Nat.cast_zero, add_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  have hkne : (k : ZMod (m + 3)) ≠ 0 := by
    intro he
    have h0 : ((k : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by rw [he, Nat.cast_zero]
    have hk0 := ClosedPolygon.natCast_inj (m := m) (show k < m + 3 by omega)
      (show 0 < m + 3 by omega) h0
    omega
  rcases hsub hxarc with h | h
  · exact P.vertex_ne_succ a (left_mem_openSegment_iff.1 (h ▸ hxo))
  · refine notMem_edge_of_mem_openSegment (P := P) (i := a) (j := a + k)
      (fun he => hkne (by linear_combination he)) hxo ?_
    rw [edge, h]
    exact left_mem_segment ℝ _ _

/-! ### An arc as a polyline

`arc a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

/-- The vertex list of an arc. -/
def arcList (P : PrePolygon m) (a : ZMod (m + 3)) : ℕ → List Plane
  | 0 => [P.vertex a]
  | k + 1 => P.vertex a :: arcList P (a + 1) k

theorem arcList_ne_nil (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : P.arcList a k ≠ [] := by
  cases k <;> simp [arcList]

theorem getLast_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    (P.arcList a k).getLast (P.arcList_ne_nil a k) = P.vertex (a + k)
  | 0, P, a => by simp [arcList]
  | k + 1, P, a => by
    change (P.vertex a :: P.arcList (a + 1) k).getLast (List.cons_ne_nil _ _)
        = P.vertex (a + ((k + 1 : ℕ) : ZMod (m + 3)))
    rw [List.getLast_cons (P.arcList_ne_nil (a + 1) k), getLast_arcList k P (a + 1)]
    congr 1
    push_cast
    ring

theorem arcPieces_succ (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcPieces a (k + 1) = (P.vertex a, P.vertex (a + 1)) :: P.arcPieces (a + 1) k := by
  rw [arcPieces, arcPieces, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [Nat.cast_zero, add_zero]
  · refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    congr 2 <;> · push_cast; ring

theorem poly_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    poly (P.arcList a (k + 1)) = P.arc a (k + 1)
  | 0, P, a => by
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ ({P.vertex (a + 1)} : Set Plane)
        = cover (P.arcPieces a 1)
    rw [arcPieces_succ P a 0, arcPieces_zero, cover_cons, cover_nil, Set.union_empty]
    exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ _ _))
  | k + 1, P, a => by
    have hstep : poly (P.arcList a (k + 2))
        = segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ poly (P.arcList (a + 1) (k + 1)) := rfl
    rw [hstep, poly_arcList k P (a + 1)]
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ cover (P.arcPieces (a + 1) (k + 1))
        = cover (P.arcPieces a (k + 2))
    rw [arcPieces_succ P a (k + 1), cover_cons]
    rfl

theorem poly_arcList_of_pos (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    poly (P.arcList a k) = P.arc a k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact poly_arcList k' P a

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.JordanSeparates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
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

/-- Two points of the plane agreeing in two distinct coordinates are equal. -/
theorem coord_ext {i j : Fin 2} (hij : i ≠ j) {z w : Plane} (hi : z i = w i) (hj : z j = w j) :
    z = w := by
  ext k
  have hk : k = i ∨ k = j := by
    revert hij; fin_cases i <;> fin_cases j <;> intro hij <;> fin_cases k <;> simp_all
  rcases hk with rfl | rfl
  · exact hi
  · exact hj

/-! ### Coordinates along a segment -/

end Plane

/-- Injectivity of a three-element vector, from the three distinctness facts. -/
theorem injective_three {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all

/-! ### Cutting an arc at an interior point -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.ModelCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The model curve `S = ∂Q`, the boundary of the square `Q = [-1,1]²`, described by the sup
norm. -/
def modelCurve : Set Plane := {x : Plane | Plane.supNorm x = 1}

/-- The corner `(1, 1)`. -/
def cornerNE : Plane := Plane.mk 1 1

/-- The corner `(-1, 1)`. -/
def cornerNW : Plane := Plane.mk (-1) 1

/-- The corner `(-1, -1)`. -/
def cornerSW : Plane := Plane.mk (-1) (-1)

/-- The corner `(1, -1)`. -/
def cornerSE : Plane := Plane.mk 1 (-1)

/-- The top side of the square, traversed from `(1,1)` to `(-1,1)`. -/
def sideTop : Set Plane := segment ℝ cornerNE cornerNW

/-- The left side of the square, traversed from `(-1,1)` to `(-1,-1)`. -/
def sideLeft : Set Plane := segment ℝ cornerNW cornerSW

/-- The bottom side of the square, traversed from `(-1,-1)` to `(1,-1)`. -/
def sideBottom : Set Plane := segment ℝ cornerSW cornerSE

/-- The right side of the square, traversed from `(1,-1)` to `(1,1)`. -/
def sideRight : Set Plane := segment ℝ cornerSE cornerNE

/-! ### The model curve is a Jordan curve -/

theorem cornerNE_ne_cornerNW : cornerNE ≠ cornerNW := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  norm_num [cornerNE, cornerNW] at this

theorem cornerNW_ne_cornerSW : cornerNW ≠ cornerSW := by
  intro h
  have := congrArg (fun p : Plane => p 1) h
  norm_num [cornerNW, cornerSW] at this

theorem cornerSW_ne_cornerSE : cornerSW ≠ cornerSE := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  norm_num [cornerSW, cornerSE] at this

theorem cornerSE_ne_cornerNE : cornerSE ≠ cornerNE := by
  intro h
  have := congrArg (fun p : Plane => p 1) h
  norm_num [cornerSE, cornerNE] at this

theorem isArcBetween_sideTop : IsArcBetween sideTop cornerNE cornerNW :=
  isArcBetween_segment cornerNE_ne_cornerNW

theorem isArcBetween_sideLeft : IsArcBetween sideLeft cornerNW cornerSW :=
  isArcBetween_segment cornerNW_ne_cornerSW

theorem isArcBetween_sideBottom : IsArcBetween sideBottom cornerSW cornerSE :=
  isArcBetween_segment cornerSW_ne_cornerSE

theorem isArcBetween_sideRight : IsArcBetween sideRight cornerSE cornerNE :=
  isArcBetween_segment cornerSE_ne_cornerNE

/-! ### The model curve is the boundary of the square

This is the blueprint's description `S = ∂Q` with `Q = [-1,1]²`, and the check that the sup-norm
definition above is the intended one. The only content is that a point of sup norm exactly `1`
is *not* interior to the square: scaling it out by a factor `1 + δ` leaves the square while
moving an arbitrarily small distance. -/

theorem smul_coord (a : ℝ) (x : Plane) (i : Fin 2) : (a • x) i = a * x i := by simp

theorem mem_closedSquare_zero_one {x : Plane} :
    x ∈ Plane.closedSquare 0 1 ↔ Plane.supNorm x ≤ 1 := by
  simp [Plane.closedSquare]

theorem modelCurve_subset_closedSquare : modelCurve ⊆ Plane.closedSquare 0 1 :=
  fun _ hx => mem_closedSquare_zero_one.mpr (le_of_eq hx)

/-- A point of the model curve is not interior to the square: pushing it radially outwards by
a factor `1 + δ` leaves the square, and `δ` may be taken as small as one likes. -/
theorem notMem_interior_closedSquare {x : Plane} (hx : Plane.supNorm x = 1) :
    x ∉ interior (Plane.closedSquare 0 1) := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hε, hball⟩ := hmem
  have hx' : max |x 0| |x 1| = 1 := hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp [Plane.supNorm] at hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set δ : ℝ := ε / (2 * ‖x‖) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  -- the pushed-out point is within `ε/2` of `x`
  have hdist : dist ((1 + δ) • x) x < ε := by
    have hsub : (1 + δ) • x - x = δ • x := by module
    have hmul : δ * ‖x‖ = ε / 2 := by
      rw [hδdef]; field_simp
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hmul]
    linarith
  have hin : Plane.supNorm ((1 + δ) • x) ≤ 1 :=
    mem_closedSquare_zero_one.mp (hball (Metric.mem_ball.mpr hdist))
  -- but the coordinate that attained the sup norm has grown past `1`
  have hgrown : 1 + δ ≤ Plane.supNorm ((1 + δ) • x) := by
    rcases max_choice |x 0| |x 1| with hm | hm
    · have h0 : |x 0| = 1 := by rw [← hm]; exact hx'
      calc 1 + δ = |(1 + δ) * x 0| := by
            rw [abs_mul, h0, abs_of_pos (by linarith), mul_one]
        _ = |((1 + δ) • x) 0| := by rw [smul_coord]
        _ ≤ Plane.supNorm ((1 + δ) • x) := Plane.abs_zero_le_supNorm _
    · have h1 : |x 1| = 1 := by rw [← hm]; exact hx'
      calc 1 + δ = |(1 + δ) * x 1| := by
            rw [abs_mul, h1, abs_of_pos (by linarith), mul_one]
        _ = |((1 + δ) • x) 1| := by rw [smul_coord]
        _ ≤ Plane.supNorm ((1 + δ) • x) := Plane.abs_one_le_supNorm _
  linarith

/-! ### A loop identifies exactly the ends of the parameter interval -/

namespace IsLoop

variable {f g : ℝ → Plane}

/-- Two parameters of `[0,1]` with the same image under a loop are equal, or are the two ends
of the interval. This is the whole of a loop's non-injectivity. -/
theorem param_eq_or (hf : IsLoop f) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (h : f s = f t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs1 : s = 1 <;> by_cases ht1 : t = 1
  · exact Or.inl (hs1.trans ht1.symm)
  · -- `s` is the finish, so the value is also taken at the start, and `t` is the start
    subst hs1
    have h0 : (0 : ℝ) = t :=
      hf.injOn ⟨le_rfl, zero_lt_one⟩ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ (hf.closes.trans h)
    exact Or.inr (Or.inr ⟨rfl, h0.symm⟩)
  · subst ht1
    have h0 : s = 0 :=
      hf.injOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩ ⟨le_rfl, zero_lt_one⟩ (h.trans hf.closes.symm)
    exact Or.inr (Or.inl ⟨h0, rfl⟩)
  · exact Or.inl
      (hf.injOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ h)

/-- Every loop makes the *same* identifications on `[0,1]`. This is what lets a loop be
transported to any other loop: the induced map on images is well defined. -/
theorem eq_of_eq (hf : IsLoop f) (hg : IsLoop g) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (h : f s = f t) : g s = g t := by
  rcases hf.param_eq_or hs ht h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact hg.closes
  · exact hg.closes.symm

/-- **Any two loops induce a homeomorphism between their images, matching parameters.**

`t ↦ f t` is a continuous surjection of the compact `[0,1]` onto the Hausdorff image, hence a
closed map, hence a quotient map; so a map out of the image is continuous as soon as its
composite with the parametrization is. The induced map is well defined by `eq_of_eq`, and
bijective because `eq_of_eq` runs in both directions. -/
theorem exists_homeomorph (hf : IsLoop f) (hg : IsLoop g) :
    ∃ h : ↥(f '' I) ≃ₜ ↥(g '' I),
      ∀ (t : ℝ) (ht : t ∈ I), (h ⟨f t, mem_image_of_mem f ht⟩ : Plane) = g t := by
  classical
  haveI : CompactSpace ↥I := isCompact_iff_compactSpace.mp isCompact_I
  haveI : CompactSpace ↥(f '' I) :=
    isCompact_iff_compactSpace.mp (isCompact_I.image_of_continuousOn hf.continuousOn)
  -- the two parametrizations, read as maps of subtypes
  set q : ↥I → ↥(f '' I) := fun t => ⟨f t, mem_image_of_mem f t.2⟩ with hq
  set q' : ↥I → ↥(g '' I) := fun t => ⟨g t, mem_image_of_mem g t.2⟩ with hq'
  have hqc : Continuous q := (hf.continuousOn.restrict).subtype_mk _
  have hq'c : Continuous q' := (hg.continuousOn.restrict).subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hq's : Function.Surjective q' := by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hquot : IsQuotientMap q := (hqc.isClosedMap).isQuotientMap hqc hqs
  -- the induced map, defined by picking a parameter and reading off the other loop
  set F : ↥(f '' I) → ↥(g '' I) := fun a => q' (Classical.choose (hqs a)) with hF
  have hFq : ∀ t : ↥I, F (q t) = q' t := by
    intro t
    have hchoice := Classical.choose_spec (hqs (q t))
    exact Subtype.ext
      (hf.eq_of_eq hg (Classical.choose (hqs (q t))).2 t.2 (congrArg Subtype.val hchoice))
  have hFc : Continuous F := by
    refine hquot.continuous_iff.mpr ?_
    have : F ∘ q = q' := funext hFq
    rw [this]
    exact hq'c
  have hFinj : Function.Injective F := by
    intro a b hab
    obtain ⟨s, rfl⟩ := hqs a
    obtain ⟨t, rfl⟩ := hqs b
    rw [hFq, hFq] at hab
    exact Subtype.ext (hg.eq_of_eq hf s.2 t.2 (congrArg Subtype.val hab))
  have hFsurj : Function.Surjective F := by
    intro b
    obtain ⟨t, rfl⟩ := hq's b
    exact ⟨q t, hFq t⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFc,
    fun t ht => ?_⟩
  exact congrArg Subtype.val (hFq ⟨t, ht⟩)

end IsLoop

/-! ### Lemma 3.1: parametrization by the model curve -/

namespace IsJordanCurve

/-- **Any two Jordan curves are homeomorphic.** -/
theorem homeomorph {C D : Set Plane} (hC : IsJordanCurve C) (hD : IsJordanCurve D) :
    Nonempty (↥C ≃ₜ ↥D) := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨h, -⟩ := hf.exists_homeomorph hg
  exact ⟨h⟩

end IsJordanCurve

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- Continuity of a bend whose three arguments vary continuously, on a closed set where the
peak stays away from the two endpoints. The two branches are pasted along the closed sets
where the argument is on one or the other side of the peak. -/
theorem continuousOn_bend (r : ℝ) {s : Set Plane} {P Q U : Plane → ℝ} (hs : IsClosed s)
    (hP : Continuous P) (hQ : Continuous Q) (hU : Continuous U)
    (h1 : ∀ z ∈ s, P z + r ≠ 0) (h2 : ∀ z ∈ s, r - P z ≠ 0) :
    ContinuousOn (fun z => bend r (P z) (Q z) (U z)) s := by
  have hcover : s = (s ∩ {z | U z ≤ P z}) ∪ (s ∩ {z | P z ≤ U z}) := by
    ext z
    constructor
    · intro hz
      rcases le_total (U z) (P z) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  rw [hcover]
  refine (continuousOn_union_iff_of_isClosed (hs.inter (isClosed_le hU hP))
    (hs.inter (isClosed_le hP hU))).2 ⟨?_, ?_⟩
  · refine ContinuousOn.congr (f := fun z => -r + (U z + r) * (Q z + r) / (P z + r)) ?_ ?_
    · exact continuousOn_const.add
        (((hU.continuousOn.add continuousOn_const).mul
          (hQ.continuousOn.add continuousOn_const)).div
            (hP.continuousOn.add continuousOn_const) fun z hz => h1 z hz.1)
    · exact fun z hz => bend_of_le hz.2
  · refine ContinuousOn.congr (f := fun z => r - (r - U z) * (r - Q z) / (r - P z)) ?_ ?_
    · exact continuousOn_const.sub
        (((continuousOn_const.sub hU.continuousOn).mul
          (continuousOn_const.sub hQ.continuousOn)).div
            (continuousOn_const.sub hP.continuousOn) fun z hz => h2 z hz.1)
    · exact fun z hz => bend_eq_right (h1 z hz.1) (h2 z hz.1) hz.2

/-! ### Coordinates of the square -/

/-- Conversely, a bound on both coordinate differences bounds the sup distance. -/
theorem supDist_le_of_forall {z c : Plane} {r : ℝ} (h : ∀ l : Fin 2, |z l - c l| ≤ r) :
    supDist z c ≤ r :=
  max_le (h 0) (h 1)

/-- The sup distance is attained at one of the two coordinates. -/
theorem exists_abs_sub_eq_of_supDist_eq {z c : Plane} {r : ℝ} (h : supDist z c = r) :
    ∃ l : Fin 2, |z l - c l| = r := by
  rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
  · exact ⟨0, by rw [← h]; exact hm.symm⟩
  · exact ⟨1, by rw [← h]; exact hm.symm⟩

/-! ### Shearing the square along one coordinate -/

/-- The weight of the level line of `z` transverse to the `i`-th coordinate: it is `1` on the
level `b` and dies away to `0` at the two sides `z j - c j = ±r` of the square. -/
noncomputable def shearWeight (c : Plane) (r b : ℝ) (j : Fin 2) (z : Plane) : ℝ :=
  tent r b (z j - c j)

/-- The shear of the square about `c` of radius `r` in the direction of the `i`-th coordinate.
On the level line indexed by `w = shearWeight`, the `i`-th coordinate is bent by the
piecewise-linear map carrying `a + k * w` to `a + (k + k') * w` and fixing the two sides
`z i - c i = ±r`. Both the map with parameters `k, k'` and its inverse, which has parameters
`k + k', -k'`, belong to this two-parameter family — that is what the second parameter is
for. -/
noncomputable def shear (c : Plane) (r a b k k' : ℝ) (i j : Fin 2) (z : Plane) : Plane :=
  z + (bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
    (z i - c i) - (z i - c i)) • EuclideanSpace.single i (1 : ℝ)

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

theorem shear_apply_same :
    shear c r a b k k' i j z i =
      c i + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z i - c i) := by
  simp only [shear, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    if_true, mul_one]
  ring

theorem shear_apply_ne (h : l ≠ i) : shear c r a b k k' i j z l = z l := by
  simp [shear, h]

/-! ### Movers of the square -/

/-! ### Moving an interior point -/

/-! ### The boundary of the square -/

theorem add_smul_single_apply (z : Plane) (t : ℝ) (l : Fin 2) :
    (z + t • EuclideanSpace.single l (1 : ℝ)) l = z l + t := by
  simp [PiLp.add_apply, PiLp.smul_apply]

theorem dist_add_smul_single (z : Plane) (t : ℝ) (l : Fin 2) :
    dist (z + t • EuclideanSpace.single l (1 : ℝ)) z = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single]
  simp

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
-- module Solutions.Q146_CD.FaceCyclesLand
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil
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

/-- The two ends of an arc are distinct: they are the images of `0` and `1`. -/
theorem IsArcBetween.ne {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨f, -, hinj, -, hf0, hf1⟩ := h
  intro he
  have h01 : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (by rw [hf0, hf1, he])
  norm_num at h01

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

/-- **Every bounded face is the interior of its boundary cycle.** -/
theorem IsFaceCycle.eq_inside_of_isBounded' {z : Plane} {e : β} {u v : Plane} {D : List β}
    (hf : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = Schoenflies.inside (edgesCover drawing (e :: D)) :=
  hf.eq_inside_of_isBounded hbdd

end Graph
end

section
-- module Solutions.Q146_CD.OuterChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A block of length one is a consecutive pair. -/
theorem chainUnion_one (Γ : ℕ → Graph α β) (i : ℕ) :
    chainUnion Γ i 1 = (Γ i).union (Γ (i + 1)) := rfl

theorem mem_edgeSet_chainUnion {e : β} :
    e ∈ E(chainUnion Γ i m) ↔ ∃ p, i ≤ p ∧ p ≤ i + m ∧ e ∈ E(Γ p) := by
  induction m with
  | zero =>
    refine ⟨fun h => ⟨i, le_rfl, by omega, h⟩, ?_⟩
    rintro ⟨p, hp, hp', he⟩
    obtain rfl : p = i := by omega
    exact he
  | succ m ih =>
    rw [chainUnion_succ, edgeSet_union, Set.mem_union, ih]
    constructor
    · rintro (⟨p, hp, hp', he⟩ | he)
      · exact ⟨p, hp, by omega, he⟩
      · exact ⟨i + m + 1, by omega, by omega, he⟩
    · rintro ⟨p, hp, hp', he⟩
      rcases Nat.lt_or_ge p (i + m + 1) with h | h
      · exact Or.inl ⟨p, hp, by omega, he⟩
      · obtain rfl : p = i + m + 1 := by omega
        exact Or.inr he

/-- A block of finite graphs is finite. -/
theorem chainUnion_finite (h : ∀ p, i ≤ p → p ≤ i + m → (Γ p).Finite) :
    (chainUnion Γ i m).Finite := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    have h1 := ih fun p hp hp' => h p hp (by omega)
    have h2 := h (i + m + 1) (by omega) le_rfl
    exact { finite_vertexSet := by
              rw [chainUnion_succ, vertexSet_union]
              exact h1.finite_vertexSet.union h2.finite_vertexSet
            finite_edgeSet := by
              rw [chainUnion_succ, edgeSet_union]
              exact h1.finite_edgeSet.union h2.finite_edgeSet }

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

theorem mem_edgesOutside {H : Graph α β} {W : List β} {g : β} :
    g ∈ edgesOutside H W ↔ g ∈ W ∧ g ∉ E(H) := Iff.rfl

theorem finite_edgesOutside (H : Graph α β) (W : List β) : (edgesOutside H W).Finite :=
  (W.finite_toSet).subset fun _ hg => hg.1

theorem edgesOutside_append (H : Graph α β) (W₁ W₂ : List β) :
    edgesOutside H (W₁ ++ W₂) = edgesOutside H W₁ ∪ edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, List.mem_append, Set.mem_union]
  tauto

theorem edgesOutside_perm {H : Graph α β} {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesOutside H W₁ = edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, hp.mem_iff]

theorem edgesOutside_eq_empty {H : Graph α β} {W : List β} (h : ∀ g ∈ W, g ∈ E(H)) :
    edgesOutside H W = ∅ := by
  ext g
  simp only [mem_edgesOutside, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact h g

/-- **The count the descent step decreases.** Replacing one arc `D₂` of a cycle by a list `R` of
edges the graph `H` already has strictly lowers the number of edges outside `H`, provided the
discarded arc had at least one such edge.

The two arcs of a cycle share no edge, which is why the discarded edge is not silently still
present on the arc that was kept: that is what the `Nodup` hypothesis on the cycle's edge list
supplies. It holds for a cycle because the detour of `Graph.IsCycleThrough` is a path and does
not contain the named edge. -/
theorem edgesOutside_splice_lt {H : Graph α β} {W W' D₁ D₂ R : List β} (hnodup : W.Nodup)
    (hperm : W.Perm (D₁ ++ D₂)) (hperm' : W'.Perm (D₁ ++ R)) (hR : ∀ g ∈ R, g ∈ E(H))
    (hD₂ : ∃ g ∈ D₂, g ∉ E(H)) :
    (edgesOutside H W').ncard < (edgesOutside H W).ncard := by
  obtain ⟨g, hgD₂, hgH⟩ := hD₂
  have hdisj : List.Disjoint D₁ D₂ :=
    List.disjoint_of_nodup_append ((List.Perm.nodup_iff hperm).1 hnodup)
  have hW' : edgesOutside H W' = edgesOutside H D₁ := by
    rw [edgesOutside_perm hperm', edgesOutside_append, edgesOutside_eq_empty hR,
      Set.union_empty]
  have hW : edgesOutside H W = edgesOutside H D₁ ∪ edgesOutside H D₂ := by
    rw [edgesOutside_perm hperm, edgesOutside_append]
  have hsub : edgesOutside H W' ⊆ edgesOutside H W := by
    rw [hW', hW]; exact Set.subset_union_left
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2 ⟨g, ?_, ?_⟩)
    (finite_edgesOutside H W)
  · rw [hW]; exact Or.inr ⟨hgD₂, hgH⟩
  · rw [hW']
    exact fun hg' => hdisj hg'.1 hgD₂

end General

/-! ## Enclosing a point -/

/-! ## The chain -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ} {x : Plane}

namespace IsPlaneChain

variable {i m p : ℕ}

/-- A point of a block's drawing lies on one of its members. -/
theorem mem_pointSet_block {z : Plane} (hz : z ∈ pointSet (chainUnion Γ i m) drawing) :
    ∃ p, i ≤ p ∧ p ≤ i + m ∧ z ∈ pointSet (Γ p) drawing := by
  induction m with
  | zero => exact ⟨i, le_rfl, le_rfl, hz⟩
  | succ m ih =>
    rw [chainUnion_succ, pointSet_union, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨p, hp, hp', hzp⟩ := ih hz
      exact ⟨p, hp, by omega, hzp⟩
    · exact ⟨i + m + 1, by omega, by omega, hz⟩

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

/-- The hypothesis of `lem:outer-chain` on consecutive pairs: `x` is in the outer face of every
`Γ p ∪ Γ (p+1)` — off its drawing, with an unbounded face through it. A consumer proves the
second clause with `Graph.beyondSquare_subset_face`, and `Graph.unbounded_face_unique` is what
makes "an unbounded face" *the* outer face. -/
def OuterOnPairs (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ p, p + 1 ≤ n → x ∈ exterior (chainUnion Γ p 1) drawing ∧
    ¬ Bornology.IsBounded (face (chainUnion Γ p 1) drawing x)

end Chain

end Graph
end

section
-- module Solutions.Q146_CD.SquareCycle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem isWalk (h : G.IsIncWalk f u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

/-- Every vertex the walk visits has value at least the source's. -/
theorem source_le (h : G.IsIncWalk f u W v) : ∀ x ∈ G.walkVertices u W, f u ≤ f x := by
  induction h with
  | nil hy =>
    intro x hx
    rw [walkVertices_nil, mem_singleton_iff] at hx
    exact le_of_eq (by rw [hx])
  | @cons u w v e W hl hf _ ih =>
    intro x hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact le_rfl
    · exact hf.le.trans (ih x hx')

/-- And at most the target's. -/
theorem le_target (h : G.IsIncWalk f u W v) : ∀ x ∈ G.walkVertices u W, f x ≤ f v := by
  induction h with
  | nil hy =>
    intro x hx
    rw [walkVertices_nil, mem_singleton_iff] at hx
    exact le_of_eq (by rw [hx])
  | @cons u w v e W hl hf hW ih =>
    intro x hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact hf.le.trans (ih w mem_walkVertices_self)
    · exact ih x hx'

/-- **An increasing walk is a path.**  The vertex a step departs from has a strictly smaller
value than everything the rest of the walk visits, so it is not among them. -/
theorem isPath (h : G.IsIncWalk f u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hf hW ih =>
    refine .cons hl ih fun hmem => ?_
    exact absurd (hW.source_le u hmem) (not_le.2 hf)

/-- The function may be replaced by any function agreeing with it on the visited vertices. -/
theorem congr_walkVertices (h : G.IsIncWalk f u W v)
    (hfg : ∀ x ∈ G.walkVertices u W, f x = g x) : G.IsIncWalk g u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hf hW ih =>
    refine .cons hl ?_ (ih fun x hx => hfg x (mem_walkVertices_cons_of_mem hl hx))
    rw [← hfg u mem_walkVertices_self,
      ← hfg w (mem_walkVertices_cons_of_mem hl mem_walkVertices_self)]
    exact hf

end IsIncWalk

end Graph

/-! ## Part 2: a tiling of one segment is a chain

Everything here happens along a single ambient segment `[a, b]`, and the coordinate is the one
`Schoenflies/SegmentOrder.lean` supplies: the distance from `a`.  A finite family of
nondegenerate pieces inside `[a, b]`, with disjoint interiors, no end interior to any of them,
and covering the part of `[a, b]` ahead of the current point, is walked through from the current
point to `b`, one piece at a time, in increasing distance from `a`. -/
end

section
-- module Solutions.Q146_CD.BoundaryCyclesGenerated
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A list which is a path in one orientation is a path in every orientation in which the
same ordered edge list is a walk.  The only alternative first orientation can occur for a
single-edge path. -/
theorem isPath_of_isWalk_of_isPath {G : Graph γ γ} {a b x y : γ} {W : List γ}
    (hP : G.IsPath a W b) (hW : G.IsWalk x W y) : G.IsPath x W y := by
  induction hP generalizing x y with
  | nil ha =>
      cases hW with
      | nil hx => exact .nil hx
  | @cons a w b e W hl hP hfresh ih =>
      cases hW with
      | @cons _ w' _ _ _ hl' hW =>
        rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .cons hl (ih hW) hfresh
        · have hnil : W = [] := by
            by_contra hne
            obtain ⟨f, hf, hinc⟩ := hW.exists_inc_source hne
            exact hfresh (Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩)
          subst W
          cases hW with
          | nil hu => exact Graph.IsPath.single hl.symm (Graph.IsPath.cons_ne hP hfresh).symm

end SubdivData

/-! ### The invariant at every generated stage -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
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

def pathHitProbability (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  (μ : Measure C(PathTime, X)) {γ | ∃ t : PathTime, γ t = x}

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLawMixtures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
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

def pathHitReal (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ :=
  (pathHitProbability μ x).toReal

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def visitAtLeastSet {X : Type*} [MetricSpace X] (n : ℕ) :
    Set (C(PathTime, X) × X) :=
  {q | ∃ t : Fin n → PathTime, Injective t ∧ ∀ i, q.1 (t i) = q.2}

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

/-- Extended number of distinct visit times, defined by finite witnesses. -/
def visitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ := by
  classical
  exact ⨆ n : ℕ, if (γ, x) ∈ visitAtLeastSet n then (n : ℝ≥0∞) else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

instance instTopologicalSpaceTagSlot : TopologicalSpace TagSlot := inferInstanceAs (TopologicalSpace (Unit ⊕ TagData))

instance instMeasurableSpaceTagSlot : MeasurableSpace TagSlot := borel TagSlot

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary tolls count every parameter visit. Counting-square-summable
weights have countable support, so their true tolls are Borel. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def boundaryToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : PathTime, m (γ t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathEndpoints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel endpoint and first-arrival restrictions for the base path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def FirstArrival (b : X) (γ : C(PathTime, X)) : Prop :=
  γ ⊤ = b ∧ ∀ t : PathTime, t < ⊤ → γ t ≠ b

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def tagDataTuple (q : TagData) : LevelTuple := ⟨q.1, q.2.1, q.2.2.1⟩

def slotTupleMeasure : TagSlot → Measure LevelTuple :=
  Sum.elim (fun _ => 0) (fun q => Measure.dirac (tagDataTuple q))

def weightedTupleMeasure (θ : ℕ → TagSlot) : Measure LevelTuple :=
  Measure.sum (fun k => slotWeight k • slotTupleMeasure (θ k))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def pathOccupation (γ : RectifiablePath X) : Measure X :=
  (pathLengthMeasure γ).map γ.val

theorem pathOccupation_apply (γ : RectifiablePath X) {s : Set X} (hs : MeasurableSet s) :
    pathOccupation γ s = pathLengthMeasure γ (γ.val ⁻¹' s) :=
  Measure.map_apply γ.val.continuous.measurable hs

theorem pathOccupation_univ (γ : RectifiablePath X) :
    pathOccupation γ univ = eVariationOn γ.val univ := by
  rw [pathOccupation_apply γ MeasurableSet.univ, preimage_univ, pathLengthMeasure_univ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClippedPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant extension of a closed path portion. Its arclength is exactly
the variation of that portion; this is used to assemble local physical lifts. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem monotone_timeClip (a b : PathTime) : Monotone (timeClip a b) :=
  monotone_const.max (monotone_const.min monotone_id)

variable {X : Type*} [MetricSpace X]

theorem variation_timeClip (γ : C(PathTime, X)) {a b : PathTime} (hab : a ≤ b) :
    eVariationOn (γ.comp (timeClip a b)) univ = eVariationOn γ (Icc a b) := by
  change eVariationOn (γ ∘ timeClip a b) univ = _
  rw [eVariationOn.comp_eq_of_monotoneOn γ (timeClip a b)
    ((monotone_timeClip a b).monotoneOn univ), image_univ, range_timeClip hab]

def clippedPath (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) : RectifiablePath X :=
  ⟨γ.val.comp (timeClip a b), by
    change eVariationOn (γ.val.comp (timeClip a b)) univ ≠ ∞
    rw [variation_timeClip γ.val hab]
    exact γ.property.mono (subset_univ _)⟩

theorem pathLengthMeasure_clipped_univ (γ : RectifiablePath X)
    {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure (clippedPath γ hab) univ = pathLengthMeasure γ (Icc a b) := by
  rw [pathLengthMeasure_univ, pathLengthMeasure_Icc γ hab]
  exact variation_timeClip γ.val hab

theorem pathLengthMeasure_clipped_Ioc (γ : RectifiablePath X)
    {a b s t : PathTime} (hab : a ≤ b) (hst : s ≤ t) :
    pathLengthMeasure (clippedPath γ hab) (Ioc s t) =
      pathLengthMeasure γ (Ioc (timeClip a b s) (timeClip a b t)) := by
  rw [pathLengthMeasure_Ioc _ hst,
    pathLengthMeasure_Ioc _ (monotone_timeClip a b hst)]
  change eVariationOn (γ.val ∘ timeClip a b) (Icc s t) = _
  have h := eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ.val (timeClip a b)
    ((monotone_timeClip a b).monotoneOn univ) (mem_univ s) (mem_univ t)
  rw [univ_inter, image_univ, range_timeClip hab] at h
  rw [h, inter_eq_right.mpr]
  intro u hu
  have hs : timeClip a b s ∈ Icc a b := by rw [← range_timeClip hab]; exact mem_range_self s
  have ht : timeClip a b t ∈ Icc a b := by rw [← range_timeClip hab]; exact mem_range_self t
  exact ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathPortionMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength measure of a constant-extended path portion is exactly the
restriction of the original time measure. Thus adjacent portions add without
charging their shared endpoint. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem Ioc_timeClip (a b s t : PathTime) :
    Ioc (timeClip a b s) (timeClip a b t) = Ioc s t ∩ Ioc a b := by
  ext x
  simp only [timeClip, ContinuousMap.coe_mk, mem_Ioc, mem_inter_iff,
    max_lt_iff, min_lt_iff, le_max_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hax, hmid⟩, hu⟩
    have hbt : x ≤ b ∧ x ≤ t := hu.resolve_left (not_le.mpr hax)
    have hs : s < x := hmid.resolve_left (not_lt.mpr hbt.1)
    exact ⟨⟨hs, hbt.2⟩, hax, hbt.1⟩
  · rintro ⟨⟨hs, ht⟩, ha, hb⟩
    exact ⟨⟨ha, Or.inr hs⟩, Or.inr ⟨hb, ht⟩⟩

variable {X : Type*} [MetricSpace X]

theorem pathLengthMeasure_clipped (γ : RectifiablePath X)
    {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure (clippedPath γ hab) = (pathLengthMeasure γ).restrict (Icc a b) := by
  have heq : pathLengthMeasure (clippedPath γ hab) =
      (pathLengthMeasure γ).restrict (Ioc a b) := by
    apply Measure.ext_of_Ioc_finite
    · rw [pathLengthMeasure_clipped_univ γ hab, Measure.restrict_apply_univ,
        pathLengthMeasure_Icc γ hab, pathLengthMeasure_Ioc γ hab]
    · intro s t hst
      rw [pathLengthMeasure_clipped_Ioc γ hab hst.le,
        Measure.restrict_apply measurableSet_Ioc, Ioc_timeClip]
  exact heq.trans (Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ)))

variable [MeasurableSpace X] [BorelSpace X]

def pathPortionOccupation (γ : RectifiablePath X) (a b : PathTime) : Measure X :=
  ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val

omit [BorelSpace X] in
theorem pathOccupation_clipped (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathOccupation (clippedPath γ hab) = pathPortionOccupation γ a b := by
  rw [pathOccupation, pathLengthMeasure_clipped γ hab]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (max a (min b t)) = γ.val t
  rw [min_eq_right ht.2, max_eq_right ht.1]

omit [BorelSpace X] in
theorem pathPortionOccupation_congr (γ η : RectifiablePath X) {a b : PathTime}
    (hab : a ≤ b) (heq : EqOn γ.val η.val (Icc a b)) :
    pathPortionOccupation γ a b = pathPortionOccupation η a b := by
  rw [← pathOccupation_clipped γ hab, ← pathOccupation_clipped η hab]
  congr 1
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply heq
  rw [← range_timeClip hab]
  exact mem_range_self t

theorem pathPortionOccupation_add (γ : RectifiablePath X)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    pathPortionOccupation γ a c =
      pathPortionOccupation γ a b + pathPortionOccupation γ b c := by
  have hrestr : (pathLengthMeasure γ).restrict (Icc a c) =
      (pathLengthMeasure γ).restrict (Icc a b) + (pathLengthMeasure γ).restrict (Icc b c) := by
    have hdis : AEDisjoint (pathLengthMeasure γ) (Icc a b) (Icc b c) := by
      rw [AEDisjoint]
      have heq : Icc a b ∩ Icc b c = {b} := by
        ext x
        simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
        constructor
        · rintro ⟨⟨_, hxb⟩, hbx, _⟩
          exact le_antisymm hxb hbx
        · rintro rfl
          exact ⟨⟨hab, le_rfl⟩, le_rfl, hbc⟩
      rw [heq]
      exact measure_singleton b
    rw [← Icc_union_Icc_eq_Icc hab hbc]
    exact Measure.restrict_union₀ hdis measurableSet_Icc.nullMeasurableSet
  rw [pathPortionOccupation, hrestr, Measure.map_add]
  · rfl
  · exact γ.val.continuous.measurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectifiableOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel occupation code on the Borel subset of rectifiable paths.
The total extension is zero off that subset; length finiteness is always
checked separately before it is used as physical occupation. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def rectifiableOccupationCode (γ : C(PathTime, X)) : Measure X :=
  if h : BoundedVariationOn γ univ then pathOccupation ⟨γ, h⟩ else 0

omit [BorelSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem rectifiableOccupationCode_eq {γ : C(PathTime, X)}
    (hγ : BoundedVariationOn γ univ) :
    rectifiableOccupationCode γ = pathOccupation ⟨γ, hγ⟩ := by
  simp only [rectifiableOccupationCode, dite_eq_left hγ]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem rectifiableOccupationCode_univ {γ : C(PathTime, X)}
    (hγ : BoundedVariationOn γ univ) :
    rectifiableOccupationCode γ univ = eVariationOn γ univ := by
  rw [rectifiableOccupationCode_eq hγ, pathOccupation_univ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathLengthLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time arclength is local on closed intervals and adds at shared endpoints. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def rectifiableLengthCode (γ : C(PathTime, X)) : Measure PathTime :=
  if h : BoundedVariationOn γ univ then pathLengthMeasure ⟨γ, h⟩ else 0

theorem rectifiableLengthCode_eq {γ : C(PathTime, X)} (hγ : BoundedVariationOn γ univ) :
    rectifiableLengthCode γ = pathLengthMeasure ⟨γ, hγ⟩ := by
  simp only [rectifiableLengthCode, dite_eq_left hγ]

theorem rectifiableLengthCode_univ {γ : C(PathTime, X)} (hγ : BoundedVariationOn γ univ) :
    rectifiableLengthCode γ univ = eVariationOn γ univ := by
  rw [rectifiableLengthCode_eq hγ, pathLengthMeasure_univ]

instance instNullSingletonClassElemRealPathTimeRectifiableLengthCode (γ : C(PathTime, X)) : NullSingletonClass (rectifiableLengthCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableLengthCode_eq hγ]; infer_instance
  · simp only [rectifiableLengthCode, dite_eq_right hγ]
    exact ⟨fun _ => by simp⟩

theorem rectifiableLengthCode_const (x : X) :
    rectifiableLengthCode (ContinuousMap.const PathTime x) = 0 := by
  have hv : eVariationOn (ContinuousMap.const PathTime x) univ = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro _ _ _ _
    exact edist_self x
  have hb : BoundedVariationOn (ContinuousMap.const PathTime x) univ := by
    change eVariationOn _ _ ≠ ∞
    rw [hv]
    exact ENNReal.zero_ne_top
  apply Measure.measure_univ_eq_zero.mp
  rw [rectifiableLengthCode_univ hb, hv]

theorem pathLengthMeasure_restrict_congr (γ η : RectifiablePath X) {a b : PathTime}
    (heq : EqOn γ.val η.val (Icc a b)) :
    (pathLengthMeasure γ).restrict (Icc a b) =
      (pathLengthMeasure η).restrict (Icc a b) := by
  by_cases hab : a ≤ b
  · rw [← pathLengthMeasure_clipped γ hab, ← pathLengthMeasure_clipped η hab]
    congr 1
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    apply heq
    rw [← range_timeClip hab]
    exact mem_range_self t
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simp

theorem pathLengthMeasure_restrict_add (γ : RectifiablePath X)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    (pathLengthMeasure γ).restrict (Icc a c) =
      (pathLengthMeasure γ).restrict (Icc a b) +
      (pathLengthMeasure γ).restrict (Icc b c) := by
  have hd : AEDisjoint (pathLengthMeasure γ) (Icc a b) (Icc b c) := by
    rw [AEDisjoint]
    have heq : Icc a b ∩ Icc b c = {b} := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, h₁⟩, h₂, _⟩
        exact h₁.antisymm h₂
      · rintro rfl
        exact ⟨⟨hab, le_rfl⟩, le_rfl, hbc⟩
    rw [heq]
    exact measure_singleton b
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact Measure.restrict_union₀ hd measurableSet_Icc.nullMeasurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem physicalSubpath_eq_on {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b c d : PathTime} (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    {t : PathTime} (ht₁ : t ∈ Icc a b) (ht₂ : t ∈ Icc c d) :
    physicalSubpath e hab ⟨γ, h₁⟩ t = physicalSubpath e hcd ⟨γ, h₂⟩ t := by
  simp only [physicalSubpath, ContinuousMap.coe_mk, timeClip,
    min_eq_right ht₁.2, max_eq_right ht₁.1,
    min_eq_right ht₂.2, max_eq_right ht₂.1]

theorem physicalSubpath_comp_clip {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) :
    (physicalSubpath e hab γ).comp (timeClip a b) = physicalSubpath e hab γ := by
  apply ContinuousMap.ext
  intro t
  have ht : timeClip a b t ∈ Icc a b := by
    rw [← range_timeClip hab]
    exact mem_range_self t
  simp only [ContinuousMap.comp_apply, physicalSubpath, ContinuousMap.coe_mk]
  apply congrArg Subtype.val
  apply congrArg e.symm
  apply Subtype.ext
  apply congrArg γ.val
  change max a (min b (timeClip a b t)) = timeClip a b t
  rw [min_eq_right ht.2, max_eq_right ht.1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalTimeLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical time arclength is local and adds across a subdivision. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalSubpath_timeLength_portion (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    (hγ : BoundedVariationOn (physicalSubpath e hab γ) univ) :
    rectifiableLengthCode (physicalSubpath e hab γ) =
      (pathLengthMeasure ⟨physicalSubpath e hab γ, hγ⟩).restrict (Icc a b) := by
  rw [rectifiableLengthCode_eq hγ, ← pathLengthMeasure_clipped _ hab]
  congr 1
  apply Subtype.ext
  exact (physicalSubpath_comp_clip e hab γ).symm

theorem physicalSubpath_timeLength_add (e : G ≃ₜ U)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a c)
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U b c)
    (hwhole : BoundedVariationOn (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) univ)
    (hleft : BoundedVariationOn (physicalSubpath e hab ⟨γ, h₁⟩) univ)
    (hright : BoundedVariationOn (physicalSubpath e hbc ⟨γ, h₂⟩) univ) :
    rectifiableLengthCode (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) =
      rectifiableLengthCode (physicalSubpath e hab ⟨γ, h₁⟩) +
      rectifiableLengthCode (physicalSubpath e hbc ⟨γ, h₂⟩) := by
  let whole : RectifiablePath Y := ⟨physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩, hwhole⟩
  let left : RectifiablePath Y := ⟨physicalSubpath e hab ⟨γ, h₁⟩, hleft⟩
  let right : RectifiablePath Y := ⟨physicalSubpath e hbc ⟨γ, h₂⟩, hright⟩
  have hl : EqOn whole.val left.val (Icc a b) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hab γ hγ h₁
      ⟨ht.1, ht.2.trans hbc⟩ ht
  have hr : EqOn whole.val right.val (Icc b c) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hbc γ hγ h₂
      ⟨hab.trans ht.1, ht.2⟩ ht
  rw [physicalSubpath_timeLength_portion e (hab.trans hbc) _ hwhole,
    pathLengthMeasure_restrict_add _ hab hbc,
    pathLengthMeasure_restrict_congr whole left hl,
    pathLengthMeasure_restrict_congr whole right hr,
    ← physicalSubpath_timeLength_portion e hab _ hleft,
    ← physicalSubpath_timeLength_portion e hbc _ hright]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DyadicTimes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed dyadic time partitions used to assemble physical-domain length. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem dyadicReal_even (n i : ℕ) : dyadicReal (n + 1) (2 * i) = dyadicReal n i := by
  unfold dyadicReal
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadicLeft_even (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicLeft (n + 1) (dyadicEven n i) = dyadicLeft n i := by
  apply Subtype.ext
  exact dyadicReal_even n i.val

theorem dyadicRight_odd (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicRight (n + 1) (dyadicOdd n i) = dyadicRight n i := by
  apply Subtype.ext
  change dyadicReal (n + 1) (2 * i.val + 1 + 1) = dyadicReal n (i.val + 1)
  rw [show 2 * i.val + 1 + 1 = 2 * (i.val + 1) by omega]
  exact dyadicReal_even n (i.val + 1)

theorem dyadicRight_even (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicRight (n + 1) (dyadicEven n i) = dyadicLeft (n + 1) (dyadicOdd n i) := rfl

theorem dyadicCell_split (n : ℕ) (i : Fin (2 ^ n)) :
    Icc (dyadicLeft n i) (dyadicRight n i) =
      Icc (dyadicLeft (n + 1) (dyadicEven n i)) (dyadicRight (n + 1) (dyadicEven n i)) ∪
      Icc (dyadicLeft (n + 1) (dyadicOdd n i)) (dyadicRight (n + 1) (dyadicOdd n i)) := by
  have hmid : dyadicRight (n + 1) (dyadicEven n i) ≤ dyadicRight (n + 1) (dyadicOdd n i) := by
    rw [dyadicRight_even]
    exact dyadicLeft_le_right _ _
  rw [← dyadicRight_even, Icc_union_Icc_eq_Icc (dyadicLeft_le_right _ _) hmid,
    dyadicLeft_even, dyadicRight_odd]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalDyadicLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalDyadicLength_le_domain (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicLength e y₀ n i γ ≤ physicalDomainLength e y₀ γ :=
  (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans
    (le_iSup (fun n => physicalStageLength e y₀ n γ) n)

theorem physicalDyadicPath_rectifiable (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) : BoundedVariationOn (physicalDyadicPath e y₀ n i γ) univ :=
  ne_of_lt ((physicalDyadicLength_le_domain e y₀ γ n i).trans_lt hγ)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

variable [MeasurableSpace Y] [BorelSpace Y]

def physicalStageOccupation (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (γ : C(PathTime, X)) : Measure Y :=
  ∑ i : Fin (2 ^ n), rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationAdd
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical arclength occupation is independent of the chosen compact
restriction and adds across a subdivision of the same physical path. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [BorelSpace Y] in
theorem physicalSubpath_occupation_portion (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    (hγ : BoundedVariationOn (physicalSubpath e hab γ) univ) :
    rectifiableOccupationCode (physicalSubpath e hab γ) =
      pathPortionOccupation ⟨physicalSubpath e hab γ, hγ⟩ a b := by
  rw [rectifiableOccupationCode_eq hγ, ← pathOccupation_clipped _ hab]
  congr 1
  apply Subtype.ext
  exact (physicalSubpath_comp_clip e hab γ).symm

theorem physicalSubpath_occupation_add (e : G ≃ₜ U)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a c)
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U b c)
    (hwhole : BoundedVariationOn (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) univ)
    (hleft : BoundedVariationOn (physicalSubpath e hab ⟨γ, h₁⟩) univ)
    (hright : BoundedVariationOn (physicalSubpath e hbc ⟨γ, h₂⟩) univ) :
    rectifiableOccupationCode (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) =
      rectifiableOccupationCode (physicalSubpath e hab ⟨γ, h₁⟩) +
      rectifiableOccupationCode (physicalSubpath e hbc ⟨γ, h₂⟩) := by
  let whole : RectifiablePath Y := ⟨physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩, hwhole⟩
  let left : RectifiablePath Y := ⟨physicalSubpath e hab ⟨γ, h₁⟩, hleft⟩
  let right : RectifiablePath Y := ⟨physicalSubpath e hbc ⟨γ, h₂⟩, hright⟩
  have hl : EqOn whole.val left.val (Icc a b) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hab γ hγ h₁
      ⟨ht.1, ht.2.trans hbc⟩ ht
  have hr : EqOn whole.val right.val (Icc b c) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hbc γ hγ h₂
      ⟨hab.trans ht.1, ht.2⟩ ht
  rw [physicalSubpath_occupation_portion e (hab.trans hbc) _ hwhole,
    pathPortionOccupation_add _ hab hbc,
    pathPortionOccupation_congr whole left hab hl,
    pathPortionOccupation_congr whole right hbc hr,
    ← physicalSubpath_occupation_portion e hab _ hleft,
    ← physicalSubpath_occupation_portion e hbc _ hright]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalDyadicMonotone
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refinement of the dyadic physical occupation measures. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem rectifiableOccupationCode_const (y : Y) :
    rectifiableOccupationCode (ContinuousMap.const PathTime y) = 0 := by
  have hv : eVariationOn (ContinuousMap.const PathTime y) univ = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro _ _ _ _
    exact edist_self y
  have hb : BoundedVariationOn (ContinuousMap.const PathTime y) univ := by
    change eVariationOn (ContinuousMap.const PathTime y) univ ≠ ∞
    rw [hv]
    exact ENNReal.zero_ne_top
  apply Measure.measure_univ_eq_zero.mp
  rw [rectifiableOccupationCode_univ hb, hv]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalDyadicPath_of_mem (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    physicalDyadicPath e y₀ n i γ = physicalSubpath e (dyadicLeft_le_right n i) ⟨γ, hγ⟩ := by
  classical
  simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_left hγ]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalSubpath_congr_endpoints (e : G ≃ₜ U) {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (ha : a = c) (hb : b = d) :
    physicalSubpath e hab ⟨γ, h₁⟩ = physicalSubpath e hcd ⟨γ, h₂⟩ := by
  cases ha
  cases hb
  rfl

theorem physicalDyadicOccupation_split (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n))
    (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  have h₁ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicEven n i))
      (dyadicRight (n + 1) (dyadicEven n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_left
  have h₂ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicOdd n i))
      (dyadicRight (n + 1) (dyadicOdd n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_right
  have hw := physicalDyadicPath_rectifiable e y₀ hfin n i
  have hl := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicEven n i)
  have hr := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicOdd n i)
  rw [physicalDyadicPath_of_mem e y₀ n i γ hγ] at hw ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicEven n i) γ h₁] at hl ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicOdd n i) γ h₂] at hr ⊢
  have hab : dyadicLeft n i ≤ dyadicRight (n + 1) (dyadicEven n i) := by
    simpa only [dyadicLeft_even] using dyadicLeft_le_right (n + 1) (dyadicEven n i)
  have hbc : dyadicRight (n + 1) (dyadicEven n i) ≤ dyadicRight n i := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using
      dyadicLeft_le_right (n + 1) (dyadicOdd n i)
  have h₁' : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight (n + 1) (dyadicEven n i)) := by
    simpa only [dyadicLeft_even] using h₁
  have h₂' : γ ∈ pathsInsideOn U (dyadicRight (n + 1) (dyadicEven n i)) (dyadicRight n i) := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using h₂
  have heq₁ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hab γ h₁ h₁'
    (dyadicLeft_even n i) rfl
  have heq₂ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hbc γ h₂ h₂'
    (dyadicRight_even n i).symm (dyadicRight_odd n i)
  rw [heq₁] at hl ⊢
  rw [heq₂] at hr ⊢
  exact physicalSubpath_occupation_add e hab hbc γ hγ h₁' h₂' hw hl hr

theorem physicalDyadicOccupation_le_children (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) :
    rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ) ≤
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  classical
  by_cases hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · exact (physicalDyadicOccupation_split e y₀ hfin n i hγ).le
  · simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hγ,
      rectifiableOccupationCode_const]
    exact bot_le

theorem monotone_physicalStageOccupation (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞) :
    Monotone (fun n => physicalStageOccupation e y₀ n γ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [physicalStageOccupation, physicalStageOccupation, sum_dyadic_children]
  exact Finset.sum_le_sum fun i _ => physicalDyadicOccupation_le_children e y₀ hfin n i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DyadicPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel limit of the increasing dyadic physical occupation measures.
Its mass is the dyadic domain-length functional, and it is supported in the
physical domain. `PhysicalLengthCharacterization` identifies the associated
time measure with compact-interval arclength and componentwise exhaustion. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

abbrev FinitePhysicalPath (e : G ≃ₜ U) (y₀ : Y) :=
  {γ : C(PathTime, X) // physicalDomainLength e y₀ γ < ∞}

def dyadicPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) : Measure Y :=
  increasingMeasureLimit (fun n => physicalStageOccupation e y₀ n γ.val)
    (monotone_physicalStageOccupation e y₀ γ.property)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DyadicTimeLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atomless time arclength measure on the open physical-domain times. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalStageTimeLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ)
    (γ : C(PathTime, X)) : Measure PathTime :=
  ∑ i : Fin (2 ^ n), rectifiableLengthCode (physicalDyadicPath e y₀ n i γ)

theorem physicalDyadicTimeLength_split (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n))
    (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    rectifiableLengthCode (physicalDyadicPath e y₀ n i γ) =
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  have h₁ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicEven n i))
      (dyadicRight (n + 1) (dyadicEven n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_left
  have h₂ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicOdd n i))
      (dyadicRight (n + 1) (dyadicOdd n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_right
  have hw := physicalDyadicPath_rectifiable e y₀ hfin n i
  have hl := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicEven n i)
  have hr := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicOdd n i)
  rw [physicalDyadicPath_of_mem e y₀ n i γ hγ] at hw ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicEven n i) γ h₁] at hl ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicOdd n i) γ h₂] at hr ⊢
  have hab : dyadicLeft n i ≤ dyadicRight (n + 1) (dyadicEven n i) := by
    simpa only [dyadicLeft_even] using dyadicLeft_le_right (n + 1) (dyadicEven n i)
  have hbc : dyadicRight (n + 1) (dyadicEven n i) ≤ dyadicRight n i := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using
      dyadicLeft_le_right (n + 1) (dyadicOdd n i)
  have h₁' : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight (n + 1) (dyadicEven n i)) := by
    simpa only [dyadicLeft_even] using h₁
  have h₂' : γ ∈ pathsInsideOn U (dyadicRight (n + 1) (dyadicEven n i)) (dyadicRight n i) := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using h₂
  have heq₁ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hab γ h₁ h₁'
    (dyadicLeft_even n i) rfl
  have heq₂ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hbc γ h₂ h₂'
    (dyadicRight_even n i).symm (dyadicRight_odd n i)
  rw [heq₁] at hl ⊢
  rw [heq₂] at hr ⊢
  exact physicalSubpath_timeLength_add e hab hbc γ hγ h₁' h₂' hw hl hr

theorem physicalDyadicTimeLength_le_children (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) :
    rectifiableLengthCode (physicalDyadicPath e y₀ n i γ) ≤
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  classical
  by_cases hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · exact (physicalDyadicTimeLength_split e y₀ hfin n i hγ).le
  · simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hγ,
      rectifiableLengthCode_const]
    exact bot_le

theorem monotone_physicalStageTimeLength (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞) :
    Monotone (fun n => physicalStageTimeLength e y₀ n γ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [physicalStageTimeLength, physicalStageTimeLength, sum_dyadic_children]
  exact Finset.sum_le_sum fun i _ => physicalDyadicTimeLength_le_children e y₀ hfin n i


def physicalTimeLength (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) : Measure PathTime :=
  increasingMeasureLimit (fun n => physicalStageTimeLength e y₀ n γ.val)
    (monotone_physicalStageTimeLength e y₀ γ.property)

theorem physicalTimeLength_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set PathTime} (hs : MeasurableSet s) :
    physicalTimeLength e y₀ γ s = ⨆ n, physicalStageTimeLength e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem physicalStageTimeLength_univ (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageTimeLength e y₀ n γ.val univ = physicalStageLength e y₀ n γ.val := by
  simp only [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableLengthCode_univ (physicalDyadicPath_rectifiable e y₀ γ.property n _)]
  rfl

theorem physicalTimeLength_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalTimeLength e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [physicalTimeLength_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageTimeLength_univ]
  rfl

instance instIsFiniteMeasureElemRealPathTimePhysicalTimeLength (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (physicalTimeLength e y₀ γ) :=
  ⟨by rw [physicalTimeLength_univ]; exact γ.property⟩

instance instNullSingletonClassElemRealPathTimePhysicalTimeLength (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    NullSingletonClass (physicalTimeLength e y₀ γ) := by
  constructor
  intro t
  rw [physicalTimeLength_apply _ _ _ (measurableSet_singleton t)]
  simp [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply, measure_singleton]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DyadicPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic partitions exhaust every compact interval inside an open set. -/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def dyadicNode (n i : ℕ) : PathTime :=
  dyadicTime n ⟨min i (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem monotone_dyadicNode (n : ℕ) : Monotone (dyadicNode n) := by
  intro i j hij
  exact dyadicReal_mono n (min_le_min_right _ hij)

theorem dyadicNode_zero (n : ℕ) : dyadicNode n 0 = ⊥ := by
  apply Subtype.ext
  simp [dyadicNode, dyadicTime, dyadicReal]

theorem dyadicNode_last (n : ℕ) : dyadicNode n (2 ^ n) = ⊤ := by
  apply Subtype.ext
  simp [dyadicNode, dyadicTime, dyadicReal]

theorem dyadicNode_left (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicNode n i = dyadicLeft n i := by
  apply Subtype.ext
  simp [dyadicNode, dyadicLeft, dyadicTime]

theorem dyadicNode_right (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicNode n (i.val + 1) = dyadicRight n i := by
  apply Subtype.ext
  simp [dyadicNode, dyadicRight, dyadicTime]

theorem sum_dyadic_variations {Y : Type*} [PseudoEMetricSpace Y]
    (ρ : PathTime → Y) (n : ℕ) :
    ∑ i : Fin (2 ^ n), eVariationOn ρ (Icc (dyadicLeft n i) (dyadicRight n i)) =
      eVariationOn ρ univ := by
  have h := eVariationOn.sum' ρ (monotone_dyadicNode n) (n := 2 ^ n)
  rw [dyadicNode_zero, dyadicNode_last, Icc_bot_top] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [dyadicNode_left, dyadicNode_right]

theorem dyadicCell_dist_le (n : ℕ) (i : Fin (2 ^ n))
    {s t : PathTime} (hs : s ∈ Icc (dyadicLeft n i) (dyadicRight n i))
    (ht : t ∈ Icc (dyadicLeft n i) (dyadicRight n i)) :
    dist s t ≤ 1 / (2 : ℝ) ^ n := by
  change |(s : ℝ) - (t : ℝ)| ≤ _
  have hlen : (dyadicRight n i : ℝ) - (dyadicLeft n i : ℝ) = 1 / (2 : ℝ) ^ n := by
    change ((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (i.val : ℝ) / (2 : ℝ) ^ n = _
    push_cast
    ring
  change (dyadicLeft n i : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (dyadicRight n i : ℝ) at hs
  change (dyadicLeft n i : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (dyadicRight n i : ℝ) at ht
  rw [abs_le]
  constructor <;> linarith

theorem exists_dyadic_cells_inside {V : Set PathTime} (hV : IsOpen V)
    {a b : PathTime} (hab : Icc a b ⊆ V) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hV hab
  have hlim : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hh := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hp
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Function.comp_apply, one_div]
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨n, fun i hi t ht => hsub ?_⟩
  obtain ⟨s, hs, hsi⟩ := hi
  exact Metric.mem_thickening_iff.mpr ⟨s, hsi, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalCompactLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic domain length controls every compact physical subinterval.
In particular it implies the local rectifiability required by the manuscript. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem timeClip_mapsTo_of_inter {a b c d : PathTime}
    (hi : (Icc a b ∩ Icc c d).Nonempty) : MapsTo (timeClip a b) (Icc c d) (Icc c d) := by
  obtain ⟨p, hp, hpc⟩ := hi
  intro t ht
  change c ≤ max a (min b t) ∧ max a (min b t) ≤ d
  exact ⟨le_max_of_le_right (le_min (hpc.1.trans hp.2) ht.1),
    max_le (hp.1.trans hpc.2) ((min_le_right _ _).trans ht.2)⟩

theorem timeClip_eq_const_of_disjoint {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (hi : ¬ (Icc a b ∩ Icc c d).Nonempty) :
    (EqOn (timeClip a b) (fun _ => a) (Icc c d)) ∨
    (EqOn (timeClip a b) (fun _ => b) (Icc c d)) := by
  have hsep : b < c ∨ d < a := by
    rw [Icc_inter_Icc, nonempty_Icc] at hi
    by_contra h
    push Not at h
    exact hi (max_le (le_min hab h.2) (le_min h.1 hcd))
  rcases hsep with h | h
  · right
    intro t ht
    change max a (min b t) = b
    rw [min_eq_left (h.le.trans ht.1), max_eq_right hab]
  · left
    intro t ht
    change max a (min b t) = a
    exact max_eq_left ((min_le_right _ _).trans (ht.2.trans h.le))

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalSubpath_clip_agree (e : G ≃ₜ U) {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (hi : (Icc a b ∩ Icc c d).Nonempty) :
    EqOn (physicalSubpath e hab ⟨γ, h₁⟩)
      ((physicalSubpath e hcd ⟨γ, h₂⟩) ∘ timeClip a b) (Icc c d) := by
  intro t ht
  have hclip : timeClip a b t ∈ Icc a b := by
    rw [← range_timeClip hab]
    exact mem_range_self t
  have hfix := congrArg (fun f : C(PathTime, Y) => f t)
    (physicalSubpath_comp_clip e hab ⟨γ, h₁⟩)
  exact hfix.symm.trans (physicalSubpath_eq_on e hab hcd γ h₁ h₂ hclip
    (timeClip_mapsTo_of_inter hi ht))

theorem physicalSubpath_variation_le_cell (e : G ≃ₜ U) {a b : PathTime}
    (hab : a ≤ b) (γ : C(PathTime, X)) (hγ : γ ∈ pathsInsideOn U a b)
    (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (hgood : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩)
      (Icc (dyadicLeft n i) (dyadicRight n i)) ≤ physicalDyadicLength e y₀ n i γ := by
  by_cases hi : (Icc a b ∩ Icc (dyadicLeft n i) (dyadicRight n i)).Nonempty
  · have hg := hgood (by rwa [inter_comm])
    rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i γ hg,
      eVariationOn.congr (physicalSubpath_clip_agree e hab (dyadicLeft_le_right n i) γ hγ hg hi)]
    exact (eVariationOn.comp_le_of_monotoneOn _ (timeClip a b)
      ((monotone_timeClip a b).monotoneOn _) (timeClip_mapsTo_of_inter hi)).trans
      (eVariationOn.mono _ (subset_univ _))
  · have hf : ∀ t, physicalSubpath e hab ⟨γ, hγ⟩ t =
        physicalSubpath e hab ⟨γ, hγ⟩ (timeClip a b t) := by
      intro t
      exact (congrArg (fun f : C(PathTime, Y) => f t)
        (physicalSubpath_comp_clip e hab ⟨γ, hγ⟩)).symm
    have hc := timeClip_eq_const_of_disjoint hab (dyadicLeft_le_right n i) hi
    have hz : eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩)
        (Icc (dyadicLeft n i) (dyadicRight n i)) = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      rcases hc with hc | hc <;> intro s hs t ht <;> rw [hf s, hf t, hc hs, hc ht, edist_self]
    rw [hz]
    exact bot_le

theorem physicalSubpath_length_le_domain (e : G ≃ₜ U) (hU : IsOpen U)
    {a b : PathTime} (hab : a ≤ b) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a b) (y₀ : Y) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ ≤ physicalDomainLength e y₀ γ := by
  obtain ⟨n, hn⟩ := exists_dyadic_cells_inside (hU.preimage γ.continuous) hγ
  rw [← sum_dyadic_variations _ n]
  exact (Finset.sum_le_sum fun i _ => physicalSubpath_variation_le_cell e hab γ hγ y₀ n i
    (fun hi => hn i hi)).trans (le_iSup (fun n => physicalStageLength e y₀ n γ) n)

theorem physicalSubpath_rectifiable (e : G ≃ₜ U) (hU : IsOpen U)
    {a b : PathTime} (hab : a ≤ b) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a b) (y₀ : Y) (hfin : physicalDomainLength e y₀ γ < ∞) :
    BoundedVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ :=
  ne_of_lt ((physicalSubpath_length_le_domain e hU hab γ hγ y₀).trans_lt hfin)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DyadicMeasurePartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomless measures split exactly over the closed dyadic cells. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem restrict_Icc_add (μ : Measure PathTime) [NullSingletonClass μ]
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.restrict (Icc a c) = μ.restrict (Icc a b) + μ.restrict (Icc b c) := by
  have hd : AEDisjoint μ (Icc a b) (Icc b c) := by
    rw [AEDisjoint, Icc_inter_Icc_eq_singleton hab hbc]
    exact measure_singleton b
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact Measure.restrict_union₀ hd measurableSet_Icc.nullMeasurableSet

theorem sum_dyadic_restrict (μ : Measure PathTime) [NullSingletonClass μ] (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ.restrict (Icc (dyadicLeft n i) (dyadicRight n i)) = μ := by
  induction n with
  | zero =>
    change (∑ i : Fin 1, μ.restrict (Icc (dyadicLeft 0 i) (dyadicRight 0 i))) = μ
    rw [Fin.sum_univ_one]
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr, Icc_bot_top, Measure.restrict_univ]
  | succ n ih =>
    rw [sum_dyadic_children]
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [← dyadicRight_even, ← restrict_Icc_add μ (dyadicLeft_le_right _ _)]
    · rw [dyadicLeft_even, dyadicRight_odd]
    · rw [dyadicRight_even]
      exact dyadicLeft_le_right _ _

theorem eventually_dyadic_cells_inside {V : Set PathTime} (hV : IsOpen V)
    {a b : PathTime} (hab : Icc a b ⊆ V) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hV hab
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hp using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Function.comp_apply, one_div]
  filter_upwards [(tendsto_order.1 hlim).2 δ hδ] with n hn i hi t ht
  obtain ⟨s, hs, hsi⟩ := hi
  exact hsub (Metric.mem_thickening_iff.mpr
    ⟨s, hsi, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalLengthRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global time measure restricts to ordinary physical arclength on
 every compact interval contained in the open physical-domain times. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalSubpath_length_inter (e : G ≃ₜ U)
    {a b c d : PathTime} (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (hb₁ : BoundedVariationOn (physicalSubpath e hab ⟨γ, h₁⟩) univ)
    (hb₂ : BoundedVariationOn (physicalSubpath e hcd ⟨γ, h₂⟩) univ) :
    (rectifiableLengthCode (physicalSubpath e hab ⟨γ, h₁⟩)).restrict (Icc c d) =
      (rectifiableLengthCode (physicalSubpath e hcd ⟨γ, h₂⟩)).restrict (Icc a b) := by
  rw [physicalSubpath_timeLength_portion e hab _ hb₁,
    physicalSubpath_timeLength_portion e hcd _ hb₂,
    Measure.restrict_restrict measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, inter_comm (Icc c d), Icc_inter_Icc]
  apply pathLengthMeasure_restrict_congr
  intro t ht
  rw [← Icc_inter_Icc] at ht
  exact physicalSubpath_eq_on e hab hcd γ h₁ h₂ ht.1 ht.2

theorem physicalDyadicTimeLength_restrict (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) (n : ℕ) (i : Fin (2 ^ n))
    (hgood : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).restrict (Icc a b) =
      (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
        (Icc (dyadicLeft n i) (dyadicRight n i)) := by
  classical
  by_cases hi : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty
  · have hg := hgood hi
    have hc := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hg] at hc ⊢
    exact physicalSubpath_length_inter e (dyadicLeft_le_right n i) hab γ.val hg hγ hc
      (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property)
  · have hzero : (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
        (Icc (dyadicLeft n i) (dyadicRight n i)) = 0 := by
      rw [physicalSubpath_timeLength_portion e hab _
        (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property),
        Measure.restrict_restrict measurableSet_Icc, not_nonempty_iff_eq_empty.mp hi,
        Measure.restrict_empty]
    rw [hzero]
    by_cases hg : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    · rw [physicalDyadicPath_of_mem e y₀ n i γ.val hg,
        physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) _ (by
          have h := physicalDyadicPath_rectifiable e y₀ γ.property n i
          rwa [physicalDyadicPath_of_mem e y₀ n i γ.val hg] at h),
        Measure.restrict_restrict measurableSet_Icc, inter_comm,
        not_nonempty_iff_eq_empty.mp hi, Measure.restrict_empty]
    · simp [physicalDyadicPath, totalPhysicalSubpath, hg, rectifiableLengthCode_const]

theorem physicalStageTimeLength_restrict (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) (n : ℕ)
    (hgood : ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    (physicalStageTimeLength e y₀ n γ.val).restrict (Icc a b) =
      rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
  calc
    _ = ∑ i : Fin (2 ^ n),
        (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).restrict (Icc a b) := by
      ext s hs
      simp [physicalStageTimeLength, Measure.restrict_apply hs,
        Measure.coe_finsetSum, Finset.sum_apply]
    _ = ∑ i : Fin (2 ^ n),
        (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
          (Icc (dyadicLeft n i) (dyadicRight n i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact physicalDyadicTimeLength_restrict e hU y₀ γ hab hγ n i (hgood i)
    _ = _ := sum_dyadic_restrict _ n

theorem physicalTimeLength_restrict_compact (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    (physicalTimeLength e y₀ γ).restrict (Icc a b) =
      rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      (physicalStageTimeLength e y₀ n γ.val).restrict (Icc a b) =
        rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
    filter_upwards [eventually_dyadic_cells_inside (hU.preimage γ.val.continuous) hγ]
      with n hn
    exact physicalStageTimeLength_restrict e hU y₀ γ hab hγ n hn
  ext s hs
  rw [Measure.restrict_apply hs, physicalTimeLength_apply _ _ _ (hs.inter measurableSet_Icc)]
  apply le_antisymm
  · apply iSup_le
    intro n
    obtain ⟨m, hm, hnm⟩ := (hevent.and (eventually_ge_atTop n)).exists
    have hval := congrArg (fun μ : Measure PathTime => μ s) hm
    rw [Measure.restrict_apply hs] at hval
    exact ((monotone_physicalStageTimeLength e y₀ γ.property hnm) _).trans_eq hval
  · obtain ⟨n, hn⟩ := hevent.exists
    have hval := congrArg (fun μ : Measure PathTime => μ s) hn
    rw [Measure.restrict_apply hs] at hval
    rw [← hval]
    exact le_iSup (fun n => physicalStageTimeLength e y₀ n γ.val (s ∩ Icc a b)) n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicOpenCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable cover of an open time set by closed dyadic intervals inside it. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev DyadicInside (V : Set PathTime) :=
  {p : (Σ n : ℕ, Fin (2 ^ n)) // Icc (dyadicLeft p.1 p.2) (dyadicRight p.1 p.2) ⊆ V}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalLengthCharacterization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness and compact-interval exhaustion of physical-domain arclength.
This identifies the dyadic construction with ordinary arclength on all open
domain-time components, including paths that revisit points. -/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalTimeLength_compact_mass (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    physicalTimeLength e y₀ γ (Icc a b) =
      eVariationOn (physicalSubpath e hab ⟨γ.val, hγ⟩) univ := by
  have h := congrArg (fun μ : Measure PathTime => μ univ)
    (physicalTimeLength_restrict_compact e hU y₀ γ hab hγ)
  rw [Measure.restrict_apply_univ,
    rectifiableLengthCode_univ (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property)] at h
  exact h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathGates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many closed collar gates give Borel restrictions on path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def GateRule (C K : Set X) (γ : C(PathTime, X)) : Prop :=
  ∀ t : PathTime, γ t ∈ C → γ t ∈ K

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def GateRules (C K : ℕ → Set X) (γ : C(PathTime, X)) : Prop :=
  ∀ n, GateRule (C n) (K n) γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BasePathCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base-code space from the positive-law construction. The defining
relations are the actual path-hit and level incidences, with physical length,
finite deletions, optional tags, endpoint conditions and collar gates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable (X Y : Type*) [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

variable {X Y}

def EndpointCode (d : PathCodeData X Y) (dustMeasure : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  AllowedTaggedPath d dustMeasure N Γ ∧
  (Γ.1 ⊥ ∈ d.anchor ∧ FirstArrival d.target Γ.1) ∧
  GateRules d.gateContours d.gateSets Γ.1

abbrev BasePathCode (d : PathCodeData X Y) :=
  {Γ : TaggedPath X // EndpointCode d 0 (fun _ _ => ∅) Γ}

variable [SecondCountableTopology X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

def baseCodePhysicalPath (d : PathCodeData X Y) (Γ : BasePathCode d) :
    FinitePhysicalPath d.domainEquiv d.basePoint :=
  ⟨Γ.val.1, Γ.property.1.1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Visit multiplicities with the terminal parameter omitted. The extended
subtraction formula is justified by an exact all-time sum decomposition. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def terminalVisitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  if γ ⊤ = x then 1 else 0

def preterminalVisitCount (γ : C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  visitCount γ x - terminalVisitCount γ x


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AtomicVisitMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable atomic part of a path's coding measure, using actual
preterminal visit multiplicity and prescribed positive point weights. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X D : Type*} [MetricSpace X] [MeasurableSpace D]

def atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X)) : Measure D :=
  Measure.sum (fun s => (c s * preterminalVisitCount γ (p s)) • Measure.dirac s)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathCostMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-part coding measure: physical occupation, countable
preterminal visits, and weighted tuples. Finiteness is a Borel code condition. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

def baseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : Measure Y :=
  dyadicPhysicalOccupation d.domainEquiv d.basePoint (baseCodePhysicalPath d Γ)

def pathCostMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) : Measure (PathCostSpace Y D) :=
  (baseCodeOccupation d Γ).map costPhysical +
  (atomicVisitMeasure p c Γ.val.1).map costAtomic +
  (weightedTupleMeasure Γ.val.2).map costTuple

variable [SecondCountableTopology X] [Countable D]

abbrev FiniteCostCode (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) :=
  {Γ : BasePathCode d // pathCostMeasure d p c Γ univ < ∞}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RetaggedCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary tuple cost can be removed from an admissible metric's
lower bound. This is the retagging step in Section 4 of the manuscript. -/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)]

/-- Admissibility for the finite coding-measure family, with the prescribed
residual-image null constraint but without any tuple exclusions. -/
def CostAdmissible (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (h : PathCostSpace Y D → ℝ≥0∞) : Prop :=
  ∀ Γ : BasePathCode d, pathCostMeasure d p c Γ univ < ∞ →
    ν (residualImage d.dust Γ.val) = 0 → 1 ≤ ∫⁻ z, h z ∂pathCostMeasure d p c Γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean occupation, atomic and tuple measures of a law on base
codes. Their sum is exactly the barycenter of the coding measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def meanCodeOccupation (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) : Measure Y :=
  (P : Measure (BasePathCode d)).bind (baseCodeOccupation d)

def meanCodeTuple (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) :
    Measure LevelTuple :=
  (P : Measure (BasePathCode d)).bind (fun Γ => weightedTupleMeasure Γ.val.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeHitMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for complete path images. At free points, tuple absolute
continuity reduces a path hit to a residual hit; residual nullity then
annihilates the integrated whole-image hit probability. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def codeHitProbability (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  (P : Measure (BasePathCode d)) {Γ | x ∈ Set.range Γ.val.1}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodePathLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting the optional tags produces the actual path law. Its full
mean visit function differs from the preterminal function by exactly one
unit at the prescribed terminal point. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def codePath (d : PathCodeData X Y) (Γ : BasePathCode d) : C(PathTime, X) := Γ.val.1

theorem measurable_codePath (d : PathCodeData X Y) : Measurable (codePath d) :=
  measurable_fst.comp measurable_subtype_coe

def codePathLaw (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) :
    ProbabilityMeasure C(PathTime, X) := P.map (f := (codePath d)) (by first | (apply Measurable.aemeasurable; apply measurable_codePath <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.KLS_Sobolev_Witnesses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def MemW1pWitness.add
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    MemW1pWitness 2 (fun x => u x + v x) Ω where
  memLp := hu.memLp.add hv.memLp
  weakGrad := fun x => hu.weakGrad x + hv.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa using! (hu.weakGrad_component_memLp i).add (hv.weakGrad_component_memLp i)
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hu_eq := hu.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hv_eq := hv.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hu_int : Integrable (fun x => u x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hu_loc : LocallyIntegrable u (volume.restrict Ω) :=
        hu.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hv_int : Integrable (fun x => v x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hv_loc : LocallyIntegrable v (volume.restrict Ω) :=
        hv.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hv_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hgu_int : Integrable (fun x => hu.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgu_loc : LocallyIntegrable (fun x => hu.weakGrad x i) (volume.restrict Ω) :=
        (hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hgv_int : Integrable (fun x => hv.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgv_loc : LocallyIntegrable (fun x => hv.weakGrad x i) (volume.restrict Ω) :=
        (hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgv_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hfun :
        (fun x => (u x + v x) * (fderiv ℝ φ x) ei) =
          (fun x => u x * (fderiv ℝ φ x) ei + v x * (fderiv ℝ φ x) ei) := by
      ext x
      ring
    have hgrad :
        (fun x => (hu.weakGrad x i + hv.weakGrad x i) * φ x) =
          (fun x => hu.weakGrad x i * φ x + hv.weakGrad x i * φ x) := by
      ext x
      ring
    calc
      ∫ x in Ω, (u x + v x) * (fderiv ℝ φ x) ei
          = (-∫ x in Ω, hu.weakGrad x i * φ x) + (-∫ x in Ω, hv.weakGrad x i * φ x) := by
            rw [hfun, integral_add hu_int hv_int, hu_eq, hv_eq]
      _ = -((∫ x in Ω, hu.weakGrad x i * φ x) + (∫ x in Ω, hv.weakGrad x i * φ x)) := by
            ring
      _ = -∫ x in Ω, (hu.weakGrad x i * φ x + hv.weakGrad x i * φ x) := by
            rw [integral_add hgu_int hgv_int]
      _ = -∫ x in Ω, ((fun x => hu.weakGrad x + hv.weakGrad x) x i * φ x) := by
            congr 2
            ext x
            simpa [Pi.add_apply] using (congrFun hgrad x).symm

noncomputable def MemW1pWitness.smul
    {Ω : Set E} {u : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (c : ℝ) :
    MemW1pWitness 2 (fun x => c * u x) Ω where
  memLp := hu.memLp.const_mul c
  weakGrad := fun x => c • hu.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using (hu.weakGrad_component_memLp i).const_mul c
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hu_eq := hu.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hu_int : Integrable (fun x => u x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hu_loc : LocallyIntegrable u (volume.restrict Ω) :=
        hu.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hgu_int : Integrable (fun x => hu.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgu_loc : LocallyIntegrable (fun x => hu.weakGrad x i) (volume.restrict Ω) :=
        (hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    calc
      ∫ x in Ω, (c * u x) * (fderiv ℝ φ x) ei
          = ∫ x in Ω, c * (u x * (fderiv ℝ φ x) ei) := by
              congr with x
              ring
      _ = c * ∫ x in Ω, u x * (fderiv ℝ φ x) ei := by
            rw [integral_const_mul]
      _ = c * (-∫ x in Ω, hu.weakGrad x i * φ x) := by rw [hu_eq]
      _ = -(c * ∫ x in Ω, hu.weakGrad x i * φ x) := by ring
      _ = -∫ x in Ω, c * (hu.weakGrad x i * φ x) := by
            rw [integral_const_mul]
      _ = -∫ x in Ω, (c * hu.weakGrad x i) * φ x := by
            congr 2
            ext x
            ring
      _ = -∫ x in Ω, ((fun x => c • hu.weakGrad x) x i * φ x) := by
            simp [smul_eq_mul]

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact smooth cutoffs and regular superlevel neighborhoods

This is the first half of the common contour construction in §1 of
the Koebe manuscript's small-disks proof. The cutoff is constructed
using Mathlib's smooth Urysohn theorem and a relatively compact open
neighborhood; its existence is unconditional.

Only the regular-value choice is conditional on a published input:
Arthur Sard, *The measure of the critical values of differentiable
maps*, Bull. Amer. Math. Soc. 48 (1942), 883--890, Theorem 7.2,
pp. 889--890, DOI: 10.1090/S0002-9904-1942-07811-6. We use only its
specialization to compactly supported smooth maps from the plane to
the real line. The assumption says that their actual critical-value
image has Lebesgue outer measure zero.
Original article: https://doi.org/10.1090/S0002-9904-1942-07811-6
Readable scan: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/sard.pdf

No smooth Jordan disk or finite-component decomposition is assumed.
The constructed neighborhood has compact closure in the prescribed
open set and its boundary lies in a compact regular level set.
-/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_regular_value_in_interval (hsard : SmoothPlanarSard)
    {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t := by
  have hnull := hsard f hf hcompact
  have hpositive : 0 < volume (Ioo a b \ (f '' {z | fderiv ℝ f z = 0})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, htnot⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_⟩
  intro z hz hcrit
  exact htnot ⟨z, hcrit, hz⟩

/-- The regular superlevel neighborhood used before taking outer
contours. The cutoff, compact support and neighborhood control are
constructed; only critical-value nullity is supplied by Sard. -/
theorem exists_smooth_regular_superlevel_neighborhood
    (hsard : SmoothPlanarSard) {A O : Set ℂ}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ O ∧
      IsCompact {z | f z = t} ∧ IsPlanarRegularValue f t ∧
      frontier {z | t < f z} ⊆ {z | f z = t} := by
  obtain ⟨f, hf, hcompact, hsupp, hrange, hone⟩ := exists_smooth_planar_cutoff hA hO hAO
  obtain ⟨t, ht, hregular⟩ := exists_regular_value_in_interval hsard hf hcompact zero_lt_one
  have hclosure := closure_superlevel_subset_tsupport (f := f) ht.1
  refine ⟨f, t, hf, hcompact, hsupp, hrange, ht, isOpen_lt continuous_const hf.continuous,
    ?_, hcompact.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hsupp,
    isCompact_nonzero_level hf.continuous hcompact ht.1.ne', hregular, ?_⟩
  · intro z hz
    change t < f z
    rw [hone.self_of_nhdsSet z hz]
    exact ht.2
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf.continuous hz).symm

/-- Isolate a compact relatively clopen piece of an obstacle by a
regular superlevel neighborhood. `IsClosed (F \ A)` is precisely the
closedness needed to exclude the other obstacle points. The positive
level, hence also the boundary, misses the whole obstacle. -/
theorem exists_regular_superlevel_isolating_obstacle
    (hsard : SmoothPlanarSard) {A F V : Set ℂ}
    (hA : IsCompact A) (hAF : A ⊆ F) (hFA : IsClosed (F \ A))
    (hV : IsOpen V) (hAV : A ⊆ V) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ ∞ f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧ IsCompact {z | f z = t} ∧
      IsPlanarRegularValue f t ∧ Disjoint {z | f z = t} F ∧
      Disjoint (frontier {z | t < f z}) F := by
  let O : Set ℂ := V ∩ (F \ A)ᶜ
  have hO : IsOpen O := hV.inter hFA.isOpen_compl
  have hAO : A ⊆ O := fun z hz => ⟨hAV hz, fun hbad => hbad.2 hz⟩
  obtain ⟨f, t, hf, _, hsupp, _, ht, hopen, hAU, hcompact, hclO,
    hlevel, hregular, hfront⟩ := exists_smooth_regular_superlevel_neighborhood hsard hA hO hAO
  have hclF : closure {z | t < f z} ∩ F = A := by
    apply Set.Subset.antisymm
    · intro z hz
      have hnot : z ∉ F \ A := (hclO hz.1).2
      by_contra hzA
      exact hnot ⟨hz.2, hzA⟩
    · intro z hz
      exact ⟨subset_closure (hAU hz), hAF hz⟩
  have hdisj : Disjoint {z | f z = t} F := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    have hzSupp : z ∈ tsupport f := subset_tsupport f (by
      change f z ≠ 0
      rw [hz]
      exact ht.1.ne')
    have hzA : z ∈ A := by
      by_contra hnot
      exact (hsupp hzSupp).2 ⟨hzF, hnot⟩
    have := hAU hzA
    change t < f z at this
    rw [hz] at this
    exact lt_irrefl _ this
  exact ⟨f, t, hf, ht, hopen, hAU, hcompact, fun z hz => (hclO hz).1,
    hclF, hlevel, hregular, hdisj, hdisj.mono_left hfront⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth regular planar contours

The implicit function theorem supplies actual smooth local coordinates on a
regular scalar level. Compactness then makes the number of components finite.
For the subsequent circle-classification step, the needed classical result is
Milnor, *Topology from the Differentiable Viewpoint* (1965), Appendix
"Classifying 1-Manifolds", theorem on p. 55: a compact connected smooth
one-manifold without boundary is diffeomorphic to the circle. Primary scan:
https://www.ux1.eiu.edu/~cidelman/Classes/4855%20and%205220/Supplementary%20Texts/MilnorTopDiffVpt.pdf
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem levelChartInverse_coe {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t})
    {y : ℝ} (hy : (t, y) ∈ e.target) :
    (levelChartInverse e he z y : ℂ) = e.symm (t, y) := by
  simp only [levelChartInverse, dite_eq_left hy]

/-- Restrict ambient regular-level coordinates to an actual real chart of the
level subtype. -/
noncomputable def planarLevelChart {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t}) :
    OpenPartialHomeomorph {w // f w = t} ℝ where
  toFun w := (e w).2
  invFun := levelChartInverse e he z
  source := Subtype.val ⁻¹' e.source
  target := (fun y : ℝ => (t, y)) ⁻¹' e.target
  map_source' := by
    intro w hw
    change (t, (e w).2) ∈ e.target
    have hp : (t, (e w).2) = e w :=
      Prod.ext ((he w).trans w.property).symm rfl
    rw [hp]
    exact e.map_source hw
  map_target' := by
    intro y hy
    change (levelChartInverse e he z y : ℂ) ∈ e.source
    rw [levelChartInverse_coe e he z hy]
    exact e.map_target hy
  left_inv' := by
    intro w hw
    apply Subtype.ext
    have hw' : (t, (e w).2) ∈ e.target := by
      have hp : (t, (e w).2) = e w :=
        Prod.ext ((he w).trans w.property).symm rfl
      rw [hp]
      exact e.map_source hw
    rw [levelChartInverse_coe e he z hw']
    have hp : (t, (e w).2) = e w :=
      Prod.ext ((he w).trans w.property).symm rfl
    rw [hp, e.left_inv hw]
  right_inv' := by
    intro y hy
    rw [levelChartInverse_coe e he z hy, e.right_inv hy]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hw => hw)).snd
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (fun y : ℝ => (levelChartInverse e he z y : ℂ))
        {y | (t, y) ∈ e.target} := by
      apply (e.continuousOn_symm.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => hy)).congr
      intro y hy
      exact levelChartInverse_coe e he z hy
    exact continuousOn_iff_continuous_domRestrict.mp hc

noncomputable def regularLevelAmbient {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) (z : {w // f w = t}) :
    OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
  Classical.choose (exists_smooth_planar_level_chart hf (ht z z.property))

theorem regularLevelAmbient_spec {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) (z : {w // f w = t}) :
    z.val ∈ (regularLevelAmbient hf ht z).source ∧
      (∀ w, (regularLevelAmbient hf ht z w).1 = f w) ∧
      ContDiff ℝ ∞ (regularLevelAmbient hf ht z) ∧
      ContDiffOn ℝ ∞ (regularLevelAmbient hf ht z).symm
        (regularLevelAmbient hf ht z).target :=
  Classical.choose_spec (exists_smooth_planar_level_chart hf (ht z z.property))

/-- The actual real atlas induced by implicit-function charts on a regular level. -/
@[instance_reducible]
noncomputable def regularLevelChartedSpace {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    ChartedSpace ℝ {w // f w = t} where
  atlas := Set.range (fun z => planarLevelChart (regularLevelAmbient hf ht z)
    (regularLevelAmbient_spec hf ht z).2.1 z)
  chartAt z := planarLevelChart (regularLevelAmbient hf ht z)
    (regularLevelAmbient_spec hf ht z).2.1 z
  mem_chart_source z := (regularLevelAmbient_spec hf ht z).1
  chart_mem_atlas z := Set.mem_range_self z

theorem regularLevel_locallyConnectedSpace {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    LocallyConnectedSpace {w // f w = t} := by
  let := regularLevelChartedSpace hf ht
  exact ChartedSpace.locallyConnectedSpace ℝ {w // f w = t}

/-- Compact regular planar levels have only finitely many connected components. -/
theorem finite_connectedComponents_regularLevel {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hc : IsCompact {w | f w = t}) :
    Finite (ConnectedComponents {w // f w = t}) := by
  let : CompactSpace {w // f w = t} := isCompact_iff_compactSpace.mp hc
  let := regularLevel_locallyConnectedSpace hf ht
  infer_instance

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelFlow
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete smooth nonstationary trajectories on compact regular levels
of the actual defining planar scalar function. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_regular_level_flow {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : ℝ} (ha : IsPlanarRegularValue f a) (hc : IsCompact {z | f z = a}) :
    Nonempty (CompactRegularLevelFlow f a) := by
  obtain ⟨V,L,hV,hVc,hVL,ht,hne⟩ := exists_compact_level_tangent hf hc (fun z hz => ha z hz)
  have he (z : {z // f z = a}) : ∃ γ : ℝ → ℂ, γ 0 = z.val ∧ ∀ t, HasDerivAt γ (V (γ t)) t :=
    compact_vector_field_global_curve hV hVc z.val
  choose γ hγ0 hγ using he
  have hscalar (z : {z // f z = a}) (t : ℝ) : f (γ z t) = a := by
    calc
      f (γ z t) = f (γ z 0) := integral_curve_preserves_scalar hf ht (hγ z) t 0
      _ = a := by rw [hγ0]; exact z.property
  refine ⟨⟨V,L,hV,hVc,hVL,ht,γ,hγ0,hγ,hscalar,fun z => smooth_integral_curve hV (hγ z),?_⟩⟩
  intro z t
  rw [(hγ z t).deriv]
  exact hne _ (hscalar z t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelFlowOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time translation and exact orbit identities for the constructed
regular-level flow. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.trajectory_shift {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (s t : ℝ) :
    F.trajectory ⟨F.trajectory x s,F.scalar x s⟩ t = F.trajectory x (t+s) := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨F.equation ⟨F.trajectory x s,F.scalar x s⟩ u,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (by rw [F.initial,zero_add])
  exact congrFun h t

lemma CompactRegularLevelFlow.trajectory_shift_of_eq {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) {x y : {z // f z = a}} {s : ℝ}
    (hxy : F.trajectory x s = y.val) (t : ℝ) :
    F.trajectory y t = F.trajectory x (t+s) := by
  have hy : (⟨F.trajectory x s,F.scalar x s⟩ : {z // f z = a}) = y := Subtype.ext hxy
  simpa only [hy] using F.trajectory_shift x s t

lemma CompactRegularLevelFlow.range_eq_of_mem {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) {x y : {z // f z = a}}
    (hy : y.val ∈ range (F.trajectory x)) :
    range (F.trajectory y) = range (F.trajectory x) := by
  obtain ⟨s,hs⟩ := hy
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t+s,(F.trajectory_shift_of_eq hs t).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t-s,?_⟩
    rw [F.trajectory_shift_of_eq hs,sub_add_cancel]

lemma CompactRegularLevelFlow.periodic_of_return {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) {p : ℝ}
    (hp : F.trajectory x p = x.val) : Periodic (F.trajectory x) p := by
  intro t
  exact (F.trajectory_shift_of_eq hp t).symm

lemma CompactRegularLevelFlow.orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x y : {z // f z = a}) :
    range (F.trajectory x) = range (F.trajectory y) ∨
      Disjoint (range (F.trajectory x)) (range (F.trajectory y)) := by
  by_cases h : Disjoint (range (F.trajectory x)) (range (F.trajectory y))
  · exact Or.inr h
  · obtain ⟨z,hzx,hzy⟩ := Set.not_disjoint_iff.mp h
    let w : {z // f z = a} := ⟨z,by obtain ⟨t,rfl⟩ := hzx; exact F.scalar x t⟩
    have h1 : range (F.trajectory w) = range (F.trajectory x) := F.range_eq_of_mem hzx
    have h2 : range (F.trajectory w) = range (F.trajectory y) := F.range_eq_of_mem hzy
    exact Or.inl (h1.symm.trans h2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LevelFlowCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonstationary trajectory has nonzero speed in the actual local
one-dimensional coordinate of its regular level. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma level_flow_coordinate_deriv_ne_zero {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    deriv (fun s => (e (F.trajectory x s)).2) t ≠ 0 := by
  let γ := F.trajectory x
  have hg : ContDiff ℝ ∞ (fun s => (e (γ s)).2) := (hs.comp (F.trajectory_smooth x)).snd
  have hfirst : (fun s => (e (γ s)).1) = (fun _ => a) := by
    funext s
    exact (he (γ s)).trans (F.scalar x s)
  have h1 : HasDerivAt (fun s => (e (γ s)).1) 0 t := by
    rw [hfirst]
    exact hasDerivAt_const t a
  intro hzero
  have h2 : HasDerivAt (fun s => (e (γ s)).2) 0 t := by
    rw [← hzero]
    exact (hg.differentiable (by simp) t).hasDerivAt
  have heγ : HasDerivAt (fun s => e (γ s)) (0 : ℝ × ℝ) t := h1.prodMk h2
  have hei := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source ht))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := hei.hasFDerivAt.comp_hasDerivAt t heγ
  have hfun : (e.symm ∘ fun s => e (γ s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [((F.trajectory_smooth x).continuous.continuousAt).preimage_mem_nhds
      (e.open_source.mem_nhds ht)] with s hs
    exact e.left_inv hs
  have hz : HasDerivAt γ 0 t := by
    simpa only [map_zero] using hd.congr_of_eventuallyEq hfun.symm
  exact F.regular x t hz.deriv

lemma level_flow_coordinate_open_image {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (ht : F.trajectory x t ∈ e.source) (he : ∀ z, (e z).1 = f z)
    (hs : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    (fun s => (e (F.trajectory x s)).2) '' U ∈ 𝓝 ((e (F.trajectory x t)).2) := by
  have hg : ContDiff ℝ ∞ (fun s => (e (F.trajectory x s)).2) :=
    (hs.comp (F.trajectory_smooth x)).snd
  have hd := (hg.contDiffAt (x := t)).hasStrictDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← hd.map_nhds_eq (level_flow_coordinate_deriv_ne_zero F x t e ht he hs hi)]
  exact Filter.mem_map_iff_exists_image.mpr ⟨U,hU,subset_refl _⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularLevelOpenOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each orbit is open in its actual regular level, as witnessed by the
nonzero derivative of its local level coordinate. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.continuous_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) : Continuous (F.levelTrajectory x) :=
  (F.trajectory_smooth x).continuous.subtype_mk _

lemma CompactRegularLevelFlow.isOpenMap_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) : IsOpenMap (F.levelTrajectory x) := by
  intro B hB
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨t,htB,rfl⟩
  obtain ⟨e,ht,he,hs,hi⟩ := exists_smooth_planar_level_chart hf (ha _ (F.scalar x t))
  let U : Set ℝ := (F.trajectory x) ⁻¹' e.source ∩ B
  have hU : U ∈ 𝓝 t := inter_mem
    ((F.trajectory_smooth x).continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht))
    (hB.mem_nhds htB)
  let J := (fun s => (e (F.trajectory x s)).2) '' U
  have hJ : J ∈ 𝓝 ((e (F.trajectory x t)).2) :=
    level_flow_coordinate_open_image F x t e ht he hs hi hU
  have hcont : Continuous (fun y : {z // f z = a} => (e y.val).2) :=
    (hs.continuous.comp continuous_subtype_val).snd
  have hsource : {y : {z // f z = a} | y.val ∈ e.source} ∈ 𝓝 (F.levelTrajectory x t) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht)
  filter_upwards [hsource,hcont.continuousAt.preimage_mem_nhds hJ] with y hyS hyJ
  obtain ⟨s,hsU,hsJ⟩ := hyJ
  have hsS : F.trajectory x s ∈ e.source := hsU.1
  have hp : e (F.trajectory x s) = e y.val := by
    apply Prod.ext
    · rw [he,he,F.scalar,y.property]
    · exact hsJ
  have hy : F.levelTrajectory x s = y := Subtype.ext (e.injOn hsS hyS hp)
  exact ⟨s,hsU.2,hy⟩

lemma CompactRegularLevelFlow.isOpen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) : IsOpen (range (F.levelTrajectory x)) := by
  simpa only [image_univ] using F.isOpenMap_levelTrajectory hf ha x univ isOpen_univ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularLevelCompactOrbit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orbits form clopen components of a compact regular level. Their
compactness forces a return for the complete nonstationary flow. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.mem_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x y : {z // f z = a}) :
    y ∈ range (F.levelTrajectory x) ↔ y.val ∈ range (F.trajectory x) := by
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

lemma CompactRegularLevelFlow.level_orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x y : {z // f z = a}) :
    range (F.levelTrajectory x) = range (F.levelTrajectory y) ∨
      Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
  rcases F.orbits_eq_or_disjoint x y with he | hd
  · left
    ext z
    rw [F.mem_range_levelTrajectory,F.mem_range_levelTrajectory,he]
  · right
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact Set.disjoint_left.mp hd ((F.mem_range_levelTrajectory x z).mp hzx)
      ((F.mem_range_levelTrajectory y z).mp hzy)

lemma CompactRegularLevelFlow.isClopen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) : IsClopen (range (F.levelTrajectory x)) := by
  refine ⟨isOpen_compl_iff.mp ?_,F.isOpen_range_levelTrajectory hf ha x⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyself : y ∈ range (F.levelTrajectory y) := ⟨0,Subtype.ext (F.initial y)⟩
  have hdis : Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
    rcases F.level_orbits_eq_or_disjoint x y with he | hd
    · exact (hy (he ▸ hyself)).elim
    · exact hd
  exact Filter.mem_of_superset ((F.isOpen_range_levelTrajectory hf ha y).mem_nhds hyself)
    (fun z hz hx => Set.disjoint_left.mp hdis hx hz)

lemma CompactRegularLevelFlow.compact_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    IsCompact (range (F.levelTrajectory x)) := by
  let : CompactSpace {z // f z = a} := isCompact_iff_compactSpace.mp hc
  exact (F.isClopen_range_levelTrajectory hf ha x).isClosed.isCompact

lemma CompactRegularLevelFlow.not_injective_trajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ¬ Injective (F.trajectory x) := by
  intro hi
  have hi' : Injective (F.levelTrajectory x) := fun s t h => hi (congrArg Subtype.val h)
  have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (F.continuous_levelTrajectory x) hi' (F.isOpenMap_levelTrajectory hf ha x)
  have hk : IsCompact (univ : Set ℝ) := he.isEmbedding.isCompact_iff.mpr (by
    simpa only [image_univ] using F.compact_range_levelTrajectory hf ha hc x)
  exact noncompact_univ ℝ hk

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelReturn
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness forces a positive return time for each nonstationary
regular-level orbit. Uniqueness turns every return into a true period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.return_of_collision {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) {s t : ℝ}
    (hst : F.trajectory x s = F.trajectory x t) :
    F.trajectory x (t-s) = x.val := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+t)).comp_add_const u t,mem_univ _⟩)
    (by simpa only [zero_add] using hst)
  have he := congrFun h (-s)
  simpa only [neg_add_cancel,neg_add_eq_sub,F.initial] using he.symm

lemma CompactRegularLevelFlow.exists_positive_period {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ p > 0, Periodic (F.trajectory x) p := by
  obtain ⟨s,t,hst,hne⟩ := not_injective_iff.mp (F.not_injective_trajectory hf ha hc x)
  have hp := F.periodic_of_return x (F.return_of_collision x hst)
  have hne' : t-s ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases lt_or_gt_of_ne hne' with hneg | hpos
  · exact ⟨-(t-s),neg_pos.mpr hneg,hp.neg⟩
  · exact ⟨t-s,hpos,hp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelLeastPeriod
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed return subgroup of a nonstationary compact regular-level
trajectory has a least positive element. This is its fundamental period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def CompactRegularLevelFlow.returnSubgroup {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) : AddSubgroup ℝ where
  carrier := {t | F.trajectory x t = x.val}
  zero_mem' := F.initial x
  add_mem' := by
    intro s t hs ht
    exact ((F.periodic_of_return x ht) s).trans hs
  neg_mem' := by
    intro t ht
    change F.trajectory x (-t) = x.val
    simpa only [zero_add] using ((F.periodic_of_return x ht).neg 0).trans (F.initial x)

lemma CompactRegularLevelFlow.returnSubgroup_closed {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) :
    IsClosed (F.returnSubgroup x : Set ℝ) :=
  isClosed_eq (F.trajectory_smooth x).continuous continuous_const

lemma CompactRegularLevelFlow.returnSubgroup_not_dense {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) :
    ¬ Dense (F.returnSubgroup x : Set ℝ) := by
  intro hd
  have he : (F.returnSubgroup x : Set ℝ) = univ :=
    (F.returnSubgroup_closed x).closure_eq.symm.trans hd.closure_eq
  have hc : F.trajectory x = fun _ => x.val := by
    funext t
    have ht : t ∈ (F.returnSubgroup x : Set ℝ) := he.symm ▸ mem_univ t
    exact ht
  exact F.regular x 0 (by rw [hc]; simp)

lemma CompactRegularLevelFlow.exists_least_positive_period {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ p : ℝ, IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p := by
  have hb : F.returnSubgroup x ≠ ⊥ := by
    obtain ⟨p,hp,hper⟩ := F.exists_positive_period hf ha hc x
    intro he
    have hm : p ∈ F.returnSubgroup x := by
      change F.trajectory x p = x.val
      simpa only [zero_add] using (hper 0).trans (F.initial x)
    have hz : p = 0 := by simpa only [he, AddSubgroup.mem_bot] using hm
    exact hp.ne' hz
  by_contra hn
  exact F.returnSubgroup_not_dense x
    ((F.returnSubgroup x).dense_of_no_min hb hn)

lemma CompactRegularLevelFlow.injOn_fundamental_interval {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) {p : ℝ}
    (hp : IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p) :
    InjOn (F.trajectory x) (Ico 0 p) := by
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hret := F.return_of_collision x hst
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [hs.1, ht.2]
  · have hret := F.return_of_collision x hst.symm
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [ht.1, hs.2]

lemma CompactRegularLevelFlow.range_levelTrajectory_eq_component {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) :
    range (F.levelTrajectory x) = connectedComponent x := by
  have hx : x ∈ range (F.levelTrajectory x) := ⟨0,Subtype.ext (F.initial x)⟩
  exact Subset.antisymm
    ((isPreconnected_range (F.continuous_levelTrajectory x)).subset_connectedComponent hx)
    ((F.isClopen_range_levelTrajectory hf ha x).connectedComponent_subset hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelPeriodicParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth embedded circles parametrizing the components of a
compact regular planar level. The parametrization comes from its tangent flow. -/
open Set Function
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.exists_regular_period_one {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ σ : ℝ → ℂ, ContDiff ℝ ∞ σ ∧ Periodic σ 1 ∧ InjOn σ (Ico 0 1) ∧
      (∀ t, deriv σ t ≠ 0) ∧ range σ = Subtype.val '' connectedComponent x := by
  obtain ⟨p,hp⟩ := F.exists_least_positive_period hf ha hc x
  have hp0 : 0 < p := hp.1.2
  have hper := F.periodic_of_return x hp.1.1
  let σ : ℝ → ℂ := fun t => F.trajectory x (p*t)
  have hσ : ContDiff ℝ ∞ σ := (F.trajectory_smooth x).comp (contDiff_const.mul contDiff_id)
  refine ⟨σ,hσ,?_,?_,?_,?_⟩
  · intro t
    dsimp [σ]
    convert hper (p*t) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · intro s hs t ht hst
    have he := F.injOn_fundamental_interval x hp
      (show p*s ∈ Ico 0 p from ⟨mul_nonneg hp0.le hs.1, mul_lt_of_lt_one_right hp0 hs.2⟩)
      (show p*t ∈ Ico 0 p from ⟨mul_nonneg hp0.le ht.1, mul_lt_of_lt_one_right hp0 ht.2⟩) hst
    exact (mul_left_cancel₀ hp0.ne' he)
  · intro t
    have hm : HasDerivAt (fun u : ℝ => p*u) p t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul p
    have hd : HasDerivAt σ (p • F.field (F.trajectory x (p*t))) t :=
      (F.equation x (p*t)).scomp t hm
    rw [hd.deriv]
    apply smul_ne_zero hp0.ne'
    simpa only [(F.equation x (p*t)).deriv] using F.regular x (p*t)
  · have hr : range σ = range (F.trajectory x) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨p*t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t/p,?_⟩
        dsimp [σ]
        rw [mul_div_cancel₀ _ hp0.ne']
    rw [hr, ← F.range_levelTrajectory_eq_component hf ha x]
    exact (range_comp Subtype.val (F.levelTrajectory x))

lemma exists_smooth_circle_of_compact_regular_level {f : ℂ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ g : Circle → ℂ, ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ g ∧ Topology.IsEmbedding g ∧
      range g = Subtype.val '' connectedComponent x := by
  obtain ⟨F⟩ := exists_compact_regular_level_flow hf ha hc
  obtain ⟨σ,hs,hp,hi,_,hr⟩ := F.exists_regular_period_one hf ha hc x
  refine ⟨periodicCircleDescent hp,periodicCircleDescent_smooth hp hs,?_,?_⟩
  · exact ((periodicCircleDescent_smooth hp hs).continuous.isClosedEmbedding
      (periodicCircleDescent_injective hp hi)).isEmbedding
  · exact (periodicCircleDescent_range hp).trans hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactRegularLevelContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth contour decomposition of the actual compact regular level,
proved by complete tangent flows instead of one-manifold classification. -/
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma compact_regular_level_circle_contours {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hc : IsCompact {z | f z = t}) :
    Finite (ConnectedComponents {z // f z = t}) ∧
      ∃ γ : ConnectedComponents {z // f z = t} → Circle → ℂ,
        (∀ c, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ c) ∧ Topology.IsEmbedding (γ c)) ∧
        Pairwise (fun c d => Disjoint (range (γ c)) (range (γ d))) ∧
        (⋃ c, range (γ c)) = {z | f z = t} := by
  classical
  let M := {z : ℂ // f z = t}
  let x (c : ConnectedComponents M) : M :=
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hx (c : ConnectedComponents M) : ConnectedComponents.mk (x c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  have hex (c : ConnectedComponents M) := exists_smooth_circle_of_compact_regular_level hf ht hc (x c)
  choose γ hγ using hex
  have hm (c : ConnectedComponents M) {z : ℂ} (hz : z ∈ range (γ c)) :
      ∃ w : M, w.val = z ∧ ConnectedComponents.mk w = c := by
    rw [hγ c |>.2.2] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨w,rfl,(ConnectedComponents.coe_eq_coe'.mpr hw).trans (hx c)⟩
  refine ⟨finite_connectedComponents_regularLevel hf ht hc,γ,fun c => ⟨(hγ c).1, (hγ c).2.1⟩,?_,?_⟩
  · intro c d hcd
    apply Set.disjoint_left.mpr
    intro z hzc hzd
    obtain ⟨u,hu,huc⟩ := hm c hzc
    obtain ⟨v,hv,hvd⟩ := hm d hzd
    have huv : u = v := Subtype.ext (hu.trans hv.symm)
    exact hcd (huc.symm.trans (huv ▸ hvd))
  · ext z
    constructor
    · intro hz
      obtain ⟨c,hzc⟩ := mem_iUnion.mp hz
      obtain ⟨w,rfl,_⟩ := hm c hzc
      exact w.property
    · intro hz
      let w : M := ⟨z,hz⟩
      let c := ConnectedComponents.mk w
      apply mem_iUnion.mpr
      refine ⟨c,?_⟩
      rw [(hγ c).2.2]
      refine ⟨w,?_,rfl⟩
      apply ConnectedComponents.coe_eq_coe'.mp
      exact (hx c).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OuterContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting outer Jordan contours

The disks are images of the unit disk by planar homeomorphisms. Connected
exteriors and the nesting alternative allow selection of the maximal
members of a finite family.
-/

open Set Filter Function
open scoped Topology

namespace CircleDomainRigidity

theorem interior_closure_jordanInterior (H : ℂ ≃ₜ ℂ) :
    interior (closure (jordanInterior H)) = jordanInterior H := by
  rw [closure_jordanInterior, ← H.image_interior, interior_closedBall _ one_ne_zero]
  rfl

theorem frontier_jordanInterior (H : ℂ ≃ₜ ℂ) :
    frontier (jordanInterior H) = H '' Metric.sphere (0 : ℂ) 1 := by
  rw [jordanInterior, ← H.image_frontier, frontier_ball _ one_ne_zero]

theorem isConnected_jordanInterior (H : ℂ ≃ₜ ℂ) : IsConnected (jordanInterior H) :=
  (Metric.isConnected_ball zero_lt_one).image H H.continuous.continuousOn

theorem isConnected_frontier_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected (frontier (jordanInterior H)) := by
  rw [frontier_jordanInterior]
  exact planar_unit_sphere_connected.image H H.continuous.continuousOn

theorem isConnected_exterior_jordanInterior (H : ℂ ≃ₜ ℂ) :
    IsConnected (closure (jordanInterior H))ᶜ := by
  rw [closure_jordanInterior, ← H.image_compl]
  exact planar_unit_exterior_connected.image H H.continuous.continuousOn

/-- A Jordan contour contained in the interior of another Jordan disk has its
entire closed fill in that interior. -/
theorem closed_jordanInterior_subset_of_frontier_subset (H K : ℂ ≃ₜ ℂ)
    (hfront : frontier (jordanInterior H) ⊆ jordanInterior K) :
    closure (jordanInterior H) ⊆ jordanInterior K :=
  closed_fill_subset_of_frontier_subset (jordanInterior_isOpen H) (jordanInterior_isOpen K)
    (interior_closure_jordanInterior K) (isCompact_closure_jordanInterior H)
    (isCompact_closure_jordanInterior K)
    (isConnected_exterior_jordanInterior K).isPreconnected hfront

/-- Disjoint Jordan contours have disjoint closed fills or one closed fill
lies strictly inside the other disk. -/
theorem disjoint_or_nested_jordanInteriors (H K : ℂ ≃ₜ ℂ)
    (hdisj : Disjoint (frontier (jordanInterior H)) (frontier (jordanInterior K))) :
    Disjoint (closure (jordanInterior H)) (closure (jordanInterior K)) ∨
      closure (jordanInterior H) ⊆ jordanInterior K ∨
      closure (jordanInterior K) ⊆ jordanInterior H :=
  disjoint_or_nested_closed_fills (jordanInterior_isOpen H) (jordanInterior_isOpen K)
    (interior_closure_jordanInterior K) (isCompact_closure_jordanInterior H)
    (isCompact_closure_jordanInterior K) (isConnected_frontier_jordanInterior H).isPreconnected
    (isConnected_jordanInterior K).isPreconnected
    (isConnected_exterior_jordanInterior K).isPreconnected hdisj

/-- Select the outer members of a finite family of disjoint Jordan contours.
Their closed disks are pairwise disjoint and cover all the original filled
disks. Since this is a subfamily, any prescribed contour properties persist. -/
theorem exists_outer_jordanInteriors {ι : Type*} [Finite ι]
    (H : ι → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j))))) :
    ∃ s : Set ι, s.Finite ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i, ∃ j ∈ s, closure (jordanInterior (H i)) ⊆ closure (jordanInterior (H j))) ∧
      (⋃ i ∈ s, closure (jordanInterior (H i))) = ⋃ i, closure (jordanInterior (H i)) := by
  classical
  let C : ι → Set ℂ := fun i => closure (jordanInterior (H i))
  let s : Set ι := {i | ∀ j, C i ⊆ C j → C j ⊆ C i}
  have hdom (i : ι) : ∃ j ∈ s, C i ⊆ C j := by
    obtain ⟨D, hiD, hD⟩ := (Set.finite_range C).exists_le_maximal (Set.mem_range_self i)
    obtain ⟨j, rfl⟩ := hD.1
    exact ⟨j, fun k hk => hD.2 (Set.mem_range_self k) hk, hiD⟩
  refine ⟨s, s.toFinite, ?_, hdom, ?_⟩
  · intro i hi j hj hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hdisj hij) with h | h | h
    · exact h
    · have hji : C j ⊆ C i := hi j (h.trans subset_closure)
      have hbad : C j ⊆ jordanInterior (H j) := hji.trans h
      obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hz' := hbad (frontier_subset_closure hz)
      have hn : z ∉ jordanInterior (H j) := by
        simpa [frontier, (jordanInterior_isOpen (H j)).interior_eq] using hz.2
      exact (hn hz').elim
    · have hij' : C i ⊆ C j := hj i (h.trans subset_closure)
      have hbad : C i ⊆ jordanInterior (H i) := hij'.trans h
      obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hz' := hbad (frontier_subset_closure hz)
      have hn : z ∉ jordanInterior (H i) := by
        simpa [frontier, (jordanInterior_isOpen (H i)).interior_eq] using hz.2
      exact (hn hz').elim
  · apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion_of_subset i subset_rfl
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨j, hj, hij⟩ := hdom i
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hij hi⟩⟩

theorem frontier_jordanInterior_eq_circle_range (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ)
    (hH : ∀ z : Circle, H (z : ℂ) = γ z) :
    frontier (jordanInterior H) = range γ := by
  rw [frontier_jordanInterior]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, (hH ⟨z, hz⟩).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.property, hH z⟩

end CircleDomainRigidity

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

/-- A physical Jordan disk in the real coordinates used for the energy
and patching calculation. -/
def realJordanInterior (H : ℂ ≃ₜ ℂ) : Set (ℝ × ℝ) :=
  Complex.equivRealProdCLM '' jordanInterior H

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanExteriors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The common exterior of finitely many disjoint Jordan disks

Removing finitely many disjoint closed Jordan disks leaves a preconnected
set. We first prove the closed-complement version by extending any separation
across disks according to which side contains their connected boundaries.
Small enlargements of the disks then give the open-complement version.
These are proved topology lemmas, not additional published inputs.
-/

open Set Filter Function Metric
open scoped Topology

namespace CircleDomainRigidity

/-- Enlarge finitely many disjoint closed Jordan disks within prescribed
open neighborhoods, keeping their closures disjoint. -/
theorem exists_disjoint_jordan_enlargements
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (O : I → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hsub : ∀ i, closure (jordanInterior (H i)) ⊆ O i) :
    ∃ r : I → ℝ, (∀ i, 1 < r i) ∧
      (∀ i, H i '' closedBall (0 : ℂ) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => H i '' closedBall (0 : ℂ) (r i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (closure (jordanInterior (H i)))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_closure isClosed_closure (hdisj hij)
  obtain ⟨V, hV, hVdisj⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (closure (jordanInterior (H i))))
  have hex (i : I) : ∃ r : ℝ, 1 < r ∧
      H i '' closedBall (0 : ℂ) r ⊆ V i ∩ O i := by
    have hopen : IsOpen ((H i) ⁻¹' (V i ∩ O i)) :=
      ((hV i).1.inter (hO i)).preimage (H i).continuous
    have hcontain : closedBall (0 : ℂ) 1 ⊆ (H i) ⁻¹' (V i ∩ O i) := by
      intro x hx
      have hx' : H i x ∈ closure (jordanInterior (H i)) := by
        rw [closure_jordanInterior]
        exact mem_image_of_mem _ hx
      exact ⟨(hV i).2 hx', hsub i hx'⟩
    obtain ⟨δ, hδ, hδsub⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hopen hcontain
    refine ⟨δ + 1, by linarith, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply hδsub
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hx
  choose r hr hrsub using hex
  refine ⟨r, hr, fun i x hx => (hrsub i hx).2, ?_⟩
  intro i j hij
  exact (hVdisj hij).mono (fun x hx => (hrsub i hx).1)
    (fun x hx => (hrsub j hx).1)

/-- Any two points outside the closed disks remain in the connected
complement of a sufficiently small simultaneous enlargement. -/
theorem isPreconnected_exterior_finite_jordanInteriors
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsPreconnected (⋃ i, closure (jordanInterior (H i)))ᶜ := by
  classical
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  let O : Set ℂ := ({x, y} : Set ℂ)ᶜ
  have hO : IsOpen O := ((Set.finite_singleton y).insert x).isClosed.isOpen_compl
  have hsub (i : I) : closure (jordanInterior (H i)) ⊆ O := by
    intro z hz hzxy
    rcases hzxy with rfl | hzxy
    · exact hx (mem_iUnion.mpr ⟨i, hz⟩)
    · have hzy : z = y := mem_singleton_iff.mp hzxy
      subst z
      exact hy (mem_iUnion.mpr ⟨i, hz⟩)
  obtain ⟨r, hr, hrsub, hrdisj⟩ :=
    exists_disjoint_jordan_enlargements H hdisj (fun _ => O) (fun _ => hO) hsub
  let U : I → Set ℂ := fun i => H i '' ball (0 : ℂ) (r i)
  have hUopen (i : I) : IsOpen (U i) := (H i).isOpenMap _ isOpen_ball
  have hUcl (i : I) : closure (U i) = H i '' closedBall (0 : ℂ) (r i) := by
    change closure (H i '' ball (0 : ℂ) (r i)) = _
    rw [← (H i).image_closure, closure_ball _ (by linarith [hr i])]
  have hUfront (i : I) : IsPreconnected (frontier (U i)) := by
    change IsPreconnected (frontier (H i '' ball (0 : ℂ) (r i)))
    rw [← (H i).image_frontier, frontier_ball _ (by linarith [hr i])]
    exact ((isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num)
      (0 : ℂ) (by linarith [hr i])).image (H i) (H i).continuous.continuousOn).isPreconnected
  have hUd : Pairwise (Disjoint on fun i => closure (U i)) := by
    intro i j hij
    simpa only [hUcl] using hrdisj hij
  refine ⟨(⋃ i, U i)ᶜ, ?_, ?_, ?_,
    isPreconnected_compl_finite_open_disks U hUopen hUfront hUd⟩
  · intro z hz hzcl
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzcl
    rw [closure_jordanInterior] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    apply hz
    exact mem_iUnion.mpr ⟨i, w, (closedBall_subset_ball (hr i)) hw, rfl⟩
  · intro hxU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    have hxO := hrsub i (hUcl i ▸ subset_closure hi)
    exact hxO (by simp)
  · intro hyU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyU
    have hyO := hrsub i (hUcl i ▸ subset_closure hi)
    exact hyO (by simp)

/-- A bounded open set cannot occupy the common exterior when its boundary
is covered by finitely many disjoint closed Jordan disks. -/
theorem open_subset_finite_jordan_fills_of_frontier_subset
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {U : Set ℂ} (hU : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hfront : frontier U ⊆ ⋃ i, closure (jordanInterior (H i))) :
    U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
  let K : Set ℂ := ⋃ i, closure (jordanInterior (H i))
  have hKbdd : Bornology.IsBounded K :=
    (isCompact_iUnion (fun i => isCompact_closure_jordanInterior (H i))).isBounded
  have hS := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hsplit : Kᶜ ⊆ U ∨ Kᶜ ⊆ (closure U)ᶜ := by
    apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
    · intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · right
        intro hzcl
        have hzfront : z ∈ frontier U := by
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
        exact hz (hfront hzfront)
  rcases hsplit with hin | hout
  · have hbad := hKbdd.union (hUbdd.subset hin)
    rw [union_compl_self] at hbad
    exact (NormedSpace.unbounded_univ ℝ ℂ hbad).elim
  · intro z hzU
    by_contra hzK
    exact hout hzK (subset_closure hzU)

/-- If the selected contours are themselves boundary curves of the open
set, coverage by closed fills is coverage by their interiors. -/
theorem open_subset_finite_jordanInteriors_of_frontier_subset
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {U : Set ℂ} (hU : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)))
    (hselected : ∀ i, frontier (jordanInterior (H i)) ⊆ frontier U) :
    U ⊆ ⋃ i, jordanInterior (H i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (open_subset_finite_jordan_fills_of_frontier_subset H hdisj hU hUbdd hcover hx)
  refine mem_iUnion.mpr ⟨i, ?_⟩
  by_contra hxi
  have hxfront : x ∈ frontier (jordanInterior (H i)) := by
    rw [(jordanInterior_isOpen (H i)).frontier_eq]
    exact ⟨hi, hxi⟩
  have hxf := hselected i hxfront
  rw [hU.frontier_eq] at hxf
  exact hxf.2 hx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Every point of a regular level borders its strict superlevel set.
Otherwise the point is a local maximum, contradicting regularity. -/
theorem frontier_superlevel_eq_regular_level {f : ℂ → ℝ} {t : ℝ}
    (hf : Continuous f) (ht : IsPlanarRegularValue f t) :
    frontier {z | t < f z} = {z | f z = t} := by
  have hU : IsOpen {z | t < f z} := isOpen_lt continuous_const hf
  apply Set.Subset.antisymm
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf hz).symm
  · intro z hz
    change f z = t at hz
    rw [hU.frontier_eq]
    refine ⟨?_, by simp [hz]⟩
    by_contra hnot
    have hlocal : IsLocalMax f z := by
      have hnbd : (closure {w | t < f w})ᶜ ∈ 𝓝 z :=
        isClosed_closure.isOpen_compl.mem_nhds hnot
      filter_upwards [hnbd] with w hw
      have hw' : ¬ t < f w := fun h => hw (subset_closure h)
      simpa only [hz] using le_of_not_gt hw'
    exact ht z hz hlocal.fderiv_eq_zero

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem closure_sphere_image_jordanInterior (H : ℂ ≃ₜ ℂ) :
    closure (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
  apply Set.Subset.antisymm
  · apply closure_minimal (image_mono subset_closure)
    exact OnePoint.isClosed_image_coe.mpr
      ⟨isClosed_closure, isCompact_closure_jordanInterior H⟩
  · exact image_closure_subset_closure_image OnePoint.continuous_coe

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalTerminals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical terminal disks and their staircase oscillations

A finite set of quotient dust points is surrounded by disjoint smooth
physical Jordan disks, with whole fibers inside the disks and boundaries
in the physical domain. The disks can be confined to prescribed
neighborhoods. Liminf and limsup bounds on those neighborhoods give the
staircase oscillation bound `a + 4h`, uniformly in width and shift.
-/

open Set Filter Function Metric
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Actual terminal disks, including their smooth boundary parametrizations.
The specified neighborhoods are in the quotient sphere. -/
structure PhysicalTerminalDisks {I : Type*} (G : Set Sphere) (π : Sphere → Sphere)
    (B : Set Sphere) (p : I → Sphere) (O : I → Set Sphere) where
  H : I → ℂ ≃ₜ ℂ
  curve : I → Circle → ℂ
  fiber_subset : ∀ i, {z : ℂ | π (z : Sphere) = p i} ⊆ jordanInterior (H i)
  closure_subset : ∀ i, closure (jordanInterior (H i)) ⊆
    (fun z : ℂ => π (z : Sphere)) ⁻¹' O i
  disjoint_closures : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))
  curve_smooth : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i)
  curve_embedding : ∀ i, Topology.IsEmbedding (curve i)
  frontier_eq : ∀ i, frontier (jordanInterior (H i)) = range (curve i)
  frontier_good : ∀ i z, z ∈ frontier (jordanInterior (H i)) →
    (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B

attribute [local instance] sphereMetric

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The retained core and completed domain of a finite disk construction

The core is the spherical complement of all terminal and filling disks.
If the disks cover the preimage of the quotient dust, the core is a compact
subset of the original domain. Filling the second family leaves precisely
the complement of the terminal interiors. This completed compact set has
the open neighborhood consisting of the original domain and the filling
interiors. In a finite chart its bounded closed pieces are compact, even
though the entire planar exterior is unbounded.

The final statements apply the actual finite patching construction to this
open neighborhood and recover local agreement on the retained core.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (sphericalDiskUnion T)ᶜ

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutoffCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The physical core containing the entire cutoff transition

Taking the complement of the open one-plateau of the cutoff gives a
compact spherical subset of the original domain. Choosing all disk
closures off this larger core guarantees genuine staircase collars.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isOpen_realChartDomain {G : Set Sphere} (hG : IsOpen G) : IsOpen (realChartDomain G) :=
  hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

theorem sphericalCore_mono {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) :
    sphericalCore A ⊆ sphericalCore B := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact infty_mem_sphericalCore B
  | coe z => exact (coe_mem_sphericalCore B z).mpr (hAB ((coe_mem_sphericalCore A z).mp hx))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance instBorelSpaceSphere_1_r006e07_1 : BorelSpace Sphere := ⟨rfl⟩
def sphericalArea : Measure Sphere :=
  Measure.map ((↑) : ℂ → Sphere)
    (volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzIntervalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

def realIntervalPath (a b : ℝ) : C(PathTime, ℝ) where
  toFun s := AffineMap.lineMap a b (s : ℝ)
  continuous_toFun := (lipschitzWith_lineMap a b).continuous.comp continuous_subtype_val

@[simp] theorem realIntervalPath_zero (a b : ℝ) : realIntervalPath a b ⊥ = a := by
  simp [realIntervalPath]

@[simp] theorem realIntervalPath_one (a b : ℝ) : realIntervalPath a b ⊤ = b := by
  simp [realIntervalPath]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffinePathTime
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing affine restriction maps and their clipped inverse on the
standard path interval. Interior inequalities remain exact after clipping. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def affinePathTime (a b : PathTime) : C(PathTime, PathTime) where
  toFun := fun t => Set.Icc.convexComb a b t
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : PathTime => (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ))
    fun_prop

theorem affinePathTime_coe (a b t : PathTime) :
    (affinePathTime a b t : ℝ) = ((b : ℝ) - a) * t + a := by
  change (1 - (t : ℝ)) * a + (t : ℝ) * b = _
  ring

theorem affinePathTime_zero (a b : PathTime) : affinePathTime a b ⊥ = a := by
  exact Set.Icc.convexComb_zero a b

theorem affinePathTime_one (a b : PathTime) : affinePathTime a b ⊤ = b := by
  exact Set.Icc.convexComb_one a b

theorem affinePathTime_strictMono {a b : PathTime} (hab : a < b) :
    StrictMono (affinePathTime a b) := by
  intro s t hst
  change (affinePathTime a b s : ℝ) < (affinePathTime a b t : ℝ)
  simp only [affinePathTime_coe]
  have h := mul_lt_mul_of_pos_left
    (show (s : ℝ) < t from hst) (sub_pos.mpr (show (a : ℝ) < b from hab))
  linarith

def rescalePathTime (a b : PathTime) : C(PathTime, PathTime) where
  toFun := fun t => projIcc 0 1 zero_le_one (((t : ℝ) - a) / ((b : ℝ) - a))
  continuous_toFun := by fun_prop

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MonotoneDyadicMass
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomless time measures split exactly over a monotone image of a dyadic
partition. This bounds restricted physical length by the old time measure. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_monotone_dyadic_restrict (μ : Measure PathTime) [NullSingletonClass μ]
    (f : PathTime → PathTime) (hf : Monotone f) (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ.restrict (Icc (f (dyadicLeft n i)) (f (dyadicRight n i))) =
      μ.restrict (Icc (f ⊥) (f ⊤)) := by
  induction n with
  | zero =>
    change (∑ i : Fin 1, μ.restrict (Icc (f (dyadicLeft 0 i)) (f (dyadicRight 0 i)))) = _
    rw [Fin.sum_univ_one]
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr]
  | succ n ih =>
    rw [sum_dyadic_children]
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [← dyadicRight_even, ← restrict_Icc_add μ (hf (dyadicLeft_le_right _ _))]
    · rw [dyadicLeft_even, dyadicRight_odd]
    · rw [dyadicRight_even]
      exact hf (dyadicLeft_le_right _ _)

theorem sum_monotone_dyadic_mass (μ : Measure PathTime) [NullSingletonClass μ]
    (f : PathTime → PathTime) (hf : Monotone f) (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ (Icc (f (dyadicLeft n i)) (f (dyadicRight n i))) =
      μ (Icc (f ⊥) (f ⊤)) := by
  have h := congrArg (fun ν : Measure PathTime => ν univ) (sum_monotone_dyadic_restrict μ f hf n)
  simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.restrict_apply_univ] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffineTagRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual affine restriction of tagged paths. Reparameterized tags keep
their old tuples; empty and constant tag pieces become inactive. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def affineRawTag (a b : PathTime) : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      rescalePathTime a b q.2.2.2.1, rescalePathTime a b q.2.2.2.2⟩

variable {X : Type*} [MetricSpace X]

def affineRestrictedPath (a b : PathTime) (γ : C(PathTime, X)) : C(PathTime, X) :=
  γ.comp (affinePathTime a b)

def affineRestrictedTag (a b : PathTime) (γ : C(PathTime, X)) (τ : TagSlot) : TagSlot :=
  if (affineRestrictedPath a b γ, affineRawTag a b τ) ∈ nonconstantTagSegment
  then affineRawTag a b τ else inactiveTag

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffinePhysicalRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An affine restriction has at most the original physical-domain length.
The estimate uses the actual inverse quotient and its arclength measure. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem affinePathTime_clip {a b : PathTime} (hab : a < b) (c d t : PathTime) :
    affinePathTime a b (timeClip c d t) =
      timeClip (affinePathTime a b c) (affinePathTime a b d) (affinePathTime a b t) := by
  change affinePathTime a b (max c (min d t)) =
    max (affinePathTime a b c) (min (affinePathTime a b d) (affinePathTime a b t))
  rw [(affinePathTime_strictMono hab).monotone.map_max,
    (affinePathTime_strictMono hab).monotone.map_min]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem pathsInsideOn_affine_image {a b : PathTime} (hab : a < b)
    (γ : C(PathTime, X)) {c d : PathTime}
    (hγ : affineRestrictedPath a b γ ∈ pathsInsideOn U c d) :
    γ ∈ pathsInsideOn U (affinePathTime a b c) (affinePathTime a b d) := by
  intro t ht
  have he := (affinePathTime a b).continuous.image_Icc_of_strictMono
    (affinePathTime_strictMono hab) (a := c) (b := d)
  rw [← he] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact hγ hs

theorem physicalSubpath_affine (e : G ≃ₜ U) {a b : PathTime} (hab : a < b)
    (γ : C(PathTime, X)) {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ ∈ pathsInsideOn U c d) :
    physicalSubpath e hcd ⟨affineRestrictedPath a b γ, hγ⟩ =
      (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
        ⟨γ, pathsInsideOn_affine_image hab γ hγ⟩).comp (affinePathTime a b) := by
  apply ContinuousMap.ext
  intro t
  change (e.symm ⟨γ (affinePathTime a b (timeClip c d t)), _⟩).val =
    (e.symm ⟨γ (timeClip (affinePathTime a b c) (affinePathTime a b d)
      (affinePathTime a b t)), _⟩).val
  apply congrArg Subtype.val
  apply congrArg e.symm
  apply Subtype.ext
  exact congrArg γ (affinePathTime_clip hab c d t)

theorem physicalSubpath_affine_length_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ.val ∈ pathsInsideOn U c d) :
    eVariationOn (physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩) univ ≤
      physicalTimeLength e y₀ γ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [physicalSubpath_affine e hab γ.val hcd hγ,
    physicalTimeLength_compact_mass e hU y₀ γ ((affinePathTime_strictMono hab).monotone hcd)
      (pathsInsideOn_affine_image hab γ.val hγ)]
  exact eVariationOn.comp_le_of_monotoneOn
    (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩) (affinePathTime a b)
    ((affinePathTime_strictMono hab).monotone.monotoneOn _) (fun _ _ => mem_univ _)

theorem physicalDyadicLength_affine_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicLength e y₀ n i (affineRestrictedPath a b γ.val) ≤
      physicalTimeLength e y₀ γ
        (Icc (affinePathTime a b (dyadicLeft n i)) (affinePathTime a b (dyadicRight n i))) := by
  by_cases hi : affineRestrictedPath a b γ.val ∈
      pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i _ hi]
    exact physicalSubpath_affine_length_le e hU y₀ γ hab (dyadicLeft_le_right n i) hi
  · simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hi]
    have hz : eVariationOn (ContinuousMap.const PathTime y₀) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact bot_le

theorem physicalDomainLength_affine_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalDomainLength e y₀ (affineRestrictedPath a b γ.val) ≤
      physicalTimeLength e y₀ γ (Icc a b) := by
  apply iSup_le
  intro n
  calc
    physicalStageLength e y₀ n (affineRestrictedPath a b γ.val) ≤
        ∑ i : Fin (2 ^ n), physicalTimeLength e y₀ γ
          (Icc (affinePathTime a b (dyadicLeft n i)) (affinePathTime a b (dyadicRight n i))) :=
      Finset.sum_le_sum fun i _ => physicalDyadicLength_affine_le e hU y₀ γ hab n i
    _ = _ := by rw [sum_monotone_dyadic_mass _ _ (affinePathTime_strictMono hab).monotone,
      affinePathTime_zero, affinePathTime_one]

theorem physicalDomainLength_affine_finite (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalDomainLength e y₀ (affineRestrictedPath a b γ.val) < ∞ :=
  (physicalDomainLength_affine_le e hU y₀ γ hab).trans_lt
    ((measure_mono (subset_univ _)).trans_lt (measure_lt_top _ _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffinePhysicalTimeMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical-domain time measure of a restricted path. The proof
identifies local arclength and the support in the open domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def affineFinitePhysicalPath (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) : FinitePhysicalPath e y₀ :=
  ⟨affineRestrictedPath a b γ.val, physicalDomainLength_affine_finite e hU y₀ γ hab⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_InterleavedCollarCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing retained fragments and genuine short joining arcs into one
allowed collar path, with the sum of their actual costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

abbrev TaggedPhysicalPath (d : PathCodeData X Y) :=
  FinitePhysicalPath d.domainEquiv d.basePoint × (ℕ → TagSlot)

def physicalTollCost (d : PathCodeData X Y) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) : ℝ≥0∞ :=
  (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) + boundaryToll γ.val m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TaggedPhysicalRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual affine restrictions of tagged finite-physical paths, retaining
all the tag and physical-cost information used by the collar fragments. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def restrictTaggedPhysicalPath (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : TaggedPhysicalPath d) {a b : PathTime} (hab : a < b) : TaggedPhysicalPath d :=
  (affineFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 hab,
    fun k => affineRestrictedTag a b Γ.1.val (Γ.2 k))

omit [MeasurableSpace X] in
@[simp] theorem restrictTaggedPhysicalPath_zero (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    (restrictTaggedPhysicalPath d hU Γ hab).1.val ⊥ = Γ.1.val a := by
  change Γ.1.val (affinePathTime a b ⊥) = _
  rw [affinePathTime_zero]

omit [MeasurableSpace X] in
@[simp] theorem restrictTaggedPhysicalPath_one (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    (restrictTaggedPhysicalPath d hU Γ hab).1.val ⊤ = Γ.1.val b := by
  change Γ.1.val (affinePathTime a b ⊤) = _
  rw [affinePathTime_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalRealCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine continuous quotient coordinate with its smooth finite-energy
physical representative, ready for finite transfer. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

structure PhysicalRealCoordinate (d : PathCodeData X Sphere) (π : Sphere → X) where
  quotient : X → ℝ
  quotient_continuous : ContinuousOn quotient d.quotientDomain
  quotient_unit : ∀x, quotient x ∈ Icc 0 1
  physical : (ℝ × ℝ) → ℝ
  physical_measurable : Measurable physical
  physical_smooth : ContDiffOn ℝ (⊤ : ℕ∞) physical (FiniteTransfer.realChartDomain d.physicalDomain)
  physical_energy : MemLp (FiniteTransfer.planarGradient physical) 2
    (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain))
  pullback : ∀z : ℂ, (z : Sphere) ∈ d.physicalDomain → physical (Complex.equivRealProdCLM z) = quotient (π z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompatibleRealBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure CompatibleRealBarrier (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (previous : ℕ → PhysicalRealCoordinate d π) (flags EStar : Set Sphere)
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
      (fun i => circleBandGraph d.quotientDomain (previous i).quotient) labels) = 0

namespace CompatibleRealBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

def controlledSize (B : CompatibleRealBarrier d π previous flags EStar regions f W₁) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∫x in FiniteTransfer.realChartDomain d.physicalDomain \
    (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' B.penalty,
      FiniteTransfer.gradientEnergy B.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) +
    countingSquareNorm B.weight

end CompatibleRealBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierRebase
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

def PhysicalRealCoordinate.rebase {d e : PathCodeData X Sphere} {π : Sphere → X}
    (Q : PhysicalRealCoordinate d π)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain) :
    PhysicalRealCoordinate e π where
  quotient := Q.quotient
  quotient_continuous := by simpa only [hU] using Q.quotient_continuous
  quotient_unit := Q.quotient_unit
  physical := Q.physical
  physical_measurable := Q.physical_measurable
  physical_smooth := by simpa only [hG] using Q.physical_smooth
  physical_energy := by simpa only [hG] using Q.physical_energy
  pullback := fun z hz => Q.pullback z (hG ▸ hz)

variable [MeasurableSpace C(PathTime, Sphere)]

def CompatibleRealBarrier.rebase {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {previous : ℕ → PhysicalRealCoordinate d π} {next : ℕ → PhysicalRealCoordinate e π}
    {flags EStar : Set Sphere} {regions : ℕ → Set Sphere}
    {f : d.quotientDomain → Sphere} {g : e.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f W)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hE : e.anchor = d.anchor) (hB : e.dust = d.dust)
    (hprev : ∀ i, (next i).quotient = (previous i).quotient)
    (hfg : ∀ x : e.quotientDomain, g x = f ⟨x.val, hU ▸ x.property⟩) :
    CompatibleRealBarrier e π next flags EStar regions g W where
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
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityContraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-linear conductivity equation is solved in the actual complex
L2 space by contraction. The operator parameter is only the contraction
property of the Beurling operator; the fixed point and its support are
constructed here. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

abbrev ComplexPlaneL2 := Lp ℂ 2 (volume : Measure EuclideanPlane)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPlaneSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness on an open plane set and integrable partial derivatives give
an actual Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace DeGiorgi

 def MemW1pWitness.sub
    {U : Set CircleDomainRigidity.EuclideanPlane} {u v : CircleDomainRigidity.EuclideanPlane → ℝ}
    (hu : MemW1pWitness 2 u U) (hv : MemW1pWitness 2 v U) :
    MemW1pWitness 2 (fun x => u x - v x) U :=
  (hu.add (hv.smul (-1))).congr_ae (Eventually.of_forall fun x => by ring)

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise classical Green input used below.

M. Spivak, Calculus on Manifolds (1965), Theorem 5-5, p.124,
Stokes' theorem on a compact oriented manifold with boundary. The
specialization is a bounded smooth Jordan region with finitely many
pairwise disjoint round holes and a smooth real one-form. Circle
boundaries have positive disk orientation, so their integrals are
subtracted. The compact region lies inside the open set of smoothness.
https://www.cimat.mx/~gil/docencia/2013/topologia_variedades/spivak-calculus-on-manifolds.pdf -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

/-- A positively oriented regular parametrization of the actual Jordan
boundary. Positivity is specified by the real argument lift around
interior points, independently of any integration formula. -/
structure PositiveJordanParametrization (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) γ
  periodic : Function.Periodic γ 1
  injective : InjOn γ (Ico 0 1)
  regular : ∀ t, deriv γ t ≠ 0
  boundary : γ '' Icc 0 1 = frontier (jordanInterior H)
  positive : ∀ z ∈ jordanInterior H, ∃ u : C(unitInterval, ℝ),
    (∀ t, (u t : UnitAddCircle) = normalizedArgument (γ t - z)) ∧ u 1 = u 0 + 1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- The concrete chart and inverse chart are inverse at all finite chart values. -/
theorem chart_chartSymm (p : Sphere) (z : ℂ) :
    chart p (chartSymm p z) = z := by
  by_cases hp : p = ∞
  · simp [chart, chartSymm, hp, finiteCoord]
  · simp [chart, chartSymm, hp, finiteCoord]

/-- The identity is conformal in both finite and infinite charts. -/
theorem isConformalAt_id (p : Sphere) : IsConformalAt id p := by
  refine ⟨continuousAt_id, 1, one_ne_zero, ?_⟩
  convert hasDerivAt_id (chart p p) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact chart_chartSymm p z

/-- Paper 047-01, Introduction, `thm:main`: removability implies rigidity. -/
def CircleDomainRemovabilityRigidity : Prop :=
  ∀ (U V : Set Sphere) (f : Sphere → Sphere),
    IsCircleDomain U → IsCircleDomain V →
    IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
    ∃ M : Mobius, ∀ p ∈ U, f p = M • p

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalComposition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composition in the concrete sphere charts

The finite and infinite charts are locally inverse at their centers.
The ordinary complex chain rule therefore proves composition of the
actual conformal-equivalence predicate used by the main statements.
-/

open Set Filter Classical
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem IsConformalEquivalence.bijOn
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V) :
    BijOn f U V := by
  obtain ⟨_, hmap, g, _, hgmap, hleft, hright⟩ := hf
  refine ⟨hmap, ?_, ?_⟩
  · intro x hx y hy hxy
    calc
      x = g (f x) := (hleft x hx).symm
      _ = g (f y) := congrArg g hxy
      _ = y := hleft y hy
  · intro y hy
    exact ⟨g y, hgmap hy, hright y hy⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MobiusNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete Möbius normalizations

Affine changes and inversion are homeomorphisms of the concrete sphere.
Their matrix actions agree with the projective-line action used in the
definition of round disks.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem affineSphere_eq_smul (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    affineSphere a b ha p = affineMobius a b ha • p := by
  cases p using OnePoint.rec with
  | infty => simp [affineSphere, OnePoint.smul_infty_eq_ite, affineMobius]
  | coe z => simp [affineSphere, affineHomeomorph, OnePoint.smul_some_eq_ite, affineMobius]

theorem isRoundClosedDisk_image_mobius {K : Set Sphere} (hK : IsRoundClosedDisk K)
    (M : Mobius) : IsRoundClosedDisk ((fun p : Sphere => M • p) '' K) := by
  obtain ⟨N, rfl⟩ := hK
  refine ⟨M * N, ?_⟩
  rw [Set.image_image]
  congr 1
  funext p
  exact (mul_smul M N p).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleMobiusImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle domains under the normalizing Möbius maps

Round complementary disks transform by multiplication of their defining
matrices. A homeomorphic Möbius map therefore preserves circle domains.
The explicit normalizer sends any prescribed sphere point to infinity.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def pointToInfinity (p : Sphere) : Sphere ≃ₜ Sphere :=
  p.elim (Homeomorph.refl _) (fun z =>
    (affineSphere 1 (-z) one_ne_zero).trans CannonMobius.inversion)

theorem pointToInfinity_apply_self (p : Sphere) : pointToInfinity p p = OnePoint.infty := by
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change CannonMobius.inv (affineSphere 1 (-z) one_ne_zero (z : Sphere)) = OnePoint.infty
    have heq : affineSphere 1 (-z) one_ne_zero (z : Sphere) = ((0 : ℂ) : Sphere) := by
      simp [affineSphere, affineHomeomorph]
    rw [heq]
    exact CannonMobius.inv_zero

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MobiusConformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Holomorphy of the explicit normalizing Möbius maps

The affine chart at infinity is the rational function z / (a + b z).
This gives a nonzero derivative there as well as in every finite chart.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem finiteCoord_sphereInv_coe (z : ℂ) : finiteCoord (sphereInv (z : Sphere)) = z⁻¹ := by
  change CannonMobius.coordinate (CannonMobius.inv (z : Sphere)) = z⁻¹
  exact CannonMobius.coordinate_inv_coe z

@[simp] theorem chart_infty_self : chart OnePoint.infty OnePoint.infty = 0 := by
  simp [finiteCoord]

theorem isConformalAt_inversion (p : Sphere) : IsConformalAt CannonMobius.inversion p := by
  refine ⟨CannonMobius.inversion.continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨1, one_ne_zero, ?_⟩
    have heq : (fun z => chart (sphereInv OnePoint.infty)
        (sphereInv (chartSymm OnePoint.infty z))) = id := by
      funext z
      simp only [sphereInv_infty, chart_coe_apply, chartSymm, ite_true, if_true,
        sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
    change HasDerivAt (fun z => chart (sphereInv OnePoint.infty)
      (sphereInv (chartSymm OnePoint.infty z))) 1 (chart OnePoint.infty OnePoint.infty)
    rw [heq, chart_infty_self]
    exact hasDerivAt_id 0
  | coe z =>
    by_cases hz : z = 0
    · subst z
      refine ⟨1, one_ne_zero, ?_⟩
      have heq : (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
          (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) = id := by
        funext w
        simp only [sphereInv_zero, chart_infty_apply, chartSymm_coe_apply,
          sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
      change HasDerivAt (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
        (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) 1 (chart ((0 : ℂ) : Sphere) ((0 : ℂ) : Sphere))
      rw [heq, chart_coe_self]
      exact hasDerivAt_id 0
    · refine ⟨-(z ^ 2)⁻¹, neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hz)), ?_⟩
      have hfp : sphereInv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by simp [sphereInv, hz]
      change HasDerivAt (fun w => chart (sphereInv (z : Sphere))
        (sphereInv (chartSymm (z : Sphere) w))) _ (chart (z : Sphere) (z : Sphere))
      simpa only [hfp, chart_coe_apply, chartSymm_coe_apply,
        finiteCoord_sphereInv_coe, finiteCoord_coe] using hasDerivAt_inv hz

theorem affine_chart_at_infinity (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    chart OnePoint.infty (affineSphere a b ha (chartSymm OnePoint.infty z)) = z / (a + b * z) := by
  by_cases hz : z = 0
  · simp [hz, chart, chartSymm, sphereInv, affineSphere, finiteCoord]
  · have hden : a * z⁻¹ + b = (a + b * z) / z := by field_simp
    have hs : chartSymm OnePoint.infty z = ((z⁻¹ : ℂ) : Sphere) := by
      simp [chartSymm, sphereInv, hz]
    rw [hs, affineSphere_coe]
    rw [chart_infty_apply, finiteCoord_sphereInv_coe, hden, inv_div]

theorem isConformalAt_affineSphere (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha) p := by
  refine ⟨(affineSphere a b ha).continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
    have hd := (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) a).add ((hasDerivAt_id (0 : ℂ)).const_mul b))
      (by simpa using ha)
    have heq : (fun z => chart (affineSphere a b ha OnePoint.infty)
        (affineSphere a b ha (chartSymm OnePoint.infty z))) = fun z => z / (a + b * z) := by
      funext z
      exact affine_chart_at_infinity a b ha z
    rw [heq, chart_infty_self]
    have hscalar : (1 * (a + b * 0) - 0 * (0 + b * 1)) / (a + b * 0) ^ 2 = a⁻¹ := by
      simp only [mul_zero, add_zero, zero_mul, sub_zero, one_mul]
      field_simp
    convert hd using 1 <;> first
      | rfl
      | (funext z; simp only [Pi.div_apply, Pi.add_apply, id])
      | (simp only [Pi.add_apply, id]; exact hscalar.symm)
  | coe z =>
    refine ⟨a, ha, ?_⟩
    simpa only [affineSphere_coe, chart_coe_apply, chartSymm_coe_apply,
      finiteCoord, OnePoint.elim_some, id_eq, mul_one] using
        ((hasDerivAt_id z).const_mul a).add_const b

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConformalNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformal point-to-infinity normalization

The explicit normalizer and its inverse are conformal in every sphere
chart. Postcomposition therefore preserves the conformal equivalence,
not just the topology and the round complementary components.
-/

open Set Function
open scoped OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem affineSphere_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    (affineSphere a b ha).symm = affineSphere a⁻¹ (-b / a) (inv_ne_zero ha) := by
  apply Homeomorph.ext
  intro p
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (((z - b) / a : ℂ) : Sphere) = ((a⁻¹ * z + -b / a : ℂ) : Sphere)
    congr 1
    ring

theorem isConformalAt_affineSphere_symm (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha).symm p := by
  rw [affineSphere_symm_eq]
  exact isConformalAt_affineSphere _ _ _ p

theorem isConformalAt_pointToInfinity (p q : Sphere) :
    IsConformalAt (pointToInfinity p) q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt (CannonMobius.inversion ∘ affineSphere 1 (-z) one_ne_zero) q
    exact (isConformalAt_inversion _).comp (isConformalAt_affineSphere _ _ _ q)

theorem isConformalAt_pointToInfinity_symm (p q : Sphere) :
    IsConformalAt (pointToInfinity p).symm q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt ((affineSphere 1 (-z) one_ne_zero).symm ∘ CannonMobius.inversion) q
    exact (isConformalAt_affineSphere_symm _ _ _ _).comp (isConformalAt_inversion q)

theorem isConformalEquivalence_of_homeomorph (e : Sphere ≃ₜ Sphere) (U : Set Sphere)
    (he : IsConformalOn e U) (hi : IsConformalOn e.symm (e '' U)) :
    IsConformalEquivalence e U (e '' U) := by
  refine ⟨he, mapsTo_image _ _, e.symm, hi, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply] using hp
  · intro p _
    exact e.symm_apply_apply p
  · intro p _
    exact e.apply_symm_apply p

theorem isConformalEquivalence_pointToInfinity (p : Sphere) (U : Set Sphere) :
    IsConformalEquivalence (pointToInfinity p) U (pointToInfinity p '' U) :=
  isConformalEquivalence_of_homeomorph _ U (fun q _ => isConformalAt_pointToInfinity p q)
    (fun q _ => isConformalAt_pointToInfinity_symm p q)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric conformality in the concrete sphere charts

Metric conformality records the pullback Gram matrix and positive
orientation of the actual real differential. When the source metric is
a positive scalar multiple of the Euclidean metric, these equations
imply the complex Cauchy--Riemann equation and a nonzero derivative.
-/

open Set Filter
open scoped Topology OnePoint Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def sphereLocalMap (f : Sphere → Sphere) (p : Sphere) : ℂ → ℂ :=
  fun z => chart (f p) (f (chartSymm p z))

def sphereChartMetric (g : (ℝ × ℝ) → PlanarMetric) (p : Sphere) : PlanarMetric := by
  classical
  exact if p = ∞ then (4 : ℝ) • (1 : PlanarMetric) else g (Complex.equivRealProdCLM (finiteCoord p))

def IsMetricConformalAt (g : (ℝ × ℝ) → PlanarMetric) (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ DifferentiableAt ℝ (sphereLocalMap f p) (chart p p) ∧
    let A := fderiv ℝ (sphereLocalMap f p) (chart p p)
    ∃ scale : ℝ, 0 < scale ∧
      (A 1).re ^ 2 + (A 1).im ^ 2 = scale * sphereChartMetric g p 0 0 ∧
      (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2 = scale * sphereChartMetric g p 1 1 ∧
      (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = scale * sphereChartMetric g p 0 1 ∧
      0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothSphereCharts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth maps in the concrete sphere charts

This regularity predicate records ordinary real smoothness. For a
holomorphic sphere map it follows from complex analyticity in a
neighborhood; composition follows from the local chart inverse law.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

/-- Real smoothness in the same source and target charts as metric conformality. -/
def IsSmoothSphereAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ContDiffAt ℝ ∞ (sphereLocalMap f p) (chart p p)

def IsSmoothSphereOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsSmoothSphereAt f p

theorem isConformalAt_chartTransform (p q : Sphere) : IsConformalAt (chartTransform p) q := by
  by_cases hp : p = OnePoint.infty
  · rw [chartTransform, ite_eq_left hp]
    exact isConformalAt_inversion q
  · rw [chartTransform, ite_eq_right hp]
    exact isConformalAt_id q

theorem analyticAt_finite_map_of_conformal
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U)
    (hf : IsConformalOn f U) {z : ℂ} (hz : (z : Sphere) ∈ U)
    (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    AnalyticAt ℂ (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hmem : ∀ᶠ w : ℂ in 𝓝 z, (w : Sphere) ∈ U :=
    OnePoint.continuous_coe.continuousAt.eventually (hU.mem_nhds hz)
  have hfin : ∀ᶠ w : ℂ in 𝓝 z, f (w : Sphere) ≠ OnePoint.infty :=
    ((hf _ hz).1.comp OnePoint.continuous_coe.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds hfinite)
  filter_upwards [hmem, hfin] with w hw hfw
  obtain ⟨_, d, _, hd⟩ := hf _ hw
  have heq : (fun y => chart (f (w : Sphere)) (f (chartSymm (w : Sphere) y))) =
      (fun y : ℂ => finiteCoord (f (y : Sphere))) := by
    funext y
    simp only [chart, hfw, ite_false, if_false, chartSymm_coe_apply]
  rw [heq, chart_coe_self] at hd
  exact hd.differentiableAt

theorem IsConformalOn.isSmoothSphereAt
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) : IsSmoothSphereAt f p := by
  let g : Sphere → Sphere := chartTransform (f p) ∘ f ∘ chartTransform p
  let V : Set Sphere := (chartTransform p) ⁻¹' U
  have hV : IsOpen V := hU.preimage (chartTransform p).continuous
  have hg : IsConformalOn g V := by
    intro q hq
    exact (isConformalAt_chartTransform _ _).comp
      ((hf _ hq).comp (isConformalAt_chartTransform _ q))
  have hcenter : chartTransform p ((chart p p : ℂ) : Sphere) = p := by
    rw [← chartSymm_eq_transform]
    exact chartSymm_chart_self p
  have hzV : ((chart p p : ℂ) : Sphere) ∈ V := by
    change chartTransform p ((chart p p : ℂ) : Sphere) ∈ U
    rwa [hcenter]
  have hfin : g ((chart p p : ℂ) : Sphere) ≠ OnePoint.infty := by
    change chartTransform (f p) (f (chartTransform p ((chart p p : ℂ) : Sphere))) ≠ _
    rw [hcenter]
    exact chartTransform_center_ne_infty _
  have ha := analyticAt_finite_map_of_conformal hV hg hzV hfin
  have heq : (fun w : ℂ => finiteCoord (g (w : Sphere))) = sphereLocalMap f p := by
    funext w
    rw [sphereLocalMap, chart_eq_coordinate_transform, chartSymm_eq_transform]
    rfl
  refine ⟨(hf p hp).1, ?_⟩
  rw [heq] at ha
  exact ha.contDiffAt.restrict_scalars ℝ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LaurentNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Principal normalization at infinity

A holomorphic germ fixing zero with nonzero derivative has a reciprocal
with one simple pole. Two divided differences isolate its pole and
constant terms and leave an analytic first-order remainder. This gives
the affine normalization used before taking limits of circle models.
-/

open Set Filter Function Asymptotics
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteCoord_sphereInv (p : Sphere) : finiteCoord (sphereInv p) = (finiteCoord p)⁻¹ := by
  cases p using OnePoint.rec with
  | infty => simp [finiteCoord]
  | coe z => simpa only [finiteCoord_coe] using finiteCoord_sphereInv_coe z

theorem analyticAt_infty_chart
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    AnalyticAt ℂ (sphereLocalMap f OnePoint.infty) 0 := by
  let F : Sphere → Sphere := CannonMobius.inversion ∘ f ∘ CannonMobius.inversion
  let V : Set Sphere := CannonMobius.inversion ⁻¹' U
  have hV : IsOpen V := hU.preimage CannonMobius.inversion.continuous
  have hF : IsConformalOn F V := by
    intro p hp
    exact (isConformalAt_inversion _).comp ((hf _ hp).comp (isConformalAt_inversion p))
  have hzero : ((0 : ℂ) : Sphere) ∈ V := by
    change CannonMobius.inv ((0 : ℂ) : Sphere) ∈ U
    simpa only [CannonMobius.inv_zero] using hinf
  have hFzero : F ((0 : ℂ) : Sphere) = ((0 : ℂ) : Sphere) := by
    change CannonMobius.inv (f (CannonMobius.inv ((0 : ℂ) : Sphere))) = _
    rw [CannonMobius.inv_zero, hfix, CannonMobius.inv_infty]
  have ha := analyticAt_finite_map_of_conformal hV hF hzero
    (by rw [hFzero]; exact OnePoint.coe_ne_infty (0 : ℂ))
  change AnalyticAt ℂ (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) 0 at ha
  have heq : sphereLocalMap f OnePoint.infty =
      (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) := by
    funext z
    change chart (f OnePoint.infty) (f (chartSymm OnePoint.infty z)) = _
    rw [hfix, chart_infty_apply, chartSymm, ite_eq_left rfl]
  rw [heq]
  exact ha

theorem affine_normalization_expansion
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * finiteCoord (f (z : Sphere)) + b = z + z⁻¹ * R z⁻¹ := by
  have ha := analyticAt_infty_chart hU hf hinf hfix
  have hzero : sphereLocalMap f OnePoint.infty 0 = 0 := by
    simp only [sphereLocalMap, chartSymm, ite_true, if_true, sphereInv_zero, hfix, chart_infty_self]
  obtain ⟨_, d, hd, hder⟩ := hf _ hinf
  have hder' : HasDerivAt (sphereLocalMap f OnePoint.infty) d 0 := by
    change HasDerivAt (sphereLocalMap f OnePoint.infty) d
      (chart OnePoint.infty OnePoint.infty) at hder
    rw [chart_infty_self] at hder
    exact hder
  have hdu : deriv (sphereLocalMap f OnePoint.infty) 0 ≠ 0 := hder'.deriv.symm ▸ hd
  obtain ⟨a, b, R, hane, hR, hexp⟩ := reciprocal_germ_normalization ha hzero hdu
  refine ⟨a, b, R, hane, hR, ?_⟩
  intro z hz
  have h := hexp z⁻¹ (inv_ne_zero hz)
  have hchart : (sphereLocalMap f OnePoint.infty z⁻¹)⁻¹ = finiteCoord (f (z : Sphere)) := by
    simp only [sphereLocalMap, hfix, chart_infty_apply, chartSymm, ite_true, if_true]
    have hinv : sphereInv ((z⁻¹ : ℂ) : Sphere) = (z : Sphere) := by
      simp [sphereInv, inv_ne_zero hz]
    rw [hinv, finiteCoord_sphereInv, inv_inv]
  simpa only [hchart, inv_inv] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def FiniteNondegenerateComplement (U : Set Sphere) : Prop :=
  (connectedComponentIn Uᶜ '' Uᶜ).Finite ∧
    ∀ p ∈ Uᶜ, (connectedComponentIn Uᶜ p).Nontrivial

def FiniteCircleUniformization : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U → Uᶜ.Nonempty →
    FiniteNondegenerateComplement U →
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isCompact_closedTerminalCap (H : ℂ ≃ₜ ℂ) : IsCompact (closedTerminalCap H) :=
  (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe

theorem isPreconnected_closedTerminalCap (H : ℂ ≃ₜ ℂ) : IsPreconnected (closedTerminalCap H) :=
  (isConnected_jordanInterior H).isPreconnected.closure.image _ OnePoint.continuous_coe.continuousOn

theorem nontrivial_closedTerminalCap (H : ℂ ≃ₜ ℂ) : (closedTerminalCap H).Nontrivial := by
  have hzero : H 0 ∈ closure (jordanInterior H) := by
    rw [closure_jordanInterior]
    exact ⟨0, by simp, rfl⟩
  have hone : H 1 ∈ closure (jordanInterior H) := by
    rw [closure_jordanInterior]
    exact ⟨1, by simp, rfl⟩
  refine ⟨(H 0 : ℂ), ⟨H 0, hzero, rfl⟩, (H 1 : ℂ), ⟨H 1, hone, rfl⟩, ?_⟩
  intro heq
  exact zero_ne_one (H.injective (OnePoint.coe_injective heq))

theorem disjoint_closedTerminalCaps {I : Type*} (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    Pairwise (Disjoint on fun i => closedTerminalCap (H i)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hyx : y = x := OnePoint.coe_injective heq
  exact Set.disjoint_left.mp (hdisj hij) hx (hyx ▸ hy)

theorem isOpen_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ) :
    IsOpen (openCompletedRegion H) :=
  (isClosed_iUnion_of_finite fun i => (isCompact_closedTerminalCap (H i)).isClosed).isOpen_compl

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedMetricUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite circle models fixing infinity

Postcomposing the actual finite metric model by the explicit Möbius
normalizer retains all conformality conclusions. Injectivity then
ensures that every finite source point has a finite target coordinate.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem finite_image_of_fixes_infty
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hU : OnePoint.infty ∈ U) (hf : f OnePoint.infty = OnePoint.infty)
    {z : ℂ} (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty := by
  intro h
  exact OnePoint.coe_ne_infty z (hinj hz hU (h.trans hf.symm))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PrincipalNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine principal normalization of a sphere map

The analytic remainder at zero is bounded near zero. After inversion
this gives the actual O(1/z) remainder at infinity, rather than only a
formal Laurent coefficient calculation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def IsPrincipalNormalized (f : Sphere → Sphere) : Prop :=
  f OnePoint.infty = OnePoint.infty ∧
    (fun z : ℂ => finiteCoord (f (z : Sphere)) - z) =O[cobounded ℂ] (fun z => z⁻¹)

theorem affine_normalization_bigO
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ a b : ℂ, a ≠ 0 ∧
      (fun z : ℂ => a * finiteCoord (f (z : Sphere)) + b - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨a, b, R, ha, hR, hexp⟩ := affine_normalization_expansion hU hf hinf hfix
  have hb : (fun z : ℂ => R z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hR.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  refine ⟨a, b, ha, hp.congr' ?_ ?_⟩
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    change z⁻¹ * R z⁻¹ = a * finiteCoord (f (z : Sphere)) + b - z
    rw [hexp z hz]
    ring
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

theorem principal_normalize_at_infty
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinj : InjOn f U) (hinf : OnePoint.infty ∈ U)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (ha : a ≠ 0), IsPrincipalNormalized (affineSphere a b ha ∘ f) := by
  obtain ⟨a, b, ha, hbig⟩ := affine_normalization_bigO hU hf hinf hfix
  refine ⟨a, b, ha, ?_, ?_⟩
  · simp only [Function.comp_apply, hfix, affineSphere_infty]
  · have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ U := by
      have hm := OnePoint.tendsto_coe_infty (hU.mem_nhds hinf)
      change {z : ℂ | (z : Sphere) ∈ U} ∈ cobounded ℂ
      rw [Metric.cobounded_eq_cocompact]
      rw [coclosedCompact_eq_cocompact] at hm
      exact hm
    apply hbig.congr' _ EventuallyEq.rfl
    filter_upwards [hm] with z hz
    have hfin := finite_image_of_fixes_infty hinj hinf hfix hz
    have hp : f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (CannonMobius.coe_coordinate hfin).symm
    have he := congrArg (fun p : Sphere => finiteCoord (affineSphere a b ha p)) hp
    simpa only [Function.comp_apply, affineSphere_coe, finiteCoord_coe] using
      congrArg (fun w : ℂ => w - z) he.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakHeightIdentification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of weak error-gradient limits with the derivatives
of the actual continuous height limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def heightLimitGradient (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (p : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun i => if i = 0 then G₀ p else G₁ p+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalScalarSolver
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar transport data for conductivity postcomposition, constructed
from smooth principal maps. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def CompactScalarPullback (φ : ℂ ≃ₜ ℂ) : Prop :=
  ∀ (u : EuclideanPlane → ℝ), Continuous u → HasCompactSupport u →
    ∀ W : DeGiorgi.MemW1pWitness 2 u univ,
    ∀ F : Set EuclideanPlane, IsCompact F →
      (∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) →
      ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
        ∀ i, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph φ '' F → V.weakGrad x i=0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalLocalInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local inverses in sphere charts

On an open set the chart expressions of a conformal sphere map are
analytic. The ordinary complex inverse function theorem therefore
identifies its neighborhood filters. An injective conformal map then
has a conformal inverse on its image, with no global extension assumed.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem IsConformalOn.analyticAt_sphereLocalMap
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) :
    AnalyticAt ℂ (sphereLocalMap f p) (chart p p) := by
  let g : Sphere → Sphere := chartTransform (f p) ∘ f ∘ chartTransform p
  let V : Set Sphere := (chartTransform p) ⁻¹' U
  have hV : IsOpen V := hU.preimage (chartTransform p).continuous
  have hg : IsConformalOn g V := by
    intro q hq
    exact (isConformalAt_chartTransform _ _).comp
      ((hf _ hq).comp (isConformalAt_chartTransform _ q))
  have hcenter : chartTransform p ((chart p p : ℂ) : Sphere) = p := by
    rw [← chartSymm_eq_transform]
    exact chartSymm_chart_self p
  have hzV : ((chart p p : ℂ) : Sphere) ∈ V := by
    change chartTransform p ((chart p p : ℂ) : Sphere) ∈ U
    rwa [hcenter]
  have hfin : g ((chart p p : ℂ) : Sphere) ≠ OnePoint.infty := by
    change chartTransform (f p) (f (chartTransform p ((chart p p : ℂ) : Sphere))) ≠ _
    rw [hcenter]
    exact chartTransform_center_ne_infty _
  have ha := analyticAt_finite_map_of_conformal hV hg hzV hfin
  have heq : (fun w : ℂ => finiteCoord (g (w : Sphere))) = sphereLocalMap f p := by
    funext w
    rw [sphereLocalMap, chart_eq_coordinate_transform, chartSymm_eq_transform]
    rfl
  rwa [heq] at ha

theorem map_chartSymm_nhds (p : Sphere) :
    map (chartSymm p) (𝓝 (chart p p)) = 𝓝 p := by
  have he : chartSymm p = fun z : ℂ => chartTransform p (z : Sphere) :=
    funext (chartSymm_eq_transform p)
  rw [he]
  change map (chartTransform p ∘ ((↑) : ℂ → Sphere)) (𝓝 (chart p p)) = _
  rw [← map_map, ← OnePoint.nhds_coe_eq, (chartTransform p).map_nhds_eq]
  congr 1
  rw [← chartSymm_eq_transform, chartSymm_chart_self]

theorem IsConformalOn.map_nhds_eq
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) {p : Sphere} (hp : p ∈ U) : map f (𝓝 p) = 𝓝 (f p) := by
  obtain ⟨hc, d, hd, hder⟩ := hf p hp
  have ha : ContDiffAt ℂ 1 (sphereLocalMap f p) (chart p p) :=
    (hf.analyticAt_sphereLocalMap hU hp).contDiffAt
  have hstrict : HasStrictDerivAt (sphereLocalMap f p) d (chart p p) :=
    ha.hasStrictDerivAt' hder (by norm_num)
  have hcenter : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  have heq : (f ∘ chartSymm p) =ᶠ[𝓝 (chart p p)]
      (chartSymm (f p) ∘ sphereLocalMap f p) := by
    have ht : Tendsto (f ∘ chartSymm p) (𝓝 (chart p p)) (𝓝 (f p)) := by
      have hc' : ContinuousAt f (chartSymm p (chart p p)) := by
        rwa [chartSymm_chart_self]
      simpa only [Function.comp_apply, chartSymm_chart_self] using
        (hc'.comp (continuous_chartSymm p).continuousAt).tendsto
    filter_upwards [ht.eventually (eventually_chartSymm_chart (f p))] with z hz
    exact hz.symm
  calc
    map f (𝓝 p) = map (f ∘ chartSymm p) (𝓝 (chart p p)) := by
      rw [← map_map, map_chartSymm_nhds]
    _ = map (chartSymm (f p) ∘ sphereLocalMap f p) (𝓝 (chart p p)) := map_congr heq
    _ = map (chartSymm (f p)) (𝓝 (chart (f p) (f p))) := by
      rw [← map_map, hstrict.map_nhds_eq hd, hcenter]
    _ = 𝓝 (f p) := map_chartSymm_nhds (f p)

theorem IsConformalOn.isOpen_image
    {f : Sphere → Sphere} {U O : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) : IsOpen (f '' O) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨p, hp, rfl⟩
  rw [← hf.map_nhds_eq hU (hOU hp)]
  exact image_mem_map (hO.mem_nhds hp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual inverse of an injective conformal sphere map

Local analytic inverse functions agree with the set-theoretic inverse
on an open source domain. Thus an injective conformal map has a genuine
two-sided conformal equivalence with its image.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_conformal_invFunOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) {p : Sphere} (hp : p ∈ U) :
    ContinuousAt (invFunOn f U) (f p) := by
  have hleft : (invFunOn f U ∘ f) =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact hinj.leftInvOn_invFunOn hx
  change map (invFunOn f U) (𝓝 (f p)) ≤ 𝓝 (invFunOn f U (f p))
  rw [hinj.leftInvOn_invFunOn hp, ← hf.map_nhds_eq hU hp, map_map, map_congr hleft, map_id]

theorem isConformalAt_invFunOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) {p : Sphere} (hp : p ∈ U) :
    IsConformalAt (invFunOn f U) (f p) := by
  obtain ⟨hfc, d, hd, hder⟩ := hf p hp
  have ha : ContDiffAt ℂ 1 (sphereLocalMap f p) (chart p p) :=
    (hf.analyticAt_sphereLocalMap hU hp).contDiffAt
  have hstrict : HasStrictDerivAt (sphereLocalMap f p) d (chart p p) :=
    ha.hasStrictDerivAt' hder (by norm_num)
  let g := invFunOn f U
  have hgp : g (f p) = p := hinj.leftInvOn_invFunOn hp
  let G : ℂ → ℂ := fun z => chart p (g (chartSymm (f p) z))
  have hsource : ∀ᶠ z in 𝓝 (chart p p), chartSymm p z ∈ U := by
    have ht : Tendsto (chartSymm p) (𝓝 (chart p p)) (𝓝 p) := by
      simpa only [chartSymm_chart_self] using
        (continuous_chartSymm p).continuousAt.tendsto (x := chart p p)
    exact ht.eventually (hU.mem_nhds hp)
  have htarget : ∀ᶠ z in 𝓝 (chart p p),
      chartSymm (f p) (chart (f p) (f (chartSymm p z))) = f (chartSymm p z) := by
    have ht : Tendsto (f ∘ chartSymm p) (𝓝 (chart p p)) (𝓝 (f p)) := by
      have hc' : ContinuousAt f (chartSymm p (chart p p)) := by
        rwa [chartSymm_chart_self]
      simpa only [Function.comp_apply, chartSymm_chart_self] using
        (hc'.comp (continuous_chartSymm p).continuousAt).tendsto
    exact ht.eventually (eventually_chartSymm_chart (f p))
  have hleft : ∀ᶠ z in 𝓝 (chart p p), G (sphereLocalMap f p z) = z := by
    filter_upwards [hsource, htarget] with z hz hs
    change chart p (g (chartSymm (f p) (chart (f p) (f (chartSymm p z))))) = z
    rw [hs]
    change chart p (invFunOn f U (f (chartSymm p z))) = z
    rw [hinj.leftInvOn_invFunOn hz, chart_chartSymm]
  have hgd := (hstrict.to_local_left_inverse hd hleft).hasDerivAt
  have hcenter : sphereLocalMap f p (chart p p) = chart (f p) (f p) := by
    simp only [sphereLocalMap, chartSymm_chart_self]
  rw [hcenter] at hgd
  refine ⟨continuousAt_conformal_invFunOn hf hU hinj hp, d⁻¹, inv_ne_zero hd, ?_⟩
  simpa only [G, g, hinj.leftInvOn_invFunOn hp] using hgd

theorem isConformalEquivalence_of_injOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) : IsConformalEquivalence f U (f '' U) := by
  refine ⟨hf, mapsTo_image _ _, invFunOn f U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact isConformalAt_invFunOn hf hU hinj hp
  · rintro _ ⟨p, hp, rfl⟩
    exact invFunOn_apply_mem hp
  · exact hinj.leftInvOn_invFunOn
  · rintro _ ⟨p, hp, rfl⟩
    exact invFunOn_apply_eq hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereRealDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def sphereRealMap (f : Sphere → Sphere) (x : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (finiteCoord (f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothSphereEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure IsSmoothSphereEquivalence (f fi : Sphere → Sphere) (U V : Set Sphere) : Prop where
  smooth : IsSmoothSphereOn f U
  mapsTo : MapsTo f U V
  smooth_inv : IsSmoothSphereOn fi V
  mapsTo_inv : MapsTo fi V U
  left_inv : ∀ p ∈ U, fi (f p) = p
  right_inv : ∀ p ∈ V, f (fi p) = p

theorem IsSmoothSphereEquivalence.bijOn
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V) :
    BijOn f U V := by
  refine ⟨h.mapsTo, ?_, ?_⟩
  · intro x hx y hy heq
    simpa only [h.left_inv x hx, h.left_inv y hy] using congrArg fi heq
  · intro y hy
    exact ⟨fi y, h.mapsTo_inv hy, h.right_inv y hy⟩

theorem IsConformalEquivalence.exists_smooth_inverse
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V)
    (hU : IsOpen U) (hV : IsOpen V) :
    ∃ fi, IsSmoothSphereEquivalence f fi U V := by
  obtain ⟨hfc, hmap, fi, hfic, himap, hl, hr⟩ := hf
  exact ⟨fi, fun p hp => hfc.isSmoothSphereAt hU hp, hmap,
    fun p hp => hfic.isSmoothSphereAt hV hp, himap, hl, hr⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DisjointDustContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous contours for finitely many clopen dust pieces

Disjoint compact physical pieces have disjoint open neighborhoods. Regular
contours and the outer subfamily of their combined family have disjoint
closed fills inside the prescribed connected-complement containers.
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

theorem _root_.Set.Finite.frontier_biUnion_subset {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) (s : ι → Set X) : frontier (⋃ i ∈ I, s i) ⊆ ⋃ i ∈ I, frontier (s i) := by
  simpa only [hI.mem_toFinset] using hI.toFinset.frontier_biUnion_subset s

namespace CircleDomainRigidity

theorem exists_disjoint_dust_contours
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (A V : I → Set ℂ) (F : Set ℂ)
    (hAc : ∀ i, IsCompact (A i)) (hAd : Pairwise (Disjoint on A))
    (hAF : ∀ i, A i ⊆ F) (hFA : ∀ i, IsClosed (F \ A i))
    (hVo : ∀ i, IsOpen (V i)) (hAV : ∀ i, A i ⊆ V i)
    (hVc : ∀ i, IsPreconnected (V i)ᶜ)
    (hVu : ∀ i, ¬ Bornology.IsBounded (V i)ᶜ) :
    ∃ (f : I → ℂ → ℝ) (t : I → ℝ)
      (γ : (Σ i, ConnectedComponents {z // f i z = t i}) → Circle → ℂ)
      (H : (Σ i, ConnectedComponents {z // f i z = t i}) → ℂ ≃ₜ ℂ)
      (s : Set (Σ i, ConnectedComponents {z // f i z = t i})),
      s.Finite ∧ ((⋃ i, A i) ⊆ ⋃ p ∈ s, jordanInterior (H p)) ∧
      s.Pairwise (fun p q => Disjoint (closure (jordanInterior (H p)))
        (closure (jordanInterior (H q)))) ∧
      ∀ p ∈ s, closure (jordanInterior (H p)) ⊆ V p.1 ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ p) ∧ Topology.IsEmbedding (γ p) ∧
        frontier (jordanInterior (H p)) = range (γ p) ∧
        Disjoint (frontier (jordanInterior (H p))) F := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (A i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hAc i).isClosed (hAc j).isClosed (hAd hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (A i))
  let O : I → Set ℂ := fun i => W i ∩ V i
  have hOo (i) : IsOpen (O i) := (hW i).1.inter (hVo i)
  have hAO (i) : A i ⊆ O i := subset_inter (hW i).2 (hAV i)
  choose f t hf ht hUo hAU hUc hUO hUF hlevel hreg havoid hfrontavoid using
    fun i => exists_regular_superlevel_isolating_obstacle hsard (hAc i) (hAF i)
      (hFA i) (hOo i) (hAO i)
  have hdata (i) := compact_regular_level_circle_contours
    (hf i) (hreg i) (hlevel i)
  have : ∀ i, Finite (ConnectedComponents {z // f i z = t i}) := fun i => (hdata i).1
  choose γ₀ hγ₀ hγd hγcover using fun i => (hdata i).2
  let γ : (Σ i, ConnectedComponents {z // f i z = t i}) → Circle → ℂ :=
    fun p => γ₀ p.1 p.2
  have hfrontU (i) : frontier {z | t i < f i z} = {z | f i z = t i} :=
    frontier_superlevel_eq_regular_level (hf i).continuous (hreg i)
  have hγO (p : Σ i, ConnectedComponents {z // f i z = t i}) : range (γ p) ⊆ O p.1 := by
    intro z hz
    apply hUO p.1
    apply frontier_subset_closure
    rw [hfrontU, ← hγcover p.1]
    exact mem_iUnion.mpr ⟨p.2, hz⟩
  have hpair : Pairwise (fun p q => Disjoint (range (γ p)) (range (γ q))) := by
    intro p q hpq
    by_cases hi : p.1 = q.1
    · obtain ⟨i, c⟩ := p
      obtain ⟨j, d⟩ := q
      dsimp at hi
      subst j
      exact hγd i (fun h => hpq (Sigma.ext rfl (heq_of_eq h)))
    · exact (hWd hi).mono (fun z hz => (hγO p hz).1) (fun z hz => (hγO q hz).1)
  choose H hH using fun p => hschoenflies (γ p) (hγ₀ p.1 p.2).2.continuous
    (hγ₀ p.1 p.2).2.injective
  have hfront (p) : frontier (jordanInterior (H p)) = range (γ p) :=
    frontier_jordanInterior_eq_circle_range (H p) (γ p) (hH p)
  have hHpair : Pairwise (fun p q => Disjoint (frontier (jordanInterior (H p)))
      (frontier (jordanInterior (H q)))) := by
    intro p q hpq
    simpa only [hfront] using hpair hpq
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hHpair
  let : Finite s := hs.to_subtype
  let U : Set ℂ := ⋃ i, {z | t i < f i z}
  have hUopen : IsOpen U := isOpen_iUnion hUo
  have hUbdd : Bornology.IsBounded U :=
    (isCompact_iUnion hUc).isBounded.subset (iUnion_mono fun _ => subset_closure)
  have hselected (p : s) : frontier (jordanInterior (H p)) ⊆ frontier U := by
    intro z hz
    have hzo : z ∈ O p.val.1 := hγO p (hfront p ▸ hz)
    have hzlevel : f p.val.1 z = t p.val.1 := by
      change z ∈ {w | f p.val.1 w = t p.val.1}
      rw [← hγcover p.val.1]
      exact mem_iUnion.mpr ⟨p.val.2, hfront p ▸ hz⟩
    rw [hUopen.frontier_eq]
    refine ⟨?_, ?_⟩
    · apply closure_mono (subset_iUnion (fun i => {z | t i < f i z}) p.val.1)
      apply frontier_subset_closure
      rwa [hfrontU]
    · intro hzU
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzU
      by_cases hij : p.val.1 = j
      · subst j
        change t p.val.1 < f p.val.1 z at hzj
        linarith [hzlevel]
      · have hzjO := hUO j (subset_closure hzj)
        exact Set.disjoint_left.mp (hWd hij) hzo.1 hzjO.1
  have hcover : frontier U ⊆ ⋃ p : s, closure (jordanInterior (H p)) := by
    intro z hz
    have hfin := (Set.toFinite (univ : Set I)).frontier_biUnion_subset
      (fun i => {z | t i < f i z})
    have hfin' : frontier U ⊆ ⋃ i, frontier {z | t i < f i z} := by
      simpa only [mem_univ, iUnion_true] using hfin
    have hzi : z ∈ ⋃ i, frontier {z | t i < f i z} := by
      exact hfin' hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzi
    rw [hfrontU, ← hγcover i] at hi
    obtain ⟨c, hc⟩ := mem_iUnion.mp hi
    let p : Σ i, ConnectedComponents {z // f i z = t i} := ⟨i, c⟩
    have hp : z ∈ closure (jordanInterior (H p)) := by
      apply frontier_subset_closure
      rw [hfront p]
      exact hc
    obtain ⟨q, hq, hpq⟩ := hdom p
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hpq hp⟩
  have hsd' : Pairwise (Disjoint on fun p : s => closure (jordanInterior (H p))) := by
    intro p q hpq
    exact hsd p.property q.property (fun h => hpq (Subtype.ext h))
  have hUcover := open_subset_finite_jordanInteriors_of_frontier_subset
    (fun p : s => H p) hsd' hUopen hUbdd hcover hselected
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hUcover (mem_iUnion.mpr ⟨i, hAU i hi⟩))
    exact mem_iUnion₂.mpr ⟨p, p.property, hp⟩
  · intro p _
    refine ⟨closed_jordanInterior_subset_of_unbounded_connected_compl (H p)
      (hVc p.1) (hVu p.1) ?_, (hγ₀ p.1 p.2).1, (hγ₀ p.1 p.2).2, hfront p, ?_⟩
    · exact fun z hz => (hγO p (hfront p ▸ hz)).2
    · apply (havoid p.1).mono_left
      intro z hz
      rw [← hγcover p.1]
      exact mem_iUnion.mpr ⟨p.2, hfront p ▸ hz⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CompletedChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
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

@[simp] theorem realChartDomain_sphericalCore (K : Set (ℝ × ℝ)) :
    realChartDomain (sphericalCore K) = K := by
  ext x
  change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ sphericalCore K ↔ x ∈ K
  simp only [coe_mem_sphericalCore, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem realChartDomain_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    realChartDomain (sphericalDiskUnion H) = ⋃ i, realJordanInterior (H i) := by
  ext x
  change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ sphericalDiskUnion H ↔ _
  rw [coe_mem_sphericalDiskUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, Complex.equivRealProdCLM.symm x, hi,
      Complex.equivRealProdCLM.apply_symm_apply x⟩
  · intro hx
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    refine ⟨i, ?_⟩
    simpa only [← hzx, ContinuousLinearEquiv.symm_apply_apply] using hz

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRealSphereMaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem coe_finiteCoord {p : Sphere} (hp : p ≠ OnePoint.infty) :
    ((finiteCoord p : ℂ) : Sphere) = p := CannonMobius.coe_coordinate hp

namespace IsSmoothSphereEquivalence

variable {f fi : Sphere → Sphere} {U V : Set Sphere}
variable (h : IsSmoothSphereEquivalence f fi U V)
variable (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)

include h hU hfix

theorem finite_forward {z : ℂ} (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty :=
  finite_image_of_fixes_infty h.bijOn.injOn hU hfix hz

end IsSmoothSphereEquivalence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ExteriorSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trapping the bounded side of a circle-model image

A compact exterior piece has closed image. Its open interior has open
image, and their difference is the image of the boundary circle. A
connected set avoiding that boundary and meeting the open image must
lie entirely in the image. This supplies the topological part of the
uniform bound for finite circle models.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereEquivalence.isOpen_image
    {f fi : Sphere → Sphere} {U V : Set Sphere} (hf : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {S : Set Sphere} (hS : IsOpen S) (hSU : S ⊆ U) : IsOpen (f '' S) := by
  have heq : f '' S = V ∩ fi ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hf.mapsTo (hSU hx), ?_⟩
      change fi (f x) ∈ S
      rwa [hf.left_inv x (hSU hx)]
    · rintro ⟨hy, hiy⟩
      exact ⟨fi y, hiy, hf.right_inv y hy⟩
  rw [heq]
  have hc : ContinuousOn fi V := fun y hy => (hf.smooth_inv y hy).1.continuousWithinAt
  exact hc.isOpen_inter_preimage hV hS

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformality of the normalized limit

`HurwitzZeroFreeLimit` records the zero-free form of the same published
Hurwitz theorem already used for injective limits: Ahlfors, *Complex
Analysis*, third edition (1979), Chapter 5, Theorem 2, p. 178. Applied
to the derivatives, it gives a nonzero limiting derivative unless the
limit is constant. The latter alternative is ruled out on each core.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isConformalAt_extendAtInfinity_coe
    {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F z) (hd : deriv F z ≠ 0) :
    IsConformalAt (extendAtInfinity F) (z : Sphere) := by
  refine ⟨OnePoint.continuousAt_coe.mpr ?_, deriv F z, hd, ?_⟩
  · exact OnePoint.continuous_coe.continuousAt.comp hF.continuousAt
  · simpa only [extendAtInfinity_coe, chart_coe_apply, chartSymm_coe_apply,
      chart_coe_self, finiteCoord_coe] using hF.hasDerivAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarModelCoefficients
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common exterior radius bounds the actual coefficient of every model.
Consequently the retained model class has near-maximal real coefficients. -/
open Set Function Filter Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem finite_differentiable_of_sphere_conformal
    {f : ℂ → ℂ} {z : ℂ} (hf : IsConformalAt (extendAtInfinity f) (z : Sphere)) :
    DifferentiableAt ℂ f z := by
  obtain ⟨_, d, _, hd⟩ := hf
  have he : (fun w => chart (extendAtInfinity f (z : Sphere))
      (extendAtInfinity f (chartSymm (z : Sphere) w))) = f := by
    funext w
    simp only [extendAtInfinity_coe, chart_coe_apply, chartSymm_coe_apply, finiteCoord_coe]
  rw [he, chart_coe_self] at hd
  exact hd.differentiableAt

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def coefficientSet (G : Set Sphere) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ) : Set ℝ :=
  Set.range (fun M : CompactScalarModel G u => M.coefficient.re)

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ControlledHeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative data proved for the actual nearly extremal height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

structure ControlledHeight (R d : ℝ) where
  height : C(ℂ, ℝ)
  error₀ : Lp ℝ 2 (volume : Measure EuclideanPlane)
  error₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)
  weak_gradient : DeGiorgi.HasWeakGrad (heightLimitGradient error₀ error₁)
    (height ∘ complexPlaneCoordinates) univ
  error_bound : (∫ p, error₀ p^2+error₁ p^2) ≤ 2*Real.pi*d
  log_bound : ∀ c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
    |height c-height z|^2*Real.log (1/r) ≤
      16*Real.pi*(2*(2*Real.pi*d)+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)
  local_bound : ∀ S, 2*R ≤ S → ∀ z ∈ closedBall 0 S, |height z| ≤ S+R
  exterior_bound : ∀ z, 2*R ≤ ‖z‖ → |height z-z.im| ≤ 2*R^2/‖z‖
  approximants : ℕ → ℂ ≃ₜ ℂ
  height_limit : TendstoLocallyUniformly (fun n z => (approximants n z).im) height atTop

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem interior_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hKG : K ⊆ G) :
    interior (f '' K) = f '' interior K := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    have hO : IsOpen (G ∩ f ⁻¹' interior (f '' K)) :=
      hc.isOpen_inter_preimage hG isOpen_interior
    have hsub : G ∩ f ⁻¹' interior (f '' K) ⊆ K := by
      rintro z ⟨hzG, hz⟩
      obtain ⟨w, hw, he⟩ := interior_subset hz
      exact (hi (hKG hw) hzG he) ▸ hw
    exact ⟨x, interior_maximal hsub hO ⟨hKG hx, hy⟩, rfl⟩
  · exact interior_maximal (image_mono interior_subset)
      (ho _ isOpen_interior (interior_subset.trans hKG))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_finite_part_of_conformalAt
    {f : Sphere → Sphere} {z : ℂ}
    (hf : IsConformalAt f (z : Sphere)) (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    ContinuousAt (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  obtain ⟨_, d, _, hd⟩ := hf
  have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) =
      (fun w : ℂ => finiteCoord (f (w : Sphere))) := by
    funext w
    simp only [chart, hfinite, ite_false, if_false, chartSymm_coe_apply]
  rw [he, chart_coe_self] at hd
  exact hd.continuousAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanDiskImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Jordan disks contained in the domain of an open embedding have their actual Jordan
interiors as images. This identifies the anchor disks in finite models. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem open_eq_jordan_of_frontier
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hf : frontier U = frontier (jordanInterior H)) :
    U = jordanInterior H := by
  have hsub : U ⊆ jordanInterior H := by
    have ht := open_subset_finite_jordanInteriors_of_frontier_subset (fun _ : Unit => H)
      (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim) hU hb
      (by simpa only [iUnion_const, hf] using frontier_subset_closure)
      (fun _ => hf.symm.subset)
    simpa only [iUnion_const] using ht
  apply Subset.antisymm hsub
  apply (isConnected_jordanInterior H).isPreconnected.subset_of_closure_inter_subset hU
  · obtain ⟨z, hz⟩ := hne
    exact ⟨z, hsub hz, hz⟩
  · rintro z ⟨hzcl, hzH⟩
    by_contra hzU
    have hzF : z ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hzcl, hzU⟩
    rw [hf, (jordanInterior_isOpen H).frontier_eq] at hzF
    exact hzF.2 hzH

/-- The images are the whole Jordan interior and its closure, rather than merely subsets of the
corresponding sides, by planar Schoenflies. -/
theorem exists_jordan_image_disk (hsch : PlanarSchoenflies)
    {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ G) :
    ∃ K : ℂ ≃ₜ ℂ,
      f '' jordanInterior H = jordanInterior K ∧
      f '' closure (jordanInterior H) = closure (jordanInterior K) ∧
      frontier (jordanInterior K) = f '' frontier (jordanInterior H) := by
  let γ : Circle → ℂ := fun t => H t
  have hγ : Continuous γ := H.continuous.comp continuous_subtype_val
  have hγH (t : Circle) : γ t ∈ frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    exact ⟨t, t.property, rfl⟩
  have hγG (t : Circle) : γ t ∈ G := hHG (frontier_subset_closure (hγH t))
  have hδ : Continuous (f ∘ γ) := hc.comp_continuous hγ hγG
  have hδinj : Injective (f ∘ γ) := by
    intro s t he
    apply Subtype.ext
    apply H.injective
    exact hi (hγG s) (hγG t) he
  obtain ⟨K, hK⟩ := hsch (f ∘ γ) hδ hδinj
  have hrange : range γ = frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hfront : frontier (jordanInterior K) = f '' frontier (jordanInterior H) := by
    rw [frontier_jordanInterior_eq_circle_range K (f ∘ γ) hK, range_comp, hrange]
  let P := closure (jordanInterior H)
  have hPc : IsCompact P := isCompact_closure_jordanInterior H
  have hPi : interior P = jordanInterior H := interior_closure_jordanInterior H
  have hPfront : frontier P = frontier (jordanInterior H) := by
    simp only [frontier, P, closure_closure, interior_closure_jordanInterior,
      (jordanInterior_isOpen H).interior_eq]
  have hiimage : interior (f '' P) = f '' jordanInterior H := by
    rw [planar_interior_image hc ho hG hi hHG, hPi]
  have hreg : closure (f '' jordanInterior H) = f '' P := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure)
        (hPc.image_of_continuousOn (hc.mono hHG)).isClosed
    · exact (hc.mono hHG).image_closure
  have himagefront : frontier (f '' jordanInterior H) = frontier (jordanInterior K) := by
    rw [frontier, hreg, (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG)).interior_eq]
    rw [← hiimage]
    have he := planar_frontier_image hc ho hG hi hPc hHG
    rw [hPfront, ← hfront] at he
    simpa only [frontier, (hPc.image_of_continuousOn (hc.mono hHG)).isClosed.closure_eq] using he
  have himage : f '' jordanInterior H = jordanInterior K :=
    open_eq_jordan_of_frontier K (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG))
      ((hPc.image_of_continuousOn (hc.mono hHG)).isBounded.subset (image_mono subset_closure))
      ((isConnected_jordanInterior H).nonempty.image f) himagefront
  exact ⟨K, himage, by rw [← hreg, himage], hfront⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientCollarJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual image of a physical collar under the component-collapse map
is a Jordan disk. Its filled side is identified by its exact frontier. -/

open Set Function Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem continuousOn_finiteCoord_of_avoids_infty {S : Set Sphere}
    (hS : OnePoint.infty ∉ S) : ContinuousOn finiteCoord S := by
  apply OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.mpr
  apply continuousOn_id.congr
  intro x hx
  change (finiteCoord x : Sphere) = x
  exact CannonMobius.coe_coordinate (fun h => hS (h ▸ hx))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def closedJordanCore {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ

theorem interior_closedJordanCore {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ) :
    interior (closedJordanCore H) = openCompletedRegion H := by
  rw [closedJordanCore, interior_compl, closure_iUnion_of_finite]
  simp only [closure_sphere_image_jordanInterior]
  rfl

theorem frontier_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    frontier (closedJordanCore H) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
  rw [closedJordanCore, frontier_compl]
  have hUo : IsOpen (⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i)) :=
    isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))
  rw [hUo.frontier_eq, closure_iUnion_of_finite]
  simp only [closure_sphere_image_jordanInterior]
  apply Subset.antisymm
  · rintro p ⟨hp, hnot⟩
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
    refine mem_iUnion.mpr ⟨i, z, ?_, rfl⟩
    rw [(jordanInterior_isOpen (H i)).frontier_eq]
    exact ⟨hz, fun hi => hnot (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)⟩
  · intro p hp
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
    refine ⟨mem_iUnion.mpr ⟨i, z, frontier_subset_closure hz, rfl⟩, ?_⟩
    intro hi
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp hi
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    by_cases hij : i = j
    · subst j
      exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ hw)
    · exact Set.disjoint_left.mp (hd hij) (frontier_subset_closure hz) (subset_closure hw)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

structure SmoothJordanCore (G : Set Sphere) where
  count : ℕ
  disk : Fin count → ℂ ≃ₜ ℂ
  curve : Fin count → Circle → ℂ
  disjoint : Pairwise (Disjoint on fun i => closure (jordanInterior (disk i)))
  subset_domain : closedJordanCore disk ⊆ G
  smooth : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i)
  embedding : ∀ i, Topology.IsEmbedding (curve i)
  boundary : ∀ i, frontier (jordanInterior (disk i)) = range (curve i)

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

def carrier : Set Sphere := closedJordanCore C.disk

theorem isCompact : IsCompact C.carrier :=
  (isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (C.disk i))).isClosed_compl.isCompact

theorem subset : C.carrier ⊆ G := C.subset_domain

end SmoothJordanCore

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NestedEndComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nested target collars and complementary components

The end-component argument uses compactness twice: a nested sequence of
continua has connected intersection, and a connected subset of a finite
disjoint closed cover stays in the piece containing its initial point.
These are proved here for the actual target sphere. No uniformization or
boundary-extension statement is assumed.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem nested_sphere_sets_eventually_subset
    {C : ℕ → Set Sphere} (hclosed : ∀ n, IsClosed (C n))
    (hnest : Antitone C) {O : Set Sphere} (hO : IsOpen O)
    (hsub : (⋂ n, C n) ⊆ O) : ∃ n, C n ⊆ O := by
  obtain ⟨n, hn⟩ := hO.isClosed_compl.isCompact.elim_directed_family_closed C hclosed
    (Set.disjoint_iff_inter_eq_empty.mp (disjoint_compl_left_iff_subset.mpr hsub)) hnest.directed_ge
  exact ⟨n, disjoint_compl_left_iff_subset.mp (Set.disjoint_iff_inter_eq_empty.mpr hn)⟩

theorem isConnected_nested_sphere_intersection
    {C : ℕ → Set Sphere} (hclosed : ∀ n, IsClosed (C n))
    (hconn : ∀ n, IsConnected (C n)) (hnest : Antitone C) :
    IsConnected (⋂ n, C n) := by
  refine ⟨IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n => hnest (Nat.le_succ n)) (fun n => (hconn n).nonempty)
    (hclosed 0).isCompact hclosed, ?_⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter hclosed)]
  intro a b ha hb hab hdisj
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hdisj
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset hclosed hnest (hu.union hv)
    (hab.trans (union_subset_union hau hbv))
  rcases (hconn n).isPreconnected.subset_or_subset hu hv huv hn with hn_u | hn_v
  · left
    exact Disjoint.left_le_of_le_sup_right hab
      (huv.mono ((iInter_subset C n).trans hn_u) hbv)
  · right
    exact (huv.symm.mono ((iInter_subset C n).trans hn_v) hau).left_le_of_le_sup_left hab

/-- A component of a subset of a finite disjoint closed union stays in
the unique piece that contains the chosen point. The pieces need not
themselves be connected. -/
theorem connectedComponentIn_subset_finite_closed_piece
    {I : Type*} [Finite I] {E : Set Sphere}
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (Disjoint on C)) (hcover : E ⊆ ⋃ i, C i)
    {i : I} {p : Sphere} (hp : p ∈ E) (hpi : p ∈ C i) :
    connectedComponentIn E p ⊆ C i := by
  classical
  let R : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    rintro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover' : E ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := E) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover')
      (by rw [hCR.inter_eq, inter_empty]) with h | h
  · exact h
  · exact fun _ _ => (Set.disjoint_left.mp hCR hpi (h (mem_connectedComponentIn hp))).elim

/-- The nested target disks for an end form exactly one complementary
component once the finite image cores give the closed covers. -/
theorem connectedComponentIn_eq_nested_end
    {I : ℕ → Type*} [∀ n, Finite (I n)] {E : Set Sphere}
    (C : (n : ℕ) → I n → Set Sphere) (b : (n : ℕ) → I n)
    (hclosed : ∀ n i, IsClosed (C n i))
    (hconn : ∀ n, IsConnected (C n (b n)))
    (hdisj : ∀ n, Pairwise (Disjoint on C n))
    (hcover : ∀ n, E ⊆ ⋃ i, C n i)
    (hnest : Antitone (fun n => C n (b n)))
    (hmiss : (⋂ n, C n (b n)) ⊆ E)
    {p : Sphere} (hp : p ∈ ⋂ n, C n (b n)) :
    connectedComponentIn E p = ⋂ n, C n (b n) := by
  apply Subset.antisymm
  · apply subset_iInter
    intro n
    exact connectedComponentIn_subset_finite_closed_piece (C n) (hclosed n)
      (hdisj n) (hcover n) (hmiss hp) (mem_iInter.mp hp n)
  · exact (isConnected_nested_sphere_intersection (fun n => hclosed n (b n)) hconn
      hnest).isPreconnected.subset_connectedComponentIn hp hmiss

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanEndComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# End components of a strict Jordan-core exhaustion

The selected target disk at each level is determined by the omitted point.
Strict core inclusion forces these disks to nest strictly. Their intersection
is exactly the full complementary component of the exhausted image.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem component_eq_nested_jordan_end
    {I : ℕ → Type*} [∀ n, Finite (I n)]
    (H : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (H n i))))
    (A : ℕ → Set Sphere) {V : Set Sphere}
    (hA : ∀ n, (A n)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H n i))
    (hstrict : ∀ n, A n ⊆ interior (A (n + 1))) (hcover : (⋃ n, A n) = V)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ b : (n : ℕ) → I n,
      connectedComponentIn Vᶜ p = ⋂ n, closedTerminalCap (H n (b n)) ∧
      (∀ n, closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n))) ∧
      ∀ n, connectedComponentIn Vᶜ p ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n)) := by
  classical
  have hAV (n : ℕ) : A n ⊆ V := by rw [← hcover]; exact subset_iUnion A n
  have hAe (n : ℕ) : A n = closedJordanCore (H n) := by
    apply compl_injective
    simpa only [closedJordanCore, compl_compl] using hA n
  have hcap (n : ℕ) (i : I n) : closedTerminalCap (H n i) ⊆ (interior (A n))ᶜ := by
    rw [hAe n, interior_closedJordanCore]
    intro q hq hqint
    exact hqint (mem_iUnion.mpr ⟨i, hq⟩)
  have hCclosed (n : ℕ) (i : I n) : IsClosed (closedTerminalCap (H n i)) :=
    (isCompact_closedTerminalCap (H n i)).isClosed
  have hCd (n : ℕ) : Pairwise (Disjoint on fun i => closedTerminalCap (H n i)) :=
    disjoint_closedTerminalCaps (H n) (hd n)
  have hCcover (n : ℕ) : Vᶜ ⊆ ⋃ i, closedTerminalCap (H n i) := by
    intro q hq
    have hqa : q ∈ (A n)ᶜ := fun h => hq (hAV n h)
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hA n ▸ hqa)
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩
  have hpopen (n : ℕ) : ∃ i : I n, p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H n i) := by
    have hpa : p ∈ (A n)ᶜ := fun h => hp (hAV n h)
    exact mem_iUnion.mp (hA n ▸ hpa)
  choose b hb using hpopen
  have hpb (n : ℕ) : p ∈ closedTerminalCap (H n (b n)) := by
    obtain ⟨z, hz, he⟩ := hb n
    exact ⟨z, subset_closure hz, he⟩
  have hsmall (n : ℕ) : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆ (A n)ᶜ := by
    intro q hq hqa
    exact hcap (n + 1) (b (n + 1)) hq (hstrict n hqa)
  have hnest (n : ℕ) : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n)) := by
    have hsub : closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
        ⋃ i, closedTerminalCap (H n i) := by
      intro q hq
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hA n ▸ hsmall n hq)
      exact mem_iUnion.mpr ⟨i, z, subset_closure hz, rfl⟩
    have hpiece := connectedComponentIn_subset_finite_closed_piece
      (fun i => closedTerminalCap (H n i)) (hCclosed n) (hCd n) hsub (hpb (n + 1)) (hpb n)
    have hconnected := (isPreconnected_closedTerminalCap (H (n + 1) (b (n + 1)))).subset_connectedComponentIn
      (hpb (n + 1)) (Subset.refl _)
    intro q hq
    have hqold := hpiece (hconnected hq)
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp (hA n ▸ hsmall n hq)
    have hqi : q ∈ closedTerminalCap (H n i) := ⟨z, subset_closure hz, he⟩
    by_cases hi : i = b n
    · exact hi ▸ ⟨z, hz, he⟩
    · exact (Set.disjoint_left.mp (hCd n hi) hqi hqold).elim
  have hanti : Antitone (fun n => closedTerminalCap (H n (b n))) := by
    apply antitone_nat_of_succ_le
    intro n q hq
    obtain ⟨z, hz, he⟩ := hnest n hq
    exact ⟨z, subset_closure hz, he⟩
  have hmiss : (⋂ n, closedTerminalCap (H n (b n))) ⊆ Vᶜ := by
    intro q hq hqV
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hqV)
    exact hsmall n (mem_iInter.mp hq (n + 1)) hn
  have he := connectedComponentIn_eq_nested_end
    (fun n i => closedTerminalCap (H n i)) b hCclosed
    (fun n => ⟨⟨p, hpb n⟩, isPreconnected_closedTerminalCap (H n (b n))⟩)
    hCd hCcover hanti hmiss (mem_iInter.mpr hpb)
  refine ⟨b, he, hnest, ?_⟩
  intro n
  rw [he]
  exact (iInter_subset _ (n + 1)).trans (hnest n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedEndChains
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Refinement of matched source and target ends

A finer source contour lies on the chosen source side exactly when its
matched target contour lies on the corresponding target side. Filling
both Jordan contours upgrades boundary containment to strict closed-disk
containment.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem matched_jordan_disk_subset_iff
    {G : Set Sphere} {f : Sphere → Sphere} (hi : InjOn f G)
    (H₀ H₁ J₀ J₁ : ℂ ≃ₜ ℂ)
    (hfrontG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁) ⊆ G)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₁))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H₀)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀)) :
    (closedTerminalCap H₁ ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H₀) ↔
      (closedTerminalCap J₁ ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J₀) := by
  constructor
  · intro hsub
    apply image_mono
    apply closed_jordanInterior_subset_of_frontier_subset J₁ J₀
    intro z hz
    have hzimg : (z : Sphere) ∈ f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H₁)) := by
      rw [hboundary]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, hfx⟩ := hzimg
    have hxcap : x ∈ closedTerminalCap H₁ := by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, frontier_subset_closure hw, rfl⟩
    have hxside : f x ∈ f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀) := by
      rw [← hside]
      exact mem_image_of_mem _ ⟨hfrontG hx, hsub hxcap⟩
    have hzsphere : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior J₀ := hfx ▸ hxside.2
    exact OnePoint.coe_injective.mem_set_image.mp hzsphere
  · intro hsub
    apply image_mono
    apply closed_jordanInterior_subset_of_frontier_subset H₁ H₀
    intro z hz
    have hzG := hfrontG (mem_image_of_mem _ hz)
    have hzfront : f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₁) := by
      rw [← hboundary]
      exact mem_image_of_mem _ (mem_image_of_mem _ hz)
    have hzcap : f (z : Sphere) ∈ closedTerminalCap J₁ := by
      obtain ⟨w, hw, he⟩ := hzfront
      exact ⟨w, frontier_subset_closure hw, he⟩
    have hzside : f (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H₀)) := by
      rw [hside]
      exact ⟨mem_image_of_mem _ hzG, hsub hzcap⟩
    obtain ⟨w, hw, he⟩ := hzside
    have hwz : w = (z : Sphere) := hi hw.1 hzG he
    exact OnePoint.coe_injective.mem_set_image.mp (hwz ▸ hw.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceTargetEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A target component corresponding to a source component

For the same sequence of matched boundary labels, the nested source disks
intersect in the original complementary component and the nested target
disks intersect in a full target complementary component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer


/-- Conversely every target complementary component has a source component
with the same matched boundary address. -/
theorem corresponding_source_end_of_target_of_continuous_open
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere), q ∈ Gᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) := by
  have hAstrict (n : ℕ) : f '' (C n).carrier ⊆ interior (f '' (C (n + 1)).carrier) := by
    rw [interior_image_of_continuous_open hf ho hG hi (C (n + 1)).subset]
    exact image_mono (hstrict n)
  have hAcover : (⋃ n, f '' (C n).carrier) = f '' G := by
    apply Subset.antisymm (iUnion_subset fun n => image_mono (C n).subset)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    exact mem_iUnion.mpr ⟨n, x, interior_subset hn, rfl⟩
  obtain ⟨b, hb, htargetnest, _⟩ := component_eq_nested_jordan_end J hJd
    (fun n => f '' (C n).carrier) hJe hAstrict hAcover hp
  have hfrontG (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxfront : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxfront
  have hsourcenest (n : ℕ) : closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) :=
    (matched_jordan_disk_subset_iff hi ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1))) (hfrontG _ _) (hboundary _ _) (hside _ _)).mpr
      (htargetnest n)
  have hanti : Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    obtain ⟨z, hz, he⟩ := hsourcenest n hx
    exact ⟨z, subset_closure hz, he⟩
  have hclosed (n : ℕ) (i : Fin (C n).count) : IsClosed (closedTerminalCap ((C n).disk i)) :=
    (isCompact_closedTerminalCap ((C n).disk i)).isClosed
  have hconnected (n : ℕ) : IsConnected (closedTerminalCap ((C n).disk (b n))) :=
    ⟨(nontrivial_closedTerminalCap ((C n).disk (b n))).nonempty,
      isPreconnected_closedTerminalCap ((C n).disk (b n))⟩
  obtain ⟨q, hq⟩ := (isConnected_nested_sphere_intersection
    (fun n => hclosed n (b n)) hconnected hanti).nonempty
  have hmiss : (⋂ n, closedTerminalCap ((C n).disk (b n))) ⊆ Gᶜ := by
    intro x hx hxG
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hxG)
    rw [SmoothJordanCore.carrier, interior_closedJordanCore] at hn
    exact hn (mem_iUnion.mpr ⟨b n, mem_iInter.mp hx n⟩)
  have hEcover (n : ℕ) : Gᶜ ⊆ ⋃ i, closedTerminalCap ((C n).disk i) := by
    intro x hx
    have hxa : x ∉ (C n).carrier := fun h => hx ((C n).subset h)
    have hxU : x ∈ ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i) := not_not.mp hxa
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, he⟩
  have hcomponent := connectedComponentIn_eq_nested_end
    (fun n i => closedTerminalCap ((C n).disk i)) b hclosed hconnected
    (fun n => disjoint_closedTerminalCaps (C n).disk (C n).disjoint) hEcover hanti hmiss hq
  exact ⟨b, q, hmiss hq, hcomponent, hb, hsourcenest⟩

theorem corresponding_source_end_of_target
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (q : Sphere), q ∈ Gᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap ((C (n + 1)).disk (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b n)) :=
  corresponding_source_end_of_target_of_continuous_open hG
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi C J hstrict hcover hJd hJe hboundary hside hp


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectionJordanCap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous extension of the inverse carries a matched closed Jordan
cap into its source cap. The boundary identity prevents crossing the source
curve, and a domain point identifies the correct side. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_fiber_on_domain
    {G : Set Sphere} {f P : Sphere → Sphere}
    (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    {x y : Sphere} (hx : x ∈ G) : P y = x ↔ y = f x := by
  constructor
  · intro h
    by_cases hy : y ∈ f '' G
    · obtain ⟨z, hz, rfl⟩ := hy
      have he : z = x := (hInv z hz).symm.trans h
      exact congrArg f he
    · exact ((hOut y hy) (h ▸ hx)).elim
  · rintro rfl
    exact hInv x hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelPointTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal section and its priority interpolation are continuous
at every point end of the actual scalar model. No boundary extension or
upper semicontinuity assertion is an extra input. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def horizontalSection (M : CompactScalarModel G u) (q : Sphere) : ℝ :=
    (finiteCoord (invFun M.projection q)).re

 theorem horizontalSection_on_domain (M : CompactScalarModel G u)
    {q : Sphere} (hq : q ∈ G) :
    M.horizontalSection q = (finiteCoord (extendAtInfinity M.function q)).re := by
  have hh : M.projection (invFun M.projection q) = q :=
    invFun_eq ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  have he := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hh
  simp only [horizontalSection, he]

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundedRoundDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded spherical round disks are Euclidean disks

The projective matrix action is converted to a norm inequality for its
inverse. Excluding infinity makes the leading quadratic coefficient
positive, so the completed-square formula gives a positive radius.
-/

open Set Function
open scoped ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

theorem mobius_smul_mem_unit_disk_iff (M : Mobius) (z : ℂ) :
    M • (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1 ↔
      ‖M 0 0 * z + M 0 1‖ ≤ ‖M 1 0 * z + M 1 1‖ := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using M.det_ne_zero
  by_cases hden : M 1 0 * z + M 1 1 = 0
  · have hnum : M 0 0 * z + M 0 1 ≠ 0 := by
      intro hn
      apply hdet
      calc
        M 0 0 * M 1 1 - M 0 1 * M 1 0 =
            M 0 0 * (M 1 0 * z + M 1 1) - M 1 0 * (M 0 0 * z + M 0 1) := by ring
        _ = 0 := by rw [hden, hn]; ring
    simp only [OnePoint.smul_some_eq_ite, hden, ite_true, if_true, OnePoint.infty_notMem_image_coe,
      norm_zero, norm_le_zero_iff, hnum]
  · rw [OnePoint.smul_some_eq_ite, ite_eq_right hden,
      OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall, dist_zero_right,
      norm_div, div_le_one (norm_pos_iff.mpr hden)]

theorem mobius_leading_normSq_pos (M : Mobius)
    (hinf : M • (OnePoint.infty : Sphere) ∉ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1) :
    0 < Complex.normSq (M 0 0) - Complex.normSq (M 1 0) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using M.det_ne_zero
  by_cases hc : M 1 0 = 0
  · have ha : M 0 0 ≠ 0 := by
      intro ha
      apply hdet
      simp only [ha, hc, zero_mul, mul_zero, sub_zero]
    rw [hc, Complex.normSq_zero, sub_zero]
    exact Complex.normSq_pos.mpr ha
  · rw [OnePoint.smul_infty_eq_ite, ite_eq_right hc,
      OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall, dist_zero_right,
      norm_div, not_le] at hinf
    have hn : ‖M 1 0‖ < ‖M 0 0‖ := by
      simpa only [one_mul] using (lt_div_iff₀ (norm_pos_iff.mpr hc)).mp hinf
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (M 1 0)]

theorem isRoundClosedDisk_eq_euclidean
    {K : Set Sphere} (hK : IsRoundClosedDisk K) (hinf : OnePoint.infty ∉ K) :
    ∃ (c : ℂ) (r : ℝ), 0 < r ∧ K = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨M, rfl⟩ := hK
  let N : Mobius := M⁻¹
  let S : Set Sphere := ((↑) : ℂ → Sphere) '' Metric.closedBall 0 1
  have hmem (p : Sphere) : p ∈ (fun q : Sphere => M • q) '' S ↔ N • p ∈ S := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [N, inv_smul_smul] using hq
    · intro hp
      exact ⟨N • p, hp, smul_inv_smul M p⟩
  have hNinf : N • (OnePoint.infty : Sphere) ∉ S := by
    intro h
    exact hinf ((hmem _).mpr h)
  have hA := mobius_leading_normSq_pos N hNinf
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using N.det_ne_zero
  let c : ℂ := -(conj (N 0 0) * N 0 1 - conj (N 1 0) * N 1 1) /
    ((Complex.normSq (N 0 0) - Complex.normSq (N 1 0) : ℝ) : ℂ)
  let r : ℝ := ‖N 0 0 * N 1 1 - N 0 1 * N 1 0‖ /
    (Complex.normSq (N 0 0) - Complex.normSq (N 1 0))
  have hregion : {z : ℂ | ‖N 0 0 * z + N 0 1‖ ≤ ‖N 1 0 * z + N 1 1‖} =
      Metric.closedBall c r := fractional_norm_region_eq_closedBall _ _ _ _ hA
  refine ⟨c, r, div_pos (norm_pos_iff.mpr hdet) hA, ?_⟩
  ext p
  cases p using OnePoint.rec with
  | infty => exact iff_of_false hinf OnePoint.infty_notMem_image_coe
  | coe z =>
    rw [hmem, mobius_smul_mem_unit_disk_iff,
      OnePoint.coe_injective.mem_set_image, ← hregion]
    rfl

theorem isRoundClosedDisk_coe_closedBall (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsRoundClosedDisk (((↑) : ℂ → Sphere) '' Metric.closedBall c r) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨affineMobius (r : ℂ) c hrc, ?_⟩
  rw [closedBall_eq_affine_image hr.le c, image_image, image_image]
  congr 1
  funext u
  rw [← affineSphere_eq_smul, affineSphere_coe]
  congr 1
  simp only [Complex.real_smul, mul_comm, add_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed conductivity height descends continuously through
the actual source projection, including every nonpoint end. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def heightSection (M : CompactScalarModel G u) {R d : ℝ} (H : ControlledHeight R d) (q : Sphere) : ℝ :=
    H.height (finiteCoord (invFun M.projection q))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanFillLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upper containment for limits of Jordan fills

Uniform convergence of boundary parametrizations traps the approximating
closed fills in every neighborhood of the limiting closed fill. The proof
uses Jordan nesting and radial enlargement.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem jordanInterior_dilated (H : ℂ ≃ₜ ℂ) {r : ℝ} (hr : 0 < r) :
    jordanInterior (dilatedJordan H r hr) = H '' ball (0 : ℂ) r := by
  change (fun z : ℂ => H ((r : ℂ) * z)) '' ball 0 1 = H '' ball 0 r
  rw [← image_image]
  congr 1
  change (fun z : ℂ => r • z) '' ball 0 1 = ball 0 r
  exact smul_unitBall_of_pos (E := ℂ) hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteModelEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Terminal components of an actual finite circle model

Every physical terminal disk determines a target complementary component.
The assignment exhausts all target components and respects every retained
Jordan contour. Only the existing topological inputs are used.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem SmoothJordanCore.boundary_subset_domain
    {G : Set Sphere} (C : SmoothJordanCore G) (i : Fin C.count) :
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i)) ⊆ G := by
  intro x hx
  apply C.subset
  have hxf : x ∈ frontier C.carrier := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    exact mem_iUnion.mpr ⟨i, hx⟩
  simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hxf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteMarkedTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

structure TerminalComponentAssignment {I : Type*} (T : I → ℂ ≃ₜ ℂ)
    (f : Sphere → Sphere) (V : Set Sphere) where
  point : I → Sphere
  outside : ∀ i, point i ∈ Vᶜ
  disjoint : Pairwise (Disjoint on fun i => connectedComponentIn Vᶜ (point i))
  covers : ∀ y ∈ Vᶜ, ∃ i, connectedComponentIn Vᶜ y = connectedComponentIn Vᶜ (point i)
  cluster : ∀ i q, q ∈ closedTerminalCap (T i) → ∀ x : ℕ → Sphere,
    Tendsto x atTop (𝓝 q) → (∀ᶠ n in atTop, x n ∈ openCompletedRegion T) →
    ∀ y, Tendsto (f ∘ x) atTop (𝓝 y) → y ∈ connectedComponentIn Vᶜ (point i)
  retained : ∀ A : SmoothJordanCore (openCompletedRegion T),
    ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
      (∀ j, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L j))) ∧
      ∀ i j, closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) →
        connectedComponentIn Vᶜ (point i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L j)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelAppendedPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact source priority and height coordinates preserve
every trace-pair condition when appended to the flattened old list. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def compactHeightSource (M : CompactScalarModel G u) {R d : ℝ}
    (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ) : EuclideanPlane → ℝ :=
  fun x => sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
    (invFun M.projection (planeSphere x))

 def compactPrioritySource (M : CompactScalarModel G u)
    (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ) (η : ℂ → ℝ) : EuclideanPlane → ℝ :=
  fun x => η (complexPlaneCoordinates x)*priorityInfiniteValue
    (fun n => χ n (complexPlaneCoordinates x)) c
    (M.horizontalSection (complexPlaneCoordinates x : Sphere))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelLocalEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Properness of the actual inverse projection bounds images of bounded
source sets. Complex change of variables then gives their finite energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem projection_bounded_lifts (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {S : Set ℂ} (hS : IsCompact S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Sphere,
      M.projection p ∈ ((↑) : ℂ → Sphere) '' S → ‖finiteCoord p‖ ≤ K := by
  let C := M.projection ⁻¹' (((↑) : ℂ → Sphere) '' S)
  have hC : IsCompact C :=
    ((hS.image OnePoint.continuous_coe).isClosed.preimage M.projection_continuous).isCompact
  have hno : OnePoint.infty ∉ C := by
    have hi : M.projection OnePoint.infty = OnePoint.infty := by
      simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z (hz.trans hi)
  obtain ⟨K, hK⟩ := (hC.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)).isBounded.exists_norm_le
  exact ⟨max K 0, le_max_right _ _, fun p hp => (hK _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)⟩

 theorem function_bounded_on_source_ball (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 R → ‖M.function z‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := M.projection_bounded_lifts hinf (isCompact_closedBall (0 : ℂ) R)
  refine ⟨K, hK, fun z hzG hz => ?_⟩
  have hp : M.projection ((M.function z : ℂ) : Sphere) ∈
      ((↑) : ℂ → Sphere) '' closedBall 0 R := by
    have hi := M.projection_inverse (z : Sphere) hzG
    simp only [extendAtInfinity_coe] at hi
    rw [hi]
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  simpa only [finiteCoord_coe] using hb (M.function z : Sphere) hp

 theorem derivative_energy_on_source_ball (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    Integrable (fun z => ‖deriv M.function z‖^2)
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G} ∩ ball 0 R
  have hU : IsOpen U := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  obtain ⟨K, _, hK⟩ := M.function_bounded_on_source_ball hinf R
  have hsub : M.function '' U ⊆ closedBall 0 K := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hK z hz.1 hz.2
  apply integrable_norm_deriv_sq_of_image_area_finite hU.measurableSet
    (fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1))
    (fun z hz w hw he => ?_)
    (((isBounded_closedBall (x := (0 : ℂ)) (r := K)).subset hsub).measure_lt_top.ne)
  apply OnePoint.coe_injective
  apply M.conformal.bijOn.injOn hz.1 hw.1
  simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source horizontal section is smooth off the dust and has
finite differential energy on each bounded source region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem source_coordinate_memLp (M : CompactScalarModel G u) (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fderiv ℝ (fun z => (M.function z).re)) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) ∧
    MemLp (fderiv ℝ (fun z => (M.function z).im)) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  exact holomorphic_coordinate_memLp hD (hD.inter isOpen_ball).measurableSet inter_subset_left
    (fun z hz => (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt)
    (M.derivative_energy_on_source_ball hG hinf R)

 theorem horizontalSection_plane_memLp (M : CompactScalarModel G u) (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fderiv ℝ (fun z : ℂ => M.horizontalSection (z : Sphere))) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  apply (M.source_coordinate_memLp hG hinf R).1.ae_eq
  filter_upwards [ae_restrict_mem (hD.inter isOpen_ball).measurableSet] with z hz
  have he : (fun w : ℂ => M.horizontalSection (w : Sphere)) =ᶠ[𝓝 z]
      (fun w => (M.function w).re) := by
    filter_upwards [hD.mem_nhds hz.1] with w hw
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hw
  exact he.fderiv_eq.symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelFlattenedSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous selection of the actual old-test flattenings, height
flattening, and small-support horizontal priority coordinate. All fields
are constructed from the existing model and the stated energy budgets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 structure FlattenedSourceSelection (M : CompactScalarModel G u) {R d : ℝ}
    (H : ControlledHeight R d)
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (A L δ ε : ℝ) where
  oldValues : Fin m → Set ℝ
  old_open : ∀ i, IsOpen (oldValues i)
  oldWitness : ∀ i, DeGiorgi.MemW1pWitness 2 (flattenValues (oldValues i) ∘ u i) (physicalPlaneDomain G)
  old_close : ∀ i t, |flattenValues (oldValues i) t-t| < δ
  old_error : ∀ i, (∫⁻ x in physicalPlaneDomain G,
    ENNReal.ofReal (‖(oldWitness i).weakGrad x-(W i).weakGrad x‖^2)) < ENNReal.ofReal ε
  heightValues : Set ℝ
  height_open : IsOpen heightValues
  heightWitness : DeGiorgi.MemW1pWitness 2
    (flattenValues heightValues ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A)
  height_close : ∀ t, |flattenValues heightValues t-t| < δ
  height_error : (∫⁻ x in ball 0 A,
    ENNReal.ofReal (‖heightWitness.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε
  center : ℕ → ℂ
  center_outside : ∀ n, (center n : Sphere) ∉ G
  target : ℕ → Sphere
  target_projection : ∀ n, M.projection (target n) = (center n : Sphere)
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_tendsto : Tendsto radius atTop (𝓝 0)
  cutoff : ℕ → ℂ → ℝ
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (cutoff n)
  cutoff_support : ∀ n, support (cutoff n) ⊆ ball (center n) (radius n)
  cutoff_unit : ∀ n z, cutoff n z ∈ Icc (0 : ℝ) 1
  value : ℕ → ℝ
  value_eq : ∀ n, value n = (finiteCoord (target n)).re
  priority_continuous : Continuous (fun z : ℂ => priorityInfiniteValue
    (fun n => cutoff n z) value (M.horizontalSection (z : Sphere)))
  priority_error_memLp : MemLp (fun z : ℂ => fderiv ℝ
    (fun w : ℂ => priorityInfiniteValue (fun n => cutoff n w) value (M.horizontalSection (w : Sphere))) z-
    fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))
  priority_error : (eLpNorm (fun z : ℂ => fderiv ℝ
    (fun w : ℂ => priorityInfiniteValue (fun n => cutoff n w) value (M.horizontalSection (w : Sphere))) z-
    fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))).toReal < ε
  support_error : (eLpNorm ((⋃ n, support (cutoff n)).indicator
    (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖))
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))).toReal < ε
  old_constant : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (cutoff n),
    flattenValues (oldValues i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a
  height_constant : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (cutoff n),
    flattenValues heightValues (M.heightSection H (z : Sphere)) = a

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained Jordan curve separates the two sides of an open connected
sphere domain. This applies to the actual finite models without extending
the model map across any terminal disk. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inversion_preimage_unitDisk :
    CannonMobius.inversion ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ := by
  ext p
  change CannonMobius.inv p ∈ ((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1 ↔ _
  cases p using OnePoint.rec with
  | infty => simp [CannonMobius.inv_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [CannonMobius.inv_zero]
    · have he : CannonMobius.inv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by
        simp [CannonMobius.inv, hz]
      rw [he]
      simpa only [OnePoint.coe_injective.mem_set_image, mem_ball, dist_zero_right,
        mem_compl_iff, mem_closedBall, not_le, norm_inv] using
        (inv_lt_one₀ (norm_pos_iff.mpr hz))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompactBarrierData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact global barriers surrounding a fixed compact set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure CompactBarrierData (K : Set EuclideanPlane) (L η : ℝ) where
  region : Set EuclideanPlane
  open_region : IsOpen region
  compact_closure : IsCompact (closure region)
  contains : K ⊆ closure region
  value : EuclideanPlane → ℝ
  witness : DeGiorgi.MemW1pWitness 2 value univ
  continuous : Continuous value
  support : tsupport value ⊆ ball 0 L
  one : ∀ x ∈ frontier region, value x = 1
  energy : (∫ x, ‖witness.weakGrad x‖^2) < η^2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConstrainedCostCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite coding-measure family with a prescribed null
residual-image constraint, as a standard Borel space of codes. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

abbrev ConstrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) :=
  {Γ : FiniteCostCode d p c // ν (residualImage d.dust Γ.val.val) = 0}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModelPairBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact target barrier is built from two continued model
coordinates. Its gradient vanishes almost everywhere on every model hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def pairBarrier (M : CompactScalarModel G u) (i j : Fin m)
    (Φ θ : EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  θ x*Φ (planePair (sphereFromPlaneFunction (u i) (M.projection (planeSphere x)))
    (sphereFromPlaneFunction (u j) (M.projection (planeSphere x))))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteJordanModelInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CircleDomainRigidity
open Set Function
open FiniteTransfer

/-- Only the finite Jordan models, including their actual sphere chart
changes, are needed by the downstream construction. -/
def FiniteJordanModelUniformization : Prop :=
  ∀ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ),
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) →
    ∀ e : Sphere ≃ₜ Sphere, ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f (e '' openCompletedRegion H) V

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TerminalTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual terminal oscillations after smooth filling

The fillings leave terminal boundaries unchanged. Since these boundaries
lie in the one-plateau of the cutoff, their transferred coordinates are
exactly the selected staircases. The original pointwise oscillation bound
therefore gives the required square-sum bound for the actual boundary
diameters, rather than for separately supplied numbers.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def terminalOscillation (T : ℂ ≃ₜ ℂ) (f : (ℝ × ℝ) → ℝ) : ℝ :=
  Metric.diam (f '' frontier (realJordanInterior T))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealTransferStage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Data retained from one actual real finite transfer

This record keeps the geometric and analytic outputs needed by the
countable model sequence. Its existence is proved by the assembled
construction, with the same explicit published inputs.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RealTransferStage {S : Type*} {n : ℕ}
    (G : Set Sphere) (π : Sphere → Sphere) (σ : S → Sphere)
    (u : Fin n → (ℝ × ℝ) → ℝ) (a b : Fin n → S → ℝ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε : ℝ) where
  indices : Set S
  finite_indices : indices.Finite
  flags : Flag ⊆ indices
  terminals : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : indices => σ s) (fun s => O s)
  core : Set (ℝ × ℝ)
  core_closed : IsClosed core
  core_contains : K₀ ⊆ interior core
  core_source : core ⊆ realChartDomain G
  core_cocompact : IsCompact (closure coreᶜ)
  core_model : sphericalCore core ⊆ openCompletedRegion terminals.H
  functions : Fin n → (ℝ × ℝ) → ℝ
  extension : Set (ℝ × ℝ)
  extension_open : IsOpen extension
  extension_contains : realChartDomain (completedRegion terminals.H) ⊆ extension
  functions_smooth : ∀ l, ContDiffOn ℝ ∞ (functions l) extension
  retained : ∀ᶠ z in 𝓝ˢ core, ∀ l, functions l z = u l z
  radius : ℝ
  radius_pos : 0 < radius
  metric : (ℝ × ℝ) → PlanarMetric
  metric_smooth : ContDiff ℝ ∞ metric
  metric_pos : ∀ z, (metric z).PosDef
  metric_core : ∀ᶠ z in 𝓝ˢ core, metric z = sphericalMetricFactor z • 1
  metric_far : ∀ z ∉ Metric.closedBall 0 radius, metric z = sphericalMetricFactor z • 1
  source_energy : ∀ l (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ core →
    (∫ z in realChartDomain (completedRegion terminals.H) \ E, gradientEnergy (functions l) metric z) <
      (∫ z in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) z) + ε
  excess : ∀ l, Real.sqrt (∑' s : indices,
    max (terminalOscillation (terminals.H s) (functions l) - (b l s - a l s)) 0 ^ 2) < ε
  oscillation : ∀ l, Real.sqrt (∑' s : indices, terminalOscillation (terminals.H s) (functions l) ^ 2) <
    Real.sqrt (∑' s : S, (b l s - a l s) ^ 2) + ε
  domain : Set Sphere
  forward : Sphere → Sphere
  inverse : Sphere → Sphere
  circle_domain : IsCircleDomain domain
  equivalence : IsSmoothSphereEquivalence forward inverse (openCompletedRegion terminals.H) domain
  conformal_core : IsConformalOn forward (sphericalCore core)
  principal : IsPrincipalNormalized forward
  metric_conformal : ∀ p ∈ openCompletedRegion terminals.H, IsMetricConformalAt metric forward p
  integrable : ∀ l, IntegrableOn (gradientEnergy (functions l) metric)
    (realChartDomain (completedRegion terminals.H))
  transported_smooth : ∀ l, ContDiffOn ℝ ∞ (functions l ∘ sphereRealMap inverse) (realChartDomain domain)

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

theorem source_infty : OnePoint.infty ∈ openCompletedRegion M.terminals.H :=
  M.core_model (infty_mem_sphericalCore M.core)

theorem prescribed_core_model : sphericalCore K₀ ⊆ openCompletedRegion M.terminals.H :=
  (sphericalCore_mono (M.core_contains.trans interior_subset)).trans M.core_model

end RealTransferStage

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CountableRealTransfer
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure CountableRealCoordinates {S : Type*}
    (G : Set Sphere) (π : Sphere → Sphere) (σ : S → Sphere) where
  source : Set Sphere
  source_open : IsOpen source
  coordinate : ℕ → Sphere → ℝ
  coordinate_continuous : ∀ l, ContinuousOn (coordinate l) source
  bound : ℕ → ℝ
  coordinate_bounded : ∀ l x, x ∈ source → |coordinate l x| ≤ bound l
  physical : ℕ → (ℝ × ℝ) → ℝ
  physical_measurable : ∀ l, Measurable (physical l)
  physical_smooth : ∀ l, ContDiffOn ℝ ∞ (physical l) (realChartDomain G)
  physical_energy : ∀ l, MemLp (planarGradient (physical l)) 2 (volume.restrict (realChartDomain G))
  source_map : ∀ z : ℂ, (z : Sphere) ∈ G → π z ∈ source
  pullback : ∀ l (z : ℂ), (z : Sphere) ∈ G → physical l (Complex.equivRealProdCLM z) = coordinate l (π z)
  labels_injective : Injective σ
  labels_dust : ∀ s, σ s ∈ π '' Gᶜ
  labels_closure : ∀ s, σ s ∈ closure source
  lower : ℕ → S → ℝ
  upper : ℕ → S → ℝ
  width_nonneg : ∀ l s, 0 ≤ upper l s - lower l s
  width_summable : ∀ l, Summable (fun s => (upper l s - lower l s) ^ 2)
  band : ∀ l s, {t : ℝ | (σ s, t) ∈ intervalFiberHull (clusterGraph source (coordinate l))} =
    Icc (lower l s) (upper l s)
  free_trace : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
    ∃ v : ℝ, {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph source (coordinate l))} = {v}

abbrev CountableRealCoordinates.Stage {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (n : ℕ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε : ℝ) :=
  RealTransferStage G π σ (fun l : Fin (n + 1) => d.physical l)
    (fun l => d.lower l) (fun l => d.upper l) Flag O K₀ ε

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

structure RealModelExhaustion {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (O : ℕ → S → Set Sphere) (ε : ℕ → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  plane : ℕ → Set ℂ
  plane_open : ∀ n, IsOpen (plane n)
  plane_connected : ∀ n, IsConnected (plane n)
  plane_monotone : Monotone plane
  cores : ℕ → Set Sphere
  core_compact : ∀ n, IsCompact (cores n)
  core_source : ∀ n, cores n ⊆ G
  plane_core : ∀ n, ((↑) : ℂ → Sphere) '' plane n ∪ {OnePoint.infty} ⊆ cores n
  exhausts : ((↑) : ℂ → Sphere) '' (⋃ n, plane n) ∪ {OnePoint.infty} = G
  exterior_core : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 radius)ᶜ) ⊆ cores n
  exterior_plane : {z : ℂ | 2 * radius ≤ ‖z‖} ⊆ plane 0
  flags : ℕ → Set S
  flags_finite : ∀ n, (flags n).Finite
  flags_monotone : Monotone flags
  stages : ∀ n, d.Stage n (flags n) (O n) (realChartDomain (cores n)) (ε n)
  indices_nonempty : ∀ n, Nonempty S → (stages n).indices.Nonempty
  marks : ∀ s, ∀ᶠ n in atTop, s ∈ (stages n).indices

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem core_model (n : ℕ) : M.cores n ⊆ openCompletedRegion (M.stages n).terminals.H := by
  intro p hp
  apply (M.stages n).prescribed_core_model
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
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactCoreRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Every fixed compact core is eventually retained

The plane domains exhaust the source, and every finite model contains a
fixed neighborhood of infinity. These two facts give eventual retention
of any compact sphere core; no extra exhaustion hypothesis is required.
-/

open Set Function Filter Metric
open scoped Topology

namespace CircleDomainRigidity

theorem eventually_compact_subset_model
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {Q : ℕ → Set Sphere} (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    {R : ℝ} (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ Q n)
    {K : Set Sphere} (hK : IsCompact K)
    (hKG : K ⊆ ((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty}) :
    ∀ᶠ n in atTop, K ⊆ Q n := by
  let S : Set ℂ := (((↑) : ℂ → Sphere) ⁻¹' K) ∩ closedBall 0 R
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) R).inter_left
    (hK.isClosed.preimage OnePoint.continuous_coe)
  have hSD : S ⊆ ⋃ n, D n := by
    intro z hz
    rcases hKG hz.1 with hzD | hzi
    · exact OnePoint.coe_injective.mem_set_image.mp hzD
    · exact (OnePoint.coe_ne_infty z hzi).elim
  obtain ⟨m, hm⟩ := hS.elim_directed_cover D hD hSD hmono.directed_le
  filter_upwards [eventually_ge_atTop m] with n hn
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact hsource n (by simp)
  | coe z =>
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · exact hDQ n z (hmono hn (hm ⟨hx, hz⟩))
    · apply hsource n
      rintro ⟨w, hw, he⟩
      have hwz : w = z := OnePoint.coe_injective he
      exact hz (hwz ▸ ball_subset_closedBall hw)

end CircleDomainRigidity

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

theorem eventually_core_contains {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) :
    ∀ᶠ n in atTop, K ⊆ M.cores n := by
  apply eventually_compact_subset_model M.plane_open M.plane_monotone
    (fun n z hz => M.plane_core n (Or.inl ⟨z, hz, rfl⟩)) M.exterior_core hK
  rwa [M.exhausts]

theorem eventually_model_contains {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) :
    ∀ᶠ n in atTop, K ⊆ openCompletedRegion (M.stages n).terminals.H :=
  (M.eventually_core_contains hK hKG).mono (fun n hn => hn.trans (M.core_model n))

end CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealMarkedModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign the actual countable real-model terminals to their original source ends. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def CountableRealCoordinates.sourceMark {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (s : S) : Sphere :=
  Classical.choose (d.labels_dust s)

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

def markIndex (n : ℕ) (s : S) : (M.stages n).indices := by
  classical
  exact if h : s ∈ (M.stages n).indices then ⟨s, h⟩
  else ⟨Classical.choose (M.indices_nonempty n ⟨s⟩),
    Classical.choose_spec (M.indices_nonempty n ⟨s⟩)⟩

end RealModelExhaustion

structure AssignedRealModelLimit {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} (M : RealModelExhaustion d O ε) where
  assignment : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
    (M.stages n).forward (M.stages n).domain
  subsequence : ℕ → ℕ
  function : ℂ → ℂ
  center : S → ℂ
  radius : S → ℝ
  cores : ℕ → SmoothJordanCore G
  contours : ∀ j, Fin (cores j).count → ℂ ≃ₜ ℂ
  strict : StrictMono subsequence
  converges : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
    finiteCoord ((M.stages (subsequence n)).forward (z : Sphere))) function
    atTop (((↑) : ℂ → Sphere) ⁻¹' G)
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  bounds : ∀ s, ‖center s‖ ≤ 3 * M.radius ∧ radius s ∈ Icc 0 (3 * M.radius)
  nested : ∀ j, (cores j).carrier ⊆ interior (cores (j + 1)).carrier
  exhausts : (⋃ j, interior (cores j).carrier) = G
  boundary : ∀ j i, extendAtInfinity function ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores j).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (contours j i))
  disjoint : ∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (contours j i)))
  image_core : ∀ j, (extendAtInfinity function '' (cores j).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (contours j i)
  side : ∀ j i, extendAtInfinity function ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores j).disk i))) =
    (extendAtInfinity function '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (contours j i))
  marked : ∀ s, ∃ (index : ∀ j, Fin (cores j).count) (p : Sphere),
    p ∈ (extendAtInfinity function '' G)ᶜ ∧
    connectedComponentIn Gᶜ (d.sourceMark s) = ⋂ j, closedTerminalCap ((cores j).disk (index j)) ∧
    connectedComponentIn (extendAtInfinity function '' G)ᶜ p =
      ⋂ j, closedTerminalCap (contours j (index j)) ∧
    ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s) ⊆
      connectedComponentIn (extendAtInfinity function '' G)ᶜ p ∧
    Tendsto (fun n => hausdorffDist
      (finiteCoord '' connectedComponentIn (M.stages (subsequence n)).domainᶜ
        ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)))
      (closedBall (center s) (radius s))) atTop (𝓝 0)

end CircleDomainRigidity.FiniteTransfer

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

structure RealTargetEnd {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    (L : AssignedRealModelLimit M) (q : Sphere) where
  address : ∀ n, Fin (L.cores n).count
  point : Sphere
  outside : point ∈ (extendAtInfinity L.function '' G)ᶜ
  source : connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((L.cores n).disk (address n))
  target : connectedComponentIn (extendAtInfinity L.function '' G)ᶜ point =
    ⋂ n, closedTerminalCap (L.contours n (address n))
  nested : ∀ n, closedTerminalCap (L.contours (n + 1) (address (n + 1))) ⊆
    ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (address n))

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

def plane : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
  connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealSourceBarriers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local plateaus of the original quotient tests collapse their corresponding full ends. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem source_cap_antitone :
    Antitone (fun n => closedTerminalCap ((L.cores n).disk (E.address n))) := by
  apply antitone_nat_of_succ_le
  intro n
  have hs := (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
    ((L.cores n).disk (E.address n)) ((L.cores (n + 1)).disk (E.address (n + 1)))
    (L.contours n (E.address n)) (L.contours (n + 1) (E.address (n + 1)))
    ((L.cores (n + 1)).boundary_subset_domain (E.address (n + 1)))
    (L.boundary (n + 1) (E.address (n + 1))) (L.side n (E.address n))).mpr (E.nested n)
  exact hs.trans (image_mono subset_closure)

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SavedBarrierMargins
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict plateau and zero margins for the saved source barriers.
Uniformly small coordinate changes preserve the exact barrier values. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem saved_barrier_one_on_neighborhood
    (A : ℂ → EuclideanPlane) (hA : Continuous A) (c : EuclideanPlane)
    (Φ : EuclideanPlane → ℝ) (K : Set ℂ) {r : ℝ} (hr : 0 < r)
    (hplateau : ∀ y, ‖y‖ ≤ r → Φ y = 1)
    (hK : ∀ x ∈ K, ‖A x-c‖ ≤ r/2) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧
      ∀ A' : ℂ → EuclideanPlane, (∀ x ∈ V, ‖A' x-A x‖ < r/4) →
        ∀ x ∈ V, Φ (A' x-c) = 1 := by
  let V := {x : ℂ | ‖A x-c‖ < 3*r/4}
  refine ⟨V,isOpen_lt ((hA.sub continuous_const).norm) continuous_const,?_,?_⟩
  · intro x hx
    have := hK x hx
    change ‖A x-c‖ < 3*r/4
    linarith
  · intro A' hchange x hx
    apply hplateau
    have ht : ‖A' x-c‖ ≤ ‖A' x-A x‖+‖A x-c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (A' x-A x) (A x-c)
    change ‖A x-c‖ < 3*r/4 at hx
    linarith [hchange x hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathSelectionInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published input for the compact-arc reduction: Kechris, Classical
Descriptive Set Theory (1995), Theorem 18.1, p.120, and Theorem 29.9,
p.227. We use only Borel relations between sphere path spaces with all
sections nonempty, and measurability after completing one probability law. -/

open Set MeasureTheory
open scoped Topology

namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def BorelPathRelationSelection : Prop :=
  ∀ (μ : ProbabilityMeasure C(PathTime, Sphere))
    (R : Set (C(PathTime, Sphere) × C(PathTime, Sphere))),
    MeasurableSet R → (∀ γ, ∃ α, (γ, α) ∈ R) →
    ∃ f : C(PathTime, Sphere) → C(PathTime, Sphere),
      NullMeasurable f (μ : Measure C(PathTime, Sphere)) ∧ ∀ γ, (γ, f γ) ∈ R

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalArcSet
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint and interior conditions of the compact arc reduction form
a Borel set. Consequently a full law of these arcs has a compact core. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_4_r006e07_1 : BorelSpace Sphere := ⟨rfl⟩
def terminalArcSet (V : Set Sphere) (b : Sphere) : Set C(PathTime, Sphere) :=
  {α | Injective α ∧ α ⊥ ∈ frontier V ∧ α ⊤ = b ∧
    MapsTo α (Ioo ⊥ ⊤) V}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactArcLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning the terminal-arc law on a compact family of mass greater
than one half loses at most a factor two in every measure bound. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_5 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredArcLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the constructed terminal arc law to centered disk coordinates.
The coordinate extension is only evaluated on the closed collar. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

def diskTerminalArcSet : Set C(PathTime, ℂ) :=
  {γ | Injective γ ∧ ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧
    ∀ t ∈ Ioo (0 : PathTime) 1, ‖γ t‖ < 1}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel physical occupation on ordinary path space, with zero extension
off the finite-length paths. This lets measurable arc selection act directly
on path laws without introducing a new code law. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

def physicalOccupationCode (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) : Measure Y :=
  if h : physicalDomainLength e y₀ γ < ∞ then dyadicPhysicalOccupation e y₀ ⟨γ, h⟩ else 0

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

def meanPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) : Measure Y :=
  (μ : Measure C(PathTime, X)).bind (physicalOccupationCode e y₀)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcIntersectionCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct intersections decrease under subarc selection. Conditioning
on a compact family of mass at least one half costs at most a factor two. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

/-- The actual measurable selection and domination data retained by compact
terminal subarc conditioning. -/
def IsSubarcLawReduction
    (μ η : ProbabilityMeasure C(PathTime, X)) : Prop :=
  ∃ f : C(PathTime, X) → C(PathTime, X),
    ∃ hf : AEMeasurable f (μ : Measure C(PathTime, X)),
    (∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ) ∧
    (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map (f := f) hf : Measure C(PathTime, X))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredTerminalLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete centered disk data of a compact terminal-arc family. All
injectivity and unit bounds hold on the actual punctured Jordan interior. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

structure CenteredTerminalFamily (J : ℂ ≃ₜ ℂ) (b : Sphere)
    (A : Set C(PathTime, Sphere)) where
  map : C(Sphere, ℂ)
  map_eq : EqOn map (centeredJordanCoordinate J b)
    (closure (((↑) : ℂ → Sphere) '' jordanInterior J))
  diskArcs : Set C(PathTime, ℂ)
  compact : IsCompact diskArcs
  terminal : diskArcs ⊆ diskTerminalArcSet
  arcMap : A → diskArcs
  continuous_arcMap : Continuous arcMap
  arcMap_eq : ∀ γ : A, (arcMap γ).val = map.comp γ.val

namespace CenteredTerminalFamily
variable {J : ℂ ≃ₜ ℂ} {b : Sphere} {A : Set C(PathTime, Sphere)}
    (P : CenteredTerminalFamily J b A)
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)

 def punctured (_P : CenteredTerminalFamily J b A) : Set Sphere := (((↑) : ℂ → Sphere) '' jordanInterior J) \ {b}

end CenteredTerminalFamily
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative family of code laws used in dust fusion is Borel and
closed under arbitrary Borel probability mixtures. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]


def codeVisitWeight (d : PathCodeData X Y) (a : S → X) (s : S) (Γ : BasePathCode d) : ℝ≥0∞ :=
  visitCount (codePath d Γ) (a s)

def CodeLawCandidate (d : PathCodeData X Y) (a : S → X) (μ : Measure Y)
    (τ : Measure LevelTuple) (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Prop :=
  BoundedDensityBudget μ (meanCodeOccupation d P) massOcc energy ∧
    CountableSquareLawBounds (codeVisitWeight d a) visitBudget P ∧
    BoundedDensityBudget τ (meanCodeTuple d P) massTuple energy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DiskStartLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomlessness and the boundary measure for the actual disk arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskTerminalArc_norm_le {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet)
    (t : PathTime) : ‖γ t‖ ≤ 1 := by
  by_cases h0 : t = 0
  · simpa only [h0, hγ.2.1] using (le_refl (1 : ℝ))
  by_cases h1 : t = 1
  · simp only [h1, hγ.2.2.1, norm_zero, zero_le_one]
  exact (hγ.2.2.2 t ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm h0),
    lt_of_le_of_ne (unitInterval.le_one t) h1⟩).le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
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

def pathHitProbability (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) : ℝ≥0∞ :=
  CircleDomainRigidity.pathHitProbability μ (ι x)

def pathHitReal (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) : ℝ :=
  (pathHitProbability ι μ x).toReal

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedFusionSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
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

def PassesHitTests (C : ℝ) (μ : ProbabilityMeasure C(PathTime, Y))
    (D : Set X) (ν : Measure X) : Prop :=
  (∀ F : Finset X, (↑F : Set X) ⊆ D → ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ C ^ 2) ∧
    ∫⁻ x, pathHitProbability ι μ x ∂ν = 0

/-- A candidate family is small when one countable set and one finite atomless
test measure rule out every member. This is the manuscript's small-set ideal. -/
def HitTestSmall (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ) (A : Set Z) : Prop :=
  ∃ D : Set X, D.Countable ∧ ∃ ν : Measure X, IsFiniteMeasure ν ∧
    NullSingletonClass ν ∧ ∀ z ∈ A, ¬PassesHitTests ι C (law z) D ν

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedConfigurations
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureMeanConfigurationMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
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

def weightedConfigurationHits (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) : ℝ :=
  ∑ i, (p.val.2 i : ℝ) * pathHitReal ι (law z) (p.val.1 i)

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionTree
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero
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

structure ClosedHitCandidate where
  carrier : Set Z
  closed : IsClosed carrier
  nonsmall : ¬HitTestSmall ι law C carrier

structure HitFusionSplit (A : ClosedHitCandidate ι law C) (n : ℕ) (r ε η : ℝ) where
  count : ℕ
  count_pos : 0 < count
  weight : Fin count → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : (∑ i, weight i) = 1
  child : Fin count → ClosedHitCandidate ι law C
  child_subset : ∀ i, (child i).carrier ⊆ A.carrier
  child_dist : ∀ i, ∀ x ∈ (child i).carrier, ∀ y ∈ (child i).carrier, dist x y ≤ η
  bound : ∀ z : Fin count → Z, (∀ i, z i ∈ (child i).carrier) →
    ∀ p : HitConfiguration X n r,
      ∑ i, weight i * weightedConfigurationHits ι law (z i) p < C + ε

variable {law C}

namespace HitFusionSplit

variable {ι}

variable {A : ClosedHitCandidate ι law C} {n : ℕ} {r ε η : ℝ}

/-- All natural-number addresses are valid; only the first `count` receive mass. -/
def index (S : HitFusionSplit ι law C A n r ε η) (a : ℕ) : Fin S.count :=
  ⟨a % S.count, Nat.mod_lt a S.count_pos⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
@[simp] theorem index_val (S : HitFusionSplit ι law C A n r ε η) (i : Fin S.count) :
    S.index i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

end HitFusionSplit

variable (ns : ℕ → ℕ) (rs : ℕ → ℝ) (ε : ℝ)
  (split : ∀ d (A : ClosedHitCandidate ι law C),
    HitFusionSplit ι law C A (ns d) (rs d) ε (1 / ((d : ℝ) + 1)))
  (root : ClosedHitCandidate ι law C)

def hitFusionNode : List ℕ → ClosedHitCandidate ι law C
  | [] => root
  | a :: l => (split l.length (hitFusionNode l)).child
      ((split l.length (hitFusionNode l)).index a)

/-- The data generated by the proved finite splitting construction. -/
structure HitFusionData where
  sizes : ℕ → ℕ
  separations : ℕ → ℝ
  error : ℝ
  initial : ClosedHitCandidate ι law C
  split : ∀ d (A : ClosedHitCandidate ι law C),
    HitFusionSplit ι law C A (sizes d) (separations d) error (1 / ((d : ℝ) + 1))

namespace HitFusionData

variable {ι}

variable (T : HitFusionData (ι := ι) (law := law) (C := C))

def node (l : List ℕ) : ClosedHitCandidate ι law C :=
  hitFusionNode ι T.sizes T.separations T.error T.split T.initial l

def splitAt (l : List ℕ) := T.split l.length (T.node l)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
@[simp] theorem node_cons (a : ℕ) (l : List ℕ) :
    T.node (a :: l) = (T.splitAt l).child ((T.splitAt l).index a) := rfl

end HitFusionData

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DustPriorContacts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prior constraints only charge residual times in the dust. Consequently
their finite-toll argument only needs visit bounds at dust marks; a possible
atom at the image of infinity does not impose an extra path constraint. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

def dustPriorHitMass {X : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (B : Set X) (μ : Measure C(PathTime, X)) : X → ℝ≥0∞ :=
  fun x => if x ∈ B then priorHitMass μ x else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PriorLawPresentation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable data attached to a recursion stage: every earlier law is
retained, its hit support has finite deletions, and every required dust mark
is among the marks prescribed to the next positive-law construction. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

structure PriorLawPresentation (B S : Set X) (μ : ℕ → Measure C(PathTime, X)) where
  marks : Set X
  marks_countable : marks.Countable
  marks_dust : marks ⊆ B
  extra_marks : S ⊆ marks
  prior_marks : ∀ i, support (dustPriorHitMass B (μ i)) ⊆ marks
  priorDeletions : ℕ → ℕ → Finset X
  prior_monotone : ∀ i, Monotone (priorDeletions i)
  prior_subset : ∀ i n, (priorDeletions i n : Set X) ⊆ support (priorHitMass (μ i))
  prior_cover : ∀ i x, x ∈ support (priorHitMass (μ i)) →
    ∀ᶠ n in atTop, x ∈ priorDeletions i n
  flagDeletions : ℕ → Finset X
  flag_monotone : Monotone flagDeletions
  flag_subset : ∀ n, (flagDeletions n : Set X) ⊆ S
  flag_cover : ∀ x ∈ S, ∀ᶠ n in atTop, x ∈ flagDeletions n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure RecursiveCodeGeometry (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) where
  data : PathCodeData Sphere Sphere
  physical_eq : data.physicalDomain = base.physicalDomain
  quotient_eq : data.quotientDomain = base.quotientDomain
  dust_eq : data.dust = base.dust
  anchor_eq : data.anchor = base.anchor
  levels_eq : data.levels = base.levels
  weights_eq : data.levelWeights = base.levelWeights
  domain_agrees : ∀ y : data.physicalDomain, (data.domainEquiv y).val = π y.val
  target_dust : data.target ∈ base.dust
  presentation : PriorLawPresentation base.dust flags data.priorLaws
  prior_deletions_eq : data.priorDeletions = presentation.priorDeletions
  flag_deletions_eq : data.flagDeletions = presentation.flagDeletions

local instance localInst_r006e07_1 : BorelSpace Sphere := ⟨rfl⟩
def RecursiveLawWitness (d : PathCodeData Sphere Sphere) (marks : Set Sphere)
    (ω : TupleType → ℝ≥0∞) :=
  Σ budgets : RecursiveLawBudgets, {law : ProbabilityMeasure (BasePathCode d) //
    CodeLawCandidate d (fun x : marks => x.val) sphericalArea (tupleReference ω)
      budgets.occupationMass budgets.tupleMass budgets.energy (budgets.visitConstant ^ 2) law ∧
    ∃ hitConstant : ℝ,
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d law) x.val ^ 2 ≤ hitConstant ^ 2) ∧
      {x | x ∈ d.dust ∧ 0 < codeHitProbability d law x}.Countable}

namespace RecursiveLawWitness
variable {d : PathCodeData Sphere Sphere} {marks : Set Sphere}
  {ω : TupleType → ℝ≥0∞} (W : RecursiveLawWitness d marks ω)
local instance localInst_r006e07_2 : BorelSpace Sphere := ⟨rfl⟩
abbrev budgets := W.1
abbrev law := W.2.val
end RecursiveLawWitness

def RecursiveCodeLaw (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) (ω : TupleType → ℝ≥0∞) :=
  Σ geometry : RecursiveCodeGeometry base π flags,
    RecursiveLawWitness geometry.data geometry.presentation.marks ω

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

abbrev geometry := L.1
abbrev witness := L.2
abbrev data := L.geometry.data
abbrev law := L.witness.law

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceAnchor
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A target-domain point has a compact source Jordan anchor whose image contains a target ball
inside any prescribed open neighborhood. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem roundJordanAt_interior (c : ℂ) (r : ℝ) (hr : 0 < r) :
    jordanInterior (roundJordanAt c r hr) = ball c r := by
  rw [roundJordanAt, jordanInterior_dilated _ hr]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm]
    change ‖(w + c) - c‖ < r
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
  · intro hz
    refine ⟨z - c, ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
    · simp

theorem roundJordanAt_closure (c : ℂ) (r : ℝ) (hr : 0 < r) :
    closure (jordanInterior (roundJordanAt c r hr)) = closedBall c r := by
  rw [roundJordanAt_interior, closure_ball _ hr.ne']

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteLiftConformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lifting a holomorphic plane injection to the finite sphere charts. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma conformalEquivalence_finiteLift {U V : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) :
    IsConformalEquivalence (extendAtInfinity f)
      (((↑) : ℂ → Sphere) '' U) (((↑) : ℂ → Sphere) '' V) := by
  have hconf : IsConformalOn (extendAtInfinity f) (((↑) : ℂ → Sphere) '' U) := by
    rintro _ ⟨z,hz,rfl⟩
    exact isConformalAt_extendAtInfinity_coe
      ((hf z hz).differentiableAt (hU.mem_nhds hz))
      (holomorphicInjOn_deriv_ne_zero hU hf hbij.injOn hz)
  have hi : InjOn (extendAtInfinity f) (((↑) : ℂ → Sphere) '' U) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
    have hxy : f x=f y := OnePoint.coe_injective he
    exact congrArg ((↑) : ℂ → Sphere) (hbij.injOn hx hy hxy)
  have himage : extendAtInfinity f '' (((↑) : ℂ → Sphere) '' U) =
      ((↑) : ℂ → Sphere) '' V := by
    calc
      _ = ((↑) : ℂ → Sphere) '' (f '' U) := by
        rw [image_image,image_image]
        rfl
      _ = _ := by rw [hbij.image_eq]
  simpa only [himage] using isConformalEquivalence_of_injOn hconf
    (OnePoint.isOpen_image_coe.mpr hU) hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanExteriorDiskChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite simply connected chart of a Jordan-hole exterior. It is
normalized at the original point at infinity, which has chart value zero. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma isSimplyConnected_sphere_jordan_exterior (H : ℂ ≃ₜ ℂ) :
    IsSimplyConnected (closedTerminalCap H)ᶜ := by
  let e : Sphere ≃ₜ Sphere := H.onePointCongr.symm.trans CannonMobius.inversion
  have hpre : e ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (closedTerminalCap H)ᶜ := by
    change H.onePointCongr.symm ⁻¹' (CannonMobius.inversion ⁻¹'
      (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)) = _
    rw [inversion_preimage_unitDisk,preimage_compl,← H.onePointCongr.image_eq_preimage_symm]
    congr 1
    simp only [closedTerminalCap,closure_jordanInterior,image_image,
      Homeomorph.onePointCongr_apply,OnePoint.map_some]
  have hball : IsSimplyConnected (ball (0 : ℂ) 1) := by
    let : ContractibleSpace (ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace (nonempty_ball.mpr zero_lt_one)
    change SimplyConnectedSpace (ball (0 : ℂ) 1)
    infer_instance
  rw [← hpre]
  exact e.isSimplyConnected_preimage.mpr
    (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image.mpr hball)

lemma finite_chart_simplyConnected {S : Set Sphere} (hS : IsSimplyConnected S)
    (hi : ∞ ∉ S) : IsSimplyConnected (((↑) : ℂ → Sphere) ⁻¹' S) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image.mp
  rw [image_preimage_eq_of_subset]
  · exact hS
  · intro x hx
    cases x using OnePoint.rec with
    | infty => exact (hi hx).elim
    | coe z => exact ⟨z,rfl⟩

lemma finite_chart_proper_of_complement_nontrivial {S : Set Sphere}
    (hS : Sᶜ.Nontrivial) : ((↑) : ℂ → Sphere) ⁻¹' S ≠ univ := by
  intro he
  have hsub : Sᶜ ⊆ {∞} := by
    intro x hx
    cases x using OnePoint.rec with
    | infty => rfl
    | coe z =>
      have hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' S := he.symm ▸ mem_univ z
      exact (hx hz).elim
  exact hS.not_subsingleton (fun _ hx _ hy => (mem_singleton_iff.mp (hsub hx)).trans (mem_singleton_iff.mp (hsub hy)).symm)

def jordanExteriorPlane (H : ℂ ≃ₜ ℂ) : Set ℂ :=
  ((↑) : ℂ → Sphere) ⁻¹'
    (pointToInfinity ((H 0 : ℂ) : Sphere) '' (closedTerminalCap H)ᶜ)

lemma jordan_exterior_plane_data (H : ℂ ≃ₜ ℂ) :
    IsOpen (jordanExteriorPlane H) ∧ IsSimplyConnected (jordanExteriorPlane H) ∧
      jordanExteriorPlane H ≠ univ ∧ (0 : ℂ) ∈ jordanExteriorPlane H := by
  let N := pointToInfinity ((H 0 : ℂ) : Sphere)
  have hcenter : ((H 0 : ℂ) : Sphere) ∈ closedTerminalCap H := by
    refine ⟨H 0,?_,rfl⟩
    rw [closure_jordanInterior]
    exact ⟨0,by simp,rfl⟩
  have hno : ∞ ∉ N '' (closedTerminalCap H)ᶜ := by
    rintro ⟨p,hp,he⟩
    have heq : p=((H 0 : ℂ) : Sphere) := N.injective
      (he.trans (pointToInfinity_apply_self _).symm)
    exact hp (heq.symm ▸ hcenter)
  have hnon : (N '' (closedTerminalCap H)ᶜ)ᶜ.Nontrivial := by
    rw [← N.image_compl,compl_compl]
    exact (nontrivial_closedTerminalCap H).image N.injective
  refine ⟨(N.isOpenMap _ (isCompact_closedTerminalCap H).isClosed.isOpen_compl).preimage
    OnePoint.continuous_coe, finite_chart_simplyConnected
      (N.isSimplyConnected_image.mpr (isSimplyConnected_sphere_jordan_exterior H)) hno,
    finite_chart_proper_of_complement_nontrivial hnon,?_⟩
  change ((0 : ℂ) : Sphere) ∈ N '' (closedTerminalCap H)ᶜ
  refine ⟨∞,?_,?_⟩
  · rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  · change CannonMobius.inversion (affineSphere 1 (-(H 0)) one_ne_zero ∞) = ((0 : ℂ) : Sphere)
    exact CannonMobius.inv_infty

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MontelProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the precise varying-domain Montel input by cutoff
exhaustion, local Schwarz bounds and compact-open Ascoli extraction. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem montelExhaustion : MontelExhaustion := by
  classical
  intro D F hD hmono hF hbound
  obtain ⟨s,hs,G,heq,he,hb⟩ := exists_montel_continuous_family D F hD hmono hF hbound
  let U := ⋃ n, D n
  have hU : IsOpen U := isOpen_iUnion hD
  let H : ℕ → C(U, ℂ) := fun n => (G n).comp ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨v,t,ht,hv⟩ := locally_uniform_complex_subsequence hU H he hb
  let f : ℂ → ℂ := fun z => if hz : z ∈ U then v ⟨z,hz⟩ else 0
  have hf : (f ∘ ((↑) : U → ℂ)) = v := by
    funext z
    simp only [Function.comp_apply,f,dite_eq_left z.property]
  have hlim : TendstoLocallyUniformlyOn (fun n => G (t n)) f atTop U := by
    apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    rw [hf]
    exact hv
  refine ⟨s ∘ t,f,hs.comp ht,?_⟩
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  have hKlim := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim K hKU hK
  exact hKlim.congr (ht.tendsto_atTop.eventually (heq K hK hKU))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RiemannDiskExtremal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized derivative extremum is attained by an actual univalent
map, using the already proved normal-family and Hurwitz theorems. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_extremal_normalized_disk_embedding {U : Set ℂ}
    (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a ∈ U)
    (hseed : ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0 ∧
      ∀ g : ℂ → ℂ, NormalizedDiskEmbedding U a g → ‖deriv g a‖≤‖deriv f a‖ := by
  let S : Set ℝ := {t | ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ ‖deriv f a‖=t}
  obtain ⟨f₀,h₀,hd₀⟩ := hseed
  have hS : S.Nonempty := ⟨‖deriv f₀ a‖,f₀,h₀,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a ha
  have hbound : BddAbove S := by
    refine ⟨1/r,?_⟩
    rintro t ⟨f,hf,rfl⟩
    exact normalized_disk_derivative_bound hf hr hball
  have hpos : 0 < sSup S := lt_of_lt_of_le (norm_pos_iff.mpr hd₀)
    (le_csSup hbound ⟨f₀,h₀,rfl⟩)
  obtain ⟨u,_hu,hu,huS⟩ := exists_seq_tendsto_sSup hS hbound
  choose F hF hderiv using huS
  obtain ⟨s,f,hs,hlim⟩ := montelExhaustion (fun _ => U) F (fun _ => hU)
    monotone_const (fun n => (hF n).holomorphic) (by
      intro K _hK hKU
      refine ⟨1,?_⟩
      intro n z _hz hzU
      exact (mem_ball_zero_iff.mp ((hF n).mapsTo hzU)).le)
  simp only [iUnion_const] at hlim
  have hhol : DifferentiableOn ℂ f U := hlim.differentiableOn
    (Eventually.of_forall (fun n => (hF (s n)).holomorphic)) hU
  have hderivlim := (hlim.deriv
    (Eventually.of_forall (fun n => (hF (s n)).holomorphic)) hU).tendsto_at ha
  have hext : ‖deriv f a‖=sSup S := by
    apply tendsto_nhds_unique hderivlim.norm
    have hseq : (fun n => ‖deriv (F (s n)) a‖) = u ∘ s := by
      funext n
      exact hderiv (s n)
    change Tendsto (fun n => ‖deriv (F (s n)) a‖) atTop (𝓝 (sSup S))
    rw [hseq]
    exact hu.comp hs.tendsto_atTop
  have hdn : deriv f a ≠ 0 := norm_pos_iff.mp (by rw [hext]; exact hpos)
  have hnotconst : ¬∃ c : ℂ, ∀ z ∈ U, f z=c := by
    rintro ⟨c,hc⟩
    have he : f =ᶠ[𝓝 a] (fun _ => c) := by
      filter_upwards [hU.mem_nhds ha] with z hz
      exact hc z hz
    exact hdn (by rw [he.deriv_eq,deriv_const])
  have hfa : f a=0 := by
    have h := hlim.tendsto_at ha
    have he : (fun n => F (s n) a) = (fun _ => (0:ℂ)) := by
      funext n
      exact (hF (s n)).at_base
    rw [he] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hnorm (z : ℂ) (hz : z ∈ U) : ‖f z‖≤1 := by
    apply le_of_tendsto (hlim.tendsto_at hz).norm
    exact Eventually.of_forall (fun n => (mem_ball_zero_iff.mp ((hF (s n)).mapsTo hz)).le)
  have hmap : MapsTo f U (ball 0 1) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    by_contra hh
    have he : ‖f z‖=1 := le_antisymm (hnorm z hz) (le_of_not_gt hh)
    have hm : IsMaxOn (norm ∘ f) U z := fun w hw => (hnorm w hw).trans he.ge
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      hc.isPreconnected hU hhol hz hm
    have heq := hconst ha
    rw [hfa] at heq
    change (0 : ℂ)=f z at heq
    have hhzero : ‖f z‖=0 := by rw [← heq]; simp
    linarith
  refine ⟨f,⟨hhol,?_,hmap,hfa⟩,hdn,?_⟩
  · exact hurwitzUnivalentLimit U (fun n => F (s n)) f hU hc
      (Eventually.of_forall (fun n => ⟨(hF (s n)).holomorphic,(hF (s n)).injective⟩))
      hlim hnotconst
  · intro g hg
    rw [hext]
    exact le_csSup hbound ⟨g,hg,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RiemannDiskMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The disk map needed for a single circularization step, constructed
from derivative maximization and the omitted-value root improvement. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma exists_normalized_riemann_disk_map {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧
      BijOn f U (ball 0 1) ∧ deriv f a ≠ 0 := by
  obtain ⟨f,hf,hdf,hmax⟩ := exists_extremal_normalized_disk_embedding hU
    hc.isPathConnected.isConnected ha (exists_normalized_disk_embedding hU hc hproper ha)
  refine ⟨f,hf,⟨hf.mapsTo,hf.injective,?_⟩,hdf⟩
  intro b hb
  by_contra hmiss
  obtain ⟨g,hg,hgain⟩ := improve_disk_embedding_of_omitted_value hU hc ha hf hdf
    (mem_ball_zero_iff.mp hb) hmiss
  exact (not_lt_of_ge (hmax g hg)) hgain

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanExteriorDiskMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual circularization of one Jordan hole. The map is conformal on
its entire exterior and fixes the point at infinity. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_jordan_exterior_circle_map (H : ℂ ≃ₜ ℂ) :
    ∃ F : Sphere → Sphere, F ∞=∞ ∧ IsConformalEquivalence F
      (closedTerminalCap H)ᶜ ((((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ) := by
  obtain ⟨hD,hsc,hproper,hzero⟩ := jordan_exterior_plane_data H
  obtain ⟨f,hf,hbij,_⟩ := exists_normalized_riemann_disk_map hD hsc hproper hzero
  let N := pointToInfinity ((H 0 : ℂ) : Sphere)
  let S := (closedTerminalCap H)ᶜ
  have hno : ∞ ∉ N '' S := by
    rintro ⟨p,hp,he⟩
    have hp' : p=((H 0 : ℂ) : Sphere) := N.injective
      (he.trans (pointToInfinity_apply_self _).symm)
    apply hp
    rw [hp']
    refine ⟨H 0,?_,rfl⟩
    rw [closure_jordanInterior]
    exact ⟨0,by simp,rfl⟩
  have hset : N '' S = ((↑) : ℂ → Sphere) '' jordanExteriorPlane H := by
    symm
    apply image_preimage_eq_of_subset
    intro x hx
    cases x using OnePoint.rec with
    | infty => exact (hno hx).elim
    | coe z => exact ⟨z,rfl⟩
  have hN := isConformalEquivalence_pointToInfinity ((H 0 : ℂ) : Sphere) S
  change IsConformalEquivalence N S (N '' S) at hN
  rw [hset] at hN
  have hF := conformalEquivalence_finiteLift hD hf.holomorphic hbij
  have hI := isConformalEquivalence_of_homeomorph CannonMobius.inversion
    (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)
    (fun p _ => isConformalAt_inversion p) (fun p _ => isConformalAt_inversion p)
  have himage : CannonMobius.inversion '' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ := by
    rw [CannonMobius.inversion.image_eq_preimage_symm]
    exact inversion_preimage_unitDisk
  rw [himage] at hI
  refine ⟨CannonMobius.inversion ∘ extendAtInfinity f ∘ N,?_,hN.trans (hF.trans hI)⟩
  change CannonMobius.inversion (extendAtInfinity f (N ∞))=∞
  have hN0 : N ∞=((0 : ℂ) : Sphere) := CannonMobius.inv_infty
  rw [hN0,extendAtInfinity_coe,hf.at_base]
  exact CannonMobius.inv_zero

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalJordanCircleMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal affine normalization of the actual one-hole circularization.
The new hole has an actual positive radius and finite Euclidean center. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_principal_jordan_circle_map (H : ℂ ≃ₜ ℂ) :
    ∃ (F : Sphere → Sphere) (c : ℂ) (r : ℝ), 0 < r ∧ IsPrincipalNormalized F ∧
      IsConformalEquivalence F (closedTerminalCap H)ᶜ
        ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ) := by
  obtain ⟨f,hfix,hf⟩ := exists_jordan_exterior_circle_map H
  have hU : IsOpen (closedTerminalCap H)ᶜ :=
    (isCompact_closedTerminalCap H).isClosed.isOpen_compl
  have hi : ∞ ∈ (closedTerminalCap H)ᶜ := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  obtain ⟨a,b,ha,hnorm⟩ := principal_normalize_at_infty hU hf.1 hf.bijOn.injOn hi hfix
  let A := affineSphere a b ha
  let D := ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1
  have hD : IsRoundClosedDisk D := isRoundClosedDisk_coe_closedBall 0 zero_lt_one
  have hAD : IsRoundClosedDisk (A '' D) := by
    have he : (A : Sphere → Sphere) = fun p => affineMobius a b ha • p :=
      funext (affineSphere_eq_smul a b ha)
    rw [he]
    exact isRoundClosedDisk_image_mobius hD _
  have hno : ∞ ∉ A '' D := by
    rintro ⟨p,hp,he⟩
    have hpinf : p=∞ := A.injective he
    subst p
    obtain ⟨z,_hz,hz⟩ := hp
    exact OnePoint.coe_ne_infty z hz
  obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hAD hno
  have hA := isConformalEquivalence_of_homeomorph A Dᶜ
    (fun p _ => isConformalAt_affineSphere a b ha p)
    (fun p _ => isConformalAt_affineSphere_symm a b ha p)
  have htarget : A '' Dᶜ = (((↑) : ℂ → Sphere) '' closedBall c r)ᶜ := by
    rw [A.image_compl,he]
  rw [htarget] at hA
  exact ⟨A ∘ f,c,r,hr,hnorm,hf.trans hA⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CompactReflectionCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reflection-invariant extension remains compactly supported: every
non-base tile lies inside one of the original finitely many disks. -/
open Set Function MeasureTheory Metric Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_10 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodBandGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The period-coordinate level graph of Definition 2.3, assembled from
local real branches on the punctured mask. The singular point belongs to
every level. Integer changes of sheet give the compatibility used below;
the closedness proof only needs the resulting equality of projected bands. -/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

def periodBandGraph {ι : Type*} (D M : Set Sphere) (b : Sphere)
    (V : ι → Set Sphere) (f : ι → Sphere → ℝ) : Set (Sphere × UnitAddCircle) :=
  {p | p.1 ∈ M ∧ (p.1 = b ∨ ∃ i, p.1 ∈ V i ∧ p ∈ circleBandGraph D (f i))}

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleLoopCircle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed path injective before its terminal time is a planar circle
embedding, to which the existing Schoenflies input applies. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem circleOfClosedPath_injective {a : ℂ} (p : Path a a)
    (hp : ∀ s t : PathTime, s < 1 → t < 1 → p s = p t → s = t) :
    Injective (circleOfClosedPath p) := by
  intro θ φ h
  rw [circleOfClosedPath_apply, circleOfClosedPath_apply] at h
  have he := hp _ _ (unitCircleCut_mem θ).2 (unitCircleCut_mem φ).2 h
  apply unitCircleCut_injective
  exact congrArg (fun t : PathTime => (t : ℝ)) he

theorem circleOfClosedPath_range {a : ℂ} (p : Path a a) :
    range (circleOfClosedPath p) = range p := by
  apply Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    rw [circleOfClosedPath_apply]
    exact mem_range_self _
  · rintro _ ⟨t, rfl⟩
    by_cases ht : t < 1
    · refine ⟨((t : ℝ) : UnitAddCircle), ?_⟩
      rw [circleOfClosedPath_apply]
      congr 1
      apply Subtype.ext
      change unitCircleCut ((t : ℝ) : UnitAddCircle) = (t : ℝ)
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from ⟨t.property.1, by simpa using ht⟩))
    · have ht1 : t = 1 := le_antisymm le_top (not_lt.mp ht)
      refine ⟨0, ?_⟩
      rw [ht1, p.target, circleOfClosedPath_apply]
      have hc : unitCircleCut (0 : UnitAddCircle) = 0 := by
        exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
          (show (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))
      have he : (⟨unitCircleCut (0 : UnitAddCircle),
          (unitCircleCut_mem 0).1, (unitCircleCut_mem 0).2.le⟩ : PathTime) = 0 :=
        Subtype.ext hc
      rw [he, p.source]

theorem exists_schoenflies_of_simple_closed_path (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a a)
    (hp : ∀ s t : PathTime, s < 1 → t < 1 → p s = p t → s = t) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath p ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) := by
  exact hsch _ ((circleOfClosedPath p).continuous.comp
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous)
    ((circleOfClosedPath_injective p hp).comp
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.injective)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TwoArcSimpleLoop
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two injective arcs that meet only at their prescribed endpoints
concatenate to a simple loop. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem two_arc_loop_injective_before_end {a b : ℂ} (p : Path a b) (q : Path b a)
    (hp : Injective p) (hq : Injective q)
    (hmeet : ∀ s t : PathTime, p s = q t → (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) :
    ∀ s t : PathTime, s < 1 → t < 1 → (p.trans q) s = (p.trans q) t → s = t := by
  intro s t hs1 ht1 he
  have hs' : (s : ℝ) < 1 := hs1
  have ht' : (t : ℝ) < 1 := ht1
  rw [Path.trans_apply, Path.trans_apply] at he
  split_ifs at he with hs ht
  · have h := congrArg Subtype.val (hp he)
    apply Subtype.ext
    change 2 * (s : ℝ) = 2 * (t : ℝ) at h
    linarith
  · rcases hmeet _ _ he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := congrArg Subtype.val hb
      change 2 * (t : ℝ) - 1 = 0 at h
      linarith
    · have h := congrArg Subtype.val hb
      change 2 * (t : ℝ) - 1 = 1 at h
      linarith
  · rcases hmeet _ _ he.symm with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := congrArg Subtype.val hb
      change 2 * (s : ℝ) - 1 = 0 at h
      linarith
    · have h := congrArg Subtype.val hb
      change 2 * (s : ℝ) - 1 = 1 at h
      linarith
  · have h := congrArg Subtype.val (hq he)
    apply Subtype.ext
    change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at h
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryClosingArc
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positively parametrized boundary arc closes a disk crosscut to a
simple loop. The resulting circle uses only the existing Schoenflies input. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem boundary_arc_parameter_mem {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) (t : PathTime) :
    unitCircleCut (normalizedArgument a) * (t : ℝ) ∈ Ico (0 : ℝ) 1 := by
  have hpos := boundary_angle_pos ha ha1
  exact ⟨mul_nonneg hpos.le t.property.1,
    (mul_le_of_le_one_right hpos.le t.property.2).trans_lt (unitCircleCut_mem _).2⟩

theorem boundaryClosingArc_norm (a : ℂ) (ha : ‖a‖ = 1) (t : PathTime) :
    ‖boundaryClosingArc a ha t‖ = 1 := Circle.norm_coe _

theorem boundaryClosingArc_injective {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    Injective (boundaryClosingArc a ha) := by
  intro s t he
  have hc := standardCirclePoint_injective he
  have hs : unitCircleCut (normalizedArgument a) * (s : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 s
  have ht : unitCircleCut (normalizedArgument a) * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 t
  have hst := (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).mp hc
  apply Subtype.ext
  exact mul_left_cancel₀ (ne_of_gt (boundary_angle_pos ha ha1)) hst

theorem crosscut_boundary_intersections {a : ℂ} (p : Path a 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∀ s t : PathTime, p s = boundaryClosingArc a ha t →
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
  intro s t he
  have hi := boundaryClosingArc_injective ha ha1
  by_cases hs0 : s = 0
  · right
    refine ⟨hs0, hi ?_⟩
    simpa only [hs0, p.source, (boundaryClosingArc a ha).target] using he.symm
  by_cases hs1 : s = 1
  · left
    refine ⟨hs1, hi ?_⟩
    simpa only [hs1, p.target, (boundaryClosingArc a ha).source] using he.symm
  have hh := hp s ⟨lt_of_le_of_ne bot_le (Ne.symm hs0), lt_of_le_of_ne le_top hs1⟩
  rw [he, boundaryClosingArc_norm] at hh
  exact (lt_irrefl _ hh).elim

theorem exists_schoenflies_of_disk_crosscut (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath (p.trans (boundaryClosingArc a ha))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) := by
  apply exists_schoenflies_of_simple_closed_path hsch
  exact two_arc_loop_injective_before_end p (boundaryClosingArc a ha) hi
    (boundaryClosingArc_injective ha ha1) (crosscut_boundary_intersections p hp ha ha1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactArcWinding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform winding bounds for initial portions of a compact simple-arc
family, in any continuous angular coordinate on the punctured plane. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

def initialArcAngles {b : ℂ}
    (q : C({x : ℂ // x ≠ b}, UnitAddCircle))
    (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = b)
    (c : PathTime) (hc : c < ⊤) : C(unitInterval, UnitAddCircle) :=
  ⟨fun t => q ⟨γ (t * c), fun h => by
    have ht : t * c = ⊤ := hi (h.trans he.symm)
    exact (not_le_of_gt hc) (ht ▸ unitInterval.mul_le_right)⟩,
    q.continuous.comp (((γ.continuous.comp (continuous_id.mul continuous_const))).subtype_mk _)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactDiskRayBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-depth part of a compact family of disk rays lies in a
common initial time interval, on which the angular lifts are uniformly bounded. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_uniform_tail
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hend : ∀ γ ∈ K, γ 1 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ c : PathTime, 0 < c ∧ c < 1 ∧
      ∀ γ ∈ K, ∀ t, c ≤ t → ‖γ t‖ < r := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let E : K × PathTime → ℂ := fun p => p.1.val p.2
  have hE : Continuous E := continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hE) r hr
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  let c : PathTime := ⟨1 - d / 2, by constructor <;> linarith⟩
  have hc0 : (0 : PathTime) < c := by
    change (0 : ℝ) < 1 - d / 2
    linarith
  have hc1 : c < 1 := by
    change 1 - d / 2 < (1 : ℝ)
    linarith
  refine ⟨c, hc0, hc1, ?_⟩
  intro γ hγ t ht
  have htd : dist t (1 : PathTime) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(t : ℝ) - 1| < δ
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    have hct : 1 - d / 2 ≤ (t : ℝ) := ht
    have hdδ : d ≤ δ := min_le_left _ _
    change -((t : ℝ) - 1) < δ
    linarith
  have hp : dist ((⟨γ, hγ⟩ : K), t) ((⟨γ, hγ⟩ : K), (1 : PathTime)) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using htd
  simpa only [E, hend γ hγ, dist_zero_right] using hmod hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanGraphGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed mean has the local real-band width and free-fiber
properties used by mixed grid geometry. These are derived from its
retained correction and the original arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_18 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedModelData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked coordinates and metric on one finite circle model.
The record retains the exact source and transported energy identities,
as well as the filling and core equalities needed by the limiting tests. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedModelData {J I : Type*} {n : ℕ}
    (T : J → ℂ ≃ₜ ℂ) (H : I → ℂ ≃ₜ ℂ) (G K : Set (ℝ × ℝ))
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ) (ε : ℝ) where
  widthIndex : ℕ
  base : Fin n → (ℝ × ℝ) → UnitAddCircle
  base_mask : ∀ l, base l =ᶠ[𝓝ˢ (M l)] f l
  base_core : ∀ᶠ z in 𝓝ˢ K, ∀ l, base l z = f l z
  functions : Fin n → (ℝ × ℝ) → UnitAddCircle
  filled : IsMaskedFilledCircleFamily (fun i => realJordanInterior (H i))
    (G ∪ ⋃ i, realJordanInterior (H i)) M
    (circleCutoffFamily base χ N (staircaseWidth (reciprocalGridStep N) widthIndex) θ) functions
  extension_contains : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, realJordanInterior (H i)
  mask_boundary_core : ∀ l, frontier (M l) ⊆ interior K
  retained : ∀ᶠ z in 𝓝ˢ K, ∀ l, functions l z = f l z
  radius : ℝ
  radius_pos : 0 < radius
  metric : (ℝ × ℝ) → PlanarMetric
  metric_smooth : ContDiff ℝ ∞ metric
  metric_pos : ∀ z, (metric z).PosDef
  metric_core : ∀ᶠ z in 𝓝ˢ K, metric z = sphericalMetricFactor z • 1
  metric_far : ∀ z ∉ Metric.closedBall 0 radius, metric z = sphericalMetricFactor z • 1
  tail : (∑ l : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M l,
    fieldEnergy (circleGradient (functions l)) metric z) < ε
  localized : ∀ l (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ K →
    (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M l,
      fieldEnergy (circleGradient (functions l)) metric z) <
    (∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f l))
      (fun z => sphericalMetricFactor z • 1) z) + ε
  domain : Set Sphere
  forward : Sphere → Sphere
  inverse : Sphere → Sphere
  circle_domain : IsCircleDomain domain
  equivalence : IsSmoothSphereEquivalence forward inverse (openCompletedRegion T) domain
  conformal_core : IsConformalOn forward (sphericalCore K)
  principal : IsPrincipalNormalized forward
  transported : ∀ l, IsOpen (sphereRealMap forward ''
      (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
    SmoothCircleOn (functions l ∘ sphereRealMap inverse)
      (sphereRealMap forward '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
    (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
      ((functions l ∘ sphereRealMap inverse) ∘ sphereRealMap forward) =ᶠ[𝓝 x] functions l)
  transported_energy : ∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
    s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
    (∫ y in sphereRealMap forward '' s,
      fieldEnergy (circleGradient (functions l ∘ sphereRealMap inverse)) (fun _ => 1) y) =
    ∫ x in s, fieldEnergy (circleGradient (functions l)) metric x

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SubordinateDustCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preliminary smooth dust covers subordinate to prescribed local
branch neighborhoods. This retains which neighborhood contains each
closed physical fill, for the mixed period-coordinate construction. -/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_smooth_physical_dust_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B A W : Set Sphere} (_hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (Q : A → Set Sphere) (hQ : ∀ a, IsOpen (Q a)) (haQ : ∀ a, a.val ∈ Q a) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Q a := by
  classical
  have hlocal (a : A) : ∃ V : Set Sphere, IsOpen V ∧ a.val ∈ V ∧
      closure V ⊆ (W ∩ {π OnePoint.infty}ᶜ) ∩ Q a ∧ IsConnected Vᶜ := by
    apply exists_sphere_neighborhood_connected_compl
      ((hW.inter isClosed_singleton.isOpen_compl).inter (hQ a))
    exact ⟨⟨hAW a.property, fun heq => hinfty (heq ▸ a.property)⟩, haQ a⟩
  choose V hVo haV hVW hVc using hlocal
  obtain ⟨m, C, a, hC, hCd, hCcover⟩ := exists_compact_clopen_refinement hA
    (fun T hT hconn => hTD T (hT.trans hAB) hconn) V hVo haV
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hCpi (i : Fin m) : π OnePoint.infty ∉ C i := by
    intro h
    exact (hVW (a i) (subset_closure ((hC i).2.2.1 h))).1.2 rfl
  have hCp (i : Fin m) : IsCompact (q ⁻¹' C i) :=
    isCompact_finite_preimage ((hC i).1.isClosed.preimage hπ) (hCpi i)
  have hCpd : Pairwise (Disjoint on fun i => q ⁻¹' C i) := by
    intro i j hij
    exact (hCd hij).preimage q
  have hCsub (i : Fin m) : q ⁻¹' C i ⊆ q ⁻¹' B :=
    preimage_mono ((hC i).2.1.trans hAB)
  have hdiff (i : Fin m) : IsClosed ((q ⁻¹' B) \ (q ⁻¹' C i)) := by
    have heq : B \ C i = (B \ A) ∪ (A \ C i) := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzB, hzC⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzC⟩
        · exact Or.inl ⟨hzB, hzA⟩
      · rintro z (hz | hz)
        · exact ⟨hz.1, fun hzC => hz.2 ((hC i).2.1 hzC)⟩
        · exact ⟨hAB hz.1, hz.2⟩
    have hc : IsClosed (B \ C i) := by
      rw [heq]
      exact hBA.union (hC i).2.2.2
    simpa only [preimage_sdiff] using hc.preimage hq
  have hVpu (i : Fin m) : IsPreconnected (q ⁻¹' V (a i))ᶜ ∧
      ¬ Bornology.IsBounded (q ⁻¹' V (a i))ᶜ := by
    apply physical_exterior_connected_unbounded_of_component_collapse
      G π hπ hclosed hsurj hr (hVo (a i)) (hVc (a i))
    exact fun h => (hVW (a i) h).1.2 rfl
  obtain ⟨f, t, γ, H, s, hs, hcover, hpair, hcurves⟩ :=
    exists_disjoint_dust_contours hsard hschoenflies (fun i => q ⁻¹' C i)
      (fun i => q ⁻¹' V (a i)) (q ⁻¹' B) hCp hCpd hCsub hdiff
      (fun i => (hVo (a i)).preimage hq) (fun i => preimage_mono (hC i).2.2.1)
      (fun i => (hVpu i).1) (fun i => (hVpu i).2)
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, (fun i => H (e.symm i)), (fun i => γ (e.symm i)), ?_, ?_, ?_⟩
  · intro z hz
    have hzC : q z ∈ ⋃ i, C i := hCcover.symm ▸ hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzC
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hcover (mem_iUnion.mpr ⟨i, hi⟩))
    refine mem_iUnion.mpr ⟨e ⟨p, hp⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hzp
  · intro i j hij
    exact hpair (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  · intro i
    let p := e.symm i
    obtain ⟨hinside, hsmooth, hemb, hfront, havoid⟩ := hcurves p p.property
    refine ⟨?_, hsmooth, hemb, hfront, ?_, a p.val.1, ?_⟩
    · exact hinside.trans (preimage_mono (subset_closure.trans
        (fun z hz => (hVW (a p.val.1) hz).1.1)))
    · intro z hz
      have hnotB : π (z : Sphere) ∉ B := fun h => Set.disjoint_left.mp havoid hz h
      refine ⟨?_, hnotB⟩
      by_contra h
      exact hnotB (hbad _ h)

    · exact hinside.trans (preimage_mono (subset_closure.trans
        (fun z hz => (hVW (a p.val.1) hz).2)))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AssembledMaskedModel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual grid, all terminal and filling caps, the common metric,
and the principal finite model are constructed from the original masked
coordinates. The boundary graphs are used only through their proved
compatibility and the local real branches. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def physicalMask (π : Sphere → Sphere) (M : Set Sphere) : Set (ℝ × ℝ) :=
  realChartDomain (π ⁻¹' M)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth replacements of the original scalar tests. Their full
boundary traces, continuous representatives and global Sobolev errors
are retained together for the circle-model construction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

structure ExactTraceTest (d : PathCodeData Sphere Sphere) (u : EuclideanPlane → ℝ) where
  smooth : EuclideanPlane → ℝ
  continuous : Continuous smooth
  compact : HasCompactSupport smooth
  contDiff : ContDiffOn ℝ (⊤ : ℕ∞) smooth (physicalPlaneDomain d.physicalDomain)
  unit : ∀ x, smooth x ∈ Icc 0 1
  partial_memLp : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ smooth x (EuclideanSpace.single i 1)) 2
    (volume.restrict (physicalPlaneDomain d.physicalDomain))
  trace : EqOn smooth u (physicalPlaneDomain d.physicalDomain)ᶜ
  coordinate : PhysicalRealCoordinate d id
  coordinate_eq : coordinate.quotient = sphereFromPlaneFunction smooth
  coordinate_continuous : Continuous coordinate.quotient
  error : DeGiorgi.MemW1pWitness 2 (fun x => u x - smooth x) univ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCoordinateData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The individual coordinate data consumed by a finite mixed transfer.
These fields retain the actual level graph and its chosen marked branches. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedCoordinateData {T : Type*} (G U : Set Sphere)
    (π : Sphere → Sphere) (σ : T → Sphere) where
  graph : Set (Sphere × UnitAddCircle)
  graph_closed : IsClosed graph
  mask : Set Sphere
  mask_closed : IsClosed mask
  mask_frontier : frontier mask ⊆ U
  singular : T
  Index : Type
  patch : Index → Set Sphere
  patch_open : ∀ i, IsOpen (patch i)
  cover : mask \ {σ singular} ⊆ ⋃ i, patch i
  branch : Index → Sphere → ℝ
  bound : Index → ℝ
  branch_bounded : ∀ i x, |branch i x| ≤ bound i
  physical : (ℝ × ℝ) → UnitAddCircle
  measurable : Measurable physical
  gradient_measurable : Measurable (circleGradient physical)
  smooth : SmoothCircleOn physical (realChartDomain G ∩ interior (physicalMask π mask))
  energy : MemLp (circleGradient physical) 2
    ((volume.restrict (realChartDomain G)).restrict (physicalMask π mask))
  physical_graph : ∀ x ∈ realChartDomain G ∩ interior (physicalMask π mask),
    (π (Complex.equivRealProdCLM.symm x : Sphere), physical x) ∈ graph
  branch_smooth : ∀ i, ContDiffOn ℝ ∞
    (fun x : ℝ × ℝ => branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
    (realChartDomain G ∩ realChartDomain (π ⁻¹' patch i))
  branch_projection : ∀ i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' patch i) →
    (branch i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = physical x
  lower : T → ℝ
  upper : T → ℝ
  width_nonneg : ∀ s, 0 ≤ upper s - lower s
  width_summable : Summable (fun s => (upper s - lower s) ^ 2)
  marked_fiber : ∀ s, {t : UnitAddCircle | (σ s, t) ∈ graph} ⊆
    ((↑) : ℝ → UnitAddCircle) '' Icc (lower s) (upper s)
  marked_branch : ∀ s, σ s ∈ mask → σ s ≠ σ singular → ∃ i,
    σ s ∈ patch i ∧ lower s = liminf (branch i) (𝓝[U] (σ s)) ∧
      upper s = limsup (branch i) (𝓝[U] (σ s))
  free_fiber : ∀ x ∈ π '' Gᶜ, x ∉ range σ → {t : UnitAddCircle | (x, t) ∈ graph}.Subsingleton

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCoordinateStage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite transfer of the given coordinate family, retaining the
actual model and every nonsingular terminal branch estimate. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedCoordinateStage {S : Type*} {n : ℕ} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : Fin n → MaskedCoordinateData G U π σ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε ρ : ℝ) (k₀ : ℕ) where
  indices : Set S
  indices_finite : indices.Finite
  flags : Flag ⊆ indices
  terminals : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : indices => σ s) (fun s => O s)
  fillCount : ℕ
  filling : Fin fillCount → ℂ ≃ₜ ℂ
  core : Set (ℝ × ℝ)
  core_closed : IsClosed core
  core_contains : K₀ ⊆ interior core
  core_source : core ⊆ realChartDomain G
  core_cocompact : IsCompact (closure coreᶜ)
  core_model : sphericalCore core ⊆ openCompletedRegion terminals.H
  cutoff : (ℝ × ℝ) → ℝ
  grid : ℕ
  offset : Fin n → ℝ
  small_grid : reciprocalGridStep grid < ρ
  model : MaskedModelData terminals.H filling (realChartDomain G) core
    (fun l => physicalMask π (C l).mask) (fun l => (C l).physical) cutoff grid offset ε
  late_width : k₀ ≤ model.widthIndex
  terminal_domain : indices → Set (ℝ × ℝ)
  terminal_branch : indices → Fin n → (ℝ × ℝ) → ℝ
  terminal_open : ∀ s, IsOpen (terminal_domain s)
  terminal_frontier : ∀ s, frontier (realJordanInterior (terminals.H s)) ⊆ terminal_domain s
  terminal_lift : ∀ l (s : indices), σ s ∈ (C l).mask → σ s ≠ σ (C l).singular →
    ContDiffOn ℝ ∞ (terminal_branch s l) (terminal_domain s) ∧
    ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (terminals.H s))),
      (terminal_branch s l x : UnitAddCircle) = model.functions l x
  terminal_excess : ∀ l, Real.sqrt
    (∑' s : {s : indices // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular},
      max (Metric.diam (terminal_branch s l '' frontier (realJordanInterior (terminals.H s))) -
        ((C l).upper s - (C l).lower s)) 0 ^ 2) < ε

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorLevelFamily
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact weighted-level data consumed by the barrier construction.
Both earlier real coordinates and the constructed masked means supply it. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

local instance localInst_r006e07_3 : BorelSpace Sphere := ⟨rfl⟩
structure PriorLevelFamily (G : Set Sphere) (π : Sphere → Sphere) where
  graph : ℕ → Set (Sphere × UnitAddCircle)
  closed : ∀ i, IsClosed (graph i)
  weighted : ∀ (i : ℕ) (g : Sphere → ℝ≥0∞), Measurable g →
    (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞ →
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in G ∩ π ⁻¹' {x | (x, θ) ∈ graph i}, g p ∂(μH[1] : Measure Sphere)) < ∞

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelRealSubfamily
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual real barrier functions retained on a masked circle model. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure ModelRealSubfamily {J I A : Type*} {n N : ℕ}
    {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ} {G K : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {f : Fin n → (ℝ × ℝ) → UnitAddCircle}
    {χ : (ℝ × ℝ) → ℝ} {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData T H G K M f χ N θ ε)
    (ι : A → Fin n) (r : A → (ℝ × ℝ) → ℝ) where
  functions : A → (ℝ × ℝ) → ℝ
  filled : IsFilledCoordinateFamily (fun i => realJordanInterior (H i))
    (G ∪ ⋃ i, realJordanInterior (H i))
    (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
      (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j)))) functions
  extension_contains : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, realJordanInterior (H i)
  projection : ∀ j x, (functions j x : UnitAddCircle) = Q.functions (ι j) x
  retained : ∀ᶠ x in 𝓝ˢ K, ∀ j, functions j x = r j x
  transported : ∀ j, ContDiffOn ℝ ∞ (functions j ∘ sphereRealMap Q.inverse)
    (realChartDomain Q.domain) ∧
    ∀ x ∈ realChartDomain (openCompletedRegion T),
      ((functions j ∘ sphereRealMap Q.inverse) ∘ sphereRealMap Q.forward) =ᶠ[𝓝 x] functions j
  transported_energy : ∀ j (s : Set (ℝ × ℝ)), MeasurableSet s →
    s ⊆ realChartDomain (openCompletedRegion T) →
    (∫ y in sphereRealMap Q.forward '' s,
      gradientEnergy (functions j ∘ sphereRealMap Q.inverse) (fun _ => 1) y) =
      ∫ x in s, gradientEnergy (functions j) Q.metric x
  metric_conformal : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt Q.metric Q.forward p

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MixedCoordinateStage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure MixedCoordinateStage {S : Type*} {n m : ℕ} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : Fin n → MaskedCoordinateData G U π σ)
    (ι : Fin m → Fin n) (r : Fin m → (ℝ × ℝ) → ℝ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε ρ : ℝ) (k₀ : ℕ)
    extends MaskedCoordinateStage C Flag O K₀ ε ρ k₀ where
  real : ModelRealSubfamily model ι r
  real_excess : ∀ j, Real.sqrt (∑' s : indices,
    max (terminalOscillation (terminals.H s) (real.functions j) -
      ((C (ι j)).upper s - (C (ι j)).lower s)) 0 ^ 2) < ε

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MixedModelExhaustion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal-family exhaustions whose finite models simultaneously retain
all the ordered period tests and the original real barrier family. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}

structure MixedModelExhaustion
    (d : CountableRealCoordinates G π σ) {C : Type*} [LinearOrder C]
    (data : C → MaskedCoordinateData G d.source π σ) (retained : ℕ → C)
    (O : ℕ → S → Set Sphere) (ε ρ : ℕ → ℝ) where
  real : RealModelExhaustion d O ε
  size : ℕ → ℕ
  label : ∀ n, Fin (size n) ↪o C
  slot : ∀ n, Fin (n + 1) → Fin (size n)
  slot_injective : ∀ n, Injective (slot n)
  label_real : ∀ n j, label n (slot n j) = retained j
  coordinate_eventually : ∀ c, ∀ᶠ n in atTop, c ∈ range (label n)
  stages : ∀ n, MixedCoordinateStage (fun j => data (label n j)) (slot n)
    (fun j => d.physical j) (real.flags n) (O n) (realChartDomain (real.cores n)) (ε n) (ρ n) n
  same_indices : ∀ n, (stages n).indices = (real.stages n).indices
  same_terminals : ∀ n, HEq (stages n).terminals (real.stages n).terminals
  same_forward : ∀ n, (stages n).model.forward = (real.stages n).forward
  same_inverse : ∀ n, (stages n).model.inverse = (real.stages n).inverse
  same_domain : ∀ n, (stages n).model.domain = (real.stages n).domain

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalCollarCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered Jordan coordinate on the constructed inward collar is a
jointly continuous punctured-disk family. Compact retention keeps the
singularity strictly on the inside of every small collar. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem PositiveJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryPairNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

abbrev BoundaryPairData := C(PathTime, ℂ) × (ℂ × ℝ≥0)

def boundaryPairFunctional (v : ℝ → ℝ) (p : BoundaryPairData) : ℝ :=
  roundDiskBoundaryPairing (p.1 ∘ projIcc 0 1 zero_le_one) p.2.1 p.2.2 v

/-- This is the open set excluded by a single retained period coordinate. -/
def boundaryExclusionSet (v : ℝ → ℝ) (budget : ℝ) : Set BoundaryPairData :=
  {p | budget < |boundaryPairFunctional v p|}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_MixedMarkedModels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original marked ends in the common mixed model. These constructions
use the actual terminal fibers; no transport of dependent terminal types
from the real subfamily is necessary. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

 def markIndex (n : ℕ) (s : S) : (M.stages n).indices :=
  ⟨(M.real.markIndex n s).val, by rw [M.same_indices n]; exact (M.real.markIndex n s).property⟩

end MixedModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MixedAssignedLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned normal limits of the actual mixed stages, retaining the
convergent center and radius sequences used by Stokes. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure AssignedMixedModelLimit {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {C : Type*} [LinearOrder C] {data : C → MaskedCoordinateData G d.source π σ}
    {retained : ℕ → C} {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ) where
  assignment : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
    (M.stages n).model.forward (M.stages n).model.domain
  subsequence : ℕ → ℕ
  function : ℂ → ℂ
  center : S → ℂ
  radius : S → ℝ
  cores : ℕ → SmoothJordanCore G
  contours : ∀ j, Fin (cores j).count → ℂ ≃ₜ ℂ
  strict : StrictMono subsequence
  converges : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
    finiteCoord ((M.stages (subsequence n)).model.forward (z : Sphere))) function
    atTop (((↑) : ℂ → Sphere) ⁻¹' G)
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  bounds : ∀ s, ‖center s‖ ≤ 3 * M.real.radius ∧ radius s ∈ Icc 0 (3 * M.real.radius)
  nested : ∀ j, (cores j).carrier ⊆ interior (cores (j + 1)).carrier
  exhausts : (⋃ j, interior (cores j).carrier) = G
  boundary : ∀ j i, extendAtInfinity function ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores j).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (contours j i))
  disjoint : ∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (contours j i)))
  image_core : ∀ j, (extendAtInfinity function '' (cores j).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (contours j i)
  side : ∀ j i, extendAtInfinity function ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores j).disk i))) =
    (extendAtInfinity function '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (contours j i))
  marked : ∀ s, ∃ (index : ∀ j, Fin (cores j).count) (p : Sphere),
    p ∈ (extendAtInfinity function '' G)ᶜ ∧
    connectedComponentIn Gᶜ (d.sourceMark s) = ⋂ j, closedTerminalCap ((cores j).disk (index j)) ∧
    connectedComponentIn (extendAtInfinity function '' G)ᶜ p =
      ⋂ j, closedTerminalCap (contours j (index j)) ∧
    ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s) ⊆
      connectedComponentIn (extendAtInfinity function '' G)ᶜ p ∧
    Tendsto (fun n => hausdorffDist
      (finiteCoord '' connectedComponentIn (M.stages (subsequence n)).model.domainᶜ
        ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)))
      (closedBall (center s) (radius s))) atTop (𝓝 0)

  disk_center : ℕ → S → ℂ
  disk_radius : ℕ → S → ℝ
  disk_bounds : ∀ n s, ‖disk_center n s‖ ≤ 3 * M.real.radius ∧
    disk_radius n s ∈ Icc 0 (3 * M.real.radius)
  disk_eq : ∀ s, ∀ᶠ n in atTop,
    connectedComponentIn (M.stages (subsequence n)).model.domainᶜ
      ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)) =
        ((↑) : ℂ → Sphere) '' closedBall (disk_center n s) (disk_radius n s)
  center_tendsto : ∀ s, Tendsto (fun n => disk_center n s) atTop (𝓝 (center s))
  radius_tendsto : ∀ s, Tendsto (fun n => disk_radius n s) atTop (𝓝 (radius s))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AssignedCollarExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every assigned mixed normal limit satisfies the actual fixed-source
collar exclusion. The terminal containment is derived from the shrinking
neighborhoods and the closed component quotient. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem AssignedMixedModelLimit.continuousOn
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained O ε ρ}
    (L : AssignedMixedModelLimit M) : ContinuousOn L.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
  intro z hz
  have h := continuousAt_finite_part_of_conformalAt (L.conformal.1 _ hz)
    (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt

 def MaskedCoordinateData.sourceStokesBudget
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (R : ℝ) : ℝ :=
  Real.sqrt Real.pi * R * Real.sqrt
    (∫ x in realChartDomain G ∩ physicalMask π C.mask,
      fieldEnergy (circleGradient C.physical) (fun x => sphericalMetricFactor x • 1) x) +
  2 * Real.pi * R * Real.sqrt
    (∑' t : {t : S // t ≠ C.singular}, (C.upper t - C.lower t) ^ 2)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B : Set Sphere} {π : Sphere → Sphere}
  (C : MaskedCoordinateData G U π (fun x : B => x.val))

local instance instBorelSpaceSphere_21_r006e07_1 : BorelSpace Sphere := ⟨rfl⟩
def dustWeight (x : Sphere) : ℝ≥0∞ := by
  classical
  exact if hx : x ∈ B then ENNReal.ofReal (C.upper ⟨x, hx⟩ - C.lower ⟨x, hx⟩) else 0

end FiniteTransfer.MaskedCoordinateData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpChainEdges
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete edges in a chain with fixed old jump disks. True edges
are actual allowed physical paths, and jump edges keep their original toll. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def physicalJumpEdge (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (x y : X) (a : ℝ≥0∞) : Prop :=
  (∃Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) ∧
    Γ.1.val ⊥ = x ∧ Γ.1.val ⊤ = y ∧ x ∈ d.quotientDomain ∧ y ∈ d.quotientDomain ∧
    physicalTollCost d g m Γ.1 = a) ∨
  (∃i, x ∈ V i ∩ d.quotientDomain ∧ y ∈ V i ∩ d.quotientDomain ∧ a = c i)

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

structure JumpBlockCode (d : PathCodeData X Y) (P : BoundedBlockPattern I n) where
  paths : ∀b : Fin (P.1.val+1), Fin ((P.2.2 b).val+1) → TaggedPhysicalPath d
  disks : ∀b : Fin (P.1.val+1), Fin (P.2.2 b).val → Set X

def jumpBlockCost (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) : ℝ≥0∞ :=
  (∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
    ∑i, fixedWidthJumpToll B m r τ (Z.disks b i))) + ∑i, T (P.2.1 i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SinglePieceBlock
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single true path as a grouped chain with no old or new jumps. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def singlePieceBlock (d : PathCodeData X Y) (γ : TaggedPhysicalPath d) :
    JumpBlockCode d (singlePiecePattern I) where
  paths := fun _ _ => γ
  disks := fun _ i => Fin.elim0 i

omit [MeasurableSpace X] in
@[simp] theorem singlePieceBlock_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (γ : TaggedPhysicalPath d) :
    jumpBlockCost d B g m r τ T (singlePiecePattern I) (singlePieceBlock d γ) =
      physicalTollCost d g m γ.1 := by
  simp [jumpBlockCost, singlePiecePattern, singlePieceBlock]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BlockCodeInvariants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain-endpoint and disk-origin invariants for normalization of mixed
paid chains into grouped jump codes. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

variable {X Y I K : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] {n : ℕ}

def BlockPathsInDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) : Prop :=
  ∀b j, (Z.paths b j).1.val ⊥ ∈ d.quotientDomain ∧ (Z.paths b j).1.val ⊤ ∈ d.quotientDomain

def BlockDisksFrom (d : PathCodeData X Y) (W : K → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) : Prop := ∀b i, ∃k, Z.disks b i = W k

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteJumpSystems
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite jump systems and their successive extensions. The label type is
retained, so adjoining a level preserves every previously installed edge. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace FiniteJumpSystem

variable {X : Type*}

variable {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def edge (A : FiniteJumpSystem X) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : X → X → ℝ≥0∞ → Prop :=
  physicalJumpEdge d ν N g m A.region A.toll

end FiniteJumpSystem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCountBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive toll floor gives one finite code space for every chain
under a fixed budget, independent of its original code bound. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def reboundJumpBlock (d : PathCodeData X Y) {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P) :
    JumpBlockCode d (reboundBlockPattern P hold hnew) := ⟨Z.paths, Z.disks⟩

omit [MeasurableSpace X] in
@[simp] theorem reboundJumpBlock_cost (d : PathCodeData X Y) (B : Set X)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞)
    {n N : ℕ} (P : BoundedBlockPattern I n) (hold : P.1.val ≤ N)
    (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P) :
    jumpBlockCost d B g m r τ T (reboundBlockPattern P hold hnew)
      (reboundJumpBlock d P hold hnew Z) = jumpBlockCost d B g m r τ T P Z := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FinitePlaneEmbedding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Openness, injectivity and continuity of the actual finite-plane maps induced by the
normalized smooth sphere equivalences. -/

open Set Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

theorem IsSmoothSphereAt.continuousAt_finite_map
    {f : Sphere → Sphere} {z : ℂ} (hf : IsSmoothSphereAt f (z : Sphere))
    (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    ContinuousAt (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  have he : sphereLocalMap f (z : Sphere) =
      fun w : ℂ => finiteCoord (f (w : Sphere)) := by
    funext w
    simp only [sphereLocalMap, chart, hfinite, ite_false, if_false, chartSymm_coe_apply]
  have hd := hf.2
  rw [he, chart_coe_self] at hd
  exact hd.continuousAt

theorem finite_part_image_eq {f : Sphere → Sphere} {S : Set ℂ}
    (hfinite : ∀ z ∈ S, f (z : Sphere) ≠ OnePoint.infty) :
    (fun z : ℂ => finiteCoord (f (z : Sphere))) '' S =
      ((↑) : ℂ → Sphere) ⁻¹' (f '' (((↑) : ℂ → Sphere) '' S)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, (coe_finiteCoord (hfinite x hx)).symm⟩
  · rintro ⟨p, ⟨x, hx, rfl⟩, he⟩
    exact ⟨x, hx, by change finiteCoord (f (x : Sphere)) = z; rw [he, finiteCoord_coe]⟩

theorem IsSmoothSphereEquivalence.finite_open_embedding
    {f fi : Sphere → Sphere} {U V : Set Sphere} (h : IsSmoothSphereEquivalence f fi U V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) (hV : IsOpen V) :
    ContinuousOn (fun z : ℂ => finiteCoord (f (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' U) ∧
      (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' U →
        IsOpen ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S)) ∧
      InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' U) := by
  refine ⟨fun z hz => ((h.smooth _ hz).continuousAt_finite_map
    (h.finite_forward hinf hfix hz)).continuousWithinAt, ?_, ?_⟩
  · intro S hS hSU
    rw [finite_part_image_eq (fun z hz => h.finite_forward hinf hfix (hSU hz))]
    apply IsOpen.preimage OnePoint.continuous_coe
    apply h.isOpen_image hV (OnePoint.isOpen_image_coe.mpr hS)
    rintro _ ⟨z, hz, rfl⟩
    exact hSU hz
  · intro x hx y hy he
    apply OnePoint.coe_injective
    apply h.bijOn.injOn hx hy
    exact (coe_finiteCoord (h.finite_forward hinf hfix hx)).symm.trans
      ((congrArg ((↑) : ℂ → Sphere) he).trans (coe_finiteCoord (h.finite_forward hinf hfix hy)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealAnchorRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
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

theorem plane_open_embedding (hG : IsOpen G) :
    ContinuousOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' G →
        IsOpen (A.function '' S)) ∧
      InjOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  have hV : IsOpen (extendAtInfinity A.function '' G) :=
    A.conformal.1.isOpen_image hG hG (Subset.refl G)
  obtain ⟨fi, heq⟩ := A.conformal.exists_smooth_inverse hG hV
  simpa only [extendAtInfinity_coe, finiteCoord_coe] using
    heq.finite_open_embedding hinf (by simp) hV

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanBandWeight
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local branch widths are controlled by the actual masked-coordinate
weights. Exact Haar length prevents a change of branch from weakening
the weight used by subsequent code laws. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_22 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RebasedLevelPresentations
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B G' U' B' : Set Sphere} {π : Sphere → Sphere}

local instance instBorelSpaceSphere_25_r006e07_1 : BorelSpace Sphere := ⟨rfl⟩
def rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    MaskedCoordinateData G' U' π (fun x : B' => x.val) := by
  subst G'; subst U'; subst B'
  exact C

 theorem graph_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).graph = C.graph := by
  subst G'; subst U'; subst B'
  rfl

 theorem mask_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).mask = C.mask := by
  subst G'; subst U'; subst B'
  rfl

 theorem physical_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).physical = C.physical := by
  subst G'; subst U'; subst B'
  rfl

 theorem singular_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    ((C.rebaseDust hG hU hB).singular : Sphere) = (C.singular : Sphere) := by
  subst G'; subst U'; subst B'
  rfl

 theorem width_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) (s : B') :
    (C.rebaseDust hG hU hB).upper s - (C.rebaseDust hG hU hB).lower s =
      C.upper ⟨s.val, hB ▸ s.property⟩ - C.lower ⟨s.val, hB ▸ s.property⟩ := by
  subst G'; subst U'; subst B'
  rfl

end FiniteTransfer.MaskedCoordinateData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedFlattenedSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Keep the large disk needed for the compact source cutoff and restrict
the same selection to the smaller disk on which that cutoff equals one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def FlattenedSourceSelection.restrictWorking
    (M : CompactScalarModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L L' δ ε : ℝ} {H : ControlledHeight R d}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε) (hL : L' ≤ L) :
    FlattenedSourceSelection M H Wold A L' δ ε := by
  let U := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  let V := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L'
  have hVU : V ⊆ U := inter_subset_inter_right _ (ball_subset_ball hL)
  have hμ : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
  have hsupport := (M.horizontalSection_plane_memLp hG hinf L).norm.indicator
    (MeasurableSet.iUnion (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet))
  refine {
    oldValues := S.oldValues, old_open := S.old_open, oldWitness := S.oldWitness
    old_close := S.old_close, old_error := S.old_error
    heightValues := S.heightValues, height_open := S.height_open, heightWitness := S.heightWitness
    height_close := S.height_close, height_error := S.height_error
    center := S.center, center_outside := S.center_outside, target := S.target
    target_projection := S.target_projection, radius := S.radius, radius_pos := S.radius_pos
    radius_tendsto := S.radius_tendsto, cutoff := S.cutoff, cutoff_smooth := S.cutoff_smooth
    cutoff_support := S.cutoff_support, cutoff_unit := S.cutoff_unit, value := S.value
    value_eq := S.value_eq, priority_continuous := S.priority_continuous
    priority_error_memLp := S.priority_error_memLp.mono_measure hμ
    priority_error := ?_, support_error := ?_
    old_constant := S.old_constant, height_constant := S.height_constant }
  · exact (ENNReal.toReal_mono S.priority_error_memLp.eLpNorm_ne_top
      (eLpNorm_mono_measure _ hμ)).trans_lt S.priority_error
  · exact (ENNReal.toReal_mono hsupport.eLpNorm_ne_top
      (eLpNorm_mono_measure _ hμ)).trans_lt S.support_error

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCompactTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite test families and the actual appending transition. The two new
coordinates occupy positions zero and one; every previous coordinate is
retained after the proved small flattening. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def AppendingPairData.toTestFamily
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η) : FiniteCompactTests G where
  count := m+2
  test := appendScalarPair D.old D.p D.q
  continuous := Fin.cases D.q_continuous (Fin.cases D.p_continuous D.old_continuous)
  compact := Fin.cases D.q_compact (Fin.cases D.p_compact D.old_compact)
  witness := Fin.cases D.q_witness (Fin.cases D.p_witness D.old_witness)
  pair_null := D.pair_null

 def FiniteCompactTests.singleton {G : Set Sphere} (u : EuclideanPlane → ℝ)
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain G)) : FiniteCompactTests G where
  count := 1
  test := fun _ => u
  continuous := fun _ => hu
  compact := fun _ => hs
  witness := fun _ => W
  pair_null := fun i j hij => (hij (Subsingleton.elim i j)).elim

/-- This finite appending supply is a derived theorem of the published
inputs, never introduced as an additional published assumption. -/
 def FiniteAppendingSupply (G : Set Sphere) (a : ℝ) : Prop :=
  ∀ T : FiniteCompactTests G, ∀ δ η : ℝ, 0 < δ → 0 < η →
    Nonempty (AppendingPairData G T.test T.witness a δ η)

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

abbrev FiniteSource (G : Set Sphere) := {z : ℂ // (z : Sphere) ∈ G}
abbrev MapDiskData (G : Set Sphere) := C(FiniteSource G, ℂ) × (ℂ × ℝ≥0)

 def finiteSourceMap {G : Set Sphere} (F : ℂ → ℂ)
    (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G)) : C(FiniteSource G, ℂ) :=
  ⟨fun z => F z, hF.domRestrict⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealEndCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every target end has a source address, and that address identifies its marked disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (L : AssignedRealModelLimit M)

theorem AssignedRealModelLimit.exists_source_end
    (hG : IsOpen G) {p : Sphere} (hp : p ∈ (extendAtInfinity L.function '' G)ᶜ) :
    ∃ q ∈ Gᶜ, ∃ E : RealTargetEnd L q, E.point = p := by
  obtain ⟨b, q, hq, hs, ht, hn⟩ := corresponding_source_end_of_target hG
    L.conformal.1 L.conformal.bijOn.injOn L.cores L.contours L.nested L.exhausts
    L.disjoint L.image_core L.boundary L.side hp
  have htn (n : ℕ) : closedTerminalCap (L.contours (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (b n)) :=
    (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
      ((L.cores n).disk (b n)) ((L.cores (n + 1)).disk (b (n + 1)))
      (L.contours n (b n)) (L.contours (n + 1) (b (n + 1)))
      ((L.cores (n + 1)).boundary_subset_domain (b (n + 1)))
      (L.boundary (n + 1) (b (n + 1))) (L.side n (b n))).mp (hn n)
  exact ⟨q, hq, ⟨b, p, hp, hs, ht, htn⟩, rfl⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MixedLimitRealProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mixed limit retains the exact real subfamily limit. Reindexing the
finite terminal assignment preserves its point labels, so all previously
proved real-barrier conclusions apply to this same limit map. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem PhysicalTerminalDisks.exists_reindexed_assignment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {τ : S → Sphere} {O : S → Set Sphere} {A B : Set S}
    (hAB : A = B)
    (T : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => τ s) (fun s => O s))
    (T' : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : B => τ s) (fun s => O s))
    (hT : HEq T T') {f : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T.H f V) :
    ∃ a' : TerminalComponentAssignment T'.H f V,
      ∀ (i : A) (j : B), (i : S) = j → a.point i = a'.point j := by
  subst B
  have hTT : T = T' := eq_of_heq hT
  subst T'
  exact ⟨a, fun i j h => congrArg a.point (Subtype.ext h)⟩

 def TerminalComponentAssignment.changeMap
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f f' : Sphere → Sphere} {V V' : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hf : f = f') (hV : V = V') :
    TerminalComponentAssignment T f' V' := by
  subst f'
  subst V'
  exact a

 theorem TerminalComponentAssignment.changeMap_point
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f f' : Sphere → Sphere} {V V' : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hf : f = f') (hV : V = V') (i : I) :
    (a.changeMap hf hV).point i = a.point i := by
  subst f'
  subst V'
  rfl

namespace FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
  {M : MixedModelExhaustion d data retained O ε ρ}

 theorem AssignedMixedModelLimit.exists_real_assignment
    (L : AssignedMixedModelLimit M) (n : ℕ) :
    ∃ a : TerminalComponentAssignment (M.real.stages n).terminals.H
      (M.real.stages n).forward (M.real.stages n).domain,
      ∀ (i : (M.stages n).indices) (j : (M.real.stages n).indices),
        (i : S) = j → (L.assignment n).point i = a.point j := by
  obtain ⟨a, ha⟩ := PhysicalTerminalDisks.exists_reindexed_assignment (M.same_indices n)
    (M.stages n).terminals (M.real.stages n).terminals (M.same_terminals n) (L.assignment n)
  refine ⟨a.changeMap (M.same_forward n) (M.same_domain n), ?_⟩
  intro i j hij
  rw [TerminalComponentAssignment.changeMap_point]
  exact ha i j hij

 def AssignedMixedModelLimit.toReal (L : AssignedMixedModelLimit M) : AssignedRealModelLimit M.real := by
  classical
  choose a ha using L.exists_real_assignment
  refine {
    assignment := a
    subsequence := L.subsequence
    function := L.function
    center := L.center
    radius := L.radius
    cores := L.cores
    contours := L.contours
    strict := L.strict
    converges := ?_
    normalized := L.normalized
    conformal := L.conformal
    bounds := L.bounds
    nested := L.nested
    exhausts := L.exhausts
    boundary := L.boundary
    disjoint := L.disjoint
    image_core := L.image_core
    side := L.side
    marked := ?_ }
  · simpa only [M.same_forward] using L.converges
  · intro s
    obtain ⟨i, p, hp, hsrc, htgt, hsub, hlim⟩ := L.marked s
    refine ⟨i, p, hp, hsrc, htgt, hsub, ?_⟩
    have he (n : ℕ) : (L.assignment (L.subsequence n)).point
        (M.markIndex (L.subsequence n) s) =
        (a (L.subsequence n)).point (M.real.markIndex (L.subsequence n) s) :=
      ha _ _ _ rfl
    simpa only [he, M.same_domain] using hlim

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RecursiveCompactReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive positive law gives an actual compactly supported terminal-arc law at
sufficiently deep collars. Its physical density and punctured hit norm are arbitrarily
small, and the original prescribed gates survive the reduction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r006e07_4 : BorelSpace Sphere := ⟨rfl⟩
structure CompactRecursiveReduction
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω) (V : Set Sphere) (ε : ℝ≥0∞) where
  arcs : Set C(PathTime, Sphere)
  compact : IsCompact arcs
  terminal : arcs ⊆ terminalArcSet V L.data.target
  finite_length : ∀ γ ∈ arcs, physicalDomainLength L.data.domainEquiv L.data.basePoint γ < ∞
  law : ProbabilityMeasure arcs
  density : Sphere → ℝ≥0∞
  density_measurable : Measurable density
  occupation : meanPhysicalOccupation L.data.domainEquiv L.data.basePoint (law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) =
    sphericalArea.withDensity density
  hit_le : ∀ x, pathHitProbability (law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) x ≤
    2 * pathHitProbability (codePathLaw L.data L.law) x
  outside : ∀ x ∉ closure V, pathHitProbability (law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) x = 0
  small : (∫⁻ x, density x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) +
    countingSquareNorm (fun s : L.data.dust =>
      if s.val ≠ L.data.target then pathHitProbability (law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) s.val else 0) < ε
  reduction : IsSubarcLawReduction (codePathLaw L.data L.law) (law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarEndCaps
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

 theorem eventually_source_cap_subset {V : Set Sphere} (hV : IsOpen V)
    (hsub : connectedComponentIn Gᶜ q ⊆ V) :
    ∀ᶠ n in atTop, closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ V := by
  obtain ⟨N, hN⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone hV
    (by rwa [← E.source])
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (E.source_cap_antitone hn).trans hN

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
namespace AssignedRealModelLimit
variable (L : AssignedRealModelLimit M)

 structure SourceEndAt (p : Sphere) where
  source : Sphere
  outside : source ∈ Gᶜ
  matching : RealTargetEnd L source
  point_eq : matching.point = p

 def chosenSourceEnd (hG : IsOpen G) (p : Sphere)
    (hp : p ∉ extendAtInfinity L.function '' G) : L.SourceEndAt p := by
  classical
  exact Classical.choice (show Nonempty (L.SourceEndAt p) from by
    obtain ⟨q, hq, E, he⟩ := L.exists_source_end hG hp
    exact ⟨⟨q, hq, E, he⟩⟩)

 def sourceProjection (hG : IsOpen G) (π : Sphere → Sphere) (p : Sphere) : Sphere := by
  classical
  exact if hp : p ∈ extendAtInfinity L.function '' G then
    π (invFunOn (extendAtInfinity L.function) G p)
    else π (L.chosenSourceEnd hG p hp).source

 theorem sourceProjection_on_image (hG : IsOpen G) (π : Sphere → Sphere)
    {x : Sphere} (hx : x ∈ G) :
    L.sourceProjection hG π (extendAtInfinity L.function x) = π x := by
  rw [sourceProjection, dite_eq_left (mem_image_of_mem _ hx),
    L.conformal.bijOn.injOn.leftInvOn_invFunOn hx]

 theorem sourceProjection_off_image (hG : IsOpen G) (π : Sphere → Sphere)
    {p : Sphere} (hp : p ∉ extendAtInfinity L.function '' G) :
    L.sourceProjection hG π p = π (L.chosenSourceEnd hG p hp).source := by
  simp only [sourceProjection, dite_eq_right hp]

end AssignedRealModelLimit

namespace RealTargetEnd
variable {L : AssignedRealModelLimit M} {q q' : Sphere}
  (E : RealTargetEnd L q)

 theorem source_in_cap_of_target_interior (E' : RealTargetEnd L q') (hq' : q' ∈ Gᶜ)
    (n : ℕ)
    (hp : E'.point ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (E.address n))) :
    q' ∈ closedTerminalCap ((L.cores n).disk (E.address n)) := by
  have hp' : E'.point ∈ closedTerminalCap (L.contours n (E'.address n)) :=
    mem_iInter.mp (E'.target ▸ mem_connectedComponentIn E'.outside) n
  have he : E'.address n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (L.contours n) (L.disjoint n) hne)
      hp' ((image_mono subset_closure) hp)
  have hqcap := mem_iInter.mp (E'.source ▸ mem_connectedComponentIn hq') n
  rwa [he] at hqcap

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AppendingEnergyTolerance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite saved family has a common positive energy tolerance. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem AppendingPairData.exists_energy_tolerance
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hG : IsOpen G) {n : ℕ} (c : Fin n → EuclideanPlane) :
    ∃ t > 0, ∀ i (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G ∩ ball 0 (65*a)))
        (Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G ∩ ball 0 (65*a))),
      (∀ z ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
        ‖planePair (p z) (q z)-planePair (D.p z) (D.q z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-D.p_witness.weakGrad z) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-D.q_witness.weakGrad z) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => D.barrier (planePair (p z) (q z)-c i))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η := by
  classical
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) (65*a)
  have hU : IsOpen U := (isOpen_physicalPlaneDomain hG).inter isOpen_ball
  have hUf : volume U ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono (inter_subset_right : U ⊆ ball 0 (65*a))).trans_lt measure_ball_lt_top).ne
  let Wx := D.p_witness.restrict hU inter_subset_left
  let Wy := D.q_witness.restrict hU inter_subset_left
  obtain ⟨C,hC⟩ := (D.barrier_compact.fderiv ℝ).exists_bound_of_continuous
    (D.barrier_smooth.continuous_fderiv (by simp))
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (D.barrier_compact.fderiv ℝ)
    (D.barrier_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hDD : ∀ x y, ‖fderiv ℝ D.barrier x-fderiv ℝ D.barrier y‖ ≤ (K : ℝ)*‖x-y‖ :=
    fun x y => by simpa only [dist_eq_norm] using hK.dist_le_mul x y
  have hdata (i : Fin n) : ∃ t > 0, ∀ (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U),
      (∀ z ∈ U, ‖planePair (p z) (q z)-planePair (D.p z) (D.q z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => D.barrier (planePair (p z) (q z)-c i)) U,
        (eLpNorm W.weakGrad 2 (volume.restrict U)).toReal < η := by
    obtain ⟨V,hV⟩ := D.small_energy (c i)
    obtain ⟨hΦ,_,_,hunit,_,hD,hDD'⟩ := translatedPhysicalBarrier_data D.barrier_smooth
      D.barrier_compact D.barrier_support D.barrier_unit D.barrier_one
      (fun x => (hC x).trans (le_max_left C 0)) hDD (c i)
    exact exists_saved_barrier_energy_tolerance hU hUf D.p_continuous D.q_continuous Wx Wy
      (hΦ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (show (0 : ℝ) ≤ 1 by norm_num) (le_max_right C 0) K.coe_nonneg
      (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hunit x).1]; exact (hunit x).2)
      hD hDD' V hV
  choose r hr hri using hdata
  obtain ⟨t,ht,htr⟩ := exists_common_positive_fin r hr
  refine ⟨t,ht,?_⟩
  intro i p q hp hq Wp Wq hclose hpE hqE
  exact hri i p q hp hq Wp Wq (fun z hz => (hclose z hz).trans (htr i))
    (hpE.trans (htr i)) (hqE.trans (htr i))

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

structure SavedSeparatingFamily (G : Set Sphere) (a η : ℝ)
    (p q : EuclideanPlane → ℝ)
    (Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G))
    (Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)) where
  count : ℕ
  jordan : Fin count → ℂ ≃ₜ ℂ
  curve : Fin count → Circle → ℂ
  neighborhood : Fin count → Set ℂ
  barrier : Fin count → EuclideanPlane → ℝ
  cover : {z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (jordan i)
  inside : ∀ i, closure (jordanInterior (jordan i)) ⊆ ball 0 (64*a)
  regular : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i) ∧ Topology.IsEmbedding (curve i) ∧
    frontier (jordanInterior (jordan i)) = range (curve i) ∧ ∀ z ∈ range (curve i), (z : Sphere) ∈ G
  open_neighborhood : ∀ i, IsOpen (neighborhood i)
  contains : ∀ i, closure (jordanInterior (jordan i)) ⊆ neighborhood i
  smooth : ∀ i, ContDiff ℝ ∞ (barrier i)
  compact : ∀ i, HasCompactSupport (barrier i)
  unit : ∀ i x, barrier i x ∈ Icc (0 : ℝ) 1
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  stable : ∀ (p' q' : EuclideanPlane → ℝ), Continuous p' → Continuous q' →
    ∀ (Wp' : DeGiorgi.MemW1pWitness 2 p' (physicalPlaneDomain G ∩ ball 0 (65*a)))
      (Wq' : DeGiorgi.MemW1pWitness 2 q' (physicalPlaneDomain G ∩ ball 0 (65*a))),
    (∀ x, ‖planePair (p' x) (q' x)-planePair (p x) (q x)‖ ≤ tolerance) →
    (eLpNorm (fun x => Wp'.weakGrad x-Wp.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ tolerance →
    (eLpNorm (fun x => Wq'.weakGrad x-Wq.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ tolerance →
    ∀ i,
      (∀ z ∈ neighborhood i, barrier i (planePair (p' (complexPlaneCoordinates.symm z))
        (q' (complexPlaneCoordinates.symm z))) = 1) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
        barrier i (planePair (p' (complexPlaneCoordinates.symm z))
          (q' (complexPlaneCoordinates.symm z))) = 0) ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => barrier i (planePair (p' x) (q' x)))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η

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

structure SavedAppendingStep {G : Set Sphere} (a : ℝ) (T : FiniteCompactTests G) (δ η : ℝ) where
  data : AppendingPairData G T.test T.witness a δ η
  saved : SavedSeparatingFamily G a η data.p data.q data.p_witness data.q_witness

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarCircleModelData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained circle-model data, separated from their construction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

structure CompactScalarCircleModel (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ) where
  function : ℂ → ℂ
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  circle : IsCircleDomain (extendAtInfinity function '' G)
  projection : Sphere → Sphere
  projection_continuous : Continuous projection
  projection_inverse : ∀ p ∈ G, projection (extendAtInfinity function p) = p
  projection_outside : ∀ p ∉ extendAtInfinity function '' G, projection p ∈ Gᶜ
  projection_component : ∀ p ∉ extendAtInfinity function '' G,
    ∀ q ∈ connectedComponentIn (extendAtInfinity function '' G)ᶜ p, projection q = projection p
  witness : ∀ i, DeGiorgi.MemW1pWitness 2
    (fun x => sphereFromPlaneFunction (u i) (projection (planeSphere x))) univ
  gradient_zero : ∀ i j, ∀ᵐ x ∂volume,
    x ∉ physicalPlaneDomain (extendAtInfinity function '' G) → (witness i).weakGrad x j = 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModelFromCircle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed circle model belongs to the coefficient-extremal class. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 namespace CompactScalarCircleModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_compact (M : CompactScalarCircleModel G u)
    (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    HasCompactSupport (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) := by
  have hp : M.projection OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
  have ht := M.projection_continuous.tendsto OnePoint.infty
  rw [hp] at ht
  have hz₀ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction (u i) p = 0 := by
    let K := complexPlaneCoordinates '' tsupport (u i)
    have hK : IsCompact K := (hs i).isCompact.image complexPlaneCoordinates.continuous
    have hN : (((↑) : ℂ → Sphere) '' K)ᶜ ∈ 𝓝 (OnePoint.infty : Sphere) :=
      (OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩).mem_nhds
        OnePoint.infty_notMem_image_coe
    filter_upwards [hN] with p hp
    cases p using OnePoint.rec with
    | infty => simp [sphereFromPlaneFunction]
    | coe z =>
      rw [sphereFromPlaneFunction_coe]
      apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hp ⟨z, ⟨complexPlaneCoordinates.symm z, hz,
        complexPlaneCoordinates.apply_symm_apply z⟩, rfl⟩
  have hz := ht.eventually hz₀
  have hC : HasCompactSupport (fun z : ℂ => sphereFromPlaneFunction (u i) (M.projection z)) := by
    rw [hasCompactSupport_iff_eventuallyEq]
    exact OnePoint.tendsto_coe_infty.eventually hz
  exact hC.comp_homeomorph complexPlaneCoordinates.toHomeomorph

 def toCompactScalarModel (M : CompactScalarCircleModel G u)
    (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i))
    (b : ℂ) (hb : HasPrincipalCoefficient M.function b) : CompactScalarModel G u where
  function := M.function
  coefficient := b
  coefficient_limit := hb
  conformal := M.conformal
  roundDomain := extendAtInfinity M.function '' G
  round_circle := M.circle
  deformation := Homeomorph.refl ℂ
  image_eq := by
    have he : ((Homeomorph.refl ℂ).onePointCongr : Sphere → Sphere) = id := by
      funext p
      cases p using OnePoint.rec <;> rfl
    rw [he, image_id]
  projection := M.projection
  projection_continuous := M.projection_continuous
  projection_inverse := M.projection_inverse
  projection_outside := M.projection_outside
  projection_component := M.projection_component
  witness := M.witness
  gradient_zero := M.gradient_zero
  scalar_compact := M.scalar_compact hinf hs

 end CompactScalarCircleModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ScalarModelLinearRecovery
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear recovery of original signed tests from bounded retained tests
preserves the same circle model and zero complementary gradients. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem sphereFromPlaneFunction_linear_difference
    (u v : EuclideanPlane → ℝ) (a b : ℝ) (p : Sphere) :
    sphereFromPlaneFunction (fun x => a * u x - b * v x) p =
      a * sphereFromPlaneFunction u p - b * sphereFromPlaneFunction v p := by
  classical
  by_cases hp : p = OnePoint.infty <;> simp [sphereFromPlaneFunction, hp]

namespace CompactScalarCircleModel

 def linearDifference {G : Set Sphere} {n m : ℕ}
    {v : Fin n → EuclideanPlane → ℝ} (M : CompactScalarCircleModel G v)
    (left right : Fin m → Fin n) (a b : Fin m → ℝ) :
    CompactScalarCircleModel G
      (fun i x => a i * v (left i) x - b i * v (right i) x) := by
  let W (i : Fin m) := ((M.witness (left i)).smul (a i)).sub
    ((M.witness (right i)).smul (b i))
  let H (i : Fin m) : DeGiorgi.MemW1pWitness 2
      (fun x => sphereFromPlaneFunction
        (fun y => a i * v (left i) y - b i * v (right i) y) (M.projection (planeSphere x))) univ :=
    (W i).congr_ae (Eventually.of_forall fun x =>
      (sphereFromPlaneFunction_linear_difference _ _ _ _ _).symm)
  exact {
    function := M.function
    normalized := M.normalized
    conformal := M.conformal
    circle := M.circle
    projection := M.projection
    projection_continuous := M.projection_continuous
    projection_inverse := M.projection_inverse
    projection_outside := M.projection_outside
    projection_component := M.projection_component
    witness := H
    gradient_zero := by
      intro i j
      filter_upwards [M.gradient_zero (left i) j, M.gradient_zero (right i) j] with x hl hr hx
      change a i * (M.witness (left i)).weakGrad x j +
        (-1) * (b i * (M.witness (right i)).weakGrad x j) = 0
      rw [hl hx, hr hx]
      ring }

end CompactScalarCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalFiniteEmbedding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite part of an injective conformal sphere map fixing infinity is
an actual holomorphic open embedding on its finite domain. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma IsConformalOn.finite_open_embedding
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hi : InjOn f U) (hinf : ∞ ∈ U) (hfix : f ∞=∞) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' U) ∧
    (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' U →
      IsOpen ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S)) ∧
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' U) := by
  have hfin (z : ℂ) (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ ∞ :=
    finite_image_of_fixes_infty hi hinf hfix hz
  refine ⟨fun z hz => (analyticAt_finite_map_of_conformal hU hf hz
    (hfin z hz)).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro S hS hSU
    rw [finite_part_image_eq (fun z hz => hfin z (hSU hz))]
    apply IsOpen.preimage OnePoint.continuous_coe
    exact hf.isOpen_image hU (OnePoint.isOpen_image_coe.mpr hS)
      (by rintro _ ⟨z,hz,rfl⟩; exact hSU hz)
  · intro x hx y hy he
    apply OnePoint.coe_injective
    apply hi hx hy
    exact (coe_finiteCoord (hfin x hx)).symm.trans
      ((congrArg ((↑) : ℂ → Sphere) he).trans (coe_finiteCoord (hfin y hy)))

lemma finite_part_sphere_image {f : Sphere → Sphere} {S : Set ℂ}
    (hfin : ∀ z ∈ S, f (z : Sphere) ≠ ∞) :
    ((↑) : ℂ → Sphere) '' ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' S) =
      f '' (((↑) : ℂ → Sphere) '' S) := by
  rw [image_image, image_image]
  exact image_congr (fun z hz => coe_finiteCoord (hfin z hz))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- Incidence in an edge-relabelled graph is exactly incidence of the uniquely represented
old edge. -/
theorem relabelEdges_inc (G : Graph α β) (f : β → δ) (hf : InjOn f E(G))
    (d : δ) (x : α) :
    (G.relabelEdges f hf).Inc d x ↔
      ∃ e ∈ E(G), f e = d ∧ G.Inc e x := by
  constructor
  · rintro ⟨y, e, he, hfe, hxy⟩
    exact ⟨e, he, hfe, y, hxy⟩
  · rintro ⟨e, he, rfl, y, hxy⟩
    exact ⟨y, hxy.relabelEdges hf⟩

/-- Relabelling an edge list does not change the vertices it covers. -/
theorem coveredVertices_relabelEdges (hf : InjOn f E(G)) {W : List β}
    (hW : ∀ e ∈ W, e ∈ E(G)) :
    (G.relabelEdges f hf).coveredVertices (W.map f) = G.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨d, hd, y, hdy⟩
    obtain ⟨e, heW, rfl⟩ := List.mem_map.1 hd
    rcases hdy with ⟨g, hg, hge, hgy⟩
    have hgeq : g = e := hf hg (hW e heW) hge
    exact ⟨e, heW, y, hgeq ▸ hgy⟩
  · rintro ⟨e, heW, y, hey⟩
    exact ⟨f e, List.mem_map_of_mem heW, y, hey.relabelEdges hf⟩

/-- Relabelling a walk's edge list does not change its visited vertices. -/
theorem walkVertices_relabelEdges (hf : InjOn f E(G)) (u : α) {W : List β}
    (hW : ∀ e ∈ W, e ∈ E(G)) :
    (G.relabelEdges f hf).walkVertices u (W.map f) = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_relabelEdges hf hW]

/-- A path pushes forward along an injective relabelling of its edges. -/
theorem IsPath.relabelEdges (hf : InjOn f E(G)) (h : G.IsPath u W v) :
    (G.relabelEdges f hf).IsPath u (W.map f) v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW fresh ih =>
    refine .cons (hl.relabelEdges hf) ih ?_
    rw [walkVertices_relabelEdges hf w hW.isWalk.edgeSet_subset]
    exact fresh

/-- A walk surviving a vertex deletion still survives that deletion after edge relabelling. -/
theorem IsWalk.relabelEdges_deleteVerts {X : Set α} {u v : α} {W : List β}
    (hf : InjOn f E(G)) (h : (G.deleteVerts X).IsWalk u W v) :
    ((G.relabelEdges f hf).deleteVerts X).IsWalk u (W.map f) v := by
  induction h with
  | nil hx =>
      apply IsWalk.nil
      rw [vertexSet_deleteVerts, vertexSet_relabelEdges]
      exact hx
  | cons hl hW ih =>
      apply IsWalk.cons _ ih
      rw [deleteVerts_isLink] at hl ⊢
      exact ⟨hl.1.relabelEdges hf, hl.2.1, hl.2.2⟩

/-! ### Relabelling a drawing -/

end Graph
end

section
-- module Solutions.Q146_CD.MatchedArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil
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

/-- A continuous injection of a compact set has a continuous `invFunOn` on its image. -/
theorem continuousOn_invFunOn_image' {f : ℝ → Plane} {s : Set ℝ} (hs : IsCompact s)
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
    exact ⟨by rw [mem_preimage, hinj.leftInvOn_invFunOn hxs]; exact hxF,
      ⟨x, hxs, rfl⟩⟩

/-! ## A subarc of a polygonal arc is polygonal -/

/-- An arc contained in another arc is the unique closed subarc between its two endpoints.
This form allows the ambient arc to have different endpoints. -/
theorem IsArcBetween.eq_of_subset_arc {A B C : Set Plane} {p q r s : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hC : IsArcBetween C r s) (hAC : A ⊆ C) (hBC : B ⊆ C) : A = B := by
  obtain ⟨f, hfc, hfi, rfl, -, -⟩ := hC
  let inv : Plane → ℝ := Function.invFunOn f I
  have hinv : ContinuousOn inv (f '' I) :=
    continuousOn_invFunOn_image' isCompact_I hfc hfi
  have hmaps : MapsTo inv (f '' I) I := by
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn f I (f t) ∈ I
    rw [hfi.leftInvOn_invFunOn ht]
    exact ht
  have image_inv (K : Set Plane) (hK : K ⊆ f '' I) : f '' (inv '' K) = K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, hxK, rfl⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hK hxK
      simpa [inv, hfi.leftInvOn_invFunOn ht] using hxK
    · intro x hxK
      obtain ⟨t, ht, rfl⟩ := hK hxK
      exact ⟨inv (f t), ⟨f t, hxK, rfl⟩, by simp [inv, hfi.leftInvOn_invFunOn ht]⟩
  have image_is_interval (K : Set Plane) (hKarc : IsArcBetween K p q)
      (hK : K ⊆ f '' I) :
      inv '' K = uIcc (inv p) (inv q) := by
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hKarc
    let k : ℝ → ℝ := inv ∘ g
    have hgmap : MapsTo g I (f '' I) := fun t ht => hK (hgim ▸ Set.mem_image_of_mem g ht)
    have hkc : ContinuousOn k I := hinv.comp hgc hgmap
    have hki : InjOn k I := by
      intro x hx y hy hxy
      apply hgi hx hy
      have hleft : ∀ z ∈ K, f (inv z) = z := by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := hK hz
        simp [inv, hfi.leftInvOn_invFunOn ht]
      rw [← hleft (g x) (hgim ▸ Set.mem_image_of_mem g hx),
        ← hleft (g y) (hgim ▸ Set.mem_image_of_mem g hy)]
      exact congrArg f (show inv (g x) = inv (g y) from hxy)
    have hkimage : k '' I = uIcc (k 0) (k 1) := by
      rcases hkc.strictMonoOn_of_injOn_Icc' zero_le_one hki with hmono | hanti
      · rw [hkc.image_Icc_of_monotoneOn zero_le_one hmono.monotoneOn,
          uIcc_of_le (hmono.monotoneOn zero_mem_I one_mem_I zero_le_one)]
      · rw [hkc.image_Icc_of_antitoneOn zero_le_one hanti.antitoneOn,
          uIcc_of_ge (hanti.antitoneOn zero_mem_I one_mem_I zero_le_one)]
    calc
      inv '' K = k '' I := by rw [← hgim, Set.image_image]; rfl
      _ = uIcc (k 0) (k 1) := hkimage
      _ = uIcc (inv p) (inv q) := by simp [k, Function.comp_def, hg0, hg1]
  have hAi := image_is_interval A hA hAC
  have hBi := image_is_interval B hB hBC
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ f '' (inv '' A) := by
      rw [image_inv A hAC]
      exact hx
    rw [hAi, ← hBi, image_inv B hBC] at hx'
    exact hx'
  · intro x hx
    have hx' : x ∈ f '' (inv '' B) := by
      rw [image_inv B hBC]
      exact hx
    rw [hBi, ← hAi, image_inv A hAC] at hx'
    exact hx'

/-! ## Matching two named arcs -/

/-! ## Transporting a plane drawing along an arc homeomorphism -/

end Schoenflies

open Schoenflies
end

section
-- module Solutions.Q146_CD.SkeletonLocal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- Positive scaling does not move a direction. -/
theorem dir_smul_pos (ht : 0 < t) (u : Plane) : Plane.dir (t • u) = Plane.dir u := by
  have hn : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [Plane.dir, Plane.dir, hn, smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc,
    inv_mul_cancel₀ ht.ne', mul_one]

/-! ### The local directions of a set -/

/-! ### The pieces through a point

Everything is now bookkeeping over a finite list of segments and a finite set of stray points.
`GoodRadius x P r` collects what a radius must avoid on account of one piece: pieces missing
`x` must stay outside the disk, and pieces through `x` must not end inside it. -/

/-! ### The membership criterion -/

/-! ### A local radius exists

The construction: choose a radius good for every piece and strictly below the distance to
every stray point other than `x`. -/

/-! ### What a local radius gives -/

end Schoenflies

/-! ### Finite polygonal plane graphs -/
end

section
-- module Solutions.Q146_CD.SkeletonAccess
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The horizontal unit vector, used only to have *some* direction to slit along. -/
theorem isDirection_mk_one_zero : Plane.IsDirection (Plane.mk 1 0) := by
  rw [Plane.IsDirection, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

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

/-! ### `lem:cellulation-invariants`(i), as a hypothesis

The only thing assumed in this module. It is *not* a restatement of the goal: it speaks about
the cells of a cellulation, an object that has no Lean definition yet, and it is exactly the
invariant that another module is proving by induction over the two elementary operations. -/

/-- **`lem:cellulation-invariants`(i)** for a family `cells` of open 2-cells whose skeleton is
`K`: *a connected set disjoint from the skeleton lies in a single open 2-cell.*

Stated in the "meets, hence contained" reading, which is the form the proof of
`lem:polygonal-side-accessibility` uses and which packages the word *single* — with the usual
`∃`-reading one still has to know that distinct 2-cells are disjoint before concluding that the
cell found is the prescribed one. It is discharged by
`Schoenflies.cellsAbsorb_of_isComponent` (each 2-cell is a connected component of the
complement of the skeleton, which is what invariant (i) asserts) or, when the cells live inside
an ambient region whose frontier belongs to the skeleton, by
`Schoenflies.cellsAbsorb_of_isComponent_in`. -/
def CellsAbsorb (K : Set Plane) (cells : Set (Set Plane)) : Prop :=
  ∀ N : Set Plane, IsPreconnected N → Disjoint N K → ∀ R ∈ cells, (N ∩ R).Nonempty → N ⊆ R

/-- A connected set that misses the frontier of an open set and meets it lies inside it. -/
theorem subset_of_isPreconnected_of_frontier_disjoint (hQ : IsOpen Q) (hN : IsPreconnected N)
    (hfr : Disjoint N (frontier Q)) (hmeet : (N ∩ Q).Nonempty) : N ⊆ Q := by
  have hcover : N ⊆ Q ∪ (closure Q)ᶜ := by
    intro w hw
    by_cases hwQ : w ∈ Q
    · exact Or.inl hwQ
    · refine Or.inr fun hcl => Set.disjoint_left.1 hfr hw ?_
      rw [hQ.frontier_eq]
      exact ⟨hcl, hwQ⟩
  have hempty : ¬ (N ∩ (closure Q)ᶜ).Nonempty := by
    intro hne
    obtain ⟨w, -, hwQ, hwc⟩ :=
      hN Q (closure Q)ᶜ hQ isClosed_closure.isOpen_compl hcover hmeet hne
    exact hwc (subset_closure hwQ)
  intro w hw
  rcases hcover hw with hq | hc
  · exact hq
  · exact absurd ⟨w, hw, hc⟩ hempty

/-- **The discharger on the target side**: the 2-cells are the connected components of what is
left of an ambient open region `Q` after the skeleton is removed, and the frontier of `Q`
belongs to the skeleton. The second clause is what stops a sector from leaking out of `Q`; in
the blueprint it is `thm:polygonal-jordan` applied to the square boundary, and here it is
`Schoenflies.subset_of_isPreconnected_of_frontier_disjoint`. -/
theorem cellsAbsorb_of_isComponent_in (hQ : IsOpen Q) (hQK : frontier Q ⊆ K)
    {cells : Set (Set Plane)}
    (h : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ K) z) : CellsAbsorb K cells := by
  rintro N hN hdisj R hR ⟨w, hwN, hwR⟩
  obtain ⟨hRQ, z, rfl⟩ := h R hR
  have hNQ : N ⊆ Q := subset_of_isPreconnected_of_frontier_disjoint hQ hN
    (hdisj.mono_right hQK) ⟨w, hwN, hRQ hwR⟩
  rw [connectedComponentIn_eq hwR]
  exact hN.subset_connectedComponentIn hwN
    fun v hv => ⟨hNQ hv, Set.disjoint_left.1 hdisj hv⟩

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

/-- **At least one sector lies in `F`.** The clause of `lem:polygonal-side-accessibility` that
`Graph.exists_access_sector` was credited with and does not prove: the sector containing a point
`y` of the 2-cell `F` lies wholly inside `F`.

The reasoning is the blueprint's, once the disk has been shrunk below the distance to the wild
set `C`: the sector is connected and misses the whole skeleton `K = |G| ∪ C`, so by
`lem:cellulation-invariants`(i) it lies in a single 2-cell, and that cell is `F` because the
sector meets `F` at `y`. -/
theorem localSector_subset_cell (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells)
    (hballC : Disjoint (ball x r) C) (hy : y ∈ ball x r) (hyF : y ∈ F)
    (hyS : y ∉ pointSet G drawing) :
    connectedComponentIn (ball x r \ pointSet G drawing) y ⊆ F := by
  refine hcells _ isPreconnected_connectedComponentIn ?_ F hF
    ⟨y, mem_connectedComponentIn ⟨hy, hyS⟩, hyF⟩
  rw [Set.disjoint_left]
  intro w hw hwK
  have hwd := connectedComponentIn_subset _ _ hw
  rcases hK ▸ hwK with hwP | hwC
  · exact hwd.2 hwP
  · exact Set.disjoint_left.1 hballC hwd.1 hwC

end Graph
end

section
-- module Solutions.Q146_CD.Line
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lines in the plane

A line is the range of the parametrization `t ↦ lineMap a b t = a + t • (b - a)` through two
points. Taking the *range of the parametrization* as the definition, rather than
`affineSpan ℝ {a, b}`, is deliberate: every proof below transports a subset of the line to a
subset of `ℝ` and back, so the parametrization has to be available at once. `line_eq_affineSpan`
records that the two descriptions agree, for a consumer that meets a line as a span.

The transport is a homeomorphism, but it is never bundled as one. Instead the inverse
`lineCoord a b x = ⟪x - a, b - a⟫ / ‖b - a‖²` is defined on the whole plane, is continuous
there, and is a two-sided inverse of the parametrization on the line (`lineCoord_lineMap`,
`lineMap_lineCoord`). Pushing a subset of the line forward along `lineCoord` and pulling it back
along `lineMap` is all that the arguments below need, and no subspace topology ever appears.

The two facts Appendix C item 1 asks for:

* a nondegenerate compact connected subset of a line is a closed segment;
* a component of the intersection of a line with a bounded open set is a bounded open segment,
  whose closure is a closed segment with endpoints in the *frontier* of the open set.

The second is what manufactures crosscuts — the blueprint uses it twice in the proof of the
`K₃,₃`-subdivision corollary ("the closure `E` of the component of `ℓ ∩ F` containing `y` is a
crosscut of `F`") — so its endpoint conclusion is stated as membership in `frontier U`, and not
merely in `closure U`.

## Blueprint

* `Plane.line`, `Plane.lineCoord` — Appendix C, item 1 (lines and their parametrization).
* `Plane.exists_segment_eq_of_isCompact_isConnected`,
  `Plane.exists_segment_eq_of_not_subsingleton` — Appendix C, item 1: a nondegenerate compact
  connected subset of a line is a closed segment.
* `Plane.exists_openSegment_eq_connectedComponentIn` — Appendix C, item 1: a component of the
  intersection of a line with a bounded open set is an open segment whose closure is a closed
  segment with endpoints in the frontier of the open set.
* `Plane.eqOn_line_of_fixed` — Appendix C, item 1: an affine map fixing two points of a line
  fixes that line pointwise.
* `Plane.affineMap_ext_of_affineIndependent` — Appendix C, item 1: an affine map of the plane is
  determined by its values at three affinely independent points.

`exists_Ioo_eq_connectedComponentIn` is the one-dimensional core: a component of a bounded open
subset of `ℝ` is an open interval whose endpoints are outside the set.
-/

open Bornology Metric Set

namespace Schoenflies

/-! ### The real line

A component of a bounded open subset of `ℝ` is a bounded open interval whose endpoints are
missing from the set. Everything the plane statement says about a component of `ℓ ∩ U` is this
fact transported along the parametrization. -/

namespace Plane

variable {a b x y : Plane} {S U : Set Plane}

/-! ### Lines and their parametrization -/

/-- The line through `a` and `b`: the range of the parametrization `t ↦ a + t • (b - a)`.
For `a = b` this degenerates to the single point `{a}`; the lemmas that need a genuine line take
`a ≠ b` as a hypothesis. -/
def line (a b : Plane) : Set Plane := Set.range (AffineMap.lineMap a b : ℝ → Plane)

/-- The coordinate of a point on the line through `a` and `b`: the inverse of the
parametrization. It is defined on the whole plane — off the line it returns the parameter of the
orthogonal projection, which is harmless and buys continuity everywhere. -/
noncomputable def lineCoord (a b x : Plane) : ℝ := inner ℝ (x - a) (b - a) / ‖b - a‖ ^ 2

theorem lineMap_mem_line (a b : Plane) (t : ℝ) : AffineMap.lineMap a b t ∈ line a b :=
  mem_range_self t

@[simp] theorem left_mem_line (a b : Plane) : a ∈ line a b :=
  ⟨0, AffineMap.lineMap_apply_zero a b⟩

@[simp] theorem right_mem_line (a b : Plane) : b ∈ line a b :=
  ⟨1, AffineMap.lineMap_apply_one a b⟩

theorem continuous_lineCoord (a b : Plane) : Continuous (lineCoord a b) := by
  unfold lineCoord
  fun_prop

/-- `lineCoord` inverts the parametrization on the left. -/
@[simp] theorem lineCoord_lineMap (hab : a ≠ b) (t : ℝ) :
    lineCoord a b (AffineMap.lineMap a b t) = t := by
  have hne : ‖b - a‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, sub_eq_zero]
    exact fun h => hab h.symm
  have hsub : (AffineMap.lineMap a b t : Plane) - a = t • (b - a) := by
    rw [AffineMap.lineMap_apply_module']
    abel
  rw [lineCoord, hsub, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- `lineCoord` inverts the parametrization on the right, on the line. This needs no
nondegeneracy hypothesis: for `a = b` both sides are `a`. -/
theorem lineMap_lineCoord (hx : x ∈ line a b) :
    AffineMap.lineMap a b (lineCoord a b x) = x := by
  obtain ⟨t, rfl⟩ := hx
  rcases eq_or_ne a b with rfl | hab
  · simp
  · rw [lineCoord_lineMap hab]

theorem lineMap_injective (hab : a ≠ b) :
    Function.Injective (AffineMap.lineMap a b : ℝ → Plane) :=
  Function.LeftInverse.injective (g := lineCoord a b) (lineCoord_lineMap hab)

/-! ### A compact connected subset of a line is a segment -/

/-! ### A component of a line inside a bounded open set -/

/-- Appendix C, item 1. A connected component of the intersection of a line with a bounded open
set `U` is an open segment of the line; its closure is the closed segment on the same two
distinct endpoints, and both endpoints lie in the frontier of `U`.

This is the crosscut factory: the closed segment meets `U` in exactly the component, and touches
`∂U` exactly at its two ends. -/
theorem exists_openSegment_eq_connectedComponentIn (hab : a ≠ b) (hU : IsOpen U)
    (hbdd : IsBounded U) (hy : y ∈ line a b ∩ U) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ line a b ∧ q ∈ line a b ∧
      connectedComponentIn (line a b ∩ U) y = openSegment ℝ p q ∧
      closure (connectedComponentIn (line a b ∩ U) y) = segment ℝ p q ∧
      p ∈ frontier U ∧ q ∈ frontier U := by
  set f : ℝ → Plane := (AffineMap.lineMap a b : ℝ → Plane) with hfdef
  -- Pull `U` back to the parameter line. It stays open, and stays bounded because the
  -- parametrization scales all distances by the fixed positive factor `dist a b`.
  set T : Set ℝ := f ⁻¹' U with hTdef
  have hTopen : IsOpen T := hU.preimage AffineMap.lineMap_continuous
  have hTbdd : IsBounded T := by
    have hpos : 0 < dist a b := dist_pos.2 hab
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
    refine Metric.isBounded_iff.2 ⟨C / dist a b, fun s hs t ht => ?_⟩
    have h1 : dist s t * dist a b ≤ C := by
      have h2 := hC hs ht
      rwa [hfdef, dist_lineMap_lineMap] at h2
    exact (le_div_iff₀ hpos).2 h1
  set s : ℝ := lineCoord a b y with hsdef
  have hfs : f s = y := lineMap_lineCoord hy.1
  have hsT : s ∈ T := by rw [hTdef, mem_preimage, hfs]; exact hy.2
  obtain ⟨t₀, t₁, hlt, hJ, hn0, hn1⟩ := exists_Ioo_eq_connectedComponentIn hTopen hTbdd hsT
  have hIooT : Ioo t₀ t₁ ⊆ T := hJ ▸ connectedComponentIn_subset T s
  have hsIoo : s ∈ Ioo t₀ t₁ := hJ ▸ mem_connectedComponentIn hsT
  -- The component upstairs is the image of the component downstairs.
  have hC : connectedComponentIn (line a b ∩ U) y = f '' Ioo t₀ t₁ := by
    refine subset_antisymm (fun z hz => ?_) ?_
    · -- The coordinates of the component form a connected subset of `T` through `s`.
      have hzmem : z ∈ line a b ∩ U := connectedComponentIn_subset _ _ hz
      have hsubT : lineCoord a b '' connectedComponentIn (line a b ∩ U) y ⊆ T := by
        rintro _ ⟨w, hw, rfl⟩
        have hwmem : w ∈ line a b ∩ U := connectedComponentIn_subset _ _ hw
        rw [hTdef, mem_preimage, hfdef, lineMap_lineCoord hwmem.1]
        exact hwmem.2
      have hpre : IsPreconnected (lineCoord a b '' connectedComponentIn (line a b ∩ U) y) :=
        isPreconnected_connectedComponentIn.image _ (continuous_lineCoord a b).continuousOn
      have hsub := hpre.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hy, hsdef.symm⟩
        hsubT
      rw [hJ] at hsub
      exact ⟨lineCoord a b z, hsub ⟨z, hz, rfl⟩, lineMap_lineCoord hzmem.1⟩
    · -- Conversely the image of `Ioo t₀ t₁` is a connected subset of `line a b ∩ U` through `y`.
      refine (isPreconnected_Ioo.image f
        AffineMap.lineMap_continuous.continuousOn).subset_connectedComponentIn ⟨s, hsIoo, hfs⟩ ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨lineMap_mem_line a b t, hIooT ht⟩
  -- An open interval of parameters is an open segment of the line.
  have himg : f '' Ioo t₀ t₁ = openSegment ℝ (f t₀) (f t₁) := by
    rw [← openSegment_eq_Ioo hlt, hfdef, image_openSegment]
  have hclos : closure (connectedComponentIn (line a b ∩ U) y) = segment ℝ (f t₀) (f t₁) := by
    rw [hC, himg, closure_openSegment]
  -- Each endpoint is in the closure of the component, hence in `closure U`, but not in `U`.
  have hsubclos : closure (connectedComponentIn (line a b ∩ U) y) ⊆ closure U :=
    closure_mono fun z hz => (connectedComponentIn_subset _ _ hz).2
  have hfrontier : ∀ t : ℝ, t ∉ T → f t ∈ segment ℝ (f t₀) (f t₁) → f t ∈ frontier U := by
    intro t ht hseg
    rw [hU.frontier_eq]
    exact ⟨hsubclos (by rw [hclos]; exact hseg), fun h => ht h⟩
  exact ⟨f t₀, f t₁, fun h => hlt.ne (lineMap_injective hab h),
    lineMap_mem_line a b t₀, lineMap_mem_line a b t₁, by rw [hC, himg], hclos,
    hfrontier t₀ hn0 (left_mem_segment ℝ _ _), hfrontier t₁ hn1 (right_mem_segment ℝ _ _)⟩

/-! ### Affine maps -/

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- **The abstract record of the initial matched cellulation.** -/
def initialStructure : CellStructure InitialCell where
  skel := initSkel
  faces := InitialCell.faces
  outerGraph := initOuter
  outerGraph_le := initOuter_le_initSkel
  boundary := initBoundary
  sub := initSub
  finite_vertexSet := InitialCell.finite_vertices
  finite_edgeSet := InitialCell.finite_edges
  finite_faces := InitialCell.finite_faces
  disjoint_vertexSet_edgeSet := InitialCell.disjoint_vertices_edges
  disjoint_faces_vertexSet := InitialCell.disjoint_faces_vertices
  disjoint_faces_edgeSet := InitialCell.disjoint_faces_edges

@[simp] theorem initialStructure_skel : initialStructure.skel = initSkel := rfl

@[simp] theorem initialStructure_sub : initialStructure.sub = initSub := rfl

@[simp] theorem initialStructure_faces : initialStructure.faces = InitialCell.faces := rfl

@[simp] theorem initialStructure_outerGraph : initialStructure.outerGraph = initOuter := rfl

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


/-! ### The source realization: the curve with one polygonal crosscut

The source realization is the pushforward of the target's outer cycle along `w = u⁻¹`, together
with the polygonal crosscut `P` as its seventh edge. Nothing about the six outer arcs has to be
proved again: `w` is injective on `S`, so each of the three drawing conditions transfers.

The crosscut arrives as a parametrization together with the one geometric fact `lem:accessible-
endpoints` supplies — that every point of it other than its two ends lies in `D` — from which
`P ∩ C = {a, b}` follows, and with it the last meeting condition. -/


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

/-! ### `prop:initial-pair`: an initial matched pair exists

The two open corner arcs the blueprint chooses `a` and `b` from are the relative interiors of
two *opposite* sides of the square, pulled back by `u`. They are relatively open in `C` and
nonempty, so the countable dense set of strongly accessible points of
`prop:countable-strong-access` meets both; `lem:tangent-cone` and `lem:accessible-endpoints`
then supply the polygonal crosscut. -/


end Schoenflies
end

section
-- module Solutions.Q146_CD.FreshAccess
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.isArcList_nil _root_.Schoenflies.isArcList_singleton _root_.Schoenflies.lastP_cons _root_.Schoenflies.lastP_nil _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Access from a fresh anchor, for `thm:finite-transfer`(b)

Direction (b) of `thm:finite-transfer` transfers a target refinement back to the source. Every
step of its induction is the same as direction (a)'s except one: when the target ear starts at
a point of `S`, that point is by hypothesis a fresh image `u(a)` of an anchor `a ∈ 𝒜`, and the
*source* endpoint `a` lies on the wild curve `C`, where no polygonal skeleton reaches it and
`lem:polygonal-side-accessibility` says nothing. The blueprint's paragraph is:

> The union `K` of all old closed nonboundary edges and the finitely many source ears already
> inserted is compact and does not contain `a`. By `lem:tangent-cone`, a tangent disk at `a`
> contains an open cone of access segments. By `lem:compact-separation`(c), shrink that cone
> until it misses `K`. Its punctured part is connected, lies in the complement of the current
> skeleton, and accumulates at `a`; therefore it lies in the unique current source 2-cell just
> identified. It supplies the required access arc.

That paragraph is proved here, end to end, as `Schoenflies.polyAccessible_of_stronglyAccessible`.

## The three facts about the cone that the paragraph needs

`Schoenflies.accessCone` is on `main` (`Schoenflies/Accessible.lean`) with its openness, its
truncation, and `StronglyAccessible.exists_cone` — a cone of *any* radius below the radius of
the tangent disk lies in the domain, which is exactly the shrinking the paragraph performs.
What was missing is the three properties that make it usable as the connected set of
`lem:cellulation-invariants`(i):

* it is **convex**, hence preconnected (`convex_accessCone`, `isPreconnected_accessCone`) —
  the condition `‖x - p‖/2 < ⟪v, x - p⟫` is the superlevel set of a concave function and the
  truncation is a ball;
* the apex is in its **closure** (`mem_closure_accessCone`) — this is "accumulates at `a`",
  and it is what identifies the cell;
* it contains a straight **access segment** from the apex (`polyAccessible_accessCone`), which
  is `Schoenflies.PolyAccessible` in the shape `lem:accessible-endpoints` consumes.

Note that no *puncturing* is needed: `Schoenflies.notMem_accessCone` says the apex is not in the
cone to begin with, so the blueprint's "its punctured part" is the cone itself.

## Which 2-cell, and why that is a hypothesis

"Therefore it lies in the unique current source 2-cell just identified" has two halves. That the
cone lies in *some* 2-cell is proved here, from `Schoenflies.CellsAbsorb` — the same single
hypothesis `Schoenflies/SkeletonAccess.lean` carries, discharged by
`Schoenflies.cellsAbsorb_of_isComponent` or `.cellsAbsorb_of_isComponent_in` — together with a
covering clause. That the cell is the *prescribed* one is the separate combinatorial paragraph
of the blueprint ("each of the resulting outer subedges is incident with exactly one source
2-cell … hence exactly one descendant 2-cell remains incident with `a`"), an induction over the
ear sequence, and it enters here as the hypothesis `hunique`: *the only cell whose closure
contains `a` is `F`*. That is a statement about the ear induction, not about the geometry of the
cone, and the induction is what will discharge it.

## Blueprint

* `Schoenflies.convex_accessCone`, `Schoenflies.isPreconnected_accessCone`,
  `Schoenflies.mem_closure_accessCone`, `Schoenflies.polyAccessible_accessCone` — the three
  properties of the cone of `lem:tangent-cone` that `thm:finite-transfer`(b) uses.
* `Schoenflies.exists_accessCone_disjoint` — "by `lem:compact-separation`(c), shrink that cone
  until it misses `K`", combining `lem:tangent-cone` with `lem:compact-separation`(c).
* `Schoenflies.accessCone_subset_cell` — "its punctured part is connected, lies in the
  complement of the current skeleton, and accumulates at `a`; therefore it lies in the unique
  current source 2-cell", from `lem:cellulation-invariants`(i) in the `CellsAbsorb` reading.
* `Schoenflies.CellsAbsorbIn`, `Schoenflies.accessCone_subset_cell_in` — the domain-restricted
  form actually used in direction (b): the access cone already lies in the Jordan domain, so
  absorption is needed only for connected subsets of that domain.
* `Schoenflies.polyAccessible_of_stronglyAccessible` — the whole paragraph: a strongly
  accessible point of the wild curve is polygonally accessible from the current source 2-cell
  incident with it. This is the one input direction (b) needs beyond direction (a).
* `Schoenflies.polyAccessible_of_stronglyAccessible_in` — the same conclusion from the
  domain-restricted absorption interface.
-/

open Metric Set

namespace Schoenflies

variable {D K F N : Set Plane} {cells : Set (Set Plane)} {p v a z : Plane} {r s t ε : ℝ}

/-! ### The cone is convex

`accessCone p v s` is cut out of the ball `B(p, s)` by `‖x - p‖/2 < ⟪v, x - p⟫`. Both halves
are convex — the second because `y ↦ ⟪v, y⟫ - ‖y‖/2` is concave — so the cone is, and in
particular it is connected, which is what `lem:cellulation-invariants`(i) asks of it. -/

/-- The truncated access cone is convex. -/
theorem convex_accessCone (p v : Plane) (s : ℝ) : Convex ℝ (accessCone p v s) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ α β hα hβ hαβ
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  -- Abbreviations for the two distances and the two inner products.
  set A := ‖x - p‖ with hA
  set B := ‖y - p‖ with hB
  set Ix := inner ℝ v (x - p) with hIx
  set Iy := inner ℝ v (y - p) with hIy
  -- Everything happens in the translated coordinates.
  have hshift : α • x + (1 - α) • y - p = α • (x - p) + (1 - α) • (y - p) := by module
  have hnorm : ‖α • x + (1 - α) • y - p‖ ≤ α * A + (1 - α) * B := by
    rw [hshift]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα,
      abs_of_nonneg hβ]
  have hinner : inner ℝ v (α • x + (1 - α) • y - p) = α * Ix + (1 - α) * Iy := by
    rw [hshift, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  -- A convex combination lies between the minimum and the maximum of its two arguments.
  have hcomb : ∀ c d : ℝ, min c d ≤ α * c + (1 - α) * d ∧ α * c + (1 - α) * d ≤ max c d := by
    intro c d
    have h1 : α * min c d ≤ α * c := mul_le_mul_of_nonneg_left (min_le_left _ _) hα
    have h2 : (1 - α) * min c d ≤ (1 - α) * d := mul_le_mul_of_nonneg_left (min_le_right _ _) hβ
    have h3 : α * c ≤ α * max c d := mul_le_mul_of_nonneg_left (le_max_left _ _) hα
    have h4 : (1 - α) * d ≤ (1 - α) * max c d := mul_le_mul_of_nonneg_left (le_max_right _ _) hβ
    constructor <;> nlinarith
  refine ⟨hnorm.trans_lt (lt_of_le_of_lt (hcomb A B).2 (max_lt hx1 hy1)), ?_⟩
  -- The cone defect `⟪v, z⟫ - ‖z‖/2` is at least the minimum of the two defects, so positive.
  rw [hinner]
  have hdef : min (Ix - A / 2) (Iy - B / 2) ≤ α * (Ix - A / 2) + (1 - α) * (Iy - B / 2) :=
    (hcomb (Ix - A / 2) (Iy - B / 2)).1
  have hminpos : 0 < min (Ix - A / 2) (Iy - B / 2) :=
    lt_min (by linarith) (by linarith)
  nlinarith

/-- The truncated access cone is preconnected: it is convex. -/
theorem isPreconnected_accessCone (p v : Plane) (s : ℝ) :
    IsPreconnected (accessCone p v s) := (convex_accessCone p v s).isPreconnected

/-! ### The cone accumulates at its apex

`Schoenflies.notMem_accessCone` says the apex is *not* a point of the cone; this says it is a
limit of points of it. That is the blueprint's "accumulates at `a`", and it is what turns
"the cone lies in some 2-cell" into "the cone lies in a 2-cell incident with `a`". -/

/-- The inner product of a unit vector with itself clears the cone condition. Used three times
below, always to point the access segment along the axis of the cone. -/
theorem half_lt_inner_self (hv : ‖v‖ = 1) : 1 / 2 < inner ℝ v v := by
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

/-- The distance from the apex to a point of the axis. -/
theorem dist_apex_axis (hv : ‖v‖ = 1) (ht : 0 < t) : dist p (p + t • v) = t := by
  have hshift : p + t • v - p = t • v := by module
  rw [dist_comm, dist_eq_norm, hshift, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]

/-- The apex lies in the closure of its own access cone. -/
theorem mem_closure_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) : p ∈ closure (accessCone p v s) := by
  refine Metric.mem_closure_iff.2 fun ε hε => ⟨p + (min ε s / 2) • v, ?_, ?_⟩
  · have hpos : 0 < min ε s / 2 := by positivity
    have hlt : min ε s / 2 < s := by
      have := min_le_right ε s
      linarith
    exact mem_accessCone hv (half_lt_inner_self hv) hpos hlt
  · have hpos : 0 < min ε s / 2 := by positivity
    rw [dist_apex_axis hv hpos]
    have := min_le_left ε s
    linarith

/-- **The straight access segment.** The cone contains an open segment leaving the apex, so the
apex is polygonally accessible from anything containing the cone. This is `PolyAccessible` in
the shape `lem:accessible-endpoints` consumes. -/
theorem polyAccessible_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) (hsub : accessCone p v s ⊆ N) :
    PolyAccessible N p := by
  have hhalf : (0:ℝ) < s / 2 := by linarith
  have hmono : accessCone p v (s / 2) ⊆ accessCone p v s := accessCone_mono (by linarith)
  have hz : p + (s / 2) • v ∈ accessCone p v s :=
    mem_accessCone hv (half_lt_inner_self hv) hhalf (by linarith)
  refine PolyAccessible.of_openSegment (hsub hz) ?_
  exact ((openSegment_subset_accessCone hv (half_lt_inner_self hv) hhalf).trans hmono).trans hsub

/-! ### Shrinking the cone off the compact part already built -/

/-- **"Shrink that cone until it misses `K`."** A strongly accessible point off a compact set
has an access cone into the domain that is disjoint from that set. `lem:tangent-cone` supplies
the cone and `lem:compact-separation`(c) the radius. -/
theorem exists_accessCone_disjoint (h : StronglyAccessible D a) (hK : IsCompact K) (ha : a ∉ K) :
    ∃ (v : Plane) (s : ℝ), ‖v‖ = 1 ∧ 0 < s ∧ accessCone a v s ⊆ D ∧
      Disjoint (accessCone a v s) K := by
  obtain ⟨v, hv, r, hr, hcone⟩ := h.exists_cone
  obtain ⟨ρ, hρ, hball⟩ := Plane.exists_ball_subset_diff isOpen_univ hK ⟨mem_univ a, ha⟩
  refine ⟨v, min r ρ, hv, lt_min hr hρ, hcone _ (min_le_left _ _), ?_⟩
  refine Set.disjoint_left.2 fun x hx hxK => ?_
  exact (hball (accessCone_subset_ball_self (accessCone_mono (min_le_right r ρ) hx))).2 hxK

/-! ### Which cell the cone lies in -/

/-- Absorption by cells for connected sets already known to lie in an ambient domain.  This is
the precise form needed for a tangent cone inside a Jordan domain when `K` contains only the
closed nonboundary edges and not the wild boundary itself. -/
def CellsAbsorbIn (D K : Set Plane) (cells : Set (Set Plane)) : Prop :=
  ∀ N : Set Plane, N ⊆ D → IsPreconnected N → Disjoint N K →
    ∀ R ∈ cells, (N ∩ R).Nonempty → N ⊆ R

/-- The unique-cell argument with absorption required only inside the ambient domain. -/
theorem accessCone_subset_cell_in (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F)
    (hv : ‖v‖ = 1) (hs : 0 < s) (hD : accessCone a v s ⊆ D)
    (hdisj : Disjoint (accessCone a v s) K) :
    accessCone a v s ⊆ F := by
  obtain ⟨x, hx⟩ := accessCone_nonempty hv hs
  obtain ⟨R, hR, hxR⟩ := hcover x (hD hx) (Set.disjoint_left.1 hdisj hx)
  have hsub : accessCone a v s ⊆ R :=
    habs _ hD (isPreconnected_accessCone a v s) hdisj R hR ⟨x, hx, hxR⟩
  rw [← hunique R hR (closure_mono hsub (mem_closure_accessCone hv hs))]
  exact hsub

/-! ### The paragraph -/

/-- The fresh-anchor paragraph with the absorption invariant stated only inside the Jordan
domain, where the tangent cone is already known to lie. -/
theorem polyAccessible_of_stronglyAccessible_in (h : StronglyAccessible D a)
    (hK : IsCompact K) (ha : a ∉ K) (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F) :
    PolyAccessible F a := by
  obtain ⟨v, s, hv, hs, hD, hdisj⟩ := exists_accessCone_disjoint h hK ha
  exact polyAccessible_accessCone hv hs
    (accessCone_subset_cell_in habs hcover hunique hv hs hD hdisj)

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The frame of the square of radius `r` about the origin. For `r = 1` this is definitionally
`modelCurve`. -/
def ringSet (r : ℝ) : Set Plane := {x : Plane | Plane.supNorm x = r}

theorem ringSet_one : ringSet 1 = modelCurve := rfl

/-- The four sides of the square of radius `r`, as a list of pieces. -/
def ringPieces (r : ℝ) : List Piece :=
  [(Plane.mk r r, Plane.mk (-r) r),
   (Plane.mk (-r) r, Plane.mk (-r) (-r)),
   (Plane.mk (-r) (-r), Plane.mk r (-r)),
   (Plane.mk r (-r), Plane.mk r r)]

theorem mk_ne_mk_of_fst {a b c d : ℝ} (h : a ≠ c) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_zero a b, he, Plane.mk_zero] at h; exact h rfl

theorem mk_ne_mk_of_snd {a b c d : ℝ} (h : b ≠ d) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_one a b, he, Plane.mk_one] at h; exact h rfl

/-- A ring of positive radius has nondegenerate sides. -/
theorem ringPieces_nondeg {r : ℝ} (hr : 0 < r) : ∀ P ∈ ringPieces r, P.Nondeg := by
  have hne : (r : ℝ) ≠ -r := by intro h; linarith
  intro P hP
  simp only [ringPieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact mk_ne_mk_of_fst hne
  · exact mk_ne_mk_of_snd hne
  · exact mk_ne_mk_of_fst hne.symm
  · exact mk_ne_mk_of_snd hne.symm

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

theorem mem_smul_segment {a b : ℝ} {z x : Plane} :
    x ∈ segment ℝ (a • z) (b • z) ↔ ∃ t ∈ segment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

/-- The radial segment from `a • z` to `b • z`, as a set of multiples of `z`. -/
theorem smul_segment_eq_image {a b : ℝ} (hab : a ≤ b) (z : Plane) :
    segment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Icc a b := by
  ext x
  rw [mem_smul_segment, segment_eq_Icc hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

/-! ### Spokes -/

/-- The radial spoke at a boundary point `z`, running from `z` inwards to `N⁻¹ • z`. -/
noncomputable def spokePiece (N : ℕ) (z : Plane) : Piece := (z, ((N : ℝ)⁻¹) • z)

/-- A spoke is the set of multiples `t • z` with `N⁻¹ ≤ t ≤ 1`. -/
theorem spokePiece_seg {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    (spokePiece N z).seg = (fun t : ℝ => t • z) '' Icc ((N : ℝ)⁻¹) 1 := by
  have key : (spokePiece N z).seg = segment ℝ (((N : ℝ)⁻¹) • z) ((1 : ℝ) • z) := by
    rw [Piece.seg, spokePiece, one_smul, segment_symm]
  rw [key, smul_segment_eq_image (inv_cast_lt_one hN).le]

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

theorem cover_map {α : Type*} (f : α → Piece) (l : List α) :
    cover (l.map f) = ⋃ a ∈ l, (f a).seg := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, cover_cons, ih]; simp

theorem cover_flatMap' {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ a ∈ l, cover (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, cover_append, ih]; simp

theorem mem_cover_iff {x : Plane} {l : List Piece} : x ∈ cover l ↔ ∃ P ∈ l, x ∈ P.seg := by
  simp only [cover, mem_iUnion, exists_prop]

/-- Cutting a piece at a point of it makes that point an endpoint of one of the halves. -/
theorem splitAt_end_of_mem (p : Plane) (P : Piece) (hmem : p ∈ P.seg) :
    ∃ R ∈ splitAt p P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hp : p ∈ P.interior
  · refine ⟨(P.1, p), by rw [splitAt, if_pos hp]; simp, ?_, Or.inr rfl⟩
    exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hmem
  · refine ⟨P, by rw [splitAt, if_neg hp]; simp, subset_rfl, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hp (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hmem)

/-- Cutting anywhere keeps an endpoint an endpoint. -/
theorem splitAt_preserves_end (q : Plane) {p : Plane} {P : Piece} (h : p = P.1 ∨ p = P.2) :
    ∃ R ∈ splitAt q P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hq : q ∈ P.interior
  · have hqseg : q ∈ P.seg := openSegment_subset_segment ℝ _ _ hq
    rcases h with rfl | rfl
    · refine ⟨(P.1, q), by rw [splitAt, if_pos hq]; simp, ?_, Or.inl rfl⟩
      exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hqseg
    · refine ⟨(q, P.2), by rw [splitAt, if_pos hq]; simp, ?_, Or.inr rfl⟩
      exact (convex_segment P.1 P.2).segment_subset hqseg (right_mem_segment ℝ _ _)
  · exact ⟨P, by rw [splitAt, if_neg hq]; simp, subset_rfl, h⟩

theorem splitAllAt_preserves_end (q : Plane) {p : Plane} {P : Piece} {pieces : List Piece}
    (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ splitAllAt q pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  obtain ⟨R, hR, hsub, hend⟩ := h
  obtain ⟨R', hR', hsub', hend'⟩ := splitAt_preserves_end q hend
  exact ⟨R', List.mem_flatMap.2 ⟨R, hR, hR'⟩, hsub'.trans hsub, hend'⟩

theorem subdivide_preserves_end (points : List Plane) {pieces : List Piece} {p : Plane}
    {P : Piece} (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ subdivide pieces points, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  induction points generalizing pieces with
  | nil => exact h
  | cons q qs ih => exact ih (splitAllAt_preserves_end q h)

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

theorem EndsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : EndsAreCut pieces points) (hsub : points ⊆ points') : EndsAreCut pieces points' :=
  fun P hP z hz => hsub (h P hP z hz)

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

/-- The mesh: the four sides of each ring, and one radial spoke at each fresh point. -/
noncomputable def meshSegments (N : ℕ) (fresh : List Plane) : List Piece :=
  (meshRadii N).flatMap ringPieces ++ fresh.map (spokePiece N)

theorem mem_meshSegments {N : ℕ} {fresh : List Plane} {P : Piece} :
    P ∈ meshSegments N fresh ↔
      (∃ r ∈ meshRadii N, P ∈ ringPieces r) ∨ ∃ z ∈ fresh, P = spokePiece N z := by
  simp only [meshSegments, List.mem_append, List.mem_flatMap, List.mem_map]
  exact or_congr Iff.rfl ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

/-- A side of the outer ring is a mesh segment. -/
theorem outer_ringPieces_mem {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {R : Piece}
    (hR : R ∈ ringPieces 1) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨1, one_mem_meshRadii hN, hR⟩)

theorem spokePiece_mem_meshSegments {N : ℕ} {fresh : List Plane} {z : Plane} (hz : z ∈ fresh) :
    spokePiece N z ∈ meshSegments N fresh := mem_meshSegments.2 (Or.inr ⟨z, hz, rfl⟩)

/-! ### Clause 2: the anchors are vertices on `S` -/

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

theorem ringSet_disjoint_modelCurve {r : ℝ} (hr : r ≠ 1) : ringSet r ∩ modelCurve = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hxr hx1
  exact hr (hxr.symm.trans hx1)

theorem mem_smul_openSegment {a b : ℝ} {z x : Plane} :
    x ∈ openSegment ℝ (a • z) (b • z) ↔ ∃ t ∈ openSegment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

theorem smul_openSegment_eq_image {a b : ℝ} (hab : a < b) (z : Plane) :
    openSegment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Ioo a b := by
  ext x
  rw [mem_smul_openSegment, openSegment_eq_Ioo hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

/-- A nondegenerate subsegment of a spoke having the spoke's outer end `z` as an endpoint runs
from `z` inwards: its interior is `{t • z : t₀ < t < 1}` for some `t₀ < 1`. This is the whole
of "only one edge leaves `S` at a fresh point" — two such edges would overlap near `z`. -/
theorem spoke_subpiece_interior {N : ℕ} (hN : 2 ≤ N) {z : Plane}
    {P : Piece} (hnd : P.Nondeg) (hsub : P.seg ⊆ (spokePiece N z).seg)
    (hend : z = P.1 ∨ z = P.2) :
    ∃ t₀ : ℝ, t₀ < 1 ∧ P.interior = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
  have key : ∀ q : Plane, q ∈ (spokePiece N z).seg → q ≠ z →
      ∃ t₀ : ℝ, t₀ < 1 ∧ openSegment ℝ z q = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
    intro q hq hne
    rw [spokePiece_seg hN] at hq
    obtain ⟨t₀, ht₀, rfl⟩ := hq
    have hlt : t₀ < 1 := lt_of_le_of_ne ht₀.2 fun h => hne (by simp [h])
    refine ⟨t₀, hlt, ?_⟩
    have hz1 : openSegment ℝ z (t₀ • z) = openSegment ℝ (t₀ • z) ((1 : ℝ) • z) := by
      rw [one_smul, openSegment_symm]
    rw [hz1, smul_openSegment_eq_image hlt]
  rcases hend with h | h
  · obtain ⟨t₀, hlt, heq⟩ :=
      key P.2 (hsub (right_mem_segment ℝ _ _)) (by rw [h]; exact Ne.symm hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [← h, heq]⟩
  · obtain ⟨t₀, hlt, heq⟩ := key P.1 (hsub (left_mem_segment ℝ _ _)) (by rw [h]; exact hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [openSegment_symm, ← h, heq]⟩

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

theorem dist_le_sqrt_two_mul_supNorm (x y : Plane) :
    dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := by
  rw [dist_eq_norm]; exact Plane.norm_le_sqrt_two_mul_supNorm _

/-- The fresh points are `δ`-dense on `S`: every connected piece of `S` that avoids all of them
has diameter at most `δ/2`.

This is the hypothesis the blueprint discharges by "parametrize `S` by a circle, use uniform
continuity to cut it into arcs of diameter `< δ/8`, and pick one fresh point in the relative
interior of each". Stated as a property of a *set* rather than of a cyclic order, it needs no
ordering of the fresh points along `S` — which is what makes the whole mesh order-free. -/
def FreshDense (fresh : List Plane) (δ : ℝ) : Prop :=
  ∀ A : Set Plane, A ⊆ modelCurve \ {x | x ∈ fresh} → IsPreconnected A →
    ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ / 2

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-- A spoke with its outer endpoint removed. -/
noncomputable def halfSpoke (N : ℕ) (z : Plane) : Set Plane :=
  (fun t : ℝ => t • z) '' Ico ((N : ℝ)⁻¹) 1

theorem isConnected_halfSpoke {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    IsConnected (halfSpoke N z) :=
  (isConnected_Ico (inv_cast_lt_one hN)).image _
    (Continuous.continuousOn (continuous_id.smul continuous_const))

theorem halfSpoke_subset {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    halfSpoke N z ⊆ (spokePiece N z).seg := by
  rw [halfSpoke, spokePiece_seg hN]
  exact Set.image_mono Ico_subset_Icc_self

theorem smul_mem_halfSpoke {N : ℕ} {t : ℝ} (ht : (N : ℝ)⁻¹ ≤ t) (ht1 : t < 1) (z : Plane) :
    t • z ∈ halfSpoke N z := ⟨t, ⟨ht, ht1⟩, rfl⟩

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.chainUnion_succ _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The hub `K` with the pieces `Γ 0, …, Γ (m-1)` glued on, one at a time. -/
def attachUnion (K : Graph α β) (Γ : ℕ → Graph α β) : ℕ → Graph α β
  | 0 => K
  | (m + 1) => (attachUnion K Γ m).union (Γ m)

@[simp] theorem attachUnion_zero (K : Graph α β) (Γ : ℕ → Graph α β) :
    attachUnion K Γ 0 = K := rfl

@[simp] theorem attachUnion_succ (K : Graph α β) (Γ : ℕ → Graph α β) (m : ℕ) :
    attachUnion K Γ (m + 1) = (attachUnion K Γ m).union (Γ m) := rfl

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

/-- The graph whose edges are the listed segments and whose vertices are their ends. -/
def pieceListGraph (edges : List Piece) : Graph Plane Piece where
  vertexSet := endSet edges
  IsLink P x y := P ∈ edges ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ edges}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

@[simp] theorem pieceListGraph_vertexSet (l : List Piece) : V(pieceListGraph l) = endSet l := rfl

@[simp] theorem pieceListGraph_mem_edgeSet {l : List Piece} {P : Piece} :
    P ∈ E(pieceListGraph l) ↔ P ∈ l := Iff.rfl

@[simp] theorem pieceListGraph_isLink {l : List Piece} {P : Piece} {x y : Plane} :
    (pieceListGraph l).IsLink P x y ↔
      P ∈ l ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

/-- The canonical link of a listed segment: it joins its own two ends. -/
theorem pieceListGraph_isLink_self {l : List Piece} {P : Piece} (h : P ∈ l) :
    (pieceListGraph l).IsLink P P.1 P.2 := ⟨h, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_vertexSet_pieceListGraph_left {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.1 ∈ V(pieceListGraph l) := ⟨P, h, Or.inl rfl⟩

theorem mem_vertexSet_pieceListGraph_right {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.2 ∈ V(pieceListGraph l) := ⟨P, h, Or.inr rfl⟩

/-- An end of a listed segment is incident with it. -/
theorem pieceListGraph_inc {l : List Piece} {P : Piece} {v : Plane} (hP : P ∈ l)
    (h : v = P.1 ∨ v = P.2) : (pieceListGraph l).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-- Two plane points with the same coordinates are equal.

`Schoenflies.Plane.coord_ext` in `Schoenflies/JordanSeparates.lean` is the same fact in a more
general form; that module is not on this one's import path, and the integrator should collapse
the two if it ever is. -/
theorem plane_eq_of_coords {z w : Plane} (h0 : z 0 = w 0) (h1 : z 1 = w 1) : z = w := by
  ext k
  fin_cases k
  exacts [h0, h1]

theorem endSet_append (l l' : List Piece) : endSet (l ++ l') = endSet l ∪ endSet l' := by
  ext v
  simp only [endSet, Set.mem_setOf_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨P, hP | hP, h⟩
    exacts [Or.inl ⟨P, hP, h⟩, Or.inr ⟨P, hP, h⟩]
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    exacts [⟨P, Or.inl hP, h⟩, ⟨P, Or.inr hP, h⟩]

/-- What a segment graph occupies is what its segments occupy: every vertex is an end of a
listed segment, so the vertices add nothing. -/
theorem pieceListGraph_pointSet (l : List Piece) :
    Graph.pointSet (pieceListGraph l) segmentDrawing = cover l := by
  ext z
  simp only [Graph.pointSet, Set.mem_union, Set.mem_iUnion, exists_prop, pieceListGraph_vertexSet,
    endSet, Set.mem_setOf_eq, pieceListGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

theorem pieceListGraph_mono {l l' : List Piece} (h : l ⊆ l') :
    pieceListGraph l ≤ pieceListGraph l' where
  vertexSet_mono := by
    rintro v ⟨P, hP, hv⟩
    exact ⟨P, h hP, hv⟩
  isLink_mono := by
    rintro P x y ⟨hP, hxy⟩
    exact ⟨h hP, hxy⟩

/-- Two segment graphs never disagree about a shared edge: an edge is its own pair of ends. -/
theorem pieceListGraph_compatible (l l' : List Piece) :
    (pieceListGraph l).Compatible (pieceListGraph l') := by
  intro P hP hP' x y
  exact ⟨fun h => ⟨hP', h.2⟩, fun h => ⟨hP, h.2⟩⟩

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-- The grid point with coordinate indices `(i, j)`. -/
def gridPt (xc yc : ℕ → ℝ) (i j : ℕ) : Plane := Plane.mk (xc i) (yc j)

/-- The horizontal grid edge from `(i, j)` to `(i+1, j)`. -/
def gridHEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc (i + 1) j)

/-- The vertical grid edge from `(i, j)` to `(i, j+1)`. -/
def gridVEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc i (j + 1))

theorem gridPt_ne_of_fst {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : xc i ≠ xc i') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 0) he
  simp only [gridPt, Plane.mk_zero] at this
  exact h this

theorem gridPt_ne_of_snd {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : yc j ≠ yc j') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 1) he
  simp only [gridPt, Plane.mk_one] at this
  exact h this

/-- The four sides of the cell whose lower-left corner is `(i, j)`, listed bottom, right, top,
left. -/
def cellEdges (xc yc : ℕ → ℝ) (i j : ℕ) : List Piece :=
  [gridHEdge xc yc i j, gridVEdge xc yc (i + 1) j, gridHEdge xc yc i (j + 1),
    gridVEdge xc yc i j]

/-- One column of `n` cells, the cells `(i, 0), …, (i, n-1)`. -/
def stripEdges (xc yc : ℕ → ℝ) (i n : ℕ) : List Piece :=
  (List.range n).flatMap (cellEdges xc yc i)

/-- The `m × n` grid: `m` columns of `n` cells. -/
def gridEdges (xc yc : ℕ → ℝ) (m n : ℕ) : List Piece :=
  (List.range m).flatMap fun i => stripEdges xc yc i n

/-- **The grid graph**: the `m × n` rectangular grid on the coordinates `xc`, `yc`, as a plane
graph with straight edges. -/
def gridGraph (xc yc : ℕ → ℝ) (m n : ℕ) : Graph Plane Piece := pieceListGraph (gridEdges xc yc m n)

theorem stripEdges_succ (xc yc : ℕ → ℝ) (i n : ℕ) :
    stripEdges xc yc i (n + 1) = stripEdges xc yc i n ++ cellEdges xc yc i n := by
  rw [stripEdges, stripEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem stripEdges_one (xc yc : ℕ → ℝ) (i : ℕ) :
    stripEdges xc yc i 1 = cellEdges xc yc i 0 := by
  rw [stripEdges_succ]; simp [stripEdges]

theorem cellEdges_subset_stripEdges {xc yc : ℕ → ℝ} {i j n : ℕ} (h : j < n) :
    cellEdges xc yc i j ⊆ stripEdges xc yc i n :=
  fun _ hP => List.mem_flatMap.2 ⟨j, List.mem_range.2 h, hP⟩

theorem gridEdges_succ (xc yc : ℕ → ℝ) (m n : ℕ) :
    gridEdges xc yc (m + 1) n = gridEdges xc yc m n ++ stripEdges xc yc m n := by
  rw [gridEdges, gridEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem gridEdges_one (xc yc : ℕ → ℝ) (n : ℕ) :
    gridEdges xc yc 1 n = stripEdges xc yc 0 n := by
  rw [gridEdges_succ]; simp [gridEdges]

theorem stripEdges_subset_gridEdges {xc yc : ℕ → ℝ} {i m n : ℕ} (h : i < m) :
    stripEdges xc yc i n ⊆ gridEdges xc yc m n :=
  fun _ hP => List.mem_flatMap.2 ⟨i, List.mem_range.2 h, hP⟩

/-! ### The cell -/

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

/-! ### Which grid edges exist

Two membership lemmas, both by the same trick: a horizontal edge at height `n` is the *top*
of a cell rather than the bottom of one, and a vertical edge on the line `i = m` is the *right*
side of a cell rather than the left. -/

theorem gridHEdge_mem_gridEdges {xc yc : ℕ → ℝ} {i j m n : ℕ} (hi : i < m) (hj : j ≤ n)
    (hn : 1 ≤ n) : gridHEdge xc yc i j ∈ gridEdges xc yc m n := by
  rcases lt_or_ge j n with h | h
  · exact stripEdges_subset_gridEdges hi (cellEdges_subset_stripEdges h (by simp [cellEdges]))
  · obtain rfl : j = n := le_antisymm hj h
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact stripEdges_subset_gridEdges hi
      (cellEdges_subset_stripEdges (Nat.lt_succ_self k) (by simp [cellEdges]))

theorem gridVEdge_mem_gridEdges {xc yc : ℕ → ℝ} {i j m n : ℕ} (hi : i ≤ m) (hj : j < n)
    (hm : 1 ≤ m) : gridVEdge xc yc i j ∈ gridEdges xc yc m n := by
  rcases lt_or_ge i m with h | h
  · exact stripEdges_subset_gridEdges h (cellEdges_subset_stripEdges hj (by simp [cellEdges]))
  · obtain rfl : i = m := le_antisymm hi h
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact stripEdges_subset_gridEdges (Nat.lt_succ_self k)
      (cellEdges_subset_stripEdges hj (by simp [cellEdges]))

/-- **The edges of the grid, classified.** A grid edge is a horizontal step in a row, or a
vertical step in a column, and nothing else. -/
theorem mem_gridEdges_iff {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece} :
    P ∈ gridEdges xc yc m n ↔
      (∃ i < m, ∃ j ≤ n, P = gridHEdge xc yc i j) ∨
        ∃ i ≤ m, ∃ j < n, P = gridVEdge xc yc i j := by
  constructor
  · intro hP
    obtain ⟨i, hi, hPi⟩ := List.mem_flatMap.1 hP
    obtain ⟨j, hj, hPj⟩ := List.mem_flatMap.1 hPi
    rw [List.mem_range] at hi hj
    simp only [cellEdges, List.mem_cons, List.not_mem_nil, or_false] at hPj
    rcases hPj with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i, hi, j, by omega, rfl⟩
    · exact Or.inr ⟨i + 1, by omega, j, hj, rfl⟩
    · exact Or.inl ⟨i, hi, j + 1, by omega, rfl⟩
    · exact Or.inr ⟨i, by omega, j, hj, rfl⟩
  · rintro (⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩)
    · exact gridHEdge_mem_gridEdges hi hj hn
    · exact gridVEdge_mem_gridEdges hi hj hm

/-- **The vertices of the grid are exactly the grid points.** -/
theorem mem_vertexSet_gridGraph_iff {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {v : Plane} :
    v ∈ V(gridGraph xc yc m n) ↔ ∃ i ≤ m, ∃ j ≤ n, v = gridPt xc yc i j := by
  constructor
  · rintro ⟨P, hP, hv⟩
    rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
    · rcases hv with rfl | rfl
      exacts [⟨i, by omega, j, hj, rfl⟩, ⟨i + 1, by omega, j, hj, rfl⟩]
    · rcases hv with rfl | rfl
      exacts [⟨i, hi, j, by omega, rfl⟩, ⟨i, hi, j + 1, by omega, rfl⟩]
  · rintro ⟨i, hi, j, hj, rfl⟩
    -- a grid point is an end of the horizontal edge on one side of it
    rcases lt_or_ge i m with h | h
    · exact mem_vertexSet_pieceListGraph_left (gridHEdge_mem_gridEdges h hj hn)
    · obtain rfl : i = m := le_antisymm hi h
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      exact mem_vertexSet_pieceListGraph_right (gridHEdge_mem_gridEdges (Nat.lt_succ_self k) hj hn)

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

theorem iUnion_Icc_chain {f : ℕ → ℝ} : ∀ m : ℕ, 1 ≤ m → (∀ i, i < m → f i ≤ f (i + 1)) →
    (⋃ i ∈ Set.Iio m, Set.Icc (f i) (f (i + 1))) = Set.Icc (f 0) (f m) := by
  intro m
  induction m with
  | zero => exact fun h => absurd h (by omega)
  | succ m ih =>
    intro _ hmono
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hsplit : (⋃ i ∈ Set.Iio (m + 1), Set.Icc (f i) (f (i + 1)))
          = (⋃ i ∈ Set.Iio m, Set.Icc (f i) (f (i + 1))) ∪ Set.Icc (f m) (f (m + 1)) := by
        ext z
        simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
          exacts [Or.inl ⟨i, h, hz⟩, Or.inr hz]
        · rintro (⟨i, hi, hz⟩ | hz)
          exacts [⟨i, by omega, hz⟩, ⟨m, by omega, hz⟩]
      rw [hsplit, ih hm fun i hi => hmono i (by omega),
        Set.Icc_union_Icc_eq_Icc (chain_le_of_le hmono 0 m (by omega) (by omega))
          (hmono m (by omega))]

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

theorem idx_le_of_coord_le {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (h : f a ≤ f b) : a ≤ b := by
  by_contra hcon
  exact absurd (hf hb ha (by omega)) (by simpa using h)

/-- **Reading an index off a coordinate.** -/
theorem idx_of_coord_mem {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a i : ℕ}
    (ha : a ≤ N) (hi : i + 1 ≤ N) (h₁ : f i ≤ f a) (h₂ : f a ≤ f (i + 1)) :
    a = i ∨ a = i + 1 := by
  have := idx_le_of_coord_le hf (by omega) ha h₁
  have := idx_le_of_coord_le hf ha hi h₂
  omega

variable {xc yc : ℕ → ℝ} {m n : ℕ}

/-- A grid edge is nondegenerate: its two ends differ in one coordinate. -/
theorem gridEdges_nondeg (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece} (hP : P ∈ gridEdges xc yc m n) : P.Nondeg := by
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact gridPt_ne_of_fst
      (ne_of_lt (hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))
  · exact gridPt_ne_of_snd
      (ne_of_lt (hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshFixed
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-! ### Concatenating two paths

`Schoenflies/Graph/Walk.lean` has `Graph.IsWalk.append` and no path analogue, because nothing
before this needed one. The general lemma is here; the integrator should hoist it. -/

namespace Schoenflies

/-! ### The subdivision hypothesis

The one general fact about `overlayGraph` that `Schoenflies/SquareMeshConnected.lean` names as
missing, stated as a `Prop` so that the axiom audit stays a real guarantee and the defect shows
up at the consumer. It is *believed*: the pieces of the subdivision of a nondegenerate segment
have pairwise disjoint interiors and cover it, so the distance from `P.1` orders them into a
chain running from `P.1` to `P.2`. Nothing about the mesh appears in it. -/

/-- **The overlay subdivides each source segment into a path.** For each nondegenerate source
segment `P` there is an ordering `W` of *exactly* the overlay edges lying inside `P` which is a
path of the overlay from `P.1` to `P.2`. -/
def SubdividesToPath (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, P.Nondeg → ∃ W : List Piece,
    (overlayGraph pieces points).IsPath P.1 W P.2 ∧
      ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)

/-- A vertex an overlay walk visits lies wherever its source and its edges lie. -/
theorem walkVertices_subset_of_edges {pieces : List Piece} {points : List Plane}
    {A : Set Plane} {u : Plane} {W : List Piece} (hu : u ∈ A) (hW : ∀ Q ∈ W, Q.seg ⊆ A)
    {x : Plane} (hx : x ∈ (overlayGraph pieces points).walkVertices u W) : x ∈ A := by
  rcases Graph.mem_walkVertices_iff.1 hx with rfl | ⟨Q, hQ, hinc⟩
  · exact hu
  · obtain ⟨y, -, hends⟩ := hinc
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [hW Q hQ (left_mem_segment ℝ _ _), hW Q hQ (right_mem_segment ℝ _ _)]

/-! ### The four sides of the outer ring

Names for the four sides of `ringPieces 1` and the six pairwise intersections. Two opposite
sides are disjoint; two adjacent ones meet in their common corner. Everything is
`mem_segment_horiz` / `mem_segment_vert` and `plane_eq_of_coords`. -/

/-- The top side of `S`, from the north-east corner to the north-west one. -/
def sideT : Piece := (Plane.mk 1 1, Plane.mk (-1) 1)

/-- The left side of `S`. -/
def sideL : Piece := (Plane.mk (-1) 1, Plane.mk (-1) (-1))

/-- The bottom side of `S`. -/
def sideB : Piece := (Plane.mk (-1) (-1), Plane.mk 1 (-1))

/-- The right side of `S`, from the south-east corner back to the north-east one. -/
def sideR : Piece := (Plane.mk 1 (-1), Plane.mk 1 1)

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.k33Graph_edgeSet _root_.Graph.k33Graph_vertexSet _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.reverse_vertex _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.Plane.left_mem_line _root_.Schoenflies.Plane.lineCoord_lineMap _root_.Schoenflies.Plane.right_mem_line _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arcPieces_zero _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre _root_.Schoenflies.PrePolygon.reverse_carrier _root_.Schoenflies.PrePolygon.reverse_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
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

/-- The sup distance is at most the Euclidean distance. -/
theorem supDist_le_dist (x y : Plane) : Plane.supDist x y ≤ dist x y := by
  rw [dist_eq_norm]
  exact Plane.supNorm_le_norm _

/-! ### What does repair clause 5

A side of `S` is a connected subset of `S` whose two ends are `2` apart. If no two fresh points
are distinct then some side avoids all of them — a single point cannot lie on both the top and
the bottom side — and `FreshDense fresh δ` applied to that side forces `4 ≤ δ`. -/

/-- The two ends of the top or the bottom side of `S` are at distance at least `2`. -/
theorem two_le_dist_side {P : Piece} (h : P = sideT ∨ P = sideB) : (2 : ℝ) ≤ dist P.1 P.2 := by
  refine le_trans (le_of_eq ?_) (supDist_le_dist P.1 P.2)
  rcases h with rfl | rfl <;>
    · simp only [sideT, sideB, Plane.supDist, Plane.supNorm, Plane.sub_apply]
      norm_num

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

/-- The `x`-coordinates of the local grid on the closed square of centre `p` and radius `s`,
cut into `k` intervals. -/
noncomputable def localGridX (p : Plane) (s : ℝ) (k : ℕ) : ℕ → ℝ :=
  uniformCoord (p 0 - s) (2 * s / k)

/-- The `y`-coordinates of the local grid. -/
noncomputable def localGridY (p : Plane) (s : ℝ) (k : ℕ) : ℕ → ℝ :=
  uniformCoord (p 1 - s) (2 * s / k)

/-- The edges of the local grid, as a list of segments. -/
noncomputable def localGridEdges (p : Plane) (s : ℝ) (k : ℕ) : List Piece :=
  gridEdges (localGridX p s k) (localGridY p s k) k k

/-- **The local grid** of `prop:local-grid-attachment`: the uniform `k × k` rectangular grid on
the closed square `W` of centre `p` and radius `s`. -/
noncomputable def localGrid (p : Plane) (s : ℝ) (k : ℕ) : Graph Plane Piece :=
  gridGraph (localGridX p s k) (localGridY p s k) k k

theorem localGrid_eq (p : Plane) (s : ℝ) (k : ℕ) :
    localGrid p s k = pieceListGraph (localGridEdges p s k) := rfl

theorem localGridX_strictMono (hs : 0 < s) (hk : 1 ≤ k) :
    StrictMono (localGridX p s k) := uniformCoord_strictMono (localGrid_step_pos hs hk) _

theorem localGridY_strictMono (hs : 0 < s) (hk : 1 ≤ k) :
    StrictMono (localGridY p s k) := uniformCoord_strictMono (localGrid_step_pos hs hk) _

@[simp] theorem localGridX_zero (p : Plane) (s : ℝ) (k : ℕ) :
    localGridX p s k 0 = p 0 - s := uniformCoord_zero _ _

@[simp] theorem localGridY_zero (p : Plane) (s : ℝ) (k : ℕ) :
    localGridY p s k 0 = p 1 - s := uniformCoord_zero _ _

theorem localGridX_last (hk : 1 ≤ k) : localGridX p s k k = p 0 + s := by
  have hkR : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact ne_of_gt this
  simp only [localGridX, uniformCoord]
  field_simp
  ring

theorem localGridY_last (hk : 1 ≤ k) : localGridY p s k k = p 1 + s := by
  have hkR : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact ne_of_gt this
  simp only [localGridY, uniformCoord]
  field_simp
  ring

/-! ### Fineness

The one quantitative clause: every closed grid rectangle is smaller than `ε`. Stated twice —
for the closed rectangle itself, which is the blueprint's wording, and for any connected subset
of `W` that avoids the grid, which is the form a face of the overlay arrives in. -/

theorem dist_lt_of_supNorm_bounds {x y : Plane} {c : ℝ} (h0 : |x 0 - y 0| < c)
    (h1 : |x 1 - y 1| < c) : dist x y < Real.sqrt 2 * c := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  refine lt_of_le_of_lt (dist_le_sqrt_two_mul_supNorm x y) (mul_lt_mul_of_pos_left ?_ hsq)
  simp only [Plane.supNorm, Plane.sub_apply]
  exact max_lt h0 h1

/-! ### Choosing the mesh

`prop:local-grid-attachment` clause 3 asks for rectangles of diameter `< ε`. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.GridAttach
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.decidableCrosses
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

/-- **The crosscut of a face along a line.** A face `F` (open, bounded) met by a line `ℓ` at `y`
supplies a segment `[q₀, q₁]` with distinct ends on `∂F`, open part inside `F`, containing `y` —
and containing every connected subset of `ℓ ∩ F` through `y`, which is how the blueprint's chosen
grid edge `J` ends up inside the crosscut. -/
theorem exists_crosscut (hab : a ≠ b) (hFopen : IsOpen F) (hFbdd : Bornology.IsBounded F)
    (hy : y ∈ Plane.line a b ∩ F) :
    ∃ q₀ q₁ : Plane, q₀ ≠ q₁ ∧ q₀ ∈ frontier F ∧ q₁ ∈ frontier F ∧
      openSegment ℝ q₀ q₁ ⊆ F ∧ y ∈ openSegment ℝ q₀ q₁ ∧
      ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
        S ⊆ openSegment ℝ q₀ q₁ := by
  obtain ⟨q₀, q₁, hne, -, -, hcomp, -, h0, h1⟩ :=
    Plane.exists_openSegment_eq_connectedComponentIn hab hFopen hFbdd hy
  refine ⟨q₀, q₁, hne, h0, h1, ?_, ?_, ?_⟩
  · rw [← hcomp]
    exact fun z hz => (connectedComponentIn_subset _ _ hz).2
  · rw [← hcomp]
    exact mem_connectedComponentIn hy
  · intro S hS hSsub hyS
    rw [← hcomp]
    exact hS.subset_connectedComponentIn hyS hSsub

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
-- module Solutions.Q146_CD.CircleDomains_Uniformization_JordanCircularizationSequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sequence of finite Jordan configurations and normalized
conformal maps obtained by successive one-hole circularizations. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

structure Step (C : FiniteJordanConfiguration I) (j : I) where
  target : FiniteJordanConfiguration I
  map : Sphere → Sphere
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  principal : IsPrincipalNormalized map
  selected : jordanInterior (target.hole j)=ball center radius
  others : ∀ i, i≠j → map '' closedTerminalCap (C.hole i)=closedTerminalCap (target.hole i)
  conformal : IsConformalEquivalence map C.region target.region
  exterior_conformal : IsConformalEquivalence map (closedTerminalCap (C.hole j))ᶜ
    ((((↑) : ℂ → Sphere) '' closedBall center radius)ᶜ)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
end



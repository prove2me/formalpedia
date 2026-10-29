-- Prove2me | Definitions.Def_OAIQ089A001
-- name    : OAIQ089A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:50:35.990096+00:00
-- url     : https://prove2.me/theorems/e146fe19-751e-4d3d-8f7a-8ae9925c0138
-- title:
--   Definitions bundle OAIQ089A001 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1556 declarations of OpenAI's Lean: 1174 definitions, 9 inductive types or structures, 9 instances and 364 theorems. The definitions and types are `OAI.ContingencyTables.BinaryContraction.DegreePositive`, `OAI.ContingencyTables.BinaryContraction.complementWeight`, `OAI.ContingencyTables.BinaryPowerPrograms.power`, `OAI.ContingencyTables.BinaryPowerPrograms.setup`, `OAI.ContingencyTables.BoundedBinarySearch.Window`, `OAI.ContingencyTables.BoundedBinarySearch.midpoint`, `OAI.ContingencyTables.BoundedBinarySearch.run`, `OAI.ContingencyTables.BoundedBinarySearch.step`, `OAI.ContingencyTables.BoundedCellShift.lower`, `OAI.ContingencyTables.BoundedCellShift.margin`, `OAI.ContingencyTables.BoundedCellShift.raise`, `OAI.ContingencyTables.BoundedComplementProgram.EntryInput`, `OAI.ContingencyTables.BoundedComplementProgram.columnIndices`, `OAI.ContingencyTables.BoundedComplementProgram.columnValue`, `OAI.ContingencyTables.BoundedComplementProgram.columnValues`, `OAI.ContingencyTables.BoundedComplementProgram.complement`, `OAI.ContingencyTables.BoundedComplementProgram.rowIndices`, `OAI.ContingencyTables.BoundedComplementProgram.rowValue`, `OAI.ContingencyTables.BoundedPowerPrograms.power`, `OAI.ContingencyTables.BoundedPowerPrograms.powerInput`, `OAI.ContingencyTables.BoundedTableComplement.columnTotal`, `OAI.ContingencyTables.BoundedTableComplement.columns`, `OAI.ContingencyTables.BoundedTableComplement.complement`, `OAI.ContingencyTables.BoundedTableComplement.rowTotal`, `OAI.ContingencyTables.BoundedTableComplement.rows`, `OAI.ContingencyTables.BoundedTableFeasibility.computedFlow`, `OAI.ContingencyTables.BoundedTableFeasibility.feasibleTest`, `OAI.ContingencyTables.BoundedTableFeasibility.networkCapacity`, `OAI.ContingencyTables.BoundedTableFeasibility.pull`, `OAI.ContingencyTables.BoundedTableFeasibility.push`, `OAI.ContingencyTables.BoundedTableFeasibility.vertices`, `OAI.ContingencyTables.BoxCompletion.Box`, `OAI.ContingencyTables.BoxCompletion.freeValues`, `OAI.ContingencyTables.CanonicalInitialEncoding.coordinateEquiv`, `OAI.ContingencyTables.CanonicalInitialEncoding.copyOrder`, `OAI.ContingencyTables.CanonicalInitialEncoding.pairOrder`, `OAI.ContingencyTables.CanonicalInitialEncoding.pairValue`, `OAI.ContingencyTables.CanonicalInitialEncoding.pairedCode`, `OAI.ContingencyTables.CellLowerTestProgram.Context`, `OAI.ContingencyTables.CellLowerTestProgram.Input` and 1143 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CompanionAnnealing`, `ContingencyTables_Counting_CompanionArithmeticProposal`, `ContingencyTables_Counting_CompanionBinIntervals`, `ContingencyTables_Counting_CompanionBinPopulation`, `ContingencyTables_Counting_CompanionBooleanPhase`, `ContingencyTables_Counting_CompanionCanonicalHistory`, `ContingencyTables_Counting_CompanionCappedReturnProgram`, `ContingencyTables_Counting_CompanionCellCatalogProgram`, `ContingencyTables_Counting_CompanionChainValidator`, `ContingencyTables_Counting_CompanionComputedInitial`, `ContingencyTables_Counting_CompanionComputedProposal`, `ContingencyTables_Counting_CompanionConcentration`, `ContingencyTables_Counting_CompanionCorrectionArithmetic`, `ContingencyTables_Counting_CompanionEstimatorWords`, `ContingencyTables_Counting_CompanionFactorialApplication`, `ContingencyTables_Counting_CompanionInitialDraw`, `ContingencyTables_Counting_CompanionInitialMatrixProgram`, `ContingencyTables_Counting_CompanionInitialStoredProgram`, `ContingencyTables_Counting_CompanionInitialization`, `ContingencyTables_Counting_CompanionInitializedRestartProgram`, `ContingencyTables_Counting_CompanionLabelMetadataProgram`, `ContingencyTables_Counting_CompanionMetropolisProgram`, `ContingencyTables_Counting_CompanionMultiplierAgreement`, `ContingencyTables_Counting_CompanionMultiplierMatrixProgram`, `ContingencyTables_Counting_CompanionMultiplierProgram`, `ContingencyTables_Counting_CompanionNearMass`, `ContingencyTables_Counting_CompanionNeighborProgram`, `ContingencyTables_Counting_CompanionOracleBudget`, `ContingencyTables_Counting_CompanionOracleChain`, `ContingencyTables_Counting_CompanionOracleCorrection`, `ContingencyTables_Counting_CompanionOracleDensity`, `ContingencyTables_Counting_CompanionOracleDraw`, `ContingencyTables_Counting_CompanionOracleEstimator`, `ContingencyTables_Counting_CompanionOracleFibres`, `ContingencyTables_Counting_CompanionOracleFiniteStep`, `ContingencyTables_Counting_CompanionOracleKernel`, `ContingencyTables_Counting_CompanionOracleMixing`, `ContingencyTables_Counting_CompanionOracleRational`, `ContingencyTables_Counting_CompanionOracleSchedule`, `ContingencyTables_Counting_CompanionOrderedProposal`, `ContingencyTables_Counting_CompanionOuterHistoryProgram`, `ContingencyTables_Counting_CompanionOuterPhaseProgram`, `ContingencyTables_Counting_CompanionPhaseContextProgram`, `ContingencyTables_Counting_CompanionPhaseCounts`, `ContingencyTables_Counting_CompanionPhaseFinishProgram`, `ContingencyTables_Counting_CompanionPhaseFinishSemantics`, `ContingencyTables_Counting_CompanionPhaseTrajectory`, `ContingencyTables_Counting_CompanionPhaseWords`, `ContingencyTables_Counting_CompanionPhysicalNormalizer`, `ContingencyTables_Counting_CompanionPhysicalTables`, `ContingencyTables_Counting_CompanionRatioSamples`, `ContingencyTables_Counting_CompanionRationalUpdates`, `ContingencyTables_Counting_CompanionRestartInitializer`, `ContingencyTables_Counting_CompanionRestartProgram`, `ContingencyTables_Counting_CompanionRestartSchedule`, `ContingencyTables_Counting_CompanionRestartStageProgram`, `ContingencyTables_Counting_CompanionStateMultiplierProgram`, `ContingencyTables_Counting_CompanionStoredShape`, `ContingencyTables_Counting_CompanionStoredSize`, `ContingencyTables_Counting_CompanionTargetMixing`, `ContingencyTables_Counting_CompanionTerminalApplication`, `ContingencyTables_Counting_CompanionTerminalMass`, `ContingencyTables_Counting_CompanionTerminalParameters`, `ContingencyTables_Counting_CompanionTrace`, `ContingencyTables_Counting_CompanionTraceProgram`, `ContingencyTables_Counting_CompanionTraceWords`, `ContingencyTables_Counting_CompanionTransitionWidth`, `ContingencyTables_Counting_CompanionUniformPhaseWidth`, `ContingencyTables_Counting_CompanionWeightOracle`, `ContingencyTables_Counting_ComputedCountingParameters`, `ContingencyTables_Counting_CountingOracleScheduleProgram`, `ContingencyTables_Counting_CountingPhaseParametersProgram`, `ContingencyTables_Counting_CountingPhaseScalarProgram`, `ContingencyTables_Counting_CountingPhaseSchedule`, `ContingencyTables_Counting_CountingTerminalSchedule`, `ContingencyTables_Counting_InitialMultiplierValues`, `ContingencyTables_Dense_CheegerCoarea`, `ContingencyTables_Dense_DenseAffine`, `ContingencyTables_Dense_DenseAxisBits`, `ContingencyTables_Dense_DenseAxisProgram`, `ContingencyTables_Dense_DenseAxisProposal`, `ContingencyTables_Dense_DenseAxisSemantics`, `ContingencyTables_Dense_DenseAxisWordProgram`, `ContingencyTables_Dense_DenseBooleanStep`, `ContingencyTables_Dense_DenseBooleanWalk`, `ContingencyTables_Dense_DenseCanonicalProgram`, `ContingencyTables_Dense_DenseCompletionProgram`, `ContingencyTables_Dense_DenseDrawProgram`, `ContingencyTables_Dense_DenseExponentListProgram`, `ContingencyTables_Dense_DenseExponentProgram`, `ContingencyTables_Dense_DenseFlatExponentProgram`, `ContingencyTables_Dense_DenseGrid`, `ContingencyTables_Dense_DenseIntegerProgram`, `ContingencyTables_Dense_DenseIntegerTable`, `ContingencyTables_Dense_DenseMatrixLayoutProgram`, `ContingencyTables_Dense_DenseNormalizeProgram`, `ContingencyTables_Dense_DenseOffsetWidths`, `ContingencyTables_Dense_DenseReservedWord`, `ContingencyTables_Dense_DenseScaleCellProgram`, `ContingencyTables_Dense_DenseSwapProgram`, `ContingencyTables_Dense_DenseTrialProgram`, `ContingencyTables_Dense_DenseWeights`, `ContingencyTables_Dense_DenseWordProgram`, `ContingencyTables_Dense_GridCover`, `ContingencyTables_Dense_GridMetropolis`, `ContingencyTables_Machines_BinVectorProgram`, `ContingencyTables_Machines_BinaryContraction`, `ContingencyTables_Machines_BinaryExchangeProgram`, `ContingencyTables_Machines_BinaryPowerProgram`, `ContingencyTables_Machines_BooleanChunkProgram`, `ContingencyTables_Machines_BoundedBinarySearch`, `ContingencyTables_Machines_BoundedComplementProgram`, `ContingencyTables_Machines_BoundedPowerProgram`, `ContingencyTables_Machines_CanonicalInitialEncoding`, `ContingencyTables_Machines_CellLowerTestProgram`, `ContingencyTables_Machines_CellMaximumProgram`, `ContingencyTables_Machines_CellMinimumProgram`, `ContingencyTables_Machines_CorrectionValueProgram`, `ContingencyTables_Machines_DependentWordProgram`, `ContingencyTables_Machines_DirectedBFSProgram`, `ContingencyTables_Machines_DirectedBFSRuntime`, `ContingencyTables_Machines_DyadicRootProgram`, `ContingencyTables_Machines_EndpointMatrixProgram`, `ContingencyTables_Machines_FairBits`, `ContingencyTables_Machines_FiniteFairBits`, `ContingencyTables_Machines_FiniteGraphCutProgram`, `ContingencyTables_Machines_FiniteGraphRootProgram`, `ContingencyTables_Machines_FiniteVaryingWordWalk`, `ContingencyTables_Machines_FiniteWordDependent`, `ContingencyTables_Machines_FiniteWordPadding`, `ContingencyTables_Machines_FiniteWordWalk`, `ContingencyTables_Machines_FixedCardinalityBits`, `ContingencyTables_Machines_FixedCardinalityFlat`, `ContingencyTables_Machines_FixedCardinalityFold`, `ContingencyTables_Machines_FixedCardinalityLaw`, `ContingencyTables_Machines_FixedCardinalityMixture`, `ContingencyTables_Machines_FixedCardinalityProgram`, `ContingencyTables_Machines_FlowEntryProgram`, `ContingencyTables_Machines_FlowLoopProgram`, `ContingencyTables_Machines_FlowMatrixProgram`, `ContingencyTables_Machines_FlowPathProgram`, `ContingencyTables_Machines_FractionAcceptanceProgram`, `ContingencyTables_Machines_FractionAggregateProgram`, `ContingencyTables_Machines_FractionMetropolisProgram`, `ContingencyTables_Machines_InitialChoiceProgram`, `ContingencyTables_Machines_InitialFactorialBits`, `ContingencyTables_Machines_IntegerMatrixProgram`, `ContingencyTables_Machines_ListSubtractProgram`, `ContingencyTables_Machines_LowerCapacityProgram`, `ContingencyTables_Machines_MatrixSubtractProgram`, `ContingencyTables_Machines_MaximalListProgram`, `ContingencyTables_Machines_MedianFractionProgram`, `ContingencyTables_Machines_NaturalBlockProgram`, `ContingencyTables_Machines_NetworkCapacityProgram`, `ContingencyTables_Machines_NetworkTableProgram`, `ContingencyTables_Machines_OffsetCountProgram`, `ContingencyTables_Machines_PairedCatalogProgram`, `ContingencyTables_Machines_PairedDemandProgram`, `ContingencyTables_Machines_PairedFactorialProgram`, `ContingencyTables_Machines_PairedProfileProgram`, `ContingencyTables_Machines_RationalIntervalProgram`, `ContingencyTables_Machines_ResidualGraphProgram`, `ContingencyTables_Machines_ScalarScheduleProgram`, `ContingencyTables_Machines_SparseViewMatrixProgram`, `ContingencyTables_Machines_TightenedInputProgram`, `ContingencyTables_Machines_WeightedArgmaxProgram`, `ContingencyTables_Model`, `ContingencyTables_PublishedInputs`, `ContingencyTables_Rooted_ComputedLargeForest`, `ContingencyTables_Rooted_ComputedRootedInput`, `ContingencyTables_Rooted_ForestAffineCoefficients`, `ContingencyTables_Rooted_ForestAffineCompletion`, `ContingencyTables_Rooted_ForestAffineProgram`, `ContingencyTables_Rooted_ForestAssignmentSplit`, `ContingencyTables_Rooted_ForestCapacity`, `ContingencyTables_Rooted_ForestCut`, `ContingencyTables_Rooted_ForestEdgeChoiceProgram`, `ContingencyTables_Rooted_ForestGreedyProgram`, `ContingencyTables_Rooted_ForestGreedySemantics`, `ContingencyTables_Rooted_ForestJoinProgram`, `ContingencyTables_Rooted_ForestLiteralCount`, `ContingencyTables_Rooted_ForestPenaltyApplication`, `ContingencyTables_Rooted_ForestPenaltyProgram`, `ContingencyTables_Rooted_ForestPhysicalCompletion`, `ContingencyTables_Rooted_ForestRootPenalty`, `ContingencyTables_Rooted_ForestScaledIdentification`, `ContingencyTables_Rooted_ForestScaledPenalty`, `ContingencyTables_Rooted_LargeEdgeCatalogProgram`, `ContingencyTables_Rooted_LargeMarginProgram`, `ContingencyTables_Rooted_MaximumForest`, `ContingencyTables_Rooted_MaximumForestExchange`, `ContingencyTables_Rooted_RootedArithmeticStep`, `ContingencyTables_Rooted_RootedBinFramesProgram`, `ContingencyTables_Rooted_RootedCatalogGrid`, `ContingencyTables_Rooted_RootedCellDataProgram`, `ContingencyTables_Rooted_RootedCoefficientProgram`, `ContingencyTables_Rooted_RootedCompletion`, `ContingencyTables_Rooted_RootedComponentCode`, `ContingencyTables_Rooted_RootedComponentProgram`, `ContingencyTables_Rooted_RootedCorrectionProgram`, `ContingencyTables_Rooted_RootedCorrectionSampleProgram`, `ContingencyTables_Rooted_RootedCut`, `ContingencyTables_Rooted_RootedDemandProgram`, `ContingencyTables_Rooted_RootedEstimatorBlockProgram`, `ContingencyTables_Rooted_RootedEstimatorLayoutProgram`, `ContingencyTables_Rooted_RootedEstimatorWordProgram`, `ContingencyTables_Rooted_RootedForestCatalog`, `ContingencyTables_Rooted_RootedForestDataProgram`, `ContingencyTables_Rooted_RootedForestPrepareProgram`, `ContingencyTables_Rooted_RootedIntegerEvaluation`, `ContingencyTables_Rooted_RootedLabelWeightProgram`, `ContingencyTables_Rooted_RootedOracleConfigProgram`, `ContingencyTables_Rooted_RootedOracleFlatProgram`, `ContingencyTables_Rooted_RootedOracleWalkProgram`, `ContingencyTables_Rooted_RootedPenalty`, `ContingencyTables_Rooted_RootedPenaltyEvaluateProgram`, `ContingencyTables_Rooted_RootedPenaltyProgram`, `ContingencyTables_Rooted_RootedPhaseHistory`, `ContingencyTables_Rooted_RootedPhysicalCompletion`, `ContingencyTables_Rooted_RootedRatioSampleProgram`, `ContingencyTables_Rooted_RootedRootPenalty`, `ContingencyTables_Rooted_RootedStoredEstimate`, `ContingencyTables_Rooted_RootedStoredHistory`, `ContingencyTables_Rooted_RootedTreeInputProgram`, `ContingencyTables_Rooted_TreeExteriorPositions`, `ContingencyTables_Rooted_TreeFeasibleMass`, `ContingencyTables_Rooted_TreeMarginalSignature`, `ContingencyTables_Sampling_FirstPaperCodeNeighbors`, `ContingencyTables_Sampling_FirstPaperPhysicalMarginal`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_GreedyRowMachine`, `ContingencyTables_Sampling_GreedyTableMachine`, `ContingencyTables_Sampling_PaddedCompletions`, `ContingencyTables_Sampling_PaddedResidualProgram`, `ContingencyTables_Sampling_Padding`, `ContingencyTables_Sampling_ProfileExchangeProgram`, `ContingencyTables_Sampling_ProfileInverseRepairProgram`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_Repair`, `ContingencyTables_Sampling_RepairFibres`, `ContingencyTables_Sampling_RepairResiduals`, `ContingencyTables_Sampling_ResidualMixture`, `ContingencyTables_Sampling_SmallBoundsProgram`, `ContingencyTables_Sampling_SmallCellCatalogProgram`, `ContingencyTables_Sampling_SmallCellIndexProgram`, `ContingencyTables_Sampling_SmallComplementProgram`, `ContingencyTables_Sampling_SmallCompletionAcceptance`, `ContingencyTables_Sampling_SmallContextCoordinates`, `ContingencyTables_Sampling_SmallDefectCodeTest`, `ContingencyTables_Sampling_SmallEntries`, `ContingencyTables_Sampling_SmallExchangeListProgram`, `ContingencyTables_Sampling_SmallInverseRepairList`, `ContingencyTables_Sampling_SmallLineSumProgram`, `ContingencyTables_Sampling_SmallMarginTestProgram`, `ContingencyTables_Sampling_SmallPatternProgram`, `ContingencyTables_Sampling_SmallProfileCode`, `ContingencyTables_Sampling_SmallProfileFlatCode`, `ContingencyTables_Sampling_SmallProfileValidator`, `ContingencyTables_Sampling_SmallRepairCodeProgram`, `ContingencyTables_Sampling_SmallRepairGeometryProgram`, `ContingencyTables_Sampling_SmallRepairListProgram`, `ContingencyTables_Sampling_SmallViewLookupProgram`, `ContingencyTables_Transport_BoundedCellShift`, `ContingencyTables_Transport_BoundedOffsetLaw`, `ContingencyTables_Transport_BoundedProfileWalk`, `ContingencyTables_Transport_BoundedTableComplement`, `ContingencyTables_Transport_BoundedTableFeasibility`, `ContingencyTables_Transport_BoxCompletion`, `ContingencyTables_Transport_ComplementChain`, `ContingencyTables_Transport_CompletionChainFlow`, `ContingencyTables_Transport_CompletionCounts`, `ContingencyTables_Transport_CompletionKernelIdentification`, `ContingencyTables_Transport_CompletionProposalLaw`, `ContingencyTables_Transport_CompletionStepApproximation`, `ContingencyTables_Transport_DirectedBFSCode`, `ContingencyTables_Transport_DyadicRootBisection`, `ContingencyTables_Transport_EdmondsKarpAlgorithm`, `ContingencyTables_Transport_FactorialSignatures`, `ContingencyTables_Transport_FiniteDependentLaw`, `ContingencyTables_Transport_FiniteDirectedBFS`, `ContingencyTables_Transport_FiniteGraphRootSemantics`, `ContingencyTables_Transport_FiniteGraphRoots`, `ContingencyTables_Transport_FinitePartialDraw`, `ContingencyTables_Transport_FiniteProposalStay`, `ContingencyTables_Transport_FiniteRationalThreshold`, `ContingencyTables_Transport_FiniteScaledDraw`, `ContingencyTables_Transport_FirstSuccess`, `ContingencyTables_Transport_FlowClamp`, `ContingencyTables_Transport_GraphCompletionCounts`, `ContingencyTables_Transport_GraphIntegralCompletion`, `ContingencyTables_Transport_InitialDefectChoices`, `ContingencyTables_Transport_InitialFactorialLaw`, `ContingencyTables_Transport_InitialTransversals`, `ContingencyTables_Transport_IntegerPropagation`, `ContingencyTables_Transport_LabelledFactorial`, `ContingencyTables_Transport_LayeredTableNetwork`, `ContingencyTables_Transport_MetropolisChain`, `ContingencyTables_Transport_NestedPenaltyApplication`, `ContingencyTables_Transport_NestedProductSignature`, `ContingencyTables_Transport_NetworkVertexCode`, `ContingencyTables_Transport_PairedLabels`, `ContingencyTables_Transport_PathAugmentation`, `ContingencyTables_Transport_PowerOfTwoApproximation`, `ContingencyTables_Transport_ProductIntegerSignature`, `ContingencyTables_Transport_PublishedEdmondsKarp`, `ContingencyTables_Transport_RationalMapProducts`, `ContingencyTables_Transport_RationalProducts`, `ContingencyTables_Transport_RationalReindex`, `ContingencyTables_Transport_RationalRootBisection`, `ContingencyTables_Transport_RationalWalkApproximation`, `ContingencyTables_Transport_RationalWalks`, `ContingencyTables_Transport_RealPathApproximation`, `ContingencyTables_Transport_ReferenceCompletionBlock`, `ContingencyTables_Transport_RejectionLaw`, `ContingencyTables_Transport_ResidualAugmentation`, `ContingencyTables_Transport_ResidualSearch`, `ContingencyTables_Transport_RowColumnPenalties`, `ContingencyTables_Transport_SignedMarginTranslation`, `ContingencyTables_Transport_StarReindex`, `ContingencyTables_Transport_TableMarginTransport`, `ContingencyTables_Transport_TableReindex`, `ContingencyTables_Transport_TableTightening`, `ContingencyTables_Transport_TranslatedCompletionAcceptance`, `ContingencyTables_Transport_TranslatedCompletionChain`, `ContingencyTables_Transport_TranslatedCompletionCounts`, `ContingencyTables_Transport_TranslatedCompletions`, `ContingencyTables_Transport_TransversalCount`, `ContingencyTables_Transport_TwoLiftStates`, `ContingencyTables_Transport_WordCompletionStep`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Arithmetic_TreeGCD`, `MatchingCount_Complexity_TreeFractionCosts`, `MatchingCount_Machines_TreeIndex`, `MatchingCount_Machines_TreeListOps`, `MatchingCount_Machines_TreeNaturalComb`, `MatchingCount_Machines_TreeRepeat`, `MatchingCount_Machines_TreeSum`, `MatchingCount_Sampling_Certify`, `MatchingCount_Sampling_TreeCategorical`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A003`, `OAIQ089A004` and `OAIQ089A005`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_MaximumForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's maximum-capacity forest

Among finite acyclic subgraphs choose one of maximum total capacity.
Positive capacities make it spanning in each large-cell component. A
free edge can replace every tree edge on its path; optimality therefore
gives the exact path-capacity inequality used in the forest estimates.
-/

namespace ContingencyTables.MaximumForest

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

noncomputable def weight (G : SimpleGraph V) (b : Sym2 V → ℕ) : ℕ :=
  ∑ e ∈ G.edgeFinset, b e

lemma weight_eq (G : SimpleGraph V) (b : Sym2 V → ℕ) [Fintype G.edgeSet] :
    weight G b=∑ e∈G.edgeFinset,b e := by
  unfold weight
  apply Finset.sum_congr
  · ext e
    simp only [mem_edgeFinset]
  · intro e _
    rfl

theorem exists_maximum (G : SimpleGraph V) (b : Sym2 V → ℕ) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsAcyclic ∧
      ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b := by
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun F => F ≤ G ∧ F.IsAcyclic)
  have hS : S.Nonempty := ⟨⊥,by simp [S]⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image S (fun F => weight F b) hS
  have hp := (Finset.mem_filter.mp hT).2
  refine ⟨T,hp.1,hp.2,?_⟩
  intro F hFG hacyc
  exact hmax F (by simp [S,hFG,hacyc])

lemma weight_sup_edge (T : SimpleGraph V) (b : Sym2 V → ℕ) (u v : V)
    (hn : ¬T.Adj u v) (hne : u≠v) :
    weight (T ⊔ edge u v) b=b s(u,v)+weight T b := by
  rw [weight_eq (T ⊔ edge u v),weight_eq T,T.edgeFinset_sup_edge hn hne,Finset.sum_cons]

omit [Fintype V] in
/-- Deleting an edge of the unique tree path separates its endpoints. -/
lemma not_reachable_delete_path_edge (T : SimpleGraph V) (hT : T.IsAcyclic)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (t : Sym2 V) (ht : t∈p.edges) :
    ¬(T.deleteEdges {t}).Reachable u v := by
  intro hreach
  obtain ⟨q,hq⟩ := hreach.exists_isPath
  have he : p=q.mapLe (T.deleteEdges_le {t}) := congrArg Subtype.val
    ((hT.subsingleton_path u v).elim ⟨p,hp⟩ ⟨q.mapLe (T.deleteEdges_le {t}),hq.mapLe _⟩)
  rw [he] at ht
  simp only [Walk.edges_map,Hom.coe_ofLE,Sym2.map_id,List.map_id_fun,id_eq] at ht
  have hmem := q.edges_subset_edgeSet ht
  rw [edgeSet_deleteEdges] at hmem
  exact hmem.2 (by simp)

omit [Fintype V] in
noncomputable def side (D : SimpleGraph V) (u v : V) : Bool := @decide (D.Reachable u v) (Classical.propDecidable _)

omit [Fintype V] in
/-- One deletion component contains an endpoint of the removed edge
and avoids the chosen root. This also works for isolated components. -/
lemma exists_root_avoiding_side (T : SimpleGraph V) (hT : T.IsAcyclic)
    {u v : V} (ht : T.Adj u v) (root : V) (hroot : T.Reachable root u) :
    ∃ r : V, T.Reachable root r ∧ side (T.deleteEdges {s(u,v)}) r root=false ∧
      side (T.deleteEdges {s(u,v)}) r u≠side (T.deleteEdges {s(u,v)}) r v := by
  let D := T.deleteEdges {s(u,v)}
  have hsep : ¬D.Reachable u v :=
    isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT ht)
  by_cases hru : D.Reachable u root
  · refine ⟨v,hroot.trans ht.reachable,?_,?_⟩
    · have hn : ¬D.Reachable v root := fun h => hsep (hru.trans h.symm)
      simpa only [side,decide_eq_false_iff_not] using hn
    · have hn : ¬D.Reachable v u := fun h => hsep h.symm
      change side D v u≠side D v v
      simp [side,hn]
  · refine ⟨u,hroot,?_,?_⟩
    · simpa only [side,decide_eq_false_iff_not] using hru
    · change side D u u≠side D u v
      simp [side,hsep]

/-- Positive capacities force the maximizing acyclic subgraph to span
every original connected component, including isolated vertices. -/
theorem maximum_spans (G T : SimpleGraph V) (b : Sym2 V → ℕ)
    (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph V, F ≤ G → F.IsAcyclic → weight F b ≤ weight T b)
    (hb : ∀ e∈G.edgeSet, 0 < b e) : T.Reachable=G.Reachable := by
  have hadj : ∀ u v, G.Adj u v → T.Reachable u v := by
    intro u v hG
    by_contra hnreach
    have hn : ¬T.Adj u v := fun h => hnreach h.reachable
    have hnew := hT.sup_edge_of_not_reachable hnreach
    have hle : T ⊔ edge u v ≤ G := sup_le hTG ((G.edge_le_iff).mpr (Or.inr hG))
    have hopt := hmax (T ⊔ edge u v) hle hnew
    have hsum := weight_sup_edge T b u v hn hG.ne
    have hpos := hb s(u,v) (by simpa using hG)
    omega
  funext u v
  apply propext
  constructor
  · intro h; exact h.mono hTG
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨Walk.nil⟩
    | cons h p ih => exact (hadj _ _ h).trans ih

end ContingencyTables.MaximumForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contingency tables with arbitrary margins

The feasible sets in result 200 are represented by natural-valued
matrices, without a positivity, balance, or sparsity restriction on
the margins. The finite encoding bound is proved rather than assumed.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

theorem totals_equal {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) : ∑ i, r i = ∑ j, c j := by
  simp_rw [← h.1, ← h.2]
  exact sum_comm

section Existence

variable [DecidableEq I] [DecidableEq J]

theorem sum_decrease_one (r : I → ℕ) (i : I) (hi : 0 < r i) :
    (∑ k, Function.update r i (r i - 1) k) + 1 = ∑ k, r k := by
  rw [sum_update_of_mem (mem_univ i)]
  have hsum := sum_erase_add (univ : Finset I) r (mem_univ i)
  simp only [sdiff_singleton_eq_erase] at *
  omega

/-- Equal total nonnegative margins always admit an unrestricted table.
The proof removes one unit at a positive row and a positive column.
It is an existence argument; no polynomial runtime is asserted here. -/
theorem exists_table (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X, HasMargins X r c := by
  suffices ∀ N (r : I → ℕ) (c : J → ℕ),
      (∑ i, r i) = N → (∑ j, c j) = N → ∃ X, HasMargins X r c by
    exact this _ r c rfl htotal.symm
  intro N
  induction N with
  | zero =>
    intro r c hr hc
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro i
      have hri := single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (mem_univ i)
      rw [hr] at hri
      simpa using (Nat.eq_zero_of_le_zero hri).symm
    · intro j
      have hcj := single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (mem_univ j)
      rw [hc] at hcj
      simpa using (Nat.eq_zero_of_le_zero hcj).symm
  | succ N ih =>
    intro r c hr hc
    obtain ⟨i₀, _, hi₀⟩ := exists_ne_zero_of_sum_ne_zero
      (s := (univ : Finset I)) (f := r) (by rw [hr]; exact Nat.succ_ne_zero _)
    obtain ⟨j₀, _, hj₀⟩ := exists_ne_zero_of_sum_ne_zero
      (s := (univ : Finset J)) (f := c) (by rw [hc]; exact Nat.succ_ne_zero _)
    let r' := Function.update r i₀ (r i₀ - 1)
    let c' := Function.update c j₀ (c j₀ - 1)
    have hr' : ∑ i, r' i = N := by
      have h := sum_decrease_one r i₀ (Nat.pos_of_ne_zero hi₀)
      dsimp [r']
      omega
    have hc' : ∑ j, c' j = N := by
      have h := sum_decrease_one c j₀ (Nat.pos_of_ne_zero hj₀)
      dsimp [c']
      omega
    obtain ⟨X, hXr, hXc⟩ := ih r' c' hr' hc'
    refine ⟨fun i j => X i j + if i = i₀ ∧ j = j₀ then 1 else 0, ?_, ?_⟩
    · intro i
      rw [sum_add_distrib, hXr i]
      by_cases hi : i = i₀
      · subst i
        simp only [true_and, sum_ite_eq', mem_univ, ite_true, if_true, r', Function.update_self]
        omega
      · simp [hi, r']
    · intro j
      rw [sum_add_distrib, hXc j]
      by_cases hj : j = j₀
      · subst j
        simp only [and_true, sum_ite_eq', mem_univ, ite_true, if_true, c', Function.update_self]
        omega
      · simp [hj, c']

theorem table_nonempty (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j) :
    Nonempty (Table r c) := by
  obtain ⟨X, hX⟩ := exists_table r c htotal
  exact ⟨⟨X, hX⟩⟩

end Existence

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-degree binary cubic contraction

The full-matrix cubic contraction in paper 200-02,
Lemma `lem:binary-contraction`, follows from the generic spectral theorem
`CommonBasesFPRAS.cubic_signature` and its closed-limit lemma. A symmetric
cubic tensor is positive on distinct triples and zero on repetitions;
its coordinate slices have the quadratic signature; contraction by an
arbitrary nonnegative vector, in particular a pair indicator, preserves
that signature on the full remaining index set.

There is no assumption of positivity on unrelated subset cardinalities.
-/

namespace ContingencyTables.BinaryContraction

open scoped BigOperators Topology Classical
open LinearMap (BilinForm)

variable {I : Type*} [Fintype I] [DecidableEq I]


/-- Positivity is required only on the paper's valid subset degree. -/
def DegreePositive (f : Set I → ℝ) (k : ℕ) : Prop :=
  ∀ A, A.ncard = k → 0 < f A


noncomputable def complementWeight (f : Set I → ℝ) (U : Set I) : ℝ := f Uᶜ

end ContingencyTables.BinaryContraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FactorialSignatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def factorialProduct (n : G → ℕ) : ℝ := ∏ u, (n u).factorial

end ContingencyTables.FactorialSignatures

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ProductIntegerSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Raw integer signatures of the actual line and unary product

The line groups are disjoint. Integer counts at zero are masked; a repeated
removal from a count below two uses a zero second-update factor. This
identifies the actual integer matrix, including its box boundaries, with a
congruence of the proved line/unary update matrix.
-/

namespace ContingencyTables.ProductIntegerSignature

open scoped BigOperators Classical Matrix
open FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def lineTotal (line : I → G) (z : I → ℕ) (g : G) : ℕ :=
  ∑ i, if line i = g then z i else 0

end ContingencyTables.ProductIntegerSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedProductSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual line and small-slot subgroup product

Each small-slot subgroup is contained in a disjoint line group. The literal
product after two removals is factored into the two-level kernel. Zero
integer counts are masked and invalid repeated removals subtract a
nonnegative diagonal.
-/

namespace ContingencyTables.NestedProductSignature

open scoped BigOperators Classical Matrix
open FactorialSignatures ProductIntegerSignature

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def smallTotal (line : I → G) (inner : I → Bool) (z : I → ℕ) (g : G) : ℕ :=
  lineTotal (fun i => (line i,inner i)) z (g,true)

end ContingencyTables.NestedProductSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LabelledFactorial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal subset factorial lifts and their conditioned copy displays

A display is the actual subtype of available labelled elements. Its group
fibres are reindexed by Fin of their exact cardinalities. Removing or adding
actual labels changes the group counts by the exact integer updates, so the
conditioned subset matrices are congruent to the proved factorial copy
matrices. No binary-lift signature is assumed.
-/

namespace ContingencyTables.LabelledFactorial

open scoped BigOperators Classical Matrix
open BinaryContraction FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def groupCount (group : I → G) (S : Set I) : G → ℕ :=
  fun u => (Finset.univ.filter (fun i => i ∈ S ∧ group i = u)).card

noncomputable def firstLift (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (S : Set I) : ℝ :=
  h (groupCount group S) * factorialProduct (groupCount group S) / D

end ContingencyTables.LabelledFactorial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedPenaltyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual positive penalties and hard equality limit

Full row/column deviations give absolute affine line factors; the nested
small-slot residual constraints give positive-part affine factors. Their
product is exactly 2^(-L D). Balanced large-slot sums retain their proved
signature, and their finite limit is the exact zero-penalty indicator sum.
-/

namespace ContingencyTables.NestedPenaltyApplication

open scoped BigOperators Classical Matrix Topology
open Filter FactorialSignatures ProductIntegerSignature
open NestedProductSignature

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def penalty (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) : ℝ :=
  (∑ g, |offset g+(lineTotal line z g:ℝ)*slope g|)+
    ∑ g, max (smallOffset g+(smallTotal line inner z g:ℝ)*smallSlope g) 0

noncomputable def hardWeight (line : C → G) (inner : C → Bool)
    (offset slope smallOffset smallSlope : G → ℝ) (z : C → ℕ) : ℝ :=
  if penalty line inner offset slope smallOffset smallSlope z=0 then 1 else 0

end ContingencyTables.NestedPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowColumnPenalties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal doubled row and column penalties

The false coordinate of a cell is its row value x. Its true coordinate
is y, with physical column value q=B-y. Thus row and column factor groups
are disjoint, while their small-cell subsets are nested inside them.
Offsets below are the actual full margins and capacity sums of the paper.
-/

namespace ContingencyTables.RowColumnPenalties

open scoped BigOperators Classical Matrix
open ProductIntegerSignature NestedProductSignature
open NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

def cellLine (u : (I × J) × Bool) : I ⊕ J := if u.2 then .inr u.1.2 else .inl u.1.1

def smallCoordinate (small : I → J → Bool) (u : (I × J) × Bool) : Bool := small u.1.1 u.1.2

def rowView (z : ((I × J) × Bool) → ℕ) (i : I) (j : J) : ℕ := z ((i,j),false)
def columnView (B : I → J → ℕ) (z : ((I × J) × Bool) → ℕ) (i : I) (j : J) : ℕ :=
  B i j-z ((i,j),true)

noncomputable def columnCapacity (B : I → J → ℕ) (j : J) : ℕ := ∑ i, B i j
noncomputable def smallColumnCapacity (small : I → J → Bool) (B : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then B i j else 0

noncomputable def fullOffset (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ) : I ⊕ J → ℝ :=
  Sum.elim (fun i => -(rbar i:ℝ)) (fun j => (columnCapacity B j:ℝ)-cbar j)

def viewSlope : I ⊕ J → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

noncomputable def smallOffset (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) : I ⊕ J → ℝ :=
  Sum.elim (fun i => -(r i:ℝ)) (fun j => (smallColumnCapacity small B j:ℝ)-c j)

lemma lineTotal_row (z : ((I × J) × Bool) → ℕ) (i : I) :
    lineTotal cellLine z (.inl i)=∑ j, rowView z i j := by
  simp [lineTotal,cellLine,Fintype.sum_prod_type,rowView]
  rw [Finset.sum_comm]
  simp

lemma lineTotal_column (z : ((I × J) × Bool) → ℕ) (j : J) :
    lineTotal cellLine z (.inr j)=∑ i, z ((i,j),true) := by
  simp [lineTotal,cellLine,Fintype.sum_prod_type]

lemma smallTotal_row (small : I → J → Bool) (z : ((I × J) × Bool) → ℕ) (i : I) :
    smallTotal cellLine (smallCoordinate small) z (.inl i)=
      ∑ j, if small i j then rowView z i j else 0 := by
  simp [smallTotal,lineTotal,cellLine,smallCoordinate,Fintype.sum_prod_type,rowView,
    ite_and]

lemma smallTotal_column (small : I → J → Bool) (z : ((I × J) × Bool) → ℕ) (j : J) :
    smallTotal cellLine (smallCoordinate small) z (.inr j)=
      ∑ i, if small i j then z ((i,j),true) else 0 := by
  simp [smallTotal,lineTotal,cellLine,smallCoordinate,Fintype.sum_prod_type,
    ite_and]

lemma full_affine_row (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (i : I) :
    fullOffset B rbar cbar (.inl i)+(lineTotal cellLine z (.inl i):ℝ)*viewSlope (I := I) (J := J) (.inl i) =
      ((∑ j, rowView z i j):ℝ)-rbar i := by
  rw [lineTotal_row]
  simp [fullOffset,viewSlope]
  ring

lemma small_affine_row (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (i : I) :
    smallOffset small B r c (.inl i)+
      (smallTotal cellLine (smallCoordinate small) z (.inl i):ℝ)*viewSlope (I := I) (J := J) (.inl i) =
      ((∑ j, if small i j then rowView z i j else 0):ℝ)-r i := by
  rw [smallTotal_row]
  simp [smallOffset,viewSlope]
  ring

def FullConditions (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : ((I × J) × Bool) → ℕ) : Prop :=
  (∀ i, ∑ j, rowView z i j=rbar i) ∧
    (∀ j, ∑ i, columnView B z i j=cbar j) ∧
    (∀ i, (∑ j, if small i j then rowView z i j else 0) ≤ r i) ∧
    (∀ j, (∑ i, if small i j then columnView B z i j else 0) ≤ c j)

end ContingencyTables.RowColumnPenalties

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed cut equations for the actual physical table views

Small row and column views may disagree. Their two incidences therefore
remain separate in the cut formula. Large cells have a single physical
value at both endpoints, so every internal large-cell contribution cancels.
-/

namespace ContingencyTables.ForestCut

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def indicator (s : Bool) : ℝ := if s then 1 else 0

end ContingencyTables.ForestCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual bipartite cell forests and their completion intervals

The graph vertices are the original row and column labels. Capacities
are attached to unordered row-column edges. The deletion-component cut
is constructed from the maximizing forest, so the hypotheses of the
physical cut estimate follow from actual graph properties.
-/

namespace ContingencyTables.ForestCapacity

open scoped BigOperators Classical
open SimpleGraph
open MaximumForest ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

def cellAdj (small : I → J → Bool) : I⊕J → I⊕J → Prop
  | .inl i,.inr j => small i j=false
  | .inr j,.inl i => small i j=false
  | _,_ => False

def cellGraph (small : I → J → Bool) : SimpleGraph (I⊕J) where
  Adj := cellAdj small
  symm := ⟨by intro v w; cases v <;> cases w <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> exact id⟩

def pairCapacity (b : I → J → ℕ) : I⊕J → I⊕J → ℕ
  | .inl i,.inr j => b i j
  | .inr j,.inl i => b i j
  | _,_ => 0

def capacity (b : I → J → ℕ) : Sym2 (I⊕J) → ℕ :=
  Sym2.lift ⟨pairCapacity b,by intro v w; cases v <;> cases w <;> rfl⟩

omit [Fintype I] [Fintype J] in
@[simp] lemma capacity_cell (b : I → J → ℕ) (i : I) (j : J) :
    capacity b s(Sum.inl i,Sum.inr j)=b i j := rfl

end ContingencyTables.ForestCapacity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_GraphIntegralCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral completion of actual graph incidence equations

Integral root-path flows give an explicit solution of every nonroot
incidence equation. This works directly on the finite row/column graph,
including disconnected components and singleton components.
-/

namespace ContingencyTables.GraphIntegralCompletion

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

omit [Fintype V] in
noncomputable def edgeFlow (u v a b : V) : ℤ :=
  (if u=a ∧ v=b then 1 else 0)-(if u=b ∧ v=a then 1 else 0)

omit [Fintype V] in
noncomputable def walkFlow {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a b : V) : ℤ :=
  (p.darts.map (fun d => edgeFlow d.fst d.snd a b)).sum

omit [Fintype V] in
@[simp] lemma walkFlow_nil (G : SimpleGraph V) (u a b : V) :
    walkFlow (Walk.nil : G.Walk u u) a b=0 := rfl

omit [Fintype V] in
noncomputable def componentRoot (G : SimpleGraph V) (v : V) : V :=
  Classical.choose (G.connectedComponentMk v).exists_rep

omit [Fintype V] in
lemma componentRoot_component (G : SimpleGraph V) (v : V) :
    G.connectedComponentMk (componentRoot G v)=G.connectedComponentMk v :=
  Classical.choose_spec (G.connectedComponentMk v).exists_rep

omit [Fintype V] in
lemma componentRoot_reachable (G : SimpleGraph V) (v : V) :
    G.Reachable v (componentRoot G v) :=
  ConnectedComponent.exact (componentRoot_component G v).symm

omit [Fintype V] in
noncomputable def rootPath (G : SimpleGraph V) (v : V) : G.Walk v (componentRoot G v) :=
  Classical.choice (componentRoot_reachable G v)

noncomputable def completionFlow (G : SimpleGraph V) (r : V → ℤ) (a b : V) : ℤ :=
  ∑ v, r v*walkFlow (rootPath G v) a b

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
noncomputable def tableCompletion (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (i : I) (j : J) : ℤ :=
  completionFlow T (Sum.elim r (fun j => -c j)) (.inl i) (.inr j)

end ContingencyTables.GraphIntegralCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_GraphCompletionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicity-one forest-coordinate sums

The finite coordinates are the actual tree cells of the row/column
forest, with physical intervals [-10 d b,10 d b]. A solution of the
nonroot equations contributes exactly once, with its original weight.
-/

namespace ContingencyTables.GraphCompletionCounts

open scoped BigOperators Classical
open SimpleGraph
open ForestCapacity GraphIntegralCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TreeCell (T : SimpleGraph (I⊕J)) :=
  {a : I×J // T.Adj (.inl a.1) (.inr a.2)}

end ContingencyTables.GraphCompletionCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPhysicalCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's actual small/free profiles and tree intervals

Residual margins subtract the two separate small views and the fixed
free values. The integral graph completion satisfies every nonroot line.
The maximum-forest cut bound then supplies, rather than assumes, the
physical tree interval used by the signature/count marginal.
-/

namespace ContingencyTables.ForestPhysicalCompletion

open scoped BigOperators Classical
open SimpleGraph
open ForestCapacity GraphIntegralCompletion GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fixedRow (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (x free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if small i j then x i j else if T.Adj (.inl i) (.inr j) then 0 else free i j

noncomputable def fixedColumn (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if small i j then q i j else if T.Adj (.inl i) (.inr j) then 0 else free i j

noncomputable def rowResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (x free : I → J → ℤ) (i : I) : ℤ :=
  r i-∑ j, fixedRow small T x free i j

noncomputable def columnResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (c : J → ℤ) (q free : I → J → ℤ) (j : J) : ℤ :=
  c j-∑ i, fixedColumn small T q free i j

noncomputable def solved (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I → J → ℤ :=
  tableCompletion T (rowResidual small T r x free) (columnResidual small T c q free)

noncomputable def completed (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then solved small T r c x q free i j else free i j

end ContingencyTables.ForestPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal companion row/column and unary tree penalties

The physical row view is ell+x; the physical column view is ell+M-y.
The line groups are the disjoint original row and column coordinates.
Roots are the actual chosen component roots of the large-cell forest.
Only the false (row) coordinate of each tree cell carries its interval
penalty. Thus the concrete exact factor family is precisely the source's
nonroot indicator times its root/tree penalty weight.
-/

namespace ContingencyTables.ForestPenaltyApplication

open scoped BigOperators Classical Matrix
open SimpleGraph
open ProductIntegerSignature
open ForestCapacity GraphIntegralCompletion RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rootFlag (T : SimpleGraph (I⊕J)) (v : I⊕J) : Bool :=
  decide (v=componentRoot T v)

end ContingencyTables.ForestPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestLiteralCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal doubled-coordinate profiles for companion completion counts

Small views are retained separately. Every large pair is balanced, with
its physical tree or free-cell value represented in the prescribed finite
interval. These identities connect the concrete laminar factor family to
the actual graph completion sum.
-/

namespace ContingencyTables.ForestLiteralCount

open scoped BigOperators Classical
open SimpleGraph
open GraphIntegralCompletion GraphCompletionCounts ForestCapacity

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def width (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) (i : I) (j : J) : ℕ :=
  if T.Adj (.inl i) (.inr j) then 20*d*b i j else b i j

noncomputable def lower (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then -((10*d*b i j:ℕ):ℤ) else 0

noncomputable def largeValue (T : SimpleGraph (I⊕J)) (tree : I → J → ℤ)
    (free : I → J → ℕ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then tree i j else free i j

noncomputable def actualDeviation (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (tree : I → J → ℤ) : I⊕J → ℝ :=
  Sum.elim
    (fun i => ((∑ j, if small i j then (x i j:ℤ) else largeValue T tree free i j):ℤ)-r i)
    (fun j => ((∑ i, if small i j then ((b i j-y i j:ℕ):ℤ)
      else largeValue T tree free i j):ℤ)-c j)

noncomputable def actualPenalty (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b x y free : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (tree : I → J → ℤ) : ℝ :=
  (∑ v, if ForestPenaltyApplication.rootFlag T v then
    |actualDeviation small T b x y free r c tree v| else 0)+
  ∑ i, ∑ j, if T.Adj (.inl i) (.inr j) then
    max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-b i j))/(b i j:ℝ) else 0

end ContingencyTables.ForestLiteralCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAssignmentSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Splitting actual large-cell assignments into tree and free choices

The coordinate enumeration used for signatures and the graph completion
sum use exactly the same assignments. This finite equivalence records
that fact, including the larger signed tree intervals.
-/

namespace ContingencyTables.ForestAssignmentSplit

open scoped BigOperators Classical
open SimpleGraph GraphCompletionCounts ForestCapacity ForestLiteralCount

variable {I J : Type*}

@[reducible] def FreeCell (small : I → J → Bool) (T : SimpleGraph (I⊕J)) :=
  {a : I×J // small a.1 a.2=false ∧ ¬T.Adj (.inl a.1) (.inr a.2)}

@[reducible] def FreeIndex (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) := (a : FreeCell small T) → Fin (b a.val.1 a.val.2+1)

noncomputable def freeTable (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) (a : FreeIndex small T b) (i : I) (j : J) : ℕ :=
  if h : small i j=false ∧ ¬T.Adj (.inl i) (.inr j) then (a ⟨(i,j),h⟩).val else 0

end ContingencyTables.ForestAssignmentSplit

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

def group (cell : P → C) (i : P × Bool) : C × Bool := (cell i.1,i.2)

def pair (p : P) : (P × Bool) × (P × Bool) := ((p,false),(p,true))

noncomputable def pairs : List ((P × Bool) × (P × Bool)) :=
  Finset.univ.toList.map pair

noncomputable def width (cell : P → C) (c : C) : ℕ :=
  (Finset.univ.filter (fun p => cell p=c)).card

noncomputable def viewCount (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) : ℕ :=
  ∑ p, if cell p=c ∧ (p,t) ∈ S then 1 else 0

lemma pair_mem (p : P) : pair p ∈ (pairs : List ((P × Bool) × (P × Bool))) := by
  simp [pairs]

omit [Fintype C] in
lemma groupCount_eq_viewCount (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    groupCount (group cell) S (c,t) = viewCount cell S c t := by
  unfold groupCount viewCount
  rw [Finset.card_filter]
  simp only [Fintype.sum_prod_type,group,Prod.mk.injEq,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro p _
  cases t <;> simp [and_comm]

omit [Fintype C] in
lemma width_eq_sum (cell : P → C) (c : C) :
    width cell c = ∑ p, if cell p=c then 1 else 0 := Finset.card_filter _ _

noncomputable def denominator (cell : P → C) : ℝ := ∏ c, ((width cell c).factorial : ℝ)

end ContingencyTables.TwoLiftStates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFactorialApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's literal completion count gives both labelled factorial signatures

The labels below are actual copies of the retained small cells. Their
fiber cardinalities are the capacities, so the original first and dual
factorial displays and the W² chain-state comparison have no abstract
signature or completion hypothesis.
-/

namespace ContingencyTables.CompanionFactorialApplication

open scoped BigOperators Classical Matrix
open SimpleGraph
open ForestCapacity GraphIntegralCompletion
open LabelledFactorial

variable (I J : Type*) [Fintype I] [Fintype J]

/-- Actual tightened bounded margins, a maximum large-cell forest, and
one feasible baseline table determine the completion counts and
factorial signatures. -/
structure Instance where
  small : I → J → Bool
  b : I → J → ℕ
  T : SimpleGraph (I⊕J)
  hTG : T ≤ cellGraph small
  hT : T.IsAcyclic
  hmax : ∀ F : SimpleGraph (I⊕J), F ≤ cellGraph small → F.IsAcyclic →
    MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b)
  r : I → ℤ
  c : J → ℤ
  X : I → J → ℤ
  d : ℕ
  W : ℕ
  hd : 1≤d
  hcard : Fintype.card I*Fintype.card J≤d
  hW : 2≤W
  hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j
  hsmall : ∀ i j, small i j=true → b i j<W
  hX : ∀ i j, 0≤X i j ∧ X i j≤b i j
  hXr : ∀ i, (∑ j, X i j)=r i
  hXc : ∀ j, (∑ i, X i j)=c j

variable {I J}

@[reducible] def SmallCell (A : Instance I J) := {a : I×J // A.small a.1 a.2=true}

@[reducible] def View (A : Instance I J) := SmallCell A×Bool

def bounds (A : Instance I J) (u : View A) : ℕ := A.b u.1.val.1 u.1.val.2

@[reducible] def Labels (A : Instance I J) := Σ s : SmallCell A, Fin (A.b s.val.1 s.val.2)

@[reducible] def labelCell (A : Instance I J) (p : Labels A) : SmallCell A := p.1

lemma label_width (A : Instance I J) (s : SmallCell A) :
    TwoLiftStates.width (labelCell A) s=A.b s.val.1 s.val.2 := by
  rw [TwoLiftStates.width_eq_sum]
  rw [Fintype.sum_sigma]
  have hinner (x : SmallCell A) :
      (∑ k : Fin (A.b x.val.1 x.val.2), if labelCell A ⟨x,k⟩=s then 1 else 0)=
        if x=s then A.b x.val.1 x.val.2 else 0 := by
    by_cases hx : x=s
    · subst x
      have he : ∀ k : Fin (A.b s.val.1 s.val.2), labelCell A ⟨s,k⟩=s := fun _ => rfl
      simp [he]
    · have he : ∀ k : Fin (A.b x.val.1 x.val.2), labelCell A ⟨x,k⟩≠s := fun _ => hx
      simp [he,hx]
  convert (show (∑ x : SmallCell A, if x=s then A.b x.val.1 x.val.2 else 0)=
      A.b s.val.1 s.val.2 by simp) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  convert hinner x using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : labelCell A ⟨x,k⟩=s <;> simp [hk]

lemma label_capacity (A : Instance I J) :
    groupCount (TwoLiftStates.group (labelCell A)) Set.univ=bounds A := by
  funext u
  rcases u with ⟨s,t⟩
  rw [TwoLiftStates.groupCount_eq_viewCount]
  unfold TwoLiftStates.viewCount
  simp only [Set.mem_univ,and_true]
  have he : (∑ p : Labels A, if labelCell A p=s then 1 else 0)=
      TwoLiftStates.width (labelCell A) s := by
    rw [TwoLiftStates.width_eq_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : labelCell A p=s <;> simp [hp]
  exact he.trans (label_width A s)

noncomputable def denominator (A : Instance I J) := TwoLiftStates.denominator (labelCell A)

lemma denominator_positive (A : Instance I J) : 0<denominator A := by
  apply Finset.prod_pos
  intro s _
  exact Nat.cast_pos.mpr (Nat.factorial_pos _)

end ContingencyTables.CompanionFactorialApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def signedResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim
    (fun i => (∑ j, if small i j then x i j else completed small T r c x q free i j)-r i)
    (fun j => -((∑ i, if small i j then q i j else completed small T r c x q free i j)-c j))

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual doubled labels form disjoint covering slots -/

namespace ContingencyTables.PairedLabels

open scoped BigOperators Classical
open TwoLiftStates

variable {P : Type*}

variable [Fintype P]

@[simp] theorem length : (pairs : List ((P×Bool)×(P×Bool))).length=Fintype.card P := by
  simp [pairs]

end ContingencyTables.PairedLabels

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionAnnealing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent actual companion weights and ideal multipliers

The parameter step is 1/(H/A). Its factor-two bounds are proved from
the literal forest penalty bound, then passed to the actual labelled
weights and their exact transversal/defect totals.
-/

namespace ContingencyTables.CompanionAnnealing

open scoped BigOperators Classical
open CompanionFactorialApplication LabelledFactorial
open TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scale (A : Instance I J) : ℝ := 10*(A.d:ℝ)^2*((A.W:ℝ)+1)

lemma scale_positive (A : Instance I J) : 0< scale A := by
  have hd : (0:ℝ)< A.d := by
    exact_mod_cast (show 0< A.d by have := A.hd; omega)
  unfold scale
  positivity

end ContingencyTables.CompanionAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open TwoLiftStates LabelledFactorial

variable {C : Type*} [Fintype C] (b : C → ℕ)

abbrev Copy := Σ c, Fin (b c)

@[reducible] def cell (p : Copy b) : C := p.1

@[reducible] noncomputable def encode (S : (c : C) → Finset (Fin (b c))) : Set (Copy b×Bool) :=
  fun p => if p.2 then p.1.2∉S p.1.1 else p.1.2∈S p.1.1

omit [Fintype C] in
@[simp] lemma encode_false (S : (c : C) → Finset (Fin (b c))) (p : Copy b) :
    (p,false)∈encode b S ↔ p.2∈S p.1 := Iff.rfl

omit [Fintype C] in
@[simp] lemma encode_true (S : (c : C) → Finset (Fin (b c))) (p : Copy b) :
    (p,true)∈encode b S ↔ p.2∉S p.1 := Iff.rfl

end ContingencyTables.InitialTransversals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact initial normalizer for the literal companion completion count -/

namespace ContingencyTables.CompanionInitialization

open scoped BigOperators Classical
open CompanionFactorialApplication LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def freeTotal (A : Instance I J) : ℝ :=
  ∏ a : ForestAssignmentSplit.FreeCell A.small A.T,
    ((A.b a.val.1 a.val.2+1:ℕ):ℝ)

end ContingencyTables.CompanionInitialization

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialDefectChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual remaining label choices for an initial defect

The hole and full pair are removed before the remaining row labels are
chosen. This gives the finite combinatorial space underlying the exact
local initialization brackets, including two removed labels in one cell.
-/

namespace ContingencyTables.InitialDefectChoices

open scoped BigOperators Classical
open TwoLiftStates
open InitialTransversals (Copy)

variable {C : Type*} [Fintype C] (b : C → ℕ) (p q : Copy b)

@[reducible] def Local (c : C) :=
  {k : Fin (b c) // (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q}

end ContingencyTables.InitialDefectChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_InitialMultiplierValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact source initial multipliers for actual labelled defects -/

namespace ContingencyTables.InitialMultiplierValues

open scoped BigOperators Classical
open TwoLiftStates InitialTransversals

variable {C : Type*} [Fintype C] (b : C → ℕ)

noncomputable def value (p q : Copy b) : ℝ :=
  if p.1=q.1 then 6 else 6*((b p.1:ℝ)+1)/((b q.1:ℝ)+2)

end ContingencyTables.InitialMultiplierValues
namespace ContingencyTables.CompanionInitialMultipliers

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionInitialization LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def multiplier (A : Instance I J)
    (p q : (Labels A×Bool)×(Labels A×Bool)) : ℝ :=
  InitialMultiplierValues.value (fun s : SmallCell A => A.b s.val.1 s.val.2) p.1.1 q.1.1

end ContingencyTables.CompanionInitialMultipliers

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded fair-bit scaling

Both papers for result 200 implement a bounded approximately uniform integer
choice by drawing `z` uniformly from `0,...,Q-1` and returning `⌊M*z/Q⌋`.
When `Q = 2^k`, the input choice uses exactly `k` fair bits.

We prove the exact integer fiber formula in 200-01, equation
`eq:dense-offset-count`, and the pointwise and total-variation error estimates
used in 200-02, Lemma `lem:dyadic-integer-draw`. The arguments are direct
finite arithmetic and have no published-input hypotheses.
-/

open scoped BigOperators

namespace ContingencyTables.FairBits

/-- The bounded scaling map on integer proposals. -/
def scale (M Q z : ℕ) : ℕ := ⌊(M : ℚ) * z / Q⌋₊

/-- The rational floor is exactly the implemented natural integer quotient. -/
lemma scale_eq_div (M Q z : ℕ) : scale M Q z = M * z / Q := by
  rw [scale, ← Nat.cast_mul, Nat.floor_div_eq_div]

/-- The first integer whose scaled value can be at least `β`. -/
def endpoint (M Q β : ℕ) : ℕ := ⌈(β : ℚ) * Q / M⌉₊

/-- The proposal integers that produce a given output. -/
def fiber (M Q β : ℕ) : Finset ℕ :=
  (Finset.range Q).filter fun z => scale M Q z = β

lemma scale_lt {M Q z : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hz : z < Q) :
    scale M Q z < M := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hzq : (z : ℚ) < Q := by exact_mod_cast hz
  rw [scale, Nat.floor_lt (by positivity), div_lt_iff₀ hQq]
  nlinarith

lemma scale_eq_iff {M Q β z : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    scale M Q z = β ↔ endpoint M Q β ≤ z ∧ z < endpoint M Q (β + 1) := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [scale, Nat.floor_eq_iff (by positivity)]
  simp only [endpoint, Nat.ceil_le, Nat.lt_ceil, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_le_iff₀ hMq).mpr
      have h := (le_div_iff₀ hQq).mp hlo
      nlinarith
    · apply (lt_div_iff₀ hMq).mpr
      have h := (div_lt_iff₀ hQq).mp hhi
      nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hQq).mpr
      have h := (div_le_iff₀ hMq).mp hlo
      nlinarith
    · apply (div_lt_iff₀ hQq).mpr
      have h := (lt_div_iff₀ hMq).mp hhi
      nlinarith

lemma endpoint_le_proposal {M Q β : ℕ} (hM : 0 < M) (hβ : β < M) :
    endpoint M Q (β + 1) ≤ Q := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hβq : ((β + 1 : ℕ) : ℚ) ≤ M := by
    exact_mod_cast Nat.succ_le_of_lt hβ
  rw [endpoint, Nat.ceil_le, div_le_iff₀ hMq]
  nlinarith [mul_le_mul_of_nonneg_right hβq (Nat.cast_nonneg Q : (0 : ℚ) ≤ Q)]

/-- The exact preimage interval, including both endpoint conventions. -/
theorem fiber_eq_interval {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hβ : β < M) :
    fiber M Q β = Finset.Ico (endpoint M Q β) (endpoint M Q (β + 1)) := by
  ext z
  simp only [fiber, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  rw [scale_eq_iff hM hQ]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨lt_of_lt_of_le h.2 (endpoint_le_proposal hM hβ), h⟩

/-- This is the ceiling-difference formula used to tabulate the implemented
output law without enumerating all random bit strings. -/
theorem fiber_card {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    (fiber M Q β).card = endpoint M Q (β + 1) - endpoint M Q β := by
  rw [fiber_eq_interval hM hQ hβ, Nat.card_Ico]

lemma endpoint_mono (M Q β : ℕ) :
    endpoint M Q β ≤ endpoint M Q (β + 1) := by
  apply Nat.ceil_mono
  simp only [Nat.cast_add, Nat.cast_one]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  nlinarith [(Nat.cast_nonneg Q : (0 : ℚ) ≤ Q)]

/-- A scaled output has a number of preimages differing by less than one
from the ideal real-valued number `Q/M`. -/
theorem fiber_card_error {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    |((fiber M Q β).card : ℚ) - (Q : ℚ) / M| < 1 := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hlo := Nat.le_ceil ((β : ℚ) * Q / M)
  have hhi := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (β : ℚ) * Q / M by positivity)
  have hlo' := Nat.le_ceil (((β + 1 : ℕ) : ℚ) * Q / M)
  have hhi' := Nat.ceil_lt_add_one
    (show (0 : ℚ) ≤ ((β + 1 : ℕ) : ℚ) * Q / M by positivity)
  rw [fiber_card hM hQ hβ, Nat.cast_sub (endpoint_mono M Q β)]
  simp only [endpoint, Nat.cast_add, Nat.cast_one] at *
  rw [abs_lt]
  have hdiff : ((β : ℚ) + 1) * Q / M = (β : ℚ) * Q / M + (Q : ℚ) / M := by ring
  constructor <;> linarith

/-- The exact mass assigned by the finite uniform proposal. -/
def outputMass (M Q β : ℕ) : ℚ := (fiber M Q β).card / (Q : ℚ)

lemma outputMass_nonnegative (M Q β : ℕ) : 0 ≤ outputMass M Q β := by
  dsimp [outputMass]
  positivity

/-- The masses are normalized on the declared output range. -/
theorem outputMass_total {M Q : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    ∑ β ∈ Finset.range M, outputMass M Q β = 1 := by
  have hc : ∑ β ∈ Finset.range M, (fiber M Q β).card = Q := by
    symm
    simpa only [fiber, Finset.card_range] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.range Q)
        (t := Finset.range M) (f := scale M Q) (by
          intro z hz
          exact Finset.mem_range.mpr (scale_lt hM hQ (Finset.mem_range.mp hz))))
  have hcq : ∑ β ∈ Finset.range M, ((fiber M Q β).card : ℚ) = Q := by
    exact_mod_cast hc
  simp only [outputMass, ← Finset.sum_div, hcq]
  exact div_self (by exact_mod_cast ne_of_gt hQ)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer bin populations for the companion weight evaluator -/

namespace ContingencyTables.CompanionBinPopulation

open scoped BigOperators Classical

variable {C : Type*} [Fintype C]

def coordinatePopulation (B N v : ℕ) : ℚ := B*(FairBits.fiber B N v).card/(N:ℚ)

def population (B : ℕ) (N : C → ℕ) (v : C → ℕ) : ℚ :=
  ∏ c,coordinatePopulation B (N c) (v c)

abbrev Assignments (B : ℕ) (N : C → ℕ) (v : C → ℕ) :=
  (c : C) → {z : ℕ // z ∈ FairBits.fiber B (N c) (v c)}

lemma coordinate_error (B N d v : ℕ) (hB : 0 < B) (hd : 1 ≤ d)
    (hN : 100*d*B ≤ N) (hv : v < B) :
    |coordinatePopulation B N v-1| ≤ 1/(100*(d:ℚ)) := by
  have hdQ : (0:ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNQ : (0:ℚ) < N := by exact_mod_cast hNpos
  have hBQ : (0:ℚ) < B := by exact_mod_cast hB
  have hsize : (100:ℚ)*d*B ≤ N := by exact_mod_cast hN
  have heq : coordinatePopulation B N v-1=
      ((B:ℚ)/N)*(((FairBits.fiber B N v).card:ℚ)-(N:ℚ)/B) := by
    unfold coordinatePopulation
    field_simp [hNQ.ne',hBQ.ne']
  rw [heq,abs_mul,abs_of_nonneg (div_nonneg hBQ.le hNQ.le)]
  calc
    _ ≤ ((B:ℚ)/N)*1 := mul_le_mul_of_nonneg_left
      (FairBits.fiber_card_error hB hNpos hv).le (by positivity)
    _ = (B:ℚ)/N := mul_one _
    _ ≤ _ := by
      rw [div_le_div_iff₀ hNQ (by positivity : (0:ℚ) < 100*d)]
      nlinarith

theorem coordinate_nonempty (B N d v : ℕ) (hB : 0 < B) (hd : 1 ≤ d)
    (hN : 100*d*B ≤ N) (hv : v < B) : (FairBits.fiber B N v).Nonempty := by
  have hh := (abs_le.mp (coordinate_error B N d v hB hd hN hv)).1
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 1/(100*(d:ℚ)) < 1 := by
    rw [div_lt_one (by positivity : (0:ℚ) < 100*d)]
    linarith
  have hp : 0 < coordinatePopulation B N v := by linarith
  apply Finset.card_pos.mp
  by_contra hzero
  have hz : (FairBits.fiber B N v).card=0 := by omega
  simp only [coordinatePopulation,hz,Nat.cast_zero,mul_zero,zero_div] at hp
  exact lt_irrefl _ hp

end ContingencyTables.CompanionBinPopulation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published analytic input for result 200

Prékopa, *On logarithmic concave measures and functions*, Acta Sci. Math.
(Szeged) 34 (1973), 335–343, Theorem 3, equation (2.3), with two source
functions. Source: https://acta.bibl.u-szeged.hu/14411/1/math_034_335-343.pdf
The one-dimensional input is Leindler (1972), *On a certain converse of
Hölder's inequality II*, 217–223, as identified in Prékopa's §2.

The finite-box specialization allows positive continuous functions on a
common compact coordinate box and finite unions of open boxes.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

abbrev Point (q : ℕ) := Fin q → ℝ

end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuous and dyadic bin weights

The actual floor-rounded weights used by the dense grid sampler. Convexity
of the penalty implies log-concavity of its density, and local changes of
the scaled penalty give explicit comparisons with the dyadic bin weights.
-/

namespace ContingencyTables.DenseWeights

noncomputable section

def density {X : Type*} (A : ℝ) (p : X → ℝ) (x : X) : ℝ :=
  (2 : ℝ) ^ (-(A * p x))

def binWeight {X : Type*} (A : ℝ) (p : X → ℝ) (v : X) : ℝ :=
  (2 : ℝ) ^ (-((⌊A * p v⌋ : ℤ) : ℝ))

end

end ContingencyTables.DenseWeights

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual maximum-forest cut coefficients of tree completions -/

namespace ContingencyTables.ForestAffineCoefficients

open scoped BigOperators Classical
open CompanionFactorialApplication GraphIntegralCompletion GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def edge (t : I×J) : Sym2 (I⊕J) := s(Sum.inl t.1,Sum.inr t.2)

noncomputable def cutVertex (A : Instance I J) (t : TreeCell A.T) : I⊕J :=
  Classical.choose (exists_root_avoiding_side A.T A.hT t.property
    (componentRoot A.T (.inl t.val.1)) (componentRoot_reachable A.T (.inl t.val.1)).symm)

noncomputable def cutSide (A : Instance I J) (t : TreeCell A.T) (v : I⊕J) : Bool :=
  side (A.T.deleteEdges {edge t.val}) (cutVertex A t) v

noncomputable def sign (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℝ :=
  indicator (cutSide A t (.inl a.1))-indicator (cutSide A t (.inr a.2))

noncomputable def coefficient (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℝ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -sign A t a/sign A t t.val else 0

end ContingencyTables.ForestAffineCoefficients

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original integral forest solution is the cut-defined affine completion -/

namespace ContingencyTables.ForestAffineCoefficients

open scoped BigOperators Classical
open CompanionFactorialApplication GraphIntegralCompletion GraphCompletionCounts
open ForestCapacity ForestCut ForestPhysicalCompletion MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallContribution (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℝ) : ℝ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    indicator (cutSide A t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      indicator (cutSide A t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

noncomputable def offset (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℝ) : ℝ :=
  A.X t.val.1 t.val.2-smallContribution A t x q/sign A t t.val-
    ∑ a : I×J,coefficient A t a*(A.X a.1 a.2:ℝ)

end ContingencyTables.ForestAffineCoefficients

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def intervalCost (x : ℝ) : ℝ := max 0 (max (-x) (x-1))

noncomputable def normalizedOffset (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) : ℝ :=
  offset A t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))/(A.b t.val.1 t.val.2:ℝ)

noncomputable def normalizedCoefficient (A : Instance I J) (B : ℝ) (t : TreeCell A.T)
    (f : FreeCell A.small A.T) : ℝ :=
  coefficient A t f.val*((A.b f.val.1 f.val.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)

noncomputable def rootConstant (A : Instance I J) (x q : I → J → ℤ) : ℝ :=
  ∑ a,if ForestPenaltyApplication.rootFlag A.T a then
    |(signedResidual A.small A.T A.r A.c x q 0 a:ℝ)| else 0

lemma free_card_le (A : Instance I J) : Fintype.card (FreeCell A.small A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer free assignments use the original scaled affine tree values -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def integerCube (A : Instance I J) (B : ℝ) (f : FreeIndex A.small A.T A.b) :
    FreeCell A.small A.T → ℝ := fun a => B*(f a).val/((A.b a.val.1 a.val.2:ℝ)+1)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable abbrev dimension (A : Instance I J) := Fintype.card (FreeCell A.small A.T)

noncomputable def index (A : Instance I J) : Fin (dimension A) ≃ FreeCell A.small A.T :=
  (Fintype.equivFin _).symm

noncomputable def pull (A : Instance I J) (v : Fin (dimension A) → ℝ) : FreeCell A.small A.T → ℝ :=
  fun f => v ((index A).symm f)

noncomputable def binWidth (A : Instance I J) (C : ℝ) : ℝ := 16*C*(A.d:ℝ)^2

noncomputable def height (A : Instance I J) (C : ℝ) : ℝ := 10*C*(A.d:ℝ)^2*((A.W:ℝ)+1)

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Four-cycle moves for the small-entry estimate

The move raises the marked cell, lowers one donor in its row and one in
its column, and raises the opposite corner. No upper cell bound is used.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The signed four-cycle update, before converting back to natural entries. -/
def fourCycleInt (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (i : I) (j : J) : ℤ :=
  X i j + ((if i = a then 1 else 0) - (if i = b then 1 else 0)) *
    ((if j = s then 1 else 0) - (if j = t then 1 else 0)) * v

omit [Fintype I] [Fintype J] in
theorem fourCycleInt_nonnegative (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ)
    (hab : a ≠ b) (hst : s ≠ t) (hrow : v ≤ X a t) (hcol : v ≤ X b s)
    (i : I) (j : J) : 0 ≤ fourCycleInt X a b s t v i j := by
  by_cases hi : i = a
  · subst i
    by_cases hj : j = s
    · subst j
      simp [fourCycleInt, hab, hst]
      omega
    · by_cases hj' : j = t
      · subst j
        simp [fourCycleInt, hab, Ne.symm hst]
        omega
      · simp [fourCycleInt, hab, hj, hj']
  · by_cases hi' : i = b
    · subst i
      by_cases hj : j = s
      · subst j
        simp [fourCycleInt, Ne.symm hab, hst]
        omega
      · by_cases hj' : j = t
        · subst j
          simp [fourCycleInt, Ne.symm hab, Ne.symm hst]
          omega
        · simp [fourCycleInt, Ne.symm hab, hj, hj']
    · simp [fourCycleInt, hi, hi']

omit [Fintype I] in
theorem fourCycleInt_rows (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (i : I) :
    ∑ j, fourCycleInt X a b s t v i j = ∑ j, (X i j : ℤ) := by
  simp only [fourCycleInt, sum_add_distrib, ← sum_mul, ← mul_sum, sum_sub_distrib]
  simp

omit [Fintype J] in
theorem fourCycleInt_columns (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (j : J) :
    ∑ i, fourCycleInt X a b s t v i j = ∑ i, (X i j : ℤ) := by
  simp only [fourCycleInt, sum_add_distrib, ← sum_mul, sum_sub_distrib]
  simp

/-- A nonnegative four-cycle is again a table with precisely the same margins. -/
def fourCycle {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) : Table r c := by
  let Y := fun i j => (fourCycleInt X.val a b s t v i j).toNat
  have hcast (i : I) (j : J) : (Y i j : ℤ) = fourCycleInt X.val a b s t v i j :=
    Int.toNat_of_nonneg (fourCycleInt_nonnegative X.val a b s t v hab hst hrow hcol i j)
  refine ⟨Y, ?_, ?_⟩
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [hcast]
    rw [fourCycleInt_rows, ← Nat.cast_sum, X.property.1 i]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [hcast]
    rw [fourCycleInt_columns, ← Nat.cast_sum, X.property.2 j]

@[simp] theorem fourCycle_cast {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) (i : I) (j : J) :
    ((fourCycle X a b s t v hab hst hrow hcol).val i j : ℤ) =
      fourCycleInt X.val a b s t v i j :=
  Int.toNat_of_nonneg (fourCycleInt_nonnegative X.val a b s t v hab hst hrow hcol i j)

@[simp] theorem fourCycle_marked {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) :
    (fourCycle X a b s t v hab hst hrow hcol).val a s = X.val a s + v := by
  apply Int.natCast_inj.mp
  rw [fourCycle_cast]
  simp [fourCycleInt, hab, hst]

/-- Double counting the four-cycle moves. The source marked value and two
donor labels suffice to reverse a move: the target marked value determines
the step. The donor-existence condition is separated from the injection so
that the margin estimate can be checked independently. -/
theorem small_entry_count_of_donors {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (t V : ℕ)
    (hdonors : ∀ X : Table r c, X.val a s < t →
      ∃ p : I × J, a ≠ p.1 ∧ s ≠ p.2 ∧ V ≤ X.val a p.2 ∧ V ≤ X.val p.1 s) :
    Fintype.card {X : Table r c // X.val a s < t} * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * t) := by
  classical
  let Bad := {X : Table r c // X.val a s < t}
  let donor (X : Bad) : I × J := Classical.choose (hdonors X.val X.property)
  have hdonor (X : Bad) : a ≠ (donor X).1 ∧ s ≠ (donor X).2 ∧
      V ≤ X.val.val a (donor X).2 ∧ V ≤ X.val.val (donor X).1 s :=
    Classical.choose_spec (hdonors X.val X.property)
  let next (X : Bad) (v : Fin V) : Table r c :=
    fourCycle X.val a (donor X).1 s (donor X).2 (v.val + 1)
      (hdonor X).1 (hdonor X).2.1
      ((Nat.succ_le_of_lt v.isLt).trans (hdonor X).2.2.1)
      ((Nat.succ_le_of_lt v.isLt).trans (hdonor X).2.2.2)
  let encode : Bad × Fin V → Table r c × ((I × J) × Fin t) := fun p =>
    (next p.1 p.2, donor p.1, ⟨p.1.val.val a s, p.1.property⟩)
  have hinj : Function.Injective encode := by
    rintro ⟨X, v⟩ ⟨Y, w⟩ heq
    have hout : next X v = next Y w := congrArg Prod.fst heq
    have hd : donor X = donor Y := congrArg (fun z => z.2.1) heq
    have hh : X.val.val a s = Y.val.val a s :=
      congrArg (fun z => z.2.2.val) heq
    have hmarked := congrArg (fun Z : Table r c => Z.val a s) hout
    have hv : v = w := by
      apply Fin.ext
      dsimp [next] at hmarked
      simp only [fourCycle_marked] at hmarked
      omega
    have hXY : X.val = Y.val := by
      apply Subtype.ext
      funext i j
      have h := congrArg (fun Z : Table r c => (Z.val i j : ℤ)) hout
      dsimp [next] at h
      simp only [fourCycle_cast, fourCycleInt] at h
      rw [← hd, ← hv] at h
      exact Int.natCast_inj.mp (add_right_cancel h)
    exact Prod.ext (Subtype.ext hXY) hv
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hinj

omit [Fintype I] [DecidableEq I] in
theorem donor_from_line (x : J → ℕ) (s : J) (d V : ℕ)
    (hsize : Fintype.card J ≤ d) (hV : 0 < V)
    (hmass : x s + d * V ≤ ∑ j, x j) :
    ∃ t, s ≠ t ∧ V ≤ x t := by
  by_contra hn
  have hlt (j : J) : (if j = s then 0 else x j) < V := by
    by_cases hj : j = s
    · simpa [hj] using hV
    · simp only [hj, ite_false]
      by_contra h
      exact hn ⟨j, Ne.symm hj, by omega⟩
  have hsum : (∑ j, if j = s then 0 else x j) < Fintype.card J * V := by
    have h := sum_lt_sum_of_nonempty (s := (univ : Finset J))
      ⟨s, mem_univ s⟩ (fun j _ => hlt j)
    simpa using h
  have hdecomp : (∑ j, if j = s then 0 else x j) + x s = ∑ j, x j := by
    calc
      _ = (∑ j, if j = s then 0 else x j) + (∑ j, if j = s then x s else 0) := by
        simp
      _ = ∑ j, ((if j = s then 0 else x j) + (if j = s then x s else 0)) :=
        sum_add_distrib.symm
      _ = ∑ j, x j := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j = s <;> simp [hj]
  have hmul : Fintype.card J * V ≤ d * V := Nat.mul_le_mul_right V hsize
  omega

/-- Margin lower bounds supply the donors for each small marked entry.
`d * V + t ≤ a₀` is the discrete form of the manuscript's choice
`V = floor (a₀/(2d))` with `2t ≤ a₀`. -/
theorem small_entry_count {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ d t V : ℕ)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s)
    (hV : 0 < V) (hscale : d * V + t ≤ a₀) :
    Fintype.card {X : Table r c // X.val a s < t} * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * t) := by
  apply small_entry_count_of_donors
  intro X hX
  obtain ⟨t', ht', hXt'⟩ := donor_from_line (X.val a) s d V hcols hV (by
    rw [X.property.1 a]
    omega)
  obtain ⟨b, hb, hXb⟩ := donor_from_line (fun i => X.val i s) a d V hrows hV (by
    rw [X.property.2 s]
    omega)
  exact ⟨(b, t'), hb, ht', hXt', hXb⟩

/-- The complete small-entry estimate of paper 200-01, expressed as the
uniform finite counting probability. It also covers zero rows or columns
away from the marked cell. -/
theorem small_entry_probability {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s)
    (ha₀ : 4 * d ≤ a₀) (ht : 2 * t ≤ a₀) :
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤ 4 * t * (d : ℝ) ^ 3 / a₀ := by
  classical
  let V := a₀ / (2 * d)
  have hV : 0 < V := Nat.div_pos (by omega) (by omega)
  have hfloor := Nat.mul_div_le a₀ (2 * d)
  change 2 * d * V ≤ a₀ at hfloor
  have hscale : d * V + t ≤ a₀ := by nlinarith [hfloor, ht]
  have hcount := small_entry_count a s a₀ d t V hrows hcols hrow hcol hV hscale
  have hmod := Nat.mod_lt a₀ (show 0 < 2 * d by omega)
  have hdiv := Nat.mod_add_div a₀ (2 * d)
  change a₀ % (2 * d) + 2 * d * V = a₀ at hdiv
  have hhalf : a₀ ≤ 4 * d * V := by nlinarith
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  have haR : (0 : ℝ) < a₀ := by exact_mod_cast (show 0 < a₀ by omega)
  have hfR : (a₀ : ℝ) ≤ 4 * d * V := by exact_mod_cast hhalf
  have hcR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * (t : ℝ)) := by
    exact_mod_cast hcount
  have hsR : (Fintype.card I : ℝ) * Fintype.card J ≤ (d : ℝ) ^ 2 := by
    have h := Nat.mul_le_mul hrows hcols
    exact_mod_cast (show Fintype.card I * Fintype.card J ≤ d ^ 2 by
      simpa only [pow_two] using h)
  apply (div_le_div_iff₀ hcardR haR).mpr
  calc
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) * a₀ ≤
        Fintype.card {X : Table r c // X.val a s < t} * (4 * d * V) :=
      mul_le_mul_of_nonneg_left hfR (Nat.cast_nonneg _)
    _ = (4 * d) * (Fintype.card {X : Table r c // X.val a s < t} * (V : ℝ)) := by ring
    _ ≤ (4 * d) * (Fintype.card (Table r c) *
        (Fintype.card I * Fintype.card J * (t : ℝ))) :=
      mul_le_mul_of_nonneg_left hcR (by positivity)
    _ ≤ (4 * d) * (Fintype.card (Table r c) * ((d : ℝ) ^ 2 * t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hsR (Nat.cast_nonneg _)
    _ = (4 * t * (d : ℝ) ^ 3) * Fintype.card (Table r c) := by ring

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Padding and the successful-table bijection

Padding a designated rectangle by a fixed amount gives a bijection from
original tables to enlarged-margin tables whose entries dominate the
padding. Each successful joint object therefore yields exactly one table.
-/

namespace ContingencyTables

open Finset
open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The union bound as an injection with a deterministically chosen bad
cell label. This counts each bad table once, even if several entries fail. -/
theorem card_exists_le_sum {α K : Type*} [Fintype α] [Fintype K]
    (P : K → α → Prop) :
    Fintype.card {x : α // ∃ k, P k x} ≤ ∑ k, Fintype.card {x : α // P k x} := by
  classical
  let encode : {x : α // ∃ k, P k x} → Σ k, {x : α // P k x} :=
    fun x => ⟨Classical.choose x.property, x.val, Classical.choose_spec x.property⟩
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Σ k, {x : α // P k x} => z.2.val) h
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective encode hinj

section SuccessFraction

theorem fraction_not_exists {α K : Type*} [Fintype α] [Fintype K]
    (P : K → α → Prop) (E : ℝ) (hcard : (0 : ℝ) < Fintype.card α)
    (hbound : ∀ k, (Fintype.card {x : α // P k x} : ℝ) / Fintype.card α ≤ E) :
    1 - Fintype.card K * E ≤
      (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) / Fintype.card α := by
  have hunion := card_exists_le_sum P
  have hunionR : (Fintype.card {x : α // ∃ k, P k x} : ℝ) ≤
      ∑ k, (Fintype.card {x : α // P k x} : ℝ) := by
    have h : (Fintype.card {x : α // ∃ k, P k x} : ℝ) ≤
        (∑ k, Fintype.card {x : α // P k x} : ℕ) := Nat.cast_le.mpr hunion
    simpa only [Nat.cast_sum] using h
  have hbad : (Fintype.card {x : α // ∃ k, P k x} : ℝ) / Fintype.card α ≤
      Fintype.card K * E := by
    calc
      _ ≤ (∑ k, (Fintype.card {x : α // P k x} : ℝ)) / Fintype.card α :=
        div_le_div_of_nonneg_right hunionR hcard.le
      _ = ∑ k, (Fintype.card {x : α // P k x} : ℝ) / Fintype.card α :=
        Finset.sum_div _ _ _
      _ ≤ ∑ _k : K, E := sum_le_sum fun k _ => hbound k
      _ = _ := by simp
  have hpart : Fintype.card {x : α // ¬∃ k, P k x} +
      Fintype.card {x : α // ∃ k, P k x} = Fintype.card α := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  have hpartR : (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) +
      Fintype.card {x : α // ∃ k, P k x} = Fintype.card α := by exact_mod_cast hpart
  have hsum : (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) / Fintype.card α +
      (Fintype.card {x : α // ∃ k, P k x} : ℝ) / Fintype.card α = 1 := by
    rw [← add_div, hpartR, div_self (ne_of_gt hcard)]
  linarith

end SuccessFraction

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ResidualMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact correction by a finite residual mixture

Finite probability arithmetic gives the residual correction used in exact
sampling. The construction is that of Göbel, Liu, Manurangsi and Pappik,
*Perfect sampling from rapidly mixing Markov chains*, arXiv:2410.00882v2
(2024), §3.1, Algorithm 1 and Theorem 6.

All probabilities are rational, as required for the finite fair-bit sampler.
-/

open scoped BigOperators

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

/-- A finite probability law with exactly represented rational masses. -/
structure RationalLaw (α : Type*) [Fintype α] where
  mass : α → ℚ
  nonnegative : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

variable [Nonempty α]

lemma card_pos : (0 : ℚ) < Fintype.card α := by
  exact_mod_cast Fintype.card_pos

/-- The uniform mass on a nonempty finite space. -/
def uniformMass : ℚ := 1 / Fintype.card α

lemma uniformMass_pos : 0 < uniformMass (α := α) := by
  exact div_pos (by norm_num) card_pos

lemma uniformMass_total : ∑ _x : α, uniformMass (α := α) = 1 := by
  simp only [uniformMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel (ne_of_gt card_pos)

end ContingencyTables.ResidualMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Free coordinates of a dense completion block

`none` denotes the pivot row or column. The free coordinates are the other
cells. These are the manuscript's actual affine completion formulas; the
row and column constraints hold identically, and feasible tables are
uniquely determined by their free cells.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def table (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) : Option I → Option J → ℝ
  | some i, some j => w i j * u (i, j)
  | some i, none => R (some i) - ∑ j, w i j * u (i, j)
  | none, some j => P (some j) - ∑ i, w i j * u (i, j)
  | none, none => R none - ∑ j, P (some j) + ∑ i, ∑ j, w i j * u (i, j)

theorem table_rows (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (i : Option I) : ∑ j, table R P w u i j = R i := by
  rw [Fintype.sum_option]
  cases i with
  | some i => simp only [table]; ring
  | none =>
    simp only [table, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => w i j * u (i, j))]
    ring

theorem table_columns (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (htotal : ∑ i, R i = ∑ j, P j) (j : Option J) :
    ∑ i, table R P w u i j = P j := by
  rw [Fintype.sum_option]
  cases j with
  | some j => simp only [table]; ring
  | none =>
    simp only [table, Finset.sum_sub_distrib]
    simp only [Fintype.sum_option] at htotal
    linarith

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cut-face cover of the interpolation shell

The continuous shell in the conductance argument is covered, except for
the null grid hyperplanes, by the finite collection of interior cut-face
tubes. No exterior faces or segment general-position hypotheses occur.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Grid (K : ℕ) := I → Set.Icc (0 : ℤ) ((K : ℤ) - 1)

def corner {K : ℕ} (a : Grid (I := I) K) : I → ℤ := fun j => (a j).val

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conductance geometry for the actual dense penalty

The free table coordinates are reindexed by `Fin q`. The bin and cut-tube
density comparisons below follow from the actual margins and integer
widths. Thus the weighted cut theorem has no assumed penalty regularity
or bin comparison when used for the dense completion sampler.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def realCorner {K : ℕ} (a : Grid (I := Fin q) K) : Fin q → ℝ :=
  fun j => (corner a j : ℝ)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MetropolisChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted Metropolis chain

The holding probability, stationary law, and cut flow are proved from
positive weights, symmetric proposals, and the proposal-degree bound.
Only the final Poincaré consequence uses the explicit published Cheeger input.
-/

namespace ContingencyTables.MetropolisChain

open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

def normalizer (w : X → ℝ) : ℝ := ∑ x, w x

theorem normalizer_pos (w : X → ℝ) (hw : ∀ x, 0 < w x) : 0 < normalizer w := by
  exact Finset.sum_pos (fun x _ => hw x) Finset.univ_nonempty

end

end ContingencyTables.MetropolisChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMetropolis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual dyadic axis-proposal chain -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

def binProposal (d : ℕ) : ℝ := 1 / (2 : ℝ) ^ Nat.clog 2 (8 * d)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite bin chain for the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The dyadic proposal is valid already at `d = 1`, including the
zero-dimensional grid. -/
lemma proposal_bounds (d : ℕ) (hd : 1 ≤ d) :
    0 < binProposal d ∧ 1/(16*(d:ℝ)) ≤ binProposal d ∧
      binProposal d ≤ 1/(8*(d:ℝ)) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 8*d := by omega
  have hlo := Nat.le_pow_clog (by decide : 1 < 2) (8*d)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hpos := Nat.clog_pos (by decide : 1 < 2) hn
  have hhi : 2^Nat.clog 2 (8*d) ≤ 16*d := by
    have he : 2^Nat.clog 2 (8*d) = 2^(Nat.clog 2 (8*d)).pred*2 := by
      conv_lhs => rw [←Nat.succ_pred_eq_of_pos hpos]
      exact pow_succ _ _
    rw [he]
    omega
  have hloR : 8*(d:ℝ) ≤ (2:ℝ)^Nat.clog 2 (8*d) := by exact_mod_cast hlo
  have hhiR : (2:ℝ)^Nat.clog 2 (8*d) ≤ 16*(d:ℝ) := by exact_mod_cast hhi
  refine ⟨by unfold binProposal; positivity,?_,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hhiR
  · exact one_div_le_one_div_of_le (by positivity) hloR

lemma proposal_degree (A : Instance I J) :
    ((2*dimension A:ℕ):ℝ)*binProposal A.d ≤ 1/4 := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have he : (dimension A:ℝ) ≤ A.d := by exact_mod_cast ForestScaledPenalty.free_card_le A
  calc
    _ ≤ (2*(dimension A:ℝ))*(1/(8*(A.d:ℝ))) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (proposal_bounds A.d A.hd).2.2 (by positivity)
    _ ≤ (2*(A.d:ℝ))*(1/(8*(A.d:ℝ))) := by gcongr
    _ = 1/4 := by field_simp; ring

def cutConstant (A : Instance I J) (K : ℕ) : ℝ := binProposal A.d/(128*(A.d:ℝ)*K)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative mixing for the companion's actual evaluator grid -/

namespace ContingencyTables.CompanionOracleDensity

open GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def mixingConstant (A : Instance I J) (K : ℕ) : ℝ := 2*(10000*(A.d:ℝ)^2*K)^2

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def integerPoint (A : Instance I J) (C : ℝ) (f : FreeIndex A.small A.T A.b) :
    Fin (dimension A) → ℝ := fun i => integerCube A (binWidth A C) f (index A i)

def integerBin (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) : Grid (I := Fin (dimension A)) K := fun i =>
  let t := index A i
  ⟨(FairBits.scale K (A.b t.val.1 t.val.2+1) (f t).val:ℤ),by
    constructor
    · positivity
    · have hh := FairBits.scale_lt hK (Nat.succ_pos _) (f t).isLt
      have hhZ : (FairBits.scale K (A.b t.val.1 t.val.2+1) (f t).val:ℤ)<K := by
        exact_mod_cast hh
      omega⟩

def integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) : Finset (FreeIndex A.small A.T A.b) :=
  Finset.univ.filter (fun f => integerBin A K hK f=v)

def assignmentCount (A : Instance I J) : ℕ := Fintype.card (FreeIndex A.small A.T A.b)


end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer bins have the manuscript's Cartesian populations -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def freeRange (A : Instance I J) (t : FreeCell A.small A.T) : ℕ := A.b t.val.1 t.val.2+1

def naturalBin (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : ℕ := ((v ((index A).symm t)).val).toNat

lemma naturalBin_cast (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : (naturalBin A v t:ℤ)=(v ((index A).symm t)).val :=
  Int.toNat_of_nonneg (v ((index A).symm t)).property.1

lemma naturalBin_lt (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : naturalBin A v t<K := by
  have hh := (v ((index A).symm t)).property.2
  have hc := naturalBin_cast A v t
  omega

lemma integerBin_eq_iff (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (f : FreeIndex A.small A.T A.b) :
    integerBin A K hK f=v ↔ ∀ t,FairBits.scale K (freeRange A t) (f t).val=naturalBin A v t := by
  constructor
  · intro h t
    have hh := congrArg (fun w : Grid (I := Fin (dimension A)) K =>
      (w ((index A).symm t)).val) h
    change (FairBits.scale K (freeRange A (index A ((index A).symm t)))
      (f (index A ((index A).symm t))).val:ℤ)=(v ((index A).symm t)).val at hh
    rw [Equiv.apply_symm_apply,←naturalBin_cast A v t] at hh
    exact_mod_cast hh
  · intro h
    funext i
    apply Subtype.ext
    have hh := congrArg (fun n : ℕ => (n:ℤ)) (h (index A i))
    rw [naturalBin_cast,Equiv.symm_apply_apply] at hh
    exact hh

def integerFiberEquiv (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    {f // f∈integerFiber A K hK v} ≃
      CompanionBinPopulation.Assignments K (freeRange A) (naturalBin A v) where
  toFun f t := ⟨(f.val t).val,by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (f.val t).isLt,?_⟩
    exact (integerBin_eq_iff A K hK v f.val).mp (Finset.mem_filter.mp f.property).2 t⟩
  invFun x := ⟨(fun t => ⟨(x t).val,by
    exact Finset.mem_range.mp (Finset.mem_filter.mp (x t).property).1⟩),by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply (integerBin_eq_iff A K hK v _).mpr
    intro t
    exact (Finset.mem_filter.mp (x t).property).2⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    exact Fin.ext rfl
  right_inv x := by
    funext t
    exact Subtype.ext rfl

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FirstSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-success law and finite-law error bounds

The bounded outer sampler repeats independent trials and uses a fixed
feasible fallback. Its geometric output law has a stationary uniform-mixture
specialization. Total-variation bounds are preserved by deterministic output
maps.
-/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def variation (p q : RationalLaw α) : ℚ :=
  (∑ x, |p.mass x - q.mass x|) / 2

variable [Nonempty α]

def uniformLaw : RationalLaw α where
  mass := fun _ => uniformMass (α := α)
  nonnegative := fun _ => uniformMass_pos.le
  total := uniformMass_total

omit [Nonempty α] in
def mapLaw [DecidableEq β] (p : RationalLaw α) (f : α → β) : RationalLaw β where
  mass := fun y => ∑ x, if f x = y then p.mass x else 0
  nonnegative := fun y => Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact p.nonnegative x
    · rfl
  total := by
    rw [Finset.sum_comm]
    simpa using p.total

omit [Nonempty α] in
/-- Deterministic postprocessing contracts total variation, as used for
the map selecting the first successful trial and unpadding its table. -/
theorem variation_map [DecidableEq β] (p q : RationalLaw α) (f : α → β) :
    variation (mapLaw p f) (mapLaw q f) ≤ variation p q := by
  unfold variation
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y, |∑ x, if f x = y then p.mass x - q.mass x else 0| := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      simp only [mapLaw, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ ≤ ∑ y, ∑ x, |if f x = y then p.mass x - q.mass x else 0| := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p.mass x - q.mass x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [abs_ite, abs_zero]
      simp

omit [Nonempty α] in
def productLaw (p : RationalLaw α) (q : RationalLaw β) : RationalLaw (α × β) where
  mass := fun z => p.mass z.1 * q.mass z.2
  nonnegative := fun z => mul_nonneg (p.nonnegative z.1) (q.nonnegative z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite rational laws transported through bijections -/

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

@[ext] theorem RationalLaw.ext {p q : RationalLaw α} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

end ContingencyTables.ResidualMixture

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def equivLaw (e : α ≃ β) (p : RationalLaw α) : RationalLaw β where
  mass := fun y => p.mass (e.symm y)
  nonnegative := fun y => p.nonnegative (e.symm y)
  total := by
    have h := Fintype.sum_equiv e p.mass (fun y => p.mass (e.symm y)) (fun x => by simp)
    rw [← h, p.total]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteFairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite binary words and their exact uniform experiment laws -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

def binaryWordEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight (fun _ : Fin k => finTwoEquiv.symm)).trans finFunctionFinEquiv

def splitWordEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ ((Fin k → Bool) × (Fin l → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def pairWordEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ (Fin (2 ^ k) × Fin (2 ^ l)) :=
  (splitWordEquiv k l).trans (Equiv.prodCongr (binaryWordEquiv k) (binaryWordEquiv l))

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

theorem uniform_equiv (e : α ≃ β) :
    equivLaw e (uniformLaw (α := α)) = uniformLaw (α := β) := by
  apply RationalLaw.ext
  funext y
  change 1 / (Fintype.card α : ℚ) = 1 / (Fintype.card β : ℚ)
  rw [Fintype.card_congr e]

theorem uniform_product :
    productLaw (uniformLaw (α := α)) (uniformLaw (α := β)) = uniformLaw (α := α × β) := by
  apply RationalLaw.ext
  funext y
  change (1 / (Fintype.card α : ℚ)) * (1 / (Fintype.card β : ℚ)) = 1 / (Fintype.card (α × β) : ℚ)
  rw [Fintype.card_prod, Nat.cast_mul]
  ring

omit [Nonempty α] [Nonempty β] in
theorem map_equiv [DecidableEq β] {γ : Type*} [Fintype γ] [DecidableEq γ]
    (e : α ≃ β) (p : RationalLaw α) (f : β → γ) :
    mapLaw (equivLaw e p) f = mapLaw p (fun x => f (e x)) := by
  apply RationalLaw.ext
  funext z
  symm
  change (∑ x, if f (e x) = z then p.mass x else 0) =
    ∑ y, if f y = z then p.mass (e.symm y) else 0
  apply Fintype.sum_equiv e
  intro x
  simp

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RejectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite repeated-trial laws and their approximation error -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

def pointLaw (z : β) : RationalLaw β where
  mass := fun y => if y = z then 1 else 0
  nonnegative := fun y => by split_ifs <;> norm_num
  total := by simp

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent composition of finite rational transition experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def bindLaw (p : RationalLaw α) (K : α → RationalLaw β) : RationalLaw β where
  mass := fun y => ∑ x, p.mass x * (K x).mass y
  nonnegative := fun y => Finset.sum_nonneg fun x _ => mul_nonneg (p.nonnegative x) ((K x).nonnegative y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (K _).total, mul_one, p.total]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact laws of a walk driven by independent fixed-length Boolean words -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def wordWalk {k : ℕ} (step : α → (Fin k → Bool) → α) (a : α) :
    (n : ℕ) → (Fin n → Fin k → Bool) → α
  | 0, _ => a
  | n + 1, bits => step (wordWalk step a n (Fin.init bits)) (bits (Fin.last n))

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite product laws for the independent bounded offset draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

def piLaw {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, RationalLaw (α i)) : RationalLaw (∀ i, α i) where
  mass := fun x => ∏ i, (p i).mass (x i)
  nonnegative := fun x => Finset.prod_nonneg (fun i _ => (p i).nonnegative (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(p _).total, Finset.prod_const_one]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedOffsetLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded scaling laws for the dense offsets -/

namespace ContingencyTables.FairBits

open scoped BigOperators
open ResidualMixture FirstSuccess

def scaledLaw (M k : ℕ) (hM : 0 < M) : RationalLaw (Fin M) where
  mass := fun β => outputMass M (2 ^ k) β.val
  nonnegative := fun β => outputMass_nonnegative _ _ _
  total := by
    rw [Fin.sum_univ_eq_sum_range]
    exact outputMass_total hM (pow_pos (by decide) _)

def uniformIntLaw (M : ℕ) (hM : 0 < M) : RationalLaw (Fin M) where
  mass := fun _ => 1 / (M : ℚ)
  nonnegative := fun _ => by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast ne_of_gt hM)

def offsetBitLength (w h d : ℕ) : ℕ := Nat.clog 2 (w + 1) + 4 * (h + d)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteScaledDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded quotient draw is realized by an actual Boolean word -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

def scaledInteger (M k : ℕ) (hM : 0 < M) (z : Fin (2 ^ k)) : Fin M :=
  ⟨M * z.val / 2 ^ k, by
    rw [← scale_eq_div]
    exact scale_lt hM (pow_pos (by decide) k) z.isLt⟩

def scaledBitInteger (M k : ℕ) (hM : 0 < M) (bits : Fin k → Bool) : Fin M :=
  scaledInteger M k hM (binaryWordEquiv k bits)

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalMapProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent finite coordinate maps and uniform product laws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

theorem mapLaw_comp {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (p : RationalLaw A) (f : A → B) (g : B → C) :
    mapLaw (mapLaw p f) g = mapLaw p (fun x => g (f x)) := by
  apply RationalLaw.ext
  funext z
  change (∑ y, if g y = z then ∑ x, if f x = y then p.mass x else 0 else 0) = _
  calc
    _ = ∑ y, ∑ x, if f x = y then (if g y = z then p.mass x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp [mapLaw]

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer intervals inside the companion evaluator bins -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def intervalSize (K N beta : ℕ) : ℕ :=
  FairBits.endpoint K N (beta+1)-FairBits.endpoint K N beta

/-- Each offset is sent to its integer by adding the exact lower ceiling
endpoint. This is the actual source interval, not a cardinality-only choice. -/
def intervalEquiv (K N beta : ℕ) (hK : 0 < K) (hN : 0 < N) (hb : beta < K) :
    Fin (intervalSize K N beta) ≃ {z : ℕ // z∈FairBits.fiber K N beta} where
  toFun x := ⟨FairBits.endpoint K N beta+x.val,by
    rw [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico]
    have hh := x.isLt
    unfold intervalSize at hh
    omega⟩
  invFun x := ⟨x.val-FairBits.endpoint K N beta,by
    have hx : FairBits.endpoint K N beta ≤ x.val ∧
        x.val < FairBits.endpoint K N (beta+1) := by
      simpa only [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico] using x.property
    unfold intervalSize
    omega⟩
  left_inv x := by apply Fin.ext; simp
  right_inv x := by
    apply Subtype.ext
    have hx : FairBits.endpoint K N beta ≤ x.val ∧
        x.val < FairBits.endpoint K N (beta+1) := by
      simpa only [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico] using x.property
    dsimp only
    omega

def binSize (A : Instance I J) (K : ℕ) (v : Grid (I := Fin (dimension A)) K)
    (i : Fin (dimension A)) : ℕ :=
  intervalSize K (freeRange A (index A i)) (naturalBin A v (index A i))

theorem binSize_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) (i : Fin (dimension A)) :
    0 < binSize A K v i := by
  have hp := CompanionBinPopulation.coordinate_nonempty K (freeRange A (index A i)) A.d
    (naturalBin A v (index A i)) hK A.hd (by
      have hb := (A.hlarge (index A i).val.1 (index A i).val.2 (index A i).property.1).1
      unfold freeRange
      omega) (naturalBin_lt A v (index A i))
  have hc := Finset.card_pos.mpr hp
  have hN : 0 < freeRange A (index A i) := Nat.succ_pos _
  rw [FairBits.fiber_card hK hN (naturalBin_lt A v (index A i))] at hc
  exact hc

def binOffsetsEquiv (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    ((i : Fin (dimension A)) → Fin (binSize A K v i)) ≃ {f // f∈integerFiber A K hK v} :=
  (Equiv.piCongrRight (fun i => intervalEquiv K (freeRange A (index A i))
    (naturalBin A v (index A i)) hK (Nat.succ_pos _) (naturalBin_lt A v (index A i)))).trans
    ((Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
      {z : ℕ // z∈FairBits.fiber K (freeRange A t) (naturalBin A v t)}) (index A)).trans
      (integerFiberEquiv A K hK v).symm)

def binOffsetValue (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K)
    (x : (i : Fin (dimension A)) → Fin (binSize A K v i)) : FreeIndex A.small A.T A.b :=
  (binOffsetsEquiv A K hK v x).val

def exactBinLaw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) : RationalLaw (FreeIndex A.small A.T A.b) :=
  mapLaw (piLaw (fun i => FairBits.uniformIntLaw (binSize A K v i) (binSize_positive A K hK hW v i)))
    (binOffsetValue A K hK v)

def approximateBinLaw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) : RationalLaw (FreeIndex A.small A.T A.b) :=
  mapLaw (piLaw (fun i => FairBits.scaledLaw (binSize A K v i)
    (FairBits.offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)))
    (binOffsetValue A K hK v)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit finite mixing schedule of the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The source uses a linear reciprocal-error allowance inside the
mixing time, avoiding any unimplemented logarithm computation. -/
def oracleTime (A : Instance I J) (C : ℝ) (K Q : ℕ) (theta : ℝ) : ℕ :=
  ⌈mixingConstant A K*(height A C+(A.d:ℝ)*K+16*Q/theta+2)⌉₊

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational arithmetic for the companion evaluator's bin weights -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty
open ForestAffineCoefficients ForestRootPenalty GraphCompletionCounts GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalBinWidth (A : Instance I J) (C : ℕ) : ℕ := 16*C*A.d^2

def rationalHeight (A : Instance I J) (C : ℕ) : ℕ := 10*C*A.d^2*(A.W+1)

lemma rationalBinWidth_cast (A : Instance I J) (C : ℕ) :
    (rationalBinWidth A C:ℝ)=binWidth A C := by
  simp only [rationalBinWidth,binWidth,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma rationalHeight_cast (A : Instance I J) (C : ℕ) :
    (rationalHeight A C:ℝ)=height A C := by
  simp only [rationalHeight,height,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational transition and finite walk of the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def oracleProposalRat (d : ℕ) : ℚ := 1/(2:ℚ)^Nat.clog 2 (8*d)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer signed-coordinate proposals for the dense grid -/

namespace ContingencyTables.GridBoundary

open scoped Classical

variable {I : Type*} [DecidableEq I] {K : ℕ}

/-- A signed step is rejected at the boundary of the declared finite grid. -/
def axisStep (a : Grid (I := I) K) (i : I) (sign : Bool) : Option (Grid (I := I) K) :=
  if sign then
    if h : corner a i + 1 ≤ (K : ℤ) - 1 then
      some (Function.update a i ⟨corner a i + 1, by
        constructor
        · have ha : 0 ≤ corner a i := (a i).property.1; omega
        · exact h⟩)
    else none
  else
    if h : 0 ≤ corner a i - 1 then
      some (Function.update a i ⟨corner a i - 1, by
        constructor
        · exact h
        · have ha : corner a i ≤ (K : ℤ) - 1 := (a i).property.2; omega⟩)
    else none

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact proposal frequencies from a bounded fair-bit integer -/

namespace ContingencyTables.GridBoundary

open scoped Classical

def directionCodeEquiv (q : ℕ) : Fin q × Bool ≃ Fin (q * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finProdFinEquiv

def axisCodeStep {q K M : ℕ} (a : Grid (I := Fin q) K) (z : Fin M) :
    Option (Grid (I := Fin q) K) :=
  if hz : z.val < q * 2 then
    let dir := (directionCodeEquiv q).symm ⟨z.val, hz⟩
    axisStep a dir.1 dir.2
  else none

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral dense completion formulas

The sampler fills dependent cells by integer sums and differences. The
acceptance test is exactly nonnegativity of these integers; accepted
outputs have the prescribed natural margins.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def integerTable (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) :
    Option I → Option J → ℤ
  | some i, some j => z (i, j)
  | some i, none => R (some i) - ∑ j, (z (i, j) : ℤ)
  | none, some j => P (some j) - ∑ i, (z (i, j) : ℤ)
  | none, none => R none - ∑ j, (P (some j) : ℤ) + ∑ i, ∑ j, (z (i, j) : ℤ)

def naturalTable (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ) :
    Option I → Option J → ℕ := fun i j => (integerTable R P z i j).toNat

theorem integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ)
    (z : I × J → ℕ) (i : Option I) (j : Option J) :
    (integerTable R P z i j : ℝ) =
      table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (fun _ _ => 1) (fun p => (z p : ℝ)) i j := by
  cases i <;> cases j <;>
    simp only [integerTable, table, Int.cast_natCast, Int.cast_sub, Int.cast_add,
      Int.cast_sum, one_mul]

theorem naturalTable_cast (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (i : Option I) (j : Option J) :
    (naturalTable R P z i j : ℝ) = (integerTable R P z i j : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (hz i j)

theorem naturalTable_rows (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (i : Option I) :
    ∑ j, naturalTable R P z i j = R i := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  simp_rw [naturalTable_cast R P z hz, integerTable_cast]
  exact table_rows _ _ _ _ i

theorem naturalTable_columns (R : Option I → ℕ) (P : Option J → ℕ) (z : I × J → ℕ)
    (hz : ∀ i j, 0 ≤ integerTable R P z i j) (htotal : ∑ i, R i = ∑ j, P j) (j : Option J) :
    ∑ i, naturalTable R P z i j = P j := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  simp_rw [naturalTable_cast R P z hz, integerTable_cast]
  exact table_columns _ _ _ _ (by exact_mod_cast htotal) j

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleFiniteStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite Boolean experiment for each actual evaluator transition -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def oracleStepBits (A : Instance I J) (C : ℕ) : ℕ :=
  Nat.clog 2 (8*A.d)+rationalHeight A C

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reserving a common word length for adaptive bounded draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

def prefixWord {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) : Fin k → Bool :=
  fun i => bits (Fin.castLE hk i)

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalWalkApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive completion errors add once per actual transition -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

theorem variation_bind_two (p q : RationalLaw α) (K L : α → RationalLaw β) :
    variation (bindLaw p K) (bindLaw q L) ≤
      variation p q+∑ x,p.mass x*variation (K x) (L x) := by
  have hpoint (x : α) (y : β) :
      |p.mass x*(K x).mass y-q.mass x*(L x).mass y| ≤
        p.mass x*|(K x).mass y-(L x).mass y|+|p.mass x-q.mass x| *(L x).mass y := by
    calc
      _ = |p.mass x*((K x).mass y-(L x).mass y)+(p.mass x-q.mass x)*(L x).mass y| := by
        congr 1
        ring
      _ ≤ |p.mass x*((K x).mass y-(L x).mass y)|+|(p.mass x-q.mass x)*(L x).mass y| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul,abs_mul,abs_of_nonneg (p.nonnegative x),abs_of_nonneg ((L x).nonnegative y)]
  have hsum :
      (∑ y,|∑ x,(p.mass x*(K x).mass y-q.mass x*(L x).mass y)|) ≤
      (∑ x,|p.mass x-q.mass x|)+∑ x,p.mass x*(∑ y,|(K x).mass y-(L x).mass y|) := by
    calc
      _ ≤ ∑ y,∑ x,|p.mass x*(K x).mass y-q.mass x*(L x).mass y| :=
        Finset.sum_le_sum (fun y _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ y,∑ x,(p.mass x*|(K x).mass y-(L x).mass y|+
          |p.mass x-q.mass x| *(L x).mass y) :=
        Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun x _ => hpoint x y))
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,(L _).total,mul_one]
        ring
  unfold variation
  change (∑ y,|(∑ x,p.mass x*(K x).mass y)-(∑ x,q.mass x*(L x).mass y)|)/2 ≤ _
  simp_rw [← Finset.sum_sub_distrib]
  have hh := div_le_div_of_nonneg_right hsum (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [add_div,Finset.sum_div,mul_div_assoc]

theorem variation_bind_uniform (p q : RationalLaw α) (K L : α → RationalLaw β)
    (η : ℚ) (hη : ∀ x,variation (K x) (L x) ≤ η) :
    variation (bindLaw p K) (bindLaw q L) ≤ variation p q+η := by
  calc
    _ ≤ variation p q+∑ x,p.mass x*variation (K x) (L x) := variation_bind_two p q K L
    _ ≤ variation p q+∑ x,p.mass x*η := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (p.nonnegative x))
    _ = _ := by rw [← Finset.sum_mul,p.total,one_mul]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded Boolean draws for the companion correction experiment -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binSize_le_range (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (i : Fin (dimension A)) :
    binSize A K v i ≤ freeRange A (index A i) := by
  have hN : 0 < freeRange A (index A i) := Nat.succ_pos _
  have he := FairBits.fiber_card hK hN (naturalBin_lt A v (index A i))
  have hc : (FairBits.fiber K (freeRange A (index A i)) (naturalBin A v (index A i))).card ≤
      freeRange A (index A i) := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  rw [he] at hc
  exact hc

abbrev BinWords (A : Instance I J) (h : ℕ) :=
  (i : Fin (dimension A)) → Fin (offsetBitLength (freeRange A (index A i)) h A.d) → Bool

def binWordBits (A : Instance I J) (h : ℕ) : ℕ :=
  ∑ i : Fin (dimension A),offsetBitLength (freeRange A (index A i)) h A.d

def binWordEquiv (A : Instance I J) (h : ℕ) :
    (Fin (binWordBits A h) → Bool) ≃ BinWords A h :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.piCurry (fun _ _ => Bool))

lemma binBits_le (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (i : Fin (dimension A)) :
    offsetBitLength (binSize A K v i) h A.d ≤
      offsetBitLength (freeRange A (index A i)) h A.d := by
  unfold offsetBitLength
  exact Nat.add_le_add_right (Nat.clog_mono_right 2
    (Nat.add_le_add_right (binSize_le_range A K hK v i) 1)) _

def binWordDraw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (bits : BinWords A h) :
    FreeIndex A.small A.T A.b :=
  binOffsetValue A K hK v (fun i => scaledBitInteger (binSize A K v i)
    (offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)
    (prefixWord (binBits_le A K hK v h i) (bits i)))

def flatBinDraw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) (bits : Fin (binWordBits A h) → Bool) :
    FreeIndex A.small A.T A.b := binWordDraw A K hK hW v h (binWordEquiv A h bits)

def oracleWalkWordEquiv (n k : ℕ) : (Fin (n*k) → Bool) ≃ (Fin n → Fin k → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def oracleIntegerBits (A : Instance I J) (C n h : ℕ) : ℕ :=
  n*oracleStepBits A C+binWordBits A h

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalRootBisection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth rational bisection for the correction power of two -/

namespace ContingencyTables.RationalRootBisection

noncomputable section

/-- Every branch compares exact rational powers. The loop count is the
explicit depth, independent of the comparison outcomes. -/
def interval (c : ℚ) (s : ℕ) : ℕ → ℚ × ℚ
  | 0 => (0,8)
  | n+1 =>
    let ab := interval c s n
    let m := (ab.1+ab.2)/2
    if m^s ≤ c then (m,ab.2) else (ab.1,m)

def midpoint (c : ℚ) (s n : ℕ) : ℚ :=
  ((interval c s n).1+(interval c s n).2)/2

end

end ContingencyTables.RationalRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PowerOfTwoApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded rational approximation to the evaluator's power of two -/

namespace ContingencyTables.PowerOfTwoApproximation

open RationalRootBisection

noncomputable section

def numerator (beta : ℚ) (s : ℕ) : ℤ := ⌊(s:ℚ)*beta⌋

def approximation (beta : ℚ) (s n : ℕ) : ℚ := midpoint ((2:ℚ)^numerator beta s) s n

def rootDegree (sigma : ℚ) : ℕ := ⌈128/sigma⌉₊

def depth (sigma : ℚ) : ℕ := Nat.clog 2 (rootDegree sigma)

def approximate (beta sigma : ℚ) : ℚ := approximation beta (rootDegree sigma) (depth sigma)

end

end ContingencyTables.PowerOfTwoApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCorrectionArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalIntegerPoint (A : Instance I J) (C : ℕ) (f : FreeIndex A.small A.T A.b) :
    Fin (dimension A) → ℚ := fun i =>
  (rationalBinWidth A C:ℚ)*(f (index A i)).val/freeRange A (index A i)

def rationalPopulation (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) : ℚ :=
  (K:ℚ)^dimension A*(integerFiber A K hK (integerBin A K hK f)).card/assignmentCount A

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRatioSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev RatioWords (A : Instance I J) (C n : ℕ) := Fin n → Fin (oracleStepBits A C) → Bool

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def offsetAccuracy (A : Instance I J) (delta : ℚ) : ℕ := ⌈4096*(A.d:ℚ)/delta⌉₊

def correctionTheta (delta : ℚ) : ℝ := (delta:ℝ)/256

def roundingTolerance (delta : ℚ) : ℚ := delta/4

def sampleCount (j : ℕ) (delta failure : ℚ) : ℕ := ⌈65536*(j+1)/(failure*delta^2)⌉₊

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalAverage {X : Type*} (g : X → ℚ) (N : ℕ) (draws : Fin N → X) : ℚ :=
  (∑ i,g (draws i))/N

abbrev RatioBlock (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) → RatioWords A C (oracleTime A C K 1 delta)

abbrev CorrectionBlock (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) →
    (Fin (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) → Bool)

abbrev EstimatorInput (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  (Fin j → RatioBlock A C K j delta failure) × CorrectionBlock A C K j delta failure

def innerTolerance (epsilon : ℚ) (j : ℕ) : ℚ := epsilon/(200*(j+1))

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The complete input length, with one independent walk for each ratio
sample and one walk plus integer-bin draw for each correction sample. -/
def estimatorWordBits (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) : ℕ :=
  j*(sampleCount j delta failure *
    (oracleTime A C K 1 delta * oracleStepBits A C)) +
  sampleCount j delta failure *
    oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)

def ratioBlockWordEquiv (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :
    (Fin (sampleCount j delta failure *
      (oracleTime A C K 1 delta * oracleStepBits A C)) → Bool) ≃
    RatioBlock A C K j delta failure :=
  (oracleWalkWordEquiv (sampleCount j delta failure)
      (oracleTime A C K 1 delta * oracleStepBits A C)).trans
    (Equiv.piCongrRight (fun _ =>
      oracleWalkWordEquiv (oracleTime A C K 1 delta) (oracleStepBits A C)))

/-- This equivalence partitions, rather than reuses, the random bits of
all the individual experiments in the estimator. -/
def estimatorWordEquiv (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :
    (Fin (estimatorWordBits A C K j delta failure) → Bool) ≃
      EstimatorInput A C K j delta failure :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr
    ((oracleWalkWordEquiv j (sampleCount j delta failure *
      (oracleTime A C K 1 delta * oracleStepBits A C))).trans
        (Equiv.piCongrRight (fun _ => ratioBlockWordEquiv A C K j delta failure)))
    (oracleWalkWordEquiv (sampleCount j delta failure)
      (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))))

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWeightOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def profile (A : Instance I J) (S : Set (Labels A×Bool)) : View A → ℕ :=
  groupCount (group (labelCell A)) S

def factorialNumerator (A : Instance I J) (S : Set (Labels A×Bool)) : ℕ :=
  ∏ u : View A, (profile A S u).factorial

def factorialDenominator (A : Instance I J) : ℕ :=
  ∏ s : SmallCell A, (A.b s.val.1 s.val.2).factorial

def factorialRatio (A : Instance I J) (S : Set (Labels A×Bool)) : ℚ :=
  (factorialNumerator A S:ℚ)/factorialDenominator A

end

end ContingencyTables.CompanionWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev Pair (A : Instance I J) := (Labels A×Bool)×(Labels A×Bool)

def initial (A : Instance I J) (p q : Pair A) : ℚ :=
  if (p.1.1).1=(q.1.1).1 then 6
  else 6*((A.b (p.1.1).1.val.1 (p.1.1).1.val.2:ℚ)+1)/
    ((A.b (q.1.1).1.val.1 (q.1.1).1.val.2:ℚ)+2)

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit fresh words and rational arithmetic for one outer phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open GridBoundary FirstSuccess FairBits TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

structure Stored (A : Instance I J) where
  multiplier : Pair A → Pair A → ℚ
  estimate : ℚ

end

end ContingencyTables.CompanionPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded dyadic comparison with a rational acceptance probability -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical

noncomputable section

def rationalThreshold (k : ℕ) (q : ℚ) : ℕ := ⌊(2:ℚ)^k*q⌋₊

abbrev rationalThresholdAccept (k : ℕ) (q : ℚ) (bits : Fin k → Bool) : Prop :=
  (binaryWordEquiv k bits).val < rationalThreshold k q

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_SignedMarginTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal reference-row/reference-column completion translation -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def star (R : Option I → ℤ) (P : Option J → ℤ) : Option I → Option J → ℤ
  | some _,some _ => 0
  | some i,none => R (some i)
  | none,some j => P (some j)
  | none,none => R none-∑ j,P (some j)

omit [Fintype I] in
lemma star_rows (R : Option I → ℤ) (P : Option J → ℤ) (i : Option I) :
    (∑ j,star R P i j)=R i := by
  cases i <;> simp only [Fintype.sum_option,star,Finset.sum_const_zero] <;> ring

lemma star_columns (R : Option I → ℤ) (P : Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j) (j : Option J) : (∑ i,star R P i j)=P j := by
  cases j with
  | none =>
    simp only [Fintype.sum_option] at htotal
    simp only [Fintype.sum_option,star]
    omega
  | some j => simp only [Fintype.sum_option,star,Finset.sum_const_zero,add_zero]

omit [Fintype I] in
lemma star_neg (R : Option I → ℤ) (P : Option J → ℤ) :
    star (fun i => -R i) (fun j => -P j)=fun i j => -star R P i j := by
  funext i j
  cases i <;> cases j <;> simp only [star,Finset.sum_neg_distrib] <;> ring

def between (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) : Option I → Option J → ℤ :=
  star (fun i => (R₁ i:ℤ)-R₀ i) (fun j => (P₁ j:ℤ)-P₀ j)

omit [Fintype I] in
lemma between_rows (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) (i : Option I) :
    (∑ j,between R₀ R₁ P₀ P₁ i j)=(R₁ i:ℤ)-R₀ i := star_rows _ _ i

lemma between_columns (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (h₀ : (∑ i,R₀ i)=∑ j,P₀ j) (h₁ : (∑ i,R₁ i)=∑ j,P₁ j) (j : Option J) :
    (∑ i,between R₀ R₁ P₀ P₁ i j)=(P₁ j:ℤ)-P₀ j := by
  apply star_columns
  simp only [Finset.sum_sub_distrib,← Nat.cast_sum,h₀,h₁]

omit [Fintype I] in
lemma between_reverse (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) :
    between R₁ R₀ P₁ P₀=fun i j => -between R₀ R₁ P₀ P₁ i j := by
  have hR : (fun i => (R₀ i:ℤ)-R₁ i)=fun i => -((R₁ i:ℤ)-R₀ i) := by funext i; ring
  have hP : (fun j => (P₀ j:ℤ)-P₁ j)=fun j => -((P₁ j:ℤ)-P₀ j) := by funext j; ring
  unfold between
  rw [hR,hP,star_neg]

omit [Fintype I] in
lemma star_abs_le (R : Option I → ℤ) (P : Option J → ℤ) (M : ℤ)
    (hM : 0 ≤ M) (hR : ∀ i,|R i| ≤ M) (hP : ∀ j,|P j| ≤ M)
    (i : Option I) (j : Option J) :
    |star R P i j| ≤ M*((Fintype.card J:ℤ)+1) := by
  have hsum : |∑ j : J,P (some j)| ≤ (Fintype.card J:ℤ)*M := by
    calc
      _ ≤ ∑ j : J,|P (some j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J,M := Finset.sum_le_sum (fun j _ => hP (some j))
      _ = _ := by simp
  have hsingle : M ≤ M*((Fintype.card J:ℤ)+1) := by
    nlinarith [mul_nonneg hM (Int.natCast_nonneg (Fintype.card J))]
  cases i with
  | some i =>
    cases j with
    | some j => simpa only [star,abs_zero] using (mul_nonneg hM (by positivity : 0 ≤ (Fintype.card J:ℤ)+1))
    | none => exact (hR (some i)).trans hsingle
  | none =>
    cases j with
    | some j => exact (hP (some j)).trans hsingle
    | none =>
      calc
        _ ≤ |R none|+|∑ j : J,P (some j)| := abs_sub _ _
        _ ≤ M+(Fintype.card J:ℤ)*M := add_le_add (hR none) hsum
        _ = _ := by ring

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslatedCompletions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accepted completion translations are exact finite bijections -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def Accepted (R : I → ℕ) (P : J → ℕ) (D : I → J → ℤ) :=
  {X : Table R P // ∀ i j,0 ≤ (X.val i j:ℤ)+D i j}

noncomputable instance acceptedFintype (R : I → ℕ) (P : J → ℕ) (D : I → J → ℤ) :
    Fintype (Accepted R P D) := by
  unfold Accepted
  classical
  infer_instance

def translate (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) : Table R₁ P₁ := by
  refine ⟨fun i j => ((X.val.val i j:ℤ)+D i j).toNat,?_,?_⟩
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [Int.toNat_of_nonneg (X.property _ _)]
    rw [Finset.sum_add_distrib,← Nat.cast_sum,X.val.property.1,hR]
    ring
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [Int.toNat_of_nonneg (X.property _ _)]
    rw [Finset.sum_add_distrib,← Nat.cast_sum,X.val.property.2,hP]
    ring

lemma translate_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) (i : I) (j : J) :
    ((translate R₀ R₁ P₀ P₁ D hR hP X).val i j:ℤ)=(X.val.val i j:ℤ)+D i j :=
  Int.toNat_of_nonneg (X.property i j)

omit [Fintype I] in
lemma reverse_rows (R₀ R₁ : I → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i) (i : I) :
    (∑ j,-D i j)=(R₀ i:ℤ)-R₁ i := by
  rw [Finset.sum_neg_distrib,hR]
  ring

omit [Fintype J] in
lemma reverse_columns (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (j : J) :
    (∑ i,-D i j)=(P₀ j:ℤ)-P₁ j := by
  rw [Finset.sum_neg_distrib,hP]
  ring

def forward (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) :
    Accepted R₁ P₁ (fun i j => -D i j) := by
  refine ⟨translate R₀ R₁ P₀ P₁ D hR hP X,?_⟩
  intro i j
  rw [translate_cast]
  dsimp only
  omega

lemma forward_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₀ P₀ D) (i : I) (j : J) :
    ((forward R₀ R₁ P₀ P₁ D hR hP X).val.val i j:ℤ)=(X.val.val i j:ℤ)+D i j :=
  translate_cast R₀ R₁ P₀ P₁ D hR hP X i j

def backward (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₁ P₁ (fun i j => -D i j)) :
    Accepted R₀ P₀ D := by
  refine ⟨translate R₁ R₀ P₁ P₀ (fun i j => -D i j)
    (reverse_rows R₀ R₁ D hR) (reverse_columns P₀ P₁ D hP) X,?_⟩
  intro i j
  rw [translate_cast]
  omega

lemma backward_cast (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) (X : Accepted R₁ P₁ (fun i j => -D i j))
    (i : I) (j : J) :
    ((backward R₀ R₁ P₀ P₁ D hR hP X).val.val i j:ℤ)=(X.val.val i j:ℤ)-D i j := by
  change ((translate R₁ R₀ P₁ P₀ (fun i j => -D i j)
    (reverse_rows R₀ R₁ D hR) (reverse_columns P₀ P₁ D hP) X).val i j:ℤ)=_
  rw [translate_cast]
  rfl

def acceptedEquiv (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) :
    Accepted R₀ P₀ D ≃ Accepted R₁ P₁ (fun i j => -D i j) where
  toFun := forward R₀ R₁ P₀ P₁ D hR hP
  invFun := backward R₀ R₁ P₀ P₁ D hR hP
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Int.natCast_inj.mp
    change ((backward R₀ R₁ P₀ P₁ D hR hP (forward R₀ R₁ P₀ P₁ D hR hP X)).val.val i j:ℤ)=_
    rw [backward_cast,forward_cast]
    ring
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Int.natCast_inj.mp
    change ((forward R₀ R₁ P₀ P₁ D hR hP (backward R₀ R₁ P₀ P₁ D hR hP X)).val.val i j:ℤ)=_
    rw [forward_cast,backward_cast]
    ring

theorem accepted_card_symmetric (R₀ R₁ : I → ℕ) (P₀ P₁ : J → ℕ) (D : I → J → ℤ)
    (hR : ∀ i,(∑ j,D i j)=(R₁ i:ℤ)-R₀ i)
    (hP : ∀ j,(∑ i,D i j)=(P₁ j:ℤ)-P₀ j) :
    Fintype.card (Accepted R₀ P₀ D)=Fintype.card (Accepted R₁ P₁ (fun i j => -D i j)) :=
  Fintype.card_congr (acceptedEquiv R₀ R₁ P₀ P₁ D hR hP)

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslatedCompletionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetric accepted counts for the literal completion adjustment -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {X I J : Type*} [Fintype I] [Fintype J]

noncomputable def blockCount (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x : X) : ℕ :=
  Fintype.card (Table (R x) (P x))

noncomputable def acceptedCount (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) : ℕ :=
  Fintype.card (Accepted (R x) (P x) (between (R x) (R y) (P x) (P y)))

lemma blockCount_pos (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j) (x : X) : 0 < blockCount R P x :=
  Fintype.card_pos_iff.mpr (table_nonempty (R x) (P x) (htotal x))

lemma acceptedCount_le (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) :
    acceptedCount R P x y ≤ blockCount R P x :=
  Fintype.card_subtype_le _

/-- Reversibility uses the cardinality of actual accepted translations,
not a Metropolis weight-ratio oracle. -/
theorem acceptedCount_symmetric (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j) (x y : X) :
    acceptedCount R P x y=acceptedCount R P y x := by
  have he := accepted_card_symmetric (R x) (R y) (P x) (P y)
    (between (R x) (R y) (P x) (P y))
    (between_rows (R x) (R y) (P x) (P y))
    (between_columns (R x) (R y) (P x) (P y) (htotal x) (htotal y))
  unfold acceptedCount
  rw [between_reverse (R x) (R y) (P x) (P y)]
  exact he

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionStepApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completion replacement in the actual proposal-and-translation step -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]

/-- A proposal is either a hold or a target state. The sampled completion
is discarded after its literal translated-nonnegativity test. -/
def completionDecision (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x : X) (proposal : Option X) (a : Table (R x) (P x)) : X :=
  match proposal with
  | none => x
  | some y => if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j then y else x

def completionStepLaw (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (proposal : X → RationalLaw (Option X))
    (draw : (x : X) → RationalLaw (Table (R x) (P x))) (x : X) : RationalLaw X :=
  bindLaw (proposal x) (fun y => mapLaw (draw x) (completionDecision R P x y))

/-- From a common state only the completion draw changes. Mapping to the
accept/reject decision and averaging over the same proposal cannot enlarge TV. -/
theorem completionStep_variation (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (proposal : X → RationalLaw (Option X))
    (μ ν : (x : X) → RationalLaw (Table (R x) (P x))) (η : ℚ)
    (h : ∀ x,variation (μ x) (ν x) ≤ η) (x : X) :
    variation (completionStepLaw R P proposal μ x) (completionStepLaw R P proposal ν x) ≤ η := by
  have hv := variation_bind_uniform (proposal x) (proposal x)
    (fun y => mapLaw (μ x) (completionDecision R P x y))
    (fun y => mapLaw (ν x) (completionDecision R P x y)) η
    (fun y => (variation_map _ _ _).trans (h x))
  simpa only [completionStepLaw,variation,sub_self,abs_zero,Finset.sum_const_zero,zero_div,zero_add] using hv

end
end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionProposalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal proposal, completion draw and acceptance test -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]

/-- Each feasible neighbor is assigned its prescribed dyadic mass; the
remaining proposal words hold at the present state. -/
def proposalLaw (w : X → ℚ) (hw : ∀ y,0 ≤ w y) (htotal : ∑ y,w y ≤ 1) :
    RationalLaw (Option X) where
  mass := fun y => match y with
    | none => 1-∑ z,w z
    | some z => w z
  nonnegative := fun y => by cases y with
    | none => exact sub_nonneg.mpr htotal
    | some y => exact hw y
  total := by rw [Fintype.sum_option]; dsimp only; ring

omit [Fintype X] in
/-- Only a proposal of y can reach y from a distinct current state x. -/
lemma completionDecision_eq (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x y : X) (hne : x≠y) (q : Option X) (a : Table (R x) (P x)) :
    completionDecision R P x q a=y ↔
      q=some y ∧ ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j := by
  cases q with
  | none => simp [completionDecision,hne]
  | some z =>
    by_cases hz : z=y
    · subst z
      simp only [completionDecision,true_and]
      split_ifs <;> simp_all
    · simp only [completionDecision,Option.some.injEq,hz,false_and]
      split_ifs <;> simp_all

lemma completionStepLaw_mass_ne (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (w : X → ℚ) (hw : ∀ y,0 ≤ w y) (htotal : ∑ y,w y ≤ 1)
    (μ : (x : X) → RationalLaw (Table (R x) (P x))) (x y : X) (hne : x≠y) :
    (completionStepLaw R P (fun _ => proposalLaw w hw htotal) μ x).mass y=
      w y*∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (μ x).mass a else 0 := by
  change (∑ q : Option X,(proposalLaw w hw htotal).mass q *
    ∑ a : Table (R x) (P x),if completionDecision R P x q a=y then (μ x).mass a else 0)=_
  simp_rw [completionDecision_eq R P x y hne]
  rw [Fintype.sum_option]
  simp only [reduceCtorEq,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_add,Option.some.injEq]
  have hh (z : X) : (∑ a : Table (R x) (P x),
      if z=y ∧ ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
      then (μ x).mass a else 0)=
      if z=y then ∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (μ x).mass a else 0 else 0 := by
    by_cases hz : z=y <;> simp [hz]
  simp_rw [hh]
  simp [proposalLaw,mul_ite]

omit [Fintype X] [DecidableEq X] in
/-- The normalized completion indicator is exactly the acceptance count
used in the reversible small kernel. -/
lemma uniformAcceptedMass (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x y : X) [Nonempty (Table (R x) (P x))] :
    (∑ a : Table (R x) (P x),
      if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
      then (uniformLaw (α := Table (R x) (P x))).mass a else 0)=
      (acceptedCount R P x y:ℚ)/(blockCount R P x:ℚ) := by
  simp only [uniformLaw,uniformMass]
  calc
    _ = (∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (1:ℚ) else 0)/(Fintype.card (Table (R x) (P x)):ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_boole,←Fintype.card_subtype]
      rfl

end
end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionKernelIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying a complete transition law from its off-diagonal probabilities -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Normalization determines the remaining holding probability. -/
theorem law_ext_except (p q : RationalLaw X) (x : X)
    (h : ∀ y,y≠x → p.mass y=q.mass y) : p=q := by
  apply RationalLaw.ext
  funext y
  by_cases hy : y=x
  · subst y
    have hs : (∑ y,(p.mass y-q.mass y))=p.mass x-q.mass x := by
      apply Finset.sum_eq_single x
      · intro y _ hy
        rw [h y hy,sub_self]
      · simp
    rw [Finset.sum_sub_distrib,p.total,q.total,sub_self] at hs
    linarith
  · exact h y hy

end ContingencyTables.FirstSuccess

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]
variable (R : X → Option I → ℕ) (P : X → Option J → ℕ)
variable [∀ x,Nonempty (Table (R x) (P x))]

omit [∀ x,Nonempty (Table (R x) (P x))] in
/-- Only the proposal distribution at the current state is observed. -/
lemma completionStepLaw_proposal_at (p q : X → RationalLaw (Option X))
    (draw : (z : X) → RationalLaw (Table (R z) (P z))) (x : X) (h : p x=q x) :
    completionStepLaw R P p draw x=completionStepLaw R P q draw x := by
  unfold completionStepLaw
  rw [h]

/-- This identifies the actual draw-and-test transition, including holds;
no independent reversibility or stationarity assertion is imposed on it. -/
theorem uniformCompletionStep_eq (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x : X) (K : RationalLaw X)
    (hK : ∀ y,y≠x → K.mass y=w y*(acceptedCount R P x y:ℚ)/(blockCount R P x:ℚ)) :
    completionStepLaw R P (fun _ => proposalLaw w hw htotal)
      (fun z => uniformLaw (α := Table (R z) (P z))) x=K := by
  apply law_ext_except _ _ x
  intro y hy
  rw [completionStepLaw_mass_ne R P w hw htotal _ x y hy.symm,uniformAcceptedMass,hK y hy]
  ring

end
end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePartialDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One Boolean word per listed proposal, with unused words giving a hold -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {X : Type*} [Fintype X]

/-- A code with no preimage is an explicit hold. -/
def injectionDraw {k : ℕ} (e : X ↪ Fin (2^k)) (b : Fin (2^k)) : Option X :=
  if h : ∃ x,e x=b then some (Classical.choose h) else none

def proposalEmbedding (k : ℕ) (h : Fintype.card X ≤ 2^k) : X ↪ Fin (2^k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

def partialBitDraw (k : ℕ) (h : Fintype.card X ≤ 2^k) (bits : Fin k → Bool) : Option X :=
  injectionDraw (proposalEmbedding k h) (binaryWordEquiv k bits)

variable {S : Type*} [Fintype S] [DecidableEq X]

def subsetBitDraw (p : X → Prop) (k : ℕ) (h : Fintype.card {x // p x} ≤ 2^k)
    (bits : Fin k → Bool) : Option X :=
  (partialBitDraw (X := {x // p x}) k h bits).map Subtype.val

end
end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBooleanPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion phase walk driven by disjoint bounded Boolean words -/

namespace ContingencyTables.CompanionBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def proposalBits (A : Instance I J) : ℕ := Nat.clog 2 (Fintype.card (Labels A)^2)

lemma dyadic_size_le_twice (n : ℕ) (hn : 0 < n) : 2^Nat.clog 2 n ≤ 2*n := by
  by_cases h1 : n=1
  · subst n
    norm_num
  have hgt : 1 < n := by omega
  have hm : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hgt
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hgt
  have he : Nat.clog 2 n=(Nat.clog 2 n).pred+1 := (Nat.succ_pred_eq_of_pos hm).symm
  calc
    _ = 2*2^(Nat.clog 2 n).pred := by
      conv_lhs => rw [he,pow_succ]
      ring
    _ ≤ 2*n := Nat.mul_le_mul_left 2 hp.le

def slowdown (A : Instance I J) : ℝ :=
  (Fintype.card (Labels A):ℝ)^2/(2:ℝ)^proposalBits A

/-- The unused proposal codes slow the source chain by at most two;
they do not change its stationary law. -/
theorem slowdown_bounds (A : Instance I J) (hp : 0 < Fintype.card (Labels A)) :
    (1/2:ℝ) ≤ slowdown A ∧ slowdown A ≤ 1 := by
  have hn : 0 < Fintype.card (Labels A)^2 := pow_pos hp _
  have hl := dyadic_size_le_twice (Fintype.card (Labels A)^2) hn
  have hu := Nat.le_pow_clog (by decide : 1<2) (Fintype.card (Labels A)^2)
  have hlR : (2:ℝ)^proposalBits A ≤ 2*(Fintype.card (Labels A):ℝ)^2 := by exact_mod_cast hl
  have huR : (Fintype.card (Labels A):ℝ)^2 ≤ (2:ℝ)^proposalBits A := by exact_mod_cast hu
  unfold slowdown
  constructor
  · rw [le_div_iff₀ (by positivity : (0:ℝ)<2^proposalBits A)]
    linarith
  · exact (div_le_one (by positivity)).mpr huR

end

end ContingencyTables.CompanionBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_Certify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ComputableReach

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (G : SimpleGraph α) [DecidableRel G.Adj]

def grow (s : Finset α) : Finset α := s ∪ univ.filter (fun b => ∃ a ∈ s, G.Adj a b)

def reached (s : Finset α) (n : ℕ) : Finset α := (grow G)^[n] s

def closure (a : α) : Finset α := reached G {a} (Fintype.card α)

lemma mem_grow (s : Finset α) (b : α) :
    b ∈ grow G s ↔ b ∈ s ∨ ∃ a ∈ s, G.Adj a b := by simp [grow]

lemma subset_grow (s : Finset α) : s ⊆ grow G s := subset_union_left

lemma reached_step (s : Finset α) (n : ℕ) : reached G s (n+1) = grow G (reached G s n) :=
  Function.iterate_succ_apply' _ _ _

lemma reached_step' (s : Finset α) (n : ℕ) : reached G s (n+1) = reached G (grow G s) n :=
  Function.iterate_succ_apply _ _ _

lemma reached_succ (s : Finset α) (n : ℕ) : reached G s n ⊆ reached G s (n+1) := by
  rw [reached_step]
  exact subset_grow G _

lemma reached_mono_time (s : Finset α) : Monotone (reached G s) :=
  monotone_nat_of_le_succ (reached_succ G s)

lemma reached_reachable (a b : α) (n : ℕ) (h : b ∈ reached G {a} n) : G.Reachable a b := by
  induction n generalizing b with
  | zero =>
    have hb : b=a := by simpa [reached] using h
    subst b
    exact SimpleGraph.Reachable.refl a
  | succ n ih =>
    rw [reached_step,mem_grow] at h
    rcases h with h | ⟨c,hc,hcb⟩
    · exact ih b h
    · exact (ih c hc).trans hcb.reachable

lemma walk_reached {s : Finset α} {a b : α} (p : G.Walk a b) (ha : a ∈ s) :
    b ∈ reached G s p.length := by
  induction p generalizing s with
  | nil => exact ha
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.length_cons,reached_step']
    exact ih ((mem_grow G s b).mpr (Or.inr ⟨a,ha,hab⟩))

@[simp] theorem mem_closure (a b : α) : b ∈ closure G a ↔ G.Reachable a b := by
  constructor
  · exact reached_reachable G a b _
  · rintro ⟨p⟩
    exact reached_mono_time G {a} p.toPath.isPath.length_lt.le
      (walk_reached G p.toPath.val (mem_singleton_self a))

end MatchingFPRAS.ComputableReach

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {B : Type}

def countDown (f : ℕ×B → B) : ℕ → B → B
  | 0,b => b
  | n+1,b => countDown f n (f (n+1,b))

namespace Repeat

inductive Point where | loop | check | rebuild | body | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.loop,.check,.rebuild,.body,.halt},by intro p; cases p <;> simp⟩
def next (f : ℕ×B → B) (nb : ℕ×B) : ℕ×B := (nb.1-1,f nb)
end Repeat

def rangeStep (x : ℕ×List ℕ) : List ℕ := (x.1-1)::x.2
lemma countDown_range (n : ℕ) (as : List ℕ) : countDown rangeStep n as=List.range n++as := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => simp [countDown,rangeStep,ih,List.range_succ,List.append_assoc]
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeNaturalComb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def factStep (x : ℕ×ℕ) : ℕ := x.1*x.2
lemma fact_countDown (n a : ℕ) : countDown factStep n a=n.factorial*a := by
  induction n generalizing a with
  | zero => simp [countDown]
  | succ n ih =>
    rw [countDown,ih]
    simp only [factStep,Nat.factorial_succ]
    ring

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {A B X : Type}

def dropStep (x : ℕ×List A) : List A := x.2.tail

def mapStep (g : X×A → B) (z : A×(X×List B)) : X×List B :=
  (z.2.1,g (z.2.1,z.1)::z.2.2)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def sortedPair (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then (x.2,x.1) else x

lemma sortedPair_order (x : ℕ×ℕ) : (sortedPair x).2≤(sortedPair x).1 := by
  unfold sortedPair; split_ifs <;> (try dsimp only) <;> omega
lemma sortedPair_gcd (x : ℕ×ℕ) : (sortedPair x).1.gcd (sortedPair x).2=x.1.gcd x.2 := by
  unfold sortedPair; split_ifs <;> simp [Nat.gcd_comm]
lemma sortedPair_size (x : ℕ×ℕ) : (sortedPair x).1.size+(sortedPair x).2.size=x.1.size+x.2.size := by
  unfold sortedPair
  split_ifs
  · exact Nat.add_comm _ _
  · rfl

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)

lemma mod_size_lt {a b : ℕ} (hb : 0<b) (hab : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := hb.trans_le hab
  have hr := Nat.mod_lt a hb
  have hq : 1≤a/b := Nat.div_pos hab hb
  have hd := Nat.mod_add_div a b
  have hm : 2*(a%b)<a := by nlinarith [Nat.mul_le_mul_left b hq]
  have hs := Nat.size_pos.mpr ha
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a.size≠0)
  have hpow:=Nat.lt_size_self a
  rw [hk,pow_succ] at hpow
  have hh : a%b<2^k := by omega
  have hsz := Nat.size_le.mpr hh
  omega

lemma gcdStep_order {x : ℕ×ℕ} (h : x.2≤x.1) : (gcdStep x).2≤(gcdStep x).1 := by
  unfold gcdStep; split_ifs with hz
  · exact h
  · exact (Nat.mod_lt _ (by omega)).le
lemma gcdStep_gcd (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep; split_ifs
  · rfl
  · simpa [Nat.gcd_comm] using (Nat.gcd_rec x.2 x.1).symm
lemma gcdStep_decrease {x : ℕ×ℕ} (h : x.2≤x.1) (hz : x.2≠0) :
    (gcdStep x).1.size+(gcdStep x).2.size<x.1.size+x.2.size := by
  simp only [gcdStep,hz,↓reduceIte]
  have hh:=mod_size_lt (by omega : 0<x.2) h
  omega

def gcdIterStep (x : ℕ×(ℕ×ℕ)) : ℕ×ℕ := gcdStep x.2
lemma gcdIter_zero (k a : ℕ) : countDown gcdIterStep k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [countDown,gcdIterStep,gcdStep,↓reduceIte] using ih

lemma gcdIter_result (k : ℕ) (x : ℕ×ℕ) (h : x.2≤x.1) (hs : x.1.size+x.2.size≤k) :
    countDown gcdIterStep k x=(x.1.gcd x.2,0) := by
  induction k generalizing x with
  | zero =>
    have hsz : x.1.size=0 := by omega
    have ha:=Nat.size_eq_zero.mp hsz
    have hb : x.2=0 := by omega
    simp [countDown,ha,hb]
    exact Prod.ext ha hb
  | succ k ih =>
    by_cases hz : x.2=0
    · obtain ⟨a,b⟩:=x; dsimp only at hz; subst b
      simp only [gcdIter_zero,Nat.gcd_zero_right]
    · rw [countDown]
      change countDown gcdIterStep k (gcdStep x)=_
      rw [ih _ (gcdStep_order h) (by have hd:=gcdStep_decrease h hz; omega),gcdStep_gcd]

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

abbrev Fraction := ℕ×ℕ
def val (x : Fraction) : ℚ := (x.1:ℚ)/x.2

def normalize (x : Fraction) : Fraction :=
  if x.2=0 then (0,1) else (x.1/(x.1.gcd x.2),x.2/(x.1.gcd x.2))

def mul (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.1,x.1.2*x.2.2)

def add (x : Fraction×Fraction) : Fraction :=
  normalize (x.1.1*x.2.2+x.2.1*x.1.2,x.1.2*x.2.2)

def div (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.2,x.1.2*x.2.1)

def less (x : Fraction×Fraction) : Bool := decide (x.1.1*x.2.2<x.2.1*x.1.2)

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for a small-profile unit exchange -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev ExchangeInput := List ℕ×(ℕ×ℕ)

def exchangeEntry (z : ExchangeInput×ℕ) : ℕ :=
  z.1.1.getD z.2 0+(if z.2=z.1.2.1 then 1 else 0)-(if z.2=z.1.2.2 then 1 else 0)

def listExchange (z : ExchangeInput) : List ℕ :=
  (List.range z.1.length).map (fun a => exchangeEntry (z,a))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedCompletions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero penalties are exactly padded residual completions

Retain the small x,y views and fill every large cell with the balanced
pair (A,B-A). For an assignment supported on large cells, the full margin
equations are precisely the padded residual margin equations. The small
positive-part penalties enforce the original nonnegative residual tests.
-/

namespace ContingencyTables.PaddedCompletions

open scoped BigOperators Classical
open RowColumnPenalties NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) : ℕ :=
  ∑ j, if small i j then X i j else 0

noncomputable def smallColumn (small : I → J → Bool) (B Y : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then B i j-Y i j else 0

noncomputable def rowLargeCount (small : I → J → Bool) (i : I) : ℕ :=
  ∑ j, if small i j then 0 else 1

noncomputable def columnLargeCount (small : I → J → Bool) (j : J) : ℕ :=
  ∑ i, if small i j then 0 else 1

def profile (small : I → J → Bool) (B X Y A : I → J → ℕ) : ((I × J) × Bool) → ℕ :=
  fun u => if u.2 then (if small u.1.1 u.1.2 then Y u.1.1 u.1.2 else B u.1.1 u.1.2-A u.1.1 u.1.2)
    else (if small u.1.1 u.1.2 then X u.1.1 u.1.2 else A u.1.1 u.1.2)

def Supported (small : I → J → Bool) (A : I → J → ℕ) : Prop :=
  ∀ i j, small i j=true → A i j=0

def OriginalResidualsNonnegative (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, smallRow small X i ≤ r i) ∧ (∀ j, smallColumn small B Y j ≤ c j)

omit [Fintype I] in
lemma profile_row (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hA : Supported small A) (i : I) :
    (∑ j, rowView (profile small B X Y A) i j)=smallRow small X i+∑ j, A i j := by
  unfold smallRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j
  · simp [rowView,profile,hs]
  · simp [rowView,profile,hs,hA i j hs]

omit [Fintype J] in
lemma profile_column (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hA : Supported small A) (hcap : ∀ i j, small i j=false → A i j ≤ B i j) (j : J) :
    (∑ i, columnView B (profile small B X Y A) i j)=smallColumn small B Y j+∑ i, A i j := by
  unfold smallColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simpa [columnView,profile,hs] using Nat.sub_sub_self (hcap i j hs)
  · simp [columnView,profile,hs,hA i j hs]

omit [Fintype I] in
lemma profile_small_row (small : I → J → Bool) (B X Y A : I → J → ℕ) (i : I) :
    (∑ j, if small i j then rowView (profile small B X Y A) i j else 0)=smallRow small X i := by
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [rowView,profile,hs]

omit [Fintype J] in
lemma profile_small_column (small : I → J → Bool) (B X Y A : I → J → ℕ) (j : J) :
    (∑ i, if small i j then columnView B (profile small B X Y A) i j else 0)=smallColumn small B Y j := by
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [columnView,profile,hs]

end ContingencyTables.PaddedCompletions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The literal zero-penalty sum counts residual completions

Finite balanced large-cell assignments are represented by bounded natural
matrices supported on the large cells. The zero-penalty predicate is
equivalent to the actual padded residual table equations. An explicit
entry bound proves when the formal capacities exclude no completion.
-/

namespace ContingencyTables.CompletionCounts

open scoped BigOperators Classical
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

def LargeCompletion (small : I → J → Bool) (R : I → ℕ) (C : J → ℕ) :=
  {A : Table R C // Supported small A.val}

noncomputable instance largeCompletionFintype (small : I → J → Bool) (R : I → ℕ) (C : J → ℕ) :
    Fintype (LargeCompletion small R C) := by
  unfold LargeCompletion
  infer_instance

def Assignment (small : I → J → Bool) (B : I → J → ℕ) :=
  {a : (i : I) → (j : J) → Fin (B i j+1) // ∀ i j, small i j=true → (a i j).val=0}

noncomputable instance assignmentFintype (small : I → J → Bool) (B : I → J → ℕ) :
    Fintype (Assignment small B) := by
  unfold Assignment
  infer_instance

def assignmentMatrix {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) : I → J → ℕ :=
  fun i j => (a.val i j).val

omit [Fintype I] [Fintype J] in
lemma assignment_supported {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) :
    Supported small (assignmentMatrix a) := a.property

omit [Fintype I] [Fintype J] in
lemma assignment_bounded {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) (i : I) (j : J) :
    assignmentMatrix a i j ≤ B i j := Nat.le_of_lt_succ (a.val i j).isLt

noncomputable def fullPenalty (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : ℝ :=
  penalty cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
    viewSlope (smallOffset small B r c) viewSlope (profile small B X Y A)

def ZeroAssignments (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {a : Assignment small B // fullPenalty small B X Y (assignmentMatrix a) r c L=0}

noncomputable instance zeroAssignmentsFintype (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (ZeroAssignments small B X Y r c L) := by
  unfold ZeroAssignments
  infer_instance

/-- The total padded residual mass is at most the original mass plus
one padding unit L for each large cell. -/
theorem padded_total_le (small : I → J → Bool) (X : I → J → ℕ) (r : I → ℕ) (L : ℕ) :
    (∑ i, (r i-smallRow small X i+rowLargeCount small i*L)) ≤
      (∑ i, r i)+(∑ i, rowLargeCount small i)*L := by
  rw [Finset.sum_add_distrib,Finset.sum_mul]
  exact Nat.add_le_add_right (Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)) _

/-- This is the exact reason the paper's formal large capacity excludes
no padded completion. No large-range enumeration is used. -/
theorem capacity_excludes_none (small : I → J → Bool) (B X : I → J → ℕ)
    (r : I → ℕ) (L d C : ℕ) (hcount : (∑ i, rowLargeCount small i) ≤ d)
    (hC : (∑ i, r i)+d*L ≤ C) (hB : ∀ i j, small i j=false → B i j=C) :
    ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j := by
  intro i j hij
  rw [hB i j hij]
  exact (padded_total_le small X r L).trans
    ((Nat.add_le_add_left (Nat.mul_le_mul_right L hcount) _).trans hC)

theorem large_count_le_dimension (small : I → J → Bool) :
    (∑ i, rowLargeCount small i) ≤ Fintype.card I*Fintype.card J := by
  calc
    _ ≤ ∑ _ : I, Fintype.card J := by
      apply Finset.sum_le_sum
      intro i _
      unfold rowLargeCount
      calc
        _ ≤ ∑ _ : J, (1:ℕ) := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs <;> omega
        _ = Fintype.card J := by simp
    _ = _ := by simp

noncomputable def paperCapacity (small : I → J → Bool) (r : I → ℕ) (d L U : ℕ) : I → J → ℕ :=
  fun i j => if small i j then U else (∑ k, r k)+d*L+U+2

/-- For the manuscript's exact C=N+dL+U+2, the capacity hypothesis of
the count equivalence follows just from the dimension allowance. -/
theorem paper_capacity_excludes_none (small : I → J → Bool) (X : I → J → ℕ)
    (r : I → ℕ) (d L U : ℕ) (hd : Fintype.card I*Fintype.card J ≤ d) :
    ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ paperCapacity small r d L U i j := by
  apply capacity_excludes_none small (paperCapacity small r d L U) X r L d
    ((∑ k, r k)+d*L+U+2) ((large_count_le_dimension small).trans hd)
  · omega
  · intro i j hij
    simp [paperCapacity,hij]

def firstPaperSmall (r : I → ℕ) (c : J → ℕ) (U : ℕ) (i : I) (j : J) : Bool :=
  decide (r i<U ∨ c j<U)

omit [Fintype I] [Fintype J] in
/-- Thus the large set is exactly the complete large-margin rectangle. -/
lemma firstPaperSmall_false_iff (r : I → ℕ) (c : J → ℕ) (U : ℕ) (i : I) (j : J) :
    firstPaperSmall r c U i j=false ↔ U ≤ r i ∧ U ≤ c j := by
  simp [firstPaperSmall]

noncomputable def dimensionAllowance : ℕ :=
  10+(Fintype.card I+1)*(Fintype.card J+1)

lemma dimension_le_allowance : Fintype.card I*Fintype.card J ≤ dimensionAllowance (I := I) (J := J) := by
  unfold dimensionAllowance
  nlinarith

end ContingencyTables.CompletionCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's physical hard marginal and its proved raw signature

This bridges the finite balanced-pair elimination theorem to the actual
supported padded-completion count, in the original row/column coordinates.
-/

namespace ContingencyTables.FirstPaperPhysicalMarginal

open scoped BigOperators Classical
open CompletionCounts
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fullHardFamily (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : (((I×J)×Bool) → ℕ) → ℝ :=
  hardWeight cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope

@[reducible] noncomputable def paperSmall (r : I → ℕ) (c : J → ℕ) : I → J → Bool :=
  firstPaperSmall r c (dimensionAllowance (I := I) (J := J)^20)

end ContingencyTables.FirstPaperPhysicalMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Repair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Repair of a defect with its large completion

The two full matrices give the row and column views, agreeing at all
large cells. Moving one unit from the positive cell to the crossing cell
and resetting the column view preserves the enlarged margins. This is the
joint-object injection underlying the repair in paper 200-01.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A single unit transfer, allowing source and receiver to coincide. -/
def transferInt (X : I → J → ℕ) (source receiver : I × J) (i : I) (j : J) : ℤ :=
  X i j - (if i = source.1 ∧ j = source.2 then 1 else 0) +
    (if i = receiver.1 ∧ j = receiver.2 then 1 else 0)

/-- The defect equation `q=x-e_t+e_s` identifies the sign convention. -/
def IsDefect (x q : I → J → ℕ) (negative positive : I × J) : Prop :=
  negative ≠ positive ∧
    ∀ i j, (q i j : ℤ) = transferInt x positive negative i j

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original residual bounds are preserved by the literal repair

Only a small source entry is lowered. Every large entry is unchanged or
increased. Since full row and column-view totals are preserved, the
small row/column sums cannot increase.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def smallColumnView (small : I → J → Bool) (Q : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then Q i j else 0

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint state-completion repair injections, including fixed contexts

Full row and column views retain the large completion explicitly. Their
finite fibre cardinalities therefore count states with the correct
completion multiplicity. The target repair is a balanced full table.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def RowColumnPair (r : I → ℕ) (c : J → ℕ) :=
  {Z : (I → J → ℕ) × (I → J → ℕ) //
    (∀ i, ∑ j, Z.1 i j=r i) ∧ (∀ j, ∑ i, Z.2 i j=c j)}

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual row-major small-prefix coordinate splitting

The retained prefix is precisely the earlier small cells. The remaining
ordinary cells all follow the next exposed cell, which is the condition
needed for the completion-retaining conditional repair injection.
-/

namespace ContingencyTables.SmallContextCoordinates

open scoped Classical

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

abbrev Cells (small : I → J → Bool) := {a : I×J // small a.1 a.2=true}

end ContingencyTables.SmallContextCoordinates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def differenceEntry (z : (List ℕ×List ℕ)×ℕ) : ℕ :=
  z.1.1.getD z.2 0-z.1.2.getD z.2 0

/-- Preserve the second list's length, including malformed inputs. -/
def listDifference (z : List ℕ×List ℕ) : List ℕ :=
  (List.range z.2.length).map (fun i => differenceEntry (z,i))

abbrev RepairInput := List ℕ×(List ℕ×(ℕ×ℕ))

/-- The final pair stores the source and receiver respectively. -/
def repairedViews (z : RepairInput) : List ℕ×List ℕ :=
  let w := listExchange (z.1,(z.2.2.2,z.2.2.1))
  (w,listDifference (z.2.1,w))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type}

def optionRep [Inhabited A] : Option A→Bool×A
  | none => (false,default)
  | some a => (true,a)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type}
  [DecidableEq A]
  [BEq A]
  [LawfulBEq A]

def indexStep (x : A×(A×ℕ)) : A×ℕ := (x.2.1,if x.2.1=x.1 then 0 else x.2.2+1)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable indices for small cells and their crossing cells -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def cellCatalog : List (ℕ×ℕ) :=
  List.ofFn (fun i => ((e i).val.1.val,(e i).val.2.val))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def pairAt (z : ℕ×ℕ) : ℕ×ℕ := (z.2/z.1,z.2%z.1)

def cellPairs (z : List ℕ×List ℕ) : List (ℕ×ℕ) :=
  (List.range (z.1.length*z.2.length)).map (fun a => pairAt (z.2.length,a))

lemma mem_cellPairs (r c : List ℕ) (i j : ℕ) :
    (i,j)∈cellPairs (r,c) ↔ i < r.length ∧ j < c.length := by
  simp only [cellPairs,List.mem_map,List.mem_range,pairAt,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,hi,hj⟩
    have hc : 0 < c.length := by nlinarith
    exact ⟨hi ▸ ((Nat.div_lt_iff_lt_mul hc).mpr ha),hj ▸ Nat.mod_lt a hc⟩
  · rintro ⟨hi,hj⟩
    have hc : 0 < c.length := Nat.zero_lt_of_lt hj
    refine ⟨i*c.length+j,by nlinarith,?_,?_⟩
    · rw [Nat.mul_comm i c.length,Nat.mul_add_div hc,Nat.div_eq_of_lt hj,add_zero]
    · simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hj]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryExchangeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

def binaryExchangeTest (z : List ℕ×(ℕ×ℕ)) : Bool :=
  decide (z.1.getD z.2.1 0=0 ∧ z.1.getD z.2.2 0=1)

def binaryExchangeIndices (xs : List ℕ) : List (ℕ×ℕ) :=
  (cellPairs (xs,xs)).filter (fun ij => binaryExchangeTest (xs,ij))

lemma cellPairs_nodup (xs ys : List ℕ) : (cellPairs (xs,ys)).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a _ b _ he
  have hq := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  dsimp only [pairAt] at hq hr
  calc
    a = a%ys.length+ys.length*(a/ys.length) := (Nat.mod_add_div a ys.length).symm
    _ = b%ys.length+ys.length*(b/ys.length) := by rw [hq,hr]
    _ = b := Nat.mod_add_div b ys.length

def binaryExchanges (xs : List ℕ) : List (List ℕ) :=
  (binaryExchangeIndices xs).map (fun ij => listExchange (xs,ij))

noncomputable def setProfile {n : ℕ} (S : Set (Fin n)) : Fin n → ℕ :=
  fun i => if i∈S then 1 else 0

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDependentLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact joint laws with a finite state-dependent completion space -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

def dependentJointLaw (p : RationalLaw X) (q : (x : X) → RationalLaw (Y x)) :
    RationalLaw ((x : X) × Y x) where
  mass := fun a => p.mass a.1*(q a.1).mass a.2
  nonnegative := fun a => mul_nonneg (p.nonnegative a.1) ((q a.1).nonnegative a.2)
  total := by
    rw [Fintype.sum_sigma]
    simp only [←Finset.mul_sum,(q _).total,mul_one,p.total]

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordDependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent words with a state-dependent second output -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B X Z : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Z]


/-- First drawing a state and then applying a fresh common word to that
state gives the corresponding composition of output laws. -/
theorem mapLaw_product_finish [DecidableEq X] [DecidableEq Z]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → X) (finish : X → B → Z) :
    mapLaw (productLaw p q) (fun ab => finish (f ab.1) ab.2)=
      bindLaw (mapLaw p f) (fun x => mapLaw q (finish x)) := by
  apply RationalLaw.ext
  funext z
  simp only [mapLaw,productLaw,bindLaw,Fintype.sum_prod_type]
  symm
  calc
    _ = ∑ a,p.mass a*(∑ b,if finish (f a) b=z then q.mass b else 0) := by
      simp_rw [Finset.sum_mul,ite_mul,zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def sum (xs : List Fraction) : Fraction := xs.foldl (fun a b=>add (b,a)) (0,1)

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped

def bitDenominator (bs : List Bool) : ℕ := bs.foldl (fun a _=>2*a) 1
lemma bitDenominator_eq (bs : List Bool) : bitDenominator bs=2^bs.length := by
  have h : ∀ a,bs.foldl (fun a _=>2*a) a=a*2^bs.length := by
    induction bs with
    | nil => intro a; simp
    | cons _ _ ih => intro a; simp only [List.foldl_cons,ih,List.length_cons,pow_succ]; ring
  simpa [bitDenominator] using h 1

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeFractionCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def height (x : Fraction) : ℕ := max x.1.size x.2.size
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionArithmeticProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit coordinate-list proposal for the companion chain

Only ordered coordinates are enumerated. The arithmetic binary-profile
program generates the possible exchanges, after which the actual chain
state predicate removes disallowed states. A dyadic list index has exactly
the same proposal law as the abstract injection.
-/

namespace ContingencyTables.CompanionArithmeticProposal
open ProfilePrograms FirstSuccess ResidualMixture FairBits
open CompanionFactorialApplication CompanionBooleanPhase TwoLiftStates
open scoped BigOperators Classical

noncomputable section

section Coordinates
variable {Γ : Type*} [Fintype Γ] {n : ℕ} (e : Γ ≃ Fin n)

def coordinateSet (S : Set Γ) : Set (Fin n) := e.symm ⁻¹' S

def physicalSet (S : Set (Fin n)) : Set Γ := e ⁻¹' S

omit [Fintype Γ] in
@[simp] lemma physical_coordinate (S : Set Γ) : physicalSet e (coordinateSet e S)=S := by
  ext a
  simp [physicalSet,coordinateSet]

omit [Fintype Γ] in
@[simp] lemma coordinate_physical (S : Set (Fin n)) : coordinateSet e (physicalSet e S)=S := by
  ext a
  simp [physicalSet,coordinateSet]

def encodeSet (S : Set Γ) : List ℕ := List.ofFn (setProfile (coordinateSet e S))

def decodeSet (xs : List ℕ) : Set Γ := {a | xs.getD (e a).val 0=1}

def neighborSets (S : Set Γ) : List (Set Γ) :=
  (binaryExchanges (encodeSet e S)).map (decodeSet e)

end Coordinates

variable {I J : Type} [Fintype I] [Fintype J]

def coordinateEquiv (A : Instance I J) : (Labels A×Bool) ≃ Fin (Fintype.card (Labels A×Bool)) :=
  Fintype.equivFin _

end
end ContingencyTables.CompanionArithmeticProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequential uniform sampling of a subset of prescribed size

The head is included with probability k/n; conditional on that choice,
the same rule is applied to the remaining coordinates. The exact mass
is k!(n-k)!/n!, matching the factorial factor in the companion lift.
-/

namespace ContingencyTables.FixedCardinalityLaw

open ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

def consEquiv (n : ℕ) : ((_b : Bool) × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun x := Fin.cons x.1 x.2
  invFun v := ⟨v 0,Fin.tail v⟩
  left_inv x := by cases x; simp
  right_inv v := Fin.cons_self_tail v

def consLaw {n : ℕ} (p : RationalLaw Bool) (Q : Bool → RationalLaw (Fin n → Bool)) :
    RationalLaw (Fin (n+1) → Bool) :=
  equivLaw (consEquiv n) (dependentJointLaw p Q)

def bernoulli (q : ℚ) (hq0 : 0≤q) (hq1 : q≤1) : RationalLaw Bool where
  mass b := if b then q else 1-q
  nonnegative b := by cases b <;> simp [hq0,sub_nonneg.mpr hq1]
  total := by simp

def headProbability (n k : ℕ) : ℚ := ((min k (n+1):ℕ):ℚ)/(n+1)

lemma headProbability_bounds (n k : ℕ) : 0≤headProbability n k ∧ headProbability n k≤1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply (div_le_one (by positivity : (0:ℚ)<n+1)).mpr
    exact_mod_cast min_le_right k (n+1)

def headLaw (n k : ℕ) : RationalLaw Bool :=
  bernoulli (headProbability n k) (headProbability_bounds n k).1 (headProbability_bounds n k).2

def remaining (n k : ℕ) (b : Bool) : ℕ := if b then k-1 else min k n

def fixedLaw : (n k : ℕ) → RationalLaw (Fin n → Bool)
  | 0, _ => pointLaw (fun i => Fin.elim0 i)
  | n+1, k => consLaw (headLaw n k) (fun b => fixedLaw n (remaining n k b))

end
end ContingencyTables.FixedCardinalityLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Boolean implementation of fixed-cardinality subset draws -/

namespace ContingencyTables.FixedCardinalityBits

open ResidualMixture FirstSuccess FairBits FixedCardinalityLaw
open scoped BigOperators Classical
noncomputable section

def headDraw (B n k : ℕ) (bits : Fin B → Bool) : Bool :=
  decide (rationalThresholdAccept B (headProbability n k) bits)

def draw (B : ℕ) : (n k : ℕ) → (Fin n → Fin B → Bool) → (Fin n → Bool)
  | 0, _, _ => fun i => Fin.elim0 i
  | n+1, k, words =>
      let b := headDraw B n k (words 0)
      Fin.cons b (draw B n (remaining n k b) (Fin.tail words))

def blockWords (n B : ℕ) : (Fin (n*B) → Bool) ≃ (Fin n → Fin B → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def bitDraw (B n k : ℕ) (bits : Fin (n*B) → Bool) : Fin n → Bool :=
  draw B n k (blockWords n B bits)

end
end ContingencyTables.FixedCardinalityBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform-size mixture realizes the initial factorial weights

A size is drawn uniformly from 0,...,n, followed by the sequential
fixed-cardinality draw. Its subset mass is the literal local factorial
weight divided by n+1. The bounded Boolean implementation uses a fresh
word for the size and for each inclusion decision.
-/

namespace ContingencyTables.FixedCardinalityMixture

open ResidualMixture FirstSuccess FairBits FixedCardinalityLaw FixedCardinalityBits
open scoped BigOperators Classical
noncomputable section

def sizeMixture (n : ℕ) : RationalLaw (Fin n → Bool) :=
  bindLaw (uniformLaw (α := Fin (n+1))) (fun k => fixedLaw n k.val)

def subsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun v := Finset.univ.filter (fun i => v i=true)
  invFun S i := decide (i∈S)
  left_inv v := by
    funext i
    cases h : v i <;> simp [h]
  right_inv S := by ext i; simp

def localLaw (n : ℕ) : RationalLaw (Finset (Fin n)) :=
  equivLaw (subsetEquiv n) (sizeMixture n)

def drawBits (B n : ℕ) := B+n*B

def vectorDraw (B n : ℕ) (bits : Fin (drawBits B n) → Bool) : Fin n → Bool :=
  let words := splitWordEquiv B (n*B) bits
  bitDraw B n (scaledBitInteger (n+1) B (Nat.succ_pos n) words.1).val words.2

def subsetDraw (B n : ℕ) (bits : Fin (drawBits B n) → Bool) : Finset (Fin n) :=
  subsetEquiv n (vectorDraw B n bits)

end
end ContingencyTables.FixedCardinalityMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialFactorialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent initial cell choices give the literal companion law

The finite rational law is the product of the uniform-size subset laws.
Encoding a choice as its paired transversal yields exactly the initial
law of the companion's factorial lift, with its actual free-completion
normalizer cancelled.
-/

namespace ContingencyTables.InitialFactorialLaw

open ResidualMixture FirstSuccess TwoLiftStates LabelledFactorial
open InitialTransversals FixedCardinalityMixture CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {C : Type*} [Fintype C] (b : C → ℕ)

def choiceLaw : RationalLaw ((c : C) → Finset (Fin (b c))) where
  mass S := ∏ c,(localLaw (b c)).mass (S c)
  nonnegative S := Finset.prod_nonneg (fun c _ => (localLaw (b c)).nonnegative (S c))
  total := by
    rw [←Fintype.prod_sum]
    simp only [(localLaw _).total,Finset.prod_const_one]

end
end ContingencyTables.InitialFactorialLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialFactorialBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite Boolean word for the actual initial transversal

The word is split into disjoint cell blocks; each block chooses a size
and then a subset of that size. The total variation errors add before
the exact paired-transversal encoding is applied.
-/

namespace ContingencyTables.InitialFactorialBits

open ResidualMixture FirstSuccess FairBits TwoLiftStates
open FixedCardinalityMixture InitialFactorialLaw InitialTransversals
open CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {q : ℕ}

def bitCount (b : Fin q → ℕ) (B : ℕ) : ℕ := ∑ i,drawBits B (b i)

def wordEquiv (b : Fin q → ℕ) (B : ℕ) :
    (Fin (bitCount b B) → Bool) ≃ (∀ i,Fin (drawBits B (b i)) → Bool) :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

def drawChoices (b : Fin q → ℕ) (B : ℕ) (bits : Fin (bitCount b B) → Bool) :
    ∀ i,Finset (Fin (b i)) :=
  fun i => subsetDraw B (b i) (wordEquiv b B bits i)

variable {C : Type*} [Fintype C]

def choiceEquiv (b : C → ℕ) (e : C ≃ Fin q) :
    (∀ i : Fin q,Finset (Fin (b (e.symm i)))) ≃ (∀ c,Finset (Fin (b c))) :=
  (Equiv.piCongrLeft' (fun c => Finset (Fin (b c))) e).symm

end
end ContingencyTables.InitialFactorialBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded-word initialization of the companion trace

The output is in the literal `PlainIndex` used by the trace chain. Its
ideal rational law is exactly the source's phase-zero law; the bounded
word implementation is within 2^(-h), with an explicit word length.
-/

namespace ContingencyTables.CompanionInitialDraw

open ResidualMixture FirstSuccess TwoLiftStates
open CompanionFactorialApplication InitialFactorialLaw InitialFactorialBits
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def cellEnum (A : Instance I J) : SmallCell A ≃ Fin (Fintype.card (SmallCell A)) :=
  Fintype.equivFin (SmallCell A)

def cellCapacity (A : Instance I J) (i : Fin (Fintype.card (SmallCell A))) : ℕ :=
  A.b ((cellEnum A).symm i).val.1 ((cellEnum A).symm i).val.2

def initialBits (A : Instance I J) (B : ℕ) : ℕ := bitCount (cellCapacity A) B

def precision (A : Instance I J) (h : ℕ) : ℕ :=
  Nat.clog 2 (A.d*(3*A.W+1)+1)+h

end
end ContingencyTables.CompanionInitialDraw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev PatternData := (List ℕ×List ℕ)×ℕ
abbrev LabelledPattern := PatternData×(ℕ×ℕ)

def pairSum (z : PatternData×ℕ) : ℕ := z.1.1.1.getD z.2 0+z.1.1.2.getD z.2 0

def balancedAt (z : PatternData×ℕ) : Bool := decide (pairSum z=z.1.2)

def balancedTest (z : PatternData) : Bool :=
  (List.range z.1.1.length).all (fun i => balancedAt (z,i))

def defectAt (z : LabelledPattern×ℕ) : Bool :=
  decide (pairSum (z.1.1,z.2)+(if z.2=z.1.2.1 then 1 else 0)=
    z.1.1.2+(if z.2=z.1.2.2 then 1 else 0))

def defectTest (z : LabelledPattern) : Bool :=
  decide (z.2.1≠z.2.2) && (List.range z.1.1.1.length).all (fun i => defectAt (z,i))

def patternTest (z : PatternData) : Bool :=
  balancedTest z || (cellPairs (z.1.1,z.1.1)).any (fun st => defectTest (z,st))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionChainValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

abbrev ValidatorInput := List (ℕ×ℕ)×List ℕ

def pairedStateTest (z : ValidatorInput) : Bool :=
  patternTest (((z.1.map (fun ij => z.2.getD ij.1 0)),
    (z.1.map (fun ij => z.2.getD ij.2 0))),1)

end ContingencyTables.CompanionChainValidator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionNeighborProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable valid-neighbor lists and their binary draw

This composes the actual integer-exchange program with the paired-state
validator and the bounded list-index program. The output code is exactly
the encoding of the semantic proposal, including its failure outcome.
-/

namespace ContingencyTables.CompanionNeighborProgram
open CompanionChainValidator CompanionArithmeticProposal CompanionFactorialApplication
open CompanionBooleanPhase ProfilePrograms MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def validExchanges (z : ValidatorInput) : List (List ℕ) :=
  (binaryExchanges z.2).filter (fun xs => pairedStateTest (z.1,xs))

end ContingencyTables.CompanionNeighborProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOrderedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with a specified coordinate order

The coordinate scan and its paired-state validator work with the same
explicit order used by the initializer. Its dyadic proposal law is
independent of this order, including unused proposal words.
-/

namespace ContingencyTables.CompanionOrderedProposal

open TwoLiftStates CompanionFactorialApplication
open CompanionArithmeticProposal CompanionChainValidator CompanionNeighborProgram
open CompanionBooleanPhase FirstSuccess ResidualMixture ProfilePrograms
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {m p : ℕ}

def orderedCatalog (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m) : List (ℕ×ℕ) :=
  List.ofFn (fun i => ((e (g i,false)).val,(e (g i,true)).val))

end
end ContingencyTables.CompanionOrderedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed Boolean word realizes each exact dense transition -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseStepBits (d : ℕ) : ℕ := Nat.clog 2 (8 * d) + 8 * d ^ 5

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dense bin draw as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

def gridWordEquiv (n k : ℕ) : (Fin (n * k) → Bool) ≃ (Fin n → Fin k → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded binary coordinate moves in the dense grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev AxisData := ((ℕ×List ℕ)×ℕ)×Bool

def axisListStep (z : AxisData) : Option (List ℕ) :=
  let K := z.1.1.1
  let xs := z.1.1.2
  let i := z.1.2
  if i<xs.length then
    if z.2 then
      if xs.getD i 0+1<K then some (listExchange (xs,(i,xs.length))) else none
    else
      if 0<xs.getD i 0 then some (listExchange (xs,(xs.length,i))) else none
  else none

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural coordinate encodings of dense axis moves -/

namespace ContingencyTables.DensePrograms
open ProfilePrograms GridBoundary
open scoped Classical

def gridNatCode {q K : ℕ} (a : Grid (I := Fin q) K) : List ℕ :=
  List.ofFn (fun i => (corner a i).toNat)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

abbrev AxisWordData := (ℕ×List ℕ)×List Bool

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list arithmetic for integral dense completion -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev MatrixCode := List (List ℕ)

def columnRead (z : ℕ×List ℕ) : ℕ := z.2.getD z.1 0

def columnTotal (z : MatrixCode×ℕ) : ℕ := (z.1.map (fun row => row.getD z.2 0)).sum

def rowTotal (z : MatrixCode×ℕ) : ℕ := (z.1.getD z.2 []).sum

def matrixTotal (z : MatrixCode) : ℕ := (z.map List.sum).sum

def matrixEntry (z : MatrixCode×(ℕ×ℕ)) : ℕ := (z.1.getD z.2.1 []).getD z.2.2 0

def matrixCode {m n : ℕ} (z : Fin m → Fin n → ℕ) : MatrixCode :=
  List.ofFn (fun i => List.ofFn (z i))

lemma matrixEntry_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) :
    matrixEntry (matrixCode z,(i.val,j.val))=z i j := by
  simp only [matrixEntry,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev CompletionData := (List ℕ×List ℕ)×MatrixCode
abbrev CompletionCell := CompletionData×(ℕ×ℕ)

/-- Index zero denotes the distinguished dependent row or column. -/
def completionParts (z : CompletionCell) : ℕ×ℕ :=
  if z.2.1=0 then
    if z.2.2=0 then
      (z.1.1.1.headD 0+matrixTotal z.1.2,z.1.1.2.tail.sum)
    else (z.1.1.2.getD z.2.2 0,columnTotal (z.1.2,z.2.2-1))
  else if z.2.2=0 then
    (z.1.1.1.getD z.2.1 0,rowTotal (z.1.2,z.2.1-1))
  else (matrixEntry (z.1.2,(z.2.1-1,z.2.2-1)),0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslatedCompletionChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal chain draws an actual uniform completion then translates it -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

noncomputable def completionMove (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (Adj : X → X → Prop) (β : ℝ) (x y : X) : ℝ :=
  if Adj x y then β*(acceptedCount R P x y:ℝ)/(blockCount R P x:ℝ) else 0

omit [Fintype X] [Nonempty X] in
lemma completionMove_nonnegative (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    0 ≤ completionMove R P Adj β x y := by
  unfold completionMove
  split_ifs
  · exact div_nonneg (mul_nonneg hβ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact le_rfl

omit [Fintype X] [Nonempty X] in
lemma completionMove_le_proposal (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    completionMove R P Adj β x y ≤ if Adj x y then β else 0 := by
  unfold completionMove
  split_ifs
  · have hf : (0:ℝ) < blockCount R P x := by exact_mod_cast blockCount_pos R P htotal x
    have hc : (acceptedCount R P x y:ℝ) ≤ blockCount R P x := by exact_mod_cast acceptedCount_le R P x y
    apply (div_le_iff₀ hf).mpr
    exact mul_le_mul_of_nonneg_left hc hβ
  · exact le_rfl

omit [Nonempty X] in
lemma completionMove_row (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (x : X) : ∑ y,completionMove R P Adj β x y ≤ 1/2 := by
  calc
    _ ≤ ∑ y,if Adj x y then β else 0 :=
      Finset.sum_le_sum (fun y _ => completionMove_le_proposal R P htotal Adj β hβ x y)
    _ = ((Finset.univ.filter (Adj x)).card:ℝ)*β := by rw [← Finset.sum_filter]; simp
    _ ≤ (D:ℝ)*β := mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree x) hβ
    _ ≤ _ := hproposal

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionChainFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact edge flow of the completion-translation chain -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

omit [Nonempty X] in
lemma completionMove_flow (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (β : ℝ) (x y : X) :
    ((blockCount R P x:ℝ)/MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      completionMove R P Adj β x y =
      if Adj x y then β*(acceptedCount R P x y:ℝ)/
        MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)) else 0 := by
  have hx : (blockCount R P x:ℝ)≠0 := ne_of_gt (by exact_mod_cast blockCount_pos R P htotal x)
  unfold completionMove
  split_ifs
  · exact div_mul_div_cancel₀' hx _ _
  · exact mul_zero _

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslatedCompletionAcceptance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Acceptance probability of the literal reference-row translation -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def referencePosition : Option I ⊕ J → Option I × Option J :=
  Sum.elim (fun i => (i,none)) (fun j => (none,some j))

abbrev ReferenceGood (R : Option I → ℕ) (P : Option J → ℕ) (t : ℕ) :=
  {X : Table R P // ¬∃ k : Option I ⊕ J,
    X.val (referencePosition k).1 (referencePosition k).2 < t}

lemma reference_good_nonnegative
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (hzero : ∀ i j,D (some i) (some j)=0) (t : ℕ)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) (X : ReferenceGood R P t) :
    ∀ i j,0 ≤ (X.val.val i j:ℤ)+D i j := by
  have hcell (k : Option I ⊕ J) :
      0 ≤ (X.val.val (referencePosition k).1 (referencePosition k).2:ℤ)+
        D (referencePosition k).1 (referencePosition k).2 := by
    have hn : t ≤ X.val.val (referencePosition k).1 (referencePosition k).2 :=
      Nat.le_of_not_gt (fun h => X.property ⟨k,h⟩)
    have hn' : (t:ℤ) ≤ X.val.val (referencePosition k).1 (referencePosition k).2 := by exact_mod_cast hn
    have hl := (abs_le.mp (hbound (referencePosition k).1 (referencePosition k).2)).1
    omega
  intro i j
  cases j with
  | none => exact hcell (.inl i)
  | some j =>
    cases i with
    | none => exact hcell (.inr j)
    | some i => rw [hzero i j,add_zero]; positivity

lemma reference_good_card_le
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (hzero : ∀ i j,D (some i) (some j)=0) (t : ℕ)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) :
    Fintype.card (ReferenceGood R P t) ≤ Fintype.card (Accepted R P D) := by
  let embed : ReferenceGood R P t → Accepted R P D :=
    fun X => ⟨X.val,reference_good_nonnegative R P D hzero t hbound X⟩
  apply Fintype.card_le_of_injective embed
  intro X Y h
  apply Subtype.ext
  exact congrArg (fun Z : Accepted R P D => Z.val) h

lemma reference_cell_fraction
    (R : Option I → ℕ) (P : Option J → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀) (k : Option I ⊕ J) :
    (Fintype.card {X : Table R P // X.val (referencePosition k).1 (referencePosition k).2 < t}:ℝ)/
      Fintype.card (Table R P) ≤ 4*t*(d:ℝ)^3/a₀ := by
  simpa only [Fintype.card_eq_nat_card] using
    small_entry_probability htotal (referencePosition k).1 (referencePosition k).2
      a₀ d t hd hrows hcols (hrow _) (hcol _) ha₀ ht

lemma reference_good_fraction
    (R : Option I → ℕ) (P : Option J → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀) :
    1-(Fintype.card I+Fintype.card J+1:ℕ)*(4*t*(d:ℝ)^3/a₀) ≤
      (Fintype.card (ReferenceGood R P t):ℝ)/Fintype.card (Table R P) := by
  have hcard : (0:ℝ) < Fintype.card (Table R P) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R P htotal)
  have hfrac := fraction_not_exists
    (fun (k : Option I ⊕ J) (X : Table R P) =>
      X.val (referencePosition k).1 (referencePosition k).2 < t)
    (4*t*(d:ℝ)^3/a₀) hcard (fun k => by
      simpa only [Fintype.card_eq_nat_card] using reference_cell_fraction R P htotal a₀ d t hd hrows hcols hrow hcol ha₀ ht k)
  have hcK : Fintype.card (Option I ⊕ J)=Fintype.card I+Fintype.card J+1 := by
    rw [Fintype.card_sum,Fintype.card_option]
    omega
  rw [hcK] at hfrac
  simpa only [Fintype.card_eq_nat_card] using hfrac

/-- The reference row and reference column contain only |I|+|J|+1
possibly changed entries. No completion outside those entries can reject. -/
theorem reference_acceptance
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (hzero : ∀ i j,D (some i) (some j)=0)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) :
    1-(Fintype.card I+Fintype.card J+1:ℕ)*(4*t*(d:ℝ)^3/a₀) ≤
      (Fintype.card (Accepted R P D):ℝ)/Fintype.card (Table R P) := by
  have hcount : (Fintype.card (ReferenceGood R P t):ℝ) ≤ Fintype.card (Accepted R P D) := by
    exact_mod_cast reference_good_card_le R P D hzero t hbound
  exact (reference_good_fraction R P htotal a₀ d t hd hrows hcols hrow hcol ha₀ ht).trans
    (div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _))

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCompletionAcceptance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half acceptance at the paper's actual padding scale -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma padding_ge_twenty_dimension (d : ℕ) (hd : 14 ≤ d) : 20*d ≤ d^12 := by
  have hp : 20 ≤ d^11 :=
    (by norm_num : 20 ≤ 14^11).trans (Nat.pow_le_pow_left hd 11)
  calc
    _ ≤ d^11*d := Nat.mul_le_mul_right d hp
    _ = _ := by ring

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabeling a rectangular completion, preserving every table -/

namespace ContingencyTables

open scoped BigOperators

variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

def tableReindex (eI : I' ≃ I) (eJ : J' ≃ J) (r : I → ℕ) (c : J → ℕ) :
    Table r c ≃ Table (fun i => r (eI i)) (fun j => c (eJ j)) where
  toFun X := ⟨fun i j => X.val (eI i) (eJ j),
    fun i => (eJ.sum_comp (X.val (eI i))).trans (X.property.1 (eI i)),
    fun j => (eI.sum_comp (fun i => X.val i (eJ j))).trans (X.property.2 (eJ j))⟩
  invFun X := ⟨fun i j => X.val (eI.symm i) (eJ.symm j),by
    constructor
    · intro i
      rw [eJ.symm.sum_comp]
      simpa only [Equiv.apply_symm_apply] using X.property.1 (eI.symm i)
    · intro j
      exact (eI.symm.sum_comp (fun i => X.val i (eJ.symm j))).trans (by
        simpa only [Equiv.apply_symm_apply] using X.property.2 (eJ.symm j))⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    simp only [Equiv.apply_symm_apply]
  right_inv X := by
    apply Subtype.ext
    funext i j
    simp only [Equiv.symm_apply_apply]

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed reference row and column for the physical completion blocks -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev LargeRows (r : I → ℕ) (U : ℕ) := {i // U ≤ r i}
abbrev LargeColumns (c : J → ℕ) (U : ℕ) := {j // U ≤ c j}

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable abbrev stateCapacity (r : I → ℕ) (c : J → ℕ) : I → J → ℕ :=
  paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableMarginTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing equal margin descriptions without changing entries -/

namespace ContingencyTables
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Enumeration instances affect the proofs of the margins, never the entries. -/
def tableFintypeTransport (fi fi' : Fintype I) (fj fj' : Fintype J)
    (r : I → ℕ) (c : J → ℕ) : @Table I J fi fj r c ≃ @Table I J fi' fj' r c where
  toFun X := ⟨X.val,by
    cases Subsingleton.elim fi fi'
    cases Subsingleton.elim fj fj'
    exact X.property⟩
  invFun X := ⟨X.val,by
    cases Subsingleton.elim fi fi'
    cases Subsingleton.elim fj fj'
    exact X.property⟩
  left_inv X := rfl
  right_inv X := rfl

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBoundsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program checking every stored coordinate bound -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def boundedValues (z : ℕ×List ℕ) : Bool := z.2.all (fun a => decide (a≤z.1))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallViewLookupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lookup of the sparse small-cell view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ViewLookupInput := (List (ℕ×ℕ)×List ℕ)×(ℕ×ℕ)

def lookupView (z : ViewLookupInput) : ℕ :=
  z.1.2.getD (z.1.1.idxOf z.2) 0

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallLineSumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

abbrev LineData := ((List (ℕ×ℕ)×List ℕ)×List ℕ)×ℕ

def lineEntry (row : Bool) (z : LineData×ℕ) : ℕ :=
  lookupView (z.1.1.1,if row then (z.1.2,z.2) else (z.2,z.1.2))

def lineSum (row : Bool) (z : LineData) : ℕ :=
  ((List.range z.1.2.length).map (fun i => lineEntry row (z,i))).sum

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallComplementProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def complementValues (z : ℕ×List ℕ) : List ℕ := z.2.map (fun a => z.1-a)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginTestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev MarginCheckData := ((List (ℕ×ℕ)×List ℕ)×(List ℕ×List ℕ))×ℕ

def marginList (row : Bool) (z : MarginCheckData) : List ℕ :=
  if row then z.1.2.1 else z.1.2.2

def lineArgument (row : Bool) (z : MarginCheckData×ℕ) : LineData :=
  ((z.1.1.1,marginList (!row) z.1),z.2)

def validMarginAt (row : Bool) (z : MarginCheckData×ℕ) : Bool :=
  let a := (marginList row z.1).getD z.2 0
  let s := lineSum row (lineArgument row z)
  decide (s≤a ∧ (a<z.1.2 → s=a))

def validMargins (row : Bool) (z : MarginCheckData) : Bool :=
  (List.range (marginList row z).length).all (fun i => validMarginAt row (z,i))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileCheckData := ((List (ℕ×ℕ)×(List ℕ×List ℕ))×(List ℕ×List ℕ))×ℕ

def profileTest (z : ProfileCheckData) : Bool :=
  decide (z.1.1.2.1.length=z.1.1.1.length) &&
    (decide (z.1.1.2.2.length=z.1.1.1.length) &&
    (boundedValues (z.2,z.1.1.2.1) &&
    (boundedValues (z.2,z.1.1.2.2) &&
    (patternTest (z.1.1.2,z.2) &&
    (validMargins true (((z.1.1.1,z.1.1.2.1),z.1.2),z.2) &&
      validMargins false (((z.1.1.1,complementValues (z.2,z.1.1.2.2)),z.1.2),z.2))))))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal lists encode exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def codeCheckData (catalog : List (ℕ×ℕ)) (r c : List ℕ) (U : ℕ)
    (v : List ℕ×List ℕ) : ProfileCheckData := (((catalog,v),(r,c)),U)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileFlatCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the two stored views for coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def flattenViews (z : List ℕ×List ℕ) : List ℕ := z.1++z.2

def splitViews (z : ℕ×List ℕ) : List ℕ×List ℕ := (z.2.take z.1,z.2.drop z.1)

def codeExchange (z : (List ℕ×List ℕ)×(ℕ×ℕ)) : List ℕ×List ℕ :=
  splitViews (z.1.1.length,listExchange (flattenViews z.1,z.2))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallExchangeListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating all directed unit exchanges of a stored profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def positiveExchangeTest (z : List ℕ×(ℕ×ℕ)) : Bool :=
  decide (z.2.1≠z.2.2 ∧ 0<z.1.getD z.2.2 0)

def positiveExchangeIndices (xs : List ℕ) : List (ℕ×ℕ) :=
  (cellPairs (xs,xs)).filter (fun ij => positiveExchangeTest (xs,ij))

def codeExchangeList (v : List ℕ×List ℕ) : List (List ℕ×List ℕ) :=
  (positiveExchangeIndices (flattenViews v)).map (fun ij => codeExchange (v,ij))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileInverseRepairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for each labelled inverse repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

/-- The three indices are the negative cell, positive cell and crossing
cell. A crossing cell outside the small list has its length as index. -/
abbrev InverseRepairInput := List ℕ×(List ℕ×(ℕ×(ℕ×ℕ)))

def backwardRows (z : InverseRepairInput) : List ℕ :=
  listExchange (z.1,(z.2.2.2.1,z.2.2.2.2))

def backwardColumns (z : InverseRepairInput) : List ℕ :=
  listExchange (backwardRows z,(z.2.2.1,z.2.2.2.1))

def backwardViews (z : InverseRepairInput) : List ℕ×List ℕ :=
  (backwardRows z,listDifference (z.2.1,backwardColumns z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of repair crossing cells and capacities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev RepairGeometry := List (ℕ×ℕ)×(ℕ×ℕ)

def crossingIndex (z : RepairGeometry) : ℕ :=
  z.1.idxOf ((z.1.getD z.2.2 (0,0)).1,(z.1.getD z.2.1 (0,0)).2)

def capacityList (z : ℕ×List ℕ) : List ℕ := z.2.map (fun _ => z.1)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev RepairData := (List (ℕ×ℕ)×(List ℕ×List ℕ))×ℕ
abbrev LabelledRepairData := RepairData×(ℕ×ℕ)

def forwardRepairCode (z : LabelledRepairData) : List ℕ×List ℕ :=
  repairedViews (z.1.1.2.1,(capacityList (z.1.2,z.1.1.2.1),
    (z.2.2,crossingIndex (z.1.1.1,z.2))))

def inverseRepairCode (z : LabelledRepairData) : List ℕ×List ℕ :=
  backwardViews (z.1.1.2.1,(capacityList (z.1.2,z.1.1.2.1),
    (z.2.1,(z.2.2,crossingIndex (z.1.1.1,z.2)))))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectCodeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled defect predicate on two binary-coded views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairLabelTest (z : LabelledRepairData) : Bool :=
  defectTest ((z.1.1.2,z.1.2),z.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairPairs (z : RepairData) : List (ℕ×ℕ) := cellPairs (z.1.2.1,z.1.2.1)

def forwardRepairLabels (z : RepairData) : List (ℕ×ℕ) :=
  (repairPairs z).filter (fun st => repairLabelTest (z,st))

def forwardRepairList (z : RepairData) : List (List ℕ×List ℕ) :=
  (forwardRepairLabels z).map (fun st => forwardRepairCode (z,st))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallInverseRepairList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def inverseLabelInput (z : LabelledRepairData) : LabelledRepairData :=
  (((z.1.1.1,inverseRepairCode z),z.1.2),z.2)

def inverseLabelTest (z : LabelledRepairData) : Bool :=
  repairLabelTest (inverseLabelInput z) &&
    decide (forwardRepairCode (inverseLabelInput z)=z.1.1.2)

def inverseRepairLabels (z : RepairData) : List (ℕ×ℕ) :=
  (repairPairs z).filter (fun st => inverseLabelTest (z,st))

def checkedInverseRepairList (z : RepairData) : List (List ℕ×List ℕ) :=
  (inverseRepairLabels z).map (fun st => inverseRepairCode (z,st))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def rawCodeNeighbors (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  codeExchangeList z.1.1.2 ++
    (forwardRepairList (z.1.1,z.2) ++ checkedInverseRepairList (z.1.1,z.2))

def candidateData (z : ProfileCheckData×(List ℕ×List ℕ)) : ProfileCheckData :=
  (((z.1.1.1.1,z.2),z.1.1.2),z.1.2)

def codeNeighbors (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  ((rawCodeNeighbors z).filter (fun v => profileTest (candidateData (z,v)))).dedup

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of one dense exponent component -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms

abbrev ComponentData := (ℕ×ℕ)×(ℕ×ℕ)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing all dense exponent components and their maximum -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms Polynomial
open scoped BigOperators

def listMaximum (z : List ℕ×ℕ) : ℕ := z.1.foldl (fun a b => max b a) z.2

abbrev ExponentData := CompletionData×ℕ

def exponentCellData (z : ExponentData×(ℕ×ℕ)) : ComponentData :=
  ((z.1.2,min (z.1.1.1.1.getD z.2.1 0) (z.1.1.1.2.getD z.2.2 0)),
    completionParts (z.1.1,z.2))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

def shiftedCell (z : ExponentData×(ℕ×ℕ)) : ExponentData×(ℕ×ℕ) :=
  (z.1,(z.2.1+1,z.2.2+1))

def gridCellWidth (z : ExponentData×(ℕ×ℕ)) : ℕ :=
  (exponentCellData (shiftedCell z)).1.2/z.1.2^8

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev GridFlatData := (List ℕ×List ℕ)×List ℕ

def sliceRow (z : (ℕ×List ℕ)×ℕ) : List ℕ :=
  (z.1.2.drop (z.2*z.1.1)).take z.1.1

def layoutRows (z : GridFlatData) : List ℕ := List.range z.1.1.tail.length

def layoutRow (z : GridFlatData×ℕ) : List ℕ :=
  sliceRow ((z.1.1.2.tail.length,z.1.2),z.2)

def unflattenGrid (z : GridFlatData) : MatrixCode :=
  (layoutRows z).map (fun i => layoutRow (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFlatExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

abbrev FlatExponentData := GridFlatData×ℕ

def flatToGridData (z : FlatExponentData) : ExponentData :=
  ((z.1.1,unflattenGrid z.1),z.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the actual dense transition word in polynomial time -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

lemma clog_two_eq_size_pred (n : ℕ) : Nat.clog 2 n=(n-1).size := by
  cases n with
  | zero => simp
  | succ n =>
    apply Nat.le_antisymm
    · apply (Nat.clog_le_iff_le_pow (by decide)).mpr
      have h := Nat.lt_size_self n
      simpa only [Nat.add_sub_cancel] using Nat.succ_le_of_lt h
    · apply Nat.size_le.mpr
      have h := Nat.le_pow_clog (by decide : 1<2) (n+1)
      simpa only [Nat.add_sub_cancel] using Nat.lt_of_succ_le h

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def wordChunk (z : (ℕ×List Bool)×ℕ) : List Bool :=
  (z.1.2.drop (z.2*z.1.1)).take z.1.1

def completeWordRows (z : ℕ×List Bool) : List ℕ := List.range (z.2.length/z.1)

def wordChunks (z : ℕ×List Bool) : List (List Bool) :=
  (completeWordRows z).map (fun i => wordChunk (z,i))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev DependentChunkData := (List ℕ×List Bool)×ℕ

def chunkStart (z : DependentChunkData) : ℕ := (z.1.1.take z.2).sum

def dependentChunk (z : DependentChunkData) : List Bool :=
  (z.1.2.drop (chunkStart z)).take (z.1.1.getD z.2 0)

open scoped BigOperators

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary arithmetic for sequential subset inclusion

The rational inclusion threshold is computed by an integer product and
quotient. In particular the denominator is never expanded into a
unary loop; the only exponential integer has the supplied word length
as its binary length.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev HeadInput := (ℕ×ℕ)×List Bool

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev DrawState := (ℕ×ℕ)×List Bool

def prepareWords (z : (ℕ×ℕ)×List (List Bool)) : List (List Bool)×DrawState := (z.2,(z.1,[]))

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A flat-word program for a local initial subset

The first B bits select the size. The remaining word is partitioned
into B-bit inclusion rows, so the input list bounds the number of loop
iterations even on malformed inputs.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

abbrev SubsetInput := (ℕ×ℕ)×List Bool

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialChoiceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial independent-cell initialization program

The capacities are a supplied list. A polynomial index scan extracts
each disjoint variable-width word block and runs the local subset
program. The resulting rows are exactly the independent cell choices
in the initial finite-word law.
-/

namespace ContingencyTables.InitialChoiceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open DensePrograms FixedCardinalityProgram

def cellWidth (z : ℕ×ℕ) : ℕ := z.1+z.2*z.1

def widths (z : List ℕ×ℕ) : List ℕ := z.1.map (fun n => cellWidth (z.2,n))

abbrev Input := (List ℕ×ℕ)×List Bool

def indices (z : Input) : List ℕ := List.range z.1.1.length

end ContingencyTables.InitialChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CanonicalInitialEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

def pairValue (b : Bool) : List ℕ := [if b then 1 else 0,if b then 0 else 1]

def pairedCode (rows : List (List Bool)) : List ℕ := rows.flatten.flatMap pairValue

noncomputable section
variable {q : ℕ} (b : Fin q → ℕ)

def copyOrder : List (Copy b) := (List.finRange q).sigma (fun i => List.finRange (b i))

def pairOrder : List (Copy b×Bool) := (copyOrder b).product [false,true]

lemma copyOrder_nodup : (copyOrder b).Nodup :=
  (List.nodup_finRange q).sigma (fun i => List.nodup_finRange (b i))

lemma copyOrder_mem (p : Copy b) : p∈copyOrder b := by
  rcases p with ⟨i,k⟩
  simp [copyOrder]

lemma pairOrder_nodup : (pairOrder b).Nodup :=
  (copyOrder_nodup b).product (by decide)

lemma pairOrder_mem (p : Copy b×Bool) : p∈pairOrder b := by
  rcases p with ⟨p,t⟩
  have hp := copyOrder_mem b p
  cases t <;> simp [pairOrder,hp]

def coordinateEquiv : (Copy b×Bool) ≃ Fin (pairOrder b).length :=
  (List.Nodup.getEquivOfForallMemList (pairOrder b) (pairOrder_nodup b) (pairOrder_mem b)).symm

end
end ContingencyTables.CanonicalInitialEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

abbrev Input := ((List ℕ×List ℕ)×MatrixCode)×ℕ

def entry (z : Input×(ℕ×ℕ)) : ℕ := matrixEntry (z.1.1.2,z.2)

def retainedTest (z : Input×(ℕ×ℕ)) : Bool := decide (entry z<z.1.2)

def catalog (z : Input) : List (ℕ×ℕ) :=
  (cellPairs z.1.1).filter (fun a => retainedTest (z,a))

def capacities (z : Input) : List ℕ := (catalog z).map (fun a => entry (z,a))

lemma catalog_nodup (z : Input) : (catalog z).Nodup :=
  (cellPairs_nodup z.1.1.1 z.1.1.2).filter _

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

def input (A : Instance (Fin m) (Fin n)) : Input :=
  (((List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat)),
    matrixCode A.b),A.W)

lemma small_iff_bound (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    A.small i j=true ↔ A.b i j<A.W := by
  constructor
  · exact A.hsmall i j
  · intro hb
    cases hs : A.small i j
    · have hh := (A.hlarge i j hs).1
      omega
    · rfl

lemma entry_input (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    entry (input A,(i.val,j.val))=A.b i j := matrixEntry_code A.b i j

lemma mem_catalog_input (A : Instance (Fin m) (Fin n)) (ij : ℕ×ℕ) :
    ij∈catalog (input A) ↔ ∃ a : SmallCell A,(a.val.1.val,a.val.2.val)=ij := by
  rw [catalog,List.mem_filter]
  change (ij∈cellPairs (List.ofFn (fun i => (A.r i).toNat),
    List.ofFn (fun j => (A.c j).toNat)) ∧ retainedTest (input A,ij)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,hb⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have he : A.b i j<A.W := by
      have hh : entry (input A,(i.val,j.val))<A.W := of_decide_eq_true hb
      rwa [entry_input] at hh
    have hs : A.small i j=true := (small_iff_bound A i j).mpr he
    exact ⟨⟨(i,j),hs⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨⟨a.val.1.isLt,a.val.2.isLt⟩,?_⟩
    apply decide_eq_true
    change entry (input A,(a.val.1.val,a.val.2.val))<A.W
    rw [entry_input]
    exact A.hsmall _ _ a.property

def catalogCell (A : Instance (Fin m) (Fin n)) (i : Fin (catalog (input A)).length) : SmallCell A :=
  Classical.choose ((mem_catalog_input A ((catalog (input A))[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_coordinates (A : Instance (Fin m) (Fin n))
    (i : Fin (catalog (input A)).length) :
    ((catalogCell A i).val.1.val,(catalogCell A i).val.2.val)=(catalog (input A))[i.val] :=
  Classical.choose_spec ((mem_catalog_input A ((catalog (input A))[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_bijective (A : Instance (Fin m) (Fin n)) :
    Function.Bijective (catalogCell A) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : SmallCell A => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((catalog_nodup (input A)).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈catalog (input A) :=
      (mem_catalog_input A _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates A ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def cellEquiv (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (input A)).length ≃ SmallCell A :=
  Equiv.ofBijective (catalogCell A) (catalogCell_bijective A)

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates
open CompanionArithmeticProposal
open scoped BigOperators Classical

abbrev ProgramInput := (CompanionCellCatalog.Input×ℕ)×List Bool

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def cellOrder : SmallCell A ≃ Fin (CompanionCellCatalog.catalog (CompanionCellCatalog.input A)).length :=
  (CompanionCellCatalog.cellEquiv A).symm

def capacities (i : Fin (CompanionCellCatalog.catalog (CompanionCellCatalog.input A)).length) : ℕ :=
  A.b ((cellOrder A).symm i).val.1 ((cellOrder A).symm i).val.2

def wordLength (B : ℕ) : ℕ := bitCount (capacities A) B

def copyOrder : Labels A ≃ Copy (capacities A) := Equiv.sigmaCongrLeft' (cellOrder A)

def pairOrder : (Labels A×Bool) ≃ (Copy (capacities A)×Bool) :=
  Equiv.prodCongr (copyOrder A) (Equiv.refl Bool)

def coordinateOrder : (Labels A×Bool) ≃ Fin (CanonicalInitialEncoding.pairOrder (capacities A)).length :=
  (pairOrder A).trans (CanonicalInitialEncoding.coordinateEquiv (capacities A))

end
end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

def indexPair (i : ℕ) : ℕ×ℕ := (2*i,2*i+1)

def catalog (xs : List ℕ) : List (ℕ×ℕ) := (List.range (xs.length/2)).map indexPair

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

def labelOrder : Fin (copyOrder b).length ≃ Copy b :=
  List.Nodup.getEquivOfForallMemList (copyOrder b) (copyOrder_nodup b) (copyOrder_mem b)

end
end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def pairLabels : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length ≃ Labels A :=
  (PairedCatalogProgram.labelOrder (capacities A)).trans (copyOrder A).symm

end
end ContingencyTables.CompanionComputedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComplementChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's original omission coordinates

Complementation reverses defect labels and their multipliers. We prove the
actual chain energy, conditional projection, and variance identities before
transferring the variance and observable inequalities back to the original
factorial lift f. The final theorems assume its omission property.
-/

namespace ContingencyTables.ComplementChain

open scoped BigOperators Classical
open BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
def complementEquiv : Set Γ ≃ Set Γ where
  toFun := compl
  invFun := compl
  left_inv := compl_compl
  right_inv := compl_compl

omit [Fintype Γ] [DecidableEq Γ] in
def reverseMultiplier (w : (Γ × Γ) → (Γ × Γ) → ℝ) : (Γ × Γ) → (Γ × Γ) → ℝ :=
  fun p r => w r p

end ContingencyTables.ComplementChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of the literal companion phase observables -/

namespace ContingencyTables.CompanionConcentration

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionAnnealing
open TwoLiftStates BinaryContraction

variable {I J : Type*} [Fintype I] [Fintype J]

lemma pairs_ne_nil (A : Instance I J) (hp : 0< Fintype.card (Labels A)) :
    (pairs : List ((Labels A×Bool)×(Labels A×Bool)))≠[] := by
  apply List.ne_nil_of_length_pos
  simpa only [PairedLabels.length] using hp

end ContingencyTables.CompanionConcentration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealPathApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping an entire finite history during real-kernel comparison -/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first coordinate records which entries of the vector have been
written. Saturation keeps the state space finite even after the horizon. -/
abbrev PathState (X : Type*) (N : ℕ) := Fin (N+1) × (Fin (N+1) → X)

def nextPosition {N : ℕ} (i : Fin (N+1)) : Fin (N+1) :=
  ⟨min (i.val+1) N,Nat.lt_succ_of_le (min_le_right _ _)⟩

def pathRead {N : ℕ} (a : PathState X N) : X := a.2 a.1

def pathPut {N : ℕ} (a : PathState X N) (x : X) : PathState X N :=
  (nextPosition a.1,Function.update a.2 (nextPosition a.1) x)

def pathInitial (N : ℕ) (x : X) : PathState X N := (0,fun _ => x)

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The observed Boolean trajectory has the source path law

The finite history stores the visited prefix. Its exact real reference
expectation is the manuscript's list-path expectation, so the row error
controls events involving all empirical observations simultaneously.
-/

namespace ContingencyTables.CompanionPhaseTrajectory

open RealKernelApproximation CompanionBooleanPhase
open FirstSuccess ResidualMixture
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

def historyPrefix {N : ℕ} (a : PathState X N) : List X :=
  List.ofFn (fun i : Fin (a.1.val+1) =>
    a.2 ⟨i.val,lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_of_lt_succ a.1.isLt))⟩)

lemma prefix_nonempty {N : ℕ} (a : PathState X N) : historyPrefix a≠[] := by
  simp [historyPrefix]

end

end ContingencyTables.CompanionPhaseTrajectory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Capped trace returns from the actual companion Boolean walk

The return search scans the recorded path after its initial state. Its
reference expectation is the finite Green sum defining the capped trace;
the Boolean walk contributes its path error.
-/

namespace ContingencyTables.CompanionTraceWords

open CompanionFactorialApplication CompanionBooleanPhase
open CompanionPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

/-- A fixed indicator convention keeps equivalent event descriptions
independent of the decision procedures inferred for their propositions. -/
def eventIndicator (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

end
end ContingencyTables.CompanionTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial code for recognizing and locating a trace return

The paired plain-state test sums the two bits of each label. The return
program scans the supplied path after its initial state; no enumeration
of the exponential paired-state space occurs.
-/

namespace ContingencyTables.CompanionTraceProgram

open CompanionChainValidator CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase CompanionTraceWords
open ProfilePrograms MatchingFPRAS.TreeTyped
open scoped Classical

def pairedPlainTest (z : ValidatorInput) : Bool :=
  balancedTest ((z.1.map (fun ij => z.2.getD ij.1 0),
    z.1.map (fun ij => z.2.getD ij.2 0)),1)

abbrev ReturnInput := List (ℕ×ℕ)×List (List ℕ)

def firstPlainCode (z : ReturnInput) : Option (List ℕ) :=
  (z.2.filter (fun xs => pairedPlainTest (z.1,xs)))[0]?

/-- Strict first return: the initial path entry is omitted. -/
def returnCode (z : ReturnInput) : Option (List ℕ) :=
  firstPlainCode (z.1,z.2.tail)

end ContingencyTables.CompanionTraceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open TwoLiftStates
open scoped Classical

def plainCountCode (z : ReturnInput) : ℕ :=
  (z.2.filter (fun xs => pairedPlainTest (z.1,xs))).length

def pairedDefectTest (z : ValidatorInput×(ℕ×ℕ)) : Bool :=
  defectTest (((z.1.1.map (fun ij => z.1.2.getD ij.1 0),
    z.1.1.map (fun ij => z.1.2.getD ij.2 0)),1),z.2)

abbrev DefectCountInput := ReturnInput×(ℕ×ℕ)

def defectItem (z : (List (ℕ×ℕ)×(ℕ×ℕ))×List ℕ) : Bool :=
  pairedDefectTest ((z.1.1,z.2),z.1.2)

def defectCountCode (z : DefectCountInput) : ℕ :=
  (z.1.2.filter (fun xs => pairedDefectTest ((z.1.1,xs),z.2))).length

end ContingencyTables.CompanionPhaseCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary rational program for each learned multiplier

The two observed frequencies have the same trajectory length, which
cancels before division. Thus one multiplication by the ratio of the
actual integer counts implements the exact rational update, including
the zero-denominator behavior on unsuccessful histories.
-/

namespace ContingencyTables.CompanionMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionPhaseCounts CompanionFactorialApplication CompanionRationalUpdates
open CompanionOrderedProposal CompanionArithmeticProposal
open scoped Classical

def countRatio (z : DefectCountInput) : TreeFraction.Fraction :=
  (plainCountCode z.1,defectCountCode z)

abbrev UpdateInput := DefectCountInput×TreeFraction.Fraction

def updateCode (z : UpdateInput) : TreeFraction.Fraction :=
  if z.1.2.1=z.1.2.2 then z.2 else TreeFraction.mul (z.2,countRatio z.1)

end ContingencyTables.CompanionMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open scoped Classical

abbrev FractionMatrix := List (List TreeFraction.Fraction)
abbrev Input := ReturnInput×FractionMatrix

def indices (z : ReturnInput) : List ℕ := List.range z.1.length

def readEntry (z : FractionMatrix×(ℕ×ℕ)) : TreeFraction.Fraction :=
  (z.1.getD z.2.1 []).getD z.2.2 (0,1)

def updateEntry (z : Input×(ℕ×ℕ)) : TreeFraction.Fraction :=
  updateCode ((z.1.1,z.2),readEntry (z.1.2,z.2))

def rowEntry (z : (Input×ℕ)×ℕ) : TreeFraction.Fraction :=
  updateEntry (z.1.1,(z.1.2,z.2))

def updateRow (z : Input×ℕ) : List TreeFraction.Fraction :=
  (indices z.1.1).map (fun j => rowEntry (z,j))

def updateMatrix (z : Input) : FractionMatrix :=
  (indices z.1).map (fun i => updateRow (z,i))

/-- Diagonal matrix entries do not name defect classes. -/
def positiveEntry (z : DefectCountInput) : Bool :=
  decide (z.2.1=z.2.2 ∨ 0<defectCountCode z)

def positiveRow (z : ReturnInput×ℕ) : Bool :=
  (indices z.1).all (fun j => positiveEntry (z.1,(z.2,j)))

def positiveCounts (z : ReturnInput) : Bool :=
  decide (0<plainCountCode z) && (indices z).all (fun i => positiveRow (z,i))

noncomputable section
open TwoLiftStates
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

def matrixCode (w : Fin p → Fin p → TreeFraction.Fraction) : FractionMatrix :=
  List.ofFn (fun i => List.ofFn (w i))

end
end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAggregateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exact fraction averages and products

These are the arithmetic folds used by the executed weight estimator.
Normalization makes the average valid on every input, including a raw
fraction with denominator zero.
-/

namespace ContingencyTables.FractionAggregateProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

def average (xs : List TreeFraction.Fraction) : TreeFraction.Fraction :=
  TreeFraction.div (TreeFraction.sum (xs.map TreeFraction.normalize),(xs.length,1))

def product (xs : List TreeFraction.Fraction) : TreeFraction.Fraction :=
  xs.foldl (fun a b => TreeFraction.mul (b,a)) (1,1)

end ContingencyTables.FractionAggregateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the observed ratio and learned phase update

The supplied pairs contain the current and next weight queries for every
observed state. Only plain states contribute to the ratio. The same actual
trajectory supplies the plain/defect counts and the abort test.
-/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionTraceProgram CompanionMultiplierMatrixProgram CompanionPhaseCounts

abbrev Fraction := TreeFraction.Fraction
abbrev Stored := FractionMatrix×Fraction
abbrev Input := ((ReturnInput×FractionMatrix)×Fraction)×List (Fraction×Fraction)
abbrev TermInput := CompanionChainValidator.ValidatorInput×(Fraction×Fraction)

def term (z : TermInput) : Fraction :=
  if CompanionTraceProgram.pairedPlainTest z.1 then TreeFraction.div (z.2.2,z.2.1) else (0,1)

def trajectory (z : Input) : ReturnInput := z.1.1.1

def indices (z : Input) : List ℕ := List.range (trajectory z).2.length

def termInput (z : Input×ℕ) : TermInput :=
  (((trajectory z.1).1,(trajectory z.1).2.getD z.2 []),z.1.2.getD z.2 ((0,1),(0,1)))

def indexedTerm (z : Input×ℕ) : Fraction := term (termInput z)

def terms (z : Input) : List Fraction := (indices z).map (fun i => indexedTerm (z,i))

attribute [local irreducible] trajectory terms

def total (z : Input) : Fraction := TreeFraction.sum (terms z)

def count (z : Input) : Fraction := (plainCountCode (trajectory z),1)

def ratio (z : Input) : Fraction := TreeFraction.div (total z,count z)

attribute [local irreducible] ratio

def estimate (z : Input) : Fraction := TreeFraction.mul (z.1.2,ratio z)

def next (z : Input) : Stored := (updateMatrix z.1.1,estimate z)

attribute [local irreducible] next

def output (z : Input) : Option Stored :=
  if positiveCounts (trajectory z) then some (next z) else none

end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit least roots of finite graph components

The selector uses the finite reachability closure, not a choice of a
quotient representative. Its defining closure runs exactly n growth
rounds on Fin n, including disconnected and singleton components.
-/

namespace ContingencyTables.FiniteGraphRoots

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma closure_nonempty (v : Fin n) : (closure G v).Nonempty :=
  ⟨v,(mem_closure G v v).mpr (Reachable.refl v)⟩

/-- The least actual vertex index in the reached component. -/
def root (v : Fin n) : Fin n := (closure G v).min' (closure_nonempty G v)

lemma root_mem (v : Fin n) : root G v∈closure G v :=
  Finset.min'_mem _ _

lemma root_reachable (v : Fin n) : G.Reachable v (root G v) :=
  (mem_closure G v (root G v)).mp (root_mem G v)

lemma root_constant {u v : Fin n} (h : G.Reachable u v) : root G u=root G v := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((mem_closure G u (root G v)).mpr
      (h.trans (root_reachable G v)))
  · exact Finset.min'_le _ _ ((mem_closure G v (root G u)).mpr
      (h.symm.trans (root_reachable G u)))

end ContingencyTables.FiniteGraphRoots

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forest completion with an explicit component-root selector

Only reachability and constancy on each component are needed for the
integral completion. Making these data explicit permits the executed
least-root selector to replace the original quotient representative,
without asserting that two different selectors are equal.
-/

namespace ContingencyTables.RootedCompletion

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestCut ForestCapacity MaximumForest

variable {V : Type*}

structure Selection (G : SimpleGraph V) where
  root : V → V
  reachable : ∀ v,G.Reachable v (root v)
  constant : ∀ {u v},G.Reachable u v → root u=root v

def canonical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Selection G where
  root := FiniteGraphRoots.root G
  reachable := FiniteGraphRoots.root_reachable G
  constant := FiniteGraphRoots.root_constant G

def Selection.map {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (S : Selection G) (e : G ≃g H) : Selection H where
  root v := e (S.root (e.symm v))
  reachable v := by
    have h := (S.reachable (e.symm v)).map e.toHom
    change H.Reachable (e (e.symm v)) (e (S.root (e.symm v))) at h
    simpa only [RelIso.apply_symm_apply] using h
  constant h := congrArg e (S.constant (h.map e.symm.toHom))

/-- The concrete row-then-column vertex order of the contingency graph. -/
def rowColumn {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n)) [DecidableRel T.Adj] :
    Selection T :=
  (canonical (T.comap finSumFinEquiv.symm)).map (Iso.comap finSumFinEquiv.symm T)

noncomputable def path {G : SimpleGraph V} (S : Selection G) (v : V) : G.Walk v (S.root v) :=
  Classical.choice (S.reachable v)

variable [Fintype V]

noncomputable def flow {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a b : V) : ℤ :=
  ∑ v,r v*walkFlow (path S v) a b

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
noncomputable def table (T : SimpleGraph (I⊕J)) (S : Selection T)
    (r : I → ℤ) (c : J → ℤ) (i : I) (j : J) : ℤ :=
  flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inr j)

end ContingencyTables.RootedCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

noncomputable def away (T : SimpleGraph V) (u v root : V) : V :=
  if (T.deleteEdges {s(u,v)}).Reachable u root then v else u

noncomputable def cut (T : SimpleGraph V) (u v root a : V) : Bool :=
  side (T.deleteEdges {s(u,v)}) (away T u v root) a

variable {I J : Type*}

noncomputable def treeCut (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (v : I⊕J) : Bool :=
  cut T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)) v

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def solved (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) : I → J → ℤ :=
  table A.T S (rowResidual A.small A.T A.r x free)
    (columnResidual A.small A.T A.c q free)

noncomputable def completed (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if A.T.Adj (.inl i) (.inr j) then solved A S x q free i j else free i j

end ContingencyTables.RootedPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical factors with the executed component-root convention

The line factors use the explicitly selected roots. Their tree factors,
widths and doubled row/column coordinates are exactly the source data.
-/

namespace ContingencyTables.RootedPenalty

open scoped BigOperators Classical Matrix
open CompanionFactorialApplication RootedCompletion
open ForestPenaltyApplication ForestLiteralCount
open ProductIntegerSignature RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rootFlag {T : SimpleGraph (I⊕J)} (S : Selection T) (v : I⊕J) : Bool :=
  decide (v=S.root v)

end ContingencyTables.RootedPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def signedResidual (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim
    (fun i => (∑ j,if A.small i j then x i j else completed A S x q free i j)-A.r i)
    (fun j => -((∑ i,if A.small i j then q i j else completed A S x q free i j)-A.c j))

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAcceptanceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev Input := TreeFraction.Fraction×List Bool

def scaledNumerator (z : Input) : ℕ := z.1.1*bitDenominator z.2

def threshold (z : Input) : ℕ := scaledNumerator z/z.1.2

end ContingencyTables.FractionAcceptanceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RationalIntervalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary arithmetic for a forest interval penalty

A signed affine numerator is stored as a difference of two naturals.
Its distance outside the interval [0,1] is a nonnegative fraction with
the same denominator; no signed rational comparison is required.
-/

namespace ContingencyTables.RationalIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := (ℕ×ℕ)×ℕ

def numerator (z : Input) : ℕ := (z.1.2-z.1.1)+(z.1.1-(z.1.2+z.2))

def intervalCode (z : Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator z,z.2)

end ContingencyTables.RationalIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

abbrev Term := (ℕ×ℕ)×ℕ
abbrev Input := ((ℕ×ℕ)×List Term)×ℕ

def positiveTerm (z : Term) : ℕ := z.1.1*z.2
def negativeTerm (z : Term) : ℕ := z.1.2*z.2

def parts (z : Input) : ℕ×ℕ :=
  (z.1.1.1+(z.1.2.map positiveTerm).sum,z.1.1.2+(z.1.2.map negativeTerm).sum)

def evaluate (z : Input) : TreeFraction.Fraction :=
  RationalIntervalProgram.intervalCode (parts z,z.2)

def signedParts (z : ℤ) : ℕ×ℕ := (z.toNat,(-z).toNat)

lemma signedParts_sub (z : ℤ) : ((signedParts z).1:ℤ)-(signedParts z).2=z := by
  change (z.toNat:ℤ)-((-z).toNat:ℤ)=z
  omega

end ContingencyTables.ForestAffineProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational assembly of the companion forest penalty

The natural root discrepancy and the finite list of tree affine forms
are combined by polynomial binary arithmetic to compute rationalD,
including the original maximum-forest cuts.
-/

namespace ContingencyTables.ForestPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionFactorialApplication CompanionOracleDensity ForestAssignmentSplit GraphCompletionCounts
open ForestScaledPenalty
open scoped BigOperators Classical

abbrev Input := (ℕ×ℕ)×List ForestAffineProgram.Input

def treeSum (z : Input) : TreeFraction.Fraction :=
  TreeFraction.sum (z.2.map ForestAffineProgram.evaluate)

def penaltyCode (z : Input) : TreeFraction.Fraction :=
  TreeFraction.mul ((z.1.1,1),TreeFraction.add ((z.1.2,1),treeSum z))


abbrev ExponentInput := (ℕ×ℕ)×Input

def weightedPenalty (z : ExponentInput) : TreeFraction.Fraction :=
  TreeFraction.mul (z.1,penaltyCode z.2)

def exponentCode (z : ExponentInput) : ℕ := (weightedPenalty z).1/(weightedPenalty z).2

end ContingencyTables.ForestPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedIntegerEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral coefficients of the executed selected-root affine penalty -/

namespace ContingencyTables.RootedIntegerEvaluation

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit

variable {I J : Type*} [Fintype I] [Fintype J]

def integerIndicator (b : Bool) : ℤ := if b then 1 else 0

noncomputable def sign (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : ℤ :=
  integerIndicator (RootedCut.treeCut A.T S t (.inl a.1))-
    integerIndicator (RootedCut.treeCut A.T S t (.inr a.2))

noncomputable def coefficient (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : ℤ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -(sign A S t a)*sign A S t t.val else 0

noncomputable def smallContribution (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℤ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    integerIndicator (RootedCut.treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      integerIndicator (RootedCut.treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

noncomputable def offset (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℤ :=
  A.X t.val.1 t.val.2-smallContribution A S t x q*sign A S t t.val-
    ∑ a : I×J,coefficient A S t a*A.X a.1 a.2

noncomputable def rationalScaledTree (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) : ℚ :=
  (offset A S t x q:ℚ)/(A.b t.val.1 t.val.2:ℚ)+
    ∑ f : FreeCell A.small A.T,
      ((coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)/B/
        (A.b t.val.1 t.val.2:ℚ))*v f

end ContingencyTables.RootedIntegerEvaluation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary penalty evaluation for the selected-root forest

The signed affine and fraction programs compute the root-specific
geometric penalty from its explicit input metadata.
-/

namespace ContingencyTables.RootedPenaltyProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open MatchingFPRAS RootedIntegerEvaluation

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rootCount (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) : ℕ :=
  ∑ a : I⊕J,if RootedPenalty.rootFlag S a then
    (RootedRootPenalty.signedResidual A S x q 0 a).natAbs else 0

noncomputable def rationalPenalty (A : Instance I J) (S : Selection A.T)
    (C : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) : ℚ :=
  C*((rootCount A S x q:ℚ)+∑ t : TreeCell A.T,max 0 (max
    (-rationalScaledTree A S (CompanionOracleDensity.rationalBinWidth A C) x q v t)
    (rationalScaledTree A S (CompanionOracleDensity.rationalBinWidth A C) x q v t-1)))

end ContingencyTables.RootedPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the stored phase update -/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS CompanionFactorialApplication CompanionTraceProgram CompanionPhaseCounts
open CompanionMultiplierMatrixProgram CompanionMultiplierProgram CompanionOrderedProposal
open CompanionArithmeticProposal CompanionRationalUpdates TwoLiftStates
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p q N : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin q)

def data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (estimate : Fraction) (values : Fin N→Fraction×Fraction) : Input :=
  ((((orderedCatalog A g e,(List.ofFn states).map (encodeSet e)),matrixCode w),estimate),List.ofFn values)

/-- The relevant view of a physical stored value consists of its actual
label-pair entries and its rational estimate. -/
def view (z : Stored) : (Fin p→Fin p→ℚ)×ℚ :=
  ((fun i j => TreeFraction.val (readEntry (z.1,(i.val,j.val)))),TreeFraction.val z.2)

def storedView (s : CompanionPhaseWords.Stored A) : (Fin p→Fin p→ℚ)×ℚ :=
  ((fun i j => s.multiplier (pair (g i)) (pair (g j))),s.estimate)

end
end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedArithmeticStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed coordinate proposals for the selected-root phase walk -/

namespace ContingencyTables.RootedArithmeticStep

open FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open RealKernelApproximation
open CompanionBooleanPhase (proposalBits )
open scoped BigOperators Classical

noncomputable section

def regroup (L P Q : Type*) : (L×(P×Q)) ≃ P×(L×Q) where
  toFun b := (b.2.1,(b.1,b.2.2))
  invFun b := (b.2.1,(b.1,b.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

end
end ContingencyTables.RootedArithmeticStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteVaryingWordWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent words for successive draws with varying widths -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits
noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev VaryingWords (width : ℕ → ℕ) (n : ℕ) :=
  (i : Fin n) → Fin (width i.val) → Bool

def varyingWalk (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) :
    (n : ℕ) → VaryingWords width n → X
  | 0,_ => x
  | n+1,bits => step n (varyingWalk width step x n (Fin.init bits)) (bits (Fin.last n))

def varyingWordEquiv (width : ℕ → ℕ) (n : ℕ) :
    (Fin (∑ i : Fin n,width i.val) → Bool) ≃ VaryingWords width n :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace restart bounds for the literal companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.CompanionTrace

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionAnnealing TwoLiftStates
open CompanionConcentration BinaryContraction

variable {I J : Type*} [Fintype I] [Fintype J]

def integerConstant (A : Instance I J) : ℕ :=
  let p := Fintype.card (Labels A)
  10*p^4*(9*(p*(1+8*p*A.W^4))+2*(8+32*p*A.W^6))

def time (A : Instance I J) (H K : ℕ) : ℕ :=
  2*integerConstant A*(H+Fintype.card (Labels A)+K+5)

noncomputable def minimumMass (A : Instance I J) (H K : ℕ) : ℝ :=
  (1/2:ℝ)^(H+Fintype.card (Labels A)+K)

end ContingencyTables.CompanionTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTargetMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing of the literal dyadic trace

The original and degree-completed state chains agree. Their traces
therefore agree as well, and the dyadic holding factor costs at most
two in the trace Poincare estimate.
-/

namespace ContingencyTables.CompanionTargetMixing

open CompanionFactorialApplication CompanionBooleanPhase
open CompanionTraceWords CompanionConcentration
open CompanionAnnealing CompanionRationalUpdates TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def restartTime (A : Instance I J) (H K : ℕ) : ℕ := 2*CompanionTrace.time A H K

end
end ContingencyTables.CompanionTargetMixing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical Matrix Topology
open Filter CompanionFactorialApplication ForestPenaltyApplication
open RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def cellWidth (A : Instance I J) (a : I×J) : ℕ :=
  ForestLiteralCount.width A.T A.d A.b a.1 a.2

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TransversalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact binomial/factorial cancellation in a transversal normalizer

Every small integer profile has a product of binomial numbers of label
preimages. Its factorial lift contributes the inverse product, so the
actual transversal normalizer is exactly the raw integer-profile sum.
-/

namespace ContingencyTables.TransversalCount

open scoped BigOperators Classical
open TwoLiftStates LabelledFactorial InitialTransversals

variable {C : Type*} [Fintype C] (b : C → ℕ)

@[reducible] def Profile := (c : C) → Fin (b c+1)

end ContingencyTables.TransversalCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual companion normalizer equals the full physical balanced mass -/

namespace ContingencyTables.CompanionPhysicalNormalizer

open scoped BigOperators Classical
open CompanionFactorialApplication TwoLiftStates
open TreeMarginalSignature
open ForestPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

lemma small_width (A : Instance I J) (s : SmallCell A) :
    cellWidth A s.val=A.b s.val.1 s.val.2 := by
  have ht : ¬A.T.Adj (.inl s.val.1) (.inr s.val.2) := by
    intro ht
    have hs : A.small s.val.1 s.val.2=false := A.hTG ht
    exact Bool.false_ne_true (hs.symm.trans s.property)
  simp only [cellWidth,ForestLiteralCount.width,ht,ite_false]

noncomputable def smallInterval (A : Instance I J) (s : SmallCell A) :
    Fin (cellWidth A s.val+1) ≃ Fin (A.b s.val.1 s.val.2+1) where
  toFun k := ⟨k.val,by rw [← small_width A s]; exact k.isLt⟩
  invFun k := ⟨k.val,by rw [small_width A s]; exact k.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ContingencyTables.CompanionPhysicalNormalizer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeExteriorPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The narrow exterior tree intervals contain fewer than 2 gamma b positions -/

namespace ContingencyTables.TreeExteriorPositions

open scoped Classical

noncomputable def positions (ell : ℤ) (b U : ℕ) (delta : ℝ) : Finset (Fin (U+1)) :=
  Finset.univ.filter (fun k =>
    ((ell+(k.val:ℤ)<0) ∧ -((ell+(k.val:ℤ):ℤ):ℝ)<delta) ∨
    (((b:ℤ)<ell+(k.val:ℤ)) ∧ (((ell+(k.val:ℤ):ℤ):ℝ)-b)<delta))

end ContingencyTables.TreeExteriorPositions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeFeasibleMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every feasible table contributes one unit to its actual cell fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

lemma lower_nonpositive (A : Instance I J) (i : I) (j : J) :
    lower A.T A.d A.b i j ≤ 0 := by
  unfold lower
  split_ifs <;> omega

lemma upper_ge_capacity (A : Instance I J) (i : I) (j : J) :
    (A.b i j:ℤ) ≤ lower A.T A.d A.b i j+width A.T A.d A.b i j := by
  unfold lower width
  split_ifs
  · have hd := A.hd
    have hprod : A.b i j ≤ A.d*A.b i j := by nlinarith
    have hh : ((A.b i j+10*A.d*A.b i j:ℕ):ℤ) ≤ (20*A.d*A.b i j:ℕ) := by
      exact_mod_cast (show A.b i j+10*A.d*A.b i j ≤ 20*A.d*A.b i j by nlinarith)
    push_cast at hh ⊢
    linarith
  · simp

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionNearMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual narrow exterior region contributes at most 4 gamma K per tree cell -/

namespace ContingencyTables.CompanionNearMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalNormalizer
open TreeMarginalSignature TreeExteriorPositions ForestPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def cellPositions (A : Instance I J) (t : I×J) (gamma : ℝ) :
    Finset (Fin (cellWidth A t+1)) :=
  positions (ForestLiteralCount.lower A.T A.d A.b t.1 t.2) (A.b t.1 t.2)
    (cellWidth A t) (gamma*A.b t.1 t.2)

end ContingencyTables.CompanionNearMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasible physical balanced profiles are exactly bounded contingency tables -/

namespace ContingencyTables.CompanionPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature

variable {I J : Type*} [Fintype I] [Fintype J]

lemma row_nonnegative (A : Instance I J) (i : I) : 0 ≤ A.r i := by
  rw [← A.hXr i]
  exact Finset.sum_nonneg (fun j _ => (A.hX i j).1)

lemma column_nonnegative (A : Instance I J) (j : J) : 0 ≤ A.c j := by
  rw [← A.hXc j]
  exact Finset.sum_nonneg (fun i _ => (A.hX i j).1)

end ContingencyTables.CompanionPhysicalTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual terminal companion normalizer approximates the table count -/

namespace ContingencyTables.CompanionTerminalMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables CompanionPhysicalNormalizer
open CompanionNearMass TreeMarginalSignature

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TreeCell (A : Instance I J) := {t : I×J // A.T.Adj (.inl t.1) (.inr t.2)}

/-- These are the actual attained minima and maxima after the paper's
integer bound-tightening step. They are feasible tables, not marginal
mass or signature assumptions. -/
structure Endpoints (A : Instance I J) where
  lowerTable : TreeCell A → I → J → ℤ
  upperTable : TreeCell A → I → J → ℤ
  lowerBounds : ∀ t i j,0 ≤ lowerTable t i j ∧ lowerTable t i j ≤ A.b i j
  upperBounds : ∀ t i j,0 ≤ upperTable t i j ∧ upperTable t i j ≤ A.b i j
  lowerRows : ∀ t i,(∑ j,lowerTable t i j)=A.r i
  lowerColumns : ∀ t j,(∑ i,lowerTable t i j)=A.c j
  upperRows : ∀ t i,(∑ j,upperTable t i j)=A.r i
  upperColumns : ∀ t j,(∑ i,upperTable t i j)=A.c j
  lowerAttains : ∀ t,lowerTable t t.val.1 t.val.2=0
  upperAttains : ∀ t,upperTable t t.val.1 t.val.2=(A.b t.val.1 t.val.2:ℤ)

noncomputable def tableCount (A : Instance I J) : ℝ :=
  Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b)

end ContingencyTables.CompanionTerminalMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion's literal terminal parameter choices -/

namespace ContingencyTables.CompanionTerminalParameters

noncomputable def precision (epsilon : ℝ) : ℕ := Nat.ceil (Real.logb 2 (1/epsilon))

noncomputable def allowance (L d : ℕ) (epsilon : ℝ) : ℕ :=
  20*(L+d+precision epsilon+1)

noncomputable def gamma (L d : ℕ) (epsilon : ℝ) : ℝ :=
  epsilon/(512*(d:ℝ)*allowance L d epsilon)

noncomputable def coefficient (L d : ℕ) (epsilon : ℝ) : ℕ :=
  Nat.ceil (4*(allowance L d epsilon:ℝ)/gamma L d epsilon)

lemma allowance_positive (L d : ℕ) (epsilon : ℝ) : 0 < allowance L d epsilon := by
  unfold allowance
  omega

lemma gamma_positive (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    0 < gamma L d epsilon := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK : (0:ℝ) < allowance L d epsilon := by exact_mod_cast allowance_positive L d epsilon
  unfold gamma
  positivity

lemma coefficient_positive (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    0 < coefficient L d epsilon := by
  apply Nat.one_le_ceil_iff.mpr
  have hK : (0:ℝ) < allowance L d epsilon := by exact_mod_cast allowance_positive L d epsilon
  exact div_pos (by positivity) (gamma_positive L d epsilon hd he)

end ContingencyTables.CompanionTerminalParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal finite phase estimator has the required counting accuracy -/

namespace ContingencyTables.CompanionTerminalApplication

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionTerminalMass CompanionTerminalParameters
open CompanionAnnealing

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def finalPhase (A : Instance I J) (L : ℕ) (epsilon : ℝ) : ℕ :=
  10*coefficient L A.d epsilon*A.d^2*(A.W+1)

end ContingencyTables.CompanionTerminalApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Soundness of the actual stored rational count estimate -/

namespace ContingencyTables.RootedStoredEstimate

open CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open CompanionTerminalMass (Endpoints tableCount )
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def initialTotal (A : Instance I J) : ℚ :=
  (∏ a : ForestAssignmentSplit.FreeCell A.small A.T,((A.b a.val.1 a.val.2+1:ℕ):ℚ))*
    ∏ s : SmallCell A,((A.b s.val.1 s.val.2+1:ℕ):ℚ)

def initialStored (A : Instance I J) : Stored A :=
  ⟨initial A,initialTotal A⟩

end
end ContingencyTables.RootedStoredEstimate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stored rational outputs of the actual outer phases

The initial record is at index zero. Later records are the outputs
stored in the finite history; the initial record also supplies every
unused future entry to the restart's multiplier function.
-/

namespace ContingencyTables.RootedStoredHistory

open CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedStoredEstimate
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def lookup (A : Instance I J) (history : List (Stored A)) : ℕ → Stored A
  | 0 => initialStored A
  | i+1 => history.getD i (initialStored A)

end
end ContingencyTables.RootedStoredHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive phases on a common finite Boolean word space -/

namespace ContingencyTables.RootedPhaseHistory

open FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open RootedStoredHistory
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

structure Settings (A : Instance I J) where
  C : ℕ
  K : ℕ
  H : ℕ
  L : ℕ
  k : ℕ
  n : ℕ
  N : ℕ
  h : ℕ
  hK : 1 ≤ K
  hW : 100*A.d*K ≤ A.W
  xi : ℚ
  v : Grid (I := Fin (dimension A)) K

lemma value_le_sum {N : ℕ} (f : Fin N → ℕ) (i : Fin N) :
    f i ≤ ∑ j,f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end
end ContingencyTables.RootedPhaseHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only canonical pair entries affect the executed chain

The finite matrix stores one entry per pair of labels. Values of the
mathematical multiplier on arbitrary noncanonical coordinate pairs
do not affect any weight call, acceptance decision, or capped return.
-/

namespace ContingencyTables.CompanionMultiplierAgreement

open CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open scoped Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def Agree (A : Instance I J) (w w' : Pair A → Pair A → ℚ) : Prop :=
  ∀ a b : Labels A, w (pair a) (pair b)=w' (pair a) (pair b)

end
end ContingencyTables.CompanionMultiplierAgreement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical multiplier entries determine the projected phase history

The extension uses only the first label of a raw coordinate pair. Its values
away from canonical pairs need not match the original multiplier.
-/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CompanionRationalUpdates CompanionMultiplierAgreement
open TwoLiftStates GridBoundary
open CompanionPhaseWords (Stored )
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

abbrev Canonical := (Fin p→Fin p→ℚ)×ℚ

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCappedReturnProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary program for a total capped return

The strict return scan is followed by the supplied initial code on a
missing return. Both operations have polynomial binary realizers.
-/

namespace ContingencyTables.CompanionCappedReturnProgram

open MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionFactorialApplication CompanionBooleanPhase CompanionChainValidator
open CompanionTraceProgram CompanionTraceWords CompanionPhaseTrajectory
open CompanionArithmeticProposal CompanionRationalUpdates GridBoundary
open scoped Classical

def optionDefault (z : List ℕ×Option (List ℕ)) : List ℕ := z.2.getD z.1

abbrev TotalReturnInput := ReturnInput×List ℕ

def totalReturnCode (z : TotalReturnInput) : List ℕ :=
  (returnCode z.1).getD z.2

end ContingencyTables.CompanionCappedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NaturalBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Input := List ℕ × List ℕ
abbrev Entry := Input × ℕ

def start (z : Entry) : ℕ := (z.1.1.take z.2).sum

def block (z : Entry) : List ℕ :=
  (z.1.2.drop (start z)).take (z.1.1.getD z.2 0)

def indices (z : Input) : List ℕ := List.range z.1.length

def blocks (z : Input) : List (List ℕ) := (indices z).map (fun i => block (z,i))

end ContingencyTables.NaturalBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev ReadInput := (List ℕ × Bool) × (ℕ × ℕ)

def sideValue (z : ReadInput) : ℕ :=
  min (z.1.1.getD (if z.1.2 then z.2.2 else z.2.1) 0) 1

def sideEntries (z : List ℕ × Bool) : List ℕ :=
  (PairedCatalogProgram.catalog z.1).map (fun p => sideValue (z,p))

def sideCount (z : List ℕ × Bool) : ℕ := (sideEntries z).sum

abbrev Input := List ℕ × List ℕ

def width (n : ℕ) : ℕ := 2*n

def rows (z : Input) : List (List ℕ) :=
  NaturalBlockProgram.blocks (z.1.map width,z.2)

def counts (xs : List ℕ) : ℕ × ℕ := (sideCount (xs,false),sideCount (xs,true))

def profileRows (z : Input) : List (ℕ × ℕ) := (rows z).map counts

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedFactorialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact factorial multiplier from the encoded paired state

Every factorial argument is bounded by the supplied code length. In a
valid code each cell block has length twice its capacity, so the computed
denominator is exactly the manuscript's capacity factorial.
-/

namespace ContingencyTables.PairedFactorialProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial PairedProfileProgram
open scoped BigOperators Classical

def sideFactor (z : List ℕ × Bool) : ℕ := (sideCount z).factorial

def pairCount (xs : List ℕ) : ℕ := xs.length/2

def denominator (xs : List ℕ) : ℕ := (pairCount xs).factorial

def numerator (xs : List ℕ) : ℕ := sideFactor (xs,false)*sideFactor (xs,true)

def rowRatio (xs : List ℕ) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator xs,denominator xs)

def output (z : PairedProfileProgram.Input) : TreeFraction.Fraction :=
  FractionAggregateProgram.product ((rows z).map rowRatio)
end ContingencyTables.PairedFactorialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDirectedBFS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic directed breadth-first search

Each round retains every discovered path and scans the vertex list for
one predecessor of each undiscovered vertex. There is one stored path
per vertex; the search does not enumerate candidate paths.
-/

namespace ContingencyTables.FiniteDirectedBFS

variable {n : ℕ}

/-- A directed walk, including its two endpoints. -/
inductive Route (E : Fin n → Fin n → Bool) (s : Fin n) :
    Fin n → List (Fin n) → Prop
  | start : Route E s s [s]
  | extend {u v xs} : Route E s u xs → E u v=true → Route E s v (xs++[v])

namespace Route

variable {E : Fin n → Fin n → Bool} {s v : Fin n} {xs : List (Fin n)}

theorem nonempty (h : Route E s v xs) : xs≠[] := by
  cases h <;> simp

theorem length_pos (h : Route E s v xs) : 0<xs.length :=
  List.length_pos_iff.mpr h.nonempty

theorem head (h : Route E s v xs) : xs.head?=some s := by
  induction h with
  | start => rfl
  | @extend u v xs h _ ih =>
    rw [List.head?_append_of_ne_nil _ h.nonempty]
    exact ih

theorem last (h : Route E s v xs) : xs.getLast?=some v := by
  cases h <;> simp

theorem chain (h : Route E s v xs) : xs.IsChain (fun a b=>E a b=true) := by
  induction h with
  | start => exact List.IsChain.singleton _
  | @extend u v xs h huv ih =>
    apply ih.append (List.IsChain.singleton _)
    simpa [h.last] using huv

/-- Every visited vertex has a prefix walk no longer than the whole walk. -/
theorem routePrefix (h : Route E s v xs) {w : Fin n} (hw : w∈xs) :
    ∃ ys, Route E s w ys ∧ ys.length≤xs.length := by
  induction h with
  | start =>
    have he : w=s := by simpa using hw
    subst w
    exact ⟨[s],Route.start,le_rfl⟩
  | @extend u v xs h huv ih =>
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨ys,hy,hl⟩ := ih hw
      exact ⟨ys,hy,hl.trans (by simp)⟩
    · have he : w=v := by simpa using hw
      subst w
      exact ⟨xs++[v],h.extend huv,le_rfl⟩

end Route

abbrev Paths (n : ℕ) := Fin n → Option (List (Fin n))

def discovered (P : Paths n) (v : Fin n) : Prop := ∃ xs,P v=some xs

def predecessor (E : Fin n → Fin n → Bool) (P : Paths n) (v : Fin n) :
    Option (Fin n) :=
  (List.finRange n).find? (fun u=> (P u).isSome && E u v)

def round (E : Fin n → Fin n → Bool) (P : Paths n) (v : Fin n) :
    Option (List (Fin n)) :=
  match P v with
  | some xs => some xs
  | none => (predecessor E P v).bind (fun u=>(P u).map (fun xs=>xs++[v]))

def paths (E : Fin n → Fin n → Bool) (s : Fin n) : ℕ → Paths n
  | 0 => fun v=>if v=s then some [s] else none
  | k+1 => round E (paths E s k)

lemma predecessor_some {E : Fin n → Fin n → Bool} {P : Paths n}
    {v u : Fin n} (h : predecessor E P v=some u) :
    discovered P u ∧ E u v=true := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true,Option.isSome_iff_exists] at hp
  exact hp

lemma predecessor_none {E : Fin n → Fin n → Bool} {P : Paths n}
    {v : Fin n} (h : predecessor E P v=none) :
    ∀ u,discovered P u → E u v≠true := by
  have hp := List.find?_eq_none.mp h
  intro u hu he
  have hx := hp u (List.mem_finRange u)
  obtain ⟨xs,hxs⟩ := hu
  simp [hxs,he] at hx

lemma round_retains {E : Fin n → Fin n → Bool} {P : Paths n}
    {v : Fin n} {xs : List (Fin n)} (h : P v=some xs) :
    round E P v=some xs := by simp [round,h]

lemma round_discovered {E : Fin n → Fin n → Bool} {P : Paths n} {v : Fin n} :
    discovered (round E P) v ↔
      discovered P v ∨ ∃ u,discovered P u ∧ E u v=true := by
  cases hv : P v with
  | some xs =>
    constructor
    · intro _; exact Or.inl ⟨xs,hv⟩
    · intro _; exact ⟨xs,round_retains hv⟩
  | none =>
    cases hp : predecessor E P v with
    | none =>
      constructor
      · rintro ⟨xs,hxs⟩
        simp [round,hv,hp] at hxs
      · intro h
        rcases h with ⟨xs,hxs⟩ | ⟨u,hu,he⟩
        · simp [hv] at hxs
        · exact False.elim (predecessor_none hp u hu he)
    | some u =>
      obtain ⟨⟨xs,hxs⟩,huv⟩ := predecessor_some hp
      constructor
      · intro _; exact Or.inr ⟨u,⟨xs,hxs⟩,huv⟩
      · intro _; exact ⟨xs++[v],by simp [round,hv,hp,hxs]⟩

theorem paths_sound {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) :
    Route E s v xs ∧ xs.length≤k+1 := by
  induction k generalizing v xs with
  | zero =>
    simp only [paths] at h
    split at h
    · rename_i he
      subst v
      have hx : xs=[s] := by simpa using h.symm
      subst xs
      exact ⟨Route.start,le_rfl⟩
    · simp at h
  | succ k ih =>
    change round E (paths E s k) v=some xs at h
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [round,hv] using h
      subst xs
      obtain ⟨hr,hl⟩ := ih hv
      exact ⟨hr,hl.trans (by omega)⟩
    | none =>
      cases hp : predecessor E (paths E s k) v with
      | none => simp [round,hv,hp] at h
      | some u =>
        obtain ⟨⟨ys,hy⟩,huv⟩ := predecessor_some hp
        have hx : ys++[v]=xs := by simpa [round,hv,hp,hy] using h
        subst xs
        obtain ⟨hr,hl⟩ := ih hy
        exact ⟨hr.extend huv,by simpa using Nat.add_le_add_right hl 1⟩

theorem route_discovered {E : Fin n → Fin n → Bool} {s v : Fin n}
    {xs : List (Fin n)} (h : Route E s v xs) (k : ℕ)
    (hl : xs.length≤k+1) : discovered (paths E s k) v := by
  induction k generalizing v xs with
  | zero =>
    cases h with
    | start => exact ⟨[s],by simp [paths]⟩
    | @extend u v ys hy _ =>
      have hp := hy.length_pos
      simp only [List.length_append,List.length_singleton] at hl
      omega
  | succ k ih =>
    change discovered (round E (paths E s k)) v
    apply round_discovered.mpr
    cases h with
    | start => exact Or.inl (ih Route.start (by simp))
    | @extend u v ys hy huv =>
      exact Or.inr ⟨u,ih hy (by simpa using hl),huv⟩

theorem paths_shortest {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) :
    ∀ ys,Route E s v ys → xs.length≤ys.length := by
  induction k generalizing v xs with
  | zero =>
    have ⟨_,hl⟩ := paths_sound h
    intro ys hy
    exact hl.trans (by have hp:=hy.length_pos; omega)
  | succ k ih =>
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [paths,round,hv] using h
      subst xs
      exact ih hv
    | none =>
      intro ys hy
      have hs := (paths_sound h).2
      by_contra hn
      have hl : ys.length≤k+1 := by omega
      obtain ⟨zs,hz⟩ := route_discovered hy k hl
      simp [hv] at hz

theorem paths_nodup {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) : xs.Nodup := by
  induction k generalizing v xs with
  | zero =>
    have ⟨hr,_⟩ := paths_sound h
    cases hr with
    | start => simp
    | @extend u v ys hy _ =>
      have hp:=hy.length_pos
      have hl := (paths_sound h).2
      simp only [List.length_append,List.length_singleton] at hl
      omega
  | succ k ih =>
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [paths,round,hv] using h
      subst xs
      exact ih hv
    | none =>
      cases hp : predecessor E (paths E s k) v with
      | none => simp [paths,round,hv,hp] at h
      | some u =>
        obtain ⟨⟨ys,hy⟩,_⟩ := predecessor_some hp
        have hx : ys++[v]=xs := by simpa [paths,round,hv,hp,hy] using h
        subst xs
        have hnot : v∉ys := by
          intro hm
          have ⟨hr,hl⟩ := paths_sound hy
          obtain ⟨zs,hz,hzl⟩ := hr.routePrefix hm
          obtain ⟨ws,hw⟩ := route_discovered hz k (hzl.trans hl)
          simp [hv] at hw
        apply List.nodup_append.mpr
        refine ⟨ih hy,by simp,?_⟩
        intro a ha b hb hab
        have hb' : b=v := by simpa using hb
        exact hnot (hab.trans hb' ▸ ha)

theorem paths_length_le {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) : xs.length≤n := by
  simpa using List.Nodup.length_le_card (paths_nodup h)

/-- Every directed walk is found within n rounds. The proof uses the
short simple path stored by the search, rather than enumerating walks. -/
theorem route_found {E : Fin n → Fin n → Bool} {s v : Fin n}
    {xs : List (Fin n)} (h : Route E s v xs) :
    discovered (paths E s n) v := by
  obtain ⟨ys,hy⟩ := route_discovered h xs.length (by omega)
  exact route_discovered (paths_sound hy).1 n
    ((paths_length_le hy).trans (by omega))

/-- The computed reached set contains the source and is closed under
every directed edge. This is the cut certificate used on failure. -/
theorem source_found (E : Fin n → Fin n → Bool) (s : Fin n) :
    discovered (paths E s n) s := route_found Route.start

theorem reached_closed {E : Fin n → Fin n → Bool} {s u v : Fin n}
    (hu : discovered (paths E s n) u) (huv : E u v=true) :
    discovered (paths E s n) v := by
  obtain ⟨xs,hxs⟩ := hu
  exact route_found ((paths_sound hxs).1.extend huv)

end ContingencyTables.FiniteDirectedBFS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DirectedBFSCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materialized breadth-first path tables

Every round reads the preceding path table and writes one table of the
same size. Consequently evaluation does not recursively recompute old
rounds when different vertices ask for their predecessors.
-/

namespace ContingencyTables.DirectedBFSCode

abbrev Graph := List (List Bool)
abbrev Store := List (Option (List ℕ))

def adjacent (g : Graph) (u v : ℕ) : Bool := (g.getD u []).getD v false
def lookup (P : Store) (v : ℕ) : Option (List ℕ) := P.getD v none

def predecessor (g : Graph) (P : Store) (v : ℕ) : Option ℕ :=
  (List.range g.length).find? (fun u=>(lookup P u).isSome && adjacent g u v)

def roundRow (g : Graph) (P : Store) (v : ℕ) : Option (List ℕ) :=
  match lookup P v with
  | some xs => some xs
  | none => (predecessor g P v).bind (fun u=>(lookup P u).map (fun xs=>xs++[v]))

def round (g : Graph) (P : Store) : Store :=
  (List.range g.length).map (roundRow g P)

def initial (g : Graph) (s : ℕ) : Store :=
  (List.range g.length).map (fun v=>if v=s then some [s] else none)

def run (g : Graph) (s : ℕ) : Store :=
  (List.range g.length).foldl (fun P _=>round g P) (initial g s)

def search (g : Graph) (s t : ℕ) : Option (List ℕ) := lookup (run g s) t

def graphCode {n : ℕ} (E : Fin n → Fin n → Bool) : Graph :=
  List.ofFn (fun u=>List.ofFn (E u))

def storeCode {n : ℕ} (P : FiniteDirectedBFS.Paths n) : Store :=
  List.ofFn (fun u=>(P u).map (List.map Fin.val))

lemma range_eq_map (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

lemma adjacent_graphCode {n : ℕ} (E : Fin n → Fin n → Bool) (u v : Fin n) :
    adjacent (graphCode E) u.val v.val=E u v := by
  simp [adjacent,graphCode,List.getD_eq_getElem?_getD,u.isLt,v.isLt]

lemma lookup_storeCode {n : ℕ} (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    lookup (storeCode P) v.val=(P v).map (List.map Fin.val) := by
  simp [lookup,storeCode,List.getD_eq_getElem?_getD,v.isLt]

lemma predecessor_code {n : ℕ} (E : Fin n → Fin n → Bool)
    (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    predecessor (graphCode E) (storeCode P) v.val=
      (FiniteDirectedBFS.predecessor E P v).map Fin.val := by
  have hlen : (graphCode E).length=n := by simp [graphCode]
  simp only [predecessor,hlen,range_eq_map,List.find?_map]
  congr 1
  apply congrArg (fun f=>(List.finRange n).find? f)
  funext u
  simp only [Function.comp_apply,lookup_storeCode,Option.isSome_map,adjacent_graphCode]

lemma roundRow_code {n : ℕ} (E : Fin n → Fin n → Bool)
    (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    roundRow (graphCode E) (storeCode P) v.val=
      (FiniteDirectedBFS.round E P v).map (List.map Fin.val) := by
  simp only [roundRow,lookup_storeCode,predecessor_code,FiniteDirectedBFS.round]
  cases hp : P v with
  | some xs => rfl
  | none =>
    cases hu : FiniteDirectedBFS.predecessor E P v with
    | none => rfl
    | some u =>
      simp only [Option.map_some,Option.bind_some,lookup_storeCode]
      cases hpu : P u <;> simp [List.map_append]

lemma round_code {n : ℕ} (E : Fin n → Fin n → Bool) (P : FiniteDirectedBFS.Paths n) :
    round (graphCode E) (storeCode P)=storeCode (FiniteDirectedBFS.round E P) := by
  simp only [round,graphCode,List.length_ofFn,range_eq_map,List.map_map]
  rw [←List.ofFn_eq_map]
  unfold storeCode
  apply congrArg List.ofFn
  funext v
  exact roundRow_code E P v

lemma initial_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) :
    initial (graphCode E) s.val=storeCode (FiniteDirectedBFS.paths E s 0) := by
  simp only [initial,graphCode,List.length_ofFn,range_eq_map,List.map_map]
  rw [←List.ofFn_eq_map]
  unfold storeCode
  apply congrArg List.ofFn
  funext v
  by_cases h : v=s
  · subst v; simp [FiniteDirectedBFS.paths]
  · have hv : v.val≠s.val := fun he=>h (Fin.ext he)
    simp [Function.comp_apply,FiniteDirectedBFS.paths,h,hv]

lemma fold_round_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) (k : ℕ) :
    (List.range k).foldl (fun P _=>round (graphCode E) P) (initial (graphCode E) s.val)=
      storeCode (FiniteDirectedBFS.paths E s k) := by
  induction k with
  | zero => simpa using initial_code E s
  | succ k ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,round_code,FiniteDirectedBFS.paths]

theorem run_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) :
    run (graphCode E) s.val=storeCode (FiniteDirectedBFS.paths E s n) := by
  simpa only [run,graphCode,List.length_ofFn] using fold_round_code E s n

theorem search_code {n : ℕ} (E : Fin n → Fin n → Bool) (s t : Fin n) :
    search (graphCode E) s.val t.val=
      (FiniteDirectedBFS.paths E s n t).map (List.map Fin.val) := by
  rw [search,run_code,lookup_storeCode]

end ContingencyTables.DirectedBFSCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionLabelMetadataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering each paired label's cell and capacity

The multiplicities come from the actual bounded profile blocks. A
large numeric capacity never causes an allocation beyond the supplied
profile code. On a canonical code, the resulting order is exactly the
copy order used by the initializer and arithmetic proposals.
-/

namespace ContingencyTables.CompanionLabelMetadataProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open PairedProfileProgram PairedFactorialProgram

abbrev Input := PairedProfileProgram.Input

def indices (z : ℕ × List ℕ) : List ℕ := List.range (pairCount z.2)

def labelRow (z : ℕ × List ℕ) : List (ℕ × ℕ) :=
  (indices z).map (fun _ => (z.1,pairCount z.2))

def rowInput (z : Input × ℕ) : ℕ × List ℕ :=
  (z.2,(rows z.1).getD z.2 [])

def indexedRow (z : Input × ℕ) : List (ℕ × ℕ) := labelRow (rowInput z)

def output (z : Input) : List (ℕ × ℕ) :=
  ((NaturalBlockProgram.indices z).map (fun i => indexedRow (z,i))).flatten
end ContingencyTables.CompanionLabelMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

abbrev Metadata := ℕ × ℕ

def numerator (z : Metadata × Metadata) : ℕ := 6*(z.1.2+1)

def denominator (z : Metadata × Metadata) : ℕ := z.2.2+2

def sameCell (z : Metadata × Metadata) : Bool := decide (z.1.1=z.2.1)

def entry (z : Metadata × Metadata) : TreeFraction.Fraction :=
  if sameCell z then (6,1) else TreeFraction.normalize (numerator z,denominator z)

def row (z : List Metadata × Metadata) : List TreeFraction.Fraction :=
  z.1.map (fun b => entry (z.2,b))

def matrix (xs : List Metadata) : FractionMatrix := xs.map (fun a => row (xs,a))

def output (z : PairedProfileProgram.Input) : FractionMatrix :=
  matrix (CompanionLabelMetadataProgram.output z)

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionRationalUpdates TwoLiftStates
open scoped Classical

variable {q : ℕ} (b : Fin q → ℕ)

def metadataAt (i : Fin (CanonicalInitialEncoding.copyOrder b).length) : Metadata :=
  ((PairedCatalogProgram.labelOrder b i).1.val,b (PairedCatalogProgram.labelOrder b i).1)

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def initialEntries (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) : TreeFraction.Fraction :=
  entry (metadataAt (capacities A) i,metadataAt (capacities A) j)

end
end ContingencyTables.CompanionInitialMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

abbrev OffsetWidthData := ExponentData×ℕ

def offsetLength (z : OffsetWidthData×(ℕ×ℕ)) : ℕ :=
  Nat.clog 2 (gridCellWidth (z.1.1,z.2)+1)+4*(z.1.2+z.1.1.2)

def freeCells (z : OffsetWidthData) : List (ℕ×ℕ) :=
  cellPairs (z.1.1.1.1.tail,z.1.1.1.2.tail)

def offsetLengths (z : OffsetWidthData) : List ℕ :=
  (freeCells z).map (fun ij => offsetLength (z,ij))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program computing a component root

The graph is supplied by adjacency lists. The program makes one growth
round per stored vertex, then minimizes the reached indices. No loop
depends on the numeric size of an index or of an edge capacity.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev GraphCode := List (List ℕ)
abbrev SearchState := GraphCode×List ℕ
abbrev Input := GraphCode×ℕ

def indices (rows : GraphCode) : List ℕ := List.range rows.length

def neighborHit (z : List ℕ×List ℕ) : Bool :=
  z.2.any (fun a => decide (a∈z.1))

def growTest (z : SearchState×ℕ) : Bool :=
  decide (z.2∈z.1.2) || neighborHit (z.1.2,z.1.1.getD z.2 [])

def grow (z : SearchState) : List ℕ :=
  (indices z.1).filter (fun a => growTest (z,a))

def advance (z : List ℕ×SearchState) : SearchState :=
  (z.2.1,grow z.2)

def prepare (z : Input) : GraphCode×SearchState := (z.1,(z.1,[z.2]))

def run (z : Input) : SearchState :=
  z.1.foldl (fun s row => advance (row,s)) (z.1,[z.2])

def reached (z : Input) : List ℕ := (run z).2

def rootCode (z : Input) : ℕ :=
  (reached z).foldl (fun b a => min a b) z.1.length

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRootSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correctness of the finite component-root program

The stored adjacency list is identified with the given finite graph.
Each list growth round is the proved finite reachability growth, and
the final binary minimum is the least vertex of the actual component.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def adjacencyRow (b : Fin n) : List ℕ :=
  ((List.finRange n).filter (fun a => decide (G.Adj a b))).map Fin.val

def graphCode : GraphCode := List.ofFn (adjacencyRow G)

lemma graphCode_length : (graphCode G).length=n := List.length_ofFn

lemma adjacencyRow_mem (b : Fin n) (a : ℕ) :
    a∈adjacencyRow G b ↔ ∃ u : Fin n,u.val=a ∧ G.Adj u b := by
  simp only [adjacencyRow,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u,hu,ha⟩
    exact ⟨u,ha,hu⟩
  · rintro ⟨u,ha,hu⟩
    exact ⟨u,hu,ha⟩

lemma fold_advance (steps : List (List ℕ)) (rows : GraphCode) (s : List ℕ) :
    (steps.foldl (fun s row => advance (row,s)) (rows,s)).2=
      (fun s => grow (rows,s))^[steps.length] s := by
  induction steps generalizing s with
  | nil => rfl
  | cons row steps ih =>
    simp only [List.foldl_cons,List.length_cons]
    change (steps.foldl (fun s row => advance (row,s)) (rows,grow (rows,s))).2=_
    rw [ih,Function.iterate_succ_apply]

lemma reached_eq_iterate (v : Fin n) :
    reached (graphCode G,v.val)=(fun s => grow (graphCode G,s))^[n] [v.val] := by
  unfold reached run
  rw [fold_advance,graphCode_length]

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphCutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the selected root-away cut

Deletion filters the stored adjacency rows. The endpoint and cut side
are then computed by the bounded reachability program.
-/

namespace ContingencyTables.FiniteGraphCutProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram

abbrev EdgeInput := GraphCode×(ℕ×ℕ)
abbrev KeepInput := ((ℕ×ℕ)×ℕ)×ℕ

def keep (z : KeepInput) : Bool :=
  if z.1.2=z.1.1.1 then decide (z.2≠z.1.1.2)
  else if z.1.2=z.1.1.2 then decide (z.2≠z.1.1.1) else true

def deleteRow (z : EdgeInput×ℕ) : List ℕ :=
  (z.1.1.getD z.2 []).filter (fun a => keep ((z.1.2,z.2),a))

def deleteGraph (z : EdgeInput) : GraphCode :=
  (indices z.1).map (fun i => deleteRow (z,i))

def reachableCode (z : Input×ℕ) : Bool := decide (z.2∈reached z.1)

abbrev CutInput := EdgeInput×ℕ

def awayCode (z : CutInput) : ℕ :=
  if reachableCode ((deleteGraph z.1,z.1.2.1),z.2) then z.1.2.2 else z.1.2.1

def cutCode (z : CutInput×ℕ) : Bool :=
  reachableCode ((deleteGraph z.1.1,awayCode z.1),z.2)

def canonicalCutCode (z : EdgeInput×ℕ) : Bool :=
  cutCode ((z.1,rootCode (z.1.1,z.1.2.1)),z.2)

end ContingencyTables.FiniteGraphCutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

abbrev Input := (EdgeInput×(ℕ×ℕ))×(ℕ×ℕ)

def bit (b : Bool) : ℕ := if b then 1 else 0

def adjacent (z : GraphCode×(ℕ×ℕ)) : Bool := decide (z.2.2 ∈ z.1.getD z.2.1 [])

def freeTest (z : Input) : Bool :=
  decide (z.2.1 ≤ z.2.2) && !adjacent (z.1.1.1,z.1.2)

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

abbrev TermInput := RootedCoefficientProgram.Input×ℕ

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

end ContingencyTables.RootedForestDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCellDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

abbrev Matrices := (MatrixCode×MatrixCode)×(MatrixCode×MatrixCode)
abbrev Frame := (EdgeInput×ℕ)×(List ℕ×List ℕ)
abbrev Input := Frame×Matrices
abbrev CellInput := Input×(ℕ×ℕ)

def values (z : Matrices×(ℕ×ℕ)) : (ℕ×ℕ)×(ℕ×ℕ) :=
  ((matrixEntry (z.1.1.1,z.2),matrixEntry (z.1.1.2,z.2)),
    (matrixEntry (z.1.2.1,z.2),matrixEntry (z.1.2.2,z.2)))

def endpoints (z : Frame×(ℕ×ℕ)) : ℕ×ℕ :=
  (z.2.1,z.1.2.1.length+z.2.2)

def cellValues (z : CellInput) : (ℕ×ℕ)×(ℕ×ℕ) := values (z.1.2,z.2)

def coefficientInput (z : CellInput) : RootedCoefficientProgram.Input :=
  ((z.1.1.1.1,endpoints (z.1.1,z.2)),(z.1.1.1.2,(cellValues z).1.1))

def baselineCell (z : Frame) : ℕ×ℕ :=
  (z.1.1.2.1,z.1.1.2.2-z.2.1.length)

open CompanionFactorialApplication RootedCompletion

end ContingencyTables.RootedCellDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the tree and free-cell catalogs

Both catalogs scan the rectangular cell array. A free cell is selected
by its binary capacity and absence from the supplied forest graph; a
tree cell is selected by graph adjacency. Empty forests need no chosen
edge and are handled by the same program.
-/

namespace ContingencyTables.RootedForestCatalog

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open RootedCoefficientProgram FiniteGraphRootProgram
open scoped Classical

abbrev Data := ((GraphCode×ℕ)×(List ℕ×List ℕ))×MatrixCode
abbrev Item := Data×(ℕ×ℕ)

def edge (z : Item) : GraphCode×(ℕ×ℕ) :=
  (z.1.1.1.1,(z.2.1,z.1.1.2.1.length+z.2.2))

def treeTest (z : Item) : Bool := adjacent (edge z)

def largeTest (z : Item) : Bool :=
  decide (z.1.1.1.2 ≤ matrixEntry (z.1.2,z.2))

def freeTest (z : Item) : Bool := largeTest z && !treeTest z

def selectedTest (z : (Data×Bool)×(ℕ×ℕ)) : Bool :=
  if z.1.2 then treeTest (z.1.1,z.2) else freeTest (z.1.1,z.2)

def catalog (z : Data×Bool) : List (ℕ×ℕ) :=
  (cellPairs z.1.1.2).filter (fun a => selectedTest (z,a))

lemma catalog_nodup (z : Data×Bool) : (catalog z).Nodup :=
  (cellPairs_nodup z.1.1.2.1 z.1.1.2.2).filter _

open CompanionFactorialApplication ForestAssignmentSplit GraphCompletionCounts

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) : Data :=
  (((graphCode (A.T.comap finSumFinEquiv.symm),A.W),
    (List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat))),matrixCode A.b)

def Selected {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) (a : Fin m×Fin n) : Prop :=
  if tree then A.T.Adj (.inl a.1) (.inr a.2)
  else A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)

abbrev Cell {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) :=
  {a : Fin m×Fin n // Selected A tree a}

end ContingencyTables.RootedForestCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialStoredProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal initial count and stored multiplier matrix

The integer count is the product of the free-cell ranges and the small-cell
ranges. Both lists come from the executed forest and cell catalogs.
-/
namespace ContingencyTables.CompanionInitialStoredProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms

abbrev Input := RootedForestCatalog.Data × PairedProfileProgram.Input

def rangeAt (z : RootedForestCatalog.Data×(ℕ×ℕ)) : ℕ := matrixEntry (z.1.2,z.2)+1

def freeRanges (d : RootedForestCatalog.Data) : List ℕ :=
  (RootedForestCatalog.catalog (d,false)).map (fun ij => rangeAt (d,ij))

def freeProduct (d : RootedForestCatalog.Data) : ℕ := (freeRanges d).prod

def smallProduct (xs : List ℕ) : ℕ := (xs.map Nat.succ).prod

def total (z : Input) : TreeFraction.Fraction :=
  (freeProduct z.1*smallProduct z.2.1,1)

def output (z : Input) : CompanionMultiplierMatrixProgram.FractionMatrix×TreeFraction.Fraction :=
  (CompanionInitialMatrixProgram.output z.2,total z)

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial ForestAssignmentSplit
open CompanionArithmeticProposal
open scoped BigOperators Classical
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def data (S : Set (Labels A×Bool)) : Input :=
  (RootedForestCatalog.data A,(List.ofFn (capacities A),encodeSet (coordinateOrder A) S))

end
end ContingencyTables.CompanionInitialStoredProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

/-- The integer form of the manuscript's observable coefficient. -/
def observable (p W : ℕ) : ℕ :=
  10*p^4*(9*(p*(1+8*p*W^4))+2*(8+32*p*W^6))

def observationCoefficient (p W : ℕ) : ℕ := 32000*p^8*observable p W

def noiseCoefficient (H tau N n : ℕ) : ℕ := 8*(N+1)+8*H*tau*(n+1)

def precision (H tau N n : ℕ) (eta : ℚ) : ℕ :=
  1024*(H+1)*noiseCoefficient H tau N n+⌈1/eta⌉₊+1

def noise (H tau N n : ℕ) (eta : ℚ) : ℚ :=
  1/(precision H tau N n eta:ℚ)

def initialPrecision (H : ℕ) : ℕ := 2048*(H+1)

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

lemma natCeil_ratCast (q : ℚ) : ⌈(q:ℝ)⌉₊=⌈q⌉₊ := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil q
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil (q:ℝ)

def precision (epsilon : ℚ) : ℕ := Nat.clog 2 ⌈1/epsilon⌉₊
def allowance (L d : ℕ) (epsilon : ℚ) : ℕ := 20*(L+d+precision epsilon+1)
def coefficient (L d : ℕ) (epsilon : ℚ) : ℕ :=
  ⌈(2048:ℚ)*d*(allowance L d epsilon)^2/epsilon⌉₊

lemma precision_eq (epsilon : ℚ) (he : 0 < epsilon) :
    precision epsilon=CompanionTerminalParameters.precision (epsilon:ℝ) := by
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he
  have hequiv (n : ℕ) :
      CompanionTerminalParameters.precision (epsilon:ℝ) ≤ n ↔ precision epsilon ≤ n := by
    rw [CompanionTerminalParameters.precision,Nat.ceil_le,precision,
      Nat.clog_le_iff_le_pow (by decide : 1 < (2:ℕ)),Nat.ceil_le]
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (by positivity),Real.rpow_natCast]
    exact_mod_cast (Iff.rfl : (1/epsilon:ℚ) ≤ (2:ℚ)^n ↔ (1/epsilon:ℚ) ≤ (2:ℚ)^n)
  exact le_antisymm ((hequiv _).mp le_rfl) ((hequiv _).mpr le_rfl)

lemma allowance_eq (L d : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    allowance L d epsilon=CompanionTerminalParameters.allowance L d (epsilon:ℝ) := by
  rw [allowance,precision_eq epsilon he,CompanionTerminalParameters.allowance]

lemma coefficient_eq (L d : ℕ) (hd : 1 ≤ d) (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient L d epsilon=CompanionTerminalParameters.coefficient L d (epsilon:ℝ) := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have heR : (epsilon:ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have ha : (CompanionTerminalParameters.allowance L d (epsilon:ℝ):ℝ) ≠ 0 := by
    exact_mod_cast (CompanionTerminalParameters.allowance_positive L d (epsilon:ℝ)).ne'
  have hratio : (4:ℝ)*CompanionTerminalParameters.allowance L d (epsilon:ℝ)/
      CompanionTerminalParameters.gamma L d (epsilon:ℝ)=
      ((2048:ℚ)*d*(allowance L d epsilon)^2/epsilon:ℚ) := by
    rw [allowance_eq L d epsilon he]
    simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow]
    unfold CompanionTerminalParameters.gamma
    field_simp [hdR,heR,ha]
    ring
  rw [CompanionTerminalParameters.coefficient,hratio,natCeil_ratCast]
  rfl

variable {I J : Type} [Fintype I] [Fintype J]

lemma coefficient_pos (L d : ℕ) (hd : 1 ≤ d) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < coefficient L d epsilon := by
  rw [coefficient_eq L d hd epsilon he]
  exact CompanionTerminalParameters.coefficient_positive L d (epsilon:ℝ) hd (by exact_mod_cast he)

end
end ContingencyTables.CountingTerminalSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def ceilQuotient (z : ℕ×ℕ) : ℕ := (z.1+z.2-1)/z.2

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Fraction := TreeFraction.Fraction

def ceiling (e : Fraction) : ℕ := OffsetCountPrograms.ceilQuotient e

def natural (n : ℕ) : Fraction := (n,1)

/-- Phase index, relative tolerance, and failure allowance. -/
abbrev SampleInput := ℕ×(Fraction×Fraction)
def sampleBase (z : SampleInput) : Fraction := natural (65536*(z.1+1))

def sampleDenominator (z : SampleInput) : Fraction :=
  TreeFraction.mul (z.2.2,TreeFraction.mul (z.2.1,z.2.1))

def sampleRatio (z : SampleInput) : Fraction := TreeFraction.div (sampleBase z,sampleDenominator z)

def sampleCount (z : SampleInput) : ℕ := ceiling (sampleRatio z)

/-- Ambient dimension and requested relative accuracy. -/
abbrev OffsetInput := ℕ×Fraction
def offsetBase (z : OffsetInput) : Fraction := natural (4096*z.1)

def offsetRatio (z : OffsetInput) : Fraction := TreeFraction.div (offsetBase z,z.2)

def offsetAccuracy (z : OffsetInput) : ℕ := ceiling (offsetRatio z)


/-- The natural mixing factor and the natural height-plus-grid allowance,
followed by the rational per-call accuracy. -/
abbrev TimeInput := (ℕ×ℕ)×Fraction

def timeBase (z : TimeInput) : Fraction := natural (z.1.1*z.1.2)

def timeNumerator (z : TimeInput) : Fraction := natural (16*z.1.1)

def timeExtra (z : TimeInput) : Fraction := TreeFraction.div (timeNumerator z,z.2)

def timeTotal (z : TimeInput) : Fraction := TreeFraction.add (timeBase z,timeExtra z)

def oracleTime (z : TimeInput) : ℕ := ceiling (timeTotal z)

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

inductive Expr where
  | input : ℕ → Expr
  | number : ℕ → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

def Expr.eval : Expr → List ℕ → ℕ
  | .input i, xs => xs.getD i 0
  | .number n, _ => n
  | .plus a b, xs => a.eval xs+b.eval xs
  | .times a b, xs => a.eval xs*b.eval xs

def Expr.pow (a : Expr) : ℕ → Expr
  | 0 => .number 1
  | n+1 => .times (a.pow n) a


instance instOfNatExpr (n : ℕ) : OfNat Expr n := ⟨.number n⟩
instance instAddExpr : Add Expr := ⟨.plus⟩
instance instMulExpr : Mul Expr := ⟨.times⟩
instance instPowExprNat : Pow Expr ℕ := ⟨Expr.pow⟩

@[simp] lemma Expr.eval_add (a b : Expr) (xs : List ℕ) :
    (a+b).eval xs=a.eval xs+b.eval xs := rfl
@[simp] lemma Expr.eval_mul (a b : Expr) (xs : List ℕ) :
    (a*b).eval xs=a.eval xs*b.eval xs := rfl
@[simp] lemma Expr.eval_ofNat (n : ℕ) (xs : List ℕ) :
    (OfNat.ofNat n : Expr).eval xs=n := rfl


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

/-- Field order: label count, cutoff, phase count, restart time,
observation count, return cap, capacity-bit allowance. -/
def p : Expr := .input 0
def w : Expr := .input 1
def h : Expr := .input 2
def tau : Expr := .input 3
def observations : Expr := .input 4
def returns : Expr := .input 5

def observable : Expr := 10*p^4*(9*(p*(1+8*p*w^4))+2*(8+32*p*w^6))
def observationNumerator : Expr := 1024*(h+1)*(32000*p^8*observable)
def precisionBase : Expr := 1024*(h+1)*(8*(observations+1)+8*h*tau*(returns+1))+1
def initialPrecision : Expr := 2048*(h+1)

end ContingencyTables.CountingPhaseScalarProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

abbrev Input := List ℕ × Fraction

def scalar (e : Expr) (z : Input) : ℕ := e.eval z.1

def scalarFraction (e : Expr) (z : Input) : Fraction := natural (scalar e z)

def toleranceDenominator : Expr := 800*(CountingPhaseScalarProgram.h+1)
def tolerance (z : Input) : Fraction := TreeFraction.div (z.2,scalarFraction toleranceDenominator z)

def toleranceSquare (z : Input) : Fraction := TreeFraction.mul (tolerance z,tolerance z)

def observationRatio (z : Input) : Fraction :=
  TreeFraction.div (scalarFraction CountingPhaseScalarProgram.observationNumerator z,
    toleranceSquare z)

def observations (z : Input) : ℕ := ceiling (observationRatio z)+1

def reciprocalTolerance (z : Input) : Fraction := TreeFraction.div ((1,1),tolerance z)

def reciprocalCeiling (z : Input) : ℕ := ceiling (reciprocalTolerance z)

def precision (z : Input) : ℕ := scalar CountingPhaseScalarProgram.precisionBase z+reciprocalCeiling z

def noise (z : Input) : Fraction := (1,precision z)

end ContingencyTables.CountingPhaseParametersProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixSubtractProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entrywise natural subtraction on a supplied matrix shape -/

namespace ContingencyTables.MatrixSubtractProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Input := MatrixCode × MatrixCode
abbrev RowInput := Input × ℕ

def entry (z : RowInput × ℕ) : ℕ :=
  matrixEntry (z.1.1.1,(z.1.2,z.2))-matrixEntry (z.1.1.2,(z.1.2,z.2))

def sourceRow (z : RowInput) : List ℕ := z.1.1.getD z.2 []

def columns (z : RowInput) : List ℕ := List.range (sourceRow z).length

def row (z : RowInput) : List ℕ := (columns z).map (fun j => entry (z,j))

def indices (z : Input) : List ℕ := List.range z.1.length

def matrix (z : Input) : MatrixCode := (indices z).map (fun i => row (z,i))

end ContingencyTables.MatrixSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SparseViewMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materializing a sparse retained-cell view in a rectangular matrix -/

namespace ContingencyTables.SparseViewMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial ProfilePrograms DensePrograms

abbrev Input := (List ℕ × List ℕ) × (List (ℕ × ℕ) × List ℕ)
abbrev RowInput := Input × ℕ

def entry (z : RowInput × ℕ) : ℕ := lookupView (z.1.1.2,(z.1.2,z.2))

def columns (z : RowInput) : List ℕ := List.range z.1.1.2.length

def row (z : RowInput) : List ℕ := (columns z).map (fun j => entry (z,j))

def rowIndices (z : Input) : List ℕ := List.range z.1.1.length

def matrix (z : Input) : MatrixCode := (rowIndices z).map (fun i => row (z,i))

end ContingencyTables.SparseViewMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

abbrev Record := ℕ×(ℕ×ℕ)
abbrev Input := ℕ×List Record

def positiveTerm (z : ℕ×Record) : ℕ := if z.1=z.2.1 then z.2.2.1 else 0
def negativeTerm (z : ℕ×Record) : ℕ := if z.1=z.2.1 then z.2.2.2 else 0

def parts (z : Input) : ℕ×ℕ :=
  ((z.2.map (fun r => positiveTerm (z.1,r))).sum,
    (z.2.map (fun r => negativeTerm (z.1,r))).sum)

def absoluteDifference (z : ℕ×ℕ) : ℕ := z.1-z.2+(z.2-z.1)

def component (z : Input) : ℕ := absoluteDifference (parts z)

def total (rs : List Record) : ℕ :=
  ((List.range rs.length).map (fun a => component (a,rs))).sum

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every root label before summing its signed demand

The input contains an adjacency list and one positive/negative demand
pair per vertex. The polynomial program computes the root labels itself.
-/

namespace ContingencyTables.RootedComponentCode

open MatchingFPRAS.TreeTyped Polynomial
open RootedCompletion RootedComponentProgram FiniteGraphRootProgram
open scoped BigOperators Classical

abbrev Input := GraphCode×List (ℕ×ℕ)

def entry (z : Input×ℕ) : Record :=
  (rootCode (z.1.1,z.2),z.1.2.getD z.2 (0,0))

def labels (z : Input) : List Record :=
  (List.range z.2.length).map (fun i => entry (z,i))

def count (z : Input) : ℕ := total (labels z)

open CompanionFactorialApplication

end ContingencyTables.RootedComponentCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram
open scoped BigOperators Classical

abbrev Input := RootedForestCatalog.Data×(MatrixCode×(MatrixCode×MatrixCode))
abbrev TermInput := (Input×ℕ)×(ℕ×ℕ)

def values (z : TermInput) : (ℕ×ℕ)×(ℕ×ℕ) :=
  RootedCellDataProgram.values (((z.1.1.1.2,z.1.1.2.1),z.1.1.2.2),z.2)

def retainedTest (z : TermInput) : Bool :=
  !RootedForestCatalog.largeTest (z.1.1.1,z.2)

def rowTest (z : TermInput) : Bool := decide (z.1.2=z.2.1)

def columnTest (z : TermInput) : Bool :=
  decide (z.1.2=z.1.1.1.1.2.1.length+z.2.2)

def vertexCount (z : Input) : ℕ := z.1.1.2.1.length+z.1.1.2.2.length

def vertices (z : Input) : List ℕ := List.range (vertexCount z)

open CompanionFactorialApplication RootedCompletion

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) : Input :=
  (RootedForestCatalog.data A,
    (matrixCode (fun i j => (A.X i j).toNat),(matrixCode x,matrixCode q)))

end ContingencyTables.RootedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Context := RootedDemandProgram.Input
abbrev Input := Context×(ℕ×ℕ)

def metadata (z : Input) : RootedForestCatalog.Data := z.1.1

def edge (z : Input) : FiniteGraphCutProgram.EdgeInput :=
  RootedForestCatalog.edge (metadata z,z.2)

def treeInput (z : Input) : RootedCellDataProgram.Input :=
  (((edge z,(metadata z).1.1.2),(metadata z).1.2),
    (((metadata z).2,z.1.2.1),z.1.2.2))

abbrev TermBundle := (RootedCellDataProgram.Input×List (ℕ×ℕ))×List ℕ

def termAt (z : TermBundle×ℕ) : RootedForestDataProgram.TermInput :=
  (RootedCellDataProgram.coefficientInput
    (z.1.1.1,z.1.1.2.getD z.2 (0,0)),z.1.2.getD z.2 0)

def indices (xs : List (ℕ×ℕ)) : List ℕ := List.range xs.length

def terms (z : TermBundle) : List RootedForestDataProgram.TermInput :=
  (indices z.1.2).map (fun k => termAt (z,k))

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedTreeInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestPrepareProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Context := RootedDemandProgram.Input
abbrev TreeInput := ((Context×ℕ)×List ℕ)×(ℕ×ℕ)
abbrev Input := ((ℕ×ℕ)×Context)×List ℕ

def treeFrame (z : TreeInput) : RootedCellDataProgram.Input :=
  RootedTreeInputProgram.treeInput (z.1.1.1,z.2)

def freeCells (z : TreeInput) : List (ℕ×ℕ) :=
  RootedForestCatalog.catalog (z.1.1.1.1,false)

def widthCapacity (z : TreeInput) : ℕ×ℕ :=
  (z.1.1.2,matrixEntry (z.1.1.1.1.2,z.2))

def treeBundle (z : Input) : (Context×ℕ)×List ℕ := ((z.1.2,z.1.1.2),z.2)

def treeCells (z : Input) : List (ℕ×ℕ) :=
  RootedForestCatalog.catalog (z.1.2.1,true)

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedForestPrepareProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

abbrev Parameters := (ℕ×ℕ)×(ℕ×ℕ)
abbrev Input := Parameters×(RootedDemandProgram.Input×List ℕ)

def squareDimension (z : Parameters) : ℕ := z.1.1*z.1.1

def scaledSquare (z : Parameters) : ℕ := z.2.1*squareDimension z

def width (z : Parameters) : ℕ := 16*scaledSquare z

def baseHeight (z : Parameters) : ℕ := 10*scaledSquare z

def height (z : Parameters) : ℕ := baseHeight z*(z.1.2+1)

def forestInput (z : Input) : RootedForestPrepareProgram.Input :=
  (((z.1.2.1,width z.1),z.2.1),z.2.2)

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

abbrev freeCount (A : Instance (Fin m) (Fin n)) :=
  (RootedForestCatalog.catalog (RootedForestCatalog.data A,false)).length

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWalkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an oracle walk

The immutable graph and cell arrays are kept separately from the grid
coordinates. A coordinate changes by at most one per transition, which
bounds every accumulator reached by the binary list fold.
-/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial
open scoped Classical

abbrev Frame := ℕ×(RootedPenaltyEvaluateProgram.Parameters×RootedDemandProgram.Input)
abbrev State := Frame×List ℕ

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess

end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := RootedDemandProgram.Input × List ℕ

def cellInput (d : RootedForestCatalog.Data) : CompanionCellCatalog.Input :=
  ((d.1.2,d.2),d.1.1.2)

def cells (z : Input) : CompanionCellCatalog.Input := cellInput z.1.1

def counts (z : Input) : List (ℕ × ℕ) :=
  PairedProfileProgram.profileRows (CompanionCellCatalog.capacities (cells z),z.2)

def sideEntry (z : Bool × (ℕ × ℕ)) : ℕ := if z.1 then z.2.2 else z.2.1

def values (z : Input × Bool) : List ℕ := (counts z.1).map (fun p => sideEntry (z.2,p))

def viewInput (z : Input × Bool) : SparseViewMatrixProgram.Input :=
  (z.1.1.1.1.2,(CompanionCellCatalog.catalog (cells z.1),values z))

def viewMatrix (z : Input × Bool) : MatrixCode := SparseViewMatrixProgram.matrix (viewInput z)

def complement (z : Input) : MatrixCode :=
  MatrixSubtractProgram.matrix (z.1.1.2,viewMatrix (z,true))

def output (z : Input) : RootedDemandProgram.Input :=
  (z.1.1,(z.1.2.1,(viewMatrix (z,false),complement z)))
end ContingencyTables.PairedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

abbrev State := Fraction × (List Fraction × List Fraction)

def step (z : Fraction × State) : State :=
  (z.2.1,(z.1::z.2.2.1,
    if TreeFraction.less (z.1,z.2.1) then z.1::z.2.2.2 else z.2.1::z.1::z.2.2.1))

def insert (z : Fraction × List Fraction) : List Fraction :=
  (z.2.reverse.foldl (fun s x => step (x,s)) (z.1,([],[z.1]))).2.2

def sort (xs : List Fraction) : List Fraction :=
  xs.reverse.foldl (fun s x => insert (x,s)) []

def median (xs : List Fraction) : Fraction :=
  (sort (xs.map TreeFraction.normalize)).getD (xs.length/2) (0,1)

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinVectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

lemma intervalSize_le (K N beta : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K) :
    CompanionOracleDensity.intervalSize K N beta ≤ N := by
  have he := FairBits.fiber_card hK hN hb
  have hc : (FairBits.fiber K N beta).card ≤ N :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range N)
  simpa only [he,CompanionOracleDensity.intervalSize] using hc

end ContingencyTables.BinVectorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinFramesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the actual bin draws from the computed free-cell catalog

Only the capacity matrix, catalog metadata, grid coordinate list and
numeric sampling parameters are supplied. The program computes each
full range and bin index before invoking the proved vector draw.
-/

namespace ContingencyTables.RootedBinFramesProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

/-- `(K,(precision,dimension))` and the catalog metadata/current bin. -/
abbrev Input := (ℕ×(ℕ×ℕ))×(RootedForestCatalog.Data×List ℕ)

def catalog (z : Input) : List (ℕ×ℕ) := RootedForestCatalog.catalog (z.2.1,false)

def cell (z : Input×ℕ) : ℕ×ℕ := (catalog z.1).getD z.2 (0,0)

def rangeSize (z : Input×ℕ) : ℕ := matrixEntry (z.1.2.1.2,cell z)+1

def coordinate (z : Input×ℕ) : ℕ := z.1.2.2.getD z.2 0

def indices (z : Input) : List ℕ := List.range (catalog z).length

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

end ContingencyTables.RootedBinFramesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer propagation tabulates adaptive finite laws without random tapes -/

namespace ContingencyTables.IntegerPropagation
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (B : A → A → ℕ) (Q : ℕ)

def numerators (start : A) : ℕ → A → ℕ
  | 0,y => if y=start then 1 else 0
  | n+1,y => ∑ x,numerators start n x*B x y

end ContingencyTables.IntegerPropagation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Missing coordinates are zero. The loop runs over the vector's length. -/
def dot (z : List ℕ×List ℕ) : ℕ :=
  ((List.range z.1.length).map (fun i => z.1.getD i 0*z.2.getD i 0)).sum

/-- A matrix is stored by columns, so each new coordinate is one dot product. -/
def propagate (z : List (List ℕ)×List ℕ) : List ℕ :=
  z.1.map (fun column => dot (z.2,column))

lemma range_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum=∑ i : Fin n,f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ,Fin.sum_univ_castSucc,ih]
    rfl

lemma dot_ofFn {n : ℕ} (v b : Fin n → ℕ) :
    dot (List.ofFn v,List.ofFn b)=∑ i,v i*b i := by
  unfold dot
  rw [List.length_ofFn,range_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD,i.isLt]

lemma propagate_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (v : Fin n → ℕ) :
    propagate (List.ofFn (fun y => List.ofFn (fun x => B x y)),List.ofFn v)=
      List.ofFn (fun y => ∑ x,v x*B x y) := by
  simp only [propagate,List.map_ofFn,Function.comp_def,dot_ofFn]

/-- One iteration retains the transition table unchanged. -/
def step (z : ℕ×(List (List ℕ)×List ℕ)) : List (List ℕ)×List ℕ :=
  (z.2.1,propagate z.2)

def iterate (z : ℕ×(List (List ℕ)×List ℕ)) : List ℕ :=
  (countDown step z.1 z.2).2

lemma iterate_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) (N : ℕ) :
    iterate (N,(List.ofFn (fun y => List.ofFn (fun x => B x y)),
      List.ofFn (fun x => if x=start then 1 else 0)))=
      List.ofFn (IntegerPropagation.numerators B start N) := by
  have hi (N : ℕ) (v : Fin n → ℕ) :
      countDown step N (List.ofFn (fun y => List.ofFn (fun x => B x y)),List.ofFn v)=
      (List.ofFn (fun y => List.ofFn (fun x => B x y)),
        List.ofFn ((fun v y => ∑ x,v x*B x y)^[N] v)) := by
    induction N generalizing v with
    | zero => rfl
    | succ N ih =>
      rw [countDown]
      change countDown step N (_,propagate (_,List.ofFn v))=_
      rw [propagate_ofFn,ih,Function.iterate_succ_apply]
  have hn (N : ℕ) : ((fun v y => ∑ x,v x*B x y)^[N]
      (fun x => if x=start then 1 else 0))=IntegerPropagation.numerators B start N := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply',ih]
      rfl
  unfold iterate
  rw [hi,hn]

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary powers with a polynomial bound in the exponent and input bits -/

namespace ContingencyTables.BinaryPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def setup (z : ℕ×ℕ) : ℕ×(List (List ℕ)×List ℕ) := (z.2,([[z.1]],[1]))

def power (z : ℕ×ℕ) : ℕ := (IntegerMatrixPrograms.iterate (setup z)).headD 0

theorem power_eq (a N : ℕ) : power (a,N)=a^N := by
  have hnum (n : ℕ) :
      IntegerPropagation.numerators (fun _ _ : Fin 1 => a) 0 n 0=a^n := by
    induction n with
    | zero => simp [IntegerPropagation.numerators]
    | succ n ih => simp [IntegerPropagation.numerators,ih,pow_succ]
  have hi:=IntegerMatrixPrograms.iterate_ofFn (fun _ _ : Fin 1 => a) 0 N
  have hs : (List.ofFn fun _ : Fin 1 => List.ofFn fun _ : Fin 1 => a)=[[a]] := by simp
  have hv : (List.ofFn fun x : Fin 1 => if x=0 then (1:ℕ) else 0)=[1] := by simp
  rw [hs,hv] at hi
  unfold power setup
  rw [hi]
  simpa using hnum N

end ContingencyTables.BinaryPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DyadicRootBisection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer implementation of the correction-root bisection

The two interval endpoints share one dyadic denominator. Every comparison
is an inequality between natural powers and products. This is the literal
integer algorithm to which the rational correction analysis is applied.
-/

namespace ContingencyTables.DyadicRootBisection

open MatchingFPRAS

abbrev State := (ℕ×ℕ)×ℕ

end ContingencyTables.DyadicRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def powerInput (z : ℕ×List Bool) : ℕ×ℕ := (z.1,z.2.length)

def markedPower (z : ℕ×List Bool) : ℕ := BinaryPowerPrograms.power (powerInput z)

abbrev Parameters := TreeFraction.Fraction×List Bool
abbrev State := Parameters×DyadicRootBisection.State

def mid (z : State) : ℕ := z.2.1.1+z.2.1.2

def twiceDenominator (z : State) : ℕ := 2*z.2.2

def leftProduct (z : State) : ℕ := markedPower (mid z,z.1.2)*z.1.1.2

def rightProduct (z : State) : ℕ := z.1.1.1*markedPower (twiceDenominator z,z.1.2)

def test (z : State) : Bool := decide (leftProduct z ≤ rightProduct z)

def next (z : State) : State :=
  (z.1,if test z then ((mid z,2*z.2.1.2),twiceDenominator z)
    else ((2*z.2.1.1,mid z),twiceDenominator z))

def advance (z : Bool×State) : State := next z.2

abbrev Input := Parameters×List Bool
def prepare (z : Input) : List Bool×State := (z.2,(z.1,((0,8),1)))

def execute (z : Input) : State := z.2.foldl (fun s a=>advance (a,s)) (z.1,((0,8),1))

def finish (z : State) : TreeFraction.Fraction :=
  TreeFraction.normalize (mid z,twiceDenominator z)

def output (z : Input) : TreeFraction.Fraction := finish (execute z)

end ContingencyTables.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CorrectionValueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary composition of the correction value

The input contains the computed grid exponent, phase ratio, point
penalty, population factor and two precision marker lists. Normalized
fraction multiplication supplies a positive denominator for the signed
exponent passed to the executed power approximation.
-/

namespace ContingencyTables.CorrectionValueProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Frame := (ℕ×TreeFraction.Fraction)×TreeFraction.Fraction

def weighted (z : Frame) : TreeFraction.Fraction := TreeFraction.mul (z.1.2,z.2)

abbrev Input := (Frame×TreeFraction.Fraction)×(List Bool×List Bool)

end ContingencyTables.CorrectionValueProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed selected-root correction

The stored grid point and sampled integer point share their literal
capacity, forest, baseline and small-view arrays.  The program computes
the grid exponent, point penalty and population factor before the
bounded rational power approximation.
-/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

abbrev State := RootedOracleWalkProgram.State
abbrev Input := (State×List ℕ)×(List Bool×List Bool)

end ContingencyTables.RootedCorrectionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

def proposalWidth (z : Frame) : ℕ := Nat.clog 2 (8*z.2.1.1.1)

def stepWidth (z : Frame) : ℕ := proposalWidth z+RootedPenaltyEvaluateProgram.height z.2.1

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev State := RootedOracleWalkProgram.State
abbrev Input := (State × ℕ) × ((List Bool × List Bool) × (List Bool × List Bool))

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

end ContingencyTables.RootedCorrectionSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an adjacent-parameter ratio sample

The exact ratio is either one or one half. The program compares the two
computed integer exponents and never materializes an exponential weight.
-/

namespace ContingencyTables.RootedRatioSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev SampleInput := RootedOracleWalkProgram.State×List Bool

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedCompletion
open scoped BigOperators

end ContingencyTables.RootedRatioSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed sample blocks and the product weight estimator

The lists contain the actual sample inputs and their disjoint finite
words. Each sample is evaluated by the checked binary program before
its average or product is formed.
-/

namespace ContingencyTables.RootedEstimatorBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev RatioBlock := List RootedRatioSampleProgram.SampleInput

end ContingencyTables.RootedEstimatorBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev State := RootedOracleWalkProgram.State
abbrev Schedule := (ℕ×ℕ)×((ℕ×ℕ)×ℕ)
abbrev Context := State×Schedule

def stepWidth (z : Context) : ℕ := RootedOracleWalkProgram.stepWidth z.1.1

def ratioWidth (z : Context) : ℕ := z.2.2.1.1*stepWidth z

def ratioBlockWidth (z : Context) : ℕ := z.2.1.2*ratioWidth z

def ratioBankWidth (z : Context) : ℕ := z.2.1.1*ratioBlockWidth z

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

def phase (z : State×ℕ) : State :=
  ((z.1.1.1,((z.1.1.2.1.1,(z.1.1.2.1.2.1,z.2)),z.1.1.2.2)),z.1.2)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLabelWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

def replaceState (z : RootedOracleWalkProgram.State × List ℕ) : RootedOracleWalkProgram.State :=
  ((z.1.1.1,(z.1.1.2.1,PairedDemandProgram.output (z.1.1.2.2,z.2))),z.1.2)
end ContingencyTables.RootedLabelWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

abbrev Input := ((RootedOracleWalkProgram.State × Fraction) × ℕ) × List Bool

def fields (z : Input) : List ℕ :=
  [z.1.1.1.1.2.1.1.1,z.1.1.1.1.1,
    RootedPenaltyEvaluateProgram.height z.1.1.1.1.2.1,z.1.2]

def dim : Expr := .input 0
def grid : Expr := .input 1
def height : Expr := .input 2
def phase : Expr := .input 3
def mixing : Expr := 2*(10000*dim^2*grid)^2
def allowance : Expr := height+dim*grid+2
def relativeDenominator : Expr := 400*(phase+1)

def scalar (e : Expr) (z : Input) : ℕ := e.eval (fields z)

def timeInput (z : Input) : ℕ × ℕ := (scalar mixing z,scalar allowance z)

def normalizedNoise (z : Input) : Fraction := TreeFraction.normalize z.1.1.2

def repeats (z : Input) : ℕ := 64*((normalizedNoise z).2.bits.length+1)
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContextProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase configuration from immutable prepared data

The reserve is used only through its length. All precision-marker bits
are false, so the physical configuration is independent of the random
contents of the word that provides its bounded allocation.
-/

namespace ContingencyTables.CompanionPhaseContextProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Prepared := RootedOracleWalkProgram.State × CountingPhaseParametersProgram.Input
abbrev Input := (Prepared × ℕ) × List Bool

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision z.1.1.2

def scalar (e : ScalarScheduleProgram.Expr) (z : Input) : ℕ :=
  CountingPhaseParametersProgram.scalar e z.1.1.2

def falseReserve (z : Input) : List Bool := z.2.map (fun _ => false)
end ContingencyTables.CompanionPhaseContextProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartInitializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed finite initializer used before every restart experiment -/
namespace ContingencyTables.CompanionRestartInitializer
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Input := Prepared×List Bool

def forest (z : Prepared) : RootedForestCatalog.Data := z.1.1.2.2.1

def cellInput (z : Prepared) : CompanionCellCatalog.Input :=
  (((forest z).1.2,(forest z).2),(forest z).1.1.2)

def fields (z : Prepared) : List ℕ := z.1.1.2.1.1.1::z.2.1

def initialBound : Expr := (.input 0)*(3*(.input 2)+1)+1
def initialExponent : Expr := 2048*((.input 3)+1)
def scalar (e : Expr) (z : Prepared) : ℕ := e.eval (fields z)

def precision (z : Prepared) : ℕ := Nat.clog 2 (scalar initialBound z)+scalar initialExponent z

def capacities (z : Prepared) : List ℕ := CompanionCellCatalog.capacities (cellInput z)

def width (z : Prepared) : ℕ := (InitialChoiceProgram.widths (capacities z,precision z)).sum

def prepare (z : Input) : CompanionComputedInitial.ProgramInput := ((cellInput z.1,precision z.1),z.2)
end ContingencyTables.CompanionRestartInitializer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStateMultiplierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the multiplier of an actual encoded chain state

The at most quadratic list of labelled defect types is searched using
the proved occupancy test. Uniqueness of defect labels identifies the
selected matrix entry with the mathematical chain multiplier.
-/

namespace ContingencyTables.CompanionStateMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionChainValidator CompanionPhaseCounts CompanionMultiplierMatrixProgram

def coordinates (z : ValidatorInput) : List ℕ := z.1.map Prod.fst

def candidates (z : ValidatorInput) : List (ℕ × ℕ) := cellPairs (coordinates z,coordinates z)

def found (z : ValidatorInput) : List (ℕ × ℕ) :=
  (candidates z).filter (fun st => pairedDefectTest (z,st))

abbrev Input := FractionMatrix × ValidatorInput

def noDefect (z : Input) : Bool := (found z.2).isEmpty

def readDefect (z : Input) : TreeFraction.Fraction := readEntry (z.1,(found z.2).getD 0 (0,0))

def output (z : Input) : TreeFraction.Fraction := if noDefect z then (1,1) else readDefect z
end ContingencyTables.CompanionStateMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := (TreeFraction.Fraction × TreeFraction.Fraction) × List Bool

def ratio (z : Input) : TreeFraction.Fraction := TreeFraction.div (z.1.2,z.1.1)

def belowOne (z : Input) : Bool := TreeFraction.less (ratio z,(1,1))

def probability (z : Input) : TreeFraction.Fraction := if belowOne z then ratio z else (1,1)

attribute [local irreducible] probability

end ContingencyTables.FractionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One physical companion-chain step with independent word fields

The proposed state is computed by the quadratic arithmetic candidate
list. Two disjoint words evaluate the current and candidate states, and
a third field supplies the rational acceptance coin.
-/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Words := Bool × (List Bool × ((List Bool × List Bool) × List Bool))

def defaultCode (z : List ℕ × Option (List ℕ)) : List ℕ := z.2.getD z.1

end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev DenseTrialData := (FlatExponentData×ℕ)×List Bool

def trialWalkBits (z : DenseTrialData) : ℕ :=
  (z.1.1.2^50*(z.1.2+1)^2)*GridBoundary.denseStepBits z.1.1.2

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev DenseDrawParameters := FlatExponentData×ℕ
abbrev DenseDrawData := (DenseDrawParameters×MatrixCode)×List Bool

def trialWidth (z : DenseDrawParameters) : ℕ :=
  trialWalkBits (z,[])+(offsetLengths (flatToGridData z.1,z.2)).sum

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MaximalListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a maximal margin in binary -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def maximumIndex (xs : List ℕ) : ℕ := xs.idxOf (listMaximum (xs,0))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSwapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column permutations for dense input normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def swapZeroIndex (z : ℕ×ℕ) : ℕ := if z.2=0 then z.1 else if z.2=z.1 then 0 else z.2

variable {A : Type}
  [Inhabited A]

def swapZeroEntry (z : (ℕ×List A)×ℕ) : A :=
  z.1.2.getD (swapZeroIndex (z.1.1,z.2)) default

def swapZeroIndices (z : ℕ×List A) : List ℕ := List.range z.2.length

def swapZeroList (z : ℕ×List A) : List A :=
  (swapZeroIndices z).map (fun i => swapZeroEntry (z,i))

def swapMatrixColumns (z : ℕ×MatrixCode) : MatrixCode :=
  z.2.map (fun row => swapZeroList (z.1,row))

def swapMatrix (z : (ℕ×ℕ)×MatrixCode) : MatrixCode :=
  swapMatrixColumns (z.1.2,swapZeroList (z.1.1,z.2))

open scoped Classical

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving maximal margins into the distinguished positions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def swapMargins (z : (ℕ×ℕ)×(List ℕ×List ℕ)) : List ℕ×List ℕ :=
  (swapZeroList (z.1.1,z.2.1),swapZeroList (z.1.2,z.2.2))

def swapFlatData (z : (ℕ×ℕ)×FlatExponentData) : FlatExponentData :=
  ((swapMargins (z.1,z.2.1.1),z.2.1.2),z.2.2)

def permuteDrawData (z : (ℕ×ℕ)×DenseDrawData) : DenseDrawData :=
  (((swapFlatData (z.1,z.2.1.1.1),z.2.1.1.2),swapMatrix (z.1,z.2.1.2)),z.2.2)

def marginIndices (z : List ℕ×List ℕ) : ℕ×ℕ := (maximumIndex z.1,maximumIndex z.2)

def drawIndices (z : DenseDrawData) : ℕ×ℕ := marginIndices z.1.1.1.1.1

def preparedDraw (z : DenseDrawData) : DenseDrawData :=
  permuteDrawData (drawIndices z,z)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyRowMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for one row of the greedy initializer -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

abbrev RowAccumulator := ℕ × (List ℕ × List ℕ)

/-- A row pass keeps its residual margin and builds both output lists
in reverse order, using only binary minimum, subtraction and list cons. -/
def rowCell (z : ℕ × RowAccumulator) : RowAccumulator :=
  let q := min z.2.1 z.1
  (z.2.1-q,(q::z.2.2.1,(z.1-q)::z.2.2.2))

/-- The list version of the already proved dimension-recursive row split. -/
def listSplitRow : ℕ → List ℕ → RowAccumulator
  | a,[] => (a,([],[]))
  | a,c::cs =>
    let q := min a c
    let tail := listSplitRow (a-q) cs
    (tail.1,(q::tail.2.1,(c-q)::tail.2.2))

lemma fold_rowCell (cs : List ℕ) (a : ℕ) (xs ys : List ℕ) :
    cs.foldl (fun z c => rowCell (c,z)) (a,(xs,ys))=
      let tail := listSplitRow a cs
      (tail.1,(tail.2.1.reverse++xs,tail.2.2.reverse++ys)) := by
  induction cs generalizing a xs ys with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons]
    change cs.foldl (fun z c => rowCell (c,z))
      (a-min a c,(min a c::xs,(c-min a c)::ys))=_
    rw [ih]
    simp only [listSplitRow,List.reverse_cons,List.append_assoc,List.singleton_append]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyTableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed binary list program constructing the greedy table -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

abbrev TableAccumulator := List ℕ × List (List ℕ)

def tableRow (z : ℕ × TableAccumulator) : TableAccumulator :=
  let row := listSplitRow z.1 z.2.1
  (row.2.2,row.2.1::z.2.2)

def listMatrix : List ℕ → List ℕ → List (List ℕ)
  | [],_ => []
  | a::as,cs =>
    let row := listSplitRow a cs
    row.2.1::listMatrix as row.2.2

lemma fold_tableRow (rs cs : List ℕ) (rows : List (List ℕ)) :
    (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).2=
      (listMatrix rs cs).reverse++rows := by
  induction rs generalizing cs rows with
  | nil => rfl
  | cons a rs ih =>
    rw [List.foldl_cons]
    change (rs.foldl (fun z a => tableRow (a,z))
      ((listSplitRow a cs).2.2,(listSplitRow a cs).2.1::rows)).2=_
    rw [ih]
    simp only [listMatrix,List.reverse_cons,List.append_assoc,List.singleton_append]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense sampling from margins with a computed grid and fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

abbrev CanonicalParameters := (List ℕ×List ℕ)×(ℕ×ℕ)
abbrev CanonicalDrawData := CanonicalParameters×List Bool

def zeroGrid (z : List ℕ×List ℕ) : List ℕ :=
  (cellPairs (z.1.tail,z.2.tail)).map (fun _ => 0)

def canonicalInput (z : CanonicalDrawData) : DenseDrawData :=
  (((((z.1.1,zeroGrid z.1.1),z.1.2.1),z.1.2.2),
    GreedyFeasibleTable.listMatrix z.1.1.1 z.1.1.2),z.2)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReservedWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

def denseParameterBits (z : DenseDrawParameters) : ℕ :=
  (z.1.2^4*(z.2+1))*trialWidth z

def preparedCanonicalParameters (z : CanonicalParameters) : DenseDrawParameters :=
  (preparedDraw (canonicalInput (z,[]))).1.1

def canonicalBitCount (z : CanonicalParameters) : ℕ :=
  denseParameterBits (preparedCanonicalParameters z)

open GridBoundary
open scoped BigOperators Classical
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedResidualProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing padded residual margins from the stored small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeFlag (z : ℕ×ℕ) : ℕ := if z.1≤z.2 then 1 else 0

def largeCount (z : ℕ×List ℕ) : ℕ := (z.2.map (fun a => largeFlag (z.1,a))).sum

abbrev PaddingData := MarginCheckData×ℕ

def paddedMarginAt (row : Bool) (z : PaddingData×ℕ) : ℕ :=
  let a := (marginList row z.1.1).getD z.2 0
  let used := lineSum row (lineArgument row (z.1.1,z.2))
  a-used+largeFlag (z.1.1.2,a)*largeCount (z.1.1.2,marginList (!row) z.1.1)*z.1.2

def paddedMargins (row : Bool) (z : PaddingData) : List ℕ :=
  (List.range (marginList row z.1).length).map (fun i => paddedMarginAt row (z,i))

open scoped BigOperators

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeIndexTest (z : (ℕ×List ℕ)×ℕ) : Bool :=
  decide (z.1.1≤z.1.2.getD z.2 0)

def largeIndices (z : ℕ×List ℕ) : List ℕ :=
  (List.range z.2.length).filter (fun i => largeIndexTest (z,i))

def selectList {A : Type} (a : A) (z : List ℕ×List A) : List A :=
  z.1.map (fun i => z.2.getD i a)

def largePaddedMargins (row : Bool) (z : PaddingData) : List ℕ :=
  selectList 0 (largeIndices (z.1.2,marginList row z.1),paddedMargins row z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def capView (z : (ℕ×ℕ)×List ℕ) : List ℕ :=
  (z.2.take z.1.1).map (fun a => min a z.1.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTransitionWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

def expression : Expr := 1+(Expr.input 0+((Expr.input 1+Expr.input 1)+Expr.input 2))
end ContingencyTables.CompanionTransitionWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartStageProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed warm-restart stage

The context supplies the phase, immutable oracle metadata and deterministic
precision markers. The matrix is the stored multiplier for that phase.
-/
namespace ContingencyTables.CompanionRestartStageProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

abbrev Request := (CompanionPhaseContextProgram.Input × FractionMatrix) × List ℕ
abbrev Input := Request × List Bool

def context (z : Request) : CompanionPhaseContextProgram.Input := z.1.1

end ContingencyTables.CompanionRestartStageProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed restart stages with disjoint variable-width words

The supplied stage list determines the number of iterations. The current
encoded profile is bounded by the original profile length after every stage.
-/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms
open CompanionMultiplierMatrixProgram

abbrev Stage := CompanionPhaseContextProgram.Input × FractionMatrix
abbrev Input := (List Stage × List ℕ) × List Bool
abbrev State := Input × List ℕ

def indices (z : Input) : List ℕ := List.range z.1.1.length

end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization and all stored-multiplier restart stages

Past entries are stored in chronological order. Entry i contains the
multiplier for restart phase i+1. Initialization and restart stages take
disjoint slices of the supplied word.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Input := (Prepared×List Stored)×List Bool

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)

def indices (z : Input) : List ℕ := List.range z.1.2.length

end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A deterministic bit allocation for initialized restart experiments -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms Polynomial

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev StageInput := Prepared×ℕ
abbrev Input := Prepared×List CompanionPhaseFinishProgram.Stored

def scalar (e : Expr) (z : StageInput) : ℕ := CountingPhaseParametersProgram.scalar e z.1.2

def proposalWidth (z : StageInput) : ℕ := Nat.clog 2 (scalar (.input 0) z*scalar (.input 0) z)

def precision (z : StageInput) : ℕ := CountingPhaseParametersProgram.precision z.1.2

def expression : Expr := (.input 3)*((.input 4+1)*(1+(.input 0+((.input 1+.input 1)+.input 2))))

def indices (z : Input) : List ℕ := List.range z.2.length

end ContingencyTables.CompanionRestartSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One complete adaptive phase from the stored chronological history -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Prepared := CompanionPhaseContextProgram.Prepared

end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterHistoryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chronological execution of all counting phases -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Prepared := CompanionPhaseContextProgram.Prepared

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A phase adds a bounded amount to each stored fraction's binary height -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram CompanionMultiplierProgram CompanionPhaseCounts

def MatrixHeight (M : ℕ) (w : FractionMatrix) : Prop :=
  ∀ row∈w,∀ x∈row,TreeFraction.height x ≤ M

def StoredHeight (M : ℕ) (s : Stored) : Prop := MatrixHeight M s.1 ∧ TreeFraction.height s.2 ≤ M

end ContingencyTables.CompanionStoredSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Height and shape invariants for chronological stored values -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram

def StoredShape (R : ℕ) (s : Stored) : Prop :=
  s.1.length ≤ R ∧ ∀ row∈s.1,row.length ≤ R

end ContingencyTables.CompanionStoredSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

abbrev Input := CompanionPhaseContextProgram.Prepared

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision z.2

def initialPrecision (z : Input) : ℕ :=
  CountingPhaseParametersProgram.scalar CountingPhaseScalarProgram.initialPrecision z.2

def x : Expr := .input 0
def innerExpression : Expr := 400*(x+1)*x
def timeExpression : Expr := 2*(10000*x^2*x)^2*(x+x*x+2+4096*innerExpression)
def sampleExpression : Expr := 65536*(x+1)*innerExpression^2
def binExpression : Expr := x*(x+1+4*(4096*x*innerExpression+x))
def estimatorExpression : Expr := x*(sampleExpression*(timeExpression*(9*x)))+
  sampleExpression*(timeExpression*(9*x)+binExpression)
def medianExpression : Expr := 64*(x+1)*estimatorExpression
def initialExpression : Expr := x*(x+1)*(x*(3*x+1)+1+x)
def stepExpression : Expr := 1+(x^2+((medianExpression+medianExpression)+x))
def stageExpression : Expr := x*((x+1)*stepExpression)
def phaseExpression : Expr := initialExpression+x*stageExpression+
  (x*stepExpression+(x+1)*(medianExpression+medianExpression))
def widthExpression : Expr := x*(x*phaseExpression)+409600*(x+1)*x+2*x+1

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary programs for one stored BFS round -/

namespace ContingencyTables.DirectedBFSProgram

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode

abbrev Context := Graph×Store
abbrev Query := Context×ℕ
abbrev Candidate := Query×ℕ

def indices (g : Graph) : List ℕ := List.range g.length

def lookupPath (z : Store×ℕ) : Option (List ℕ) := lookup z.1 z.2

def readEdge (z : (Graph×ℕ)×ℕ) : Bool := adjacent z.1.1 z.1.2 z.2

def candidate (z : Candidate) : Bool :=
  (lookup z.1.1.2 z.2).isSome && adjacent z.1.1.1 z.2 z.1.2

def predecessorInput (z : Query) : Option ℕ := DirectedBFSCode.predecessor z.1.1 z.1.2 z.2

def appendPath (z : Query×List ℕ) : Option (List ℕ) := Option.some (z.2++[z.1.2])

def fromPredecessor (z : Query×ℕ) : Option (List ℕ) :=
  (lookup z.1.1.2 z.2).map (fun xs=>xs++[z.1.2])

def missing (z : Query) : Option (List ℕ) :=
  (predecessorInput z).bind (fun u=>fromPredecessor (z,u))

def rowInput (z : Query) : Option (List ℕ) := roundRow z.1.1 z.1.2 z.2

def roundInput (z : Context) : Store := round z.1 z.2

end ContingencyTables.DirectedBFSProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the entire materialized BFS -/

namespace ContingencyTables.DirectedBFSRuntime

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode DirectedBFSProgram

def advance (z : ℕ×Context) : Context := (z.2.1,round z.2.1 z.2.2)

lemma fold_eq (steps : List ℕ) (g : Graph) (P : Store) :
    steps.foldl (fun s i=>advance (i,s)) (g,P)=
      (g,steps.foldl (fun P _=>round g P) P) := by
  induction steps generalizing P with
  | nil => rfl
  | cons i steps ih => exact ih (round g P)

def initialRow (z : ℕ×ℕ) : Option (List ℕ) :=
  if z.2=z.1 then Option.some [z.1] else none

def initialInput (z : Graph×ℕ) : Store := initial z.1 z.2

def prepare (z : Graph×ℕ) : List ℕ×Context :=
  (indices z.1,(z.1,initial z.1 z.2))

def runInput (z : Graph×ℕ) : Store := run z.1 z.2

def searchInput (z : (Graph×ℕ)×ℕ) : Option (List ℕ) := search z.1.1 z.1.2 z.2

end ContingencyTables.DirectedBFSRuntime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PublishedEdmondsKarp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shortest-augmenting-path bound

The finite integral-network specialization of Edmonds and Karp,
*Theoretical Improvements in Algorithmic Efficiency for Network Flow
Problems*, J. ACM 19(2) (1972), 248–264, Theorem 1 (printed page 251).
The bound (n³−n)/4 implies the n³ bound for shortest residual augmentations.

Primary text:
https://web.eecs.umich.edu/~pettie/matching/Edmonds-Karp-network-flow.pdf
-/

namespace ContingencyTables.PublishedEdmondsKarp

open scoped BigOperators

abbrev Flow (n : ℕ) := Fin n → Fin n → ℤ
abbrev Capacity (n : ℕ) := Fin n → Fin n → ℕ

/-- Skew flows combine the two antiparallel directions. The upper
capacity bound and skew symmetry give both directed residual bounds. -/
def Feasible {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n) : Prop :=
  (∀ u v, f u v= -f v u) ∧
  (∀ u v, f u v ≤ c u v) ∧
  (∀ u, u≠s → u≠t → (∑ v, f u v)=0)

def value {n : ℕ} (s : Fin n) (f : Flow n) : ℤ := ∑ v, f s v

def IsMaximum {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n) : Prop :=
  Feasible c s t f ∧ ∀ g, Feasible c s t g → value s g≤value s f

/-- A directed residual path with k arcs and no repeated vertices. -/
def ResidualPath {n : ℕ} (c : Capacity n) (f : Flow n) (s t : Fin n)
    (k : ℕ) (p : Fin (k+1) → Fin n) : Prop :=
  p 0=s ∧ p (Fin.last k)=t ∧ Function.Injective p ∧
  ∀ i : Fin k, 0<(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)

/-- An actual saturating augmentation along a shortest residual path.
The bottleneck is positive, bounded by every residual capacity, and
attained by an arc. The displayed update adds it forward and subtracts
it backward on precisely the traversed arcs. -/
def ShortestAugmentation {n : ℕ} (c : Capacity n) (s t : Fin n)
    (f g : Flow n) : Prop :=
  ∃ (k : ℕ) (p : Fin (k+1) → Fin n) (a : ℤ),
    ResidualPath c f s t k p ∧
    (∀ (l : ℕ) (q : Fin (l+1) → Fin n), ResidualPath c f s t l q → k≤l) ∧
    0<a ∧
    (∀ i : Fin k, a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    (∃ i : Fin k, a=(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    ∀ u v, g u v=f u v+a*((∑ i : Fin k,
      if p i.castSucc=u ∧ p i.succ=v then (1:ℤ) else 0)-
      (∑ i : Fin k, if p i.castSucc=v ∧ p i.succ=u then (1:ℤ) else 0))

/-- A finite initial segment of an actual shortest-augmentation
execution. It need not already have reached a maximum flow. -/
def AugmentationTrace {n K : ℕ} (c : Capacity n) (s t : Fin n)
    (F : Fin (K+1) → Flow n) : Prop :=
  F 0=0 ∧
  (∀ i, Feasible c s t (F i)) ∧
  ∀ i : Fin K, ShortestAugmentation c s t (F i.castSucc) (F i.succ)

/-- The shortest-augmenting-path bound for integral skew flows.
Every finite initial segment has at most n³ augmentations, independently
of the rule used to break ties between shortest paths. -/
def EdmondsKarp1972Theorem1 : Prop :=
  ∀ (n : ℕ) (c : Capacity n), (∀ u, c u u=0) →
    ∀ (s t : Fin n), s≠t →
      ∀ (K : ℕ) (F : Fin (K+1) → Flow n),
        AugmentationTrace c s t F → K≤n^3

theorem no_long_trace (hEK : EdmondsKarp1972Theorem1)
    {n : ℕ} (c : Capacity n) (hc : ∀ u, c u u=0)
    (s t : Fin n) (hst : s≠t) (F : Fin (n^3+2) → Flow n) :
    ¬AugmentationTrace c s t F := by
  intro hF
  have h := hEK n c hc s t hst (n^3+1) F hF
  exact Nat.not_succ_le_self _ h

end ContingencyTables.PublishedEdmondsKarp

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed residual search and its maximum-flow certificate

The search itself is the deterministic directed BFS. Success supplies
the precise shortest simple residual path required by the published
augmentation bound; failure supplies a saturated cut, hence maximality.
-/

namespace ContingencyTables.ResidualSearch

open FiniteDirectedBFS PublishedEdmondsKarp
open scoped BigOperators

variable {n : ℕ}

def edge (c : Capacity n) (f : Flow n) (u v : Fin n) : Bool :=
  decide (0<(c u v:ℤ)-f u v)

def search (c : Capacity n) (f : Flow n) (s t : Fin n) : Option (List (Fin n)) :=
  paths (edge c f) s n t

lemma route_of_fin (E : Fin n → Fin n → Bool) (k : ℕ)
    (p : Fin (k+1) → Fin n)
    (hp : ∀ i : Fin k,E (p i.castSucc) (p i.succ)=true) :
    Route E (p 0) (p (Fin.last k)) (List.ofFn p) := by
  induction k with
  | zero => simpa [List.ofFn_succ] using (Route.start (E:=E) (s:=p 0))
  | succ k ih =>
    let q : Fin (k+1) → Fin n := fun i=>p i.castSucc
    have hq : ∀ i : Fin k,E (q i.castSucc) (q i.succ)=true := by
      intro i
      exact hp i.castSucc
    have hr := ih q hq
    have he : E (q (Fin.last k)) (p (Fin.last (k+1)))=true :=
      hp (Fin.last k)
    simpa only [List.ofFn_succ_last,q,Fin.castSucc_zero] using hr.extend he

lemma route_of_residual (c : Capacity n) (f : Flow n) (s t : Fin n)
    (k : ℕ) (p : Fin (k+1) → Fin n) (hp : ResidualPath c f s t k p) :
    Route (edge c f) s t (List.ofFn p) := by
  have h := route_of_fin (edge c f) k p (fun i=>by simpa [edge] using hp.2.2.2 i)
  simpa only [hp.1,hp.2.1] using h

theorem search_shortest (c : Capacity n) (f : Flow n) (s t : Fin n)
    (xs : List (Fin n)) (hs : search c f s t=some xs) :
    ∃ (k : ℕ) (p : Fin (k+1) → Fin n),
      xs=List.ofFn p ∧ ResidualPath c f s t k p ∧
      ∀ (l : ℕ) (q : Fin (l+1) → Fin n), ResidualPath c f s t l q → k≤l := by
  have hr := (paths_sound hs).1
  have hn := paths_nodup hs
  cases xs with
  | nil => exact False.elim (hr.nonempty rfl)
  | cons a ys =>
    let p : Fin (ys.length+1) → Fin n := Fin.cons a ys.get
    have he : List.ofFn p=a::ys := by simp [p]
    have hhead : p 0=s := by simpa [←he,List.ofFn_succ] using hr.head
    have hlast : p (Fin.last ys.length)=t := by
      have hh := hr.last
      rw [←he,List.getLast?_eq_some_getLast (by simp)] at hh
      simpa only [List.getLast_ofFn_succ,Option.some.injEq] using hh
    have hinj : Function.Injective p := List.nodup_ofFn.mp (he.symm ▸ hn)
    have hchain := List.isChain_ofFn.mp (he.symm ▸ hr.chain)
    have hres : ResidualPath c f s t ys.length p := by
      refine ⟨hhead,hlast,hinj,?_⟩
      intro i
      have hc := hchain i.val (by omega)
      change edge c f (p i.castSucc) (p i.succ)=true at hc
      exact of_decide_eq_true hc
    refine ⟨ys.length,p,he.symm,hres,?_⟩
    intro l q hq
    have hle := paths_shortest hs (List.ofFn q) (route_of_residual c f s t l q hq)
    simpa using hle

def reached (c : Capacity n) (f : Flow n) (s : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v=>(paths (edge c f) s n v).isSome)

lemma mem_reached (c : Capacity n) (f : Flow n) (s v : Fin n) :
    v∈reached c f s ↔ discovered (paths (edge c f) s n) v := by
  simp [reached,discovered,Option.isSome_iff_exists]

lemma source_reached (c : Capacity n) (f : Flow n) (s : Fin n) :
    s∈reached c f s := (mem_reached c f s s).mpr (source_found _ _)

lemma target_not_reached (c : Capacity n) (f : Flow n) (s t : Fin n)
    (h : search c f s t=none) : t∉reached c f s := by
  rw [mem_reached]
  rintro ⟨xs,hxs⟩
  simp [search] at h
  simp [h] at hxs

lemma cut_saturated (c : Capacity n) (f : Flow n) (s : Fin n)
    (hcap : ∀ u v,f u v ≤ c u v) {u v : Fin n}
    (hu : u∈reached c f s) (hv : v∉reached c f s) : f u v=c u v := by
  have hno : ¬0<(c u v:ℤ)-f u v := by
    intro hp
    have he : edge c f u v=true := by simpa [edge] using hp
    exact hv ((mem_reached c f s v).mpr
      (reached_closed ((mem_reached c f s u).mp hu) he))
  have hc := hcap u v
  omega

lemma sum_internal_zero (f : Flow n) (hf : ∀ u v,f u v= -f v u)
    (S : Finset (Fin n)) : (∑ u∈S,∑ v∈S,f u v)=0 := by
  have hn : (∑ u∈S,∑ v∈S,f u v)= -(∑ u∈S,∑ v∈S,f u v) := by
    calc
      _ = ∑ v∈S,∑ u∈S,f u v := Finset.sum_comm
      _ = ∑ v∈S,∑ u∈S,-f v u := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_congr rfl (fun u _=>hf u v)
      _ = _ := by simp
  omega

lemma value_eq_cut (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (S : Finset (Fin n)) (hs : s∈S) (ht : t∉S) :
    value s f=∑ u∈S,∑ v∈Sᶜ,f u v := by
  have hb : (∑ u∈S,∑ v,f u v)=value s f := by
    apply Finset.sum_eq_single s
    · intro u hu hus
      exact hf.2.2 u hus (fun hut=>ht (hut ▸ hu))
    · exact fun h=>False.elim (h hs)
  have hc : (∑ u∈S,∑ v,f u v)=
      (∑ u∈S,∑ v∈S,f u v)+(∑ u∈S,∑ v∈Sᶜ,f u v) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl S (f u)).symm
  rw [sum_internal_zero f hf.1,zero_add] at hc
  exact hb.symm.trans hc

/-- Failure of the actual finite BFS implies maximum flow. No
max-flow/min-cut result is included in the published input. -/
theorem failure_maximum (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (h : search c f s t=none) : IsMaximum c s t f := by
  refine ⟨hf,?_⟩
  intro g hg
  let S := reached c f s
  have hs : s∈S := source_reached c f s
  have ht : t∉S := target_not_reached c f s t h
  rw [value_eq_cut c s t g hg S hs ht,value_eq_cut c s t f hf S hs ht]
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  have hv' : v∉S := by simpa using hv
  have he : f u v=c u v := cut_saturated c f s hf.2.1 hu hv'
  simpa only [he] using hg.2.1 u v

end ContingencyTables.ResidualSearch

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction and search of the actual residual graph -/

namespace ContingencyTables.ResidualGraphProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram

abbrev NatMatrix := List (List ℕ)

def matrixIndices (C : NatMatrix) : List ℕ := List.range C.length

def capacityEntry (z : NatMatrix×(ℕ×ℕ)) : ℕ :=
  (z.1.getD z.2.1 []).getD z.2.2 0

def natCode {m n : ℕ} (c : Fin m→Fin n→ℕ) : NatMatrix :=
  List.ofFn (fun u=>List.ofFn (c u))

lemma capacityEntry_code {m n : ℕ} (c : Fin m→Fin n→ℕ) (u : Fin m) (v : Fin n) :
    capacityEntry (natCode c,(u.val,v.val))=c u v := by
  simp only [capacityEntry,natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    u.isLt,v.isLt,dite_true,Option.getD_some,Fin.eta]

end ContingencyTables.ResidualGraphProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FlowClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary flow magnitudes and a harmless total-domain clamp

Skew symmetry bounds a feasible entry between its two directed
capacities. The executed list program clamps normalized entries to this
interval. This is the identity on every valid flow and bounds every
stored value even on unrelated raw program inputs.
-/

namespace ContingencyTables.FlowClamp

open MatchingFPRAS.TreeTyped PublishedEdmondsKarp

lemma feasible_lower {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (u v : Fin n) : -(c v u:ℤ)≤f u v := by
  have h := hf.2.1 v u
  have hs := hf.1 u v
  omega

end ContingencyTables.FlowClamp

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PathAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral augmentation along a simple path

The identities here prove conservation and capacity preservation for the
literal forward-minus-reverse update in the published-input interface.
-/

namespace ContingencyTables.PathAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n k : ℕ}

def arcCount (p : Fin (k+1) → Fin n) (u v : Fin n) : ℤ :=
  ∑ i : Fin k,if p i.castSucc=u ∧ p i.succ=v then 1 else 0

def update (f : Flow n) (p : Fin (k+1) → Fin n) (a : ℤ) : Flow n :=
  fun u v=>f u v+a*(arcCount p u v-arcCount p v u)

lemma arcCount_nonneg (p : Fin (k+1) → Fin n) (u v : Fin n) :
    0≤arcCount p u v := by
  apply Finset.sum_nonneg
  intro i _
  split <;> omega

lemma row_arcCount (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v,arcCount p u v)=∑ i : Fin k,if p i.castSucc=u then (1:ℤ) else 0 := by
  unfold arcCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i.castSucc=u
  · simp [h]
  · simp [h]

lemma column_arcCount (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v,arcCount p v u)=∑ i : Fin k,if p i.succ=u then (1:ℤ) else 0 := by
  unfold arcCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i.succ=u
  · simp [h]
  · simp [h]

lemma path_divergence (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v : Fin n,(arcCount p u v-arcCount p v u))=
      (if p 0=u then (1:ℤ) else 0)-(if p (Fin.last k)=u then 1 else 0) := by
  have he : (∑ v : Fin n,(arcCount p u v-arcCount p v u))=
      (∑ v : Fin n,arcCount p u v)-(∑ v : Fin n,arcCount p v u) :=
    Finset.sum_sub_distrib (fun v : Fin n=>arcCount p u v) (fun v : Fin n=>arcCount p v u)
  have h1 := Fin.sum_univ_castSucc (fun i : Fin (k+1)=>if p i=u then (1:ℤ) else 0)
  have h2 := Fin.sum_univ_succ (fun i : Fin (k+1)=>if p i=u then (1:ℤ) else 0)
  rw [row_arcCount,column_arcCount] at he
  omega

lemma update_skew (f : Flow n) (hf : ∀ u v,f u v= -f v u)
    (p : Fin (k+1) → Fin n) (a : ℤ) :
    ∀ u v,update f p a u v= -update f p a v u := by
  intro u v
  unfold update
  rw [hf u v]
  ring

lemma update_sum (f : Flow n) (p : Fin (k+1) → Fin n) (a : ℤ) (u : Fin n) :
    (∑ v,update f p a u v)=(∑ v,f u v)+
      a*((if p 0=u then (1:ℤ) else 0)-(if p (Fin.last k)=u then 1 else 0)) := by
  simp only [update,Finset.sum_add_distrib,←Finset.mul_sum]
  exact congrArg (fun z : ℤ=>(∑ v,f u v)+a*z) (path_divergence p u)

end ContingencyTables.PathAugmentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed bottleneck and residual augmentation

The program takes the actual BFS path list, scans its residual capacities
for a minimum, and adds the resulting skew path flow. No path or amount
is chosen through a mathematical existence proof.
-/

namespace ContingencyTables.ResidualAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n : ℕ}

def arcs : List (Fin n) → List (Fin n×Fin n)
  | [] => []
  | [_] => []
  | u::v::xs => (u,v)::arcs (v::xs)

def bottleneck (c : Capacity n) (f : Flow n) (xs : List (Fin n)) : ℤ :=
  ((arcs xs).map (fun uv=>(c uv.1 uv.2:ℤ)-f uv.1 uv.2)).min?.getD 0

def listUpdate (f : Flow n) (xs : List (Fin n)) (a : ℤ) : Flow n :=
  fun u v=>f u v+a*((((arcs xs).map (fun uv=>if uv=(u,v) then (1:ℤ) else 0)).sum)-
    (((arcs xs).map (fun uv=>if uv=(v,u) then (1:ℤ) else 0)).sum))

def step (c : Capacity n) (s t : Fin n) (f : Flow n) : Option (Flow n) :=
  (ResidualSearch.search c f s t).map (fun xs=>listUpdate f xs (bottleneck c f xs))

lemma arcs_ofFn (k : ℕ) (p : Fin (k+1) → Fin n) :
    arcs (List.ofFn p)=List.ofFn (fun i : Fin k=>(p i.castSucc,p i.succ)) := by
  induction k with
  | zero => simp [List.ofFn_succ,arcs]
  | succ k ih =>
    rw [List.ofFn_succ (f:=p)]
    rw [List.ofFn_succ (f:=fun i : Fin (k+1)=>p i.succ)]
    rw [arcs]
    have h := ih (fun i : Fin (k+1)=>p i.succ)
    rw [List.ofFn_succ] at h
    rw [h,List.ofFn_succ]
    rfl

lemma listUpdate_ofFn (f : Flow n) (k : ℕ) (p : Fin (k+1) → Fin n) (a : ℤ) :
    listUpdate f (List.ofFn p) a=PathAugmentation.update f p a := by
  funext u v
  simp only [listUpdate,arcs_ofFn,List.map_ofFn,Function.comp_apply,Fin.sum_ofFn,
    PathAugmentation.update,PathAugmentation.arcCount,Prod.mk.injEq]

lemma bottleneck_ofFn (c : Capacity n) (f : Flow n) (k : ℕ)
    (p : Fin (k+1) → Fin n) :
    bottleneck c f (List.ofFn p)=
      (List.ofFn (fun i : Fin k=>(c (p i.castSucc) (p i.succ):ℤ)-
        f (p i.castSucc) (p i.succ))).min?.getD 0 := by
  simp only [bottleneck,arcs_ofFn,List.map_ofFn,Function.comp_def]

lemma bottleneck_spec (c : Capacity n) (s t : Fin n) (hst : s≠t) (f : Flow n)
    (k : ℕ) (p : Fin (k+1) → Fin n) (hp : ResidualPath c f s t k p) :
    0<bottleneck c f (List.ofFn p) ∧
    (∀ i : Fin k,bottleneck c f (List.ofFn p)≤
      (c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    ∃ i : Fin k,bottleneck c f (List.ofFn p)=
      (c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ) := by
  have hk : k≠0 := by
    intro h
    subst k
    have he : s=t := hp.1.symm.trans hp.2.1
    exact hst he
  let r : Fin k → ℤ := fun i=>(c (p i.castSucc) (p i.succ):ℤ)-
    f (p i.castSucc) (p i.succ)
  rw [bottleneck_ofFn]
  change 0<(List.ofFn r).min?.getD 0 ∧
    (∀ i,(List.ofFn r).min?.getD 0 ≤ r i) ∧ ∃ i,(List.ofFn r).min?.getD 0=r i
  cases hm : (List.ofFn r).min? with
  | none =>
    have hz : k=0 := List.ofFn_eq_nil_iff.mp (List.min?_eq_none_iff.mp hm)
    exact False.elim (hk hz)
  | some a =>
    have ha := List.min?_eq_some_iff.mp hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha.1
    simp only [Option.getD_some]
    refine ⟨?_,?_,⟨i,hi.symm⟩⟩
    · rw [←hi]
      exact hp.2.2.2 i
    · intro j
      exact ha.2 (r j) (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem step_augmentation (c : Capacity n) (s t : Fin n) (hst : s≠t)
    (f g : Flow n) (h : step c s t f=some g) : ShortestAugmentation c s t f g := by
  obtain ⟨xs,hxs,hg⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨k,p,hp,hr,hshort⟩ := ResidualSearch.search_shortest c f s t xs hxs
  subst xs
  have hb := bottleneck_spec c s t hst f k p hr
  refine ⟨k,p,bottleneck c f (List.ofFn p),hr,hshort,hb.1,hb.2.1,hb.2.2,?_⟩
  intro u v
  rw [←hg,listUpdate_ofFn]
  rfl

theorem step_none_maximum (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (h : step c s t f=none) : IsMaximum c s t f := by
  apply ResidualSearch.failure_maximum c s t f hf
  exact Option.map_eq_none_iff.mp h

end ContingencyTables.ResidualAugmentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary path bottlenecks and one integral flow-entry update -/

namespace ContingencyTables.FlowPathProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram

/-- Adjacent path entries, using only indices below the stored path length. -/
def arcPairs (xs : List ℕ) : List (ℕ×ℕ) :=
  (List.range (xs.length-1)).map (fun i=>(xs.getD i 0,xs.getD (i+1) 0))

def pairAt (z : List ℕ×ℕ) : ℕ×ℕ := (z.1.getD z.2 0,z.1.getD (z.2+1) 0)

def arcIndices (xs : List ℕ) : List ℕ := List.range (xs.length-1)

lemma arcPairs_cons_cons (u v : ℕ) (xs : List ℕ) :
    arcPairs (u::v::xs)=(u,v)::arcPairs (v::xs) := by
  simp [arcPairs,List.range_succ_eq_map,Function.comp_def]

lemma arcPairs_map {n : ℕ} (xs : List (Fin n)) :
    arcPairs (xs.map Fin.val)=
      (ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)) := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    cases xs with
    | nil => rfl
    | cons v xs =>
      simpa only [List.map_cons,arcPairs_cons_cons,ResidualAugmentation.arcs] using
        congrArg (List.cons (u.val,v.val)) ih

def minimumScan (xs : List ℕ) : ℕ :=
  match xs with
  | [] => 0
  | a::as => as.foldl (fun b a=>min a b) a

lemma minimumFold_cast (xs : List ℕ) (a : ℕ) :
    ((xs.foldl (fun b a : ℕ=>min a b) a:ℕ):ℤ)=
      (xs.map (fun a : ℕ=>(a:ℤ))).foldl min (a:ℤ) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [ih,Nat.cast_min,min_comm (b:ℤ) (a:ℤ)]

lemma minimumScan_cast (xs : List ℕ) :
    (minimumScan xs:ℤ)=(xs.map (fun a : ℕ=>(a:ℤ))).min?.getD 0 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [minimumScan,List.map_cons,List.min?_cons',Option.getD_some]
    exact minimumFold_cast xs a

def pairEqual (z : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  decide (z.1.1=z.2.1) && decide (z.1.2=z.2.2)

def arcCount (z : (ℕ×ℕ)×List (ℕ×ℕ)) : ℕ :=
  (z.2.filter (fun uv=>pairEqual (z.1,uv))).length

lemma arcCount_cast (uv : ℕ×ℕ) (xs : List (ℕ×ℕ)) :
    (arcCount (uv,xs):ℤ)=(xs.map (fun xy=>if xy=uv then (1:ℤ) else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=uv
    · subst a
      simpa [arcCount,pairEqual,add_comm] using congrArg (fun z : ℤ=>1+z) ih
    · have he : pairEqual (uv,a)=false := by
        by_cases h1 : uv.1=a.1
        · by_cases h2 : uv.2=a.2
          · exact False.elim (h (Prod.ext h1.symm h2.symm))
          · simp [pairEqual,h1,h2]
        · simp [pairEqual,h1]
      simp only [arcCount,List.filter_cons,he,Bool.false_eq_true,ite_false,
        List.map_cons,h,ite_false,List.sum_cons,zero_add]
      exact ih

end ContingencyTables.FlowPathProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowEntryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed augmentation of one matrix entry -/

namespace ContingencyTables.FlowEntryProgram

open MatchingFPRAS.TreeTyped ResidualGraphProgram FlowPathProgram

lemma arcCount_map {n : ℕ} (u v : Fin n) (xs : List (Fin n×Fin n)) :
    (arcCount ((u.val,v.val),xs.map (fun xy=>(xy.1.val,xy.2.val))):ℤ)=
      (xs.map (fun xy=>if xy=(u,v) then (1:ℤ) else 0)).sum := by
  rw [arcCount_cast,List.map_map]
  congr 1
  apply List.map_congr_left
  intro xy _
  simp only [Function.comp_apply,Fin.val_inj,Prod.ext_iff]

end ContingencyTables.FlowEntryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The bounded deterministic integral max-flow algorithm

Conditional on the augmentation-count bound, concrete residual searches,
bottlenecks and flow updates preserve feasibility and yield a stopping
certificate.
-/

namespace ContingencyTables.EdmondsKarpAlgorithm

open PublishedEdmondsKarp ResidualAugmentation

variable {n : ℕ}

def advance (c : Capacity n) (s t : Fin n) (f : Flow n) : Flow n :=
  (step c s t f).getD f

def run (c : Capacity n) (s t : Fin n) : ℕ → Flow n
  | 0 => 0
  | k+1 => advance c s t (run c s t k)

def maxFlow (c : Capacity n) (s t : Fin n) : Flow n := run c s t (n^3+1)

lemma zero_feasible (c : Capacity n) (s t : Fin n) : Feasible c s t 0 := by
  refine ⟨?_,?_,?_⟩
  · intro u v; simp
  · intro u v
    change (0:ℤ)≤(c u v:ℤ)
    exact_mod_cast Nat.zero_le (c u v)
  · intro u _ _; simp

lemma run_step (c : Capacity n) (s t : Fin n) (k : ℕ) (g : Flow n)
    (h : step c s t (run c s t k)=some g) : run c s t (k+1)=g := by
  simp only [run,advance,h,Option.getD_some]

lemma run_stops (c : Capacity n) (s t : Fin n) (k : ℕ)
    (h : step c s t (run c s t k)=none) (j : ℕ) :
    run c s t (k+j)=run c s t k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ,run,ih,advance,h,Option.getD_none]

end ContingencyTables.EdmondsKarpAlgorithm

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materialized binary residual augmentation

The path and bottleneck are computed once, then every matrix entry is
updated from the preceding matrix. Missing paths leave that matrix
unchanged.
-/

namespace ContingencyTables.FlowMatrixProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram FlowPathProgram
  FlowEntryProgram

lemma search_residual_nonnegative {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (s t : Fin n) (xs : List (Fin n))
    (h : ResidualSearch.search c f s t=some xs) :
    ∀ uv∈ResidualAugmentation.arcs xs,0≤(c uv.1 uv.2:ℤ)-f uv.1 uv.2 := by
  obtain ⟨k,p,rfl,hp,_⟩ := ResidualSearch.search_shortest c f s t xs h
  intro uv huv
  rw [ResidualAugmentation.arcs_ofFn] at huv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp huv
  exact (hp.2.2.2 i).le

end ContingencyTables.FlowMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowLoopProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded residual-flow loop -/

namespace ContingencyTables.FlowLoopProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev Context := NatMatrix×(ℕ×ℕ)

def cube (n : ℕ) : ℕ := n*n*n

def iterationCount (C : NatMatrix) : ℕ := cube C.length+1

def steps (C : NatMatrix) : List ℕ := List.range (iterationCount C)

end ContingencyTables.FlowLoopProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LayeredTableNetwork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source-row-column-sink network for bounded tables

The only nonzero capacities are the three layers prescribed in the
manuscript. Both antiparallel orientations are stored as one skew flow.
-/

namespace ContingencyTables.LayeredTableNetwork

open scoped BigOperators

abbrev Vertex (m n : ℕ) := Bool ⊕ (Fin m ⊕ Fin n)

variable {m n : ℕ}

def source : Vertex m n := Sum.inl false
def sink : Vertex m n := Sum.inl true
def row (i : Fin m) : Vertex m n := Sum.inr (Sum.inl i)
def column (j : Fin n) : Vertex m n := Sum.inr (Sum.inr j)

def capacity (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℕ
  | .inl false,.inr (.inl i) => r i
  | .inr (.inl i),.inr (.inr j) => b i j
  | .inr (.inr j),.inl true => c j
  | _,_ => 0

def Feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : Vertex m n → Vertex m n → ℤ) : Prop :=
  (∀ u v,f u v= -f v u) ∧
  (∀ u v,f u v ≤ capacity r c b u v) ∧
  ∀ u,u≠source → u≠sink → (∑ v,f u v)=0

def value (f : Vertex m n → Vertex m n → ℤ) : ℤ := ∑ v,f source v

def tableFlow (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℤ
  | .inl false,.inr (.inl i) => r i
  | .inr (.inl i),.inl false => -(r i:ℤ)
  | .inr (.inl i),.inr (.inr j) => X i j
  | .inr (.inr j),.inr (.inl i) => -(X i j:ℤ)
  | .inr (.inr j),.inl true => c j
  | .inl true,.inr (.inr j) => -(c j:ℤ)
  | _,_ => 0

lemma capacity_diagonal (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (v : Vertex m n) : capacity r c b v v=0 := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · rfl
  · rfl

lemma tableFlow_skew (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Fin m → Fin n → ℕ) :
    ∀ u v,tableFlow r c X u v= -tableFlow r c X v u := by
  rintro (a | i | j) (d | k | l)
  all_goals (try cases a) <;> (try cases d) <;> simp [tableFlow]

theorem tableFlow_feasible (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b X : Fin m → Fin n → ℕ) (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    Feasible r c b (tableFlow r c X) := by
  refine ⟨tableFlow_skew r c X,?_,?_⟩
  · rintro (a | i | j) (d | k | l)
    all_goals (try cases a) <;> (try cases d) <;> simp [tableFlow,capacity]
    all_goals exact_mod_cast hb _ _
  · rintro (a | i | j) hs ht
    · cases a
      · exact False.elim (hs rfl)
      · exact False.elim (ht rfl)
    · have h : (∑ j,(X i j:ℤ))=(r i:ℤ) := by exact_mod_cast hm.1 i
      simp [Fintype.sum_sum_type,tableFlow,h]
    · have h : (∑ i,(X i j:ℤ))=(c j:ℤ) := by exact_mod_cast hm.2 j
      simp [Fintype.sum_sum_type,tableFlow,h]

theorem tableFlow_value (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : Fin m → Fin n → ℕ) : value (tableFlow r c X)=∑ i,(r i:ℤ) := by
  simp [value,source,tableFlow,Fintype.sum_sum_type]

lemma zero_of_no_capacity (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (u v : Vertex m n)
    (huv : capacity r c b u v=0) (hvu : capacity r c b v u=0) : f u v=0 := by
  have h1 := hf.2.1 u v
  have h2 := hf.2.1 v u
  rw [huv] at h1
  rw [hvu] at h2
  have hs := hf.1 u v
  omega

lemma row_column_nonnegative (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (i : Fin m) (j : Fin n) : 0≤f (row i) (column j) := by
  have h := hf.2.1 (column j) (row i)
  have hs := hf.1 (row i) (column j)
  change f (column j) (row i)≤(0:ℤ) at h
  omega

lemma source_value (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) : value f=∑ i,f source (row i) := by
  have hss : f source source=0 := by have h:=hf.1 source source; omega
  have hst : f source sink=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hsc : ∀ j,f source (column j)=0 := fun j=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  simp only [source,sink,column] at hss hst hsc
  simp [value,source,row,Fintype.sum_sum_type,hss,hst,hsc]

theorem value_le_total (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) : value f≤∑ i,(r i:ℤ) := by
  rw [source_value r c b f hf]
  exact Finset.sum_le_sum (fun i _=>hf.2.1 source (row i))

lemma row_balance (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (i : Fin m) :
    (∑ j,f (row i) (column j))=f source (row i) := by
  have hr : ∀ k,f (row i) (row k)=0 := fun k=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  have ht : f (row i) sink=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hs := hf.1 (row i) source
  have h := hf.2.2 (row i) (by simp [row,source]) (by simp [row,sink])
  have he : (∑ v,f (row i) v)=f (row i) source+(∑ j,f (row i) (column j)) := by
    simp only [row,sink] at hr ht
    simp [Fintype.sum_sum_type,source,row,column,hr,ht]
  rw [he] at h
  omega

lemma column_balance (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (j : Fin n) :
    (∑ i,f (row i) (column j))=f (column j) sink := by
  have hc : ∀ k,f (column j) (column k)=0 := fun k=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hs : f (column j) source=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hneg : ∀ i,f (column j) (row i)= -f (row i) (column j) :=
    fun i=>hf.1 _ _
  have h := hf.2.2 (column j) (by simp [column,source]) (by simp [column,sink])
  have he : (∑ v,f (column j) v)=f (column j) sink-(∑ i,f (row i) (column j)) := by
    simp only [row,column,source] at hc hs hneg
    simp [Fintype.sum_sum_type,sink,row,column,hc,hs,hneg,sub_eq_add_neg]
  rw [he] at h
  omega

lemma saturation {q : ℕ} (f g : Fin q → ℤ) (hfg : ∀ i,f i≤g i)
    (hs : (∑ i,f i)=∑ i,g i) : ∀ i,f i=g i := by
  have hsum : (∑ i,(g i-f i))=0 := by
    rw [Finset.sum_sub_distrib,hs]
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>sub_nonneg.mpr (hfg i))).mp hsum
  intro i
  have hi := hz i (Finset.mem_univ i)
  omega

lemma source_saturated (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ)) :
    ∀ i,f source (row i)=r i := by
  apply saturation
  · intro i
    exact hf.2.1 source (row i)
  · simpa only [source_value r c b f hf] using hv

lemma column_saturated (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ))
    (htotal : (∑ i,r i)=∑ j,c j) :
    ∀ j,f (column j) sink=c j := by
  apply saturation
  · intro j
    exact hf.2.1 (column j) sink
  · calc
      (∑ j,f (column j) sink) = ∑ j,∑ i,f (row i) (column j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (column_balance r c b f hf j).symm
      _ = ∑ i,∑ j,f (row i) (column j) := Finset.sum_comm
      _ = ∑ i,(r i:ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (row_balance r c b f hf i).trans (source_saturated r c b f hf hv i)
      _ = ∑ j,(c j:ℤ) := by exact_mod_cast htotal

def decode (f : Vertex m n → Vertex m n → ℤ) (i : Fin m) (j : Fin n) : ℕ :=
  (f (row i) (column j)).toNat

theorem decode_boundedTable (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ))
    (htotal : (∑ i,r i)=∑ j,c j) :
    HasMargins (decode f) r c ∧ ∀ i j,decode f i j≤b i j := by
  have hd : ∀ i j,(decode f i j:ℤ)=f (row i) (column j) := fun i j=>
    Int.toNat_of_nonneg (row_column_nonnegative r c b f hf i j)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    have he : (∑ j,(decode f i j:ℤ))=(r i:ℤ) := by
      simp only [hd]
      exact (row_balance r c b f hf i).trans (source_saturated r c b f hf hv i)
    exact_mod_cast he
  · intro j
    have he : (∑ i,(decode f i j:ℤ))=(c j:ℤ) := by
      simp only [hd]
      exact (column_balance r c b f hf j).trans
        (column_saturated r c b f hf hv htotal j)
    exact_mod_cast he
  · intro i j
    have he := hf.2.1 (row i) (column j)
    change f (row i) (column j)≤(b i j:ℤ) at he
    rw [←hd] at he
    exact_mod_cast he

end ContingencyTables.LayeredTableNetwork

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedTableFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed bounded-table feasibility from the cited flow bound

The test runs the concrete residual algorithm on the literal three-layer
network. It handles zero margins, empty row or column types, and structural
zeros. No bounded-table feasibility oracle is assumed.
-/

namespace ContingencyTables.BoundedTableFeasibility

open LayeredTableNetwork
open scoped BigOperators

def vertices (m n : ℕ) : Vertex m n ≃ Fin (2+(m+n)) :=
  (Equiv.sumCongr finTwoEquiv.symm finSumFinEquiv).trans finSumFinEquiv

variable {m n : ℕ}

def networkCapacity (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    PublishedEdmondsKarp.Capacity (2+(m+n)) :=
  fun u v=>capacity r c b ((vertices m n).symm u) ((vertices m n).symm v)

def pull (f : PublishedEdmondsKarp.Flow (2+(m+n))) : Vertex m n → Vertex m n → ℤ :=
  fun u v=>f (vertices m n u) (vertices m n v)

def push (f : Vertex m n → Vertex m n → ℤ) : PublishedEdmondsKarp.Flow (2+(m+n)) :=
  fun u v=>f ((vertices m n).symm u) ((vertices m n).symm v)

lemma source_ne_sink : vertices m n (source : Vertex m n)≠vertices m n sink := by
  intro h
  have he := (vertices m n).injective h
  cases he

lemma capacity_loop (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (u : Fin (2+(m+n))) : networkCapacity r c b u u=0 :=
  capacity_diagonal r c b _

lemma pull_feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : PublishedEdmondsKarp.Flow (2+(m+n)))
    (hf : PublishedEdmondsKarp.Feasible (networkCapacity r c b)
      (vertices m n source) (vertices m n sink) f) : Feasible r c b (pull f) := by
  refine ⟨fun u v=>hf.1 _ _,?_,?_⟩
  · intro u v
    simpa only [pull,networkCapacity,Equiv.symm_apply_apply] using hf.2.1
      (vertices m n u) (vertices m n v)
  · intro u hs ht
    have h := hf.2.2 (vertices m n u)
      (fun he=>hs ((vertices m n).injective he))
      (fun he=>ht ((vertices m n).injective he))
    simpa only [pull,(vertices m n).sum_comp] using h

lemma push_feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : Vertex m n → Vertex m n → ℤ) (hf : Feasible r c b f) :
    PublishedEdmondsKarp.Feasible (networkCapacity r c b)
      (vertices m n source) (vertices m n sink) (push f) := by
  refine ⟨fun u v=>hf.1 _ _,fun u v=>hf.2.1 _ _,?_⟩
  intro u hs ht
  have h := hf.2.2 ((vertices m n).symm u)
    (fun he=>hs ((vertices m n).symm_apply_eq.mp he))
    (fun he=>ht ((vertices m n).symm_apply_eq.mp he))
  simpa only [push,(vertices m n).symm.sum_comp] using h

lemma pull_value (f : PublishedEdmondsKarp.Flow (2+(m+n))) :
    value (pull f)=PublishedEdmondsKarp.value (vertices m n source) f := by
  exact (vertices m n).sum_comp (fun v=>f (vertices m n source) v)

lemma push_value (f : Vertex m n → Vertex m n → ℤ) :
    PublishedEdmondsKarp.value (vertices m n source) (push f)=value f := by
  simp only [PublishedEdmondsKarp.value,push,Equiv.symm_apply_apply]
  exact (vertices m n).symm.sum_comp (fun v=>f source v)

def computedFlow (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℤ :=
  pull (EdmondsKarpAlgorithm.maxFlow (networkCapacity r c b)
    (vertices m n source) (vertices m n sink))

def feasibleTest (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) : Bool :=
  decide ((∑ i,r i)=∑ j,c j ∧ value (computedFlow r c b)=∑ i,(r i:ℤ))

end ContingencyTables.BoundedTableFeasibility

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NetworkVertexCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit source/row/column/sink indices for the executed network -/

namespace ContingencyTables.NetworkVertexCode

open LayeredTableNetwork ResidualGraphProgram

variable {m n : ℕ}

/-- Source and sink occupy zero and one, then rows and columns. -/
def index : Vertex m n→ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr (.inl i) => 2+i.val
  | .inr (.inr j) => 2+m+j.val

def tag : Vertex m n→ℕ
  | .inl false => 0
  | .inl true => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 3

def kind (m k : ℕ) : ℕ :=
  if k=0 then 0 else if k=1 then 1 else if k<2+m then 2 else 3

lemma kind_index (v : Vertex m n) : kind m (index v)=tag v := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · have h0 : 2+i.val≠0 := by omega
    have h1 : 2+i.val≠1 := by omega
    have h2 : 2+i.val<2+m := by have hi := i.isLt; omega
    simp only [index,tag,kind,h0,h1,h2,ite_false,ite_true, if_true]
  · have h0 : 2+m+j.val≠0 := by omega
    have h1 : 2+m+j.val≠1 := by omega
    have h2 : ¬2+m+j.val<2+m := by omega
    simp only [index,tag,kind,h0,h1,h2,ite_false]

lemma index_vertices (v : Vertex m n) :
    (BoundedTableFeasibility.vertices m n v).val=index v := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · simp [BoundedTableFeasibility.vertices,index,finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
  · simp [BoundedTableFeasibility.vertices,index,
      finSumFinEquiv_apply_right,Nat.add_assoc]

abbrev Input := (List ℕ×List ℕ)×NatMatrix

def entry (z : Input×(ℕ×ℕ)) : ℕ :=
  let ku := kind z.1.1.1.length z.2.1
  let kv := kind z.1.1.1.length z.2.2
  if ku=0 ∧ kv=2 then z.1.1.1.getD (z.2.2-2) 0
  else if ku=2 ∧ kv=3 then capacityEntry (z.1.2,(z.2.1-2,z.2.2-(2+z.1.1.1.length)))
  else if ku=3 ∧ kv=1 then z.1.1.2.getD (z.2.1-(2+z.1.1.1.length)) 0
  else 0

def data (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) : Input :=
  ((List.ofFn r,List.ofFn c),natCode b)

lemma entry_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (u v : Vertex m n) :
    entry (data r c b,(index u,index v))=capacity r c b u v := by
  have he : (data r c b).1.1.length=m := by simp [data]
  have hcol (k : ℕ) : 2+(m+k)-(2+m)=k := by omega
  simp only [entry,he,kind_index]
  rcases u with a | (i | j) <;> rcases v with d | (k | l)
  all_goals (try cases a) <;> (try cases d)
  all_goals simp [tag,index,data,capacity,capacityEntry,natCode,
    List.getD_eq_getElem?_getD,
    Nat.add_assoc,hcol]

def vertexCount (z : Input) : ℕ := 2+(z.1.1.length+z.1.2.length)

def matrix (z : Input) : NatMatrix :=
  (List.range (vertexCount z)).map (fun u=>
    (List.range (vertexCount z)).map (fun v=>entry (z,(u,v))))

lemma matrix_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    matrix (data r c b)=natCode (BoundedTableFeasibility.networkCapacity r c b) := by
  have hn : vertexCount (data r c b)=2+(m+n) := by simp [vertexCount,data]
  simp only [matrix,hn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have hu : u.val=index ((BoundedTableFeasibility.vertices m n).symm u) := by
    rw [←index_vertices,Equiv.apply_symm_apply]
  have hv : v.val=index ((BoundedTableFeasibility.vertices m n).symm v) := by
    rw [←index_vertices,Equiv.apply_symm_apply]
  simp only [Function.comp_apply,hu,hv]
  exact entry_code r c b _ _

end ContingencyTables.NetworkVertexCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkCapacityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded-table capacity network in binary -/

namespace ContingencyTables.NetworkCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram

abbrev EntryInput := Input×(ℕ×ℕ)

def rowCount (z : EntryInput) : ℕ := z.1.1.1.length

def columnBase (z : EntryInput) : ℕ := 2+rowCount z

def kinds (z : EntryInput) : ℕ×ℕ :=
  (kind (rowCount z) z.2.1,kind (rowCount z) z.2.2)

def pattern (a b : ℕ) (z : EntryInput) : Bool :=
  decide ((kinds z).1=a) && decide ((kinds z).2=b)

def rowRead (z : EntryInput) : ℕ := z.1.1.1.getD (z.2.2-2) 0

def columnRead (z : EntryInput) : ℕ := z.1.1.2.getD (z.2.1-columnBase z) 0

def boundRead (z : EntryInput) : ℕ :=
  capacityEntry (z.1.2,(z.2.1-2,z.2.2-columnBase z))

def vertices (z : Input) : List ℕ := List.range (vertexCount z)

def row (z : Input×ℕ) : List ℕ :=
  (vertices z.1).map (fun v=>entry (z.1,(z.2,v)))

end ContingencyTables.NetworkCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedTableComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complementing a bounded table

The map X ↦ b-X transforms cell minima into maxima. All margin
subtractions are justified by an actual feasible table.
-/

namespace ContingencyTables.BoundedTableComplement

open scoped BigOperators

variable {m n : ℕ}

def complement (b X : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := b i j-X i j

def rowTotal (b : Fin m→Fin n→ℕ) (i : Fin m) : ℕ := ∑ j,b i j
def columnTotal (b : Fin m→Fin n→ℕ) (j : Fin n) : ℕ := ∑ i,b i j

def rows (b : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (i : Fin m) : ℕ := rowTotal b i-r i
def columns (b : Fin m→Fin n→ℕ) (c : Fin n→ℕ) (j : Fin n) : ℕ := columnTotal b j-c j

lemma complement_bounds (b X : Fin m→Fin n→ℕ) :
    ∀ i j,complement b X i j≤b i j := fun _ _=>Nat.sub_le _ _

lemma complement_margins (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    HasMargins (complement b X) (rows b r) (columns b c) := by
  constructor
  · intro i
    have hs : (∑ j,complement b X i j)+(∑ j,X i j)=rowTotal b i := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (hb i j)
    rw [hm.1 i] at hs
    unfold rows
    omega
  · intro j
    have hs : (∑ i,complement b X i j)+(∑ i,X i j)=columnTotal b j := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (hb i j)
    rw [hm.2 j] at hs
    unfold columns
    omega

lemma row_total_ge (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) (i : Fin m) :
    r i ≤ rowTotal b i := by
  rw [←hm.1 i]
  exact Finset.sum_le_sum (fun j _=>hb i j)

lemma column_total_ge (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) (j : Fin n) :
    c j ≤ columnTotal b j := by
  rw [←hm.2 j]
  exact Finset.sum_le_sum (fun i _=>hb i j)

lemma margins_twice (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    rows b (rows b r)=r ∧ columns b (columns b c)=c := by
  constructor
  · funext i
    exact Nat.sub_sub_self (row_total_ge b X r c hm hb i)
  · funext j
    exact Nat.sub_sub_self (column_total_ge b X r c hm hb j)

lemma complement_reverse_margins (b X Y : Fin m→Fin n→ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (hx : HasMargins X r c) (hxb : ∀ i j,X i j≤b i j)
    (hy : HasMargins Y (rows b r) (columns b c)) (hyb : ∀ i j,Y i j≤b i j) :
    HasMargins (complement b Y) r c := by
  have h := complement_margins b Y (rows b r) (columns b c) hy hyb
  obtain ⟨hr,hc⟩ := margins_twice b X r c hx hxb
  rwa [hr,hc] at h

end ContingencyTables.BoundedTableComplement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedComplementProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing complementary bounded-table margins in binary -/

namespace ContingencyTables.BoundedComplementProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode

abbrev EntryInput := Input×ℕ

def rowValue (z : EntryInput) : ℕ :=
  (z.1.2.getD z.2 []).sum-z.1.1.1.getD z.2 0

def columnValues (z : EntryInput) : List ℕ := z.1.2.map (fun row=>row.getD z.2 0)

def columnValue (z : EntryInput) : ℕ :=
  (columnValues z).sum-z.1.1.2.getD z.2 0

def rowIndices (z : Input) : List ℕ := List.range z.1.1.length
def columnIndices (z : Input) : List ℕ := List.range z.1.2.length

def complement (z : Input) : Input :=
  (((rowIndices z).map (fun i=>rowValue (z,i)),
    (columnIndices z).map (fun j=>columnValue (z,j))),z.2)

lemma rowValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (i : Fin m) :
    rowValue (data r c b,i.val)=BoundedTableComplement.rows b r i := by
  simp only [rowValue,data,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,
    BoundedTableComplement.rows,BoundedTableComplement.rowTotal]

lemma columnValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (j : Fin n) :
    columnValue (data r c b,j.val)=BoundedTableComplement.columns b c j := by
  simp only [columnValue,columnValues,data,ResidualGraphProgram.natCode,List.map_ofFn,
    Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,
    dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,
    BoundedTableComplement.columns,BoundedTableComplement.columnTotal]

lemma complement_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    complement (data r c b)=data (BoundedTableComplement.rows b r)
      (BoundedTableComplement.columns b c) b := by
  unfold complement
  apply Prod.ext
  · apply Prod.ext
    · simp only [rowIndices,data,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
        List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact rowValue_code r c b i
    · simp only [columnIndices,data,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
        List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      exact columnValue_code r c b j
  · rfl

end ContingencyTables.BoundedComplementProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedBinarySearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary search for the attained endpoint of a monotone feasibility test

A fixed number of midpoint tests finds a known cutoff. The number of
tests is logarithmic in the binary upper bound; no values are enumerated.
-/

namespace ContingencyTables.BoundedBinarySearch

abbrev Window := ℕ×ℕ

def midpoint (p : Window) : ℕ := p.1+(p.2-p.1+1)/2

def step (test : ℕ→Bool) (p : Window) : Window :=
  if test (midpoint p) then (midpoint p,p.2) else (p.1,midpoint p-1)

def run (test : ℕ→Bool) : ℕ→Window→Window
  | 0,p => p
  | k+1,p => run test k (step test p)

lemma step_width (test : ℕ→Bool) (p : Window) :
    2*((step test p).2-(step test p).1)≤p.2-p.1 := by
  rcases p with ⟨lo,hi⟩
  unfold step midpoint
  split_ifs <;> dsimp only <;> omega

lemma run_width (test : ℕ→Bool) (k : ℕ) (p : Window) :
    ((run test k p).2-(run test k p).1)*2^k≤p.2-p.1 := by
  induction k generalizing p with
  | zero => simp [run]
  | succ k ih =>
    have h := ih (step test p)
    have hs := step_width test p
    change ((run test k (step test p)).2-(run test k (step test p)).1)*2^(k+1)≤_
    calc
      _ = (((run test k (step test p)).2-(run test k (step test p)).1)*2^k)*2 := by
        rw [pow_succ]
        ring
      _ ≤ ((step test p).2-(step test p).1)*2 := Nat.mul_le_mul_right 2 h
      _ ≤ p.2-p.1 := by simpa only [Nat.mul_comm] using hs

lemma step_contains (test : ℕ→Bool) (K : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (p : Window)
    (hlo : p.1≤K) (hhi : K≤p.2) :
    (step test p).1≤K ∧ K≤(step test p).2 := by
  unfold step
  split_ifs with h
  · exact ⟨(ht _).mp h,hhi⟩
  · have hm : K < midpoint p := by
      by_contra hn
      exact h ((ht _).mpr (by omega))
    exact ⟨hlo,by dsimp only;omega⟩

lemma run_contains (test : ℕ→Bool) (K : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (k : ℕ) (p : Window)
    (hlo : p.1≤K) (hhi : K≤p.2) :
    (run test k p).1≤K ∧ K≤(run test k p).2 := by
  induction k generalizing p with
  | zero => exact ⟨hlo,hhi⟩
  | succ k ih =>
    have hs := step_contains test K ht p hlo hhi
    exact ih (step test p) hs.1 hs.2

theorem run_eq_cutoff (test : ℕ→Bool) (K U k : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (hK : K≤U) (hk : U<2^k) :
    run test k (0,U)=(K,K) := by
  have hb := run_contains test K ht k (0,U) (Nat.zero_le _) hK
  have hw := run_width test k (0,U)
  have hz : (run test k (0,U)).2-(run test k (0,U)).1=0 := by
    simp only [Nat.sub_zero] at hw
    by_contra hn
    have hp : 1≤(run test k (0,U)).2-(run test k (0,U)).1 := by omega
    have hm := Nat.mul_le_mul_right (2^k) hp
    nlinarith
  apply Prod.ext <;> dsimp only <;> omega

end ContingencyTables.BoundedBinarySearch

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedCellShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A literal one-cell lower-bound reduction

Requiring the selected entry to be at least t is equivalent to subtracting
t from that entry, its incident margins and its capacity. The three guards
are retained explicitly, including for zero margins and structural zeros.
-/

namespace ContingencyTables.BoundedCellShift

open scoped BigOperators

variable {m n : ℕ}

def margin (r : Fin m→ℕ) (i₀ : Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  if i=i₀ then r i-t else r i

def lower (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  if i=i₀ ∧ j=j₀ then X i j-t else X i j

def raise (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  X i j+if i=i₀ ∧ j=j₀ then t else 0

lemma raise_lower (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (ht : t≤X i₀ j₀) : raise (lower X i₀ j₀ t) i₀ j₀ t=X := by
  funext i j
  by_cases hi : i=i₀ <;> by_cases hj : j=j₀
  · subst i; subst j
    simpa only [raise,lower,ite_true, if_true,true_and,add_zero] using Nat.sub_add_cancel ht
  all_goals simp [lower,raise,hi,hj]

lemma raise_row_sum (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (i : Fin m) :
    (∑ j,raise X i₀ j₀ t i j)=(∑ j,X i j)+if i=i₀ then t else 0 := by
  by_cases hi : i=i₀
  · subst i
    simp [raise,Finset.sum_add_distrib]
  · simp [raise,hi]

lemma raise_column_sum (X : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (j : Fin n) :
    (∑ i,raise X i₀ j₀ t i j)=(∑ i,X i j)+if j=j₀ then t else 0 := by
  by_cases hj : j=j₀
  · subst j
    simp [raise,Finset.sum_add_distrib]
  · simp [raise,hj]

lemma lower_margins (X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) (hm : HasMargins X r c)
    (ht : t≤X i₀ j₀) :
    HasMargins (lower X i₀ j₀ t) (margin r i₀ t) (margin c j₀ t) := by
  have he := raise_lower X i₀ j₀ t ht
  constructor
  · intro i
    by_cases hi : i=i₀
    · subst i
      have hs := raise_row_sum (lower X i₀ j₀ t) i₀ j₀ t i₀
      rw [he,hm.1 i₀] at hs
      simp only [ite_true, if_true] at hs
      simp only [margin,ite_true, if_true]
      omega
    · have hs := raise_row_sum (lower X i₀ j₀ t) i₀ j₀ t i
      rw [he,hm.1 i] at hs
      simpa only [margin,hi,ite_false,Nat.add_zero] using hs.symm
  · intro j
    by_cases hj : j=j₀
    · subst j
      have hs := raise_column_sum (lower X i₀ j₀ t) i₀ j₀ t j₀
      rw [he,hm.2 j₀] at hs
      simp only [ite_true, if_true] at hs
      simp only [margin,ite_true, if_true]
      omega
    · have hs := raise_column_sum (lower X i₀ j₀ t) i₀ j₀ t j
      rw [he,hm.2 j] at hs
      simpa only [margin,hj,ite_false,Nat.add_zero] using hs.symm

lemma raise_margins (Y : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (i₀ : Fin m) (j₀ : Fin n) (t : ℕ)
    (hr : t ≤ r i₀) (hc : t ≤ c j₀)
    (hm : HasMargins Y (margin r i₀ t) (margin c j₀ t)) :
    HasMargins (raise Y i₀ j₀ t) r c := by
  constructor
  · intro i
    rw [raise_row_sum,hm.1 i]
    by_cases hi : i=i₀
    · subst i
      simpa [margin] using Nat.sub_add_cancel hr
    · simp [margin,hi]
  · intro j
    rw [raise_column_sum,hm.2 j]
    by_cases hj : j=j₀
    · subst j
      simpa [margin] using Nat.sub_add_cancel hc
    · simp [margin,hj]

lemma lower_bounds (X b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (hb : ∀ i j,X i j≤b i j) :
    ∀ i j,lower X i₀ j₀ t i j≤lower b i₀ j₀ t i j := by
  intro i j
  unfold lower
  split_ifs
  · exact Nat.sub_le_sub_right (hb i j) t
  · exact hb i j

lemma raise_bounds (Y b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n)
    (t : ℕ) (ht : t≤b i₀ j₀)
    (hb : ∀ i j,Y i j≤lower b i₀ j₀ t i j) :
    ∀ i j,raise Y i₀ j₀ t i j≤b i j := by
  intro i j
  have h := hb i j
  by_cases hi : i=i₀ <;> by_cases hj : j=j₀
  · subst i; subst j
    simp only [lower,ite_true, if_true,true_and] at h
    simp only [raise,ite_true, if_true,true_and]
    omega
  all_goals simpa [raise,lower,hi,hj] using h

theorem feasible_lower_iff (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) :
    (∃ X,HasMargins X r c ∧ (∀ i j,X i j≤b i j) ∧ t≤X i₀ j₀) ↔
      t ≤ r i₀ ∧ t ≤ c j₀ ∧ t≤b i₀ j₀ ∧
      ∃ Y,HasMargins Y (margin r i₀ t) (margin c j₀ t) ∧
        ∀ i j,Y i j≤lower b i₀ j₀ t i j := by
  constructor
  · rintro ⟨X,hm,hb,ht⟩
    have hc : X i₀ j₀ ≤ c j₀ := by
      rw [←hm.2 j₀]
      exact Finset.single_le_sum (f := fun i=>X i j₀) (fun _ _=>Nat.zero_le _)
        (Finset.mem_univ i₀)
    exact ⟨ht.trans (entry_le_row hm i₀ j₀),ht.trans hc,ht.trans (hb i₀ j₀),
      lower X i₀ j₀ t,lower_margins X r c i₀ j₀ t hm ht,lower_bounds X b i₀ j₀ t hb⟩
  · rintro ⟨hr,hc,hb,Y,hm,hy⟩
    refine ⟨raise Y i₀ j₀ t,raise_margins Y r c i₀ j₀ t hr hc hm,
      raise_bounds Y b i₀ j₀ t hb hy,?_⟩
    simp only [raise,ite_true, if_true,true_and]
    omega

end ContingencyTables.BoundedCellShift

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListSubtractProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary subtraction at one list coordinate

The scan depends on the stored list length. The subtracted amount remains
binary throughout and never controls a loop.
-/

namespace ContingencyTables.ListSubtractProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Input := (List ℕ×ℕ)×ℕ
abbrev Cell := Input×ℕ

def entry (z : Cell) : ℕ :=
  z.1.1.1.getD z.2 0-if z.2=z.1.1.2 then z.1.2 else 0

def indices (z : Input) : List ℕ := List.range z.1.1.length

def subtractAt (z : Input) : List ℕ :=
  (indices z).map (fun i=>entry (z,i))

lemma subtractAt_ofFn {m : ℕ} (x : Fin m→ℕ) (i : Fin m) (t : ℕ) :
    subtractAt ((List.ofFn x,i.val),t)=List.ofFn (BoundedCellShift.margin x i t) := by
  simp only [subtractAt,indices,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [entry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,BoundedCellShift.margin]
  by_cases h : j=i
  · subst j
    simp
  · have hn : j.val≠i.val := fun he=>h (Fin.ext he)
    simp [h,hn]

end ContingencyTables.ListSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LowerCapacityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable subtraction of a lower bound from a capacity matrix -/

namespace ContingencyTables.LowerCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev Input := (NatMatrix×(ℕ×ℕ))×ℕ
abbrev RowInput := Input×ℕ

def readRow (z : RowInput) : List ℕ := z.1.1.1.getD z.2 []

def selected (z : RowInput) : Bool := decide (z.2=z.1.1.2.1)

def shiftedInput (z : RowInput) : ListSubtractProgram.Input :=
  ((readRow z,z.1.1.2.2),z.1.2)

def row (z : RowInput) : List ℕ :=
  if z.2=z.1.1.2.1 then ListSubtractProgram.subtractAt (shiftedInput z) else readRow z

def indices (z : Input) : List ℕ := List.range z.1.1.length

def matrix (z : Input) : NatMatrix := (indices z).map (fun i=>row (z,i))

lemma matrix_code {m n : ℕ} (b : Fin m→Fin n→ℕ) (i₀ : Fin m) (j₀ : Fin n) (t : ℕ) :
    matrix ((natCode b,(i₀.val,j₀.val)),t)=natCode (BoundedCellShift.lower b i₀ j₀ t) := by
  simp only [matrix,indices,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  have hr : readRow ((((List.ofFn (fun i=>List.ofFn (b i)),(i₀.val,j₀.val)),t),i.val))=
      List.ofFn (b i) := by
    simp only [readRow,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
      dite_true,Option.getD_some,Fin.eta]
  by_cases hi : i=i₀
  · subst i
    simp only [row,ite_true, if_true,shiftedInput,hr]
    rw [ListSubtractProgram.subtractAt_ofFn]
    apply congrArg List.ofFn
    funext j
    simp [BoundedCellShift.margin,BoundedCellShift.lower]
  · have hn : i.val≠i₀.val := fun he=>hi (Fin.ext he)
    simp only [row,hn,ite_false,hr]
    apply congrArg List.ofFn
    funext j
    simp [BoundedCellShift.lower,hi]

end ContingencyTables.LowerCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellLowerTestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed feasibility test with one extra lower cell bound -/

namespace ContingencyTables.CellLowerTestProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Context := NetworkVertexCode.Input×(ℕ×ℕ)
abbrev Input := Context×ℕ

def shifted (z : Input) : NetworkVertexCode.Input :=
  ((ListSubtractProgram.subtractAt ((z.1.1.1.1,z.1.2.1),z.2),
    ListSubtractProgram.subtractAt ((z.1.1.1.2,z.1.2.2),z.2)),
    LowerCapacityProgram.matrix ((z.1.1.2,z.1.2),z.2))

def guards (z : Input) : Bool :=
  decide (z.2≤z.1.1.1.1.getD z.1.2.1 0) &&
    (decide (z.2≤z.1.1.1.2.getD z.1.2.2 0) &&
      decide (z.2≤ResidualGraphProgram.capacityEntry (z.1.1.2,z.1.2)))

lemma shifted_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    shifted ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=
      NetworkVertexCode.data (BoundedCellShift.margin r i t)
        (BoundedCellShift.margin c j t) (BoundedCellShift.lower b i j t) := by
  unfold shifted NetworkVertexCode.data
  rw [ListSubtractProgram.subtractAt_ofFn,ListSubtractProgram.subtractAt_ofFn,
    LowerCapacityProgram.matrix_code]

lemma guards_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    guards ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔
      t ≤ r i ∧ t ≤ c j ∧ t≤b i j := by
  dsimp only [guards, NetworkVertexCode.data]
  rw [ResidualGraphProgram.capacityEntry_code]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Bool.and_eq_true]
  constructor
  · rintro ⟨hr,hc,hb⟩
    exact ⟨_root_.of_decide_eq_true hr,_root_.of_decide_eq_true hc,_root_.of_decide_eq_true hb⟩
  · rintro ⟨hr,hc,hb⟩
    exact ⟨_root_.decide_eq_true hr,_root_.decide_eq_true hc,_root_.decide_eq_true hb⟩

end ContingencyTables.CellLowerTestProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained cell maximum by binary feasibility search

A finite maximum is used only to prove the result of the executed binary
search. The program never enumerates feasible tables.
-/

namespace ContingencyTables.CellMaximumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram
open scoped Classical

def bound (z : Context) : ℕ := ResidualGraphProgram.capacityEntry (z.1.2,z.2)

lemma bound_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    bound (NetworkVertexCode.data r c b,(i.val,j.val))=b i j :=
  ResidualGraphProgram.capacityEntry_code b i j

end ContingencyTables.CellMaximumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMinimumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained minimum through the complementary table

Complementation changes the lower endpoint query to the
upper endpoint query and preserves every cell capacity.
-/

namespace ContingencyTables.CellMinimumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram

def complemented (z : Context) : Context := (BoundedComplementProgram.complement z.1,z.2)

lemma complemented_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    complemented (NetworkVertexCode.data r c b,(i.val,j.val))=
      (NetworkVertexCode.data (BoundedTableComplement.rows b r)
        (BoundedTableComplement.columns b c) b,(i.val,j.val)) := by
  unfold complemented
  rw [BoundedComplementProgram.complement_code]

end ContingencyTables.CellMinimumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_EndpointMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every attained cell endpoint

Both scans use the dimensions of the stored margin lists. Each entry is
computed by the binary feasibility search; neither scan enumerates tables.
-/

namespace ContingencyTables.EndpointMatrixProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev Input := NetworkVertexCode.Input
abbrev RowInput := Input × ℕ
abbrev CellInput := RowInput × ℕ

def context (z : CellInput) : CellLowerTestProgram.Context := (z.1.1,(z.1.2,z.2))

def columns (z : RowInput) : List ℕ := List.range z.1.1.2.length

def rows (z : Input) : List ℕ := List.range z.1.1.length

end ContingencyTables.EndpointMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting the bounded table from the executed flow

The output reads the row-to-column arcs of the computed flow. Both the
matrix dimensions and the encoded entries are obtained from the input;
there is no choice of a mathematical witness in the program.
-/

namespace ContingencyTables.NetworkTableProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram
open scoped BigOperators

lemma signedParts_toNat (z : ℤ) :
    (ForestAffineProgram.signedParts z).1-(ForestAffineProgram.signedParts z).2=z.toNat := by
  cases z <;> simp [ForestAffineProgram.signedParts]

end ContingencyTables.NetworkTableProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableTightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous tightening and translation by attained cell minima

The hypotheses here are exactly the extremum properties proved for the
executed searches. The maps preserve all tables, with explicit inverse
addition and with both endpoints of every translated interval attained.
-/

namespace ContingencyTables.TableTightening

open scoped BigOperators

variable {m n : ℕ}

def subtract (X l : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := X i j-l i j
def add (Y l : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := Y i j+l i j

def rows (r : Fin m→ℕ) (l : Fin m→Fin n→ℕ) (i : Fin m) : ℕ := r i-∑ j,l i j
def columns (c : Fin n→ℕ) (l : Fin m→Fin n→ℕ) (j : Fin n) : ℕ := c j-∑ i,l i j

def bounds (l u : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := u i j-l i j

lemma subtract_margins (X l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hl : ∀ i j,l i j≤X i j) :
    HasMargins (subtract X l) (rows r l) (columns c l) := by
  constructor
  · intro i
    have he : (∑ j,subtract X l i j)+(∑ j,l i j)=r i := by
      rw [←Finset.sum_add_distrib,←hm.1 i]
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (hl i j)
    unfold rows
    omega
  · intro j
    have he : (∑ i,subtract X l i j)+(∑ i,l i j)=c j := by
      rw [←Finset.sum_add_distrib,←hm.2 j]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (hl i j)
    unfold columns
    omega

variable (r : Fin m→ℕ) (c : Fin n→ℕ) (b l u : Fin m→Fin n→ℕ)

def Feasible (X : Fin m→Fin n→ℕ) : Prop := HasMargins X r c ∧ ∀ i j,X i j≤b i j

def TightFeasible (Y : Fin m→Fin n→ℕ) : Prop :=
  HasMargins Y (rows r l) (columns c l) ∧ ∀ i j,Y i j≤bounds l u i j

/-- A feasible table lies in every attained coordinate interval. -/
theorem subtract_feasible (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ X,Feasible r c b X→∀ i j,X i j≤u i j)
    {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X) :
    TightFeasible r c l u (subtract X l) := by
  refine ⟨subtract_margins X l r c hX.1 (hl X hX),?_⟩
  intro i j
  exact Nat.sub_le_sub_right (hu X hX i j) (l i j)

/-- Both translated endpoints are actual table entries, including when
an interval has width zero. -/
theorem endpoints (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ X,Feasible r c b X→∀ i j,X i j≤u i j)
    (hlo : ∀ i j,∃ X,Feasible r c b X ∧ X i j=l i j)
    (hup : ∀ i j,∃ X,Feasible r c b X ∧ X i j=u i j) :
    (∀ i j,∃ Y,TightFeasible r c l u Y ∧ Y i j=0) ∧
      (∀ i j,∃ Y,TightFeasible r c l u Y ∧ Y i j=bounds l u i j) := by
  constructor
  · intro i j
    obtain ⟨X,hX,he⟩ := hlo i j
    refine ⟨subtract X l,subtract_feasible r c b l u hl hu hX,?_⟩
    simp only [subtract,he,Nat.sub_self]
  · intro i j
    obtain ⟨X,hX,he⟩ := hup i j
    refine ⟨subtract X l,subtract_feasible r c b l u hl hu hX,?_⟩
    simp only [subtract,he,bounds]

end ContingencyTables.TableTightening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TightenedInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed endpoint translation and a feasible tightened baseline

The lower and upper matrices are computed by the endpoint scans. Binary
subtraction updates the capacities and both margins, then the same proved
flow program produces a baseline table in the translated instance.
-/

namespace ContingencyTables.TightenedInputProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram NetworkVertexCode
open scoped BigOperators Classical

abbrev TranslationInput := Input×NatMatrix
abbrev MarginInput := TranslationInput×ℕ
abbrev CellInput := MarginInput×ℕ

def rowValue (z : MarginInput) : ℕ :=
  z.1.1.1.1.getD z.2 0-(z.1.1.2.getD z.2 []).sum

def columnValue (z : MarginInput) : ℕ :=
  z.1.1.1.2.getD z.2 0-(BoundedComplementProgram.columnValues (z.1.1,z.2)).sum

def position (z : CellInput) : ℕ×ℕ := (z.1.2,z.2)

def cellValue (z : CellInput) : ℕ :=
  capacityEntry (z.1.1.2,position z)-capacityEntry (z.1.1.1.2,position z)

def rowIndices (z : TranslationInput) : List ℕ := BoundedComplementProgram.rowIndices z.1

def columnIndices (z : TranslationInput) : List ℕ := BoundedComplementProgram.columnIndices z.1

def capacityRow (z : MarginInput) : List ℕ :=
  (columnIndices z.1).map (fun j=>cellValue (z,j))

def translate (z : TranslationInput) : Input :=
  (((rowIndices z).map (fun i=>rowValue (z,i)),
    (columnIndices z).map (fun j=>columnValue (z,j))),
    (rowIndices z).map (fun i=>capacityRow (z,i)))

lemma rowValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) (i : Fin m) :
    rowValue ((data r c l,natCode u),i.val)=TableTightening.rows r l i := by
  simp only [rowValue,data,natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,TableTightening.rows]

lemma columnValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) (j : Fin n) :
    columnValue ((data r c l,natCode u),j.val)=TableTightening.columns c l j := by
  simp only [columnValue,BoundedComplementProgram.columnValues,data,natCode,List.map_ofFn,
    Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    j.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn,TableTightening.columns]

lemma cellValue_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    cellValue (((data r c l,natCode u),i.val),j.val)=TableTightening.bounds l u i j := by
  change capacityEntry (natCode u,(i.val,j.val))-capacityEntry (natCode l,(i.val,j.val))=_
  rw [capacityEntry_code,capacityEntry_code]
  rfl

lemma translate_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (l u : Fin m→Fin n→ℕ) :
    translate (data r c l,natCode u)=data (TableTightening.rows r l)
      (TableTightening.columns c l) (TableTightening.bounds l u) := by
  unfold translate
  apply Prod.ext
  · apply Prod.ext
    · simp only [rowIndices,BoundedComplementProgram.rowIndices,data,List.length_ofFn,
        DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact rowValue_code r c l u i
    · simp only [columnIndices,BoundedComplementProgram.columnIndices,data,List.length_ofFn,
        DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      exact columnValue_code r c l u j
  · simp only [rowIndices,BoundedComplementProgram.rowIndices,data,List.length_ofFn,
      DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    simp only [capacityRow,columnIndices,BoundedComplementProgram.columnIndices,List.length_ofFn,
      DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact cellValue_code r c l u i j

end ContingencyTables.TightenedInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_WeightedArgmaxProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary scan selecting a greatest weighted edge

The accumulator is either empty or one stored edge. Its binary size is
bounded by the input list size even when capacities are numerically large.
-/

namespace ContingencyTables.WeightedArgmaxProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Edge := (ℕ×ℕ)×ℕ
abbrev Input := Edge×Option Edge

def advance (z : Input) : Option Edge :=
  match z.2 with
  | none => Option.some z.1
  | Option.some old => if old.2<z.1.2 then Option.some z.1 else Option.some old

def best (xs : List Edge) : Option Edge := xs.foldl (fun o e=>advance (e,o)) none

lemma best_argmax (xs : List Edge) : best xs=xs.argmax Prod.snd := by
  have hf : (fun o e=>advance (e,o))=
      List.argAux (fun a b : Edge=>b.2<a.2) := by
    funext o e
    cases o <;> rfl
  unfold best List.argmax
  rw [hf]

lemma best_mem {xs : List Edge} {e : Edge} (he : best xs=some e) : e∈xs := by
  rw [best_argmax] at he
  exact List.argmax_mem he

lemma best_max {xs : List Edge} {e : Edge} (he : best xs=some e)
    {a : Edge} (ha : a∈xs) : a.2≤e.2 := by
  rw [best_argmax] at he
  exact List.le_of_mem_argmax (f := Prod.snd) ha he

lemma best_none (xs : List Edge) : best xs=none ↔ xs=[] := by
  rw [best_argmax,List.argmax_eq_none]

end ContingencyTables.WeightedArgmaxProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestEdgeChoiceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the heaviest edge between distinct forest components

The filter runs the actual finite component-search program. The maximum
scan receives only eligible stored edges and retains their binary weights.
-/

namespace ContingencyTables.ForestEdgeChoiceProgram

open MatchingFPRAS.TreeTyped WeightedArgmaxProgram FiniteGraphRootProgram
open FiniteGraphCutProgram
open scoped Classical

abbrev Input := GraphCode×List Edge
abbrev TestInput := Input×Edge

def query (z : TestInput) : FiniteGraphRootProgram.Input×ℕ :=
  ((z.1.1,z.2.1.1),z.2.1.2)

def eligible (z : TestInput) : Bool := !reachableCode (query z)

def filtered (z : Input) : List Edge := z.2.filter (fun e=>eligible (z,e))

def choice (z : Input) : Option Edge := WeightedArgmaxProgram.best (filtered z)

lemma choice_mem {z : Input} {e : Edge} (he : choice z=some e) :
    e∈z.2 ∧ eligible (z,e)=true :=
  List.mem_filter.mp (WeightedArgmaxProgram.best_mem he)

lemma choice_max {z : Input} {e a : Edge} (he : choice z=some e)
    (ha : a∈z.2) (hel : eligible (z,a)=true) : a.2≤e.2 :=
  WeightedArgmaxProgram.best_max he (List.mem_filter.mpr ⟨ha,hel⟩)

lemma choice_none {z : Input} (he : choice z=none) :
    ∀ e∈z.2,eligible (z,e)=false := by
  have hn : filtered z=[] := (WeightedArgmaxProgram.best_none _).mp he
  intro e he
  cases h : eligible (z,e) with
  | false=>rfl
  | true=>
    have hm : e∈filtered z := List.mem_filter.mpr ⟨he,h⟩
    rw [hn] at hm
    exact (List.not_mem_nil hm).elim

end ContingencyTables.ForestEdgeChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestJoinProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical adjacency-list insertion of a forest edge

Every row is rebuilt from the stored vertex range. This keeps the graph
encoding canonical and bounds all intermediate lists by the vertex count.
-/

namespace ContingencyTables.ForestJoinProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram SimpleGraph

abbrev Input := GraphCode×(ℕ×ℕ)
abbrev RowInput := Input×ℕ
abbrev TestInput := RowInput×ℕ

def keep (z : TestInput) : Bool :=
  decide (z.2∈z.1.1.1.getD z.1.2 []) ||
    ((decide (z.1.2=z.1.1.2.1) && decide (z.2=z.1.1.2.2)) ||
     (decide (z.1.2=z.1.1.2.2) && decide (z.2=z.1.1.2.1)))

def vertices (z : RowInput) : List ℕ := indices z.1.1

def row (z : RowInput) : List ℕ := (vertices z).filter (fun a=>keep (z,a))

def join (z : Input) : GraphCode := (indices z.1).map (fun i=>row (z,i))

end ContingencyTables.ForestJoinProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeEdgeCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weighted catalog of large cells

Rows and columns are indexed by their stored margin-list lengths. The
catalog contains each retained large cell once, with its actual binary
capacity and its row/column graph endpoints.
-/

namespace ContingencyTables.LargeEdgeCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms WeightedArgmaxProgram

abbrev Input := CompanionCellCatalog.Input
abbrev CellInput := Input×(ℕ×ℕ)

def vertexCount (z : Input) : ℕ := z.1.1.1.length+z.1.1.2.length

def endpoints (z : CellInput) : ℕ×ℕ := (z.2.1,z.1.1.1.1.length+z.2.2)

def entry (z : CellInput) : Edge := (endpoints z,CompanionCellCatalog.entry z)

def large (z : CellInput) : Bool := !CompanionCellCatalog.retainedTest z

def cells (z : Input) : List (ℕ×ℕ) :=
  (cellPairs z.1.1).filter (fun a=>large (z,a))

def catalog (z : Input) : List Edge := (cells z).map (fun a=>entry (z,a))

variable {m n : ℕ}

lemma entry_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (i : Fin m) (j : Fin n) :
    entry ((NetworkVertexCode.data r c b,W),(i.val,j.val))=
      ((i.val,m+j.val),b i j) := by
  change ((i.val,(List.ofFn r).length+j.val),matrixEntry (matrixCode b,(i.val,j.val)))=_
  rw [List.length_ofFn,matrixEntry_code]

lemma mem_cells_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (a : ℕ×ℕ) :
    a∈cells (NetworkVertexCode.data r c b,W) ↔
      ∃ i : Fin m,∃ j : Fin n,a=(i.val,j.val) ∧ W≤b i j := by
  rw [cells,List.mem_filter]
  change (a∈cellPairs (List.ofFn r,List.ofFn c) ∧
    large ((NetworkVertexCode.data r c b,W),a)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,ht⟩
    let i : Fin m := ⟨a.1,hi⟩
    let j : Fin n := ⟨a.2,hj⟩
    refine ⟨i,j,rfl,?_⟩
    have hn : ¬CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))<W := by
      simpa only [large,CompanionCellCatalog.retainedTest,Bool.not_eq_true',
        decide_eq_false_iff_not] using ht
    have he : CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))=b i j := matrixEntry_code b i j
    rw [he] at hn
    exact Nat.le_of_not_gt hn
  · rintro ⟨i,j,rfl,hb⟩
    refine ⟨⟨i.isLt,j.isLt⟩,?_⟩
    have he : CompanionCellCatalog.entry
        ((NetworkVertexCode.data r c b,W),(i.val,j.val))=b i j := matrixEntry_code b i j
    simpa only [large,CompanionCellCatalog.retainedTest,Bool.not_eq_true',
      decide_eq_false_iff_not,he] using Nat.not_lt.mpr hb

/-- Exact source cell capacities and graph endpoints, with no finite
choice or supplied catalog-correctness hypothesis. -/
theorem mem_catalog_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (e : Edge) :
    e∈catalog (NetworkVertexCode.data r c b,W) ↔
      ∃ i : Fin m,∃ j : Fin n,W≤b i j ∧ e=((i.val,m+j.val),b i j) := by
  rw [catalog,List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    obtain ⟨i,j,rfl,hb⟩ := (mem_cells_code r c b W a).mp ha
    exact ⟨i,j,hb,he.symm.trans (entry_code r c b W i j)⟩
  · rintro ⟨i,j,hb,rfl⟩
    exact ⟨(i.val,j.val),(mem_cells_code r c b W _).mpr ⟨i,j,rfl,hb⟩,
      entry_code r c b W i j⟩

lemma vertexCount_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    vertexCount (NetworkVertexCode.data r c b,W)=m+n := by
  simp only [vertexCount,NetworkVertexCode.data,List.length_ofFn]

end ContingencyTables.LargeEdgeCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestGreedyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the component-greedy forest loop

The immutable weighted edge catalog is scanned after every insertion.
There are at most the square of the stored vertex count many iterations;
all adjacency rows stay inside that fixed vertex range.
-/

namespace ContingencyTables.ForestGreedyProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram WeightedArgmaxProgram

abbrev State := ForestEdgeChoiceProgram.Input

def insert (z : State×Edge) : GraphCode := ForestJoinProgram.join (z.1.1,z.2.1)

def update (s : State) : GraphCode :=
  (ForestEdgeChoiceProgram.choice s).elim s.1 (fun e=>insert (s,e))

def advance (z : ℕ×State) : State := (update z.2,z.2.2)

def slots (s : State) : List ℕ := List.range (s.1.length*s.1.length)

def execute (s : State) : State := (slots s).foldl (fun s a=>advance (a,s)) s

def emptyGraph (z : LargeEdgeCatalogProgram.Input) : GraphCode :=
  (List.range (LargeEdgeCatalogProgram.vertexCount z)).map (fun _=>[])

def prepare (z : LargeEdgeCatalogProgram.Input) : State :=
  (emptyGraph z,LargeEdgeCatalogProgram.catalog z)

def forest (z : LargeEdgeCatalogProgram.Input) : GraphCode := (execute (prepare z)).1

end ContingencyTables.ForestGreedyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_MaximumForestExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The safe-edge invariant for the executed maximum-forest algorithm

At every step, choose a largest-capacity edge whose endpoints lie in
different current components. It extends the current forest inside a
maximum-weight forest. This is the exchange proof behind the binary
component-search implementation; no forest is enumerated by that program.
-/

namespace ContingencyTables.MaximumForestExchange

open SimpleGraph MaximumForest
open scoped BigOperators Classical

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- In an acyclic supergraph, an edge between vertices already joined by
the subgraph must itself belong to that subgraph. -/
lemma adj_of_reachable_of_acyclic {T F : SimpleGraph V} (hTF : T≤F)
    (hF : F.IsAcyclic) {u v : V} (hr : T.Reachable u v) (hf : F.Adj u v) : T.Adj u v := by
  have hc : (T⊔edge u v).IsAcyclic :=
    hF.anti (sup_le hTF ((F.edge_le_iff).mpr (Or.inr hf)))
  have h := (isAcyclic_sup_fromEdgeSet_iff.mp hc).2 hr
  exact h.resolve_left hf.ne

omit [Fintype V] in
/-- Every path between different current components contains an edge
between different current components. -/
lemma path_crosses {T F : SimpleGraph V} {u v : V} (p : F.Walk u v)
    (hn : ¬T.Reachable u v) :
    ∃ a b,F.Adj a b ∧ s(a,b)∈p.edges ∧ ¬T.Reachable a b := by
  induction p with
  | nil => exact (hn (Reachable.refl _)).elim
  | @cons u w v h p ih =>
    by_cases hu : T.Reachable u w
    · obtain ⟨a,b,hab,he,hnab⟩ := ih (fun hw=>hn (hu.trans hw))
      exact ⟨a,b,hab,by simp only [Walk.edges_cons,List.mem_cons]; exact Or.inr he,hnab⟩
    · exact ⟨u,w,h,by simp only [Walk.edges_cons,List.mem_cons,true_or],hu⟩

lemma weight_delete {F : SimpleGraph V} (b : Sym2 V→ℕ)
    {e : Sym2 V} (he : e∈F.edgeSet) :
    weight (F.deleteEdges {e}) b+b e=weight F b := by
  have hs : (F.deleteEdges {e}).edgeFinset=F.edgeFinset.erase e := by
    ext a
    simp [edgeSet_deleteEdges,and_comm]
  rw [weight_eq (F.deleteEdges {e}),weight_eq F,hs]
  exact Finset.sum_erase_add (s:=F.edgeFinset) (a:=e) b (by simpa using he)

/-- The current forest is contained in some globally optimal forest. -/
def Extendible (G T : SimpleGraph V) (b : Sym2 V→ℕ) : Prop :=
  ∃ F : SimpleGraph V,T≤F ∧ F≤G ∧ F.IsAcyclic ∧
    ∀ H : SimpleGraph V,H≤G → H.IsAcyclic → weight H b≤weight F b

lemma bottom_extendible (G : SimpleGraph V) (b : Sym2 V→ℕ) : Extendible G ⊥ b := by
  obtain ⟨F,hFG,hF,hmax⟩ := exists_maximum G b
  exact ⟨F,bot_le,hFG,hF,hmax⟩

/-- A greatest edge joining two current components is safe. The argument
uses a maximum forest only as a witness for the invariant. -/
theorem safe_edge (G T : SimpleGraph V) (b : Sym2 V→ℕ)
    (hb : ∀ e∈G.edgeSet,0<b e) (hT : Extendible G T b)
    {u v : V} (he : G.Adj u v) (hn : ¬T.Reachable u v)
    (hbest : ∀ a d,G.Adj a d → ¬T.Reachable a d → b s(a,d)≤b s(u,v)) :
    Extendible G (T⊔edge u v) b := by
  obtain ⟨F,hTF,hFG,hF,hmax⟩ := hT
  by_cases hef : F.Adj u v
  · exact ⟨F,sup_le hTF ((F.edge_le_iff).mpr (Or.inr hef)),hFG,hF,hmax⟩
  have hspan := maximum_spans G F b hFG hF hmax hb
  have hreach : F.Reachable u v := by rw [hspan]; exact he.reachable
  obtain ⟨p,hp⟩ := hreach.exists_isPath
  obtain ⟨a,d,had,ht,hnad⟩ := path_crosses p hn
  let t := s(a,d)
  let D := F.deleteEdges {t}
  have htF : t∈F.edgeSet := by simpa only [t,mem_edgeSet] using had
  have htT : ¬T.Adj a d := fun h=>hnad h.reachable
  have hTD : T≤D := by
    intro x y hxy
    have hne : s(x,y)≠t := by
      intro hxyad
      have ha : T.Adj a d := by
        have hmem : t∈T.edgeSet := by rw [←hxyad]; simpa using hxy
        simpa only [t,mem_edgeSet] using hmem
      exact htT ha
    exact (deleteEdges_adj).mpr ⟨hTF hxy,by simpa only [Set.mem_singleton_iff] using hne⟩
  have hDF : D≤F := F.deleteEdges_le {t}
  have hDuv : ¬D.Reachable u v :=
    not_reachable_delete_path_edge F hF p hp t ht
  have hDacyc : (D⊔edge u v).IsAcyclic :=
    (hF.anti hDF).sup_edge_of_not_reachable hDuv
  have hDfree : ¬D.Adj u v := fun h=>hef (hDF h)
  have hDG : D⊔edge u v≤G :=
    sup_le (hDF.trans hFG) ((G.edge_le_iff).mpr (Or.inr he))
  have hweight := weight_sup_edge D b u v hDfree he.ne
  have hdelete := weight_delete b htF
  have hbetter := hbest a d (hFG had) hnad
  have hmono : weight F b≤weight (D⊔edge u v) b := by
    dsimp only [D,t] at hweight hdelete hbetter ⊢
    omega
  refine ⟨D⊔edge u v,sup_le_sup_right hTD _,hDG,hDacyc,?_⟩
  intro H hHG hH
  exact (hmax H hHG hH).trans hmono

/-- Once no edge joins different current components, the invariant
certifies global optimality of the current forest. -/
theorem finished (G T : SimpleGraph V) (b : Sym2 V→ℕ)
    (hT : Extendible G T b)
    (hn : ∀ u v,G.Adj u v → T.Reachable u v) :
    T≤G ∧ T.IsAcyclic ∧
      ∀ H : SimpleGraph V,H≤G → H.IsAcyclic → weight H b≤weight T b := by
  obtain ⟨F,hTF,hFG,hF,hmax⟩ := hT
  have hFT : F≤T := by
    intro u v hf
    exact adj_of_reachable_of_acyclic hTF hF (hn u v (hFG hf)) hf
  have heq : F=T := le_antisymm hFT hTF
  exact heq ▸ ⟨hFG,hF,hmax⟩

end ContingencyTables.MaximumForestExchange

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestGreedySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of the actual binary forest loop

The invariant refers to the adjacency list produced by the program.
The final graph is decoded directly from that list. Optimal forests
occur only as proof witnesses for the safe-edge invariant.
-/

namespace ContingencyTables.ForestGreedySemantics

open SimpleGraph MaximumForest MaximumForestExchange
open ForestGreedyProgram ForestEdgeChoiceProgram FiniteGraphRootProgram WeightedArgmaxProgram
open scoped Classical

variable {n : ℕ}

/-- Every stored edge is valid, and every graph edge is stored in at least
one orientation with its exact capacity. -/
def Catalog (G : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ) (es : List Edge) : Prop :=
  (∀ e∈es,∃ u v : Fin n,G.Adj u v ∧ e=((u.val,v.val),b s(u,v))) ∧
  (∀ u v,G.Adj u v →
    ((u.val,v.val),b s(u,v))∈es ∨ ((v.val,u.val),b s(u,v))∈es)

def iterate : ℕ→State→State
  | 0,s=>s
  | k+1,s=>iterate k (ForestGreedyProgram.advance (0,s))

lemma fold_eq_iterate (xs : List ℕ) (s : State) :
    xs.foldl (fun s a=>ForestGreedyProgram.advance (a,s)) s=iterate xs.length s := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>simpa only [List.foldl_cons,List.length_cons,iterate,ForestGreedyProgram.advance] using ih (ForestGreedyProgram.advance (a,s))

lemma execute_iterate (s : State) : execute s=iterate (s.1.length*s.1.length) s := by
  simpa only [execute,slots,List.length_range] using fold_eq_iterate (slots s) s

lemma advance_none {s : State} (he : choice s=none) : ForestGreedyProgram.advance (0,s)=s := by
  simp only [ForestGreedyProgram.advance,update,he,Option.elim_none]

lemma iterate_none {s : State} (he : choice s=none) (k : ℕ) : iterate k s=s := by
  induction k with
  | zero=>rfl
  | succ k ih=>simpa only [iterate,advance_none he] using ih

noncomputable def edgeCount (G : SimpleGraph (Fin n)) : ℕ := G.edgeFinset.card

lemma edgeCount_le (G : SimpleGraph (Fin n)) :
    edgeCount G≤Fintype.card (Sym2 (Fin n)) := Finset.card_le_univ _

lemma card_add (T : SimpleGraph (Fin n)) {u v : Fin n}
    (hn : ¬T.Reachable u v) (huv : u≠v) :
    edgeCount (T⊔edge u v)=edgeCount T+1 := by
  have h := T.card_edgeFinset_sup_edge (fun ht=>hn ht.reachable) huv
  unfold edgeCount
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext a
  simp only [mem_edgeFinset]

def decoded (g : GraphCode) : SimpleGraph (Fin n) where
  Adj u v := u≠v ∧ u.val∈g.getD v.val [] ∧ v.val∈g.getD u.val []
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

lemma unordered_pair_budget : Fintype.card (Sym2 (Fin n))≤n*n := by
  have hs : Function.Surjective (fun p : Fin n×Fin n=>s(p.1,p.2)) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v=>exact ⟨(u,v),rfl⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_surjective _ hs

end ContingencyTables.ForestGreedySemantics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedLargeForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed maximum-capacity forest on the original cell vertices

The program uses the concrete row-then-column natural indexing. The
returned adjacency list is decoded and transported back to the original
bipartite vertex type. Its catalog and optimality obligations follow
from the stored capacities, rather than supplied correctness predicates.
-/

namespace ContingencyTables.ComputedLargeForest

open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped BigOperators Classical

variable {m n : ℕ}

abbrev vertexEquiv : (Fin m⊕Fin n) ≃ Fin (m+n) := finSumFinEquiv

def small (b : Fin m→Fin n→ℕ) (W : ℕ) (i : Fin m) (j : Fin n) : Bool :=
  decide (b i j<W)

def graph (b : Fin m→Fin n→ℕ) (W : ℕ) : SimpleGraph (Fin (m+n)) :=
  (cellGraph (small b W)).map vertexEquiv.toEmbedding

def capacities (b : Fin m→Fin n→ℕ) (e : Sym2 (Fin (m+n))) : ℕ :=
  capacity b (Sym2.map vertexEquiv.symm e)

lemma graph_edge (b : Fin m→Fin n→ℕ) (W : ℕ) (i : Fin m) (j : Fin n) :
    (graph b W).Adj (vertexEquiv (.inl i)) (vertexEquiv (.inr j)) ↔ W≤b i j := by
  change ((cellGraph (small b W)).map vertexEquiv.toEmbedding).Adj
    (vertexEquiv.toEmbedding (.inl i)) (vertexEquiv.toEmbedding (.inr j)) ↔ _
  have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
    (f:=vertexEquiv.toEmbedding) (a:=Sum.inl i) (b:=Sum.inr j)
  exact hm.trans (by simp only [cellGraph,cellAdj,small,decide_eq_false_iff_not,not_lt])

lemma capacities_cell (b : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) :
    capacities b s(vertexEquiv (.inl i),vertexEquiv (.inr j))=b i j := by
  simp only [capacities,Sym2.map_mk,Equiv.symm_apply_apply,capacity_cell]

lemma catalog_correct (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    Catalog (graph b W) (capacities b) (catalog (NetworkVertexCode.data r c b,W)) := by
  constructor
  · intro e he
    obtain ⟨i,j,hb,rfl⟩ := (mem_catalog_code r c b W e).mp he
    refine ⟨vertexEquiv (.inl i),vertexEquiv (.inr j),(graph_edge b W i j).mpr hb,?_⟩
    rw [capacities_cell]
    simp only [vertexEquiv,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.val_castAdd,Fin.val_natAdd]
  · intro u v huv
    obtain ⟨a,rfl⟩ := vertexEquiv.surjective u
    obtain ⟨d,rfl⟩ := vertexEquiv.surjective v
    have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=a) (b:=d)
    have h : (cellGraph (small b W)).Adj a d := hm.mp huv
    cases a with
    | inl i=>
      cases d with
      | inl k=>exact False.elim h
      | inr j=>
        left
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        apply (mem_catalog_code r c b W _).mpr
        refine ⟨i,j,hb,?_⟩
        rw [capacities_cell]
        simp only [vertexEquiv,finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]
    | inr j=>
      cases d with
      | inr k=>exact False.elim h
      | inl i=>
        right
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        apply (mem_catalog_code r c b W _).mpr
        refine ⟨i,j,hb,?_⟩
        rw [show s(vertexEquiv (.inr j),vertexEquiv (.inl i))=
          s(vertexEquiv (.inl i),vertexEquiv (.inr j)) from Sym2.eq_swap]
        rw [capacities_cell]
        simp only [vertexEquiv,finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

lemma capacity_positive (b : Fin m→Fin n→ℕ) (W : ℕ) (hW : 1≤W) :
    ∀ e∈(graph b W).edgeSet,0 < capacities b e := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v=>
    obtain ⟨a,rfl⟩ := vertexEquiv.surjective u
    obtain ⟨d,rfl⟩ := vertexEquiv.surjective v
    have hm := SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=a) (b:=d)
    have h : (cellGraph (small b W)).Adj a d := hm.mp he
    cases a with
    | inl i=>
      cases d with
      | inl k=>exact False.elim h
      | inr j=>
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        rw [capacities_cell b i j]
        omega
    | inr j=>
      cases d with
      | inr k=>exact False.elim h
      | inl i=>
        rw [show s(vertexEquiv (.inr j),vertexEquiv (.inl i))=
          s(vertexEquiv (.inl i),vertexEquiv (.inr j)) from Sym2.eq_swap]
        have hb : W≤b i j := by simpa only [cellGraph,cellAdj,small,
          decide_eq_false_iff_not,not_lt] using h
        rw [capacities_cell b i j]
        omega

/-- The output list itself determines the forest. -/
noncomputable def computed (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (W : ℕ) :
    SimpleGraph (Fin m⊕Fin n) :=
  (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).comap vertexEquiv

lemma weight_transport {V U : Type*} [Fintype V] [Fintype U]
    (e : V≃U) (G : SimpleGraph V) (b : Sym2 V→ℕ) :
    weight (G.map e.toEmbedding) (fun a=>b (Sym2.map e.symm a))=weight G b := by
  rw [weight_eq,weight_eq,edgeFinset_map,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  change b (Sym2.map e.symm (Sym2.map e a))=b a
  congr 1
  induction a using Sym2.inductionOn with
  | _ u v=>simp only [Sym2.map_mk,Equiv.symm_apply_apply]

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def dimensionAllowance : ℕ := 1+m*n

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted finite coarea for the published Cheeger input -/
namespace ContingencyTables.CheegerProof
open MeasureTheory
open scoped BigOperators Classical
noncomputable section

def level (a t : ℝ) : ℝ := if 0 ≤ t ∧ t < a then 1 else 0

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reusing a unary allowance across a binary transition table -/

namespace ContingencyTables.BoundedPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def powerInput (z : List Bool×ℕ) : ℕ×ℕ := (2,z.1.length-z.2)

def power (z : List Bool×ℕ) : ℕ := BinaryPowerPrograms.power (powerInput z)

end ContingencyTables.BoundedPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

abbrev Input := NetworkVertexCode.Input×ℕ

open scoped Classical

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoxCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating tables through their free entries -/

namespace ContingencyTables.BoxCompletion
open DenseAffine DensePrograms
open scoped BigOperators Classical
noncomputable section

abbrev Box (m n N : ℕ) := Fin (m*n) → Fin (N+1)

def freeValues {m n N : ℕ} (z : Box m n N) : Fin m×Fin n → ℕ :=
  fun ij => (z (finProdFinEquiv ij)).val

end
end ContingencyTables.BoxCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteProposalStay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite proposal with unused words held at the current state -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X : Type*} [Fintype X] [DecidableEq X]

def proposalStayLaw (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x : X) : RationalLaw X :=
  mapLaw (proposalLaw w hw htotal) (fun y => y.getD x)

lemma proposalStayLaw_mass (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x y : X) :
    (proposalStayLaw w hw htotal x).mass y=
      w y+if x=y then 1-∑ z,w z else 0 := by
  change (∑ z : Option X,if z.getD x=y then (proposalLaw w hw htotal).mass z else 0)=_
  rw [Fintype.sum_option]
  simp only [Option.getD_none,Option.getD_some,proposalLaw]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true, if_true]
  ring

end
end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_StarReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completion shift is invariant under computed tail indexing -/

namespace ContingencyTables.CompletionTranslation
open scoped BigOperators

variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

lemma sum_some_reindex (e : Option I' ≃ Option I) (he : e none=none) (f : Option I → ℤ) :
    (∑ i,f (e (some i)))=∑ i,f (some i) := by
  have h := e.sum_comp f
  simp only [Fintype.sum_option,he] at h
  exact add_left_cancel h

omit [Fintype I] [Fintype I'] in
lemma reindex_some_ne_none (e : Option I' ≃ Option I) (he : e none=none) (i : I') :
    e (some i)≠none := by
  intro h
  have h' := e.injective (h.trans he.symm)
  cases h'

omit [Fintype I] [Fintype I'] in
theorem star_reindex (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none) (R : Option I → ℤ) (P : Option J → ℤ)
    (i : Option I') (j : Option J') :
    star (fun i => R (eI i)) (fun j => P (eJ j)) i j=star R P (eI i) (eJ j) := by
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [star,hI,hJ]
      rw [sum_some_reindex eJ hJ]
    | some j =>
      rcases h : eJ (some j) with _|j'
      · exact False.elim (reindex_some_ne_none eJ hJ j h)
      · simp only [star,hI,h]
  | some i =>
    rcases h : eI (some i) with _|i'
    · exact False.elim (reindex_some_ne_none eI hI i h)
    · cases j with
      | none => simp only [star,h,hJ]
      | some j =>
        rcases h' : eJ (some j) with _|j'
        · exact False.elim (reindex_some_ne_none eJ hJ j h')
        · rfl

omit [Fintype I] [Fintype I'] in
theorem between_reindex (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none)
    (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (i : Option I') (j : Option J') :
    between (fun i => R₀ (eI i)) (fun i => R₁ (eI i))
      (fun j => P₀ (eJ j)) (fun j => P₁ (eJ j)) i j=
      between R₀ R₁ P₀ P₁ (eI i) (eJ j) :=
  star_reindex eI eJ hI hJ (fun i => (R₁ i:ℤ)-R₀ i) (fun j => (P₁ j:ℤ)-P₀ j) i j

end ContingencyTables.CompletionTranslation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_WordCompletionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent finite words for a proposal and its completion test -/

namespace ContingencyTables.CompletionTranslation
open FirstSuccess FairBits
open scoped Classical
noncomputable section
variable {X I J : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype J]
variable {s f : ℕ} (R : X → Option I → ℕ) (P : X → Option J → ℕ)
variable (proposal : X → (Fin s → Bool) → Option X)
variable (draw : (x : X) → (Fin f → Bool) → Table (R x) (P x))

def wordCompletionStep (x : X) (bits : Fin (s+f) → Bool) : X :=
  let parts := splitWordEquiv s f bits
  completionDecision R P x (proposal x parts.1) (draw x parts.2)

theorem wordCompletionStep_law (x : X) :
    mapLaw (uniformLaw (α := Fin (s+f) → Bool)) (wordCompletionStep R P proposal draw x)=
      completionStepLaw R P
        (fun x => mapLaw (uniformLaw (α := Fin s → Bool)) (proposal x))
        (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (draw x)) x := by
  let finish := fun y word => completionDecision R P x y (draw x word)
  let F := fun ab : (Fin s → Bool)×(Fin f → Bool) => finish (proposal x ab.1) ab.2
  have he := map_equiv (splitWordEquiv s f) (uniformLaw (α := Fin (s+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin s → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = _ := by
      rw [mapLaw_product_finish]
      unfold completionStepLaw
      congr 1
      funext y
      exact (mapLaw_comp (uniformLaw (α := Fin f → Bool)) (draw x)
        (completionDecision R P x y)).symm

end
end ContingencyTables.CompletionTranslation

end OAI
end



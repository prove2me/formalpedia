-- Prove2me | Definitions.Def_OAIQ361V3Ea000
-- name    : OAIQ361V3Ea000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T16:22:32.972198+00:00
-- url     : https://prove2.me/theorems/ae1bbbe8-a20f-48cf-be11-22e1f9c3c64b
-- title:
--   Definitions bundle OAIQ361V3Ea000 of the split of OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1076 declarations of OpenAI's Lean: 511 definitions, 10 inductive types or structures, 6 instances and 549 theorems. The definitions and types are `OAI.EditApproximation.AdaptiveSeedTrace`, `OAI.EditApproximation.BP`, `OAI.EditApproximation.BandParentSpace`, `OAI.EditApproximation.BellmanAction`, `OAI.EditApproximation.BinaryBellmanAction.decode`, `OAI.EditApproximation.BinaryFraction.CoarseBinaryBox`, `OAI.EditApproximation.BinaryFraction.CoarseCompact`, `OAI.EditApproximation.BinaryFraction.CoarseGridCell`, `OAI.EditApproximation.BinaryFraction.PreparedKernelInputBounds`, `OAI.EditApproximation.BinaryFraction.PreparedKernelNumericBounds`, `OAI.EditApproximation.BinaryFraction.affineGuardBitBudget`, `OAI.EditApproximation.BinaryFraction.anchorGuardBitBudget`, `OAI.EditApproximation.BinaryFraction.bandActionBitBudget`, `OAI.EditApproximation.BinaryFraction.bandActionWithWork`, `OAI.EditApproximation.BinaryFraction.bandCoordinateBitBudget`, `OAI.EditApproximation.BinaryFraction.bandCoordinateWithWork`, `OAI.EditApproximation.BinaryFraction.bandCoordinatesBitBudget`, `OAI.EditApproximation.BinaryFraction.bandEnvelopeBitBudget`, `OAI.EditApproximation.BinaryFraction.bandEnvelopeWithWork`, `OAI.EditApproximation.BinaryFraction.bandEnvelopeWordBudget`, `OAI.EditApproximation.BinaryFraction.bandFromActionsBitBudget`, `OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork`, `OAI.EditApproximation.BinaryFraction.bandMassTotalStorageBudget`, `OAI.EditApproximation.BinaryFraction.bandPredicateBitBudget`, `OAI.EditApproximation.BinaryFraction.bandPredicateWithWork`, `OAI.EditApproximation.BinaryFraction.bandPreparationBitBudget`, `OAI.EditApproximation.BinaryFraction.bandToleranceBitBudget`, `OAI.EditApproximation.BinaryFraction.bandVertexWordBudget`, `OAI.EditApproximation.BinaryFraction.bandVerticesWithWork`, `OAI.EditApproximation.BinaryFraction.bellmanActionBitBudget`, `OAI.EditApproximation.BinaryFraction.bellmanActionWithWork`, `OAI.EditApproximation.BinaryFraction.bellmanActionWordBudget`, `OAI.EditApproximation.BinaryFraction.bellmanBitBudget`, `OAI.EditApproximation.BinaryFraction.bellmanWithWork`, `OAI.EditApproximation.BinaryFraction.boundedScaleBitBudget`, `OAI.EditApproximation.BinaryFraction.boundedScaleWordBudget`, `OAI.EditApproximation.BinaryFraction.cachedInitialProgramBitBudget`, `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork`, `OAI.EditApproximation.BinaryFraction.castGroupSourceAllocation`, `OAI.EditApproximation.BinaryFraction.cellCentersBitBudget` and 481 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `EditApproximation_Binary_BinaryActionSelection`, `EditApproximation_Binary_BinaryActualBandOptimizer`, `EditApproximation_Binary_BinaryAffineGuard`, `EditApproximation_Binary_BinaryArithmeticWork`, `EditApproximation_Binary_BinaryBandAction`, `EditApproximation_Binary_BinaryBandCoordinates`, `EditApproximation_Binary_BinaryBandEnvelope`, `EditApproximation_Binary_BinaryBandGuardWork`, `EditApproximation_Binary_BinaryBandInputWork`, `EditApproximation_Binary_BinaryBandInputs`, `EditApproximation_Binary_BinaryBandReads`, `EditApproximation_Binary_BinaryBandSpace`, `EditApproximation_Binary_BinaryBandTailWork`, `EditApproximation_Binary_BinaryBellmanKernel`, `EditApproximation_Binary_BinaryBellmanSpace`, `EditApproximation_Binary_BinaryBufferSpace`, `EditApproximation_Binary_BinaryCachedShellWork`, `EditApproximation_Binary_BinaryCanonicalWork`, `EditApproximation_Binary_BinaryCeilingWork`, `EditApproximation_Binary_BinaryCellCenters`, `EditApproximation_Binary_BinaryCellCentersWork`, `EditApproximation_Binary_BinaryCellGrid`, `EditApproximation_Binary_BinaryCellGridWork`, `EditApproximation_Binary_BinaryCellGroupKernel`, `EditApproximation_Binary_BinaryCellReads`, `EditApproximation_Binary_BinaryCellSourcePort`, `EditApproximation_Binary_BinaryCellSourceSpace`, `EditApproximation_Binary_BinaryCellSpace`, `EditApproximation_Binary_BinaryComputedCellGroup`, `EditApproximation_Binary_BinaryContinuationSpace`, `EditApproximation_Binary_BinaryContinuationWork`, `EditApproximation_Binary_BinaryCoordinateAction`, `EditApproximation_Binary_BinaryCountedActionSpace`, `EditApproximation_Binary_BinaryCountedGroup`, `EditApproximation_Binary_BinaryCountedGroupWork`, `EditApproximation_Binary_BinaryCountedOptimizerSpace`, `EditApproximation_Binary_BinaryCutReads`, `EditApproximation_Binary_BinaryDistanceWork`, `EditApproximation_Binary_BinaryDivisionWork`, `EditApproximation_Binary_BinaryDyadicCeiling`, `EditApproximation_Binary_BinaryDyadicSampledGroups`, `EditApproximation_Binary_BinaryEnvelopeReads`, `EditApproximation_Binary_BinaryEnvelopeSpace`, `EditApproximation_Binary_BinaryFiniteLoops`, `EditApproximation_Binary_BinaryFractionWork`, `EditApproximation_Binary_BinaryGatheredValues`, `EditApproximation_Binary_BinaryGeometrySpace`, `EditApproximation_Binary_BinaryGradientWork`, `EditApproximation_Binary_BinaryGridSpace`, `EditApproximation_Binary_BinaryGridWork`, `EditApproximation_Binary_BinaryGroupActionReads`, `EditApproximation_Binary_BinaryGroupActionSourceSpace`, `EditApproximation_Binary_BinaryGroupKernel`, `EditApproximation_Binary_BinaryGroupReads`, `EditApproximation_Binary_BinaryGroupReductionSpace`, `EditApproximation_Binary_BinaryGroupSetup`, `EditApproximation_Binary_BinaryGroupSetupWork`, `EditApproximation_Binary_BinaryGroupSourcePort`, `EditApproximation_Binary_BinaryGroupSourceSpace`, `EditApproximation_Binary_BinaryGroupSpace`, `EditApproximation_Binary_BinaryGuardSpace`, `EditApproximation_Binary_BinaryInitialGridWork`, `EditApproximation_Binary_BinaryInitialGuardSpace`, `EditApproximation_Binary_BinaryInitialGuardWork`, `EditApproximation_Binary_BinaryInitialKernel`, `EditApproximation_Binary_BinaryInitialMinimumWork`, `EditApproximation_Binary_BinaryInitialReadSpace`, `EditApproximation_Binary_BinaryInitialReads`, `EditApproximation_Binary_BinaryInitialWork`, `EditApproximation_Binary_BinaryKeyedOnline`, `EditApproximation_Binary_BinaryLocalGrid`, `EditApproximation_Binary_BinaryLocalGridWork`, `EditApproximation_Binary_BinaryLocalGroupActions`, `EditApproximation_Binary_BinaryLocalGroupReads`, `EditApproximation_Binary_BinaryLocalGroupSource`, `EditApproximation_Binary_BinaryLocalGroupSourceSpace`, `EditApproximation_Binary_BinaryLocalGuardWork`, `EditApproximation_Binary_BinaryLocalOnlineReads`, `EditApproximation_Binary_BinaryLocalOnlineSource`, `EditApproximation_Binary_BinaryLocalOnlineSourceSpace`, `EditApproximation_Binary_BinaryLocalRepresentativeWork`, `EditApproximation_Binary_BinaryLocalWarmupKernel`, `EditApproximation_Binary_BinaryLocalWarmupWork`, `EditApproximation_Binary_BinaryLogWork`, `EditApproximation_Binary_BinaryLoopSpace`, `EditApproximation_Binary_BinaryMaximizerWork`, `EditApproximation_Binary_BinaryMedianKernel`, `EditApproximation_Binary_BinaryMedianSpace`, `EditApproximation_Binary_BinaryMemo`, `EditApproximation_Binary_BinaryMemoSpace`, `EditApproximation_Binary_BinaryNormalizationSpace`, `EditApproximation_Binary_BinaryNumericSpace`, `EditApproximation_Binary_BinaryOnlineInputWork`, `EditApproximation_Binary_BinaryOnlineInputs`, `EditApproximation_Binary_BinaryOnlineReads`, `EditApproximation_Binary_BinaryOnlineSetupWork`, `EditApproximation_Binary_BinaryOnlineSourceSpace`, `EditApproximation_Binary_BinaryOnlineSpace`, `EditApproximation_Binary_BinaryOptimizerSpace`, `EditApproximation_Binary_BinaryOptimizerWork`, `EditApproximation_Binary_BinaryOrderWork`, `EditApproximation_Binary_BinaryPhysicalContinuation`, `EditApproximation_Binary_BinaryPhysicalContinuationWork`, `EditApproximation_Binary_BinaryPowerStorage`, `EditApproximation_Binary_BinaryPrefixReads`, `EditApproximation_Binary_BinaryPrefixSpace`, `EditApproximation_Binary_BinaryPrefixWork`, `EditApproximation_Binary_BinaryPreparedCellGroup`, `EditApproximation_Binary_BinaryPreparedCellGroupWork`, `EditApproximation_Binary_BinaryPreparedComputedCell`, `EditApproximation_Binary_BinaryPreparedKernelWork`, `EditApproximation_Binary_BinaryPreparedLocalGroupWork`, `EditApproximation_Binary_BinaryPreparedLocalGroups`, `EditApproximation_Binary_BinaryPreparedLocalKernel`, `EditApproximation_Binary_BinaryPreparedLocalOnline`, `EditApproximation_Binary_BinaryPreparedLocalOnlineWork`, `EditApproximation_Binary_BinaryPreparedOnline`, `EditApproximation_Binary_BinaryPreparedOnlineReads`, `EditApproximation_Binary_BinaryPreparedOnlineWork`, `EditApproximation_Binary_BinaryPreparedRepresentative`, `EditApproximation_Binary_BinaryPreparedRepresentativeWork`, `EditApproximation_Binary_BinaryPreparedUnskipped`, `EditApproximation_Binary_BinaryPreparedUnskippedWork`, `EditApproximation_Binary_BinaryRawCost`, `EditApproximation_Binary_BinaryRawNumerics`, `EditApproximation_Binary_BinaryReadComposition`, `EditApproximation_Binary_BinaryReadCostBounds`, `EditApproximation_Binary_BinaryReductionSpace`, `EditApproximation_Binary_BinaryRefinementLists`, `EditApproximation_Binary_BinaryRefinementParameters`, `EditApproximation_Binary_BinaryRepresentativeKernel`, `EditApproximation_Binary_BinaryRepresentativeReads`, `EditApproximation_Binary_BinaryRepresentativeSpace`, `EditApproximation_Binary_BinaryRepresentativeWork`, `EditApproximation_Binary_BinaryRoundedKernel`, `EditApproximation_Binary_BinaryRoundedReads`, `EditApproximation_Binary_BinaryRoundedWork`, `EditApproximation_Binary_BinaryRoundingSpace`, `EditApproximation_Binary_BinarySampledGroupWork`, `EditApproximation_Binary_BinarySampledGroups`, `EditApproximation_Binary_BinarySampledOnline`, `EditApproximation_Binary_BinarySampledOnlinePolynomial`, `EditApproximation_Binary_BinarySampledOnlineSpace`, `EditApproximation_Binary_BinarySampledSourcePort`, `EditApproximation_Binary_BinaryScaleGrid`, `EditApproximation_Binary_BinaryScoreReads`, `EditApproximation_Binary_BinarySeedMedianWork`, `EditApproximation_Binary_BinarySelectedGroupWork`, `EditApproximation_Binary_BinarySelectionSpace`, `EditApproximation_Binary_BinarySubtractWork`, `EditApproximation_Binary_BinaryTriangularChoice`, `EditApproximation_Binary_BinaryTriangularSpace`, `EditApproximation_Binary_BinaryUnskippedGuardWork`, `EditApproximation_Binary_BinaryUnskippedReads`, `EditApproximation_Binary_BinaryUnskippedSpace`, `EditApproximation_Binary_BinaryUpdateWork`, `EditApproximation_Binary_BinaryWarmupAverage`, `EditApproximation_Binary_BinaryWideActionsWork`, `EditApproximation_Binary_BinaryWideChildWork`, `EditApproximation_Binary_BinaryWideGrid`, `EditApproximation_Binary_BinaryWideSpace`, `EditApproximation_Binary_BitAllocation`, `EditApproximation_Binary_BitMemoHeap`, `EditApproximation_Binary_BitMemoMap`, `EditApproximation_Binary_BitMemoRun`, `EditApproximation_Binary_BitQuery`, `EditApproximation_Binary_BitQueryKeysSpace`, `EditApproximation_Binary_BitQueryOn`, `EditApproximation_Binary_BitQuerySpace`, `EditApproximation_Binary_FractionAllocation`, `EditApproximation_Binary_IntegerAlgorithm`, `EditApproximation_Binary_SignedBinaryOrderWork`, `EditApproximation_Binary_SignedBinaryWork`, `EditApproximation_Binary_UnreducedNumerics`, `EditApproximation_Binary_UnreducedOptimizer`, `EditApproximation_Binary_UnreducedRational`, `EditApproximation_Binary_UnreducedStorage`, `EditApproximation_Coarse_CoarseAccuracy`, `EditApproximation_Coarse_CoarseArrayArithmetic`, `EditApproximation_Coarse_CoarseBinaryBox`, `EditApproximation_Coarse_CoarseBinaryEvaluation`, `EditApproximation_Coarse_CoarseBinaryWeight`, `EditApproximation_Coarse_CoarseCompactCells`, `EditApproximation_Coarse_CoarseDenominatorArithmetic`, `EditApproximation_Coarse_CoarseGlobalSeed`, `EditApproximation_Coarse_CoarseIndexBudget`, `EditApproximation_Coarse_CoarseIndexedCompare`, `EditApproximation_Coarse_CoarseIndexedExtra`, `EditApproximation_Coarse_CoarseIndexedInitialCost`, `EditApproximation_Coarse_CoarseIndexedRead`, `EditApproximation_Coarse_CoarseIndexedRootCost`, `EditApproximation_Coarse_CoarseInitial`, `EditApproximation_Coarse_CoarseInitialBinary`, `EditApproximation_Coarse_CoarseInitialExecution`, `EditApproximation_Coarse_CoarseLevelMagnitude`, `EditApproximation_Coarse_CoarseNumericalUnit`, `EditApproximation_Coarse_CoarseProbability`, `EditApproximation_Coarse_CoarseReadBudget`, `EditApproximation_Coarse_CoarseReadCore`, `EditApproximation_Coarse_CoarseReadTree`, `EditApproximation_Coarse_CoarseRootExecution`, `EditApproximation_Coarse_CoarseSampling`, `EditApproximation_Geometry_ActualRepresentatives`, `EditApproximation_Geometry_BandActionPolynomial`, `EditApproximation_Geometry_BandOptimizerWork`, `EditApproximation_Geometry_BandRounding`, `EditApproximation_Geometry_Bellman`, `EditApproximation_Geometry_CanonicalFractionWork`, `EditApproximation_Geometry_ChargedPhysicalRequest`, `EditApproximation_Geometry_ChargedQueryProgress`, `EditApproximation_Geometry_CommonSeedTrace`, `EditApproximation_Geometry_ComparisonTree`, `EditApproximation_Geometry_DependencyExpansion`, `EditApproximation_Geometry_DependencyWeightedWork`, `EditApproximation_Geometry_Geometry`, `EditApproximation_Geometry_Grid`, `EditApproximation_Geometry_LocalOnlineProgram`, `EditApproximation_Geometry_LocalSeedSequence`, `EditApproximation_Geometry_LocalWideStep`, `EditApproximation_Geometry_MemoCodeWork`, `EditApproximation_Geometry_OccurrencePrefix`, `EditApproximation_Geometry_ParameterConstruction`, `EditApproximation_Geometry_PrefixBitEnvelope`, `EditApproximation_Geometry_PreparedBandPolynomial`, `EditApproximation_Geometry_PreparedCachedKernelWork`, `EditApproximation_Geometry_PublishedInputs`, `EditApproximation_Geometry_RankedMemoStorage`, `EditApproximation_Geometry_Seed`, `EditApproximation_Geometry_UnifiedPhysicalTable`, `EditApproximation_Numerics_Numerics`, `EditApproximation_Numerics_RationalWideStep`, `EditApproximation_Numerics_ScalarAllocation`, `EditApproximation_Numerics_VectorOptimizerWork`, `EditApproximation_Probability_AdaptiveSeedTrace`, `EditApproximation_Probability_ExactSampling`, `EditApproximation_Probability_FiniteBitPolynomial`, `EditApproximation_Probability_FiniteEnumerationWork`, `EditApproximation_Queries_QueryActionInputCost`, `EditApproximation_Queries_QueryBandInputCost`, `EditApproximation_Queries_QueryBoundedBody`, `EditApproximation_Queries_QueryBoundedWork`, `EditApproximation_Queries_QueryBufferSpace`, `EditApproximation_Queries_QueryBufferedSharedCost`, `EditApproximation_Queries_QueryCellCost`, `EditApproximation_Queries_QueryCellStateCost`, `EditApproximation_Queries_QueryChargedSeed`, `EditApproximation_Queries_QueryContinuationSpace`, `EditApproximation_Queries_QueryCoordinateSpace`, `EditApproximation_Queries_QueryDataBuffers`, `EditApproximation_Queries_QueryEligibilitySpace`, `EditApproximation_Queries_QueryFamilyActive`, `EditApproximation_Queries_QueryFamilyReaderBounds`, `EditApproximation_Queries_QueryFamilyRefinement`, `EditApproximation_Queries_QueryFinishCost`, `EditApproximation_Queries_QueryGapStateCost`, `EditApproximation_Queries_QueryGatherSpace`, `EditApproximation_Queries_QueryGridCost`, `EditApproximation_Queries_QueryGroupInputCost`, `EditApproximation_Queries_QueryGroupKeyCost`, `EditApproximation_Queries_QueryGroupLabelCost`, `EditApproximation_Queries_QueryGroupSampleCost`, `EditApproximation_Queries_QueryGroupSamples`, `EditApproximation_Queries_QueryGroupSetupSpace`, `EditApproximation_Queries_QueryGroupSourceCost`, `EditApproximation_Queries_QueryGroupSourceSpace`, `EditApproximation_Queries_QueryHistoryInputCost`, `EditApproximation_Queries_QueryHistoryInputs`, `EditApproximation_Queries_QueryHistorySpace`, `EditApproximation_Queries_QueryIndexedSlice`, `EditApproximation_Queries_QueryInitialCenterCost`, `EditApproximation_Queries_QueryInitialConeCenters`, `EditApproximation_Queries_QueryInitialConeSpace`, `EditApproximation_Queries_QueryInitialProgramCost`, `EditApproximation_Queries_QueryInitialSpace`, `EditApproximation_Queries_QueryInitialSupport`, `EditApproximation_Queries_QueryInitialSupportCost`, `EditApproximation_Queries_QueryInitialSupportSpace`, `EditApproximation_Queries_QueryInputCodes`, `EditApproximation_Queries_QueryInputSpace`, `EditApproximation_Queries_QueryListWork`, `EditApproximation_Queries_QueryLocalBand`, `EditApproximation_Queries_QueryLocalBandCost`, `EditApproximation_Queries_QueryLocalBuffers`, `EditApproximation_Queries_QueryLocalFinishCost`, `EditApproximation_Queries_QueryLocalProgram`, `EditApproximation_Queries_QueryLocalProgramCost`, `EditApproximation_Queries_QueryLocalRefinement`, `EditApproximation_Queries_QueryLocalRefinementCost`, `EditApproximation_Queries_QueryLocalRepresentativeSpace`, `EditApproximation_Queries_QueryLocalSelectorSpace`, `EditApproximation_Queries_QueryLocalSelectors`, `EditApproximation_Queries_QueryLocalSources`, `EditApproximation_Queries_QueryLocalSourcesCost`, `EditApproximation_Queries_QueryMeanRead`, `EditApproximation_Queries_QueryOnlineKeyCost`, `EditApproximation_Queries_QueryOnlineRangeCost`, `EditApproximation_Queries_QueryOnlineRangeSpace`, `EditApproximation_Queries_QueryOrderedSpace`, `EditApproximation_Queries_QueryOuterGatherCost`, `EditApproximation_Queries_QueryPhysicalProgram`, `EditApproximation_Queries_QueryPhysicalProgramCost`, `EditApproximation_Queries_QueryRawCenterCost`, `EditApproximation_Queries_QueryRefinementWorkBound`, `EditApproximation_Queries_QueryRepresentativeCost`, `EditApproximation_Queries_QueryRestrictionCost`, `EditApproximation_Queries_QueryRoundedStateCost`, `EditApproximation_Queries_QueryScopedSourceCost`, `EditApproximation_Queries_QuerySharedCellCost`, `EditApproximation_Queries_QuerySharedGeometry`, `EditApproximation_Queries_QuerySharedGeometrySpace`, `EditApproximation_Queries_QuerySharedInputCost`, `EditApproximation_Queries_QuerySharedSpace`, `EditApproximation_Queries_QuerySourceBuffers`, `EditApproximation_Queries_QuerySourceGatherCost`, `EditApproximation_Queries_QueryWarmupProgramCost`, `EditApproximation_Queries_QueryWarmupSpace`, `EditApproximation_Refinement_ComputedPhysicalUniform`, `EditApproximation_Refinement_PhysicalConditionalNode`, `EditApproximation_Refinement_PhysicalDependencyRank`, `EditApproximation_Refinement_PhysicalInitial`, `EditApproximation_Refinement_PhysicalLocalRefinement`, `EditApproximation_Refinement_PhysicalLocalWarmup`, `EditApproximation_Refinement_PhysicalOnlineBand`, `EditApproximation_Refinement_PhysicalParentDraw`, `EditApproximation_Refinement_PhysicalPreparedInputBounds`, `EditApproximation_Refinement_PhysicalQueryProgress`, `EditApproximation_Refinement_PhysicalRationalWarmup`, `EditApproximation_Refinement_PhysicalRefinement`, `EditApproximation_Refinement_PhysicalRequestEncoding`, `EditApproximation_Refinement_PhysicalSeedMedian`, `EditApproximation_Refinement_PhysicalSubtree`, `EditApproximation_Refinement_PhysicalUniformAccuracy`, `EditApproximation_Refinement_StageWarmup`, `EditApproximation_Specification_Footprint`.
--
--   **Imports.** It imports the published bundles `Def_EditApproxScheme_01`, `Def_EditApproxScheme_02`, `Def_EditApproxScheme_03`, `Def_EditApproxScheme_04`, `Def_EditApproxScheme_05`, `Def_EditApproxScheme_06`, `Def_EditApproxScheme_07`, `Def_EditApproxScheme_08`, `Def_EditApproxScheme_09`, `Def_EditApproxScheme_10`, `Def_EditApproxScheme_11`, `Def_EditApproxScheme_12`, `Def_EditApproxScheme_13`, `Def_EditApproxScheme_14`, `Def_EditApproxScheme_15` and `Def_EditApproxScheme_16`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ361V3Ea002` and `OAIQ361V3Ea003`; the statements `OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost`, `OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds`, `OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork`, `OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound`, `OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound`, `OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate`, `OAI.EditApproximation.BinaryFraction.localWarmupKernelWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost`, `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost`, `OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds`, `OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on`, `OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost`, `OAI.EditApproximation.queryChargedWarmup_refines`, `OAI.EditApproximation.queryFamilyBoundedActive_refines`, `OAI.EditApproximation.queryInitialConeProgramAt_work_bound`, `OAI.EditApproximation.queryLocalRandomSources_refines`, `OAI.EditApproximation.queryLocalRefinement_work_bound`, `OAI.EditApproximation.queryOnlineSourceGather_work_bound` and `OAI.EditApproximation.queryWarmupProgram_work_bound`; the proofs of `OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost`, `OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds`, `OAI.EditApproximation.BinaryFraction.coarseBinaryEval_bitWork`, `OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound`, `OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate`, `OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost`, `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost`, `OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.unskippedEstimateWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_cost` and `OAI.EditApproximation.queryWarmupProgram_work_bound`.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16

section
-- module Solutions.OAIQ361V3_EA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryArithmeticWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean ripple addition. The counter counts Boolean gates and
bit writes, not unit-cost arithmetic on unbounded integers. -/

namespace EditApproximation







theorem bitAdder_value (a b carry : Bool) :
    (bitSum a b carry).toNat + 2 * (bitCarry a b carry).toNat =
      a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide





theorem bitAddWithWork_value (left right : List Bool) (carry : Bool) :
    bitWordValue (bitAddWithWork left right carry).1 =
      bitWordValue left + bitWordValue right + carry.toNat := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork, bitWordValue]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, bitWordValue, ih]
      have h := bitAdder_value false b carry
      simp only [Bool.toNat_false] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, bitWordValue, ih]
      have h := bitAdder_value a false carry
      simp only [Bool.toNat_false] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, bitWordValue, ih]
      have h := bitAdder_value a b carry
      omega

theorem bitWordValue_bits (n : ℕ) : bitWordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitWordValue]
  | bit bit n h ih =>
    rw [Nat.bits_append_bit n bit h]
    cases bit <;> simp [bitWordValue, ih, Nat.bit, Nat.add_comm]



theorem binaryNaturalAddWithWork_value (a b : ℕ) :
    bitWordValue (binaryNaturalAddWithWork a b).1 = a + b := by
  simp [binaryNaturalAddWithWork, bitAddWithWork_value, bitWordValue_bits]



theorem bitMulWithWork_value (left right : List Bool) :
    bitWordValue (bitMulWithWork left right).1 = bitWordValue left * bitWordValue right := by
  induction left with
  | nil => simp [bitMulWithWork, bitWordValue]
  | cons bit bits ih =>
    cases bit <;> simp [bitMulWithWork, bitWordValue, bitAddWithWork_value, ih] <;> ring



theorem binaryNaturalMulWithWork_value (a b : ℕ) :
    bitWordValue (binaryNaturalMulWithWork a b).1 = a * b := by
  simp [binaryNaturalMulWithWork, bitMulWithWork_value, bitWordValue_bits]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_Numerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

/-- Cumulative integer mass for the triangular exact sampler. -/


theorem optimizerTriangularMass_succ (K : ℕ) :
    optimizerTriangularMass (K + 1) = optimizerTriangularMass K + (K + 1) := by
  unfold optimizerTriangularMass
  rw [sum_range_succ]

theorem optimizerTriangularMass_twice (K : ℕ) :
    2 * optimizerTriangularMass K = K * (K + 1) := by
  induction K with
  | zero => simp [optimizerTriangularMass]
  | succ K ih =>
    rw [optimizerTriangularMass_succ]
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact fractions with positive, unreduced denominators. These operations
perform no greatest-common-divisor computation. The representation lemmas
apply to the intermediate fractions, not merely their reduced Rat values. -/

namespace EditApproximation



namespace UnreducedRational

theorem eq_of_num_den {a b : UnreducedRational} (hnum : a.num = b.num) (hden : a.den = b.den) : a = b := by
  cases a
  cases b
  cases hnum
  cases hden
  rfl



def ofRat (a : ℚ) : UnreducedRational := ⟨a.num, a.den, a.den_pos⟩



def add (a b : UnreducedRational) : UnreducedRational :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def neg (a : UnreducedRational) : UnreducedRational := ⟨-a.num, a.den, a.den_pos⟩







def storageBits (a : UnreducedRational) : ℕ := Nat.size a.num.natAbs + Nat.size a.den + 1

@[simp] theorem value_ofRat (a : ℚ) : (ofRat a).value = a := by
  exact a.num_div_den

@[simp] theorem value_zero : zero.value = 0 := by simp [zero, value]

@[simp] theorem value_add (a b : UnreducedRational) : (a.add b).value = a.value + b.value := by
  unfold add value
  push_cast
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  field_simp [ha, hb]

@[simp] theorem value_neg (a : UnreducedRational) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

@[simp] theorem value_mul (a b : UnreducedRational) : (a.mul b).value = a.value * b.value := by
  simp [mul, value, mul_div_mul_comm]

@[simp] theorem value_inv (a : UnreducedRational) : a.inv.value = a.value⁻¹ := by
  by_cases h : a.num = 0
  · simp [inv, h, value, zero]
  · have hn : (a.num.natAbs : ℚ) ≠ 0 := by exact_mod_cast (Int.natAbs_pos.mpr h).ne'
    have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
    have hsign : ((a.num.sign : ℤ) : ℚ) * a.num = (a.num.natAbs : ℚ) := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs a.num)
    simp only [inv, h, ↓reduceDIte, value]
    push_cast
    apply eq_inv_of_mul_eq_one_left
    field_simp [hn, hd]
    exact hsign

@[simp] theorem value_div (a b : UnreducedRational) : (a.div b).value = a.value / b.value := by
  simp [div, div_eq_mul_inv]

@[simp] theorem lt_eq_true (a b : UnreducedRational) : a.lt b = true ↔ a.value < b.value := by
  simp only [lt, decide_eq_true_eq, value]
  rw [div_lt_div_iff₀ (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)
    (by exact_mod_cast b.den_pos : (0 : ℚ) < b.den)]
  exact_mod_cast (Iff.rfl : a.num * (b.den : ℤ) < b.num * (a.den : ℤ) ↔ _)

end UnreducedRational

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def one : UnreducedRational := ofRat 1



def sub (a b : UnreducedRational) : UnreducedRational := a.add b.neg

def pow (a : UnreducedRational) : ℕ → UnreducedRational
  | 0 => one
  | n + 1 => (pow a n).mul a

@[simp] theorem value_one : one.value = 1 := value_ofRat _
@[simp] theorem value_nat (n : ℕ) : (nat n).value = n := by simp [nat, value]
@[simp] theorem value_sub (a b : UnreducedRational) : (a.sub b).value = a.value - b.value := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_pow (a : UnreducedRational) (n : ℕ) : (a.pow n).value = a.value ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

def optimizerStep (j : ℕ) : UnreducedRational := (nat 2).div (nat (j + 2))

@[simp] theorem optimizerStep_value (j : ℕ) :
    (optimizerStep j).value = 2 / ((j : ℚ) + 2) := by
  simp [optimizerStep]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

theorem optimizerTriangularMass_positive (K : ℕ) (hK : 0 < K) :
    0 < optimizerTriangularMass K := by
  have hproduct : 0 < K * (K + 1) := Nat.mul_pos hK (by omega)
  rw [← optimizerTriangularMass_twice K] at hproduct
  omega

/- Executable triangular-block lookup. Its finite linear search also
has polynomial cost in the prescribed number of optimizer steps. -/


end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_VectorOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialized rational optimizer iterates. Finite vectors store the
previous iterate and its gradient, and a scored scan stores the current
best score. Counters charge rational arithmetic, comparisons, array
accesses and array writes. Integer/rational bit costs are separate. -/

namespace EditApproximation

open Finset

theorem vector_get_ofFn {α : Type*} {d : ℕ} (f : Fin d → α) (i : Fin d) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

/-- A single materializing array pass. The operation count includes
array construction, the value/counter traversals, and summing counters. -/


theorem vectorMapWithWork_value {α : Type*} (d : ℕ) (f : Fin d → α × ℕ) (i : Fin d) :
    (vectorMapWithWork d f).1.get i = (f i).1 := by
  change (Vector.ofFn f |>.map Prod.fst)[i.val] = _
  simp only [Vector.getElem_map, Vector.getElem_ofFn]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fraction-only implementation of the actual finite optimizer. None of
its arithmetic or score comparisons requires reduced rational numbers. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def dotList {d : ℕ} (left right : Vector UnreducedRational d) : List (Fin d) → UnreducedRational
  | [] => zero
  | i :: rest => ((left.get i).mul (right.get i)).add (dotList left right rest)

def dot {d : ℕ} (left right : Vector UnreducedRational d) : UnreducedRational :=
  dotList left right (List.finRange d)

theorem dotList_value {d : ℕ} (left right : Vector UnreducedRational d) (indices : List (Fin d)) :
    (dotList left right indices).value =
      (indices.map fun i => (left.get i).value * (right.get i).value).sum := by
  induction indices with
  | nil => simp [dotList]
  | cons i rest ih => simp [dotList, ih]

theorem dot_value {d : ℕ} (left right : Vector UnreducedRational d) :
    (dot left right).value = ∑ i, (left.get i).value * (right.get i).value := by
  simp only [dot, dotList_value]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCanonicalWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Removing only leading zero bits of an integer word. This is unrelated
to rational reduction: no common divisor is computed. -/

namespace EditApproximation



theorem trimBitWordWithWork_value (bits : List Bool) :
    bitWordValue (trimBitWordWithWork bits).1 = bitWordValue bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [trimBitWordWithWork]
    split_ifs with h
    · have ht : bitWordValue bits = 0 := by rw [← ih, h.1]; rfl
      simp [h.2, bitWordValue, ht]
    · simp only [bitWordValue, ih]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOrderWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Most-significant comparison performed directly on little-endian Boolean
words, allowing leading zero bits. -/

namespace EditApproximation





theorem bitOrdering_matches (high : Ordering) (a b : Bool) (x y : ℕ)
    (h : orderingMatches high x y) :
    orderingMatches (bitOrdering high a b) (a.toNat + 2 * x) (b.toNat + 2 * y) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
  · cases a <;> cases b <;> simp [bitOrdering, orderingMatches]
  · exact Or.inr (Or.inr ⟨rfl, by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩)





theorem bitCompareWithWork_matches (left right : List Bool) :
    orderingMatches (bitCompareWithWork left right).1 (bitWordValue left) (bitWordValue right) := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => simp [bitCompareNilLeftWithWork, orderingMatches, bitWordValue]
    | cons b bs ih =>
      simpa only [bitCompareNilLeftWithWork, bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using bitOrdering_matches (bitCompareNilLeftWithWork bs).1 false b 0 (bitWordValue bs) ih
  | cons a as ih =>
    cases right with
    | nil =>
      simpa only [bitCompareWithWork, bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using bitOrdering_matches (bitCompareWithWork as []).1 a false (bitWordValue as) 0 (ih [])
    | cons b bs =>
      simpa only [bitCompareWithWork, bitWordValue] using
        bitOrdering_matches (bitCompareWithWork as bs).1 a b (bitWordValue as) (bitWordValue bs) (ih bs)

theorem bitCompareWithWork_lt (left right : List Bool) :
    (bitCompareWithWork left right).1 = .lt ↔ bitWordValue left < bitWordValue right := by
  have h := bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

theorem bitCompareWithWork_eq (left right : List Bool) :
    (bitCompareWithWork left right).1 = .eq ↔ bitWordValue left = bitWordValue right := by
  have h := bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

theorem bitCompareWithWork_cost (left right : List Bool) :
    (bitCompareWithWork left right).2 ≤ 4 * (left.length + right.length) + 1 := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => simp [bitCompareNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitCompareNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [bitCompareWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs
      simp only [bitCompareWithWork, List.length_cons] at *
      omega



theorem binaryNaturalCompareWithWork_lt (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).1 = .lt ↔ a < b := by
  simpa only [binaryNaturalCompareWithWork, bitWordValue_bits] using bitCompareWithWork_lt a.bits b.bits

theorem binaryNaturalCompareWithWork_eq (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).1 = .eq ↔ a = b := by
  simpa only [binaryNaturalCompareWithWork, bitWordValue_bits] using bitCompareWithWork_eq a.bits b.bits

theorem binaryNaturalCompareWithWork_cost (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).2 ≤ 4 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalCompareWithWork, Nat.size_eq_bits_len] using bitCompareWithWork_cost a.bits b.bits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySubtractWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Ripple-borrow subtraction, used after the magnitude comparison in
signed-integer addition. No unit-cost operation on unbounded integers is
used by this Boolean routine. -/

namespace EditApproximation





theorem bitSubtractor_value (a b borrow : Bool) :
    a.toNat + 2 * (bitBorrow a b borrow).toNat =
      b.toNat + borrow.toNat + (bitDifference a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- Ripple-borrow subtraction when the minuend has no remaining bits. -/




theorem bitSubtractWithWork_length (left right : List Bool) (borrow : Bool) :
    (bitSubtractWithWork left right borrow).1.length = max left.length right.length := by
  induction left generalizing right borrow with
  | nil =>
    simp only [bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [bitSubtractNilLeftWithWork]
    | cons b bs ih => simp [bitSubtractNilLeftWithWork, ih]
  | cons a as ih =>
    cases right with
    | nil => simp [bitSubtractWithWork, ih]
    | cons b bs => simp [bitSubtractWithWork, ih, Nat.succ_max_succ]

theorem bitSubtractionRippleEquation (a b borrow nextBorrow difference left right result tail : ℕ)
    (htail : result + right + nextBorrow = left + tail)
    (hbit : a + 2 * nextBorrow = b + borrow + difference) :
    (difference + 2 * result) + (b + 2 * right) + borrow =
      (a + 2 * left) + 2 * tail := by
  omega

theorem bitSubtractWithWork_value (left right : List Bool) (borrow : Bool) :
    bitWordValue (bitSubtractWithWork left right borrow).1 + bitWordValue right + borrow.toNat =
      bitWordValue left + 2 ^ max left.length right.length *
        (bitSubtractWithWork left right borrow).2.1.toNat := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => simp [bitSubtractWithWork, bitSubtractNilLeftWithWork, bitWordValue]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      have hb := bitSubtractor_value false b borrow
      simp only [bitSubtractWithWork, bitSubtractNilLeftWithWork, bitWordValue,
        List.length_nil, List.length_cons, Nat.zero_max, pow_succ, Bool.toNat_false] at h hb ⊢
      have hs := bitSubtractionRippleEquation 0 b.toNat borrow.toNat (bitBorrow false b borrow).toNat
        (bitDifference false b borrow).toNat 0 (bitWordValue bs)
        (bitWordValue (bitSubtractNilLeftWithWork bs (bitBorrow false b borrow)).1)
        (2 ^ bs.length * (bitSubtractNilLeftWithWork bs (bitBorrow false b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      have hb := bitSubtractor_value a false borrow
      simp only [bitSubtractWithWork, bitWordValue, List.length_nil, List.length_cons,
        Nat.max_zero, pow_succ, Bool.toNat_false] at h hb ⊢
      have hs := bitSubtractionRippleEquation a.toNat 0 borrow.toNat (bitBorrow a false borrow).toNat
        (bitDifference a false borrow).toNat (bitWordValue as) 0
        (bitWordValue (bitSubtractWithWork as [] (bitBorrow a false borrow)).1)
        (2 ^ as.length * (bitSubtractWithWork as [] (bitBorrow a false borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      have hb := bitSubtractor_value a b borrow
      simp only [bitSubtractWithWork, bitWordValue, List.length_cons, Nat.succ_max_succ,
        pow_succ] at h hb ⊢
      have hs := bitSubtractionRippleEquation a.toNat b.toNat borrow.toNat (bitBorrow a b borrow).toNat
        (bitDifference a b borrow).toNat (bitWordValue as) (bitWordValue bs)
        (bitWordValue (bitSubtractWithWork as bs (bitBorrow a b borrow)).1)
        (2 ^ max as.length bs.length * (bitSubtractWithWork as bs (bitBorrow a b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hs

theorem bitWordValue_lt_pow_length (bits : List Bool) : bitWordValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitWordValue]
  | cons bit bits ih =>
    cases bit <;> simp only [bitWordValue, List.length_cons, pow_succ, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem bitSubtractWithWork_sub (left right : List Bool) (h : bitWordValue right ≤ bitWordValue left) :
    bitWordValue (bitSubtractWithWork left right false).1 = bitWordValue left - bitWordValue right := by
  have hvalue := bitSubtractWithWork_value left right false
  have hlt := bitWordValue_lt_pow_length (bitSubtractWithWork left right false).1
  rw [bitSubtractWithWork_length] at hlt
  cases hb : (bitSubtractWithWork left right false).2.1
  · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hvalue
    omega
  · simp only [hb, Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hvalue
    omega



theorem binaryNaturalSubtractWithWork_value (a b : ℕ) (h : b ≤ a) :
    bitWordValue (binaryNaturalSubtractWithWork a b).1 = a - b := by
  simpa only [binaryNaturalSubtractWithWork, bitWordValue_bits] using
    bitSubtractWithWork_sub a.bits b.bits (by simpa only [bitWordValue_bits] using h)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_SignedBinaryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Signed integers represented by a sign bit and a Boolean magnitude word.
Arithmetic uses Boolean ripple and shift-add routines. -/

namespace EditApproximation





namespace SignedBinary











@[simp] theorem value_ofInt (a : ℤ) : (ofInt a).value = a := by
  by_cases h : a < 0
  · simpa only [ofInt, value, bitWordValue_bits, signedMagnitude, h, decide_true,
      ↓reduceIte] using (Int.eq_neg_natAbs_of_nonpos (by omega : a ≤ 0)).symm
  · simpa only [ofInt, value, bitWordValue_bits, signedMagnitude, h, decide_false,
      Bool.false_eq_true, ↓reduceIte] using (Int.eq_natAbs_of_nonneg (by omega : 0 ≤ a)).symm

@[simp] theorem value_neg (a : SignedBinary) : a.neg.value = -a.value := by
  cases a with
  | mk negative bits => cases negative <;> simp [neg, value, signedMagnitude]

theorem subtract_signed_value (negative : Bool) (a b : List Bool)
    (h : bitWordValue b ≤ bitWordValue a) :
    signedMagnitude negative (bitWordValue (bitSubtractWithWork a b false).1) =
      signedMagnitude negative (bitWordValue a) - signedMagnitude negative (bitWordValue b) := by
  rw [bitSubtractWithWork_sub a b h]
  cases negative <;> simp only [signedMagnitude, Bool.false_eq_true, ↓reduceIte ]
  · exact Int.ofNat_sub h
  · rw [Int.ofNat_sub h]
    ring

theorem addWithWork_value (a b : SignedBinary) :
    (a.addWithWork b).1.value = a.value + b.value := by
  by_cases hsign : a.negative = b.negative
  · simp only [addWithWork, hsign, ↓reduceIte, value, bitAddWithWork_value,
      Bool.toNat_false, Nat.add_zero]
    rw [← hsign]
    cases a.negative <;> simp [signedMagnitude, add_comm]
  · simp only [addWithWork, hsign, ↓reduceIte]
    have hcomparison := bitCompareWithWork_matches a.bits b.bits
    rcases hcomparison with ⟨hcompare, hlt⟩ | ⟨hcompare, heq⟩ | ⟨hcompare, hgt⟩
    · rw [hcompare]
      change signedMagnitude b.negative (bitWordValue (bitSubtractWithWork b.bits a.bits false).1) = _
      rw [subtract_signed_value b.negative b.bits a.bits hlt.le]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude]
      all_goals ring
    · rw [hcompare]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude, bitWordValue]
    · rw [hcompare]
      change signedMagnitude a.negative (bitWordValue (bitSubtractWithWork a.bits b.bits false).1) = _
      rw [subtract_signed_value a.negative a.bits b.bits hgt.le]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude]
      all_goals ring

theorem mulWithWork_value (a b : SignedBinary) :
    (a.mulWithWork b).1.value = a.value * b.value := by
  simp only [mulWithWork, value, bitMulWithWork_value]
  cases a.negative <;> cases b.negative <;> simp [signedMagnitude]

end SignedBinary
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_SignedBinaryOrderWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Signed comparisons performed on Boolean magnitude words, including the
noncanonical negative-zero representation. -/

namespace EditApproximation
namespace SignedBinary



theorem nonzeroWithWork_value (bits : List Bool) :
    (nonzeroWithWork bits).1 = true ↔ bitWordValue bits ≠ 0 := by
  simp [nonzeroWithWork, bitCompareWithWork_eq, bitWordValue]



theorem ltWithWork_value (a b : SignedBinary) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  cases ha : a.negative <;> cases hb : b.negative
  · simp [ltWithWork, ha, hb, value, signedMagnitude, bitCompareWithWork_lt]
  · simp [ltWithWork, ha, hb, value, signedMagnitude]
  · simp only [ltWithWork, ha, hb, ↓reduceIte, Bool.false_eq_true,
      Bool.or_eq_true, nonzeroWithWork_value, value, signedMagnitude]
    omega
  · simp [ltWithWork, ha, hb, value, signedMagnitude, bitCompareWithWork_lt]

end SignedBinary
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFractionWork
attribute [-simp] _root_.OAI.EditApproximation.UnreducedRational.optimizerStep_value _root_.OAI.EditApproximation.UnreducedRational.value_nat _root_.OAI.EditApproximation.UnreducedRational.value_one _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Unreduced fractions stored as Boolean words. Every numerator operation
below runs the literal signed ripple/shift-add code; denominator products
run the literal Boolean multiplication routine. -/

namespace EditApproximation



namespace BinaryFraction





@[simp] theorem representation_value (a : BinaryFraction) : a.representation.value = a.value := rfl





@[simp] theorem denominatorInteger_value (a : BinaryFraction) :
    a.denominatorInteger.value = (bitWordValue a.denominator : ℤ) := rfl





theorem addWithWork_representation (a b : BinaryFraction) :
    (a.addWithWork b).1.representation = a.representation.add b.representation := by
  apply UnreducedRational.eq_of_num_den
  · simp only [addWithWork, representation, UnreducedRational.add,
      SignedBinary.addWithWork_value, SignedBinary.mulWithWork_value, denominatorInteger_value]
  · exact bitMulWithWork_value a.denominator b.denominator

theorem mulWithWork_representation (a b : BinaryFraction) :
    (a.mulWithWork b).1.representation = a.representation.mul b.representation := by
  apply UnreducedRational.eq_of_num_den
  · exact SignedBinary.mulWithWork_value a.numerator b.numerator
  · exact bitMulWithWork_value a.denominator b.denominator

theorem zero_representation : zero.representation = UnreducedRational.zero := by
  apply UnreducedRational.eq_of_num_den <;> rfl

theorem neg_representation (a : BinaryFraction) :
    a.neg.representation = a.representation.neg := by
  apply UnreducedRational.eq_of_num_den
  · exact SignedBinary.value_neg a.numerator
  · rfl

theorem invWithWork_representation (a : BinaryFraction) :
    (a.invWithWork).1.representation = a.representation.inv := by
  unfold invWithWork
  dsimp only
  split_ifs with h
  · have hz : bitWordValue a.numerator.bits = 0 := by
      simpa only [bitWordValue] using (bitCompareWithWork_eq a.numerator.bits []).1 h
    have hv : a.numerator.value = 0 := by simp [SignedBinary.value, signedMagnitude, hz]
    simp only [UnreducedRational.inv, representation, hv, ↓reduceDIte]
    exact zero_representation
  · have hn : bitWordValue a.numerator.bits ≠ 0 := by
      intro hz
      exact h ((bitCompareWithWork_eq a.numerator.bits []).2 (by simpa [bitWordValue] using hz))
    have hv : a.numerator.value ≠ 0 := by
      cases hs : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, hs, hn]
    simp only [UnreducedRational.inv, representation, hv, ↓reduceDIte]
    apply UnreducedRational.eq_of_num_den
    · cases hs : a.numerator.negative <;>
        simp [SignedBinary.value, signedMagnitude, hs, Int.sign_natCast_of_ne_zero hn]
    · cases hs : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, hs]



theorem ltWithWork_representation (a b : BinaryFraction) :
    (a.ltWithWork b).1 = a.representation.lt b.representation := by
  apply Bool.eq_iff_iff.mpr
  rw [UnreducedRational.lt_eq_true]
  simp only [ltWithWork, SignedBinary.ltWithWork_value, SignedBinary.mulWithWork_value,
    denominatorInteger_value, representation_value]
  unfold value
  rw [div_lt_div_iff₀ (by exact_mod_cast a.denominator_pos : (0 : ℚ) < bitWordValue a.denominator)
    (by exact_mod_cast b.denominator_pos : (0 : ℚ) < bitWordValue b.denominator)]
  exact_mod_cast (Iff.rfl :
    a.numerator.value * (bitWordValue b.denominator : ℤ) <
      b.numerator.value * (bitWordValue a.denominator : ℤ) ↔ _)

theorem ltWithWork_value (a b : BinaryFraction) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  rw [ltWithWork_representation, UnreducedRational.lt_eq_true]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CanonicalFractionWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fractions retain their unreduced numerator and denominator, but discard
leading zero bits after each operation. This exposes actual storage length
without charging or performing rational normalization. -/

namespace EditApproximation
namespace BinaryFraction



theorem canonicalizeWithWork_representation (a : BinaryFraction) :
    (canonicalizeWithWork a).1.representation = a.representation := by
  apply UnreducedRational.eq_of_num_den
  · simp only [canonicalizeWithWork, representation, SignedBinary.value, trimBitWordWithWork_value]
  · exact trimBitWordWithWork_value a.denominator





theorem canonicalAddWithWork_representation (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.representation = a.representation.add b.representation := by
  rw [canonicalAddWithWork, canonicalizeWithWork_representation, addWithWork_representation]

theorem canonicalMulWithWork_representation (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.representation = a.representation.mul b.representation := by
  rw [canonicalMulWithWork, canonicalizeWithWork_representation, mulWithWork_representation]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction

@[simp] theorem vector_map_get {α β : Type*} {d : ℕ} (f : α → β) (v : Vector α d) (i : Fin d) :
    (v.map f).get i = f (v.get i) := Vector.getElem_map f i.isLt




@[simp] theorem nat_representation (n : ℕ) : (nat n).representation = UnreducedRational.nat n := by
  apply UnreducedRational.eq_of_num_den
  · change (SignedBinary.ofInt (n : ℤ)).value = (n : ℤ)
    exact SignedBinary.value_ofInt _
  · rfl



theorem one_representation : one.representation = UnreducedRational.one := by
  rw [one, nat_representation]
  rfl



theorem subWithWork_representation (a b : BinaryFraction) :
    (a.subWithWork b).1.representation = a.representation.sub b.representation := by
  simp only [subWithWork, canonicalAddWithWork_representation, neg_representation,
    UnreducedRational.sub]



theorem divWithWork_representation (a b : BinaryFraction) :
    (a.divWithWork b).1.representation = a.representation.div b.representation := by
  simp only [divWithWork, canonicalMulWithWork_representation, invWithWork_representation,
    UnreducedRational.div]



theorem dotListWithWork_representation {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) :
    (dotListWithWork left right indices).1.representation =
      UnreducedRational.dotList (left.map representation) (right.map representation) indices := by
  induction indices with
  | nil => exact zero_representation
  | cons i rest ih =>
    simp only [dotListWithWork, canonicalAddWithWork_representation,
      canonicalMulWithWork_representation, UnreducedRational.dotList, ih, vector_map_get]



theorem dotWithWork_representation {d : ℕ} (left right : Vector BinaryFraction d) :
    (dotWithWork left right).1.representation =
      UnreducedRational.dot (left.map representation) (right.map representation) :=
  dotListWithWork_representation _ _ _



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

def logarithmStorageBudget (B K : ℕ) : ℕ :=
  Nat.size (2 * K) + 2 * (K * K * (4 * B + 18) +
    K * (Nat.size (2 * K + 1) + 1) + 1) + 1

def gradientStorageBudget (G pointBits linearBits : ℕ) : ℕ :=
  4 * logarithmStorageBudget (2 * pointBits + 2 * (5 + 50 * (Nat.size G + 2)) + 2) (G ^ 60) +
    2 * linearBits + 18

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit-operation bounds for the literal Boolean arithmetic calls and
bounded-width power loops used inside the entropy optimizer. -/

namespace EditApproximation
namespace BinaryFraction

def dotWordBudget (n B V : ℕ) : ℕ :=
  B + Nat.size (n * V * V) + 2 * (1 + n * (B + B)) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLogWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the finite logarithm series on unreduced Boolean fractions.
Every bound is for the executed power/division/addition loops. -/

namespace EditApproximation
namespace BinaryFraction

def logarithmPartialWordBudget (b : BinaryFraction) (K : ℕ) : ℕ :=
  b.width +
    (Nat.size K + 2 * (K * K * Nat.size b.representation.den +
      K * (Nat.size (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * Nat.size b.representation.den + 1) + 2) +
    Nat.size (2 * K + 1) + 10

def logarithmPartialBitStep (W K : ℕ) : ℕ :=
  (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) +
    2100 * (W + 2) ^ 2 + 6000 * (W + 1) ^ 2 + Nat.size (2 * K + 1) + 6

def logarithmUniversalWordBudget (B K : ℕ) : ℕ :=
  B + (Nat.size K + 2 * (K * K * B + K * (Nat.size (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * B + 1) + 2) + Nat.size (2 * K + 1) + 10

def logarithmRatio (r : BinaryFraction) : BinaryFraction :=
  ((r.subWithWork one).1.divWithWork (canonicalAddWithWork r one).1).1

def logarithmBitBudget (B K : ℕ) : ℕ :=
  let W := logarithmUniversalWordBudget (8 * B + 22) K
  12000 * (B + 4) ^ 2 + 2100 * (4 * B + 12) ^ 2 +
    K * logarithmPartialBitStep W K + 2000 * (W + 5) ^ 2 + 10

def generalPowerWordBudget (a : BinaryFraction) (n : ℕ) : ℕ :=
  a.width + 3 + n * (2 * a.width + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGradientWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bit-operation bound for each actually materialized gradient coordinate. -/

namespace EditApproximation
namespace BinaryFraction

def smoothingStorageBudget (G : ℕ) : ℕ := 3 + 50 * (Nat.size G + 2)

def shiftedStorageBudget (G pointBits : ℕ) : ℕ := 4 * pointBits + 2 * smoothingStorageBudget G + 8

def gradientLogStorageBudget (G pointBits : ℕ) : ℕ :=
  UnreducedRational.logarithmStorageBudget (shiftedStorageBudget G pointBits) (G ^ 60)

def gradientCellBitBudget (G pointBits linearBits : ℕ) : ℕ :=
  let S := smoothingStorageBudget G
  let R := shiftedStorageBudget G pointBits
  let L := gradientLogStorageBudget G pointBits
  (1 + 50 * (2000 * (generalPowerWordBudget (nat G) 50 + 1) ^ 2 + 1)) +
    (4 * S + 3) + 6000 * (pointBits + S + 2) ^ 2 + logarithmBitBudget R (G ^ 60) +
    (6000 * (L + 4) ^ 2 + 1) + 6000 * (linearBits + 2 * L + 9) ^ 2 + Nat.size G + 70

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMaximizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted stored-score maximization for Boolean fraction coordinates. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def maximizerWordBudget (d B V : ℕ) : ℕ := dotWordBudget d B V

def maximizerBitBudget (d v B V : ℕ) : ℕ :=
  let W := maximizerWordBudget d B V
  v * (1 + d * (100000 * (W + 1) ^ 2) + 1000 * (W + 1) ^ 2 + 2) + d + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUpdateWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the actual coordinate update, including construction of
its rational step and complement. -/

namespace EditApproximation
namespace BinaryFraction

def updateCoefficientWordBudget (K : ℕ) : ℕ := Nat.size (K + 2) + 8

def updateCoordinateWordBudget (K P : ℕ) : ℕ := P + 2 * updateCoefficientWordBudget K + 8

def optimizerUpdateBitBudget (d K P : ℕ) : ℕ :=
  2100 * (Nat.size (K + 2) + 6) ^ 2 +
    (6000 * (updateCoefficientWordBudget K + 4) ^ 2 + 1) +
    d * (110000 * (updateCoordinateWordBudget K P + 1) ^ 2 + 6) + Nat.size (K + 2) + 4

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total bit operations of the executed Boolean-fraction optimizer.
The bound includes logarithm sums, gradient materialization, scored vertex
search and every coordinate update, with no unit-cost rational primitive. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def optimizerPointWordBudget (K B Bv : ℕ) : ℕ :=
  Bv + 2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2

def optimizerGradientWordBudget (G K B Bv L : ℕ) : ℕ :=
  UnreducedRational.gradientStorageBudget G (2 * optimizerPointWordBudget K B Bv + 1) (2 * L + 1)

def optimizerRoundBitBudget (d v G K B Bv L V : ℕ) : ℕ :=
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  d * (gradientCellBitBudget G P L + 6) +
    maximizerBitBudget d v (max P W) (2 * G ^ 60 + 1 + V + 1) +
    optimizerUpdateBitBudget d K P + 3

def optimizerBitBudget (d v G K B Bv L V : ℕ) : ℕ :=
  d + 1 + K * optimizerRoundBitBudget d v G K B Bv L V

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryActionSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The final Boolean maximization retains the actual action label. This
is the sampled atom of the optimizer, rather than its averaged vector. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def selectionBitBudget (d vertices G K B Bv L V : ℕ) : ℕ :=
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  optimizerBitBudget d vertices G K B Bv L V + d * (gradientCellBitBudget G P L + 6) +
    maximizerBitBudget d vertices (max P W) (2 * G ^ 60 + 1 + V + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Interval-state edit geometry

The edit distance here is the repository's unrestricted unit-cost
insertion/deletion/substitution distance, not an abstract metric supplied
as a hypothesis. These are the length and endpoint bounds in Section 2.
-/

namespace EditApproximation

open EditDistortion

universe u

/-- The target substring with boundary indices `lo` and `hi`. -/


theorem substring_length {α : Type u} (word : List α) (lo hi : ℕ)
    (hhi : hi ≤ word.length) : (substring word lo hi).length = hi - lo := by
  simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left hhi]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

structure BellmanAction (Parent Child : Type*) (M : ℕ) where
  center : Parent
  connection : ℝ
  childState : Fin M → Child

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Grid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer endpoint grids

Rounding is an executable integer division. It preserves valid interval
states and shared endpoints, and the edit-distance perturbation is bounded
by the actual two remainders. No real-valued grid is substituted for it.
-/

namespace EditApproximation



@[simp] theorem gridRound_one (position : ℕ) : gridRound 1 position = position := by
  simp [gridRound]



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PublishedInputs
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar Bernstein concentration

The only concentration input needed by the coarse estimator and the shared
group sampler is finite scalar Bernstein: Joel A. Tropp, *ACM 217:
Probability in High Dimensions*, Caltech CMS Lecture Notes 2021-01,
corrected March 2023, Theorem 4.16 (printed p. 36).
https://tropp.caltech.edu/notes/Tro21-Probability-High-LN-corr.pdf

`FiniteBernsteinInput` states the bound for centered bounded finite sums
with an upper bound on their summed variances. Independence identifies the
variance of the sum with the sum of the variances. Positivity of the proxy
avoids the zero-denominator case.
-/

namespace EditApproximation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The finite centered-sum specialization of Tropp, Theorem 4.16.
This is the exact Lean proposition to be passed explicitly to downstream
concentration theorems. -/
def FiniteBernsteinInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (bound varianceProxy deviation : ℝ),
    0 < bound → 0 < varianceProxy → 0 < deviation →
    iIndepFun X μ → (∀ i, Measurable (X i)) →
    (∀ i, Integrable (X i) μ) →
    (∀ i, (∫ ω, X i ω ∂μ) = 0) →
    (∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ bound) →
    (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ varianceProxy →
    μ.real {ω | deviation ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-deviation ^ 2 /
        (2 * varianceProxy + (2 / 3 : ℝ) * bound * deviation))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRounding
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer rounding spacings from the dyadic band envelopes

Taking the nonnegative part of the dyadic product exponent computes the
integer spacing max(1, theta*h). The resulting spacing preserves the wide
grid by actual divisibility of powers of two.
-/

namespace EditApproximation

open Finset





theorem dyadic_nonnegative_spacing (exponent : ℤ) :
    ((2 ^ exponent.toNat : ℕ) : ℚ) = max 1 ((2 : ℚ) ^ exponent) := by
  by_cases hnonneg : 0 ≤ exponent
  · have hcast : ((exponent.toNat : ℕ) : ℤ) = exponent := Int.toNat_of_nonneg hnonneg
    have hone : (1 : ℚ) ≤ 2 ^ exponent := by
      exact one_le_zpow₀ (by norm_num) hnonneg
    rw [max_eq_right hone, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hcast]
  · have hnegative : exponent ≤ 0 := by omega
    have htoNat : exponent.toNat = 0 := Int.toNat_eq_zero.mpr hnegative
    have hone : (2 : ℚ) ^ exponent ≤ 1 := by
      simpa only [zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hnegative
    simp only [htoNat, pow_zero, Nat.cast_one, max_eq_left hone]

theorem bandRoundSpacing_exact {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (bandRoundSpacing thetaExponent b band initial i : ℚ) =
      max 1 ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i) := by
  rw [bandRoundSpacing, dyadic_nonnegative_spacing]
  unfold bandChildEnvelope rationalDyadicCeiling bandEnvelopeExponent
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 2
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

def listedBandCoordinateVector {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) : Vector (Fin M × σ) (listedBandCoordinates band).length :=
  Vector.ofFn (listedBandCoordinates band).get

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual Boolean construction of the normalized band vertices.
The input masses are stored fractions; their sum and divisions use the
counted routines and no reduced-rational conversion is performed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem value_abs_le_pow_width (a : BinaryFraction) : |a.value| ≤ (2 : ℚ) ^ a.width := by
  have hn := (bitWordValue_lt_pow_length a.numerator.bits).le
  have hw : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hn' : bitWordValue a.numerator.bits ≤ 2 ^ a.width :=
    hn.trans (Nat.pow_le_pow_right (by decide) hw)
  have hden : (1 : ℚ) ≤ bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  have habs : |(a.numerator.value : ℚ)| = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  unfold value
  rw [abs_div, habs, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hden)]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hden)).mpr
  have hnQ : (bitWordValue a.numerator.bits : ℚ) ≤ (2 : ℚ) ^ a.width := by exact_mod_cast hn'
  exact hnQ.trans (le_mul_of_one_le_right (by positivity) hden)



theorem bandMassTotalWithWork_value {M : ℕ} (mass : Vector BinaryFraction M) :
    (bandMassTotalWithWork mass).1.value = ∑ i, (mass.get i).value := by
  rw [bandMassTotalWithWork, ← representation_value, dotWithWork_representation,
    UnreducedRational.dot_value]
  simp [one_representation]

def bandMassTotalStorageBudget (M B : ℕ) : ℕ :=
  Nat.size M + B + 2 * (1 + M * (B + 1)) + 2

def bandVertexWordBudget (M B : ℕ) : ℕ := 2 * B + bandMassTotalStorageBudget M B + 3

def bandCoordinateWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) : BinaryFraction × ℕ :=
  if coordinate.2 = action coordinate.1 then divWithWork (mass.get coordinate.1) total else (zero, 1)

def bandVerticesWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : List (Vector BinaryFraction d) × ℕ :=
  let total := bandMassTotalWithWork mass
  let vertices := band.map fun action => vectorMapWithWork d fun i =>
    bandCoordinateWithWork mass total.1 action (coordinates.get i)
  (vertices.map Prod.fst, total.2 + (vertices.map Prod.snd).sum + 6 * band.length)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDyadicCeiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The dyadic envelope is found by a bounded sequence of exact Boolean
comparisons.  The scan starts at `2⁻ᴮ`, doubles at most `2B` times, and uses
the stored fraction width `B`; no real logarithm is evaluated. -/

namespace EditApproximation



theorem powerTwoWord_value (n : ℕ) : bitWordValue (powerTwoWord n) = 2 ^ n := by
  induction n with
  | zero => simp [powerTwoWord, bitWordValue]
  | succ n ih =>
    simp only [powerTwoWord, List.replicate_succ, List.cons_append, bitWordValue,
      Bool.toNat_false, zero_add] at *
    rw [ih, pow_succ]
    omega

namespace BinaryFraction



theorem inversePowerTwo_value (n : ℕ) : (inversePowerTwo n).value = (2 : ℚ) ^ (-(n : ℤ)) := by
  simp only [inversePowerTwo, value, SignedBinary.value, signedMagnitude, Bool.false_eq_true,
    ↓reduceIte, bitWordValue, Bool.toNat_true,
    Int.cast_natCast, powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast]
  norm_num [one_div]



theorem doubleFraction_value (a : BinaryFraction) : (doubleFraction a).value = 2 * a.value := by
  cases h : a.numerator.negative <;>
    simp [doubleFraction, value, SignedBinary.value, signedMagnitude, h, bitWordValue] <;> ring



theorem dyadicCeiling_eq_of_bounds (r : ℚ) (e : ℤ) (hr : 0 < r)
    (hlower : (2 : ℚ) ^ (e - 1) < r) (hupper : r ≤ (2 : ℚ) ^ e) :
    rationalDyadicCeiling r = (2 : ℚ) ^ e := by
  have hl := (Int.zpow_lt_iff_lt_clog (by decide : 1 < 2) hr).mp hlower
  have hu := (Int.le_zpow_iff_clog_le (by decide : 1 < 2) hr).mp hupper
  have he : Int.clog 2 r = e := by omega
  rw [rationalDyadicCeiling, he]

theorem dyadicScanWithWork_value (a candidate : BinaryFraction) (n : ℕ) (e : ℤ)
    (ha : 0 < a.value) (hc : candidate.value = (2 : ℚ) ^ e)
    (hlower : (2 : ℚ) ^ (e - 1) < a.value)
    (hupper : a.value ≤ candidate.value * (2 : ℚ) ^ n) :
    (dyadicScanWithWork a candidate n).1.value = rationalDyadicCeiling a.value := by
  induction n generalizing candidate e with
  | zero =>
    simp only [pow_zero, mul_one] at hupper
    exact hc.trans (dyadicCeiling_eq_of_bounds a.value e ha hlower (hc ▸ hupper)).symm
  | succ n ih =>
    unfold dyadicScanWithWork
    dsimp only
    split_ifs with hlt
    · have hlt' := (ltWithWork_value candidate a).mp hlt
      have hc' : (doubleFraction candidate).value = (2 : ℚ) ^ (e + 1) := by
        rw [doubleFraction_value, hc, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
        ring
      apply ih _ (e + 1) hc'
      · simpa only [add_sub_cancel_right, ← hc] using hlt'
      · rw [doubleFraction_value]
        simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hupper
    · have hupper' : a.value ≤ candidate.value :=
        le_of_not_gt (fun h => hlt ((ltWithWork_value candidate a).mpr h))
      exact hc.trans (dyadicCeiling_eq_of_bounds a.value e ha hlower (hc ▸ hupper')).symm

theorem positive_value_lower (a : BinaryFraction) (ha : 0 < a.value) :
    (2 : ℚ) ^ (-(a.width : ℤ)) ≤ a.value := by
  have hd : (0 : ℚ) < bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  have hn : (0 : ℚ) < a.numerator.value := (div_pos_iff_of_pos_right hd).mp ha
  have hnum : (1 : ℚ) ≤ a.numerator.value := by
    have hnZ : (0 : ℤ) < a.numerator.value := by exact_mod_cast hn
    exact_mod_cast (show (1 : ℤ) ≤ a.numerator.value by omega)
  have hden : (bitWordValue a.denominator : ℚ) ≤ (2 : ℚ) ^ a.width := by
    exact_mod_cast (bitWordValue_lt_pow_length a.denominator).le.trans
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [zpow_neg, zpow_natCast, ← one_div]
  change 1 / (2 : ℚ) ^ a.width ≤ (a.numerator.value : ℚ) / bitWordValue a.denominator
  apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) _) hd).mpr
  simpa only [one_mul] using
    hden.trans (le_mul_of_one_le_left (pow_nonneg (by norm_num) _) hnum)



theorem dyadicCeilingWithWork_value (a : BinaryFraction) (ha : 0 < a.value) :
    (dyadicCeilingWithWork a).1.value = rationalDyadicCeiling a.value := by
  apply dyadicScanWithWork_value a (inversePowerTwo a.width) (2 * a.width) (-(a.width : ℤ)) ha
    (inversePowerTwo_value _)
  · have hpos : (0 : ℚ) < (2 : ℚ) ^ (-(a.width : ℤ) - 1) := zpow_pos (by norm_num) _
    have hdouble : (2 : ℚ) ^ (-(a.width : ℤ) - 1) * 2 = (2 : ℚ) ^ (-(a.width : ℤ)) := by
      rw [← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1
      omega
    have hl := positive_value_lower a ha
    nlinarith only [hpos, hdouble, hl]
  · rw [inversePowerTwo_value, ← zpow_natCast]
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    have he : -(a.width : ℤ) + (2 * a.width : ℕ) = (a.width : ℤ) := by omega
    rw [he, zpow_natCast]
    exact (le_abs_self _).trans (value_abs_le_pow_width a)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem canonicalAddWithWork_value (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.value = a.value + b.value := by
  rw [← representation_value, canonicalAddWithWork_representation,
    UnreducedRational.value_add, representation_value, representation_value]

@[simp] theorem canonicalMulWithWork_value (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.value = a.value * b.value := by
  rw [← representation_value, canonicalMulWithWork_representation,
    UnreducedRational.value_mul, representation_value, representation_value]

@[simp] theorem divWithWork_value (a b : BinaryFraction) :
    (divWithWork a b).1.value = a.value / b.value := by
  rw [← representation_value, divWithWork_representation,
    UnreducedRational.value_div, representation_value, representation_value]

@[simp] theorem subWithWork_value (a b : BinaryFraction) :
    (subWithWork a b).1.value = a.value - b.value := by
  rw [← representation_value, subWithWork_representation,
    UnreducedRational.value_sub, representation_value, representation_value]

def gainWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let quotient := divWithWork (table s i).neg (mass i.1)
  (quotient.1, quotient.2 + 1)

def decrementWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let difference := subWithWork (table s i) (table (s + 1) i)
  let quotient := divWithWork difference.1 (mass i.1)
  (quotient.1, difference.2 + quotient.2 + 1)



def optimisticTermWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let gain := gainWithWork mass table s i
  let decrement := decrementWithWork mass table s i
  let scaled := canonicalMulWithWork coefficient decrement.1
  let total := canonicalAddWithWork gain.1 scaled.1
  (total.1, gain.2 + decrement.2 + scaled.2 + total.2 + 2)

@[simp] theorem decrementWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (decrementWithWork mass table s i).1.value =
      childDecrement (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [decrementWithWork, divWithWork_value, subWithWork_value, childDecrement]

@[simp] theorem coefficientWithWork_value (kappa : BinaryFraction) :
    (coefficientWithWork kappa).1.value = 1 - 2 * kappa.value := by
  simp only [coefficientWithWork, subWithWork_value, canonicalMulWithWork_value]
  rw [← representation_value one, one_representation, UnreducedRational.value_one,
    ← representation_value (nat 2), nat_representation, UnreducedRational.value_nat]
  norm_num

def onlineLinearWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let coefficient := coefficientWithWork kappa
  let terms := vectorMapWithWork t fun s => optimisticTermWithWork mass table coefficient.1 s.val i
  let history := bandMassTotalWithWork terms.1
  let current := gainWithWork mass table t i
  let total := canonicalAddWithWork history.1 current.1
  let result := canonicalMulWithWork eta total.1
  (result.1, coefficient.2 + terms.2 + history.2 + current.2 + total.2 + result.2 + 3)

def optimisticTermStorageBudget (Bm Bt Bc : ℕ) : ℕ := 20 * Bt + 8 * Bm + 4 * Bc + 30

def onlineLinearStorageBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  2 * Be + 2 * bandMassTotalStorageBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    2 * (2 * Bt + 2 * Bm + 4) + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean construction of the child envelope of a finite band.
It scans the actual child values, compares with `b/M`, and runs the exact
bounded dyadic scan. Table reads are accounted for by the query program. -/

namespace EditApproximation
namespace BinaryFraction



theorem maxWithWork_value (a b : BinaryFraction) :
    (maxWithWork a b).1.value = max a.value b.value := by
  by_cases h : a.value < b.value
  · simp only [maxWithWork, (ltWithWork_value a b).mpr h, ↓reduceIte, max_eq_right h.le]
  · have hb : (a.ltWithWork b).1 = false := Bool.eq_false_iff.mpr (fun hh => h ((ltWithWork_value a b).mp hh))
    simp only [maxWithWork, hb, Bool.false_eq_true, ↓reduceIte, max_eq_left (le_of_not_gt h)]



theorem maximumWithWork_value (fallback : BinaryFraction) (values : List BinaryFraction) :
    (maximumWithWork fallback values).1.value = rationalMaximum fallback.value (values.map value) := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    simp only [maximumWithWork, maxWithWork_value, ih, List.map_cons, rationalMaximum]

def bandEnvelopeWithWork {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M) : BinaryFraction × ℕ :=
  let floor := divWithWork (nat b) (nat M)
  let maximum := maximumWithWork zero (band.map fun action => initial i (action i))
  let input := maxWithWork floor.1 maximum.1
  let result := dyadicCeilingWithWork input.1
  (result.1, floor.2 + maximum.2 + input.2 + result.2 + band.length + 4)

theorem bandEnvelopeWithWork_value {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M)
    (hb : 0 < b) :
    (bandEnvelopeWithWork b band initial i).1.value =
      bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  have hM : 0 < M := Nat.pos_of_ne_zero (fun h => by cases h; exact Fin.elim0 i)
  have hfloor : (divWithWork (nat b) (nat M)).1.value = (b : ℚ) / M := by
    rw [divWithWork_value, ← representation_value (nat b), nat_representation,
      UnreducedRational.value_nat, ← representation_value (nat M), nat_representation,
      UnreducedRational.value_nat]
  have hp : 0 < (maxWithWork (divWithWork (nat b) (nat M)).1
      (maximumWithWork zero (band.map fun action => initial i (action i))).1).1.value := by
    rw [maxWithWork_value, hfloor]
    exact lt_of_lt_of_le (div_pos (by exact_mod_cast hb) (by exact_mod_cast hM)) (le_max_left _ _)
  change (dyadicCeilingWithWork _).1.value = _
  rw [dyadicCeilingWithWork_value _ hp, maxWithWork_value, hfloor, maximumWithWork_value]
  simp only [zero_representation, ← representation_value zero, UnreducedRational.value_zero,
    List.map_map, Function.comp_def, bandChildEnvelope]

def bandEnvelopeWordBudget (b M B : ℕ) : ℕ := B + Nat.size b + Nat.size M + 8


def bandEnvelopeBitBudget (b M size B : ℕ) : ℕ :=
  let W := bandEnvelopeWordBudget b M B
  2100 * (Nat.size b + Nat.size M + 6) ^ 2 +
    (1 + size * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + size + 4

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit-operation costs for preparing the actual stored band vertices.  The
large numerical values in the generic dot-product bound occur only inside
`Nat.size`; the resulting bound is polynomial in the stored word width. -/

namespace EditApproximation
namespace BinaryFraction

def storedSumWordBudget (n B : ℕ) : ℕ :=
  (B + 1) + Nat.size n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

def storedSumBitBudget (n B : ℕ) : ℕ :=
  1 + n * (100000 * (storedSumWordBudget n B + 1) ^ 2)

def bandCoordinateBitBudget (M B : ℕ) : ℕ :=
  2100 * (B + bandMassTotalStorageBudget M B + 2) ^ 2

def bandPreparationBitBudget (M d vertices B : ℕ) : ℕ :=
  storedSumBitBudget M B + vertices * (d * (bandCoordinateBitBudget M B + 6)) + 6 * vertices

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite optimistic-history builder uses only the charged Boolean
fraction instructions.  These bounds derive every intermediate width from
the stored table and mass widths. -/

namespace EditApproximation
namespace BinaryFraction

def gainBitBudget (Bm Bt : ℕ) : ℕ := 2100 * (Bm + Bt + 2) ^ 2 + 1

def decrementBitBudget (Bm Bt : ℕ) : ℕ :=
  6000 * (Bt + 1) ^ 2 + 2100 * (8 * Bt + Bm + 8) ^ 2 + 2

def coefficientBitBudget (Bk : ℕ) : ℕ :=
  2000 * (Bk + 3) ^ 2 + 6000 * (2 * Bk + 7) ^ 2 + 2

def optimisticTermWordBudget (Bm Bt Bc : ℕ) : ℕ := 8 * Bt + 2 * Bm + 2 * Bc + 12

def optimisticTermBitBudget (Bm Bt Bc : ℕ) : ℕ :=
  gainBitBudget Bm Bt + decrementBitBudget Bm Bt +
    2000 * (optimisticTermWordBudget Bm Bt Bc + 1) ^ 2 +
    6000 * (optimisticTermWordBudget Bm Bt Bc + 1) ^ 2 + 2

def onlineFinalWordBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  Be + bandMassTotalStorageBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    (2 * Bt + 2 * Bm + 4) + 2

def onlineLinearBitBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  coefficientBitBudget Bk + t * (optimisticTermBitBudget Bm Bt (4 * Bk + 18) + 6) +
    storedSumBitBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    gainBitBudget Bm Bt + 6000 * (onlineFinalWordBudget Be Bk Bm Bt t + 1) ^ 2 +
    2000 * (2 * onlineFinalWordBudget Be Bk Bm Bt t + 3) ^ 2 + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryActualBandOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Boolean band optimizer constructs its envelopes from the
stored initial table, then constructs the vertices and history vector. The
normalized history bounds follow from actual band-coordinate membership. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def envelopeVectorWithWork {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) : Vector BinaryFraction M × ℕ :=
  vectorMapWithWork M (bandEnvelopeWithWork b band initial)

theorem envelopeVectorWithWork_value {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (hb : 0 < b) (i : Fin M) :
    ((envelopeVectorWithWork b band initial).1.get i).value =
      bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  simp only [envelopeVectorWithWork, vectorMapWithWork_value]
  exact bandEnvelopeWithWork_value b band initial i hb

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFiniteLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed finite filters and stored fraction reductions used by the
band tests. Callback costs and list construction are included. -/

namespace EditApproximation



theorem filterWithWork_value {α : Type*} (test : α → Bool × ℕ) (values : List α) :
    (filterWithWork test values).1 = values.filter (fun a => (test a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [filterWithWork, List.filter_cons, ih]

/-- Both branch values are visited; this makes the work count independent
of the outcome while returning the usual finite conjunction. -/


theorem allWithWork_value {α : Type*} (test : α → Bool × ℕ) (values : List α) :
    (allWithWork test values).1 = true ↔ ∀ a ∈ values, (test a).1 = true := by
  induction values with
  | nil => simp [allWithWork]
  | cons a rest ih => simp only [allWithWork, Bool.and_eq_true, ih, List.forall_mem_cons]

namespace BinaryFraction



theorem leWithWork_value (a b : BinaryFraction) :
    (a.leWithWork b).1 = true ↔ a.value ≤ b.value := by
  simp only [leWithWork, Bool.not_eq_true_eq_eq_false]
  rw [Bool.eq_false_iff]
  constructor
  · intro h
    exact le_of_not_gt (fun hlt => h ((ltWithWork_value b a).mpr hlt))
  · intro h hlt
    exact (not_lt_of_ge h) ((ltWithWork_value b a).mp hlt)




theorem minWithWork_value (a b : BinaryFraction) :
    (minWithWork a b).1.value = min a.value b.value := by
  by_cases h : a.value < b.value
  · simp only [minWithWork, (ltWithWork_value a b).mpr h, ↓reduceIte, min_eq_left h.le]
  · have hb : (a.ltWithWork b).1 = false :=
      Bool.eq_false_iff.mpr (fun hh => h ((ltWithWork_value a b).mp hh))
    simp only [minWithWork, hb, Bool.false_eq_true, ↓reduceIte, min_eq_right (le_of_not_gt h)]



theorem minimumWithWork_value (fallback : BinaryFraction) (values : List BinaryFraction) :
    (minimumWithWork fallback values).1.value = rationalMinimum fallback.value (values.map value) := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    simp only [minimumWithWork, minWithWork_value, ih, List.map_cons, rationalMinimum]



theorem sumListWithWork_value (values : List BinaryFraction) :
    (sumListWithWork values).1.value = (values.map value).sum := by
  rw [sumListWithWork, bandMassTotalWithWork_value]
  simp only [vector_get_ofFn]
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteEnumerationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal finite enumeration with counters. Each callback is evaluated
once and its returned work is charged; list cells and copied output cells
are charged separately. -/

namespace EditApproximation



theorem arithmeticMapWithWork_value {α β : Type*} (f : α → β × ℕ) (values : List α) :
    (arithmeticMapWithWork f values).1 = values.map (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [arithmeticMapWithWork, ih, List.map_cons]

theorem arithmeticMapWithWork_cost {α β : Type*} (f : α → β × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) :
    (arithmeticMapWithWork f values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp only [arithmeticMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
    simp only [arithmeticMapWithWork, List.length_cons]
    nlinarith only [ha, htail]



theorem arithmeticFlatMapWithWork_value {α β : Type*} (f : α → List β × ℕ) (values : List α) :
    (arithmeticFlatMapWithWork f values).1 = values.flatMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [arithmeticFlatMapWithWork, ih, List.flatMap_cons]

/-- Each complete assignment is stored in an array, so later coordinate
access is constant time. The recursive tail is constructed once. -/


theorem materializedAssignmentsWithWork_value {α : Type*} (M : ℕ) (choices : Fin M → List α) :
    ((materializedAssignmentsWithWork M choices).1.map Vector.get) = finiteAssignments M choices := by
  have hget {m : ℕ} (f : Fin m → α) : (Vector.ofFn f).get = f := funext (vector_get_ofFn f)
  induction M with
  | zero => simp only [materializedAssignmentsWithWork, finiteAssignments, List.map_cons,
      List.map_nil, hget]
  | succ M ih =>
    simp only [materializedAssignmentsWithWork, arithmeticFlatMapWithWork_value,
      arithmeticMapWithWork_value, List.map_flatMap, List.map_map, Function.comp_def, hget]
    unfold finiteAssignments
    apply List.flatMap_congr
    intro head _
    rw [← ih (fun i => choices i.succ), List.map_map]
    rfl

def materializedWideActionsWithWork {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) : List (Vector (TargetInterval ny) M) × ℕ :=
  materializedAssignmentsWithWork M (wideChildStateList parent r b P)

theorem materializedWideActionsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) :
    ((materializedWideActionsWithWork M parent r b P).1.map Vector.get) =
      wideActionList M parent r b P :=
  materializedAssignmentsWithWork_value M _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDistanceWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Absolute differences used in the literal prefix and band tests.
The sign update retains the magnitude words; subtraction uses signed
Boolean arithmetic. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem absolute_value (a : BinaryFraction) : a.absolute.value = |a.value| := by
  have hn : |(a.numerator.value : ℚ)| = (bitWordValue a.numerator.bits : ℚ) := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  have hd : (0 : ℚ) < bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  change (bitWordValue a.numerator.bits : ℚ) / bitWordValue a.denominator =
    |(a.numerator.value : ℚ) / bitWordValue a.denominator|
  rw [abs_div, hn, abs_of_pos hd]

@[simp] theorem absolute_width (a : BinaryFraction) : a.absolute.width = a.width := rfl

@[simp] theorem nat_value (n : ℕ) : (nat n).value = (n : ℚ) := by
  rw [← representation_value, nat_representation, UnreducedRational.value_nat]



@[simp] theorem distanceWithWork_value (a b : BinaryFraction) :
    (distanceWithWork a b).1.value = |a.value - b.value| := by
  simp only [distanceWithWork, absolute_value, subWithWork_value]

/-- List of the literal endpoint differences. Natural endpoints are encoded
when encountered, and their bit-writing work is charged here. -/


@[simp] theorem connectionTermsWithWork_length {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    (connectionTermsWithWork start states finish).1.length = states.length + 1 := by
  induction states generalizing start with
  | nil => rfl
  | cons state rest ih =>
    simp only [connectionTermsWithWork, List.length_cons, ih]

theorem connectionTermsWithWork_value {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    ((connectionTermsWithWork start states finish).1.map value).sum =
      rationalConnectionBudget start.value states finish.value := by
  induction states generalizing start with
  | nil => simp only [connectionTermsWithWork, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, distanceWithWork_value, rationalConnectionBudget]
  | cons state rest ih =>
    simp only [connectionTermsWithWork, List.map_cons, List.sum_cons,
      distanceWithWork_value, nat_value, ih, rationalConnectionBudget]

 def connectionTermsBitBudget (k B : ℕ) : ℕ :=
  (k + 1) * (6000 * (B + 1) ^ 2 + 4) + k * (2 * B + 6)



@[simp] theorem connectionWithWork_value {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    (connectionWithWork start finish states).1.value =
      rationalConnectionBudget start.value states finish.value := by
  simp only [connectionWithWork, sumListWithWork_value, connectionTermsWithWork_value]

def connectionWordBudget (k B : ℕ) : ℕ := bandMassTotalStorageBudget (k + 1) (8 * B + 6)

def connectionBitBudget (k B : ℕ) : ℕ :=
  connectionTermsBitBudget k B + storedSumBitBudget (k + 1) (8 * B + 6) + 6 * (k + 1) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryAffineGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean tests for the affine errors in band membership.  The literal
product, both subtractions and final comparison have charged bit work. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem affineErrorWithWork_value (position offset velocity prediction tolerance : BinaryFraction) :
    (affineErrorWithWork position offset velocity prediction tolerance).1 = true ↔
      |position.value - offset.value - velocity.value * prediction.value| ≤ tolerance.value := by
  simp only [affineErrorWithWork, leWithWork_value, absolute_value,
    subWithWork_value, canonicalMulWithWork_value]

def affineGuardBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 1 + 2000 * (B + 1) ^ 2 +
    (6000 * (12 * B + 9) ^ 2 + 1) +
    (1000 * (96 * B + 71) ^ 2 + 1) + 4

/-- Threshold used in every internal-cut predicate. -/


@[simp] theorem bandToleranceWithWork_value (tau theta : BinaryFraction) (b M : ℕ) :
    (bandToleranceWithWork tau theta b M).1.value = tau.value * theta.value * b / M := by
  simp only [bandToleranceWithWork, divWithWork_value, canonicalMulWithWork_value, nat_value]

def bandToleranceBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 2 * B + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Materialized Boolean vertices retain their band labels. The resulting
selected action, including every tie, is the action used by the online
sampler in the accuracy development. -/

namespace EditApproximation
namespace BinaryFraction

def labeledBandVerticesWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : List ((Fin M → σ) × Vector BinaryFraction d) × ℕ :=
  let total := bandMassTotalWithWork mass
  let vertices := band.map fun action =>
    let vertex := vectorMapWithWork d fun i =>
      bandCoordinateWithWork mass total.1 action (coordinates.get i)
    ((action, vertex.1), vertex.2)
  (vertices.map Prod.fst, total.2 + (vertices.map Prod.snd).sum + 8 * band.length)

def preparedBandActionWithWork {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G j t : ℕ) :
    Option (Fin M → σ) × ℕ :=
  let coordinates := listedBandCoordinateVector band
  let vertices := labeledBandVerticesWithWork coordinates mass band
  let linear := vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)
  let selected := selectionWithWork vertices.1 linear.1 G j
  (selected.1, vertices.2 + linear.2 + selected.2 + 2)

def preparedBandActionBitBudget (M d vertices G K t Be Bk Bm Bt E : ℕ) : ℕ :=
  bandPreparationBitBudget M d vertices Bm + 2 * vertices +
    d * (onlineLinearBitBudget Be Bk Bm Bt t + 6) +
    selectionBitBudget d vertices G K (bandVertexWordBudget M Bm) (bandVertexWordBudget M Bm)
      (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1)) + 2

def bandActionWithWork {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny)) (G j t : ℕ) :
    Option (Fin M → TargetInterval ny) × ℕ :=
  let mass := envelopeVectorWithWork b band initial
  let selected := preparedBandActionWithWork mass.1 table eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

def bandActionBitBudget (M d b vertices G K t Be Bk Bi Bt E : ℕ) : ℕ :=
  M * (bandEnvelopeBitBudget b M vertices Bi + 6) +
    preparedBandActionBitBudget M d vertices G K t Be Bk
      (3 * bandEnvelopeWordBudget b M Bi + 1) Bt E + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDivisionWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.denominatorInteger_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary long division. A high-prefix quotient and remainder are extended
by one source bit, then compared with the positive divisor and reduced by
at most one ripple-borrow subtraction. -/

namespace EditApproximation



theorem bitDivModWithWork_value (divisor bits : List Bool) (hd : 0 < bitWordValue divisor) :
    bitWordValue bits = bitWordValue divisor * bitWordValue (bitDivModWithWork divisor bits).1 +
      bitWordValue (bitDivModWithWork divisor bits).2.1 ∧
      bitWordValue (bitDivModWithWork divisor bits).2.1 < bitWordValue divisor := by
  induction bits with
  | nil => simp [bitDivModWithWork, bitWordValue, hd]
  | cons bit bits ih =>
    let previous := bitDivModWithWork divisor bits
    let candidate := bit :: previous.2.1
    have hp : bitWordValue bits = bitWordValue divisor * bitWordValue previous.1 +
        bitWordValue previous.2.1 := ih.1
    have hr : bitWordValue previous.2.1 < bitWordValue divisor := ih.2
    have hc : bitWordValue candidate < 2 * bitWordValue divisor := by
      dsimp only [candidate, bitWordValue]
      cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    by_cases hlt : (bitCompareWithWork candidate divisor).1 = .lt
    · have hv := (bitCompareWithWork_lt candidate divisor).1 hlt
      simp only [bitDivModWithWork, show (bitCompareWithWork (bit :: (bitDivModWithWork divisor bits).2.1)
        divisor).1 = .lt from hlt, ↓reduceIte]
      change bitWordValue (bit :: bits) = bitWordValue divisor *
        bitWordValue (false :: previous.1) + bitWordValue candidate ∧ bitWordValue candidate < _
      constructor
      · simp only [bitWordValue, Bool.toNat_false]
        dsimp only [candidate, bitWordValue]
        nlinarith only [hp]
      · exact hv
    · have hv : bitWordValue divisor ≤ bitWordValue candidate := by
        exact Nat.le_of_not_gt (fun h => hlt ((bitCompareWithWork_lt candidate divisor).2 h))
      have hs := bitSubtractWithWork_sub candidate divisor hv
      simp only [bitDivModWithWork, show (bitCompareWithWork (bit :: (bitDivModWithWork divisor bits).2.1)
        divisor).1 ≠ .lt from hlt, ↓reduceIte]
      change bitWordValue (bit :: bits) = bitWordValue divisor * bitWordValue (true :: previous.1) +
        bitWordValue (bitSubtractWithWork candidate divisor false).1 ∧
        bitWordValue (bitSubtractWithWork candidate divisor false).1 < _
      rw [hs]
      constructor
      · simp only [bitWordValue, Bool.toNat_true]
        have he := Nat.sub_add_cancel hv
        dsimp only [candidate, bitWordValue] at he ⊢
        nlinarith only [hp, he]
      · omega



theorem binaryNaturalDivModWithWork_spec (n d : ℕ) (hd : 0 < d) :
    bitWordValue (binaryNaturalDivModWithWork n d).1 = n / d ∧
      bitWordValue (binaryNaturalDivModWithWork n d).2.1 = n % d := by
  have h := bitDivModWithWork_value d.bits n.bits (by simpa only [bitWordValue_bits] using hd)
  simp only [bitWordValue_bits] at h
  have hmod : n % d = bitWordValue (bitDivModWithWork d.bits n.bits).2.1 := by
    conv_lhs => rw [h.1]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt h.2]
  have hdiv : n / d = bitWordValue (bitDivModWithWork d.bits n.bits).1 := by
    conv_lhs => rw [h.1]
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h.2, Nat.add_zero]
  exact ⟨hdiv.symm, hmod.symm⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCeilingWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact natural ceilings from the executed binary quotient and remainder.
Negative fractions have natural ceiling zero, as in the seed update. -/

namespace EditApproximation



theorem bitCeilDivWithWork_value (divisor bits : List Bool) (hd : 0 < bitWordValue divisor) :
    bitWordValue (bitCeilDivWithWork divisor bits).1 =
      ⌈((bitWordValue bits : ℚ) / bitWordValue divisor)⌉₊ := by
  let q := bitWordValue (bitDivModWithWork divisor bits).1
  let r := bitWordValue (bitDivModWithWork divisor bits).2.1
  have h := bitDivModWithWork_value divisor bits hd
  have heq : bitWordValue bits = bitWordValue divisor * q + r := h.1
  have hr : r < bitWordValue divisor := h.2
  have hdQ : (0 : ℚ) < bitWordValue divisor := by exact_mod_cast hd
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs with hz
  · have hr0 : r = 0 := by
      exact (bitCompareWithWork_eq (bitDivModWithWork divisor bits).2.1 []).1 hz
    have hratio : (bitWordValue bits : ℚ) / bitWordValue divisor = (q : ℚ) := by
      apply (div_eq_iff hdQ.ne').mpr
      exact_mod_cast (show bitWordValue bits = q * bitWordValue divisor by nlinarith only [heq, hr0])
    rw [hratio]
    exact (Nat.ceil_natCast q).symm
  · have hr0 : r ≠ 0 := by
      intro hzero
      exact hz ((bitCompareWithWork_eq (bitDivModWithWork divisor bits).2.1 []).2 hzero)
    rw [bitAddWithWork_value]
    change q + 1 + 0 = _
    simp only [Nat.add_zero]
    symm
    apply (Nat.ceil_eq_iff (by omega : q + 1 ≠ 0)).mpr
    constructor
    · simp only [Nat.add_sub_cancel]
      rw [lt_div_iff₀ hdQ]
      exact_mod_cast (show q * bitWordValue divisor < bitWordValue bits by
        nlinarith only [heq, Nat.pos_of_ne_zero hr0])
    · rw [div_le_iff₀ hdQ]
      push_cast
      exact_mod_cast (show bitWordValue bits ≤ (q + 1) * bitWordValue divisor by nlinarith only [heq, hr])

namespace BinaryFraction



theorem naturalCeilingWithWork_value (a : BinaryFraction) :
    bitWordValue (a.naturalCeilingWithWork).1 = ⌈a.value⌉₊ := by
  cases hs : a.numerator.negative
  · simpa only [naturalCeilingWithWork, hs, Bool.false_eq_true, ↓reduceIte,
      value, SignedBinary.value, signedMagnitude, Int.cast_natCast] using
      bitCeilDivWithWork_value a.denominator a.numerator.bits a.denominator_pos
  · have hn : a.value ≤ 0 := by
      simp only [value, SignedBinary.value, signedMagnitude, hs, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    simp only [naturalCeilingWithWork, hs, ↓reduceIte, bitWordValue]
    exact (Nat.ceil_eq_zero.mpr hn).symm

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Endpoint rounding executed by binary division followed by multiplication. -/

namespace EditApproximation



theorem binaryGridRoundWithWork_value (spacing position : ℕ) (hspacing : 0 < spacing) :
    bitWordValue (binaryGridRoundWithWork spacing position).1 = gridRound spacing position := by
  simp only [binaryGridRoundWithWork, bitMulWithWork_value, bitWordValue_bits,
    (binaryNaturalDivModWithWork_spec position spacing hspacing).1, gridRound]



theorem binaryIntervalRoundWithWork_value {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : TargetInterval n) :
    (bitWordValue (binaryIntervalRoundWithWork spacing q.lo q.hi).1.1,
      bitWordValue (binaryIntervalRoundWithWork spacing q.lo q.hi).1.2) =
      ((roundInterval spacing q).lo, (roundInterval spacing q).hi) := by
  simp only [binaryIntervalRoundWithWork, binaryGridRoundWithWork_value _ _ hspacing,
    roundInterval]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPrefixWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal stored-fraction evaluation of the finite prefix predictor.
Every prefix minimum scans the finite action array and uses exact
Boolean comparisons. No rational operation is assigned unit cost. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def prefixWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    BinaryFraction × ℕ :=
  let finish := canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
  let connection := connectionWithWork (nat r.lo) finish.1 ((List.ofFn states).take j)
  let total := sumListWithWork (List.ofFn fun i : Fin M =>
    if i.val < j then child i (states i) else zero)
  let result := canonicalAddWithWork connection.1 total.1
  (result.1, finish.2 + connection.2 + total.2 + result.2 +
    Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + Nat.size r.lo + 6 * M + 5)

@[simp] theorem prefixWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    (prefixWithWork parent r states child j p).1.value =
      rationalWidePrefixCost parent r states (fun i q => (child i q).value) j p.value := by
  simp only [prefixWithWork, canonicalAddWithWork_value, connectionWithWork_value,
    nat_value, sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalWidePrefixCost]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hi : i.val < j <;> simp [hi, zero, value, SignedBinary.value, signedMagnitude, bitWordValue]

def prefixConnectionWord (M j B : ℕ) : ℕ := connectionWordBudget (min j M) (8 * B + 6)

def prefixWordBudget (M j B : ℕ) : ℕ :=
  8 * (prefixConnectionWord M j B + bandMassTotalStorageBudget M B) + 6

def prefixBitBudget (M j B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + connectionBitBudget (min j M) (8 * B + 6) +
    storedSumBitBudget M B + 6 * M +
    6000 * (prefixConnectionWord M j B + bandMassTotalStorageBudget M B + 1) ^ 2 +
    2 * B + 6 * M + 5

def prefixMinimumWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    BinaryFraction × ℕ :=
  let fallback := prefixWithWork parent r (actions.head hne) child j p
  let scores := arithmeticMapWithWork (fun action => prefixWithWork parent r action child j p) actions
  let result := minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 1)

@[simp] theorem prefixMinimumWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    (prefixMinimumWithWork parent r actions hne child j p).1.value =
      rationalWidePrefixMinimum parent r actions hne (fun i q => (child i q).value) j p.value := by
  simp only [prefixMinimumWithWork, minimumWithWork_value, arithmeticMapWithWork_value,
    List.map_map, Function.comp_def, prefixWithWork_value, rationalWidePrefixMinimum]

def prefixMinimumBitBudget (M j v B : ℕ) : ℕ :=
  prefixBitBudget M j B + v * (prefixBitBudget M j B + 3) +
    (1 + v * (1000 * (prefixWordBudget M j B + 1) ^ 2 + 2)) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact finite band predicates evaluated on stored Boolean fractions.
The cut tests use the actual finite prefix minimum; the other tests are
Boolean comparisons of the actual interval endpoints. -/

namespace EditApproximation

open Finset



@[simp] theorem naturalEqualWithWork_value (a b : ℕ) :
    (naturalEqualWithWork a b).1 = true ↔ a = b := by
  simp only [naturalEqualWithWork, decide_eq_true_eq, binaryNaturalCompareWithWork_eq]

theorem naturalEqualWithWork_cost (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    (naturalEqualWithWork a b).2 ≤ 8 * B + 2 := by
  have h := binaryNaturalCompareWithWork_cost a b
  change (binaryNaturalCompareWithWork a b).2 + 1 ≤ _
  omega



@[simp] theorem zeroConnectionWithWork_value {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) :
    (zeroConnectionWithWork start states finish).1 = true ↔
      connectionBudget start states finish = 0 := by
  induction states generalizing start with
  | nil =>
    change (naturalEqualWithWork start finish).1 = true ↔ Nat.dist start finish = 0
    exact (naturalEqualWithWork_value start finish).trans
      ⟨Nat.dist_eq_zero, Nat.eq_of_dist_eq_zero⟩
  | cons state rest ih =>
    change ((naturalEqualWithWork start state.lo).1 &&
      (zeroConnectionWithWork state.hi rest finish).1) = true ↔
        Nat.dist start state.lo + connectionBudget state.hi rest finish = 0
    rw [Bool.and_eq_true, naturalEqualWithWork_value, ih, Nat.add_eq_zero_iff]
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨Nat.dist_eq_zero hs, ht⟩
    · rintro ⟨hs, ht⟩
      exact ⟨Nat.eq_of_dist_eq_zero hs, ht⟩

/-- Construct a translated endpoint by the actual binary subtract/add routines. -/


@[simp] theorem translatedEndpointWithWork_value (reference root endpoint : ℕ) (h : root ≤ endpoint) :
    (translatedEndpointWithWork reference root endpoint).1 = reference + (endpoint - root) := by
  simp only [translatedEndpointWithWork, binaryNaturalAddWithWork_value,
    binaryNaturalSubtractWithWork_value endpoint root h]

namespace BinaryFraction

theorem nat_dist_cast (a b : ℕ) : (Nat.dist a b : ℚ) = |(a : ℚ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]



@[simp] theorem naturalDistanceLeWithWork_value (a b radius : ℕ) :
    (naturalDistanceLeWithWork a b radius).1 = true ↔ Nat.dist a b ≤ radius := by
  simp only [naturalDistanceLeWithWork, leWithWork_value, distanceWithWork_value, nat_value]
  rw [← nat_dist_cast]
  constructor <;> intro h <;> exact_mod_cast h

def naturalDistanceBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3

def cutGuardWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) : Bool × ℕ :=
  if j.val = 0 then (true, 1) else
    let shift := subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)
    let offset := subWithWork (nat r.lo) (nat parent.lo)
    let prediction := prefixMinimumWithWork parent r actions hne child j.val shift.1
    let result := affineErrorWithWork shift.1 offset.1 velocity prediction.1 tolerance
    (result.1, shift.2 + offset.2 + prediction.2 + result.2 +
      Nat.size (states j).lo + Nat.size (sourceChild parent j).lo + Nat.size r.lo + Nat.size parent.lo + 5)

@[simp] theorem cutGuardWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) :
    (cutGuardWithWork parent r actions hne child states velocity tolerance j).1 = true ↔
      (0 < j.val → |bandCutShift parent states j - ((r.lo : ℚ) - parent.lo) - velocity.value *
        rationalWidePrefixMinimum parent r actions hne (fun i q => (child i q).value)
          j.val (bandCutShift parent states j)| ≤ tolerance.value) := by
  by_cases hj : j.val = 0
  · simp [cutGuardWithWork, hj]
  · rw [cutGuardWithWork, ite_eq_right hj]
    dsimp only
    rw [affineErrorWithWork_value]
    simp only [subWithWork_value, nat_value, prefixMinimumWithWork_value, bandCutShift]
    constructor
    · intro h _
      exact h
    · intro h
      exact h (Nat.pos_of_ne_zero hj)

def cutGuardWordBudget (M j B : ℕ) : ℕ :=
  prefixWordBudget M j (8 * B + 6) + 76 * B + 50

def cutGuardBitBudget (M j v B : ℕ) : ℕ :=
  2 * (6000 * (B + 1) ^ 2 + 1) +
    prefixMinimumBitBudget M j v (8 * B + 6) +
    affineGuardBitBudget (cutGuardWordBudget M j B) + 4 * B + 6

def bandPredicateWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny) : Bool × ℕ :=
  let connection := zeroConnectionWithWork r.lo (List.ofFn states) r.hi
  let anchors := allWithWork (fun i : Fin M =>
    let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
    let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
    let radius := binaryNaturalMulWithWork 6 b
    let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
    let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
    (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3)) (List.finRange M)
  let tolerance := bandToleranceWithWork tau theta b M
  let cuts := allWithWork (cutGuardWithWork parent r actions hne child states velocity tolerance.1)
    (List.finRange M)
  (connection.1 && anchors.1 && cuts.1, connection.2 + anchors.2 + tolerance.2 + cuts.2 + 4)

@[simp] theorem bandPredicateWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny) :
    (bandPredicateWithWork parent r b tau theta velocity actions hne child states).1 = true ↔
      bandActionPredicate parent r b tau.value theta.value velocity.value actions hne
        (fun i q => (child i q).value) states := by
  have hlo (i : Fin M) : parent.lo ≤ (sourceChild parent i).lo := Nat.le_add_right _ _
  have hhi (i : Fin M) : parent.lo ≤ (sourceChild parent i).hi := Nat.le_add_right _ _
  simp only [bandPredicateWithWork, Bool.and_eq_true, zeroConnectionWithWork_value,
    allWithWork_value, naturalDistanceLeWithWork_value, cutGuardWithWork_value,
    translatedEndpointWithWork_value _ _ _ (hlo _), translatedEndpointWithWork_value _ _ _ (hhi _),
    binaryNaturalMulWithWork_value, bandToleranceWithWork_value, List.mem_finRange, forall_true_left,
    endpointActionConnection, bandActionPredicate]
  exact and_assoc

def anchorGuardBitBudget (B : ℕ) : ℕ :=
  2 * (36 * B + 4) + 80 * (B + 4) + 2 * naturalDistanceBitBudget B + 3

def bandPredicateBitBudget (M B C : ℕ) : ℕ :=
  (M + 1) * (8 * B + 3) + M * (anchorGuardBitBudget B + 3) +
    bandToleranceBitBudget B + M * (C + 3) + 4

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRationalWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



def rationalPhysicalBellman {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℚ) (state : PhysicalEntry M J target.length) : ℚ :=
  let parent := physicalSourceInterval source.length state.1
  if hbelow : state.1.1.val < J then
    if parent.hi - parent.lo ≤ 1 then initial state else
      rationalBellman (fun q => initial (state.1, q))
        (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent (representatives state.1) P)
        (fun is => value (physicalChild state.1 hbelow is.1, is.2)) state.2
  else initial state

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalWideStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One literal refinement update with finite selected-group cones and online action values. -/

namespace EditApproximation

open Finset

def rationalWideStepCone {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q : TargetInterval ny) : ℚ :=
  rationalMinimum (rationalBellman initial (fun q r => targetEndpointDistance q r) L
    (rationalActualWideActions parent representatives P) old q)
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q))

def rationalWideStep {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups online : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q : TargetInterval ny) : ℚ :=
  rationalRefinementUpdate delta (rationalWideStepCone parent representatives P initial L old current groups q)
    (rationalOnlineMinimum (online.map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBellmanKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Stored-fraction execution of the Bellman and refinement continuations.
The action lists and child entries have already been gathered; the routines
below perform every numerical operation returning the next table value. -/

namespace EditApproximation



def BinaryBellmanAction.decode {Parent Child : Type*} {M : ℕ}
    (action : BinaryBellmanAction Parent Child M) : RationalBellmanAction Parent Child M :=
  ⟨action.center, action.connection.value, action.childState⟩

namespace BinaryFraction

open Finset

def bellmanActionWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (action : BinaryBellmanAction Parent Child M) :
    BinaryFraction × ℕ :=
  let dist := distance query action.center
  let spatial := canonicalMulWithWork L dist.1
  let connection := canonicalAddWithWork spatial.1 action.connection
  let children := sumListWithWork (List.ofFn fun i => child (action.childState i))
  let result := canonicalAddWithWork connection.1 children.1
  (result.1, dist.2 + spatial.2 + connection.2 + children.2 + result.2 + 3)

@[simp] theorem bellmanActionWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (action : BinaryBellmanAction Parent Child M) :
    (bellmanActionWithWork distance L child query action).1.value =
      rationalActionValue (fun q r => (distance q r).1.value) L.value
        (fun s => (child s).value) query action.decode := by
  simp only [bellmanActionWithWork, canonicalAddWithWork_value, canonicalMulWithWork_value,
    sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalActionValue, BinaryBellmanAction.decode, Function.comp_def]

def bellmanActionWordBudget (M B : ℕ) : ℕ :=
  8 * (40 * B + 22 + bandMassTotalStorageBudget M B) + 6

def bellmanActionBitBudget (M B C : ℕ) : ℕ :=
  C + 2000 * (B + 1) ^ 2 + 6000 * (5 * B + 3) ^ 2 + storedSumBitBudget M B + 6 * M +
    6000 * (40 * B + 22 + bandMassTotalStorageBudget M B + 1) ^ 2 + 3

def bellmanWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M)) :
    BinaryFraction × ℕ :=
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L child query) actions
  let result := minimumWithWork fallback scores.1
  (result.1, scores.2 + result.2 + 1)

@[simp] theorem bellmanWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent) (actions : List (BinaryBellmanAction Parent Child M)) :
    (bellmanWithWork distance L fallback child query actions).1.value =
      rationalBellman (fun _ => fallback.value) (fun q r => (distance q r).1.value) L.value
        (actions.map BinaryBellmanAction.decode) (fun s => (child s).value) query := by
  simp only [bellmanWithWork, minimumWithWork_value, arithmeticMapWithWork_value, List.map_map,
    Function.comp_def, bellmanActionWithWork_value, rationalBellman]

def bellmanBitBudget (M n B F C : ℕ) : ℕ :=
  n * (bellmanActionBitBudget M B C + 3) +
    (1 + n * (1000 * (F + bellmanActionWordBudget M B + 1) ^ 2 + 2)) + 1



@[simp] theorem onlineMinimumWithWork_value (values : List BinaryFraction) :
    ((onlineMinimumWithWork values).1.map value) = rationalOnlineMinimum (values.map value) := by
  cases values with
  | nil => rfl
  | cons first rest => simp only [onlineMinimumWithWork, Option.map_some, minimumWithWork_value,
      rationalOnlineMinimum, List.map_cons]



@[simp] theorem refinementUpdateWithWork_value (delta cone : BinaryFraction) (online : Option BinaryFraction) :
    (refinementUpdateWithWork delta cone online).1.value =
      rationalRefinementUpdate delta.value cone.value (online.map value) := by
  cases online with
  | none => rfl
  | some online =>
    simp only [refinementUpdateWithWork, minWithWork_value, maxWithWork_value,
      divWithWork_value, canonicalAddWithWork_value, one, nat_value,
      Nat.cast_one, Option.map_some, rationalRefinementUpdate]

def refinementUpdateWordBudget (B : ℕ) : ℕ := 32 * B + 28

def refinementUpdateBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 2100 * (8 * B + 8) ^ 2 +
    2 * (1000 * (32 * B + 29) ^ 2 + 1) + 2

/-- Numerical tail of the actual local refinement query, after its finite
wide, group and online lists have been prepared from gathered data. -/
def localContinuationWithWork {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) : BinaryFraction × ℕ :=
  let warm := bellmanWithWork distance L fallback old query wide
  let cone := bellmanWithWork distance L warm.1 current query groups
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L current query) online
  let onlineMin := onlineMinimumWithWork scores.1
  let result := refinementUpdateWithWork delta cone.1 onlineMin.1
  (result.1, warm.2 + cone.2 + scores.2 + onlineMin.2 + result.2 + 3)

@[simp] theorem localContinuationWithWork_value {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) :
    (localContinuationWithWork distance L delta fallback old current query wide groups online).1.value =
      rationalRefinementUpdate delta.value
        (rationalMinimum
          (rationalBellman (fun _ => fallback.value) (fun q r => (distance q r).1.value) L.value
            (wide.map BinaryBellmanAction.decode) (fun s => (old s).value) query)
          ((groups.map BinaryBellmanAction.decode).map
            (rationalActionValue (fun q r => (distance q r).1.value) L.value (fun s => (current s).value) query)))
        (rationalOnlineMinimum ((online.map BinaryBellmanAction.decode).map
          (rationalActionValue (fun q r => (distance q r).1.value) L.value (fun s => (current s).value) query))) := by
  simp only [localContinuationWithWork, refinementUpdateWithWork_value, bellmanWithWork_value,
    onlineMinimumWithWork_value, arithmeticMapWithWork_value, List.map_map, Function.comp_def,
    bellmanActionWithWork_value, rationalBellman]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal group estimates on gathered stored fractions. Each child/scale
comparison is executed, the supplied draw indices are reused, and ordered
selection uses the same tie rule as the mathematical group program. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



@[simp] theorem equalWithWork_value (a b : BinaryFraction) :
    (equalWithWork a b).1 = true ↔ a.value = b.value := by
  simp only [equalWithWork, Bool.and_eq_true, leWithWork_value]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩



@[simp] theorem groupTermsWithWork_value {M : ℕ} (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    ((groupTermsWithWork h envelope values indices).1.map value) =
      indices.map (fun i => if (envelope.get i).value = h.value then (values.get i).value else 0) := by
  simp only [groupTermsWithWork, arithmeticMapWithWork_value, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  by_cases hi : (envelope.get i).value = h.value
  · have ht := (equalWithWork_value (envelope.get i) h).mpr hi
    simp only [ht, ↓reduceIte, hi]
  · have ht : (equalWithWork (envelope.get i) h).1 = false :=
      Bool.eq_false_iff.mpr (fun h => hi ((equalWithWork_value _ _).mp h))
    simp only [ht, Bool.false_eq_true, ↓reduceIte, hi]
    rw [← representation_value, zero_representation, UnreducedRational.value_zero]



@[simp] theorem groupIndexWithWork_value {M : ℕ} (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    (groupIndexWithWork h envelope values indices).1.value =
      (indices.map fun i => if (envelope.get i).value = h.value then (values.get i).value else 0).sum := by
  simp only [groupIndexWithWork, sumListWithWork_value, groupTermsWithWork_value]

def groupIndexBitBudget (n B : ℕ) : ℕ :=
  n * (2 * (1000 * (B + 1) ^ 2 + 1) + 6) + storedSumBitBudget n B + 6 * n + 1

def groupScaleWithWork {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) : BinaryFraction × ℕ :=
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  let subtotal := groupIndexWithWork h envelope values indices
  let factor := if k = M then (one, 1) else divWithWork (nat M) (nat k)
  let result := canonicalMulWithWork factor.1 subtotal.1
  (result.1, subtotal.2 + factor.2 + result.2 + Nat.size M + Nat.size k + 3)

@[simp] theorem groupScaleWithWork_value {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    (groupScaleWithWork k h envelope values draw).1.value =
      groupScaleEstimate k h.value (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  unfold groupScaleWithWork groupScaleEstimate
  split_ifs with heq
  · simp only [canonicalMulWithWork_value, groupIndexWithWork_value, one, nat_value, Nat.cast_one, one_mul]
    simp only [groupScaleTrueCost, ← List.ofFn_eq_map, List.sum_ofFn]
  · simp only [canonicalMulWithWork_value, groupIndexWithWork_value, divWithWork_value, nat_value,
      List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.sum_ofFn]

def groupScaleTermCount (M k : ℕ) : ℕ := if k = M then M else k

def groupScaleWordBudget (M k B : ℕ) : ℕ :=
  4 * (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B) + 2

def groupScaleBitBudget (M k B : ℕ) : ℕ :=
  groupIndexBitBudget (groupScaleTermCount M k) B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B + 1) ^ 2 + 2 * B + 3

/-- Every scale is accumulated using the same finite child arrays. -/
def groupMemberWithWork {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) : BinaryFraction × ℕ :=
  let terms := arithmeticMapWithWork (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)
  let subtotal := sumListWithWork terms.1
  let result := canonicalAddWithWork connection subtotal.1
  (result.1, terms.2 + subtotal.2 + result.2 + 1)

@[simp] theorem groupMemberWithWork_value {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) :
    (groupMemberWithWork scales count connection envelope values draw).1.value =
      groupMemberEstimate (fun s => (scales s).value) count connection.value
        (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  simp only [groupMemberWithWork, canonicalAddWithWork_value, sumListWithWork_value,
    arithmeticMapWithWork_value, List.map_map, Function.comp_def, groupScaleWithWork_value,
    groupMemberEstimate]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

def groupMemberWordBudget (T B W : ℕ) : ℕ :=
  8 * (B + bandMassTotalStorageBudget T W) + 6

def groupMemberBitBudget (T B C W : ℕ) : ℕ :=
  T * (C + 3) + storedSumBitBudget T W + 6 * T +
    6000 * (B + bandMassTotalStorageBudget T W + 1) ^ 2 + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMedianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary multiplication, natural ceiling, sorting and clamping for the
literal seed median. The stored words are sorted without decoding them. -/

namespace EditApproximation

/-- Comparison of two stored nonnegative binary words. -/


@[simp] theorem wordLEWithWork_value (a b : List Bool) :
    (wordLEWithWork a b).1 = true ↔ bitWordValue a ≤ bitWordValue b := by
  simp only [wordLEWithWork, Bool.not_eq_true', decide_eq_false_iff_not,
    bitCompareWithWork_lt, not_lt]



@[simp] theorem wordMinWithWork_value (a b : List Bool) :
    bitWordValue (wordMinWithWork a b).1 = min (bitWordValue a) (bitWordValue b) := by
  unfold wordMinWithWork
  dsimp only
  split_ifs with h
  · exact (min_eq_left ((wordLEWithWork_value a b).mp h)).symm
  · exact (min_eq_right (le_of_not_ge (fun hle => h ((wordLEWithWork_value a b).mpr hle)))).symm



@[simp] theorem wordInsertWithWork_value (a : List Bool) (words : List (List Bool)) :
    ((wordInsertWithWork a words).1.map bitWordValue) =
      List.orderedInsert (· ≤ ·) (bitWordValue a) (words.map bitWordValue) := by
  induction words with
  | nil => rfl
  | cons b rest ih =>
    unfold wordInsertWithWork
    dsimp only
    by_cases h : (wordLEWithWork a b).1 = true
    · have hle := (wordLEWithWork_value a b).mp h
      simp only [h, ↓reduceIte, List.map_cons, List.orderedInsert, hle]
    · have hle : ¬ bitWordValue a ≤ bitWordValue b := fun hle => h ((wordLEWithWork_value a b).mpr hle)
      simp only [h, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.orderedInsert, hle, ih]



@[simp] theorem wordSortWithWork_value (words : List (List Bool)) :
    ((wordSortWithWork words).1.map bitWordValue) =
      List.insertionSort (· ≤ ·) (words.map bitWordValue) := by
  induction words with
  | nil => rfl
  | cons a rest ih =>
    simp only [wordSortWithWork, wordInsertWithWork_value, ih,
      List.map_cons, List.insertionSort_cons]

namespace BinaryFraction



@[simp] theorem scaledCeilingWithWork_value (multiplier : ℕ) (a : BinaryFraction) :
    bitWordValue (scaledCeilingWithWork multiplier a).1 = ⌈(multiplier : ℚ) * a.value⌉₊ := by
  simp only [scaledCeilingWithWork, naturalCeilingWithWork_value,
    canonicalMulWithWork_value, nat_value]

def scaledCeilingBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 500 * (4 * B + 3) ^ 2 + B + 3

/-- The exact clamped upper median on binary words, including every copy's
multiplication and ceiling, all sorting comparisons and the middle read. -/


@[simp] theorem medianSeedWithWork_value (N multiplier : ℕ) (values : List BinaryFraction) :
    bitWordValue (medianSeedWithWork N multiplier values).1 =
      min N (upperMedian (values.map fun a => ⌈(multiplier : ℚ) * a.value⌉₊)) := by
  unfold medianSeedWithWork
  rw [wordMinWithWork_value, bitWordValue_bits]
  congr 1
  rw [upperMedian, List.length_map, List.mergeSort_eq_insertionSort]
  have hs := wordSortWithWork_value
    (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  rw [arithmeticMapWithWork_value, List.map_map] at hs
  simp only [Function.comp_def, scaledCeilingWithWork_value] at hs
  have hm := congrArg (fun words : List ℕ => words.getD (values.length / 2) 0) hs
  change ((wordSortWithWork (values.map (fun a => (scaledCeilingWithWork multiplier a).1))).1.map
    bitWordValue).getD (values.length / 2) (bitWordValue []) = _ at hm
  rw [List.getD_map] at hm
  simpa only [arithmeticMapWithWork_value] using hm

def medianSeedBitBudget (n B : ℕ) : ℕ :=
  n * (scaledCeilingBitBudget B + 3) + (n + 1) ^ 2 * (8 * (4 * B + 4) + 6) +
    n + 4 * (B + (4 * B + 4)) + 3 + B + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeKernel
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite representative-band construction on stored binary fractions:
connection and child sums, the exact wide minimum, velocity, and every
literal band predicate. The Cartesian product materializes the wide-action enumeration. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem nat_distance_value (a b : ℕ) : (Nat.dist a b : ℚ) = |(a : ℚ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

theorem rationalConnectionBudget_nat {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) :
    rationalConnectionBudget start states finish = (connectionBudget start states finish : ℚ) := by
  induction states generalizing start with
  | nil => simp only [rationalConnectionBudget, connectionBudget, nat_distance_value]
  | cons state rest ih =>
    simp only [rationalConnectionBudget, connectionBudget, Nat.cast_add, ih, nat_distance_value]



@[simp] theorem endpointDistanceWithWork_value {n : ℕ} (q r : TargetInterval n) :
    (endpointDistanceWithWork q r).1.value = (targetEndpointDistance q r : ℚ) := by
  simp only [endpointDistanceWithWork, canonicalAddWithWork_value, distanceWithWork_value,
    nat_value, targetEndpointDistance, Nat.cast_add, nat_distance_value]



@[simp] theorem endpointConnectionWithWork_value {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) :
    (endpointConnectionWithWork r states).1.value = (endpointActionConnection r states : ℚ) := by
  simp only [endpointConnectionWithWork, connectionWithWork_value, nat_value,
    rationalConnectionBudget_nat, endpointActionConnection]

def endpointScoreWithWork {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n) :
    BinaryFraction × ℕ :=
  let connection := endpointConnectionWithWork r states
  let children := sumListWithWork (List.ofFn fun i => child i (states i))
  let result := canonicalAddWithWork connection.1 children.1
  (result.1, connection.2 + children.2 + result.2 + 2)

@[simp] theorem endpointScoreWithWork_value {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction) (states : Fin M → TargetInterval n) :
    (endpointScoreWithWork r child states).1.value =
      rationalEndpointActionValue r states (fun i s => (child i s).value) := by
  simp only [endpointScoreWithWork, canonicalAddWithWork_value, endpointConnectionWithWork_value,
    sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalEndpointActionValue, Function.comp_def]

def wideMinimumWithWork {n M : ℕ} (r : TargetInterval n)
    (child : Fin M → TargetInterval n → BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) : BinaryFraction × ℕ :=
  let fallback := endpointScoreWithWork r child (actions.head hne)
  let scores := arithmeticMapWithWork (endpointScoreWithWork r child) actions
  let result := minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 2)

@[simp] theorem wideMinimumWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (child : Fin M → TargetInterval ny → BinaryFraction)
    (hne : wideActionList M parent r b P ≠ []) :
    (wideMinimumWithWork r child (wideActionList M parent r b P) hne).1.value =
      rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value) := by
  simp only [wideMinimumWithWork, minimumWithWork_value, arithmeticMapWithWork_value,
    List.map_map, Function.comp_def, endpointScoreWithWork_value, rationalWideActionMinimum]



@[simp] theorem stateGapWithWork_value {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) :
    (stateGapWithWork sourceLength r).1.value = (r.hi : ℚ) - r.lo - sourceLength := by
  simp only [stateGapWithWork, subWithWork_value, nat_value]

/-- Every filter callback is the literal binary band predicate. -/
def bandFromActionsWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) :
    List (Fin M → TargetInterval ny) × ℕ :=
  let margin := subWithWork one tau
  let guard := leWithWork velocity.absolute margin.1
  if guard.1 then
    let filtered := filterWithWork
      (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions
    (filtered.1, margin.2 + guard.2 + filtered.2 + 2)
  else ([], margin.2 + guard.2 + 1)

@[simp] theorem bandFromActionsWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) :
    (bandFromActionsWithWork parent r b tau theta velocity child actions hne).1 =
      if |velocity.value| ≤ 1 - tau.value then
        actions.filter (fun states => decide (bandActionPredicate parent r b tau.value theta.value
          velocity.value actions hne (fun i s => (child i s).value) states)) else [] := by
  have hguard : (leWithWork velocity.absolute (subWithWork one tau).1).1 = true ↔
      |velocity.value| ≤ 1 - tau.value := by
    simp only [leWithWork_value, absolute_value, subWithWork_value, one, nat_value, Nat.cast_one]
  unfold bandFromActionsWithWork
  dsimp only
  by_cases h : |velocity.value| ≤ 1 - tau.value
  · rw [ite_eq_left (hguard.mpr h), ite_eq_left h, filterWithWork_value]
    apply List.filter_congr
    intro states _
    apply Bool.eq_iff_iff.mpr
    exact (bandPredicateWithWork_value parent r b tau theta velocity actions hne child states).trans
      decide_eq_true_iff.symm
  · rw [ite_eq_right (fun hg => h (hguard.mp hg)), ite_eq_right h]

/-- The actions have been materialized once and are reused for the wide
minimum and all prefix queries. -/
def representativeFromActionsWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) : List (Fin M → TargetInterval ny) × ℕ :=
  if hne : actions = [] then ([], 1) else
    let Z := wideMinimumWithWork r child actions hne
    let positive := ltWithWork zero Z.1
    if positive.1 then
      let gap := stateGapWithWork sourceLength r
      let velocity := divWithWork gap.1 Z.1
      let result := bandFromActionsWithWork parent r b tau theta velocity.1 child actions hne
      (result.1, Z.2 + positive.2 + gap.2 + velocity.2 + result.2 + 3)
    else ([], Z.2 + positive.2 + 2)

/-- Full stored-data representative construction, including the Cartesian
product and all subsequent numerical work. -/
def representativeBandWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction) : List (Fin M → TargetInterval ny) × ℕ :=
  let wide := materializedWideActionsWithWork M parent r b P
  let result := representativeFromActionsWithWork parent r sourceLength b tau theta child (wide.1.map Vector.get)
  (result.1, wide.2 + result.2 + wide.1.length + 1)

theorem representativeFromActionsWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (representativeFromActionsWithWork parent r (parent.hi - parent.lo) b tau theta child
      (wideActionList M parent r b P)).1 =
      representativeBandActions source target parent r b P tau.value theta.value
        (fun i s => (child i s).value) := by
  have hgap : (stateGapWithWork (parent.hi - parent.lo) r).1.value =
      rationalStateGap (substring source parent.lo parent.hi) target r := by
    rw [stateGapWithWork_value, rationalStateGap, substring_length source parent.lo parent.hi parent.valid]
  by_cases hne : wideActionList M parent r b P = []
  · simp only [representativeFromActionsWithWork, representativeBandActions, dite_eq_left hne]
  · have hz := wideMinimumWithWork_value parent r b P child hne
    have hzero : zero.value = 0 := by
      rw [← representation_value, zero_representation, UnreducedRational.value_zero]
    have hpositive : (ltWithWork zero (wideMinimumWithWork r child
        (wideActionList M parent r b P) hne).1).1 = true ↔
        0 < rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value) := by
      rw [ltWithWork_value, hz, hzero]
    simp only [representativeFromActionsWithWork, representativeBandActions, dite_eq_right hne]
    by_cases hp : 0 < rationalWideActionMinimum parent r b P hne (fun i s => (child i s).value)
    · rw [ite_eq_left (hpositive.mpr hp), ite_eq_left hp]
      dsimp only
      rw [bandFromActionsWithWork_value]
      simp only [divWithWork_value, hgap, hz, computedBandActions, dite_eq_right hne]
    · rw [ite_eq_right (fun h => hp (hpositive.mp h)), ite_eq_right hp]

theorem representativeBandWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (representativeBandWithWork parent r (parent.hi - parent.lo) b P tau theta child).1 =
      representativeBandActions source target parent r b P tau.value theta.value
        (fun i s => (child i s).value) := by
  simp only [representativeBandWithWork, materializedWideActionsWithWork_value]
  exact representativeFromActionsWithWork_value source target parent r b P tau theta child

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact rounded canonical actions from their computed binary envelopes.
Rounding spacing is obtained by a natural ceiling, since the dyadic product
is either below one or an integer. No logarithm is evaluated. -/

namespace EditApproximation

open Finset

theorem interval_eq_of_endpoints {n : ℕ} (a b : TargetInterval n)
    (hl : a.lo = b.lo) (hh : a.hi = b.hi) : a = b := by
  cases a
  cases b
  cases hl
  cases hh
  rfl

/-- A binary interval output, with its order/range proofs erased. -/


@[simp] theorem roundStateWithWork_value {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : TargetInterval n) : (roundStateWithWork spacing hspacing q).1 = roundInterval spacing q := by
  apply interval_eq_of_endpoints
  · exact congrArg Prod.fst (binaryIntervalRoundWithWork_value spacing hspacing q)
  · exact congrArg Prod.snd (binaryIntervalRoundWithWork_value spacing hspacing q)



@[simp] theorem actionEqualWithWork_value {n M : ℕ} (a b : Fin M → TargetInterval n) :
    (actionEqualWithWork a b).1 = true ↔ a = b := by
  simp only [actionEqualWithWork, allWithWork_value, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · intro h
    funext i
    exact interval_eq_of_endpoints _ _ (h i).1 (h i).2
  · intro h
    subst b
    exact fun _ => ⟨rfl, rfl⟩

/-- A literal membership scan, preserving the wide-list definition on
inaccurate as well as accurate input seeds. -/


@[simp] theorem actionMemberWithWork_value {n M : ℕ} (a : Fin M → TargetInterval n)
    (actions : List (Fin M → TargetInterval n)) :
    (actionMemberWithWork a actions).1 = true ↔ a ∈ actions := by
  induction actions with
  | nil => simp only [actionMemberWithWork, Bool.false_eq_true, List.not_mem_nil]
  | cons b rest ih =>
    simp only [actionMemberWithWork, Bool.or_eq_true, actionEqualWithWork_value, ih, List.mem_cons]

namespace BinaryFraction



@[simp] theorem roundedSpacingWithWork_value (theta envelope : BinaryFraction) :
    bitWordValue (roundedSpacingWithWork theta envelope).1 = ⌈max 1 (theta.value * envelope.value)⌉₊ := by
  simp only [roundedSpacingWithWork, naturalCeilingWithWork_value, maxWithWork_value,
    canonicalMulWithWork_value, one, nat_value, Nat.cast_one]

theorem roundedSpacingWithWork_pos (theta envelope : BinaryFraction) :
    0 < bitWordValue (roundedSpacingWithWork theta envelope).1 := by
  rw [roundedSpacingWithWork_value, Nat.ceil_pos]
  exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (le_max_left _ _)

theorem roundedSpacingWithWork_band_value {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M) (hb : 0 < b) :
    bitWordValue (roundedSpacingWithWork (inversePowerTwo thetaExponent)
      (bandEnvelopeWithWork b band initial i).1).1 =
      bandRoundSpacing thetaExponent b band (fun j q => (initial j q).value) i := by
  rw [roundedSpacingWithWork_value, inversePowerTwo_value, bandEnvelopeWithWork_value _ _ _ _ hb,
    ← bandRoundSpacing_exact thetaExponent b band (fun j q => (initial j q).value) i, Nat.ceil_natCast]

def roundedBandWithWork {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) :
    Vector (TargetInterval ny) M × ℕ :=
  vectorMapWithWork M fun i =>
    let envelope := bandEnvelopeWithWork b band initial i
    let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
    let rounded := roundStateWithWork (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos _ _) (band.head hne i)
    (rounded.1, envelope.2 + spacing.2 + rounded.2 + thetaExponent + 3)

@[simp] theorem roundedBandWithWork_value {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (hb : 0 < b) :
    (roundedBandWithWork thetaExponent b band hne initial).1.get =
      canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) := by
  funext i
  simp only [roundedBandWithWork, vectorMapWithWork_value, roundStateWithWork_value,
    roundedSpacingWithWork_band_value _ _ _ _ _ hb,
    canonicalRoundedBandAction, roundedBandAction]

/-- All numerical acceptance tests after a nonempty band has been built. -/
def unskippedGuardWithWork {nx ny M : ℕ} (parent : TargetInterval nx) (_center : TargetInterval ny)
    (b thetaExponent : ℕ) (F : BinaryFraction) (band wide : List (Fin M → TargetInterval ny))
    (hne : band ≠ []) (initial : Fin M → TargetInterval ny → BinaryFraction) : Bool × ℕ :=
  let envelope := envelopeVectorWithWork b band initial
  let total := bandMassTotalWithWork envelope.1
  let fb := canonicalMulWithWork F (nat b)
  let limit := canonicalMulWithWork (nat 64) fb.1
  let sumGuard := leWithWork total.1 limit.1
  let rounded := roundedBandWithWork thetaExponent b band hne initial
  let wideGuard := actionMemberWithWork rounded.1.get wide
  let gapGuard := allWithWork (fun i =>
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.1.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.1.get i)
    let test := leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3)) (List.finRange M)
  (sumGuard.1 && wideGuard.1 && gapGuard.1,
    envelope.2 + total.2 + fb.2 + limit.2 + sumGuard.2 + rounded.2 + wideGuard.2 + gapGuard.2 + 5)

@[simp] theorem unskippedGuardWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b thetaExponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval target.length)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval target.length → BinaryFraction) (hb : 0 < b) :
    (unskippedGuardWithWork parent center b thetaExponent F band wide hne initial).1 = true ↔
      (∑ i, bandChildEnvelope b band (fun j q => (initial j q).value) i) ≤ 64 * F.value * b ∧
      canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) ∈ wide ∧
      ∀ i, |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
        (canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) i)| ≤
          2 * bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  have hsub (i : Fin M) :
      bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).1 =
        (sourceChild parent i).hi - (sourceChild parent i).lo :=
    binaryNaturalSubtractWithWork_value _ _ (sourceChild parent i).ordered
  simp only [unskippedGuardWithWork, Bool.and_eq_true, leWithWork_value,
    bandMassTotalWithWork_value, canonicalMulWithWork_value, nat_value,
    envelopeVectorWithWork_value b band initial hb, roundedBandWithWork_value _ _ _ _ _ hb,
    actionMemberWithWork_value, allWithWork_value, List.mem_finRange, forall_true_left,
    absolute_value, stateGapWithWork_value, hsub, rationalStateGap,
    substring_length source _ _ (sourceChild parent _).valid]
  rw [mul_assoc, Nat.cast_ofNat, and_assoc, Nat.cast_ofNat]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boolean work for the actual canonical rounding and wide-membership
tests. Interval endpoints retain their original target bound after rounding. -/

namespace EditApproximation

namespace BinaryFraction

def roundedSpacingWordBudget (B : ℕ) : ℕ := 4 * B + 4

def roundedSpacingBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 1500 * (4 * B + 3) ^ 2 + 3

def roundedBandInputBudget (thetaExponent b M B : ℕ) : ℕ :=
  thetaExponent + 2 + 3 * bandEnvelopeWordBudget b M B + B

def roundedBandBitBudget (thetaExponent b M size B : ℕ) : ℕ :=
  let W := roundedBandInputBudget thetaExponent b M B
  M * (bandEnvelopeBitBudget b M size B + roundedSpacingBitBudget W +
    500 * (roundedSpacingWordBudget W + B + 1) ^ 2 + thetaExponent + 11)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialization of the online coordinate array includes its equality
tests and duplicate-removal scan. Endpoints and child indices are compared
by the verified binary natural comparator. -/

namespace EditApproximation



@[simp] theorem coordinateEqualWithWork_value {M n : ℕ} (a b : Fin M × TargetInterval n) :
    (coordinateEqualWithWork a b).1 = true ↔ a = b := by
  simp only [coordinateEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · rintro ⟨⟨hc, hl⟩, hh⟩
    have hi : a.1 = b.1 := Fin.ext hc
    have hq : a.2 = b.2 := by
      rcases a with ⟨i, q⟩
      rcases b with ⟨j, r⟩
      cases q
      cases r
      cases hl
      cases hh
      rfl
    exact Prod.ext hi hq
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem coordinateEqualWithWork_cost {M n : ℕ} (a b : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (coordinateEqualWithWork a b).2 ≤ 24 * B + 8 := by
  have hc := naturalEqualWithWork_cost a.1.val b.1.val B
    ((Nat.size_le_size a.1.isLt.le).trans hM) ((Nat.size_le_size b.1.isLt.le).trans hM)
  have hl := naturalEqualWithWork_cost a.2.lo b.2.lo B
    ((Nat.size_le_size (a.2.ordered.trans a.2.valid)).trans hn)
    ((Nat.size_le_size (b.2.ordered.trans b.2.valid)).trans hn)
  have hh := naturalEqualWithWork_cost a.2.hi b.2.hi B
    ((Nat.size_le_size a.2.valid).trans hn) ((Nat.size_le_size b.2.valid).trans hn)
  change _ + _ + _ + 2 ≤ _
  omega



theorem memberByWithWork_value {α : Type*} (equal : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b) (a : α) (xs : List α) :
    (memberByWithWork equal a xs).1 = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp only [memberByWithWork, Bool.false_eq_true, List.not_mem_nil]
  | cons b xs ih => simp only [memberByWithWork, Bool.or_eq_true, heq, ih, List.mem_cons]



theorem dedupByWithWork_value {α : Type*} [DecidableEq α] (equal : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b) (xs : List α) :
    (dedupByWithWork equal xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hm := memberByWithWork_value equal heq a rest
    have ht : (memberByWithWork equal a rest).1 = decide (a ∈ rest) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hm)
    simp only [dedupByWithWork, ht, ih, List.dedup_cons, decide_eq_true_eq]

namespace BinaryFraction



@[simp] theorem bandCoordinatesWithWork_value {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    (bandCoordinatesWithWork band).1 = listedBandCoordinates band := by
  simp only [bandCoordinatesWithWork, dedupByWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, listedBandCoordinates,
    List.ofFn_eq_map]

def bandCoordinatesBitBudget (M vertices B : ℕ) : ℕ :=
  vertices * (5 * M + 3) + (vertices * M + 1) ^ 2 * (24 * B + 12) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Callback work is retained when a finite loop is supplied with a
costed reader. These lemmas compare the literal loop counters, so a
lookup cannot disappear when its returned word is passed to arithmetic. -/

namespace EditApproximation

theorem arithmeticMapWithWork_extra {α β : Type*} (read plain : α → β × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
      (arithmeticMapWithWork read xs).2 ≤
        (arithmeticMapWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · change (read x).1 :: (arithmeticMapWithWork read xs).1 =
        (plain x).1 :: (arithmeticMapWithWork plain xs).1
      rw [hv, ht.1]
    · change (read x).2 + (arithmeticMapWithWork read xs).2 + 3 ≤
        (plain x).2 + (arithmeticMapWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hc ht.2

theorem filterWithWork_extra {α : Type*} (read plain : α → Bool × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
      (filterWithWork read xs).2 ≤
        (filterWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · change (if (read x).1 then x :: (filterWithWork read xs).1 else (filterWithWork read xs).1) =
        (if (plain x).1 then x :: (filterWithWork plain xs).1 else (filterWithWork plain xs).1)
      rw [hv, ht.1]
    · change (read x).2 + (filterWithWork read xs).2 + 3 ≤
        (plain x).2 + (filterWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hc ht.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPrefixReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Prefix predictors retain the costs of the child words they inspect. -/

namespace EditApproximation
namespace BinaryFraction



theorem prefixReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) :
    (prefixReadWithWork parent r states read j p).1 =
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).1 := by
  have hw : (arithmeticMapWithWork (fun i : Fin M =>
      if i.val < j then read i (states i) else (zero, 1)) (List.finRange M)).1 =
      List.ofFn (fun i : Fin M => if i.val < j then (read i (states i)).1 else zero) := by
    simp only [arithmeticMapWithWork_value, List.ofFn_eq_map]
    apply List.map_congr_left
    intro i _
    split_ifs <;> rfl
  simp only [prefixReadWithWork, hw, prefixWithWork]

theorem prefixReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 + M * (R + 4) := by
  let get := fun i : Fin M => if i.val < j then read i (states i) else (zero, 1)
  have h := arithmeticMapWithWork_cost get (List.finRange M) (R + 1) (by
    intro i _
    dsimp only [get]
    split_ifs
    · exact (hr i).trans (Nat.le_succ R)
    · omega)
  have hw : (arithmeticMapWithWork get (List.finRange M)).1 =
      List.ofFn (fun i : Fin M => if i.val < j then (read i (states i)).1 else zero) := by
    simp only [arithmeticMapWithWork_value, List.ofFn_eq_map]
    apply List.map_congr_left
    intro i _
    dsimp only [get]
    split_ifs <;> rfl
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at h
  change (arithmeticMapWithWork get (List.finRange M)).2 + _ + _ + _ + _ + _ + _ + 6 * M + 5 ≤ _
  rw [hw]
  unfold prefixWithWork
  dsimp only
  omega



theorem prefixMinimumReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction) :
    (prefixMinimumReadWithWork parent r actions hne read j p).1 =
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).1 := by
  simp only [prefixMinimumReadWithWork, prefixMinimumWithWork, arithmeticMapWithWork_value,
    prefixReadWithWork_eq]

theorem prefixMinimumReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 +
        (actions.length + 1) * (M * (R + 4)) := by
  have h := arithmeticMapWithWork_extra (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    (fun _ => M * (R + 4)) actions
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_cost parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_cost parent r (actions.head hne) read j p R (hr _ (List.head_mem hne))
  have hs : (actions.map (fun _ => M * (R + 4))).sum = actions.length * (M * (R + 4)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold prefixMinimumReadWithWork prefixMinimumWithWork
  dsimp only
  rw [prefixReadWithWork_eq, h.1]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCutReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal cut predicates and all-cut loops with costed child readers. -/

namespace EditApproximation

theorem allWithWork_extra {α : Type*} (read plain : α → Bool × ℕ) (extra : α → ℕ)
    (xs : List α) (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
      (allWithWork read xs).2 ≤ (allWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hh := hv x List.mem_cons_self
    have hhCost := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · change ((read x).1 && (allWithWork read xs).1) =
        ((plain x).1 && (allWithWork plain xs).1)
      rw [hh, ht.1]
    · change (read x).2 + (allWithWork read xs).2 + 3 ≤
        (plain x).2 + (allWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hhCost ht.2

namespace BinaryFraction



theorem cutGuardReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).1 =
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).1 := by
  simp only [cutGuardReadWithWork, cutGuardWithWork]
  split_ifs
  · rfl
  · simp only [prefixMinimumReadWithWork_eq]

theorem cutGuardReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 +
        (actions.length + 1) * (M * (R + 4)) := by
  have costBound (s o p p' v u w x y A : ℕ) (hp : p ≤ p' + A) :
      s + o + p + v + u + w + x + y + 5 ≤ s + o + p' + v + u + w + x + y + 5 + A := by
    omega
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · exact Nat.le_add_right _ _
  · have h := prefixMinimumReadWithWork_cost parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    exact costBound _ _ _ _ _ _ _ _ _ _ h



theorem bandPredicateReadWithWork_eq_cost {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).1 =
      (bandPredicateWithWork parent r b tau theta velocity actions hne
        (fun i q => (read i q).1) states).1 ∧
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne
        (fun i q => (read i q).1) states).2 + M * ((actions.length + 1) * (M * (R + 4))) := by
  have costBound (c a t k k' A : ℕ) (hk : k ≤ k' + A) :
      c + a + t + k + 4 ≤ c + a + t + k' + 4 + A := by
    omega
  have h := allWithWork_extra
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (fun _ => (actions.length + 1) * (M * (R + 4))) (List.finRange M)
    (fun i _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ i)
    (fun i _ => cutGuardReadWithWork_cost parent r actions hne read states velocity _ i R hr)
  simp only [List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul] at h
  constructor
  · simp only [bandPredicateReadWithWork, bandPredicateWithWork, h.1]
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    exact costBound _ _ _ _ _ _ h.2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteBitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A structural polynomial bound for finite Boolean arithmetic loops.
The expression language includes only operations whose magnitude is bounded
by a fixed power of a common input bound. -/

namespace EditApproximation

inductive FiniteBitPolynomial (ι : Type*) where
  | input (i : ι)
  | constant (n : ℕ)
  | add (a b : FiniteBitPolynomial ι)
  | mul (a b : FiniteBitPolynomial ι)
  | pow (a : FiniteBitPolynomial ι) (n : ℕ)
  | maximum (a b : FiniteBitPolynomial ι)
  | minimum (a b : FiniteBitPolynomial ι)
  | bitLength (a : FiniteBitPolynomial ι)

namespace FiniteBitPolynomial

instance instOfNat {ι : Type*} (n : ℕ) : OfNat (FiniteBitPolynomial ι) n := ⟨.constant n⟩
instance instAdd {ι : Type*} : Add (FiniteBitPolynomial ι) := ⟨.add⟩
instance instMul {ι : Type*} : Mul (FiniteBitPolynomial ι) := ⟨.mul⟩
instance instPowNat {ι : Type*} : Pow (FiniteBitPolynomial ι) ℕ := ⟨.pow⟩

def eval {ι : Type*} (env : ι → ℕ) : FiniteBitPolynomial ι → ℕ
  | .input i => env i
  | .constant n => n
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .pow a n => a.eval env ^ n
  | .maximum a b => max (a.eval env) (b.eval env)
  | .minimum a b => min (a.eval env) (b.eval env)
  | .bitLength a => Nat.size (a.eval env)

def degree {ι : Type*} : FiniteBitPolynomial ι → ℕ
  | .input _ => 1
  | .constant n => Nat.size n
  | .add a b => max a.degree b.degree + 1
  | .mul a b => a.degree + b.degree
  | .pow a n => a.degree * n
  | .maximum a b => max a.degree b.degree
  | .minimum a b => max a.degree b.degree
  | .bitLength a => a.degree

end FiniteBitPolynomial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixBitEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree polynomial envelope for the literal prefix and band-test
arithmetic. The finite expression represents the bit counters;
its degree is independent of every input length and parameter. -/

namespace EditApproximation

abbrev PE := FiniteBitPolynomial (Fin 4)

def ps (a : PE) : PE := .bitLength a
def pn (a b : PE) : PE := .minimum a b

def peSumWord (n B : PE) : PE :=
  (B + 1) + ps n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
def peSumBit (n B : PE) : PE := 1 + n * (100000 * (peSumWord n B + 1) ^ 2)
def peSumStorage (n B : PE) : PE := ps n + B + 2 * (1 + n * (B + 1)) + 2
def peConnectionWord (n B : PE) : PE := peSumStorage (n + 1) (8 * B + 6)
def peConnectionBit (n B : PE) : PE :=
  (n + 1) * (6000 * (B + 1) ^ 2 + 4) + n * (2 * B + 6) +
    peSumBit (n + 1) (8 * B + 6) + 6 * (n + 1) + 1
def pePrefixWord (M j B : PE) : PE :=
  8 * (peConnectionWord (pn j M) (8 * B + 6) + peSumStorage M B) + 6
def pePrefixBit (M j B : PE) : PE :=
  6000 * (B + 1) ^ 2 + peConnectionBit (pn j M) (8 * B + 6) +
    peSumBit M B + 6 * M +
    6000 * (peConnectionWord (pn j M) (8 * B + 6) + peSumStorage M B + 1) ^ 2 +
    2 * B + 6 * M + 5
def pePrefixMinimumBit (M j v B : PE) : PE :=
  pePrefixBit M j B + v * (pePrefixBit M j B + 3) +
    (1 + v * (1000 * (pePrefixWord M j B + 1) ^ 2 + 2)) + 1
def peAffineBit (B : PE) : PE :=
  6000 * (B + 1) ^ 2 + 1 + 2000 * (B + 1) ^ 2 +
    (6000 * (12 * B + 9) ^ 2 + 1) + (1000 * (96 * B + 71) ^ 2 + 1) + 4
def peCutWord (M j B : PE) : PE := pePrefixWord M j (8 * B + 6) + 76 * B + 50
def peCutBit (M j v B : PE) : PE :=
  2 * (6000 * (B + 1) ^ 2 + 1) + pePrefixMinimumBit M j v (8 * B + 6) +
    peAffineBit (peCutWord M j B) + 4 * B + 6
def peNaturalDistanceBit (B : PE) : PE :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3
def peToleranceBit (B : PE) : PE :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 + 2 * B + 3
def prefixAggregateExpression : PE :=
  let M := .input 0
  let j := .input 1
  let v := .input 2
  let B := .input 3
  pePrefixWord M j B + pePrefixBit M j B + pePrefixMinimumBit M j v B +
    peCutWord M j B + peCutBit M j v B + peNaturalDistanceBit B + peToleranceBit B

/-- Fixed degree of the prefix/guard arithmetic implementation. -/
def prefixArithmeticDegree : ℕ := prefixAggregateExpression.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the executed representative scores and velocity. They use
only the widths of actual stored inputs, and apply on every seed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def endpointDistanceWordBudget (B : ℕ) : ℕ := 64 * B + 54

def endpointDistanceBitBudget (B : ℕ) : ℕ :=
  2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3

def endpointScoreWordBudget (M B : ℕ) : ℕ :=
  8 * (connectionWordBudget M B + bandMassTotalStorageBudget M B) + 6

def endpointScoreBitBudget (M B : ℕ) : ℕ :=
  connectionBitBudget M B + 2 * B + M + 2 + storedSumBitBudget M B + 6 * M +
    6000 * (connectionWordBudget M B + bandMassTotalStorageBudget M B + 1) ^ 2 + 2

def wideMinimumBitBudget (M n B : ℕ) : ℕ :=
  endpointScoreBitBudget M B + n * (endpointScoreBitBudget M B + 3) +
    (1 + n * (1000 * (endpointScoreWordBudget M B + 1) ^ 2 + 2)) + 2

def stateGapWordBudget (B : ℕ) : ℕ := 64 * B + 54

def stateGapBitBudget (B : ℕ) : ℕ :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandTailWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Work of the literal representative tail. The sole callback premise is
an explicit bound on the already-defined band predicate, whose primitive
bound is `bandPredicateWithWork_cost`; no accuracy property is assumed. -/

namespace EditApproximation
namespace BinaryFraction

def bandFromActionsBitBudget (n B C : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 1000 * (8 * B + 7) ^ 2 + n * (C + 3) + 4

def representativeTailInputBudget (M B : ℕ) : ℕ :=
  B + endpointScoreWordBudget M B + stateGapWordBudget B + 1

def representativeTailBitBudget (M n B C : ℕ) : ℕ :=
  let W := representativeTailInputBudget M B
  wideMinimumBitBudget M n B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
    2100 * (W + 2) ^ 2 + bandFromActionsBitBudget n (4 * W + 4) C + 3

def representativeGuardInputBudget (M vertices B : ℕ) : ℕ :=
  4 * representativeTailInputBudget M B + 4 + B + M + vertices + 2

def representativeCompleteBitBudget (M vertices B : ℕ) : ℕ :=
  let S := representativeGuardInputBudget M vertices B
  representativeTailBitBudget M vertices B
    (bandPredicateBitBudget M S (S ^ prefixArithmeticDegree))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGrid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Local endpoint lists executed with binary division, multiplication,
subtraction and validity comparisons. Only the bounded grid-index range
is visited. -/

namespace EditApproximation



@[simp] theorem saturatingSubtractWithWork_value (a b : ℕ) :
    bitWordValue (saturatingSubtractWithWork a b).1 = a - b := by
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs with h
  · have hlt := (binaryNaturalCompareWithWork_lt a b).mp h
    simp only [bitWordValue, Nat.sub_eq_zero_of_le hlt.le]
  · exact binaryNaturalSubtractWithWork_value a b (le_of_not_gt (fun hab =>
      h ((binaryNaturalCompareWithWork_lt a b).mpr hab)))

theorem naturalCeiling_div_eq_ceilDiv (lo g : ℕ) (hg : 0 < g) :
    ⌈(lo : ℚ) / g⌉₊ = lo ⌈/⌉ g := by
  have hgQ : (0 : ℚ) < g := by exact_mod_cast hg
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hgQ).mpr
    have h := (ceilDiv_le_iff_le_mul hg).mp (le_rfl : lo ⌈/⌉ g ≤ lo ⌈/⌉ g)
    exact_mod_cast (by simpa only [mul_comm] using h : lo ≤ (lo ⌈/⌉ g) * g)
  · apply (ceilDiv_le_iff_le_mul hg).mpr
    have h := (div_le_iff₀ hgQ).mp (Nat.le_ceil ((lo : ℚ) / g))
    exact_mod_cast (by simpa only [mul_comm] using h : (lo : ℚ) ≤ g * ⌈(lo : ℚ) / g⌉₊)



@[simp] theorem gridPointsWithWork_value (g lo hi : ℕ) (hg : 0 < g) :
    (gridPointsWithWork g lo hi).1 = gridPointsBetween g lo hi := by
  have hl : bitWordValue (bitCeilDivWithWork g.bits lo.bits).1 = lo ⌈/⌉ g := by
    rw [bitCeilDivWithWork_value _ _ (by simpa only [bitWordValue_bits] using hg),
      bitWordValue_bits, bitWordValue_bits, naturalCeiling_div_eq_ceilDiv lo g hg]
  have hu := (binaryNaturalDivModWithWork_spec hi g hg).1
  simp only [gridPointsWithWork, arithmeticMapWithWork_value, binaryNaturalMulWithWork_value,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, hl, hu, gridPointsBetween]



@[simp] theorem makeStateWithWork_value (n lo hi : ℕ) :
    (makeStateWithWork n lo hi).1 = makeTargetState n lo hi := by
  have htest : ((wordLEWithWork lo.bits hi.bits).1 && (wordLEWithWork hi.bits n.bits).1) = true ↔
      lo ≤ hi ∧ hi ≤ n := by
    simp only [Bool.and_eq_true, wordLEWithWork_value, bitWordValue_bits]
  unfold makeStateWithWork makeTargetState
  dsimp only
  by_cases h : lo ≤ hi ∧ hi ≤ n
  · rw [dite_eq_left (htest.mpr h), dite_eq_left h]
  · rw [dite_eq_right (fun ht => h (htest.mp ht)), dite_eq_right h]



@[simp] theorem filterMapWithWork_value {α β : Type*} (f : α → Option β × ℕ) (values : List α) :
    (filterMapWithWork f values).1 = values.filterMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [filterMapWithWork, List.filterMap_cons, ih]
    cases (f a).1 <;> rfl



@[simp] theorem gridStateBoxWithWork_value (n g radius lo hi : ℕ) (hg : 0 < g) :
    (gridStateBoxWithWork n g radius lo hi).1 = gridStateBox n g radius lo hi := by
  simp only [gridStateBoxWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value, gridPointsWithWork_value _ _ _ hg, saturatingSubtractWithWork_value,
    binaryNaturalAddWithWork_value, gridStateBox]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary work for the actual bounded endpoint-index loops. The bound is
linear in the emitted one-dimensional grid size and quadratic in bit width. -/

namespace EditApproximation

def gridPointsBitBudget (n B : ℕ) : ℕ :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)

def gridStateBoxBitBudget (count B : ℕ) : ℕ :=
  96 * (B + 1) + 2 * gridPointsBitBudget count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialKernel
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal initial-cone arithmetic on gathered integer seed entries. The
local grid list is supplied by its bounded enumerator; all values, ceilings,
spatial charges and the fallback minimum are computed on binary storage. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem ofNaturalWord_value (bits : List Bool) :
    (ofNaturalWord bits).value = (bitWordValue bits : ℚ) := by
  simp only [ofNaturalWord, value, SignedBinary.value, signedMagnitude, Bool.false_eq_true,
    ↓reduceIte, Int.cast_natCast, bitWordValue, Bool.toNat_true, Nat.mul_zero, Nat.add_zero,
    Nat.cast_one, div_one]

@[simp] theorem ofNaturalWord_width (bits : List Bool) :
    (ofNaturalWord bits).width = max bits.length 1 := rfl



@[simp] theorem scaledSeedWithWork_value (U : ℕ) (a gap : BinaryFraction) :
    (scaledSeedWithWork U a gap).1.value = scaledSeedValue U a.value gap.value := by
  simp only [scaledSeedWithWork, maxWithWork_value, ofNaturalWord_value,
    naturalCeilingWithWork_value, divWithWork_value, nat_value, absolute_value, scaledSeedValue]



@[simp] theorem initialConeWithWork_value {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (a L : BinaryFraction)
    (query center : TargetInterval target.length) :
    (initialConeWithWork source.length U a L query center).1.value =
      initialConeValue source target U a.value L.value query center := by
  simp only [initialConeWithWork, canonicalAddWithWork_value, canonicalMulWithWork_value,
    scaledSeedWithWork_value, stateGapWithWork_value, endpointDistanceWithWork_value,
    initialConeValue, rationalStateGap]

/-- The local initial-cone arithmetic after the center list has been
constructed and the corresponding seed values gathered. -/
def initialMinimumWithWork {n : ℕ} (sourceLength : ℕ) (U : TargetInterval n → ℕ)
    (N F : ℕ) (a : BinaryFraction) (query : TargetInterval n) (centers : List (TargetInterval n)) :
    BinaryFraction × ℕ :=
  let zeroTest := naturalEqualWithWork (U query) 0
  if zeroTest.1 then (zero, zeroTest.2 + 1) else
    let L := canonicalMulWithWork (nat 32) (nat F)
    let coefficient := canonicalAddWithWork L.1 one
    let fallback := canonicalMulWithWork coefficient.1 (nat N)
    let scores := arithmeticMapWithWork (initialConeWithWork sourceLength U a L.1 query) centers
    let result := minimumWithWork fallback.1 scores.1
    (result.1, zeroTest.2 + L.2 + coefficient.2 + fallback.2 + scores.2 + result.2 +
      Nat.size F + Nat.size N + 6)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryScaleGrid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal dyadic scales and the finite initial-cone center list, with
binary rational comparisons and bounded grid enumeration. -/

namespace EditApproximation

theorem log_two_add_one_eq_size (N : ℕ) (hN : 0 < N) :
    Nat.log 2 N + 1 = Nat.size N := by
  apply Nat.le_antisymm
  · have h := Nat.pow_log_le_self 2 hN.ne'
    have hlt : Nat.log 2 N < Nat.size N := Nat.lt_size.mpr h
    omega
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N)



@[simp] theorem dyadicScalesWithWork_value (N : ℕ) :
    (dyadicScalesWithWork N).1 = dyadicScales N := by
  have hcount : max 1 N.bits.length = Nat.log 2 N + 1 := by
    by_cases hz : N = 0
    · subst N
      decide
    · have h := log_two_add_one_eq_size N (Nat.pos_of_ne_zero hz)
      have hp := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
      rw [Nat.size_eq_bits_len, max_eq_right hp, h]
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value, hcount,
    dyadicScales]



@[simp] theorem seedGridSpacingWithWork_value (b P : ℕ) (hP : 0 < P) :
    bitWordValue (seedGridSpacingWithWork b P).1 = seedGridSpacing b P := by
  have hv := (binaryNaturalDivModWithWork_spec b P hP).1
  unfold seedGridSpacingWithWork seedGridSpacing
  dsimp only
  split_ifs with ht
  · have hq : b / P ≤ 1 := by
      have h := (wordLEWithWork_value _ _).mp ht
      change bitWordValue (binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rwa [hv] at h
    rw [max_eq_left hq]
    rfl
  · have hq : 1 ≤ b / P := by
      have h := mt (wordLEWithWork_value _ _).mpr ht
      change ¬ bitWordValue (binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rw [hv] at h
      exact Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [max_eq_right hq]
    exact hv

theorem seedGridSpacingWithWork_pos (b P : ℕ) (hP : 0 < P) :
    0 < bitWordValue (seedGridSpacingWithWork b P).1 := by
  rw [seedGridSpacingWithWork_value b P hP]
  unfold seedGridSpacing
  omega

namespace BinaryFraction



@[simp] theorem initialScaleGuardWithWork_value (U b : ℕ) (A : BinaryFraction) :
    (initialScaleGuardWithWork U b A).1 = true ↔
      (U : ℚ) / (16 * A.value ^ 2) ≤ b ∧ (b : ℚ) ≤ 4 * A.value * U := by
  simp only [initialScaleGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value, pow_two]
  norm_num



@[simp] theorem initialCenterGuardWithWork_value (b U : ℕ) (A : BinaryFraction) :
    (initialCenterGuardWithWork b U A).1 = true ↔
      (b : ℚ) / 2 ≤ U ∧ (U : ℚ) ≤ 4 * A.value * b := by
  simp only [initialCenterGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value]
  norm_num

def initialCentersWithWork {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) : List (TargetInterval n) × ℕ :=
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork (U q) b A) scales.1
  let centers := arithmeticFlatMapWithWork (fun b =>
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
    let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
    (selected.1, spacing.2 + points.2 + selected.2 + 2)) active.1
  (centers.1, scales.2 + active.2 + centers.2 + 3)

@[simp] theorem initialCentersWithWork_value {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) (hP : 0 < P) :
    (initialCentersWithWork N P A U q).1 = localInitialConeCenters N P A.value U q := by
  have hscale (b : ℕ) : (initialScaleGuardWithWork (U q) b A).1 =
      decide ((U q : ℚ) / (16 * A.value ^ 2) ≤ b ∧ (b : ℚ) ≤ 4 * A.value * U q) :=
    Bool.eq_iff_iff.mpr (by simp only [initialScaleGuardWithWork_value, decide_eq_true_eq])
  have hcenter (b : ℕ) (r : TargetInterval n) : (initialCenterGuardWithWork b (U r) A).1 =
      decide ((b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A.value * b) :=
    Bool.eq_iff_iff.mpr (by simp only [initialCenterGuardWithWork_value, decide_eq_true_eq])
  have hgrid (b : ℕ) :
      (gridStateBoxWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
        (U q) q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) (U q) q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (seedGridSpacingWithWork_pos b P hP),
      seedGridSpacingWithWork_value b P hP]
    rfl
  simp only [initialCentersWithWork, arithmeticFlatMapWithWork_value,
    filterWithWork_value, dyadicScalesWithWork_value, hgrid,
    hscale, hcenter, localInitialConeCenters]

def initialProgramWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) : BinaryFraction × ℕ :=
  let centers := initialCentersWithWork N P A U q
  let result := initialMinimumWithWork sourceLength U N F a q centers.1
  (result.1, centers.2 + result.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideGrid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual wide-action materialization starts from binary balanced cuts and
bounded endpoint grids. The Cartesian-product routine receives the lists
just computed, so their construction is included in the counter. -/

namespace EditApproximation



@[simp] theorem balancedCutWithWork_value (lo width M i : ℕ) (hM : 0 < M) :
    bitWordValue (balancedCutWithWork lo width M i).1 = balancedCut lo width M i := by
  simp only [balancedCutWithWork, binaryNaturalAddWithWork_value,
    (binaryNaturalDivModWithWork_spec _ M hM).1, binaryNaturalMulWithWork_value, balancedCut]



@[simp] theorem sourceChildWithWork_value {n M : ℕ} (parent : TargetInterval n) (i : Fin M) :
    (sourceChildWithWork parent i).1 = sourceChild parent i := by
  have hl : (sourceChildWithWork parent i).1.lo = (sourceChild parent i).lo := by
    simp only [sourceChildWithWork, balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
      saturatingSubtractWithWork_value, sourceChild]
  have hh : (sourceChildWithWork parent i).1.hi = (sourceChild parent i).hi := by
    simp only [sourceChildWithWork, balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, sourceChild]
  generalize heq : (sourceChildWithWork parent i).1 = first at hl hh ⊢
  generalize hother : sourceChild parent i = second at hl hh ⊢
  cases first
  cases second
  cases hl
  cases hh
  rfl



@[simp] theorem wideChildGridWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (i : Fin M) (hP : 0 < P) :
    (wideChildGridWithWork parent r b P i).1 = wideChildStateList parent r b P i := by
  simp only [wideChildGridWithWork, sourceChildWithWork_value,
    seedGridSpacingWithWork_value b P hP, binaryNaturalMulWithWork_value,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, wideChildStateList]
  apply gridStateBoxWithWork_value
  unfold seedGridSpacing
  omega



@[simp] theorem wideActionGridWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) :
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) = wideActionList M parent r b P := by
  have hchoices : (vectorMapWithWork M (wideChildGridWithWork parent r b P)).1.get =
      wideChildStateList parent r b P := by
    funext i
    rw [vectorMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]
  simp only [wideActionGridWithWork, materializedAssignmentsWithWork_value, hchoices, wideActionList]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideChildWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every child-grid list is constructed before the Cartesian product.
These bounds include the balanced endpoints, integer spacing and radius,
endpoint translations, and the two bounded grid loops. -/

namespace EditApproximation

def wideChildGridBitBudget (P B : ℕ) : ℕ :=
  10000 * (B + 12) ^ 2 + gridStateBoxBitBudget (40 * P + 2) (B + 12)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedRepresentative
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The representative constructor executes the balanced child grids
before materializing the Cartesian product and evaluating its scores. -/

namespace EditApproximation
namespace BinaryFraction

def preparedRepresentativeWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction) : List (Fin M → TargetInterval ny) × ℕ :=
  let wide := wideActionGridWithWork M parent center b P
  let result := representativeFromActionsWithWork parent center sourceLength b tau theta child
    (wide.1.map Vector.get)
  (result.1, wide.2 + result.2 + wide.1.length + 1)

theorem preparedRepresentativeWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (hP : 0 < P)
    (tau theta : BinaryFraction) (child : Fin M → TargetInterval ny → BinaryFraction) :
    (preparedRepresentativeWithWork parent center sourceLength b P tau theta child).1 =
      (representativeBandWithWork parent center sourceLength b P tau theta child).1 := by
  simp only [preparedRepresentativeWithWork, representativeBandWithWork,
    wideActionGridWithWork_value M parent center b P hP, materializedWideActionsWithWork_value]

@[simp] theorem preparedRepresentativeWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b P : ℕ) (hP : 0 < P) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).1 =
      representativeBandActions source target parent center b P tau.value theta.value
        (fun i q => (child i q).value) := by
  rw [preparedRepresentativeWithWork_eq _ _ _ _ _ hP]
  exact representativeBandWithWork_value source target parent center b P tau theta child

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryScoreReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Representative scores use literal reader calls at their child
coordinates. The stored value agrees with the previous arithmetic kernel. -/

namespace EditApproximation
namespace BinaryFraction



theorem endpointScoreReadWithWork_eq {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n) :
    (endpointScoreReadWithWork r read states).1 =
      (endpointScoreWithWork r (fun i q => (read i q).1) states).1 := by
  simp only [endpointScoreReadWithWork, endpointScoreWithWork,
    arithmeticMapWithWork_value, List.ofFn_eq_map]

theorem endpointScoreReadWithWork_cost {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 + M * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun i => read i (states i))
    (List.finRange M) R (fun i _ => hr i)
  simp only [List.length_finRange] at h
  simp only [endpointScoreReadWithWork, endpointScoreWithWork,
    arithmeticMapWithWork_value, List.ofFn_eq_map]
  omega



theorem wideMinimumReadWithWork_eq {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) :
    (wideMinimumReadWithWork r read actions hne).1 =
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1 := by
  simp only [wideMinimumReadWithWork, wideMinimumWithWork, arithmeticMapWithWork_value,
    endpointScoreReadWithWork_eq]

theorem wideMinimumReadWithWork_cost {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 +
        (actions.length + 1) * (M * (R + 3)) := by
  have h := arithmeticMapWithWork_extra (endpointScoreReadWithWork r read)
    (endpointScoreWithWork r (fun i q => (read i q).1)) (fun _ => M * (R + 3)) actions
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_cost r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_cost r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hs : (actions.map (fun _ => M * (R + 3))).sum = actions.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold wideMinimumReadWithWork wideMinimumWithWork
  dsimp only
  rw [endpointScoreReadWithWork_eq, h.1]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Representative bands with charged child-table reads in every score
and prefix predicate over the materialized wide grid. -/

namespace EditApproximation
namespace BinaryFraction



theorem bandFromActionsReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).1 =
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).1 ∧
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 +
        actions.length * (M * ((actions.length + 1) * (M * (R + 4)))) := by
  have costBound (a a' m g A : ℕ) (ha : a ≤ a' + A) :
      m + g + a + 2 ≤ m + g + a' + 2 + A := by
    omega
  have h := filterWithWork_extra
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    (fun _ => M * ((actions.length + 1) * (M * (R + 4)))) actions
    (fun states _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne read states R hr).1)
    (fun states _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne read states R hr).2)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · exact ⟨h.1, costBound _ _ _ _ _ h.2⟩
  · exact ⟨rfl, Nat.le_add_right _ _⟩



def representativeReadOverhead (M vertices R : ℕ) : ℕ :=
  (vertices + 1) * (M * (R + 4)) + vertices * (M * ((vertices + 1) * (M * (R + 4))))

theorem representativeFromActionsReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval ny)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).1 =
      (representativeFromActionsWithWork parent r sourceLength b tau theta (fun i q => (read i q).1) actions).1 ∧
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta (fun i q => (read i q).1) actions).2 +
        representativeReadOverhead M actions.length R := by
  have costBound (a a' c c' x y z A B : ℕ)
      (ha : a ≤ a' + A) (hc : c ≤ c' + B) :
      a + x + y + z + c + 3 ≤ a' + x + y + z + c' + 3 + (A + B) := by
    omega
  have shortCostBound (a a' x A B : ℕ) (ha : a ≤ a' + A) :
      a + x + 2 ≤ a' + x + 2 + (A + B) := by
    omega
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    exact ⟨trivial, Nat.le_add_right _ _⟩
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_cost r read actions hne R hr
    have hmono : (actions.length + 1) * (M * (R + 3)) ≤ (actions.length + 1) * (M * (R + 4)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.add_le_add_left (by decide : 3 ≤ 4) R))
    have hz' := hz.trans (Nat.add_le_add_left hmono _)
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_eq_cost parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      refine ⟨hb.1, ?_⟩
      exact costBound _ _ _ _ _ _ _ _ _ hz' hb.2
    · exact ⟨rfl, shortCostBound _ _ _ _ _ hz'⟩



theorem preparedRepresentativeReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).1 =
      (preparedRepresentativeWithWork parent center sourceLength b P tau theta (fun i q => (read i q).1)).1 ∧
    (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent center sourceLength b P tau theta (fun i q => (read i q).1)).2 +
        representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R := by
  have h := representativeFromActionsReadWithWork_eq_cost parent center sourceLength b tau theta read
    ((wideActionGridWithWork M parent center b P).1.map Vector.get) R (fun _ _ i => hr i _)
  simp only [List.length_map] at h
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  exact ⟨h.1, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitAllocation
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fresh Boolean-list cells allocated by the literal arithmetic routines.
Input tails are shared. Counts include discarded intermediate lists, so they
also bound the cells simultaneously live during evaluation. -/

namespace EditApproximation





theorem bitAddAllocation_le_work (left right : List Bool) (carry : Bool) :
    bitAddAllocation left right carry ≤ (bitAddWithWork left right carry).2 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddAllocation, bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftAllocation, bitAddNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitCarry false b carry)
      simp only [bitAddNilLeftAllocation, bitAddNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitCarry a false carry)
      simp only [bitAddAllocation, bitAddWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitCarry a b carry)
      simp only [bitAddAllocation, bitAddWithWork]
      omega





theorem bitSubtractAllocation_le_work (left right : List Bool) (borrow : Bool) :
    bitSubtractAllocation left right borrow ≤ (bitSubtractWithWork left right borrow).2.2 := by
  induction left generalizing right borrow with
  | nil =>
    simp only [bitSubtractAllocation, bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [bitSubtractNilLeftAllocation, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractNilLeftAllocation, bitSubtractNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractAllocation, bitSubtractWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractAllocation, bitSubtractWithWork]
      omega



theorem bitMulAllocation_le_work (left right : List Bool) :
    bitMulAllocation left right ≤ (bitMulWithWork left right).2 := by
  induction left with
  | nil => simp [bitMulAllocation, bitMulWithWork]
  | cons bit bits ih =>
    have h := bitAddAllocation_le_work (false :: (bitMulWithWork bits right).1) right false
    cases bit <;> simp only [bitMulAllocation, bitMulWithWork, Bool.false_eq_true, ↓reduceIte] <;>
      omega



theorem trimBitWordAllocation_le_work (bits : List Bool) :
    trimBitWordAllocation bits ≤ (trimBitWordWithWork bits).2 := by
  induction bits with
  | nil => simp [trimBitWordAllocation, trimBitWordWithWork]
  | cons bit bits ih =>
    simp only [trimBitWordAllocation, trimBitWordWithWork]
    split_ifs <;> omega

/-- Each division step allocates one candidate cell and one quotient cell,
plus the fresh subtraction result exactly when subtraction is executed. -/


theorem bitDivModAllocation_le_work (divisor bits : List Bool) :
    bitDivModAllocation divisor bits ≤ (bitDivModWithWork divisor bits).2.2 := by
  induction bits with
  | nil => simp [bitDivModAllocation, bitDivModWithWork]
  | cons bit bits ih =>
    have h := bitSubtractAllocation_le_work
      (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
    simp only [bitDivModAllocation, bitDivModWithWork]
    split_ifs <;> dsimp only <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_FractionAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace SignedBinary

/-- Fresh magnitude cells in exactly the branch taken by signed addition. -/


theorem addAllocation_le_work (a b : SignedBinary) :
    a.addAllocation b ≤ (a.addWithWork b).2 := by
  have ha := bitAddAllocation_le_work a.bits b.bits false
  have hs := bitSubtractAllocation_le_work a.bits b.bits false
  have ht := bitSubtractAllocation_le_work b.bits a.bits false
  unfold addAllocation addWithWork
  split_ifs
  · dsimp only
    omega
  · cases h : (bitCompareWithWork a.bits b.bits).1 <;> simp only [h] <;> omega



theorem mulAllocation_le_work (a b : SignedBinary) :
    a.mulAllocation b ≤ (a.mulWithWork b).2 := by
  have h := bitMulAllocation_le_work a.bits b.bits
  change bitMulAllocation a.bits b.bits ≤ (bitMulWithWork a.bits b.bits).2 + 4
  omega

end SignedBinary
namespace BinaryFraction

/-- Counts every newly allocated magnitude and denominator cell, including
cross-products that are discarded after the numerator is computed. -/


theorem addAllocation_le_work (a b : BinaryFraction) :
    a.addAllocation b ≤ (a.addWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulAllocation_le_work b.numerator a.denominatorInteger
  have h3 := SignedBinary.addAllocation_le_work
    (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  have h4 := bitMulAllocation_le_work a.denominator b.denominator
  unfold addAllocation addWithWork
  dsimp only
  omega



theorem mulAllocation_le_work (a b : BinaryFraction) :
    a.mulAllocation b ≤ (a.mulWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.numerator
  have h2 := bitMulAllocation_le_work a.denominator b.denominator
  unfold mulAllocation mulWithWork
  dsimp only
  omega

/-- Signed comparisons themselves reuse input words; rational comparison
allocates just its two cross-products. -/


theorem ltAllocation_le_work (a b : BinaryFraction) :
    a.ltAllocation b ≤ (a.ltWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulAllocation_le_work b.numerator a.denominatorInteger
  unfold ltAllocation ltWithWork
  dsimp only
  omega



theorem canonicalizeAllocation_le_work (a : BinaryFraction) :
    canonicalizeAllocation a ≤ (canonicalizeWithWork a).2 := by
  have hn := trimBitWordAllocation_le_work a.numerator.bits
  have hd := trimBitWordAllocation_le_work a.denominator
  unfold canonicalizeAllocation canonicalizeWithWork
  dsimp only
  omega



theorem canonicalAddAllocation_le_work (a b : BinaryFraction) :
    canonicalAddAllocation a b ≤ (canonicalAddWithWork a b).2 := by
  exact Nat.add_le_add (addAllocation_le_work a b)
    (canonicalizeAllocation_le_work (a.addWithWork b).1)



theorem canonicalMulAllocation_le_work (a b : BinaryFraction) :
    canonicalMulAllocation a b ≤ (canonicalMulWithWork a b).2 := by
  exact Nat.add_le_add (mulAllocation_le_work a b)
    (canonicalizeAllocation_le_work (a.mulWithWork b).1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem bitPowerWithWork_value (base : List Bool) (n : ℕ) :
    bitWordValue (bitPowerWithWork base n).1 = bitWordValue base ^ n := by
  induction n with
  | zero => simp [bitPowerWithWork, bitWordValue]
  | succ n ih =>
    simp only [bitPowerWithWork, trimBitWordWithWork_value, bitMulWithWork_value, ih, pow_succ]

def bitPowerBitBudget (n B : ℕ) : ℕ :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

namespace BinaryFraction



def powerDenominatorBitBudget (n A B : ℕ) : ℕ :=
  bitPowerBitBudget n B + 5000 * (A + (n * B + 1) + 2) ^ 2 + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Threshold reconstruction in the initial estimator

Deterministic reconstruction from Section 3 of the September 24, 2026
edit-distance manuscript.  Concentration is kept separate: the thresholds
can influence the approximate child costs, so no independence assumption
about those approximate costs is made here.
-/

namespace EditApproximation

/-- A threshold contribution of the coarse estimator. -/
noncomputable def thresholdContribution (threshold scale value : ℝ) : ℝ :=
  if threshold ≤ value then max value scale else 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pathwise accuracy of the concrete coarse recurrence

The events concern only fixed true child minima sampled with independent
labels. The deterministic reconstruction requires no independence of
approximate child costs.
-/

namespace EditApproximation

open Finset

universe u

/-- The true-cost threshold sum appearing in the simultaneous event. -/
noncomputable def coarseTrueThresholdSum {B D : ℕ} {α : Type u}
    (k : ℕ) (Q : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (allowance : ℚ) (transform : ℝ → ℝ) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) →
      ℕ → Fin (2 * k + 1) → ℝ
  | [], _, _ => 0
  | (child, draw, _) :: rest, start, shift =>
    thresholdContribution (coarseChildThreshold B Q allowance draw) (allowance / Q)
      (transform ((univ.inf' univ_nonempty
        (fun next => trueValue child start next + 2 * Nat.dist shift.val next.val) : ℕ) : ℝ)) +
      coarseTrueThresholdSum k Q trueValue allowance transform rest (start + child.word.length) shift

/-- Child accuracy at precisely the source positions visited by the
actual traversal, with its actual per-child allowance. -/
noncomputable def CoarseChildAccuracy {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (allowance : ℚ) (f : ℝ) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) → ℕ → Prop
  | [], _ => True
  | (child, draw, below) :: rest, start =>
    (∀ shift,
      (trueValue child start shift : ℝ) / f -
          ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) ≤
        value child below (lam * coarseChildThreshold B Q allowance draw) start shift ∧
      (value child below (lam * coarseChildThreshold B Q allowance draw) start shift : ℝ) ≤
        f * trueValue child start shift + ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) ∧
    CoarseChildAccuracy k Q lam trueValue value allowance f rest (start + child.word.length)

/-- The exact depth factor in Section 3. -/
noncomputable def coarseStructuralFactor (lam : ℚ) (D : ℕ) : ℝ :=
  ((1 + (lam : ℝ)) / (1 - (lam : ℝ))) ^ D

/-- Events for all children, including children below a pruned node. -/
def CoarseDescendantEvents {B D : ℕ} {α : Type u} (Q lam allowance : ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) → ℕ → Prop
  | [], _ => True
  | (child, draw, below) :: rest, start =>
    event child below (lam * coarseChildThreshold B Q allowance draw) start ∧
      CoarseDescendantEvents Q lam allowance event rest (start + child.word.length)

/-- The actual finite-tree event. At every node it uses only deterministic
true-cost minima and the node's current child threshold labels. -/
noncomputable def CoarseAccuracyEvent {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α)) :
    {D : ℕ} → CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop
  | _, .leaf _, _, _, _ => True
  | D + 1, .branch children, (draws, below), allowance, start =>
    let data := List.ofFn (fun i => (children i, draws i, below i))
    let trueValue := fun child => coarseShiftCost k frame child
    let f := coarseStructuralFactor lam D
    CoarseDescendantEvents Q lam allowance
      (fun child => CoarseAccuracyEvent k Q lam frame child) data start ∧
    ∀ shift,
      (1 - (lam : ℝ)) *
          (((coarseChildrenCost k trueValue (data.map Prod.fst) start shift : ℕ) : ℝ) /
            (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => cost / (f * (1 + (lam : ℝ)))) data start shift ∧
      coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => f * cost / (1 - (lam : ℝ))) data start shift ≤
        (1 + (lam : ℝ)) *
          (f * ((coarseChildrenCost k trueValue (data.map Prod.fst) start shift : ℕ) : ℝ) /
            (1 - (lam : ℝ))) + allowance

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent heterogeneous coarse threshold samples

Every child has its own fixed true cost and an independent uniform label
in `1,...,B`. The child estimates are absent from this probability space:
they enter only the pathwise reconstruction proved separately.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def coarseThresholdSample {B : ℕ} (scale value : ℝ) (draw : Fin B) : ℝ :=
  thresholdContribution (scale * (draw.val + 1 : ℕ) / B) scale value

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite coarse randomness

At each internal node, the child thresholds are independent uniform labels.
Recursive subtrees are independent of these labels. This complete probability
space also includes labels below pruned nodes.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

def coarseNodeChildStart {B D : ℕ} {α : Type u}
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ) (i : Fin B) : ℕ :=
  start + (((List.ofFn children).take i.val).map CoarseSourceTree.word).flatten.length

def coarseNodeChildCost {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (shift : Fin (2 * k + 1)) (i : Fin B) : ℕ :=
  univ.inf' univ_nonempty (fun next => value (children i) (coarseNodeChildStart children start i) next +
    2 * Nat.dist shift.val next.val)

/-- The two deterministic cost lists used at a node, simultaneously for
all shifts. The Boolean coordinate selects the lower or upper list. -/
noncomputable def coarseNodeSamplingValue {B D : ℕ} {α : Type u}
    (k : ℕ) (lam : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (index : Fin (2 * k + 1) × Bool) (i : Fin B) : ℝ :=
  if index.2 then
    (coarseNodeChildCost k value children start index.1 i : ℝ) / (f * (1 + (lam : ℝ)))
  else f * coarseNodeChildCost k value children start index.1 i / (1 - (lam : ℝ))

noncomputable def CoarseNodeDeviationEvent {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (draws : Fin B → Fin B) : Prop :=
  ∀ index : Fin (2 * k + 1) × Bool,
    |(∑ i, coarseThresholdSample ((allowance : ℝ) / Q)
        (coarseNodeSamplingValue k lam f value children start index i) (draws i)) -
      ∑ i, coarseNodeSamplingValue k lam f value children start index i| ≤
      (lam : ℝ) * (∑ i, coarseNodeSamplingValue k lam f value children start index i) + allowance

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseDenominatorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Construct the common denominator by Boolean products and binary
exponentiation, charging all intermediate bit operations. -/


 theorem coarseDenominatorWithWork_value (allowanceDen q L branching : List Bool) (D : ℕ) :
    bitWordValue (coarseDenominatorWithWork allowanceDen q L branching D).1 =
      coarseCommonDenominator (bitWordValue allowanceDen) (bitWordValue q)
        (bitWordValue L) (bitWordValue branching) D := by
  simp only [coarseDenominatorWithWork, trimBitWordWithWork_value,
    bitMulWithWork_value, bitPowerWithWork_value, coarseCommonDenominator]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_ScalarAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem bitPowerAllocation_le_work (base : List Bool) (n : ℕ) :
    bitPowerAllocation base n ≤ (bitPowerWithWork base n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm := bitMulAllocation_le_work (bitPowerWithWork base n).1 base
    have ht := trimBitWordAllocation_le_work
      (bitMulWithWork (bitPowerWithWork base n).1 base).1
    simp only [bitPowerAllocation, bitPowerWithWork]
    omega



theorem bitCeilDivAllocation_le_work (divisor bits : List Bool) :
    bitCeilDivAllocation divisor bits ≤ (bitCeilDivWithWork divisor bits).2 := by
  have hd := bitDivModAllocation_le_work divisor bits
  have ha := bitAddAllocation_le_work (bitDivModWithWork divisor bits).1 [true] false
  unfold bitCeilDivAllocation bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- Map allocation includes one result spine cell for every callback. -/


theorem arithmeticMapAllocation_le_work {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, allocation a ≤ (f a).2) :
    arithmeticMapAllocation allocation values ≤ (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork]
    omega

namespace BinaryFraction



theorem invAllocation_le_work (a : BinaryFraction) :
    invAllocation a ≤ a.invWithWork.2 := by
  unfold invAllocation invWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.zero_le _



theorem divAllocation_le_work (a b : BinaryFraction) :
    divAllocation a b ≤ (divWithWork a b).2 := by
  have hi := invAllocation_le_work b
  have hm := canonicalMulAllocation_le_work a b.invWithWork.1
  unfold divAllocation divWithWork
  dsimp only
  omega



theorem fixedDenominatorAllocation_le_work (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    fixedDenominatorAllocation a denominator hden ≤ (fixedDenominatorWithWork a denominator hden).2 := by
  have hm := bitMulAllocation_le_work a.numerator.bits denominator
  have hd := bitDivModAllocation_le_work a.denominator
    (bitMulWithWork a.numerator.bits denominator).1
  have hc := canonicalizeAllocation_le_work
    (⟨⟨a.numerator.negative,
      (bitDivModWithWork a.denominator (bitMulWithWork a.numerator.bits denominator).1).1⟩,
      denominator, hden⟩ : BinaryFraction)
  unfold fixedDenominatorAllocation fixedDenominatorWithWork
  dsimp only
  omega



theorem naturalCeilingAllocation_le_work (a : BinaryFraction) :
    naturalCeilingAllocation a ≤ a.naturalCeilingWithWork.2 := by
  have h := bitCeilDivAllocation_le_work a.denominator a.numerator.bits
  unfold naturalCeilingAllocation naturalCeilingWithWork
  split_ifs <;> dsimp only <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLoopSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fresh result-spine cells and recursive call frames for the literal
finite loops used in local continuation arithmetic. Callback footprints
are accounted separately; list elements are retained by pointer. -/

namespace EditApproximation



theorem arithmeticFlatMapAllocation_le_work {α β : Type*} (f : α → List β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (f x).2) :
    arithmeticFlatMapAllocation f allocation xs ≤ (arithmeticFlatMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapAllocation, arithmeticFlatMapWithWork]
    omega

theorem filterAllocation_le_work {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    filterAllocation test allocation xs ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterAllocation, filterWithWork]
    split_ifs <;> omega



theorem filterMapAllocation_le_work {α β : Type*} (f : α → Option β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (f x).2) :
    filterMapAllocation f allocation xs ≤ (filterMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterMapAllocation, filterMapWithWork]
    cases he : (f x).1 <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte] <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryNumericSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Allocation and invocation traces for the actual Boolean logarithm,
dot-product, and gradient loops. Constant literal words are shared. -/

namespace EditApproximation.BinaryFraction



theorem subAllocation_le_work (a b : BinaryFraction) :
    subAllocation a b ≤ (subWithWork a b).2 := by
  have h := canonicalAddAllocation_le_work a b.neg
  unfold subAllocation subWithWork
  dsimp only
  omega

theorem powAllocation_le_work (a : BinaryFraction) (n : ℕ) :
    powAllocation a n ≤ (powWithWork a n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := canonicalMulAllocation_le_work (powWithWork a n).1 a
    simp only [powAllocation, powWithWork]
    exact (Nat.add_le_add ih h).trans (Nat.le_succ _)

theorem logarithmPartialAllocation_le_work (b : BinaryFraction) (n : ℕ) :
    logarithmPartialAllocation b n ≤ (logarithmPartialWithWork b n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hp := powAllocation_le_work b (2 * n + 1)
    have hd := divAllocation_le_work (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))
    have ha := canonicalAddAllocation_le_work (logarithmPartialWithWork b n).1
      (divWithWork (powWithWork b (2 * n + 1)).1 (nat (2 * n + 1))).1
    simp only [logarithmPartialAllocation, logarithmPartialWithWork]
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ih hp) hd) ha) _)
      (by decide : 1 ≤ 5)

theorem logarithmAllocation_le_work (r : BinaryFraction) (n : ℕ) :
    logarithmAllocation r n ≤ (logarithmWithWork r n).2 := by
  have h1 := subAllocation_le_work r one
  have h2 := canonicalAddAllocation_le_work r one
  have h3 := divAllocation_le_work (subWithWork r one).1 (canonicalAddWithWork r one).1
  have h4 := logarithmPartialAllocation_le_work (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n
  have h5 := canonicalMulAllocation_le_work (nat 2)
    (logarithmPartialWithWork (divWithWork (subWithWork r one).1 (canonicalAddWithWork r one).1).1 n).1
  unfold logarithmAllocation logarithmWithWork
  dsimp only
  omega

theorem dotListAllocation_le_work {d : ℕ} (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListAllocation left right indices ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => simp only [dotListAllocation, dotListWithWork, Nat.zero_le]
  | cons i rest ih =>
    have hm := canonicalMulAllocation_le_work (left.get i) (right.get i)
    have ha := canonicalAddAllocation_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListAllocation, dotListWithWork]
    omega

theorem gradientCellAllocation_le_work {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    gradientCellAllocation G linear point i ≤ (gradientCellWithWork G linear point i).2 := by
  have h1 := powAllocation_le_work (nat G) 50
  have h2 := invAllocation_le_work (powWithWork (nat G) 50).1
  have h3 := canonicalAddAllocation_le_work (point.get i) (powWithWork (nat G) 50).1.invWithWork.1
  have h4 := logarithmAllocation_le_work
    (canonicalAddWithWork (point.get i) (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)
  have h5 := subAllocation_le_work
    (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one
  have h6 := canonicalAddAllocation_le_work
    (subWithWork (logarithmWithWork (canonicalAddWithWork (point.get i)
      (powWithWork (nat G) 50).1.invWithWork.1).1 (G ^ 60)).1.neg one).1 (linear.get i)
  unfold gradientCellAllocation gradientCellWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWarmupAverage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The warmup mass used in band construction is computed from the gathered
warmup entries by a stored sum and one stored division. -/

namespace EditApproximation
namespace BinaryFraction

def warmupAverageWithWork (values : List BinaryFraction) : BinaryFraction × ℕ :=
  let total := sumListWithWork values
  let result := divWithWork total.1 (nat values.length)
  (result.1, total.2 + result.2 + Nat.size values.length + 2)

@[simp] theorem warmupAverageWithWork_value (values : List BinaryFraction) :
    (warmupAverageWithWork values).1.value = (values.map value).sum / values.length := by
  simp only [warmupAverageWithWork, divWithWork_value, sumListWithWork_value, nat_value]

def warmupAverageWordBudget (n B : ℕ) : ℕ :=
  4 * (bandMassTotalStorageBudget n B + Nat.size n + 2) + 4

def warmupAverageBitBudget (n B : ℕ) : ℕ :=
  storedSumBitBudget n B + 6 * n +
    2100 * (bandMassTotalStorageBudget n B + Nat.size n + 4) ^ 2 + Nat.size n + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReductionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual reduction scratch: comparisons retain their cross-products;
sums retain all dot-product intermediates and the materialized vectors. -/

namespace EditApproximation.BinaryFraction

/-- Two materialized index/value list spines fit the dot loop's per-cell charge. -/
theorem dotListAllocation_with_spines_le_work {d : ℕ}
    (left right : Vector BinaryFraction d) (indices : List (Fin d)) :
    dotListAllocation left right indices + 2 * indices.length ≤ (dotListWithWork left right indices).2 := by
  induction indices with
  | nil => simp only [dotListAllocation, dotListWithWork, List.length_nil]; omega
  | cons i rest ih =>
    have hm := canonicalMulAllocation_le_work (left.get i) (right.get i)
    have ha := canonicalAddAllocation_le_work
      (canonicalMulWithWork (left.get i) (right.get i)).1 (dotListWithWork left right rest).1
    simp only [dotListAllocation, dotListWithWork, List.length_cons]
    omega

theorem bandMassAllocation_le_work {M : ℕ} (mass : Vector BinaryFraction M) :
    bandMassAllocation mass ≤ (bandMassTotalWithWork mass).2 := by
  simpa only [bandMassAllocation, bandMassTotalWithWork, dotWithWork, List.length_finRange] using
    dotListAllocation_with_spines_le_work mass (Vector.replicate M one) (List.finRange M)

theorem minAllocation_le_work (a b : BinaryFraction) :
    minAllocation a b ≤ (minWithWork a b).2 := by
  exact (ltAllocation_le_work a b).trans (Nat.le_add_right _ _)

theorem minimumAllocation_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    minimumAllocation fallback values ≤ (minimumWithWork fallback values).2 := by
  induction values with
  | nil => simp only [minimumAllocation, minimumWithWork, Nat.zero_le]
  | cons head rest ih =>
    have h := minAllocation_le_work head (minimumWithWork fallback rest).1
    simp only [minimumAllocation, minimumWithWork]
    omega

theorem maxAllocation_le_work (a b : BinaryFraction) :
    maxAllocation a b ≤ (maxWithWork a b).2 := by
  exact (ltAllocation_le_work a b).trans (Nat.le_add_right _ _)

theorem maximumAllocation_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    maximumAllocation fallback values ≤ (maximumWithWork fallback values).2 := by
  induction values with
  | nil => simp only [maximumAllocation, maximumWithWork, Nat.zero_le]
  | cons head rest ih =>
    have h := maxAllocation_le_work head (maximumWithWork fallback rest).1
    simp only [maximumAllocation, maximumWithWork]
    omega

theorem sumListAllocation_le_work (values : List BinaryFraction) :
    sumListAllocation values ≤ (sumListWithWork values).2 := by
  have h := dotListAllocation_le_work (Vector.ofFn values.get) (Vector.replicate values.length one)
    (List.finRange values.length)
  unfold sumListAllocation sumListWithWork bandMassTotalWithWork dotWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGeometrySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Endpoint geometry and actual finite score/minimum scans retain
all arithmetic scratch and all callback read invocations. -/

namespace EditApproximation.BinaryFraction



theorem distanceAllocation_le_work (a b : BinaryFraction) :
    distanceAllocation a b ≤ (distanceWithWork a b).2 := by
  have h := subAllocation_le_work a b
  unfold distanceAllocation distanceWithWork
  dsimp only
  omega



theorem connectionTermsAllocation_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionTermsAllocation start states finish ≤ (connectionTermsWithWork start states finish).2 := by
  induction states generalizing start with
  | nil =>
    have h := distanceAllocation_le_work start finish
    unfold connectionTermsAllocation connectionTermsWithWork
    dsimp only
    exact Nat.add_le_add h (by decide : 1 ≤ 2)
  | cons state rest ih =>
    have hc := distanceAllocation_le_work start (nat state.lo)
    have ht := ih (nat state.hi)
    unfold connectionTermsAllocation connectionTermsWithWork
    dsimp only
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hc ht) _) _)
      (by decide : 3 ≤ 6)



theorem connectionAllocation_le_work {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    connectionAllocation start finish states ≤ (connectionWithWork start finish states).2 := by
  have ht := connectionTermsAllocation_le_work start finish states
  have hs := sumListAllocation_le_work (connectionTermsWithWork start states finish).1
  unfold connectionAllocation connectionWithWork
  dsimp only
  omega



theorem endpointDistanceAllocation_le_work {n : ℕ} (q r : TargetInterval n) :
    endpointDistanceAllocation q r ≤ (endpointDistanceWithWork q r).2 := by
  have hl := distanceAllocation_le_work (nat q.lo) (nat r.lo)
  have hr := distanceAllocation_le_work (nat q.hi) (nat r.hi)
  have ha := canonicalAddAllocation_le_work (distanceWithWork (nat q.lo) (nat r.lo)).1
    (distanceWithWork (nat q.hi) (nat r.hi)).1
  unfold endpointDistanceAllocation endpointDistanceWithWork
  dsimp only
  omega



theorem endpointConnectionAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) :
    endpointConnectionAllocation r states ≤ (endpointConnectionWithWork r states).2 := by
  have h := connectionAllocation_le_work (nat r.lo) (nat r.hi) (List.ofFn states)
  unfold endpointConnectionAllocation endpointConnectionWithWork
  dsimp only
  omega



theorem stateGapAllocation_le_work {n : ℕ} (sourceLength : ℕ) (r : TargetInterval n) :
    stateGapAllocation sourceLength r ≤ (stateGapWithWork sourceLength r).2 := by
  have h1 := subAllocation_le_work (nat r.hi) (nat r.lo)
  have h2 := subAllocation_le_work (subWithWork (nat r.hi) (nat r.lo)).1 (nat sourceLength)
  unfold stateGapAllocation stateGapWithWork
  dsimp only
  omega



theorem endpointScoreReadAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (states : Fin M → TargetInterval n)
    (h : ∀ i, footprint i (states i) ≤ (read i (states i)).2) :
    endpointScoreReadAllocation r read footprint states ≤ (endpointScoreReadWithWork r read states).2 := by
  have hw := arithmeticMapAllocation_le_work (fun i => read i (states i))
    (fun i => footprint i (states i)) (List.finRange M) (fun i _ => h i)
  have hc := endpointConnectionAllocation_le_work r states
  let words := (arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)).1
  have hs := sumListAllocation_le_work words
  have ha := canonicalAddAllocation_le_work (endpointConnectionWithWork r states).1 (sumListWithWork words).1
  unfold endpointScoreReadAllocation endpointScoreReadWithWork
  dsimp only
  dsimp only [words] at hs ha
  omega



theorem wideMinimumReadAllocation_le_work {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (h : ∀ action ∈ actions, ∀ i, footprint i (action i) ≤ (read i (action i)).2) :
    wideMinimumReadAllocation r read footprint actions hne ≤ (wideMinimumReadWithWork r read actions hne).2 := by
  have hf := endpointScoreReadAllocation_le_work r read footprint (actions.head hne) (h _ (List.head_mem hne))
  have hs := arithmeticMapAllocation_le_work (endpointScoreReadWithWork r read)
    (endpointScoreReadAllocation r read footprint) actions
    (fun action ha => endpointScoreReadAllocation_le_work r read footprint action (h action ha))
  have hm := minimumAllocation_le_work (endpointScoreReadWithWork r read (actions.head hne)).1
    (arithmeticMapWithWork (endpointScoreReadWithWork r read) actions).1
  unfold wideMinimumReadAllocation wideMinimumReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPrefixSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem prefixReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (j : ℕ) (p : BinaryFraction)
    (h : ∀ i, allocation i (states i) ≤ (read i (states i)).2) :
    prefixReadAllocation parent r states read allocation j p ≤
      (prefixReadWithWork parent r states read j p).2 := by
  let words := (arithmeticMapWithWork (fun i : Fin M =>
    if i.val < j then read i (states i) else (zero, 1)) (List.finRange M)).1
  let finish := (canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p).1
  have hw := arithmeticMapAllocation_le_work
    (fun i : Fin M => if i.val < j then read i (states i) else (zero, 1))
    (fun i : Fin M => if i.val < j then allocation i (states i) else 0) (List.finRange M) (by
      intro i _
      split_ifs
      · exact h i
      · exact Nat.zero_le _)
  have hf := canonicalAddAllocation_le_work (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
  have hc := connectionAllocation_le_work (nat r.lo) finish ((List.ofFn states).take j)
  have hs := sumListAllocation_le_work words
  have ha := canonicalAddAllocation_le_work
    (connectionWithWork (nat r.lo) finish ((List.ofFn states).take j)).1 (sumListWithWork words).1
  unfold prefixReadAllocation prefixReadWithWork
  dsimp only [words, finish] at hc hs ha ⊢
  omega



theorem prefixMinimumReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (j : ℕ) (p : BinaryFraction)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    prefixMinimumReadAllocation parent r actions hne read allocation j p ≤
      (prefixMinimumReadWithWork parent r actions hne read j p).2 := by
  have hf := prefixReadAllocation_le_work parent r (actions.head hne) read allocation j p
    (h _ (List.head_mem hne))
  have hs := arithmeticMapAllocation_le_work
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixReadAllocation parent r action read allocation j p) actions
    (fun action ha => prefixReadAllocation_le_work parent r action read allocation j p (h action ha))
  have hm := minimumAllocation_le_work (prefixReadWithWork parent r (actions.head hne) read j p).1
    (arithmeticMapWithWork (fun action => prefixReadWithWork parent r action read j p) actions).1
  unfold prefixMinimumReadAllocation prefixMinimumReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryContinuationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit costs for the full numerical tail after its finite candidate lists
have been prepared. Both Bellman minima, the online score minimum, and the
final clipped decrement are executed by the counter being bounded. -/

namespace EditApproximation
namespace BinaryFraction

def localContinuationInputBudget (M B : ℕ) : ℕ :=
  B + 2 * bellmanActionWordBudget M B + 1

def localContinuationWordBudget (M B : ℕ) : ℕ :=
  refinementUpdateWordBudget (localContinuationInputBudget M B)

def localContinuationBitBudget (M nw ng no B C : ℕ) : ℕ :=
  bellmanBitBudget M nw B B C +
  bellmanBitBudget M ng B (B + bellmanActionWordBudget M B) C +
  no * (bellmanActionBitBudget M B C + 3) +
  (2 + no * (1000 * (bellmanActionWordBudget M B + 1) ^ 2 + 2)) +
  refinementUpdateBitBudget (localContinuationInputBudget M B) + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite representative list and the actual rounded comparison representative. -/

namespace EditApproximation

def representativeList {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) : List (ℕ × TargetInterval n) :=
  (dyadicScales N).flatMap fun b =>
    ((targetStates n).filter fun r => decide
      (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
        (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b)).map fun r => (b, r)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



def physicalInitialTable {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (state : PhysicalEntry M J target.length) : ℚ :=
  let piece := physicalSource source state.1
  if piece.length ≤ 1 then shortSourceCost piece (substring target state.2.lo state.2.hi)
  else localInitialConeTable piece target (fun q => U (state.1, q)) N P F A a state.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal initial table, representative enumeration and rational warmup of one refinement pass. -/

namespace EditApproximation



def stageInitial {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) :
    PhysicalEntry M J target.length → ℚ :=
  physicalInitialTable source target U N P F A (refinementFactor A F)

def stageRepresentatives {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (node : PhysicalNode M J) : List (ℕ × TargetInterval target.length) :=
  representativeList N P F (refinementFactor A F) (fun q => stageInitial source target U N P F A (node, q))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





structure PhysicalSelections (M J nx ny P : ℕ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval ny)) where
  groups : PhysicalNode M J → PhysicalChildTables M ny → ℕ → List (PhysicalRationalAction M ny)
  online : PhysicalNode M J → PhysicalChildTables M ny → ℕ → TargetInterval ny →
    List (PhysicalRationalAction M ny)
  groups_mem : ∀ node children t action, action ∈ groups node children t →
    action ∈ rationalActualWideActions (physicalSourceInterval nx node) (representatives node) P
  online_mem : ∀ node children t q action, action ∈ online node children t q →
    action ∈ rationalActualWideActions (physicalSourceInterval nx node) (representatives node) P

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalBandChildInitial (i : Fin M) (s : TargetInterval target.length) : ℚ :=
  stageInitial source target U N P F A (physicalChild node hbelow i, s)


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalWideStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One concrete refinement entry, using direct local representative and
cell loops. Band data and previously gathered child tables are arguments;
no complete current-index child table is enumerated. -/

namespace EditApproximation

def rationalLocalWideStep {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) : ℚ :=
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun is => old is.1 is.2) q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
  let cone := rationalMinimum fallback
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (fun is => current is.1 is.2) q))
  rationalRefinementUpdate delta cone
    (rationalOnlineMinimum (online.map
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => current is.1 is.2) q)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPhysicalContinuation
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The local refinement return is computed by the binary-fraction
continuation. Wide actions are built from the emitted endpoint grids, and
their connection charges are evaluated before the two Bellman minima. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem endpointActionWithWork_decode {ny M : ℕ} (center : TargetInterval ny)
    (states : Fin M → TargetInterval ny) :
    (endpointActionWithWork center states).1.decode =
      (⟨center, endpointActionConnection center states, fun i => (i, states i)⟩ :
        PhysicalRationalAction M ny) := by
  simp only [endpointActionWithWork, BinaryBellmanAction.decode, endpointConnectionWithWork_value]



@[simp] theorem wideActionsFromRepresentativesWithWork_decode {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (hP : 0 < P) :
    ((wideActionsFromRepresentativesWithWork M parent representatives P).1.map
      BinaryBellmanAction.decode) = rationalActualWideActions parent representatives P := by
  simp only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value,
    List.map_flatMap, arithmeticMapWithWork_value, List.map_map, Function.comp_def,
    endpointActionWithWork_decode, rationalActualWideActions]
  apply List.flatMap_congr
  intro br _
  rw [← wideActionGridWithWork_value M parent br.2 br.1 P hP, List.map_map]
  rfl

def physicalContinuationWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) : BinaryFraction × ℕ :=
  let wide := wideActionsFromRepresentativesWithWork M parent representatives P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := localContinuationWithWork endpointDistanceWithWork L.1 delta fallback
    old current query wide.1 groups online
  (result.1, wide.2 + L.2 + result.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetup
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal scale list and sample counts, including scales below one.
Dyadic input exponents are carried by the computed parameter construction;
no real logarithm is evaluated by these routines. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem signedPowerTwoWithWork_value (e : ℤ) :
    (signedPowerTwoWithWork e).1.value = (2 : ℚ) ^ e := by
  unfold signedPowerTwoWithWork
  split_ifs with h
  · change (bitWordValue (powerTwoWord e.toNat) : ℚ) / 1 = (2 : ℚ) ^ e
    rw [div_one, powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg h]
  · rw [inversePowerTwo_value, Int.toNat_of_nonneg
      (show 0 ≤ -e from neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))), neg_neg]



@[simp] theorem groupScalesWithWork_value (eM eb eF : ℕ) :
    ((groupScalesWithWork eM eb eF).1.map value) =
      groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF) := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  simp only [groupScalesWithWork, arithmeticMapWithWork_value, List.map_map,
    Function.comp_def, signedPowerTwoWithWork_value, groupDyadicScales, hlower, hupper, hlog, hclog]

/-- Exact versus sampled is decided from the actual binary sample count. -/


@[simp] theorem groupSampleCountWithWork_value (M Q b : ℕ) (h : BinaryFraction) :
    bitWordValue (groupSampleCountWithWork M Q b h).1 = groupSampleCount M Q b h.value := by
  simp only [groupSampleCountWithWork, wordMinWithWork_value, bitWordValue_bits,
    naturalCeilingWithWork_value, divWithWork_value, canonicalMulWithWork_value,
    nat_value, groupSampleCount]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryTriangularChoice
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's sampled iteration is obtained by the exact triangular
block search, with every threshold multiplication and comparison charged. -/

namespace EditApproximation



@[simp] theorem triangularMassWithWork_value (K : ℕ) :
    bitWordValue (triangularMassWithWork K).1 = optimizerTriangularMass K := by
  simp only [triangularMassWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value,
    (binaryNaturalDivModWithWork_spec _ 2 (by decide)).1]
  rw [← optimizerTriangularMass_twice K, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]



@[simp] theorem triangularChoiceWithWork_value (K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    (triangularChoiceWithWork K integer).1 = triangularChoice K integer := by
  induction K with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have ht := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using ht
        let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
        (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
      else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).1 = _
    unfold triangularChoice
    dsimp only
    by_cases hs : integer.val < optimizerTriangularMass K
    · have ht : (binaryNaturalCompareWithWork integer.val
          (bitWordValue (triangularMassWithWork K).1)).1 = .lt := by
        apply (binaryNaturalCompareWithWork_lt _ _).mpr
        simpa only [triangularMassWithWork_value] using hs
      simp only [ht, dite_true, hs, ih]
    · have ht : (binaryNaturalCompareWithWork integer.val
          (bitWordValue (triangularMassWithWork K).1)).1 ≠ .lt := by
        intro ht
        apply hs
        simpa only [triangularMassWithWork_value] using (binaryNaturalCompareWithWork_lt _ _).mp ht
      simp only [ht, dite_false, hs]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite uniform source integer is passed through the actual triangular
search and the actual stored-fraction optimizer. The returned zero-connection
physical action has exactly the online sampler's value, including ties. -/

namespace EditApproximation
namespace BinaryFraction

def sampledOnlineActionWithWork {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M × ℕ :=
  let chosen := triangularChoiceWithWork K integer
  let selected := bandActionWithWork b initial table eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCoordinateAction
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The prepared online action explicitly constructs its coordinate array
and compares stored endpoints when constructing each vertex. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem coordinateVectorWithWork_value {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    (coordinateVectorWithWork band).1 = listedBandCoordinateVector band := by
  unfold coordinateVectorWithWork listedBandCoordinateVector
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, List.get_eq_getElem]
  exact List.getElem_of_eq (bandCoordinatesWithWork_value band) _



def countedPreparedActionWithWork {M n : ℕ} (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → TargetInterval n) × ℕ :=
  let coordinates := coordinateVectorWithWork band
  let vertices := countedBandVerticesWithWork coordinates.1 mass band
  let linear := vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun child => mass.get child) table eta kappa t (coordinates.1.get i)
  let selected := selectionWithWork vertices.1 linear.1 G j
  (selected.1, coordinates.2 + vertices.2 + linear.2 + selected.2 + 3)

def countedBandActionWithWork {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → TargetInterval n) × ℕ :=
  let mass := envelopeVectorWithWork b band initial
  let selected := countedPreparedActionWithWork mass.1 table eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

def countedSampledOnlineWithWork {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M × ℕ :=
  let chosen := triangularChoiceWithWork K integer
  let selected := countedBandActionWithWork b initial table eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal warmup can be calculated by direct bounded endpoint
loops. Equality with the complete tables is only asserted on good seeds;
the local rules themselves remain finite and bounded on every seed. -/

namespace EditApproximation

open Finset

def physicalLocalWarmup {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) : ℕ → PhysicalEntry M J target.length → ℚ
  | 0, state => stageInitial source target U N P F A state
  | t + 1, state =>
    if hbelow : state.1.1.val < J then
      if (physicalSourceInterval source.length state.1).hi -
          (physicalSourceInterval source.length state.1).lo ≤ 1 then
        stageInitial source target U N P F A state
      else rationalBellman (fun q => stageInitial source target U N P F A (state.1, q))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length state.1)
          (localRefinementRepresentatives N P F (refinementFactor A F)
            (fun q => stageInitial source target U N P F A (state.1, q)) state.2) P)
        (fun is => physicalLocalWarmup source target U N P F A t
          (physicalChild state.1 hbelow is.1, is.2)) state.2
    else stageInitial source target U N P F A state

def physicalLocalWarmupMass {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (state : PhysicalEntry M J target.length) : ℚ :=
  (∑ t ∈ Finset.range T, physicalLocalWarmup source target U N P F A t state) / T

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local finite refinement recurrence, with direct query groups and
local warmup data. Current-index dependencies go only to physical children;
the recurrence is well founded before any accuracy assertion. -/

namespace EditApproximation

def physicalLocalChildMass {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J) :
    Fin M → TargetInterval target.length → ℚ :=
  fun i r => physicalLocalWarmupMass source target U N P F A T (physicalChild node hbelow i, r)

def physicalLocalRefinement {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) : ℕ → TargetInterval target.length → ℚ :=
  if hbelow : node.1.val < J then
    if (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 then
      fun _ q => stageInitial source target U N P F A (node, q)
    else
      let children : PhysicalChildTables M target.length := fun i =>
        physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online
          (physicalChild node hbelow i)
      fun t q => match t with
        | 0 => physicalLocalWarmup source target U N P F A T (node, q)
        | s + 1 => rationalLocalWideStep source target (physicalSourceInterval source.length node)
            N P F exponent Q tau (refinementFactor A F) delta
            (fun r => stageInitial source target U N P F A (node, r))
            (physicalLocalChildMass source target U N P F A T node hbelow)
            (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
            (fun i r => children i s r) (fun i r => children i (s + 1) r)
            (draw ⟨node, hbelow⟩ (s + 1)) (online node children (s + 1) q) q
  else fun _ q => stageInitial source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











@[simp] theorem lookup_insert_same (tree : BinaryMemo α) (key : List Bool) (a : α) :
    (tree.insert key a).lookup key = some a := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simpa only [insert, lookup, left, right] using ih _

@[simp] theorem lookup_empty (key : List Bool) : (empty : BinaryMemo α).lookup key = none := by
  induction key with
  | nil => rfl
  | cons b rest ih => cases b <;> exact ih

def nodes : BinaryMemo α → ℕ
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

/-- An instrumented lookup returns exactly the ordinary dictionary
answer, charging one node visit per consumed bit and one terminal visit. -/


theorem lookupCosted_spec (tree : BinaryMemo α) (key : List Bool) :
    tree.lookupCosted key = (tree.lookup key, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [lookupCosted, lookup, ih, List.length_cons]

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
attribute [-instance] _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

/-- Node labels carry remaining physical depth and remaining rank.
Children in the first and second arrays have distinct edge sorts. -/
inductive DependencyExpansion where
  | node (depth rank sameCount earlierCount : ℕ)
      (sameChildren : Fin sameCount → DependencyExpansion)
      (earlierChildren : Fin earlierCount → DependencyExpansion) : DependencyExpansion

namespace DependencyExpansion

def depth : DependencyExpansion → ℕ
  | .node d _ _ _ _ _ => d

def rank : DependencyExpansion → ℕ
  | .node _ k _ _ _ _ => k

/-- Charge every actual node by a function of its remaining physical
depth, as needed for length-dependent initial-state evaluation. -/
def depthWeightedCount (weight : ℕ → ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier => weight d +
      (∑ i, depthWeightedCount weight (same i)) +
      ∑ i, depthWeightedCount weight (earlier i)

end DependencyExpansion
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalDependencyRank
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Concrete table requests and their dependency order. A single table
index identifies the end of warmup with refinement time zero. Copy labels
remain part of a request but do not reset its dependency rank. -/

namespace EditApproximation





namespace PhysicalTableRequest

variable {M J ny : ℕ}











def changeCopy (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    PhysicalTableRequest M J ny := { request with copy := copy }

@[simp] theorem rank_changeCopy (T S : ℕ) (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    rank T S (changeCopy request copy) = rank T S request := rfl

@[simp] theorem remainingDepth_changeCopy (request : PhysicalTableRequest M J ny) (copy : ℕ) :
    remainingDepth (changeCopy request copy) = remainingDepth request := rfl

@[simp] theorem warmup_rank (pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny) :
    rank T S (warmup pass copy node j state) = pass * (T + S + 1) + j := rfl

@[simp] theorem refinement_rank (pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny) :
    rank T S (refinement pass copy node T t state) = pass * (T + S + 1) + (T + t) := rfl

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_cost {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).2 ≤ 1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork]; omega
    | cons value values =>
      have hc := hC query key
      have hi := ih values
      simp only [gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBufferSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Stored key/value words and the actual linear lookup call tree. Reads
return pointers to retained words; only comparison scratch is fresh. -/

namespace EditApproximation.BinaryFraction

theorem gatheredLookupAllocation_le_work {κ : Type*} (equal : κ → κ → Bool × ℕ)
    (allocation : κ → κ → ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (h : ∀ key ∈ keys, allocation query key ≤ (equal query key).2) :
    gatheredLookupAllocation equal allocation keys values query ≤
      (gatheredWordLookupWithWork equal keys values query).2 := by
  induction keys generalizing values with
  | nil => exact Nat.zero_le 1
  | cons key keys ih =>
    cases values with
    | nil => exact Nat.zero_le 1
    | cons value values =>
      have hc := h key List.mem_cons_self
      have ht := ih values (fun k hk => h k (List.mem_cons_of_mem _ hk))
      unfold gatheredLookupAllocation gatheredWordLookupWithWork
      dsimp only
      split_ifs <;> dsimp only
      · exact Nat.add_le_add hc (Nat.zero_le 1)
      · exact (Nat.add_le_add hc ht).trans (Nat.le_succ _)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset

section Physical

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)

def physicalLocalOnline {R : ℕ} [NeZero R]
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    localOnlineCandidates source target (physicalSourceInterval source.length node)
      N P F exponent H tau (refinementFactor A F) eta kappa
      (fun r => stageInitial source target U N P F A (node, r))
      (physicalLocalChildMass source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow)
      children (t - 1) (integer ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q
  else []

end Physical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalParentDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parent random streams in a fixed child environment

Finite parent arrays contain independent uniform optimizer integers and
actual shared-group draws. The projection laws are exact. Their use in the
node bound needs only the individual marginals, so no independence between
an online payoff and a group-failure indicator is asserted there.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

abbrev ParentGroupDraw (M K : ℕ) (count : Fin K → ℕ) :=
  ∀ scale : Fin K, Fin (count scale) → Fin M

abbrev ParentRandomSpace (R O M K : ℕ) (count : Fin K → ℕ) :=
  (Fin R → Fin O) × (Fin R → ParentGroupDraw M K count)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGrid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The whole-cell grids and nearby cell indices are generated by literal
binary quotient, endpoint and bounded-range operations. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem naturalFloorWithWork_value (a : BinaryFraction) :
    bitWordValue (naturalFloorWithWork a).1 = ⌊a.value⌋₊ := by
  cases hs : a.numerator.negative
  · have hdiv := bitDivModWithWork_value a.denominator a.numerator.bits a.denominator_pos
    have hq : bitWordValue (bitDivModWithWork a.denominator a.numerator.bits).1 =
        bitWordValue a.numerator.bits / bitWordValue a.denominator := by
      conv_rhs => rw [hdiv.1]
      rw [Nat.mul_add_div a.denominator_pos, Nat.div_eq_of_lt hdiv.2, Nat.add_zero]
    simpa only [naturalFloorWithWork, hs, Bool.false_eq_true, ↓reduceIte, value,
      SignedBinary.value, signedMagnitude, Int.cast_natCast, Nat.floor_div_eq_div] using hq
  · have hn : a.value ≤ 0 := by
      simp only [value, SignedBinary.value, signedMagnitude, hs, ↓reduceIte,
        Int.cast_neg, Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    simp only [naturalFloorWithWork, hs, ↓reduceIte, bitWordValue]
    exact (Nat.floor_eq_zero.mpr (lt_of_le_of_lt hn (by norm_num))).symm



@[simp] theorem cellCoordinatesWithWork_value (side : BinaryFraction) (p radius : ℕ) :
    (cellCoordinatesWithWork side p radius).1 = localCellCoordinates side.value p radius := by
  simp only [cellCoordinatesWithWork, naturalFloorWithWork_value, divWithWork_value,
    nat_value, saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value,
    localCellCoordinates]



@[simp] theorem targetCellsWithWork_value {n : ℕ} (side : BinaryFraction) (radius : ℕ)
    (q : TargetInterval n) :
    (targetCellsWithWork side radius q).1 = localTargetCells side.value radius q := by
  simp only [targetCellsWithWork, arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    cellCoordinatesWithWork_value, localTargetCells]



@[simp] theorem cellGridPointsWithWork_value (side : BinaryFraction) (g cell : ℕ) :
    (cellGridPointsWithWork side g cell).1 = cellGridPoints side.value g cell := by
  simp only [cellGridPointsWithWork, arithmeticMapWithWork_value, binaryNaturalMulWithWork_value,
    binaryNaturalAddWithWork_value, canonicalMulWithWork_value, divWithWork_value,
    naturalCeilingWithWork_value, nat_value, saturatingSubtractWithWork_value, cellGridPoints,
    Nat.cast_add, Nat.cast_one]



@[simp] theorem cellStatesWithWork_value (n g : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ) :
    (cellStatesWithWork n g side cell).1 = cellTargetStates n g side.value cell := by
  simp only [cellStatesWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    cellGridPointsWithWork_value, makeStateWithWork_value, cellTargetStates]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellCenters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal eligibility scans for the whole-cell representative list. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem centerEligibilityWithWork_value (b F : ℕ) (a initial : BinaryFraction) :
    (centerEligibilityWithWork b F a initial).1 = true ↔
      (b : ℚ) / (4 * a.value) ≤ initial.value ∧ initial.value ≤ 8 * F * b := by
  simp only [centerEligibilityWithWork, Bool.and_eq_true, leWithWork_value,
    divWithWork_value, canonicalMulWithWork_value, nat_value]
  norm_num

def cellCentersWithWork {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) states.1
  (selected.1, spacing.2 + side.2 + states.2 + selected.2 + 3)

@[simp] theorem cellCentersWithWork_value {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ) (hP : 0 < P) :
    (cellCentersWithWork P F b a theta initial cell).1 =
      cellRepresentativeStates n P F b a.value (fun r => (initial r).value) theta.value cell := by
  have htest (r : TargetInterval n) : (centerEligibilityWithWork b F a (initial r)).1 =
      decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧ (initial r).value ≤ 8 * F * b) :=
    Bool.eq_iff_iff.mpr (by simp only [centerEligibilityWithWork_value, decide_eq_true_eq])
  simp only [cellCentersWithWork, filterWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value b P hP, canonicalMulWithWork_value, nat_value,
    htest, cellRepresentativeStates]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSetupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit bit costs of the dyadic-scale and exact sample-count builders.
The generated count determines the finite draw type. -/

namespace EditApproximation
namespace BinaryFraction

def groupScalesBitBudget (eM eb eF : ℕ) : ℕ :=
  (7 + eM + eF) * (eM + eb + eF + 13) +
    Nat.size eM + Nat.size eb + Nat.size eF + 8

def groupSampleCountWordBudget (B : ℕ) : ℕ := 64 * B + 46

def groupSampleCountBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 500 * (64 * B + 45) ^ 2 +
    4 * (65 * B + 46) + 3 * B + 8

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group evaluation reads the exact finite sampler indexed by the count
computed from the stored rational scale. Casting indices below is proof
transport only; the emitted natural count is used by the executed loop. -/

namespace EditApproximation
namespace BinaryFraction

def countedGroupMemberWithWork {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) : BinaryFraction × ℕ :=
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  let heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  let result := groupMemberWithWork scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j))
  (result.1, counts.2 + result.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count used by every sampled scale is at most the actual child
arity. Consequently the complete group counter is bounded from stored
input widths, without assuming estimates on its internal callbacks. -/

namespace EditApproximation
namespace BinaryFraction

def boundedScaleWordBudget (M B : ℕ) : ℕ :=
  4 * (4 * B + 4 + bandMassTotalStorageBudget M B) + 2

def boundedScaleBitBudget (M B : ℕ) : ℕ :=
  groupIndexBitBudget M B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + bandMassTotalStorageBudget M B + 1) ^ 2 + 2 * B + 3

def countedGroupBitBudget (M T B : ℕ) : ℕ :=
  T * (groupSampleCountBitBudget B + 6) +
    groupMemberBitBudget T B (boundedScaleBitBudget M B) (boundedScaleWordBudget M B) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled group continuation uses the executed envelopes, rounded
states, exact finite sample counts, and ordered minimizing scan. Its output
is the same physical action as the group program used by the accuracy proof. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ) (hb : 0 < b)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

def unskippedEstimateWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorWithWork b member.actions initial
  let rounded := roundedBandWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => (current i (rounded.1.get i), 1)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

def chooseBinaryUnskippedWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current scales draw)

def sampledGroupActionWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryDyadicSampledGroups
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The generated binary scale list is reindexed into the finite
draw domain. Only proof transport is used: the accepted draw count is the
same natural computed by `groupSampleCountWithWork`. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem indexedGroupScales_value (raw : List BinaryFraction) (M b : ℕ) (F : ℚ)
    (h : raw.map value = groupDyadicScales M b F)
    (i : Fin (groupDyadicScales M b F).length) :
    (indexedGroupScales raw M b F h i).value = groupDyadicScaleAt M b F i := by
  unfold indexedGroupScales groupDyadicScaleAt
  simp only [List.get_eq_getElem]
  rw [← List.getElem_map value (l := raw) (i := i.val) (h := by rw [h]; exact i.isLt)]
  simp only [h]

section Physical
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
  (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

def dyadicSampledGroupActionWithWork (members : List Member) (hne : members ≠ []) :=
  sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
    (indexedGroupScales raw M b F.value hraw)
    (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
      (indexedGroupScales_value raw M b F.value hraw t)) j)) members hne

end Physical
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGroupKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One complete whole-cell group: enumerate its eligible centers, execute
every band guard, estimate all surviving members with the original finite
draws, and select the same ordered minimum. -/

namespace EditApproximation
namespace BinaryFraction

abbrev cellScaleDraw (M b Q : ℕ) (f : ℚ) :=
  ∀ t : Fin (groupDyadicScales M b f).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → Fin M

def cellReferenceAction {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a f : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (draw : cellScaleDraw M b Q f) : Option (PhysicalRationalAction M target.length) :=
  let members := unskippedBandList source target parent b P exponent tau f child initial
    (cellRepresentativeStates target.length P F b a parentInitial ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
  if h : members = [] then none else some (chooseUnskippedGroup Q current members h draw).rationalAction

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryComputedCellGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell kernel constructs its rational scales from the dyadic
parameter exponents. -/

namespace EditApproximation
namespace BinaryFraction

theorem computedGroupScales_value (M b F eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF) :
    (groupScalesWithWork eM eb eF).1.map value = groupDyadicScales M b (nat F).value := by
  rw [nat_value, hM, hb, hF, Nat.cast_pow, Nat.cast_ofNat]
  exact groupScalesWithWork_value eM eb eF

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupActions
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The complete local group list is obtained by executed scale, cell,
band, and sampled-selection loops. The source keeps the original finite
sample counts and shares its draws between all members of each cell. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem refinementScaleGuardWithWork_value (F b : ℕ) (a w : BinaryFraction) :
    (refinementScaleGuardWithWork F b a w).1 = true ↔
      w.value / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a.value * w.value := by
  simp only [refinementScaleGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value, Nat.cast_ofNat]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRefinementLists
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal local scale and representative lists. Each bounded endpoint
grid is constructed before the center eligibility tests are performed. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryExponentsWithWork_value (N F : ℕ) (a w : BinaryFraction) :
    ((queryExponentsWithWork N F a w).1.map (fun e => 2 ^ e)) =
      dyadicQueryWindow N w.value a.value F := by
  have hscale : (List.range (max 1 N.bits.length)).map (fun e => 2 ^ e) = dyadicScales N := by
    simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value] using
      dyadicScalesWithWork_value N
  have hguard (e : ℕ) : (refinementScaleGuardWithWork F (2 ^ e) a w).1 =
      decide (w.value / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a.value * w.value) :=
    Bool.eq_iff_iff.mpr (by simp only [refinementScaleGuardWithWork_value, decide_eq_true_eq])
  simp only [queryExponentsWithWork, filterWithWork_value, hguard]
  unfold dyadicQueryWindow
  rw [← hscale, List.filter_map]
  rfl

def localRepresentativesWithWork {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n) :
    List (ℕ × TargetInterval n) × ℕ :=
  let scales := queryExponentsWithWork N F a (initial query)
  let radius := naturalCeilingWithWork (initial query)
  let result := arithmeticFlatMapWithWork (fun e =>
    let b := 2 ^ e
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius.1) query.lo query.hi
    let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) points.1
    let labeled := arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
    (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)) scales.1
  (result.1, scales.2 + radius.2 + result.2 + 3)

@[simp] theorem localRepresentativesWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n) :
    (localRepresentativesWithWork N P F a initial query).1 =
      localRefinementRepresentatives N P F a.value (fun r => (initial r).value) query := by
  have hcenter (b : ℕ) (r : TargetInterval n) : (centerEligibilityWithWork b F a (initial r)).1 =
      decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧ (initial r).value ≤ 8 * F * b) :=
    Bool.eq_iff_iff.mpr (by simp only [centerEligibilityWithWork_value, decide_eq_true_eq])
  have hgrid (e : ℕ) : (gridStateBoxWithWork n (seedGridSpacing (2 ^ e) P)
      ⌈(initial query).value⌉₊ query.lo query.hi).1 =
      localTargetStates n (seedGridSpacing (2 ^ e) P) ⌈(initial query).value⌉₊ query := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  unfold localRepresentativesWithWork
  simp only [arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, filterWithWork_value,
    hcenter, naturalCeilingWithWork_value, seedGridSpacingWithWork_value _ _ hP, hgrid]
  change (queryExponentsWithWork N F a (initial query)).1.flatMap
    (fun e => (((localTargetStates n (seedGridSpacing (2 ^ e) P) ⌈(initial query).value⌉₊ query).filter
      (fun r => decide (((2 ^ e : ℕ) : ℚ) / (4 * a.value) ≤ (initial r).value ∧
        (initial r).value ≤ 8 * F * (2 ^ e : ℕ)))).map (fun r => (2 ^ e, r)))) = _
  trans ((queryExponentsWithWork N F a (initial query)).1.map (fun e => 2 ^ e)).flatMap
    (fun b => ((localTargetStates n (seedGridSpacing b P) ⌈(initial query).value⌉₊ query).filter
      (fun r => decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧
        (initial r).value ≤ 8 * F * b))).map (fun r => (b, r)))
  · rw [List.flatMap_map]
  · rw [queryExponentsWithWork_value]
    rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





@[simp] theorem queryIntervalEqualWithWork_value {n : ℕ} (a b : TargetInterval n) :
    (queryIntervalEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryIntervalEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · rintro ⟨hl, hh⟩
    cases a
    cases b
    cases hl
    cases hh
    rfl
  · intro h
    subst b
    exact ⟨rfl, rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryScalesWithWork_value (N F : ℕ) (a value : BinaryFraction) :
    (queryScalesWithWork N F a value).1 = dyadicQueryWindow N value.value a.value F := by
  simp only [queryScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value,
    queryExponentsWithWork_value]



@[simp] theorem queryGroupKeysWithWork_value {n : ℕ} (N F exponent : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryGroupKeysWithWork N F exponent a value q).1 =
      localGroupQueryKeys N F exponent a.value (fun _ => value.value) q := by
  simp only [queryGroupKeysWithWork, arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    queryScalesWithWork_value, targetCellsWithWork_value, naturalCeilingWithWork_value,
    canonicalMulWithWork_value, inversePowerTwo_value, nat_value, localGroupQueryKeys]



@[simp] theorem queryOnlineKeysWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryOnlineKeysWithWork N P F hP a value q).1 =
      localOnlineSourceKeys N P F a.value (fun _ => value.value) q := by
  simp only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, queryScalesWithWork_value,
    roundStateWithWork_value, seedGridSpacingWithWork_value _ _ hP, localOnlineSourceKeys]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSamples
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Group sample coordinates are enumerated from the computed dyadic
scale array and binary sample counts. Equalities used in index casts are
proofs only; the loop bounds are the values just computed. -/

namespace EditApproximation



@[simp] theorem queryFinRange_value (n m : ℕ) (h : n = m) :
    queryFinRange n m h = List.finRange m := by
  subst m
  simp only [queryFinRange, Fin.eta, List.map_id']

namespace BinaryFraction



@[simp] theorem queryScaleAt_value (words : List BinaryFraction) (scales : List ℚ)
    (h : words.map value = scales) (i : Fin scales.length) :
    (queryScaleAt words scales h i).value = scales[i.val] := by
  subst scales
  simp only [queryScaleAt, List.getElem_map]

theorem queryGroupScaleAt_value (M b F : ℕ) (words : List BinaryFraction)
    (h : words.map value = groupDyadicScales M b F)
    (i : Fin (groupDyadicScales M b F).length) :
    (queryScaleAt words (groupDyadicScales M b F) h i).value = groupDyadicScaleAt M b F i :=
  queryScaleAt_value words (groupDyadicScales M b F) h i



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputCodes
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



@[simp] theorem queryChildCodeWithWork_value {M n : ℕ} (input : Fin M × TargetInterval n) :
    (queryChildCodeWithWork input).1 = childInputCode input := by
  simp only [queryChildCodeWithWork, binaryNaturalAddWithWork_value,
    binaryNaturalMulWithWork_value, childInputCode]



@[simp] theorem queryPairWithWork_value (a b : ℕ) :
    (queryPairWithWork a b).1 = Nat.pair a b := by
  unfold queryPairWithWork Nat.pair
  by_cases h : a < b
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt a b).mpr h), ite_eq_left h]
    simp only [binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]
  · rw [ite_eq_right (fun ht => h ((binaryNaturalCompareWithWork_lt a b).mp ht)), ite_eq_right h]
    simp only [binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]



@[simp] theorem queryHistoryCodeWithWork_value {M n : ℕ} (input : Fin M × ℕ × TargetInterval n) :
    (queryHistoryCodeWithWork input).1 = historyInputCode input := by
  simp only [queryHistoryCodeWithWork, queryPairWithWork_value, queryChildCodeWithWork_value,
    historyInputCode]



@[simp] theorem queryHistoryEqualWithWork_value {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    (queryHistoryEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryHistoryEqualWithWork, Bool.and_eq_true, coordinateEqualWithWork_value,
    naturalEqualWithWork_value, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi, hq⟩, ht⟩
    exact Prod.ext hi (Prod.ext ht hq)
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryEnvelopeReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The dyadic child envelope explicitly gathers its initial-value
words before taking the maximum. -/

namespace EditApproximation

theorem vectorMapWithWork_extra {α : Type*} (d : ℕ) (read plain : Fin d → α × ℕ) (C : ℕ)
    (hv : ∀ i, (read i).1 = (plain i).1) (hc : ∀ i, (read i).2 ≤ (plain i).2 + C) :
    (vectorMapWithWork d read).1 = (vectorMapWithWork d plain).1 ∧
    (vectorMapWithWork d read).2 ≤ (vectorMapWithWork d plain).2 + d * C := by
  constructor
  · apply Vector.ext
    intro i hi
    change (vectorMapWithWork d read).1.get ⟨i, hi⟩ = (vectorMapWithWork d plain).1.get ⟨i, hi⟩
    rw [vectorMapWithWork_value, vectorMapWithWork_value]
    exact hv _
  · simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    exact (Nat.add_le_add_right h (6 * d)).trans_eq (Nat.add_right_comm _ _ _)

namespace BinaryFraction



theorem bandEnvelopeReadWithWork_eq {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) :
    (bandEnvelopeReadWithWork b band read i).1 =
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).1 := by
  simp only [bandEnvelopeReadWithWork, bandEnvelopeWithWork, arithmeticMapWithWork_value]

theorem bandEnvelopeReadWithWork_cost {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) (R : ℕ)
    (hr : ∀ action ∈ band, (read i (action i)).2 ≤ R) :
    (bandEnvelopeReadWithWork b band read i).2 ≤
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).2 + band.length * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun action => read i (action i)) band R hr
  simp only [bandEnvelopeReadWithWork, bandEnvelopeWithWork, arithmeticMapWithWork_value]
  omega



theorem envelopeVectorReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval n)) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (R : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) :
    (envelopeVectorReadWithWork b band read).1 =
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).1 ∧
    (envelopeVectorReadWithWork b band read).2 ≤
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).2 + M * (band.length * (R + 3)) := by
  exact vectorMapWithWork_extra M _ _ _
    (bandEnvelopeReadWithWork_eq b band read)
    (fun i => bandEnvelopeReadWithWork_cost b band read i R (fun _ _ => hr i _))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundedReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rounded canonical actions and their acceptance guards retain the
literal initial-table reads used by each child-envelope computation. -/

namespace EditApproximation
namespace BinaryFraction



theorem roundedBandReadWithWork_eq_cost {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (roundedBandReadWithWork exponent b band hne read).1 =
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).1 ∧
    (roundedBandReadWithWork exponent b band hne read).2 ≤
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).2 + M * (band.length * (R + 3)) := by
  have add_cost (a b s t e D : ℕ) (h : a ≤ b + D) :
      a + s + t + e + 3 ≤ b + s + t + e + 3 + D := by omega
  apply vectorMapWithWork_extra
  · intro i
    simp only [bandEnvelopeReadWithWork_eq]
  · intro i
    have h := bandEnvelopeReadWithWork_cost b band read i R (fun _ _ => hr i _)
    dsimp only
    simp only [bandEnvelopeReadWithWork_eq]
    exact add_cost _ _ _ _ _ _ h



theorem unskippedGuardReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (unskippedGuardReadWithWork parent center b exponent F band wide hne read).1 =
      (unskippedGuardWithWork parent center b exponent F band wide hne (fun i q => (read i q).1)).1 ∧
    (unskippedGuardReadWithWork parent center b exponent F band wide hne read).2 ≤
      (unskippedGuardWithWork parent center b exponent F band wide hne (fun i q => (read i q).1)).2 +
        M * (band.length * (R + 3)) + M * (band.length * (R + 3)) := by
  have he := envelopeVectorReadWithWork_eq_cost b band read R hr
  have hrnd := roundedBandReadWithWork_eq_cost exponent b band hne read R hr
  unfold unskippedGuardReadWithWork unskippedGuardWithWork
  dsimp only
  rw [he.1, hrnd.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group estimates and the ordered minimizing scan retain finite-table
lookup costs, using Fin-indexed source arrays. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

def unskippedEstimateReadWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorReadWithWork b member.actions initial
  let rounded := roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

def chooseUnskippedReadWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current scales draw)

end Group
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupActionReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected group action uses the same minimizing member and rounded
endpoints, while charging both the initial and current-table readers. -/

namespace EditApproximation
namespace BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

def sampledGroupActionReadWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseUnskippedReadWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)

end Group

def dyadicSampledGroupActionReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child : Fin M → TargetInterval target.length → BinaryFraction)
    (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
    (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)
    (members : List (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).1.value))) (hne : members ≠ []) :=
  sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
    (indexedGroupScales raw M b F.value hraw)
    (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
      (indexedGroupScales_value raw M b F.value hraw t)) j)) members hne

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedUnskipped
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete band guards construct the actual child endpoint grids before
testing the rounded action. Proof fields carry no runtime cost. -/

namespace EditApproximation
namespace BinaryFraction

theorem prepared_rounded_band_congr {ny M : ℕ} (e b : ℕ)
    {first second : List (Fin M → TargetInterval ny)} (h : first = second)
    (hf : first ≠ []) (hs : second ≠ []) (initial : Fin M → TargetInterval ny → ℚ) :
    canonicalRoundedBandAction e b first hf initial =
      canonicalRoundedBandAction e b second hs initial := by
  subst second
  rfl

def preparedUnskippedCandidateWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction) (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length) :
    Option (UnskippedBand source target parent b P thetaExponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value)) × ℕ :=
  let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo thetaExponent) child
  if hband : band.1 = [] then (none, band.2 + 1) else
    let wide := wideActionGridWithWork M parent center b P
    let guard := unskippedGuardWithWork parent center b thetaExponent F band.1
      (wide.1.map Vector.get) hband initial
    if hguard : guard.1 = true then
      let facts := (unskippedGuardWithWork_value source target parent center b thetaExponent F
        band.1 (wide.1.map Vector.get) hband initial hb).mp hguard
      let hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
          ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (fun i q => (child i q).value) := by
        simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target parent center b P hP
          tau (inversePowerTwo thetaExponent) child
      let hwideValue : wide.1.map Vector.get = wideActionList M parent center b P :=
        wideActionGridWithWork_value M parent center b P hP
      (some {
        center := center
        nonempty := by
          intro hzero
          apply hband
          exact hbandValue.trans hzero
        sum_guard := by
          simpa only [hbandValue] using facts.1
        wide_guard := by
          have hw := facts.2.1
          rw [hwideValue] at hw
          rw [prepared_rounded_band_congr thetaExponent b hbandValue hband _] at hw
          exact hw
        imbalance_guard := by
          simpa only [hbandValue] using facts.2.2 },
        band.2 + wide.2 + guard.2 + wide.1.length + 3)
    else (none, band.2 + wide.2 + guard.2 + wide.1.length + 2)

@[simp] theorem preparedUnskippedCandidateWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction) (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length) :
    (preparedUnskippedCandidateWithWork source target parent b P thetaExponent hb hP tau F child initial center).1 =
      testUnskippedBand source target parent b P thetaExponent tau.value F.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center := by
  let band := representativeBandActions source target parent center b P tau.value
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (fun i q => (child i q).value)
  have hbandValue : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
      tau (inversePowerTwo thetaExponent) child).1 = band := by
    simpa only [inversePowerTwo_value] using
      preparedRepresentativeWithWork_value source target parent center b P hP tau (inversePowerTwo thetaExponent) child
  unfold preparedUnskippedCandidateWithWork testUnskippedBand
  dsimp only
  change _ = (if hband : band = [] then _ else _)
  by_cases hband : band = []
  · have hactual := hbandValue.trans hband
    simp only [dite_eq_left hactual, dite_eq_left hband]
  · have hactual : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo thetaExponent) child).1 ≠ [] := fun h => hband (hbandValue.symm.trans h)
    simp only [dite_eq_right hactual, dite_eq_right hband]
    have hround := prepared_rounded_band_congr thetaExponent b hbandValue hactual hband
      (fun j q => (initial j q).value)
    have hguard := unskippedGuardWithWork_value source target parent center b thetaExponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo thetaExponent) child).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hactual initial hb
    conv_rhs at hguard =>
      rw [wideActionGridWithWork_value M parent center b P hP, hround]
      simp only [hbandValue]
    by_cases hs : (∑ i, bandChildEnvelope b band (fun j q => (initial j q).value) i) ≤ 64 * F.value * b
    · rw [dite_eq_left hs]
      by_cases hw : canonicalRoundedBandAction thetaExponent b band hband
          (fun j q => (initial j q).value) ∈ wideActionList M parent center b P
      · rw [dite_eq_left hw]
        by_cases hg : ∀ i, |rationalStateGap
            (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
            (canonicalRoundedBandAction thetaExponent b band hband (fun j q => (initial j q).value) i)| ≤
              2 * bandChildEnvelope b band (fun j q => (initial j q).value) i
        · rw [dite_eq_left hg, dite_eq_left (hguard.mpr ⟨hs, hw, hg⟩)]
        · rw [dite_eq_right hg, dite_eq_right (fun h => hg (hguard.mp h).2.2)]
      · rw [dite_eq_right hw, dite_eq_right (fun h => hw (hguard.mp h).2.1)]
    · rw [dite_eq_right hs, dite_eq_right (fun h => hs (hguard.mp h).1)]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedCellGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell selection with the prepared-grid band constructor. -/

namespace EditApproximation
namespace BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction)
  (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

def preparedCellGroupWithWork (hP : 0 < P) (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := dyadicSampledGroupActionWithWork source target parent b P exponent Q tau (nat F)
      child initial current raw hraw draw members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem rounded_action_congr {n M : ℕ} (e b : ℕ)
    {first second : List (Fin M → TargetInterval n)} (h : first = second)
    (hf : first ≠ []) (hs : second ≠ []) (initial : Fin M → TargetInterval n → ℚ) :
    canonicalRoundedBandAction e b first hf initial = canonicalRoundedBandAction e b second hs initial := by
  subst second
  rfl

def preparedUnskippedReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    Option (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (read i q).1.value) (fun i q => (initial i q).1.value)) × ℕ :=
  let band := preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) read
  if hband : band.1 = [] then (none, band.2 + 1) else
    let wide := wideActionGridWithWork M parent center b P
    let guard := unskippedGuardReadWithWork parent center b exponent F band.1
      (wide.1.map Vector.get) hband initial
    if hguard : guard.1 = true then
      let hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F band.1
        (wide.1.map Vector.get) hband initial C hi).1
      let facts := (unskippedGuardWithWork_value source target parent center b exponent F
        band.1 (wide.1.map Vector.get) hband (fun i q => (initial i q).1) hb).mp (hg.symm.trans hguard)
      let hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
          ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (read i q).1.value) := by
        apply (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo) b P
          tau (inversePowerTwo exponent) read R hr).1.trans
        simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target
          parent center b P hP tau (inversePowerTwo exponent) (fun i q => (read i q).1)
      let hwideValue : wide.1.map Vector.get = wideActionList M parent center b P :=
        wideActionGridWithWork_value M parent center b P hP
      (some {
        center := center
        nonempty := fun hzero => hband (hbandValue.trans hzero)
        sum_guard := by simpa only [hbandValue] using facts.1
        wide_guard := by
          have hw := facts.2.1
          rw [hwideValue] at hw
          rw [rounded_action_congr exponent b hbandValue hband _] at hw
          exact hw
        imbalance_guard := by simpa only [hbandValue] using facts.2.2 },
        band.2 + wide.2 + guard.2 + wide.1.length + 3)
    else (none, band.2 + wide.2 + guard.2 + wide.1.length + 2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reader-aware whole-cell construction. Every eligibility test reads its
initial word, and every accepted band and selected action uses the counted
reader kernels. -/

namespace EditApproximation

namespace BinaryFraction



section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M)

def preparedCellGroupReadWithWork (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := dyadicSampledGroupActionReadWithWork source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current raw hraw draw members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

end Cell
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every local eligibility test is charged at the bit level, including
its rational divisions and the construction of its two thresholds. -/

namespace EditApproximation
namespace BinaryFraction

def localEligibilityBitBudget (B : ℕ) : ℕ :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalRepresentativeWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete bit work of the query-local scale and center loops. The
one-dimensional grid size follows from the tested scale inequality. -/

namespace EditApproximation
namespace BinaryFraction

def queryExponentsBitBudget (B : ℕ) : ℕ :=
  (B + 1) * (localEligibilityBitBudget (B + 4) + B + 5) + 2 * B + 3

def localRepresentativeScaleBitBudget (P F B : ℕ) : ℕ :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gridStateBoxBitBudget L C +
    L ^ 2 * (localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6

def localRepresentativesBitBudget (P F B : ℕ) : ℕ :=
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (localRepresentativeScaleBitBudget P F B + (64 * F * P + 2) ^ 2 + 3) + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Query-local representative construction reads its finite initial
table explicitly. Each center lookup is charged before testing it. -/

namespace EditApproximation
namespace BinaryFraction

def representativeScalePlainWithWork {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (radius : List Bool)
    (query : TargetInterval n) (e : ℕ) : List (ℕ × TargetInterval n) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius) query.lo query.hi
  let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) points.1
  let labeled := arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
  (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The earlier-history cover is materialized from its small coordinate
lists, then sorted by the original history encoding. It never enumerates
the much larger Cartesian set of complete wide actions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawHistoryInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P history : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1 =
      representatives.flatMap (fun br => (List.finRange M).flatMap fun i =>
        (List.range history).flatMap fun t =>
          (wideChildStateList parent br.2 br.1 P i).map fun r => (i, t, r)) := by
  simp only [queryRawHistoryInputsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedGeometry
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean endpoint enumeration for the whole-cell shared-read cover.
The inner interval is centered at each computed left endpoint plus the
child length, exactly as in the published query's gap guard. -/

namespace EditApproximation



@[simp] theorem queryGapStatesWithWork_value (n g anchor radius sourceLength gapRadius : ℕ)
    (hg : 0 < g) :
    (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).1 =
      gridGapStates n g anchor radius sourceLength gapRadius := by
  simp only [queryGapStatesWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value, gridPointsWithWork_value _ _ _ hg,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, gridGapStates]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



@[simp] theorem queryGroupKeyEqualWithWork_value {M F Q : ℕ} (a b : GroupScalarKey M F Q) :
    (queryGroupKeyEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryGroupKeyEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · rcases a with ⟨⟨a, c, d⟩, s, i⟩
    rcases b with ⟨⟨b, e, f⟩, t, j⟩
    rintro ⟨⟨⟨⟨hab, hce⟩, hdf⟩, hst⟩, hij⟩
    dsimp only at hab hce hdf hst hij
    cases hab
    cases hce
    cases hdf
    have hs : s = t := Fin.ext hst
    cases hs
    have hi : i = j := Fin.ext hij
    cases hi
    rfl
  · intro h
    subst b
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩



@[simp] theorem queryOnlineKeyEqualWithWork_value {n : ℕ} (a b : ℕ × TargetInterval n) :
    (queryOnlineKeyEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryOnlineKeyEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value,
    queryIntervalEqualWithWork_value, Prod.ext_iff]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction

theorem queryChildReadWithWork_cost {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryChildReadWithWork keys values i q).2 ≤ 1 + keys.length * (24 * B + 9) := by
  exact gatheredWordLookupWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn) keys values (i, q)



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBufferSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Materializing the two natural-word encodings fits the comparison loop. -/
theorem bitCompareWithWork_input_cells (left right : List Bool) :
    left.length + right.length ≤ (bitCompareWithWork left right).2 := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => decide
    | cons bit rest ih =>
      simp only [bitCompareNilLeftWithWork, List.length_nil, List.length_cons] at *
      omega
  | cons bit rest ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [bitCompareWithWork, List.length_nil, List.length_cons] at *
      omega
    | cons bit' rest' =>
      have h := ih rest'
      simp only [bitCompareWithWork, List.length_cons] at *
      omega



theorem naturalEqualAllocation_le_work (a b : ℕ) :
    naturalEqualAllocation a b ≤ (naturalEqualWithWork a b).2 :=
  Nat.add_le_add_right (bitCompareWithWork_input_cells a.bits b.bits) 1



theorem coordinateEqualAllocation_le_work {M n : ℕ} (a b : Fin M × TargetInterval n) :
    coordinateEqualAllocation a b ≤ (coordinateEqualWithWork a b).2 := by
  have hi := naturalEqualAllocation_le_work a.1.val b.1.val
  have hl := naturalEqualAllocation_le_work a.2.lo b.2.lo
  have hh := naturalEqualAllocation_le_work a.2.hi b.2.hi
  unfold coordinateEqualAllocation coordinateEqualWithWork
  dsimp only
  omega



theorem queryHistoryEqualAllocation_le_work {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    queryHistoryEqualAllocation a b ≤ (queryHistoryEqualWithWork a b).2 := by
  have hc := coordinateEqualAllocation_le_work (a.1, a.2.2) (b.1, b.2.2)
  have ht := naturalEqualAllocation_le_work a.2.1 b.2.1
  unfold queryHistoryEqualAllocation queryHistoryEqualWithWork
  dsimp only
  omega



theorem queryIntervalEqualAllocation_le_work {n : ℕ} (a b : TargetInterval n) :
    queryIntervalEqualAllocation a b ≤ (queryIntervalEqualWithWork a b).2 := by
  have hl := naturalEqualAllocation_le_work a.lo b.lo
  have hh := naturalEqualAllocation_le_work a.hi b.hi
  unfold queryIntervalEqualAllocation queryIntervalEqualWithWork
  dsimp only
  omega



theorem queryOnlineKeyEqualAllocation_le_work {n : ℕ} (a b : ℕ × TargetInterval n) :
    queryOnlineKeyEqualAllocation a b ≤ (queryOnlineKeyEqualWithWork a b).2 := by
  have hs := naturalEqualAllocation_le_work a.1 b.1
  have hi := queryIntervalEqualAllocation_le_work a.2 b.2
  unfold queryOnlineKeyEqualAllocation queryOnlineKeyEqualWithWork
  dsimp only
  omega



theorem queryGroupKeyEqualAllocation_le_work {M F Q : ℕ} (a b : GroupScalarKey M F Q) :
    queryGroupKeyEqualAllocation a b ≤ (queryGroupKeyEqualWithWork a b).2 := by
  have h1 := naturalEqualAllocation_le_work a.1.1 b.1.1
  have h2 := naturalEqualAllocation_le_work a.1.2.1 b.1.2.1
  have h3 := naturalEqualAllocation_le_work a.1.2.2 b.1.2.2
  have h4 := naturalEqualAllocation_le_work a.2.1.val b.2.1.val
  have h5 := naturalEqualAllocation_le_work a.2.2.val b.2.2.val
  unfold queryGroupKeyEqualAllocation queryGroupKeyEqualWithWork
  dsimp only
  omega

namespace BinaryFraction



theorem queryChildReadAllocation_le_work {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n) :
    queryChildReadAllocation keys values i q ≤ (queryChildReadWithWork keys values i q).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun key _ => coordinateEqualAllocation_le_work _ key)



theorem queryHistoryReadAllocation_le_work {M n : ℕ} (keys : List (Fin M × ℕ × TargetInterval n))
    (values : List BinaryFraction) (s : ℕ) (input : Fin M × TargetInterval n) :
    queryHistoryReadAllocation keys values s input ≤ (queryHistoryReadWithWork keys values s input).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun key _ => queryHistoryEqualAllocation_le_work _ key)



theorem naturalFloorAllocation_le_work (a : BinaryFraction) :
    naturalFloorAllocation a ≤ (naturalFloorWithWork a).2 := by
  have h := bitDivModAllocation_le_work a.denominator a.numerator.bits
  unfold naturalFloorAllocation naturalFloorWithWork
  split_ifs <;> dsimp only <;> omega



theorem queryOnlineIntegerReadAllocation_le_work {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    queryOnlineIntegerReadAllocation keys values b q ≤ (queryOnlineIntegerReadWithWork keys values b q).2 := by
  have hl := gatheredLookupAllocation_le_work queryOnlineKeyEqualWithWork queryOnlineKeyEqualAllocation
    keys values (b, q) (fun key _ => queryOnlineKeyEqualAllocation_le_work _ key)
  have hf := naturalFloorAllocation_le_work (gatheredWordLookupWithWork queryOnlineKeyEqualWithWork keys values (b, q)).1
  unfold queryOnlineIntegerReadAllocation queryOnlineIntegerReadWithWork
  dsimp only
  omega



theorem queryGroupDrawReadAllocation_le_work {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) :
    queryGroupDrawReadAllocation keys values b cell scale sample ≤
      (queryGroupDrawReadWithWork keys values b cell scale sample).2 := by
  let key : GroupScalarKey M F Q := ⟨(b, cell), scale, sample⟩
  have hl := gatheredLookupAllocation_le_work queryGroupKeyEqualWithWork queryGroupKeyEqualAllocation
    keys values key (fun key' _ => queryGroupKeyEqualAllocation_le_work key key')
  have hf := naturalFloorAllocation_le_work (gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values key).1
  have hd := bitDivModAllocation_le_work M.bits
    (bitWordValue (naturalFloorWithWork (gatheredWordLookupWithWork queryGroupKeyEqualWithWork keys values key).1).1).bits
  unfold queryGroupDrawReadAllocation queryGroupDrawReadWithWork binaryNaturalDivModWithWork
  dsimp only [key] at hl hf hd ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCoordinateSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The spare loop charge also covers the input index-list spine. -/
theorem arithmeticMapAllocation_with_spine {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α) (h : ∀ a ∈ values, allocation a ≤ (f a).2) :
    arithmeticMapAllocation allocation values + values.length ≤ (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork, List.length_cons]
    omega



theorem memberByAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (a : α) (values : List α)
    (h : ∀ b ∈ values, allocation a b ≤ (equal a b).2) :
    memberByAllocation allocation a values ≤ (memberByWithWork equal a values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have hb := h b List.mem_cons_self
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [memberByAllocation, memberByWithWork]
    omega



theorem dedupByAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (values : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    dedupByAllocation equal allocation values ≤ (dedupByWithWork equal values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have hm := memberByAllocation_le_work equal allocation a rest (fun b _ => h a b)
    simp only [dedupByAllocation, dedupByWithWork]
    split_ifs <;> omega

namespace BinaryFraction



theorem bandCoordinatesAllocation_le_work {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    bandCoordinatesAllocation band ≤ (bandCoordinatesWithWork band).2 := by
  let build := fun action : Fin M → TargetInterval n =>
    arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)
  have hr := arithmeticFlatMapAllocation_le_work build
    (fun _ => arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) band (by
      intro action _
      simpa only [List.length_finRange] using arithmeticMapAllocation_with_spine
        (fun i : Fin M => ((i, action i), 1)) (fun _ => 1) (List.finRange M) (fun _ _ => le_rfl))
  have hd := dedupByAllocation_le_work coordinateEqualWithWork coordinateEqualAllocation
    (arithmeticFlatMapWithWork build band).1 coordinateEqualAllocation_le_work
  unfold bandCoordinatesAllocation bandCoordinatesWithWork
  dsimp only [build] at hr hd ⊢
  omega



theorem coordinateVectorAllocation_le_work {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    coordinateVectorAllocation band ≤ (coordinateVectorWithWork band).2 := by
  have h := bandCoordinatesAllocation_le_work band
  unfold coordinateVectorAllocation coordinateVectorWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGridSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem binaryNaturalAddAllocation_le_work (a b : ℕ) :
    binaryNaturalAddAllocation a b ≤ (binaryNaturalAddWithWork a b).2 := bitAddAllocation_le_work _ _ _



theorem binaryNaturalMulAllocation_le_work (a b : ℕ) :
    binaryNaturalMulAllocation a b ≤ (binaryNaturalMulWithWork a b).2 := bitMulAllocation_le_work _ _



theorem binaryNaturalDivAllocation_le_work (a b : ℕ) :
    binaryNaturalDivAllocation a b ≤ (binaryNaturalDivModWithWork a b).2.2 := bitDivModAllocation_le_work _ _



theorem naturalWordLEAllocation_le_work (a b : List Bool) :
    naturalWordLEAllocation a b ≤ (wordLEWithWork a b).2 := by
  have h := bitCompareWithWork_input_cells b a
  change a.length + b.length + 1 ≤ (bitCompareWithWork b a).2 + 1
  omega



theorem saturatingSubtractAllocation_le_work (a b : ℕ) :
    saturatingSubtractAllocation a b ≤ (saturatingSubtractWithWork a b).2 := by
  have hc := bitCompareWithWork_input_cells a.bits b.bits
  have hs := bitSubtractAllocation_le_work a.bits b.bits false
  unfold saturatingSubtractAllocation saturatingSubtractWithWork binaryNaturalCompareWithWork binaryNaturalSubtractWithWork
  dsimp only
  split_ifs <;> omega



theorem gridPointsAllocation_le_work (g lo hi : ℕ) :
    gridPointsAllocation g lo hi ≤ (gridPointsWithWork g lo hi).2 := by
  let lower := (bitCeilDivWithWork g.bits lo.bits).1
  let upper := (binaryNaturalDivModWithWork hi g).1
  let stop := (binaryNaturalAddWithWork (bitWordValue upper) 1).1
  let count := (saturatingSubtractWithWork (bitWordValue stop) (bitWordValue lower)).1
  let indices := List.range' (bitWordValue lower) (bitWordValue count)
  have hl := bitCeilDivAllocation_le_work g.bits lo.bits
  have hu := binaryNaturalDivAllocation_le_work hi g
  have hs := binaryNaturalAddAllocation_le_work (bitWordValue upper) 1
  have hc := saturatingSubtractAllocation_le_work (bitWordValue stop) (bitWordValue lower)
  have hm := arithmeticMapAllocation_with_spine
    (fun i => (bitWordValue (binaryNaturalMulWithWork g i).1, (binaryNaturalMulWithWork g i).2 + Nat.size i + 2))
    (fun i => binaryNaturalMulAllocation g i) indices
    (fun i _ => (binaryNaturalMulAllocation_le_work g i).trans (by omega))
  unfold gridPointsAllocation gridPointsWithWork
  dsimp only [lower, upper, stop, count, indices] at hl hu hs hc hm ⊢
  omega



theorem makeStateAllocation_le_work (n lo hi : ℕ) :
    makeStateAllocation n lo hi ≤ (makeStateWithWork n lo hi).2 := by
  have hl := naturalWordLEAllocation_le_work lo.bits hi.bits
  have hh := naturalWordLEAllocation_le_work hi.bits n.bits
  unfold makeStateAllocation makeStateWithWork
  dsimp only
  split_ifs <;> omega



theorem gridStateBoxAllocation_le_work (n g radius lo hi : ℕ) :
    gridStateBoxAllocation n g radius lo hi ≤ (gridStateBoxWithWork n g radius lo hi).2 := by
  let leftLow := (saturatingSubtractWithWork lo radius).1
  let leftHigh := (binaryNaturalAddWithWork lo radius).1
  let rightLow := (saturatingSubtractWithWork hi radius).1
  let rightHigh := (binaryNaturalAddWithWork hi radius).1
  let left := (gridPointsWithWork g (bitWordValue leftLow) (bitWordValue leftHigh)).1
  let right := (gridPointsWithWork g (bitWordValue rightLow) (bitWordValue rightHigh)).1
  have h1 := saturatingSubtractAllocation_le_work lo radius
  have h2 := binaryNaturalAddAllocation_le_work lo radius
  have h3 := saturatingSubtractAllocation_le_work hi radius
  have h4 := binaryNaturalAddAllocation_le_work hi radius
  have h5 := gridPointsAllocation_le_work g (bitWordValue leftLow) (bitWordValue leftHigh)
  have h6 := gridPointsAllocation_le_work g (bitWordValue rightLow) (bitWordValue rightHigh)
  have hf := arithmeticFlatMapAllocation_le_work
    (fun s => filterMapWithWork (makeStateWithWork n s) right)
    (fun s => filterMapAllocation (makeStateWithWork n s) (makeStateAllocation n s) right) left
    (fun s _ => filterMapAllocation_le_work (makeStateWithWork n s) (makeStateAllocation n s) right
      (fun k _ => makeStateAllocation_le_work n s k))
  unfold gridStateBoxAllocation gridStateBoxWithWork
  dsimp only [leftLow, leftHigh, rightLow, rightHigh, left, right] at h5 h6 hf ⊢
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOptimizerSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fresh list cells and primitive call frames of the materialized Boolean
optimizer. Intermediate vectors may all remain live; the counters include
every optimizer iteration and every candidate score. -/

namespace EditApproximation



theorem vectorMapAllocation_le_work {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (allocation : Fin d → ℕ) (h : ∀ i, allocation i ≤ (f i).2) :
    vectorMapAllocation d allocation ≤ (vectorMapWithWork d f).2 := by
  have hs := Finset.sum_le_sum (fun (i : Fin d) (_ : i ∈ Finset.univ) => h i)
  have he : ((Vector.ofFn f).map Prod.snd).toList.sum = ∑ i : Fin d, (f i).2 := by
    simp only [Vector.toList_map, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
      List.sum_ofFn]
  unfold vectorMapAllocation vectorMapWithWork
  dsimp only
  rw [he]
  omega

namespace BinaryFraction



theorem gradientAllocation_le_work {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    gradientAllocation G linear point ≤ (gradientWithWork G linear point).2 :=
  vectorMapAllocation_le_work d _ _ (gradientCellAllocation_le_work G linear point)

theorem scoredArgmaxAllocation_le_work {α : Type*} (score : α → BinaryFraction × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ a ∈ xs, allocation a ≤ (score a).2) :
    scoredArgmaxAllocation score allocation xs ≤ (scoredArgmaxWithWork score xs).2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [scoredArgmaxAllocation, scoredArgmaxWithWork]
    cases he : (scoredArgmaxWithWork score xs).1 with
    | none => dsimp only; omega
    | some best =>
      have hc := ltAllocation_le_work (score a).1 best.2
      change scoredArgmaxAllocation score allocation xs + allocation a +
        (ltAllocation (score a).1 best.2 + 1) ≤
          (scoredArgmaxWithWork score xs).2 + (score a).2 +
            ((score a).1.ltWithWork best.2).2 + 2
      omega

theorem maximizerAllocation_le_work {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    maximizerAllocation gradient vertices ≤ (maximizerWithWork gradient vertices).2 := by
  have h := scoredArgmaxAllocation_le_work (dotWithWork gradient)
    (fun v => dotListAllocation gradient v (List.finRange d)) vertices
    (fun v _ => dotListAllocation_le_work gradient v (List.finRange d))
  unfold maximizerAllocation maximizerWithWork
  dsimp only
  omega

theorem optimizerUpdateAllocation_le_work {d : ℕ} (j : ℕ) (previous selected : Vector BinaryFraction d) :
    optimizerUpdateAllocation j previous selected ≤ (optimizerUpdateWithWork j previous selected).2 := by
  have h1 := divAllocation_le_work (nat 2) (nat (j + 2))
  have h2 := subAllocation_le_work one (divWithWork (nat 2) (nat (j + 2))).1
  have h3 := vectorMapAllocation_le_work d
    (fun i =>
      let first := canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
      let second := canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
      let total := canonicalAddWithWork first.1 second.1
      (total.1, first.2 + second.2 + total.2 + 4))
    (optimizerUpdateCellAllocation (divWithWork (nat 2) (nat (j + 2))).1
      (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 previous selected) (by
        intro i
        have hm1 := canonicalMulAllocation_le_work (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
        have hm2 := canonicalMulAllocation_le_work (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
        have ha := canonicalAddAllocation_le_work
          (canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)).1
          (canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)).1
        unfold optimizerUpdateCellAllocation
        dsimp only
        omega)
  unfold optimizerUpdateAllocation optimizerUpdateWithWork
  dsimp only at h3 ⊢
  omega

theorem optimizerAllocation_le_work {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    optimizerAllocation vertices linear G K ≤ (finiteOptimizerWithWork vertices linear G K).2 := by
  induction K with
  | zero => exact Nat.le_succ _
  | succ K ih =>
    have hg := gradientAllocation_le_work G linear (finiteOptimizerWithWork vertices linear G K).1
    have hm := maximizerAllocation_le_work (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    have hu := optimizerUpdateAllocation_le_work K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1
    simp only [optimizerAllocation, finiteOptimizerWithWork]
    exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ih hg) hm) hu).trans
      (Nat.le_add_right _ 3)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem balancedCutAllocation_le_work (lo width M i : ℕ) :
    balancedCutAllocation lo width M i ≤ (balancedCutWithWork lo width M i).2 := by
  have hm := binaryNaturalMulAllocation_le_work i width
  have hd := binaryNaturalDivAllocation_le_work (bitWordValue (binaryNaturalMulWithWork i width).1) M
  have ha := binaryNaturalAddAllocation_le_work lo
    (bitWordValue (binaryNaturalDivModWithWork (bitWordValue (binaryNaturalMulWithWork i width).1) M).1)
  unfold balancedCutAllocation balancedCutWithWork
  dsimp only
  omega



theorem sourceChildAllocation_le_work {n M : ℕ} (parent : TargetInterval n) (i : Fin M) :
    sourceChildAllocation parent i ≤ (sourceChildWithWork parent i).2 := by
  have hw := saturatingSubtractAllocation_le_work parent.hi parent.lo
  have hn := binaryNaturalAddAllocation_le_work i.val 1
  have hl := balancedCutAllocation_le_work parent.lo
    (bitWordValue (saturatingSubtractWithWork parent.hi parent.lo).1) M i.val
  have hr := balancedCutAllocation_le_work parent.lo
    (bitWordValue (saturatingSubtractWithWork parent.hi parent.lo).1) M
    (bitWordValue (binaryNaturalAddWithWork i.val 1).1)
  unfold sourceChildAllocation sourceChildWithWork
  dsimp only
  omega



theorem seedGridSpacingAllocation_le_work (b P : ℕ) :
    seedGridSpacingAllocation b P ≤ (seedGridSpacingWithWork b P).2 := by
  have hd := binaryNaturalDivAllocation_le_work b P
  have hl := naturalWordLEAllocation_le_work (binaryNaturalDivModWithWork b P).1 [true]
  unfold seedGridSpacingAllocation seedGridSpacingWithWork
  dsimp only
  omega



theorem wideChildGridAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (i : Fin M) :
    wideChildGridAllocation parent r b P i ≤ (wideChildGridWithWork parent r b P i).2 := by
  let child := (sourceChildWithWork parent i).1
  let spacing := (seedGridSpacingWithWork b P).1
  let radius := (binaryNaturalMulWithWork 10 b).1
  let leftOffset := (saturatingSubtractWithWork child.lo parent.lo).1
  let rightOffset := (saturatingSubtractWithWork child.hi parent.lo).1
  let left := (binaryNaturalAddWithWork r.lo (bitWordValue leftOffset)).1
  let right := (binaryNaturalAddWithWork r.lo (bitWordValue rightOffset)).1
  have h1 := sourceChildAllocation_le_work parent i
  have h2 := seedGridSpacingAllocation_le_work b P
  have h3 := binaryNaturalMulAllocation_le_work 10 b
  have h4 := saturatingSubtractAllocation_le_work child.lo parent.lo
  have h5 := saturatingSubtractAllocation_le_work child.hi parent.lo
  have h6 := binaryNaturalAddAllocation_le_work r.lo (bitWordValue leftOffset)
  have h7 := binaryNaturalAddAllocation_le_work r.lo (bitWordValue rightOffset)
  have h8 := gridStateBoxAllocation_le_work ny (bitWordValue spacing) (bitWordValue radius)
    (bitWordValue left) (bitWordValue right)
  unfold wideChildGridAllocation wideChildGridWithWork
  dsimp only [child, spacing, radius, leftOffset, rightOffset, left, right] at h4 h5 h6 h7 h8 ⊢
  omega

/-- Allocations of every prefix Cartesian product, including the actual
output vector cells and the nested map/concatenation spines. -/


theorem materializedAssignmentsAllocation_le_work {α : Type*} (M : ℕ) (choices : Fin M → List α) :
    materializedAssignmentsAllocation M choices ≤ (materializedAssignmentsWithWork M choices).2 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    let previous := (materializedAssignmentsWithWork M (fun i => choices i.succ)).1
    let build := fun head => arithmeticMapWithWork (fun tail : Vector α M =>
      (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous
    have hp := ih (fun i => choices i.succ)
    have hm := arithmeticFlatMapAllocation_le_work build
      (fun _ => arithmeticMapAllocation (fun _ : Vector α M => M + 1) previous) (choices 0) (by
        intro head _
        exact arithmeticMapAllocation_le_work _ _ previous (fun _ _ => by dsimp only; omega))
    change materializedAssignmentsAllocation M (fun i => choices i.succ) +
      arithmeticFlatMapAllocation build
        (fun _ => arithmeticMapAllocation (fun _ : Vector α M => M + 1) previous) (choices 0) ≤
      (materializedAssignmentsWithWork M (fun i => choices i.succ)).2 +
        (arithmeticFlatMapWithWork build (choices 0)).2 + 1
    omega



theorem wideActionGridAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) :
    wideActionGridAllocation M parent r b P ≤ (wideActionGridWithWork M parent r b P).2 := by
  have hc := vectorMapAllocation_le_work M (wideChildGridWithWork parent r b P)
    (wideChildGridAllocation parent r b P) (wideChildGridAllocation_le_work parent r b P)
  have hp := materializedAssignmentsAllocation_le_work M
    (vectorMapWithWork M (wideChildGridWithWork parent r b P)).1.get
  unfold wideActionGridAllocation wideActionGridWithWork
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGuardSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- List traversal, including the input index spine when it is freshly generated. -/


theorem allAllocation_le_work {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    allAllocation allocation xs ≤ (allWithWork test xs).2 := by
  induction xs with
  | nil => simp only [allAllocation, allWithWork, Nat.zero_le]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold allAllocation allWithWork
    dsimp only
    exact Nat.add_le_add (Nat.add_le_add hh ht) (by decide : 1 ≤ 3)

theorem allAllocation_with_spine {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    allAllocation allocation xs + xs.length ≤ (allWithWork test xs).2 := by
  have costBound (a a' b b' l : ℕ) (ha : a ≤ a') (hb : b + l ≤ b') :
      a + b + 1 + (l + 1) ≤ a' + b' + 3 := by
    omega
  induction xs with
  | nil => simp only [allAllocation, allWithWork, List.length_nil, Nat.zero_add, Nat.zero_le]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold allAllocation allWithWork
    dsimp only
    simp only [List.length_cons]
    exact costBound _ _ _ _ _ hh ht



theorem zeroConnectionAllocation_le_work {n : ℕ} (start finish : ℕ) (states : List (TargetInterval n)) :
    zeroConnectionAllocation start states finish ≤ (zeroConnectionWithWork start states finish).2 := by
  induction states generalizing start with
  | nil => exact naturalEqualAllocation_le_work start finish
  | cons state rest ih =>
    have hh := naturalEqualAllocation_le_work start state.lo
    have ht := ih state.hi
    unfold zeroConnectionAllocation zeroConnectionWithWork
    dsimp only
    exact Nat.add_le_add_right (Nat.add_le_add hh ht) 1



theorem translatedEndpointAllocation_le_work (reference root endpoint : ℕ) :
    translatedEndpointAllocation reference root endpoint ≤ (translatedEndpointWithWork reference root endpoint).2 := by
  have hs := bitSubtractAllocation_le_work endpoint.bits root.bits false
  have ha := binaryNaturalAddAllocation_le_work reference (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1)
  unfold translatedEndpointAllocation translatedEndpointWithWork binaryNaturalSubtractWithWork
  dsimp only [binaryNaturalSubtractWithWork] at ha ⊢
  omega

namespace BinaryFraction



theorem leAllocation_le_work (a b : BinaryFraction) :
    leAllocation a b ≤ (leWithWork a b).2 := by
  have h := ltAllocation_le_work b a
  unfold leAllocation leWithWork
  dsimp only
  omega



theorem naturalDistanceLeAllocation_le_work (a b radius : ℕ) :
    naturalDistanceLeAllocation a b radius ≤ (naturalDistanceLeWithWork a b radius).2 := by
  have hd := distanceAllocation_le_work (nat a) (nat b)
  have hl := leAllocation_le_work (distanceWithWork (nat a) (nat b)).1 (nat radius)
  unfold naturalDistanceLeAllocation naturalDistanceLeWithWork
  dsimp only
  omega



theorem affineErrorAllocation_le_work (position offset velocity prediction tolerance : BinaryFraction) :
    affineErrorAllocation position offset velocity prediction tolerance ≤
      (affineErrorWithWork position offset velocity prediction tolerance).2 := by
  have hd := subAllocation_le_work position offset
  have hp := canonicalMulAllocation_le_work velocity prediction
  have he := subAllocation_le_work (subWithWork position offset).1 (canonicalMulWithWork velocity prediction).1
  have hl := leAllocation_le_work
    (subWithWork (subWithWork position offset).1 (canonicalMulWithWork velocity prediction).1).1.absolute tolerance
  unfold affineErrorAllocation affineErrorWithWork
  dsimp only
  omega



theorem bandToleranceAllocation_le_work (tau theta : BinaryFraction) (b M : ℕ) :
    bandToleranceAllocation tau theta b M ≤ (bandToleranceWithWork tau theta b M).2 := by
  have hp := canonicalMulAllocation_le_work tau theta
  have hs := canonicalMulAllocation_le_work (canonicalMulWithWork tau theta).1 (nat b)
  have hd := divAllocation_le_work (canonicalMulWithWork (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M)
  unfold bandToleranceAllocation bandToleranceWithWork
  dsimp only
  omega



theorem cutGuardReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    cutGuardReadAllocation parent r actions hne read allocation states velocity tolerance j ≤
      (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 := by
  have hs := subAllocation_le_work (nat (states j).lo) (nat (sourceChild parent j).lo)
  have ho := subAllocation_le_work (nat r.lo) (nat parent.lo)
  have hp := prefixMinimumReadAllocation_le_work parent r actions hne read allocation j.val
    (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 h
  have he := affineErrorAllocation_le_work
    (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1
    (subWithWork (nat r.lo) (nat parent.lo)).1 velocity
    (prefixMinimumReadWithWork parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1).1 tolerance
  unfold cutGuardReadAllocation cutGuardReadWithWork
  split_ifs <;> dsimp only
  · exact Nat.zero_le _
  · have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs ho) hp) he
    exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hsum _) _) _) _).trans (Nat.le_add_right _ 5)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem anchorGuardAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (b : ℕ) (states : Fin M → TargetInterval ny) (i : Fin M) :
    anchorGuardAllocation parent r b states i ≤
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).2 +
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).2 +
      (binaryNaturalMulWithWork 6 b).2 +
      (naturalDistanceLeWithWork (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1
        (states i).lo (bitWordValue (binaryNaturalMulWithWork 6 b).1)).2 +
      (naturalDistanceLeWithWork (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1
        (states i).hi (bitWordValue (binaryNaturalMulWithWork 6 b).1)).2 + 3 := by
  have hl := translatedEndpointAllocation_le_work r.lo parent.lo (sourceChild parent i).lo
  have hr := translatedEndpointAllocation_le_work r.lo parent.lo (sourceChild parent i).hi
  have hm := binaryNaturalMulAllocation_le_work 6 b
  have hld := naturalDistanceLeAllocation_le_work
    (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1
    (states i).lo (bitWordValue (binaryNaturalMulWithWork 6 b).1)
  have hrd := naturalDistanceLeAllocation_le_work
    (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1
    (states i).hi (bitWordValue (binaryNaturalMulWithWork 6 b).1)
  unfold anchorGuardAllocation
  dsimp only
  omega



theorem bandPredicateReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (states : Fin M → TargetInterval ny)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    bandPredicateReadAllocation parent r b tau theta velocity actions hne read allocation states ≤
      (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 := by
  have hz := zeroConnectionAllocation_le_work r.lo r.hi (List.ofFn states)
  have ha := allAllocation_with_spine (fun i : Fin M =>
    let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
    let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
    let radius := binaryNaturalMulWithWork 6 b
    let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
    let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
    (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3))
    (anchorGuardAllocation parent r b states) (List.finRange M)
    (fun i _ => anchorGuardAllocation_le_work parent r b states i)
  have ht := bandToleranceAllocation_le_work tau theta b M
  have hc := allAllocation_le_work
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardReadAllocation parent r actions hne read allocation states velocity (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (fun i _ => cutGuardReadAllocation_le_work parent r actions hne read allocation states velocity _ i h)
  simp only [List.length_finRange] at ha
  unfold bandPredicateReadAllocation bandPredicateReadWithWork
  dsimp only at ha hc ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBellmanSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Actual temporary cells allocated while scoring one action; child values
are retained pointers and their lookup scratch is counted by `footprint`. -/


theorem bellmanActionReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L : BinaryFraction) (read : Child → BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (action : BinaryBellmanAction Parent Child M)
    (hd : distanceAllocation query action.center ≤ (distance query action.center).2)
    (hr : ∀ i, footprint (action.childState i) ≤ (read (action.childState i)).2) :
    bellmanActionReadAllocation distance distanceAllocation L read footprint query action ≤
      (bellmanActionReadWithWork distance L read query action).2 := by
  have hw := arithmeticMapAllocation_le_work (fun i => read (action.childState i))
    (fun i => footprint (action.childState i)) (List.finRange M) (fun i _ => hr i)
  have hm := canonicalMulAllocation_le_work L (distance query action.center).1
  have ha := canonicalAddAllocation_le_work (canonicalMulWithWork L (distance query action.center).1).1 action.connection
  let words := (arithmeticMapWithWork (fun i => read (action.childState i)) (List.finRange M)).1
  have hs := sumListAllocation_le_work words
  have hf := canonicalAddAllocation_le_work
    (canonicalAddWithWork (canonicalMulWithWork L (distance query action.center).1).1 action.connection).1
    (sumListWithWork words).1
  unfold bellmanActionReadAllocation bellmanActionReadWithWork
  dsimp only [words] at hs hf ⊢
  omega



theorem bellmanReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L fallback : BinaryFraction) (read : Child → BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (actions : List (BinaryBellmanAction Parent Child M))
    (hd : ∀ action ∈ actions, distanceAllocation query action.center ≤ (distance query action.center).2)
    (hr : ∀ action ∈ actions, ∀ i, footprint (action.childState i) ≤ (read (action.childState i)).2) :
    bellmanReadAllocation distance distanceAllocation L fallback read footprint query actions ≤
      (bellmanReadWithWork distance L fallback read query actions).2 := by
  have hs := arithmeticMapAllocation_le_work (bellmanActionReadWithWork distance L read query)
    (bellmanActionReadAllocation distance distanceAllocation L read footprint query) actions
    (fun action ha => bellmanActionReadAllocation_le_work distance distanceAllocation L read footprint
      query action (hd action ha) (hr action ha))
  have hm := minimumAllocation_le_work fallback
    (arithmeticMapWithWork (bellmanActionReadWithWork distance L read query) actions).1
  unfold bellmanReadAllocation bellmanReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two initial-grid predicates are evaluated by explicit stored
multiplication, division and comparison. -/

namespace EditApproximation
namespace BinaryFraction

def initialScaleGuardBitBudget (B : ℕ) : ℕ :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7

def initialCenterGuardBitBudget (B : ℕ) : ℕ :=
  2100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 11) ^ 2 + 1) + 2 * B + 5

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input-width bounds for executed ceilings and initial-cone arithmetic. -/

namespace EditApproximation
namespace BinaryFraction

def scaledSeedWordBudget (B : ℕ) : ℕ := 4 * B + 6

def scaledSeedBitBudget (B : ℕ) : ℕ :=
  2100 * (B + 2) ^ 2 + 500 * (4 * B + 5) ^ 2 +
    (1000 * (4 * B + 7) ^ 2 + 1) + B + 3

def initialConeInputBudget (B : ℕ) : ℕ := B + endpointDistanceWordBudget B + stateGapWordBudget B

def initialConeWordBudget (B : ℕ) : ℕ := 32 * initialConeInputBudget B + 54

def initialConeBitBudget (B : ℕ) : ℕ :=
  stateGapBitBudget B + scaledSeedBitBudget (initialConeInputBudget B) + endpointDistanceBitBudget B +
    2000 * (initialConeInputBudget B + 1) ^ 2 +
    6000 * (4 * initialConeInputBudget B + 7) ^ 2 + 4

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialMinimumWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial entry's complete arithmetic counter, including its zero
test, spatial coefficient, fallback and finite minimum. Grid construction
is charged by the separate local endpoint enumerator. -/

namespace EditApproximation
namespace BinaryFraction

def initialMinimumInputBudget (B : ℕ) : ℕ := 40 * B + 22

def initialMinimumWordBudget (B : ℕ) : ℕ :=
  128 * B + 90 + initialConeWordBudget (initialMinimumInputBudget B)

def initialMinimumBitBudget (n B : ℕ) : ℕ :=
  (8 * B + 2) + 2000 * (B + 1) ^ 2 + 6000 * (4 * B + 3) ^ 2 +
    2000 * (32 * B + 23) ^ 2 + n * (initialConeBitBudget (initialMinimumInputBudget B) + 3) +
    (1 + n * (1000 * (initialMinimumWordBudget B + 1) ^ 2 + 2)) + 2 * B + 6

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedComputedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell kernel constructs its rational scales from the dyadic
parameter exponents. -/

namespace EditApproximation
namespace BinaryFraction

def preparedComputedCellGroupWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF) (hP : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := preparedCellGroupWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current scales.1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw hP cell
  (result.1, scales.2 + result.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell query groups with fully constructed endpoint grids. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalGroupScaleWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent Q eM eF eb : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork (parentInitial query)
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    preparedComputedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM rfl hF hP
      tau a parentInitial child initial current
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

def preparedLocalCellGroupsWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query)
    if guard.1 then
      let selected := preparedLocalGroupScaleWithWork source target parent P F exponent Q eM eF eb hM hF hP
        tau a parentInitial child initial current draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, groups.2 + count + N.bits.length + 2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryKeyedOnline
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The online branch computes its representative, all guards, coordinate
count, iteration bound and accepted source residue before executing the
literal finite optimizer. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem reduceOnlineIntegerWithWork_value (K : ℕ) (hK : 0 < K) (integer : ℕ) :
    (reduceOnlineIntegerWithWork K hK integer).1 =
      boundedOnlineInteger (optimizerTriangularMass K) (optimizerTriangularMass_positive K hK) integer := by
  apply Fin.ext
  change bitWordValue (binaryNaturalDivModWithWork integer
    (bitWordValue (triangularMassWithWork K).1)).2.1 = integer % optimizerTriangularMass K
  rw [triangularMassWithWork_value]
  exact (binaryNaturalDivModWithWork_spec integer _ (optimizerTriangularMass_positive K hK)).2



@[simp] theorem onlineIndexSetupWithWork_value {M n : ℕ} (H : ℕ)
    (band : List (Fin M → TargetInterval n)) :
    (onlineIndexSetupWithWork H band).1 = H + (listedBandCoordinates band).length + 2 := by
  simp only [onlineIndexSetupWithWork, binaryNaturalAddWithWork_value, bandCoordinatesWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The keyed online branch executes the actual endpoint grids before
its guard and optimizer. The original finite source range is preserved. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    let guard := preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F) child initial center
    if guard.1.isSome then
      let sampled := countedSampledOnlineWithWork center b initial table eta kappa band.1 hband
        G (G ^ 80) t accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One rounded center is queried at each retained dyadic scale. Both
eligibility and the complete online optimizer are charged. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalOnlineScaleWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let eligible := centerEligibilityWithWork b F a (parentInitial center.1)
  if eligible.1 then
    let selected := preparedOnlineWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table t center.1 (integer b center.1)
    (selected.1, spacing.2 + center.2 + eligible.2 + selected.2 + e + 4)
  else (none, spacing.2 + center.2 + eligible.2 + e + 3)

def preparedLocalOnlineActionsWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := queryExponentsWithWork N F a (parentInitial query)
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      parentInitial child initial table t integer query) scales.1
  (selected.1, scales.2 + selected.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full stored-data local refinement kernel. All candidate lists are
built by their literal counted routines, then the Bellman/online update
is performed. No action-list equality premise is assumed. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalKernelWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) : BinaryFraction × ℕ :=
  let representatives := localRepresentativesWithWork N P F a parentInitial query
  let groups := preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
    tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
  let online := preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial childMass childInitial history t integer query
  let result := physicalContinuationWithWork parent representatives.1 P F delta (parentInitial query)
    old current groups.1 online.1 query
  (result.1, representatives.2 + groups.2 + online.2 + result.2 + 4)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of every local initial-cone center is charged, including
rejected center predicates. The scale test itself bounds the emitted grid. -/

namespace EditApproximation
namespace BinaryFraction

def initialGridScaleBitBudget (P Amax B : ℕ) : ℕ :=
  let L := 64 * Amax ^ 2 * P + 2
  100 * (B + 6) ^ 2 + gridStateBoxBitBudget L (B + 5) +
    L ^ 2 * (initialCenterGuardBitBudget (B + 4) + 3) + 2

attribute [local irreducible] seedGridSpacingWithWork gridStateBoxWithWork filterWithWork
  initialCenterGuardWithWork initialScaleGuardWithWork

def initialCentersBitBudget (P Amax B : ℕ) : ℕ :=
  let L := 64 * Amax ^ 2 * P + 2
  (B + 1) * (B + 9) + 2 + (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (initialGridScaleBitBudget P Amax B + L ^ 2 + 3) + 3

def initialProgramBitBudget (P Amax B : ℕ) : ℕ :=
  initialCentersBitBudget P Amax B +
    initialMinimumBitBudget ((B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2) (B + 4) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalWarmupKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonterminal warmup step uses the same local representative grids,
but computes a single Bellman minimum and performs no online update. -/

namespace EditApproximation
namespace BinaryFraction

def localWarmupKernelWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny) :
    BinaryFraction × ℕ :=
  let representatives := localRepresentativesWithWork N P F a initial query
  let actions := wideActionsFromRepresentativesWithWork M parent representatives.1 P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := bellmanWithWork endpointDistanceWithWork L.1 (initial query) child query actions.1
  (result.1, representatives.2 + actions.2 + L.2 + result.2 + 3)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedRepresentativeWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete representative work, with every endpoint grid construction
and every score/prefix predicate charged. Only input word bounds occur. -/

namespace EditApproximation
namespace BinaryFraction

def wideMaterializationBitBudget (M P B : ℕ) : ℕ :=
  M * (wideChildGridBitBudget P B + 6) +
    (M + 1) * (6 * M + 10) * ((40 * P + 2) ^ 2 + 1) ^ (M + 1) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWideActionsWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full wide-action list materializes each grid and each connection
charge. Endpoint representation bounds follow from the interval subtype. -/

namespace EditApproximation
namespace BinaryFraction

def wideActionsBitBudget (M P count B : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  count * (wideMaterializationBitBudget M P B +
    V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1 + V + 3)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPhysicalContinuationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual endpoint distances and connection words supply all representation
premises of the two Bellman scans and final refinement update. -/

namespace EditApproximation
namespace BinaryFraction

def physicalContinuationInputBudget (M B : ℕ) : ℕ :=
  B + connectionWordBudget M B + endpointDistanceWordBudget B + 4 * B + 2

def physicalContinuationBitBudget (M P nr ng no B : ℕ) : ℕ :=
  wideActionsBitBudget M P nr B + 2000 * (B + 1) ^ 2 +
    localContinuationBitBudget M (nr * (40 * P + 2) ^ (2 * M)) ng no
      (physicalContinuationInputBudget M B) (endpointDistanceBitBudget B) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalWarmupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The warmup branch constructs its actual local representative/action
lists and evaluates their finite Bellman minimum with counted arithmetic. -/

namespace EditApproximation
namespace BinaryFraction

def localWarmupWordBudget (M B : ℕ) : ℕ :=
  let W := physicalContinuationInputBudget M (B + 4)
  W + bellmanActionWordBudget M W

def localWarmupBitBudget (M P F B : ℕ) : ℕ :=
  let nr := (B + 1) * (64 * F * P + 2) ^ 2
  let W := physicalContinuationInputBudget M (B + 4)
  localRepresentativesBitBudget P F B + wideActionsBitBudget M P nr (B + 4) +
    2000 * (B + 5) ^ 2 + bellmanBitBudget M (nr * (40 * P + 2) ^ (2 * M)) W W
      (endpointDistanceBitBudget (B + 4)) + 3

attribute [local irreducible] localRepresentativesWithWork wideActionsFromRepresentativesWithWork

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCachedShellWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial and warmup returns are integers on every seed. Their cache
representation is produced by the counted fixed-denominator routine, rather
than by an uncharged conversion of a rational value. -/

namespace EditApproximation

namespace BinaryFraction

attribute [local irreducible] initialProgramWithWork localWarmupKernelWithWork

def cachedInitialProgramWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (U : TargetInterval n → ℕ) (query : TargetInterval n) : BinaryFraction × ℕ :=
  finishCachedWithWork (initialProgramWithWork sourceLength N P F A a U query)
    [true] (by decide) 0

def cachedInitialProgramBitBudget (P Amax B : ℕ) : ℕ :=
  initialProgramBitBudget P Amax B + powerDenominatorBitBudget 0 (initialMinimumWordBudget (B + 4)) 1 + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellGridWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word-size bounds for the literal whole-cell index scans. The
cardinalities here are the emitted local ranges, not the target length. -/

namespace EditApproximation
namespace BinaryFraction

def cellCoordinateSetupBitBudget (B : ℕ) : ℕ :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)

def targetCellsBitBudget (left right B : ℕ) : ℕ :=
  2 * cellCoordinateSetupBitBudget B + left + right + left * (5 * right + 3) + 2

def cellGridSetupBitBudget (B : ℕ) : ℕ := 2000000 * (B + 100) ^ 2

def cellGridPointBitBudget (B : ℕ) : ℕ := 1000 * (B + 100) ^ 2

def cellGridPointsBitBudget (count B : ℕ) : ℕ :=
  cellGridSetupBitBudget B + count * (cellGridPointBitBudget B + 5)


def cellStatesBitBudget (left right B : ℕ) : ℕ :=
  cellGridPointsBitBudget left B + cellGridPointsBitBudget right B +
    left * (right * (16 * (17 * B + 78) + 11) + right + 3) + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellCentersWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete work for a whole-cell representative scan, including both
endpoint grids and every initial-value eligibility test. -/

namespace EditApproximation
namespace BinaryFraction

def cellCentersBitBudget (left right B : ℕ) : ℕ :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    cellStatesBitBudget left right (4 * B + 40) +
    left * right * (localEligibilityBitBudget B + 3) + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact finite-count source reads inside a sampled group estimator.
A source read is executed only in the sampled branch; an exact scale
uses the complete child array and makes no random-source lookup. -/

namespace EditApproximation.BinaryFraction

/-- The exact number of source calls at one group scale. -/
def groupScaleSourceCalls (M k : ℕ) : ℕ := if k = M then 0 else k



end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReads
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online objective construction charges every historical table read,
including repeated uses in gain and decrement terms. -/

namespace EditApproximation
namespace BinaryFraction





@[simp] theorem gainReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (s : ℕ) (i : β × σ) :
    (gainReadWithWork mass read s i).1 = (gainWithWork mass (fun t j => (read t j).1) s i).1 := rfl

@[simp] theorem decrementReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (s : ℕ) (i : β × σ) :
    (decrementReadWithWork mass read s i).1 = (decrementWithWork mass (fun t j => (read t j).1) s i).1 := rfl



@[simp] theorem optimisticTermReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) :
    (optimisticTermReadWithWork mass read coefficient s i).1 =
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).1 := rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadCostBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lookup overhead is controlled by the loops that actually run.
These comparisons require only a bound on one finite-buffer lookup. -/

namespace EditApproximation

namespace BinaryFraction

def tableReadFactor (R : ℕ) : ℕ := 4 * (R + 4)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table-reader and random-source costs are retained together through
member estimation, tie-broken selection, and rounded action return. -/

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

def unskippedEstimateSourceWithWork (member : Member) : BinaryFraction × ℕ :=
  let mass := envelopeVectorReadWithWork b member.actions initial
  let rounded := roundedBandReadWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => current i (rounded.1.get i)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let result := countedGroupMemberSourceWithWork Q b scales connection.1 mass.1 values.1 draw
  (result.1, mass.2 + rounded.2 + values.2 + connection.2 + result.2 + 5)

def chooseUnskippedSourceWithWork (members : List Member) (hne : members ≠ []) : Member × ℕ :=
  selectGroupWithWork members hne
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw)

def sampledGroupActionSourceWithWork (members : List Member) (hne : members ≠ []) :
    BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M × ℕ :=
  let selected := chooseUnskippedSourceWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne
  let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
  let result := endpointActionWithWork selected.1.center rounded.1.get
  (result.1, selected.2 + rounded.2 + result.2 + 3)


end Group
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellSourcePort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)

/-- The same raw dyadic scale list and Fin-count indices as the original
cell estimator, now with the cost of decoding every sampled coordinate. -/
def preparedCellGroupSourceWithWork (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let centers := cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell
  let members := filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers.1
  if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
    let selected := sampledGroupActionSourceWithWork source target parent b P exponent Q tau (nat F)
      (fun i q => (child i q).1) initial current (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members.1 h
    (some selected.1, centers.2 + members.2 + selected.2 + 2)

end Cell
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySeedMedianWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The natural seed cache stores a trimmed result, so repeated median
passes do not accumulate leading zero words. The trimming scan is charged. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem seedMedianWithWork_value (N multiplier : ℕ) (values : List BinaryFraction) :
    bitWordValue (seedMedianWithWork N multiplier values).1 =
      min N (upperMedian (values.map fun a => ⌈(multiplier : ℚ) * a.value⌉₊)) := by
  simp only [seedMedianWithWork, trimBitWordWithWork_value, medianSeedWithWork_value]

def seedMedianBitBudget (n B : ℕ) : ℕ := medianSeedBitBudget n B + 12 * B + 14

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMedianSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every insertion-sort copy, median traversal, ceiling and final trimming
scan is retained in these seed-branch allocation and call-frame counters. -/

namespace EditApproximation



theorem wordLEAllocation_le_work (a b : List Bool) :
    wordLEAllocation a b ≤ (wordLEWithWork a b).2 := by
  exact Nat.zero_le _



theorem wordInsertAllocation_le_work (a : List Bool) (words : List (List Bool)) :
    wordInsertAllocation a words ≤ (wordInsertWithWork a words).2 := by
  induction words with
  | nil => rfl
  | cons b rest ih =>
    have hc := wordLEAllocation_le_work a b
    unfold wordInsertAllocation wordInsertWithWork
    dsimp only
    split_ifs <;> dsimp only
    · exact Nat.add_le_add_right hc 2
    · calc
        _ = (wordLEAllocation a b + wordInsertAllocation a rest) + 1 := (Nat.add_assoc _ _ _).symm
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add hc ih) (by decide : 1 ≤ 2)



theorem wordSortAllocation_le_work (words : List (List Bool)) :
    wordSortAllocation words ≤ (wordSortWithWork words).2 := by
  induction words with
  | nil => simp only [wordSortAllocation, wordSortWithWork]; omega
  | cons a rest ih =>
    have hi := wordInsertAllocation_le_work a (wordSortWithWork rest).1
    simp only [wordSortAllocation, wordSortWithWork]
    omega

namespace BinaryFraction



theorem scaledCeilingAllocation_le_work (multiplier : ℕ) (a : BinaryFraction) :
    scaledCeilingAllocation multiplier a ≤ (scaledCeilingWithWork multiplier a).2 := by
  have hm := canonicalMulAllocation_le_work (nat multiplier) a
  have hc := naturalCeilingAllocation_le_work (canonicalMulWithWork (nat multiplier) a).1
  unfold scaledCeilingAllocation scaledCeilingWithWork
  dsimp only
  omega



theorem medianSeedAllocation_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    medianSeedAllocation N multiplier values ≤ (medianSeedWithWork N multiplier values).2 := by
  have hm := arithmeticMapAllocation_le_work (scaledCeilingWithWork multiplier)
    (scaledCeilingAllocation multiplier) values (fun a _ => scaledCeilingAllocation_le_work multiplier a)
  let rounded := (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  have hs := wordSortAllocation_le_work rounded
  have hc := wordLEAllocation_le_work N.bits ((wordSortWithWork rounded).1.getD (values.length / 2) [])
  unfold medianSeedAllocation medianSeedWithWork wordMinWithWork
  dsimp only
  dsimp only [rounded] at hs hc
  omega



theorem seedMedianAllocation_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    seedMedianAllocation N multiplier values ≤ (seedMedianWithWork N multiplier values).2 := by
  have hm := medianSeedAllocation_le_work N multiplier values
  have ht := trimBitWordAllocation_le_work (medianSeedWithWork N multiplier values).1
  unfold seedMedianAllocation seedMedianWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal exact/sample reductions and the sample-count constructor.
The child-index list cells and every comparison are included. -/

namespace EditApproximation.BinaryFraction



theorem equalAllocation_le_work (a b : BinaryFraction) :
    equalAllocation a b ≤ (equalWithWork a b).2 := by
  have hl := ltAllocation_le_work b a
  have hr := ltAllocation_le_work a b
  unfold equalAllocation equalWithWork leWithWork
  dsimp only
  omega



theorem groupTermsAllocation_le_work {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupTermsAllocation h envelope indices ≤ (groupTermsWithWork h envelope values indices).2 := by
  apply arithmeticMapAllocation_le_work
  intro i _
  have hc := equalAllocation_le_work (envelope.get i) h
  dsimp only
  omega



theorem groupIndexAllocation_le_work {M : ℕ}
    (h : BinaryFraction) (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    groupIndexAllocation h envelope values indices ≤ (groupIndexWithWork h envelope values indices).2 := by
  have ht := groupTermsAllocation_le_work h envelope values indices
  have hs := sumListAllocation_le_work (groupTermsWithWork h envelope values indices).1
  unfold groupIndexAllocation groupIndexWithWork
  dsimp only
  omega



theorem groupSampleCountAllocation_le_work (M Q b : ℕ) (h : BinaryFraction) :
    groupSampleCountAllocation M Q b h ≤ (groupSampleCountWithWork M Q b h).2 := by
  have h1 := canonicalMulAllocation_le_work (nat Q) (nat M)
  have h2 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat Q) (nat M)).1 h
  have h3 := divAllocation_le_work (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)
  have h4 := naturalCeilingAllocation_le_work
    (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1
  have h5 := wordLEAllocation_le_work M.bits
    (naturalCeilingWithWork (divWithWork (canonicalMulWithWork (canonicalMulWithWork (nat Q) (nat M)).1 h).1 (nat b)).1).1
  unfold groupSampleCountAllocation groupSampleCountWithWork wordMinWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupReductionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem selectGroupAllocation_le_work {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) (allocation : ι → ℕ)
    (h : ∀ member ∈ members, allocation member ≤ (estimate member).2) :
    selectGroupAllocation members estimate allocation ≤ (selectGroupWithWork members hne estimate).2 := by
  have hs := scoredArgmaxAllocation_le_work
    (fun member => ((estimate member).1.neg, (estimate member).2 + 1)) allocation members
    (fun member hm => (h member hm).trans (Nat.le_succ _))
  unfold selectGroupAllocation selectGroupWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Index decoding, the sampled index spine and the exact/sample reduction. -/


theorem groupScaleSourceAllocation_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ)
    (allocation : Fin k → ℕ) (ha : ∀ i, allocation i ≤ (draw i).2) :
    groupScaleSourceAllocation k h envelope values draw allocation ≤
      (groupScaleSourceWithWork k h envelope values draw).2 := by
  let indices := if k = M then (List.finRange M, 0) else arithmeticMapWithWork draw (List.finRange k)
  have hi := groupIndexAllocation_le_work h envelope values indices.1
  have hm := arithmeticMapAllocation_le_work draw allocation (List.finRange k) (fun i _ => ha i)
  have hd := divAllocation_le_work (nat M) (nat k)
  have hp := canonicalMulAllocation_le_work
    (if k = M then (one, 1) else divWithWork (nat M) (nat k)).1
    (groupIndexWithWork h envelope values indices.1).1
  unfold groupScaleSourceAllocation groupScaleSourceWithWork
  dsimp only [indices] at hi hp
  dsimp only
  by_cases heq : k = M
  · simp only [ite_eq_left heq] at hi hp ⊢
    omega
  · simp only [ite_eq_right heq] at hi hp ⊢
    omega



theorem groupMemberSourceAllocation_le_work {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ)
    (allocation : ∀ s : Fin T, Fin (count s) → ℕ)
    (ha : ∀ s i, allocation s i ≤ (draw s i).2) :
    groupMemberSourceAllocation scales count connection envelope values draw allocation ≤
      (groupMemberSourceWithWork scales count connection envelope values draw).2 := by
  let terms := (arithmeticMapWithWork (fun s => groupScaleSourceWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)).1
  have ht := arithmeticMapAllocation_le_work
    (fun s => groupScaleSourceWithWork (count s) (scales s) envelope values (draw s))
    (fun s => groupScaleSourceAllocation (count s) (scales s) envelope values (draw s) (allocation s)) (List.finRange T)
    (fun s _ => groupScaleSourceAllocation_le_work (count s) (scales s) envelope values (draw s) (allocation s) (ha s))
  have hs := sumListAllocation_le_work terms
  have ha := canonicalAddAllocation_le_work connection (sumListWithWork terms).1
  unfold groupMemberSourceAllocation groupMemberSourceWithWork
  dsimp only [terms] at hs ha ⊢
  omega



theorem countedGroupMemberSourceAllocation_le_work {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
    (allocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)
    (ha : ∀ t i, allocation t i ≤ (draw t i).2) :
    countedGroupMemberSourceAllocation Q b scales connection envelope values draw allocation ≤
      (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).2 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  have hc := vectorMapAllocation_le_work T (fun t => groupSampleCountWithWork M Q b (scales t))
    (fun t => groupSampleCountAllocation M Q b (scales t)) (fun t => groupSampleCountAllocation_le_work M Q b (scales t))
  have hg := groupMemberSourceAllocation_le_work scales count connection envelope values (fun t j => draw t (Fin.cast (heq t) j))
    (fun t j => allocation t (Fin.cast (heq t) j)) (fun t j => ha t _)
  unfold countedGroupMemberSourceAllocation countedGroupMemberSourceWithWork
  dsimp only [count, counts] at hg ⊢
  omega


end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryEnvelopeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Scratch replay for the bounded dyadic scan and the actual band
initial-value reads used to form each child envelope. -/

namespace EditApproximation.BinaryFraction



theorem dyadicScanAllocation_le_work (a candidate : BinaryFraction) (n : ℕ) :
    dyadicScanAllocation a candidate n ≤ (dyadicScanWithWork a candidate n).2 := by
  induction n generalizing candidate with
  | zero => simp only [dyadicScanAllocation, dyadicScanWithWork]; exact Nat.zero_le _
  | succ n ih =>
    have hc := ltAllocation_le_work candidate a
    have ht := ih (doubleFraction candidate)
    unfold dyadicScanAllocation dyadicScanWithWork
    dsimp only
    split_ifs <;> dsimp only
    · exact (Nat.add_assoc _ _ _).symm.le.trans
        (Nat.add_le_add (Nat.add_le_add hc ht) (by decide : 1 ≤ 2))
    · exact Nat.add_le_add hc (Nat.zero_le 1)



theorem dyadicCeilingAllocation_le_work (a : BinaryFraction) :
    dyadicCeilingAllocation a ≤ (dyadicCeilingWithWork a).2 := by
  have h := dyadicScanAllocation_le_work a (inversePowerTwo a.width) (2 * a.width)
  unfold dyadicCeilingAllocation dyadicCeilingWithWork
  dsimp only
  omega



theorem bandEnvelopeReadAllocation_le_work {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (i : Fin M)
    (h : ∀ action ∈ band, footprint i (action i) ≤ (read i (action i)).2) :
    bandEnvelopeReadAllocation b band read footprint i ≤ (bandEnvelopeReadWithWork b band read i).2 := by
  have hv := arithmeticMapAllocation_le_work (fun action => read i (action i))
    (fun action => footprint i (action i)) band h
  let values := (arithmeticMapWithWork (fun action => read i (action i)) band).1
  have hd := divAllocation_le_work (nat b) (nat M)
  have hm := maximumAllocation_le_work zero values
  have hx := maxAllocation_le_work (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1
  have he := dyadicCeilingAllocation_le_work
    (maxWithWork (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1).1
  unfold bandEnvelopeReadAllocation bandEnvelopeReadWithWork
  dsimp only
  dsimp only [values] at hm hx he
  omega



theorem envelopeVectorReadAllocation_le_work {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (h : ∀ i action, action ∈ band → footprint i (action i) ≤ (read i (action i)).2) :
    envelopeVectorReadAllocation b band read footprint ≤ (envelopeVectorReadWithWork b band read).2 := by
  exact vectorMapAllocation_le_work M _ _ (fun i => bandEnvelopeReadAllocation_le_work b band read footprint i (h i))

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRoundingSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem binaryGridRoundAllocation_le_work (spacing position : ℕ) :
    binaryGridRoundAllocation spacing position ≤ (binaryGridRoundWithWork spacing position).2 := by
  have hd := binaryNaturalDivAllocation_le_work position spacing
  have hm := bitMulAllocation_le_work spacing.bits (binaryNaturalDivModWithWork position spacing).1
  unfold binaryGridRoundAllocation binaryGridRoundWithWork
  dsimp only
  omega



theorem roundStateAllocation_le_work {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing) (q : TargetInterval n) :
    roundStateAllocation spacing q ≤ (roundStateWithWork spacing hspacing q).2 := by
  have hl := binaryGridRoundAllocation_le_work spacing q.lo
  have hr := binaryGridRoundAllocation_le_work spacing q.hi
  unfold roundStateAllocation roundStateWithWork binaryIntervalRoundWithWork
  dsimp only
  omega



theorem actionEqualAllocation_le_work {n M : ℕ} (a b : Fin M → TargetInterval n) :
    actionEqualAllocation a b ≤ (actionEqualWithWork a b).2 := by
  apply allAllocation_le_work
  intro i _
  have hl := naturalEqualAllocation_le_work (a i).lo (b i).lo
  have hr := naturalEqualAllocation_le_work (a i).hi (b i).hi
  dsimp only
  omega



theorem actionMemberAllocation_le_work {n M : ℕ} (a : Fin M → TargetInterval n)
    (actions : List (Fin M → TargetInterval n)) :
    actionMemberAllocation a actions ≤ (actionMemberWithWork a actions).2 := by
  induction actions with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have hh := actionEqualAllocation_le_work a b
    unfold actionMemberAllocation actionMemberWithWork
    dsimp only
    exact (Nat.add_le_add hh ih).trans (Nat.le_succ _)

namespace BinaryFraction



theorem roundedSpacingAllocation_le_work (theta envelope : BinaryFraction) :
    roundedSpacingAllocation theta envelope ≤ (roundedSpacingWithWork theta envelope).2 := by
  have hp := canonicalMulAllocation_le_work theta envelope
  have hm := maxAllocation_le_work one (canonicalMulWithWork theta envelope).1
  have hc := naturalCeilingAllocation_le_work (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  unfold roundedSpacingAllocation roundedSpacingWithWork
  dsimp only
  omega



theorem roundedBandReadAllocation_le_work {n M : ℕ} (exponent b : ℕ) (band : List (Fin M → TargetInterval n))
    (hne : band ≠ []) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval n → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    roundedBandReadAllocation exponent b band hne read allocation ≤
      (roundedBandReadWithWork exponent b band hne read).2 := by
  apply vectorMapAllocation_le_work
  intro i
  have he := bandEnvelopeReadAllocation_le_work b band read allocation i (fun action _ => h i (action i))
  have hs := roundedSpacingAllocation_le_work (inversePowerTwo exponent) (bandEnvelopeReadWithWork b band read i).1
  have hr := roundStateAllocation_le_work
    (bitWordValue (roundedSpacingWithWork (inversePowerTwo exponent) (bandEnvelopeReadWithWork b band read i).1).1)
    (roundedSpacingWithWork_pos _ _) (band.head hne i)
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryContinuationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem onlineMinimumAllocation_le_work (values : List BinaryFraction) :
    onlineMinimumAllocation values ≤ (onlineMinimumWithWork values).2 := by
  cases values with
  | nil => exact Nat.zero_le _
  | cons first rest => exact (minimumAllocation_le_work first rest).trans (Nat.le_add_right _ _)



theorem refinementUpdateAllocation_le_work (delta cone : BinaryFraction) (online : Option BinaryFraction) :
    refinementUpdateAllocation delta cone online ≤ (refinementUpdateWithWork delta cone online).2 := by
  cases online with
  | none => exact Nat.zero_le _
  | some online =>
    have ha := canonicalAddAllocation_le_work one delta
    have hd := divAllocation_le_work cone (canonicalAddWithWork one delta).1
    have hm := maxAllocation_le_work (divWithWork cone (canonicalAddWithWork one delta).1).1 online
    have hf := minAllocation_le_work cone
      (maxWithWork (divWithWork cone (canonicalAddWithWork one delta).1).1 online).1
    unfold refinementUpdateAllocation refinementUpdateWithWork
    dsimp only
    omega

/-- The two Bellman passes, materialized online scores and final arithmetic
retain their actual primitive allocation traces. -/


theorem localContinuationReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L delta fallback : BinaryFraction) (old current : Child → BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Child → ℕ) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M))
    (hd : ∀ state, distanceAllocation query state ≤ (distance query state).2)
    (ho : ∀ child, oldAllocation child ≤ (old child).2)
    (hc : ∀ child, currentAllocation child ≤ (current child).2) :
    localContinuationReadAllocation distance distanceAllocation L delta fallback old current
      oldAllocation currentAllocation query wide groups online ≤
      (localContinuationReadWithWork distance L delta fallback old current query wide groups online).2 := by
  have hw := bellmanReadAllocation_le_work distance distanceAllocation L fallback old oldAllocation query wide
    (fun action _ => hd action.center) (fun action _ i => ho (action.childState i))
  have hg := bellmanReadAllocation_le_work distance distanceAllocation L
    (bellmanReadWithWork distance L fallback old query wide).1 current currentAllocation query groups
    (fun action _ => hd action.center) (fun action _ i => hc (action.childState i))
  have hs := arithmeticMapAllocation_le_work (bellmanActionReadWithWork distance L current query)
    (bellmanActionReadAllocation distance distanceAllocation L current currentAllocation query) online
    (fun action _ => bellmanActionReadAllocation_le_work distance distanceAllocation L current
      currentAllocation query action (hd action.center) (fun i => hc (action.childState i)))
  let scores := (arithmeticMapWithWork (bellmanActionReadWithWork distance L current query) online).1
  have hm := onlineMinimumAllocation_le_work scores
  have hf := refinementUpdateAllocation_le_work delta
    (bellmanReadWithWork distance L (bellmanReadWithWork distance L fallback old query wide).1 current query groups).1
    (onlineMinimumWithWork scores).1
  unfold localContinuationReadAllocation localContinuationReadWithWork
  dsimp only [scores] at hm hf ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Inline initial-cone evaluation reads the gathered previous-pass seed
words explicitly. Each query seed is loaded once per routine and each
visited center load contributes its measured lookup cost. -/

namespace EditApproximation
namespace BinaryFraction



def initialGridPlainWithWork {n : ℕ} (P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (radius : ℕ) (q : TargetInterval n) (b : ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
  (selected.1, spacing.2 + points.2 + selected.2 + 2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem cellCoordinatesAllocation_le_work (side : BinaryFraction) (p radius : ℕ) :
    cellCoordinatesAllocation side p radius ≤ (cellCoordinatesWithWork side p radius).2 := by
  let lower := (saturatingSubtractWithWork p radius).1
  let upper := (binaryNaturalAddWithWork p radius).1
  let firstQ := (divWithWork (nat (bitWordValue lower)) side).1
  let lastQ := (divWithWork (nat (bitWordValue upper)) side).1
  let first := (naturalFloorWithWork firstQ).1
  let last := (naturalFloorWithWork lastQ).1
  let stop := (binaryNaturalAddWithWork (bitWordValue last) 1).1
  have h1 := saturatingSubtractAllocation_le_work p radius
  have h2 := binaryNaturalAddAllocation_le_work p radius
  have h3 := divAllocation_le_work (nat (bitWordValue lower)) side
  have h4 := divAllocation_le_work (nat (bitWordValue upper)) side
  have h5 := naturalFloorAllocation_le_work firstQ
  have h6 := naturalFloorAllocation_le_work lastQ
  have h7 := binaryNaturalAddAllocation_le_work (bitWordValue last) 1
  have h8 := saturatingSubtractAllocation_le_work (bitWordValue stop) (bitWordValue first)
  unfold cellCoordinatesAllocation cellCoordinatesWithWork
  dsimp only [lower, upper, firstQ, lastQ, first, last, stop] at h3 h4 h5 h6 h7 h8 ⊢
  rw [List.length_range']
  omega



theorem targetCellsAllocation_le_work {n : ℕ} (side : BinaryFraction) (radius : ℕ) (q : TargetInterval n) :
    targetCellsAllocation side radius q ≤ (targetCellsWithWork side radius q).2 := by
  have hl := cellCoordinatesAllocation_le_work side q.lo radius
  have hr := cellCoordinatesAllocation_le_work side q.hi radius
  have hm := arithmeticFlatMapAllocation_le_work
    (fun lo => arithmeticMapWithWork (fun hi => ((lo, hi), 1)) (cellCoordinatesWithWork side q.hi radius).1)
    (fun _ => arithmeticMapAllocation (fun _ => 1) (cellCoordinatesWithWork side q.hi radius).1)
    (cellCoordinatesWithWork side q.lo radius).1 (fun _ _ =>
      arithmeticMapAllocation_le_work _ _ _ (fun _ _ => le_rfl))
  unfold targetCellsAllocation targetCellsWithWork
  dsimp only
  omega



theorem cellGridPointsAllocation_le_work (side : BinaryFraction) (g cell : ℕ) :
    cellGridPointsAllocation side g cell ≤ (cellGridPointsWithWork side g cell).2 := by
  let next := (binaryNaturalAddWithWork cell 1).1
  let lower := (canonicalMulWithWork (nat cell) side).1
  let upper := (canonicalMulWithWork (nat (bitWordValue next)) side).1
  let firstQ := (divWithWork lower (nat g)).1
  let lastQ := (divWithWork upper (nat g)).1
  let first := (naturalCeilingWithWork firstQ).1
  let last := (naturalCeilingWithWork lastQ).1
  let count := (saturatingSubtractWithWork (bitWordValue last) (bitWordValue first)).1
  let indices := List.range' (bitWordValue first) (bitWordValue count)
  have h1 := binaryNaturalAddAllocation_le_work cell 1
  have h2 := canonicalMulAllocation_le_work (nat cell) side
  have h3 := canonicalMulAllocation_le_work (nat (bitWordValue next)) side
  have h4 := divAllocation_le_work lower (nat g)
  have h5 := divAllocation_le_work upper (nat g)
  have h6 := naturalCeilingAllocation_le_work firstQ
  have h7 := naturalCeilingAllocation_le_work lastQ
  have h8 := saturatingSubtractAllocation_le_work (bitWordValue last) (bitWordValue first)
  have h9 := arithmeticMapAllocation_le_work (fun i =>
      (bitWordValue (binaryNaturalMulWithWork g i).1, (binaryNaturalMulWithWork g i).2 + Nat.size i + 2))
    (fun i => binaryNaturalMulAllocation g i + Nat.size i) indices (by
      intro i _
      have h := binaryNaturalMulAllocation_le_work g i
      dsimp only
      omega)
  unfold cellGridPointsAllocation cellGridPointsWithWork
  dsimp only [next, lower, upper, firstQ, lastQ, first, last, count, indices] at h3 h4 h5 h6 h7 h8 h9 ⊢
  omega



theorem cellStatesAllocation_le_work (n g : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ) :
    cellStatesAllocation n g side cell ≤ (cellStatesWithWork n g side cell).2 := by
  have hl := cellGridPointsAllocation_le_work side g cell.1
  have hr := cellGridPointsAllocation_le_work side g cell.2
  have hm := arithmeticFlatMapAllocation_le_work
    (fun lo => filterMapWithWork (makeStateWithWork n lo) (cellGridPointsWithWork side g cell.2).1)
    (fun lo => filterMapAllocation (makeStateWithWork n lo) (makeStateAllocation n lo) (cellGridPointsWithWork side g cell.2).1)
    (cellGridPointsWithWork side g cell.1).1 (fun lo _ => filterMapAllocation_le_work _ _ _
      (fun hi _ => makeStateAllocation_le_work n lo hi))
  unfold cellStatesAllocation cellStatesWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryEligibilitySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem centerEligibilityAllocation_le_work (b F : ℕ) (a initial : BinaryFraction) :
    centerEligibilityAllocation b F a initial ≤ (centerEligibilityWithWork b F a initial).2 := by
  have hd := canonicalMulAllocation_le_work (nat 4) a
  have hlo := divAllocation_le_work (nat b) (canonicalMulWithWork (nat 4) a).1
  have hfac := canonicalMulAllocation_le_work (nat 8) (nat F)
  have hup := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
  have hl := leAllocation_le_work (divWithWork (nat b) (canonicalMulWithWork (nat 4) a).1).1 initial
  have hh := leAllocation_le_work initial (canonicalMulWithWork (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)).1
  unfold centerEligibilityAllocation centerEligibilityWithWork
  dsimp only
  omega



theorem refinementScaleGuardAllocation_le_work (F b : ℕ) (a w : BinaryFraction) :
    refinementScaleGuardAllocation F b a w ≤ (refinementScaleGuardWithWork F b a w).2 := by
  have hd := canonicalMulAllocation_le_work (nat 16) (nat F)
  have hlo := divAllocation_le_work w (canonicalMulWithWork (nat 16) (nat F)).1
  have hfac := canonicalMulAllocation_le_work (nat 8) a
  have hup := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 8) a).1 w
  have hl := leAllocation_le_work (divWithWork w (canonicalMulWithWork (nat 16) (nat F)).1).1 (nat b)
  have hh := leAllocation_le_work (nat b) (canonicalMulWithWork (canonicalMulWithWork (nat 8) a).1 w).1
  unfold refinementScaleGuardAllocation refinementScaleGuardWithWork
  dsimp only
  omega



theorem queryExponentsAllocation_le_work (N F : ℕ) (a w : BinaryFraction) :
    queryExponentsAllocation N F a w ≤ (queryExponentsWithWork N F a w).2 := by
  have hf := filterAllocation_le_work
    (fun e => ((refinementScaleGuardWithWork F (2 ^ e) a w).1,
      (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2))
    (fun e => refinementScaleGuardAllocation F (2 ^ e) a w + e + 1)
    (List.range (max 1 N.bits.length)) (by
      intro e _
      have h := refinementScaleGuardAllocation_le_work F (2 ^ e) a w
      dsimp only
      omega)
  unfold queryExponentsAllocation queryExponentsWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalRepresentativeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem representativeScaleReadAllocation_le_work {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (radius : List Bool) (query : TargetInterval n) (e : ℕ)
    (h : ∀ r, allocation r ≤ (read r).2) :
    representativeScaleReadAllocation P F a read allocation radius query e ≤
      (representativeScaleReadWithWork P F a read radius query e).2 := by
  let b := 2 ^ e
  let spacing := (seedGridSpacingWithWork b P).1
  let points := (gridStateBoxWithWork n (bitWordValue spacing) (bitWordValue radius) query.lo query.hi).1
  let test := fun r => ((centerEligibilityWithWork b F a (read r).1).1,
    (centerEligibilityWithWork b F a (read r).1).2 + (read r).2)
  have hs := seedGridSpacingAllocation_le_work b P
  have hg := gridStateBoxAllocation_le_work n (bitWordValue spacing) (bitWordValue radius) query.lo query.hi
  have hf := filterAllocation_le_work test
    (fun r => centerEligibilityAllocation b F a (read r).1 + allocation r) points (by
      intro r _
      exact Nat.add_le_add (centerEligibilityAllocation_le_work b F a (read r).1) (h r))
  have hm := arithmeticMapAllocation_le_work (fun r => ((b, r), 1)) (fun _ => 1)
    (filterWithWork test points).1 (fun _ _ => le_rfl)
  unfold representativeScaleReadAllocation representativeScaleReadWithWork
  dsimp only [b, spacing, points, test] at hs hg hf hm ⊢
  omega



theorem localRepresentativeReadAllocation_le_work {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (query : TargetInterval n) (h : ∀ r, allocation r ≤ (read r).2) :
    localRepresentativeReadAllocation N P F a read allocation query ≤
      (localRepresentativeReadWithWork N P F a read query).2 := by
  have hq := h query
  have hs := queryExponentsAllocation_le_work N F a (read query).1
  have hr := naturalCeilingAllocation_le_work (read query).1
  have hl := arithmeticFlatMapAllocation_le_work
    (representativeScaleReadWithWork P F a read (naturalCeilingWithWork (read query).1).1 query)
    (representativeScaleReadAllocation P F a read allocation (naturalCeilingWithWork (read query).1).1 query)
    (queryExponentsWithWork N F a (read query).1).1
    (fun e _ => representativeScaleReadAllocation_le_work P F a read allocation _ query e h)
  unfold localRepresentativeReadAllocation localRepresentativeReadWithWork
  dsimp only
  omega



theorem cellCentersReadAllocation_le_work {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (cell : ℕ × ℕ) (h : ∀ r, allocation r ≤ (initial r).2) :
    cellCentersReadAllocation P F b a theta initial allocation cell ≤
      (cellCentersReadWithWork P F b a theta initial cell).2 := by
  let spacing := (seedGridSpacingWithWork b P).1
  let side := (canonicalMulWithWork theta (nat b)).1
  let states := (cellStatesWithWork n (bitWordValue spacing) side cell).1
  let test := fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
    (initial r).2 + (centerEligibilityWithWork b F a (initial r).1).2)
  have hs := seedGridSpacingAllocation_le_work b P
  have hm := canonicalMulAllocation_le_work theta (nat b)
  have hg := cellStatesAllocation_le_work n (bitWordValue spacing) side cell
  have hf := filterAllocation_le_work test (fun r => allocation r + centerEligibilityAllocation b F a (initial r).1)
    states (fun r _ => Nat.add_le_add (h r) (centerEligibilityAllocation_le_work b F a (initial r).1))
  unfold cellCentersReadAllocation cellCentersReadWithWork
  dsimp only [spacing, side, states, test] at hg hf ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryContinuationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem endpointActionAllocation_le_work {ny M : ℕ} (center : TargetInterval ny)
    (states : Fin M → TargetInterval ny) :
    endpointActionAllocation center states ≤ (endpointActionWithWork center states).2 := by
  have h := endpointConnectionAllocation_le_work center states
  unfold endpointActionAllocation endpointActionWithWork
  dsimp only
  omega



theorem wideActionsFromRepresentativesAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    wideActionsFromRepresentativesAllocation M parent representatives P ≤
      (wideActionsFromRepresentativesWithWork M parent representatives P).2 := by
  apply arithmeticFlatMapAllocation_le_work
  intro br _
  have hw := wideActionGridAllocation_le_work M parent br.2 br.1 P
  have ha := arithmeticMapAllocation_le_work (fun states : Vector (TargetInterval ny) M => endpointActionWithWork br.2 states.get)
    (fun states => endpointActionAllocation br.2 states.get)
    (wideActionGridWithWork M parent br.2 br.1 P).1 (fun states _ => endpointActionAllocation_le_work br.2 states.get)
  dsimp only
  omega



theorem physicalContinuationReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ) (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Fin M × TargetInterval ny → ℕ)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny)
    (ho : ∀ input, oldAllocation input ≤ (old input).2)
    (hc : ∀ input, currentAllocation input ≤ (current input).2) :
    physicalContinuationReadAllocation parent representatives P F delta fallback old current oldAllocation currentAllocation groups online query ≤
      (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).2 := by
  have hw := wideActionsFromRepresentativesAllocation_le_work M parent representatives P
  have hl := canonicalMulAllocation_le_work (nat 128) (nat F)
  have hf := localContinuationReadAllocation_le_work endpointDistanceWithWork endpointDistanceAllocation
    (canonicalMulWithWork (nat 128) (nat F)).1 delta fallback old current oldAllocation currentAllocation query
    (wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online
    (endpointDistanceAllocation_le_work query) ho hc
  unfold physicalContinuationReadAllocation physicalContinuationReadWithWork
  dsimp only
  omega



theorem queryRefinementFinishAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ)
    (a delta : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (initialAllocation : TargetInterval ny → ℕ) (t : ℕ)
    (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
    (query : TargetInterval ny) (hi : ∀ r, initialAllocation r ≤ (initial r).2) :
    queryRefinementFinishAllocation parent N P F a delta initial initialAllocation t earlierKeys earlierWords
      groups online currentKeys currentWords query ≤
      (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online currentKeys currentWords query).2 := by
  have hq := hi query
  have hr := localRepresentativeReadAllocation_le_work N P F a initial initialAllocation query hi
  have hf := physicalContinuationReadAllocation_le_work parent (localRepresentativeReadWithWork N P F a initial query).1
    P F delta (initial query).1
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork currentKeys currentWords input.1 input.2)
    (queryHistoryReadAllocation earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadAllocation currentKeys currentWords input.1 input.2) groups online query
    (queryHistoryReadAllocation_le_work earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadAllocation_le_work currentKeys currentWords input.1 input.2)
  unfold queryRefinementFinishAllocation queryRefinementFinishWithWork
  dsimp only
  omega



theorem localWarmupReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (initialAllocation : TargetInterval ny → ℕ) (child : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (childAllocation : Fin M × TargetInterval ny → ℕ) (query : TargetInterval ny)
    (hi : ∀ r, initialAllocation r ≤ (initial r).2)
    (hc : ∀ input, childAllocation input ≤ (child input).2) :
    localWarmupReadAllocation parent N P F a initial initialAllocation child childAllocation query ≤
      (localWarmupReadKernelWithWork parent N P F a initial child query).2 := by
  have hq := hi query
  have hr := localRepresentativeReadAllocation_le_work N P F a initial initialAllocation query hi
  have hw := wideActionsFromRepresentativesAllocation_le_work M parent
    (localRepresentativeReadWithWork N P F a initial query).1 P
  have hl := canonicalMulAllocation_le_work (nat 128) (nat F)
  have hb := bellmanReadAllocation_le_work endpointDistanceWithWork endpointDistanceAllocation
    (canonicalMulWithWork (nat 128) (nat F)).1 (initial query).1 child childAllocation query
    (wideActionsFromRepresentativesWithWork M parent (localRepresentativeReadWithWork N P F a initial query).1 P).1
    (fun action _ => endpointDistanceAllocation_le_work query action.center)
    (fun action _ i => hc (action.childState i))
  unfold localWarmupReadAllocation localWarmupReadKernelWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupActionSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

def unskippedEstimateSourceAllocation (member : Member) : ℕ :=
  let mass := (envelopeVectorReadWithWork b member.actions initial).1
  let rounded := (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1
  let values := (vectorMapWithWork M (fun i => current i (rounded.get i))).1
  let connection := (endpointConnectionWithWork member.center rounded.get).1
  envelopeVectorReadAllocation b member.actions initial initialAllocation +
    roundedBandReadAllocation exponent b member.actions member.nonempty initial initialAllocation +
    vectorMapAllocation M (fun i => currentAllocation i (rounded.get i)) +
    endpointConnectionAllocation member.center rounded.get + countedGroupMemberSourceAllocation Q b scales connection mass values draw drawAllocation

theorem unskippedEstimateSourceAllocation_le_work (member : Member)
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    unskippedEstimateSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation member ≤
      (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw member).2 := by
  let mass := (envelopeVectorReadWithWork b member.actions initial).1
  let rounded := (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1
  let values := (vectorMapWithWork M (fun i => current i (rounded.get i))).1
  have he := envelopeVectorReadAllocation_le_work b member.actions initial initialAllocation (fun i action _ => hi i (action i))
  have hr := roundedBandReadAllocation_le_work exponent b member.actions member.nonempty initial initialAllocation hi
  have hv := vectorMapAllocation_le_work M (fun i => current i (rounded.get i))
    (fun i => currentAllocation i (rounded.get i)) (fun i => hc i (rounded.get i))
  have hg := endpointConnectionAllocation_le_work member.center rounded.get
  have hm := countedGroupMemberSourceAllocation_le_work Q b scales
    (endpointConnectionWithWork member.center rounded.get).1 mass values draw drawAllocation ha
  unfold unskippedEstimateSourceAllocation unskippedEstimateSourceWithWork
  dsimp only [mass, rounded, values] at hv hg hm ⊢
  omega

def chooseUnskippedSourceAllocation (members : List Member) : ℕ :=
  selectGroupAllocation members
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw)
    (unskippedEstimateSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation)

theorem chooseUnskippedSourceAllocation_le_work (members : List Member) (hne : members ≠ [])
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation members ≤
      (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current scales draw members hne).2 :=
  selectGroupAllocation_le_work members hne _ _ (fun member _ =>
    unskippedEstimateSourceAllocation_le_work source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation member hi hc ha)

def sampledGroupActionSourceAllocation (members : List Member) (hne : members ≠ []) : ℕ :=
  let selected := (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).1
  let rounded := (roundedBandReadWithWork exponent b selected.actions selected.nonempty initial).1
  chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
    initialAllocation currentAllocation scales draw drawAllocation members +
    roundedBandReadAllocation exponent b selected.actions selected.nonempty initial initialAllocation +
    endpointActionAllocation selected.center rounded.get

theorem sampledGroupActionSourceAllocation_le_work (members : List Member) (hne : members ≠ [])
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    sampledGroupActionSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation members hne ≤
      (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current scales draw members hne).2 := by
  let selected := (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).1
  have hs := chooseUnskippedSourceAllocation_le_work source target parent b P exponent Q tau F child initial current
    initialAllocation currentAllocation scales draw drawAllocation members hne hi hc ha
  have hr := roundedBandReadAllocation_le_work exponent b selected.actions selected.nonempty initial initialAllocation hi
  have ha := endpointActionAllocation_le_work selected.center
    (roundedBandReadWithWork exponent b selected.actions selected.nonempty initial).1.get
  unfold sampledGroupActionSourceAllocation sampledGroupActionSourceWithWork
  dsimp only [selected] at hr ha ⊢
  omega

end Group

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem bandFromActionsReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    bandFromActionsReadAllocation parent r b tau theta velocity read allocation actions hne ≤
      (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 := by
  have hm := subAllocation_le_work one tau
  have hg := leAllocation_le_work velocity.absolute (subWithWork one tau).1
  have hf := filterAllocation_le_work
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateReadAllocation parent r b tau theta velocity actions hne read allocation) actions
    (fun action _ => bandPredicateReadAllocation_le_work parent r b tau theta velocity actions hne read allocation action h)
  unfold bandFromActionsReadAllocation bandFromActionsReadWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact (Nat.add_le_add (Nat.add_le_add hm hg) hf).trans (Nat.le_add_right _ 2)
  · exact Nat.add_le_add (Nat.add_le_add hm hg) (Nat.zero_le 1)



theorem representativeFromActionsReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (actions : List (Fin M → TargetInterval ny))
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    representativeFromActionsReadAllocation parent r sourceLength b tau theta read allocation actions ≤
      (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 := by
  have costBound (z z' p p' g g' d d' b b' : ℕ)
      (hz : z ≤ z') (hp : p ≤ p') (hg : g ≤ g') (hd : d ≤ d') (hb : b ≤ b') :
      z + p + (g + d + b) ≤ z' + p' + g' + d' + b' + 3 := by
    omega
  unfold representativeFromActionsReadAllocation representativeFromActionsReadWithWork
  by_cases hne : actions = []
  · simp only [hne, ↓reduceDIte, Nat.zero_le]
  · simp only [hne, ↓reduceDIte]
    have hz := wideMinimumReadAllocation_le_work r read allocation actions hne h
    have hp := ltAllocation_le_work zero (wideMinimumReadWithWork r read actions hne).1
    have hg := stateGapAllocation_le_work sourceLength r
    have hd := divAllocation_le_work (stateGapWithWork sourceLength r).1
      (wideMinimumReadWithWork r read actions hne).1
    have hb := bandFromActionsReadAllocation_le_work parent r b tau theta
      (divWithWork (stateGapWithWork sourceLength r).1 (wideMinimumReadWithWork r read actions hne).1).1
      read allocation actions hne h
    split_ifs <;> dsimp only
    · exact costBound _ _ _ _ _ _ _ _ _ _ hz hp hg hd hb
    · exact Nat.add_le_add (Nat.add_le_add hz hp) (by decide : 0 ≤ 2)



theorem preparedRepresentativeReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    preparedRepresentativeReadAllocation parent center sourceLength b P tau theta read allocation ≤
      (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).2 := by
  have hw := wideActionGridAllocation_le_work M parent center b P
  have hr := representativeFromActionsReadAllocation_le_work parent center sourceLength b tau theta read allocation
    ((wideActionGridWithWork M parent center b P).1.map Vector.get) (fun _ _ i => h i _)
  unfold preparedRepresentativeReadAllocation preparedRepresentativeReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem gapGuardAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (envelope : Vector BinaryFraction M) (rounded : Vector (TargetInterval ny) M) (i : Fin M) :
    gapGuardAllocation parent envelope rounded i ≤
      (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).2 +
      (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
        (sourceChild parent i).lo).1) (rounded.get i)).2 +
      (canonicalMulWithWork (nat 2) (envelope.get i)).2 +
      (leWithWork (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
        (sourceChild parent i).lo).1) (rounded.get i)).1.absolute
        (canonicalMulWithWork (nat 2) (envelope.get i)).1).2 + 3 := by
  have hs := bitSubtractAllocation_le_work (sourceChild parent i).hi.bits (sourceChild parent i).lo.bits false
  have hg := stateGapAllocation_le_work
    (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).1)
    (rounded.get i)
  have hm := canonicalMulAllocation_le_work (nat 2) (envelope.get i)
  have hl := leAllocation_le_work
    (stateGapWithWork (bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi
      (sourceChild parent i).lo).1) (rounded.get i)).1.absolute
    (canonicalMulWithWork (nat 2) (envelope.get i)).1
  unfold gapGuardAllocation
  dsimp only
  have hs' : bitSubtractAllocation (sourceChild parent i).hi.bits (sourceChild parent i).lo.bits false ≤
      (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).2 := hs
  omega



theorem unskippedGuardReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    unskippedGuardReadAllocation parent center b exponent F band wide hne read allocation ≤
      (unskippedGuardReadWithWork parent center b exponent F band wide hne read).2 := by
  let envelope := (envelopeVectorReadWithWork b band read).1
  let rounded := (roundedBandReadWithWork exponent b band hne read).1
  have he := envelopeVectorReadAllocation_le_work b band read allocation (fun i action _ => h i (action i))
  have ht := bandMassAllocation_le_work envelope
  have hf := canonicalMulAllocation_le_work F (nat b)
  have hl := canonicalMulAllocation_le_work (nat 64) (canonicalMulWithWork F (nat b)).1
  have hs := leAllocation_le_work (bandMassTotalWithWork envelope).1
    (canonicalMulWithWork (nat 64) (canonicalMulWithWork F (nat b)).1).1
  have hr := roundedBandReadAllocation_le_work exponent b band hne read allocation h
  have hw := actionMemberAllocation_le_work rounded.get wide
  have hg := allAllocation_le_work (fun i =>
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.get i)
    let test := leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3))
    (gapGuardAllocation parent envelope rounded) (List.finRange M)
    (fun i _ => gapGuardAllocation_le_work parent envelope rounded i)
  unfold unskippedGuardReadAllocation unskippedGuardReadWithWork
  dsimp only [envelope, rounded] at ht hs hw hg ⊢
  omega



theorem preparedUnskippedReadAllocation_le_work {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P) (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (readAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (ha : ∀ i q, readAllocation i q ≤ (read i q).2)
    (hinit : ∀ i q, initialAllocation i q ≤ (initial i q).2) :
    preparedUnskippedReadAllocation parent center b P exponent tau F read initial readAllocation initialAllocation ≤
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 := by
  have costBound (a a' w w' g g' l k k' : ℕ)
      (ha : a ≤ a') (hw : w ≤ w') (hg : g ≤ g') (hk : k ≤ k') :
      a + (w + l + g + k) ≤ a' + w' + g' + l + k' := by
    omega
  have hbnd := preparedRepresentativeReadAllocation_le_work parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) read readAllocation ha
  have hw := wideActionGridAllocation_le_work M parent center b P
  unfold preparedUnskippedReadAllocation preparedUnskippedReadWithWork
  dsimp only
  split_ifs with hband hguard
  · exact Nat.add_le_add hbnd (by decide : 0 ≤ 1)
  · have hg := unskippedGuardReadAllocation_le_work parent center b exponent F
      (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) read).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hband initial initialAllocation hinit
    dsimp only
    exact costBound _ _ _ _ _ _ _ 3 3 hbnd hw hg (Nat.le_refl _)
  · have hg := unskippedGuardReadAllocation_le_work parent center b exponent F
      (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) read).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hband initial initialAllocation hinit
    dsimp only
    exact costBound _ _ _ _ _ _ _ 0 2 hbnd hw hg (by decide : 0 ≤ 2)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Cell
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R C : ℕ) (hr : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b (nat F).value)
  (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)

def preparedCellGroupSourceAllocation (cell : ℕ × ℕ) : ℕ :=
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  let members := (filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers).1
  cellCentersReadAllocation P F b a (inversePowerTwo exponent) parentInitial parentAllocation cell +
    filterMapAllocation (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi)
      (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation) centers +
    if hempty : members = [] then 0 else
      sampledGroupActionSourceAllocation source target parent b P exponent Q tau (nat F)
        (fun i q => (child i q).1) initial current initialAllocation currentAllocation
        (indexedGroupScales raw M b (nat F).value hraw)
        (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
          (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
        (fun t j => drawAllocation t (Fin.cast (congrArg (groupSampleCount M Q b)
          (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members hempty + 1

theorem preparedCellGroupSourceAllocation_le_work (cell : ℕ × ℕ)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hc : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hin : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    preparedCellGroupSourceAllocation source target parent b P F exponent Q hb hP tau a
      parentInitial child initial current R C hr hi raw hraw draw
      parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell ≤
      (preparedCellGroupSourceWithWork source target parent b P F exponent Q hb hP tau a
        parentInitial child initial current R C hr hi raw hraw draw cell).2 := by
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  let members := (filterMapWithWork
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi) centers).1
  have hcenters := cellCentersReadAllocation_le_work P F b a (inversePowerTwo exponent)
    parentInitial parentAllocation cell hp
  have hmembers := filterMapAllocation_le_work
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R C hr hi)
    (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
      child initial childAllocation initialAllocation) centers
    (fun center _ => preparedUnskippedReadAllocation_le_work source target parent center b P exponent
      hb hP tau (nat F) child initial childAllocation initialAllocation R C hr hi hc hin)
  dsimp only [centers] at hmembers
  unfold preparedCellGroupSourceAllocation preparedCellGroupSourceWithWork
  dsimp only
  split_ifs with hempty
  · exact Nat.add_le_add (Nat.add_le_add hcenters hmembers) (by decide : 0 ≤ 1)
  · have hsample := sampledGroupActionSourceAllocation_le_work source target parent b P exponent Q
      tau (nat F) (fun i q => (child i q).1) initial current initialAllocation currentAllocation
      (indexedGroupScales raw M b (nat F).value hraw)
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j))
      (fun t j => drawAllocation t (Fin.cast (congrArg (groupSampleCount M Q b)
        (indexedGroupScales_value raw M b (nat F).value hraw t)) j)) members hempty hin hcur
      (fun t j => hd t _)
    dsimp only [centers, members] at hmembers hsample
    exact (Nat.add_assoc _ _ _).symm.le.trans
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcenters hmembers) hsample)
        (by decide : 1 ≤ 2))

end Cell
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The online objective includes every repeated history-buffer read.
Its allocation and frame counters follow the same Boolean arithmetic and
materialized vector passes as the executed continuation. -/

namespace EditApproximation.BinaryFraction



theorem coefficientAllocation_le_work (kappa : BinaryFraction) :
    coefficientAllocation kappa ≤ (coefficientWithWork kappa).2 := by
  have h1 := canonicalMulAllocation_le_work (nat 2) kappa
  have h2 := subAllocation_le_work one (canonicalMulWithWork (nat 2) kappa).1
  unfold coefficientAllocation coefficientWithWork
  dsimp only
  omega



theorem gainReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2) :
    gainReadAllocation mass read footprint s i ≤ (gainReadWithWork mass read s i).2 := by
  have hd := divAllocation_le_work (read s i).1.neg (mass i.1)
  unfold gainReadAllocation gainReadWithWork
  dsimp only
  omega



theorem decrementReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (s : ℕ) (i : β × σ) (h : footprint s i ≤ (read s i).2)
    (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    decrementReadAllocation mass read footprint s i ≤ (decrementReadWithWork mass read s i).2 := by
  have hs := subAllocation_le_work (read s i).1 (read (s + 1) i).1
  have hd := divAllocation_le_work (subWithWork (read s i).1 (read (s + 1) i).1).1 (mass i.1)
  unfold decrementReadAllocation decrementReadWithWork
  dsimp only
  omega



theorem optimisticTermReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (coefficient : BinaryFraction) (s : ℕ) (i : β × σ)
    (h : footprint s i ≤ (read s i).2) (hnext : footprint (s + 1) i ≤ (read (s + 1) i).2) :
    optimisticTermReadAllocation mass read footprint coefficient s i ≤
      (optimisticTermReadWithWork mass read coefficient s i).2 := by
  have hg := gainReadAllocation_le_work mass read footprint s i h
  have hd := decrementReadAllocation_le_work mass read footprint s i h hnext
  have hm := canonicalMulAllocation_le_work coefficient (decrementReadWithWork mass read s i).1
  have ha := canonicalAddAllocation_le_work (gainReadWithWork mass read s i).1
    (canonicalMulWithWork coefficient (decrementReadWithWork mass read s i).1).1
  unfold optimisticTermReadAllocation optimisticTermReadWithWork
  dsimp only
  omega



theorem onlineLinearReadAllocation_le_work {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (eta kappa : BinaryFraction) (t : ℕ) (i : β × σ)
    (h : ∀ s ≤ t + 1, footprint s i ≤ (read s i).2) :
    onlineLinearReadAllocation mass read footprint eta kappa t i ≤
      (onlineLinearReadWithWork mass read eta kappa t i).2 := by
  have hc := coefficientAllocation_le_work kappa
  have ht := vectorMapAllocation_le_work t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadAllocation mass read footprint (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermReadAllocation_le_work mass read footprint _ s.val i
      (h _ (by omega)) (h _ (by omega)))
  let terms := (vectorMapWithWork t fun s =>
    optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i).1
  have hh := bandMassAllocation_le_work terms
  have hg := gainReadAllocation_le_work mass read footprint t i (h _ (by omega))
  have ha := canonicalAddAllocation_le_work (bandMassTotalWithWork terms).1 (gainReadWithWork mass read t i).1
  have hm := canonicalMulAllocation_le_work eta (canonicalAddWithWork (bandMassTotalWithWork terms).1
    (gainReadWithWork mass read t i).1).1
  unfold onlineLinearReadAllocation onlineLinearReadWithWork
  dsimp only
  dsimp only [terms] at hh ha hm
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySelectionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

theorem scoredArgmaxWithWork_count {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    values.length ≤ (scoredArgmaxWithWork score values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons value rest ih =>
    simp only [scoredArgmaxWithWork, List.length_cons]
    split <;> dsimp only <;> omega

/-- Includes the pointer list passed to the optimizer, then the final
label-preserving gradient and maximum scan. -/


theorem selectionAllocation_le_work {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G j : ℕ) :
    selectionAllocation vertices linear G j ≤ 2 * (selectionWithWork vertices linear G j).2 := by
  let iterate := (finiteOptimizerWithWork (vertices.map Prod.snd) linear G j).1
  let gradient := (gradientWithWork G linear iterate).1
  have hi := optimizerAllocation_le_work (vertices.map Prod.snd) linear G j
  have hg := gradientAllocation_le_work G linear iterate
  have hs := scoredArgmaxAllocation_le_work (fun vertex : α × Vector BinaryFraction d =>
    dotWithWork gradient vertex.2) (fun vertex => dotListAllocation gradient vertex.2 (List.finRange d)) vertices
    (fun vertex _ => dotListAllocation_le_work gradient vertex.2 (List.finRange d))
  have hn := scoredArgmaxWithWork_count (fun vertex : α × Vector BinaryFraction d => dotWithWork gradient vertex.2) vertices
  unfold selectionAllocation selectionWithWork
  dsimp only [iterate, gradient] at hi hg hs hn ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedOptimizerSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem countedBandCoordinateAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (total : BinaryFraction) (action : Fin M → TargetInterval n) (coordinate : Fin M × TargetInterval n) :
    countedBandCoordinateAllocation mass total action coordinate ≤
      (countedBandCoordinateWithWork mass total action coordinate).2 := by
  have hc := coordinateEqualAllocation_le_work coordinate (coordinate.1, action coordinate.1)
  have hd := divAllocation_le_work (mass.get coordinate.1) total
  unfold countedBandCoordinateAllocation countedBandCoordinateWithWork
  dsimp only
  split_ifs <;> (try dsimp only) <;> omega



theorem countedBandVerticesAllocation_le_work {M n d : ℕ} (coordinates : Vector (Fin M × TargetInterval n) d)
    (mass : Vector BinaryFraction M) (band : List (Fin M → TargetInterval n)) :
    countedBandVerticesAllocation coordinates mass band ≤ (countedBandVerticesWithWork coordinates mass band).2 := by
  have hm := bandMassAllocation_le_work mass
  have hs : (band.map fun action => vectorMapAllocation d fun i =>
      countedBandCoordinateAllocation mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum ≤
      (band.map fun action => (vectorMapWithWork d fun i =>
        countedBandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).2).sum := by
    induction band with
    | nil => simp
    | cons a rest ih =>
      have h := vectorMapAllocation_le_work d
        (fun i => countedBandCoordinateWithWork mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => countedBandCoordinateAllocation mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => countedBandCoordinateAllocation_le_work _ _ _ _)
      simp only [List.map_cons, List.sum_cons]
      omega
  unfold countedBandVerticesAllocation countedBandVerticesWithWork
  simp only [List.map_map, Function.comp_def]
  omega

/-- Arithmetic and labeled-vector allocation after coordinate construction.
Coordinate construction itself is accounted by its separate list allocator. -/


theorem countedPreparedActionKernelAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (h : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedPreparedActionKernelAllocation mass read footprint eta kappa band G j t ≤
      2 * (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
  let coordinates := (coordinateVectorWithWork band).1
  have hv := countedBandVerticesAllocation_le_work coordinates mass band
  have hl := vectorMapAllocation_le_work _
    (fun i => onlineLinearReadWithWork (fun child => mass.get child) read eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation (fun child => mass.get child) read footprint eta kappa t (coordinates.get i))
    (fun i => onlineLinearReadAllocation_le_work _ _ _ _ _ _ _ (fun s _ => h s _))
  have hs := selectionAllocation_le_work (countedBandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork _ fun i => onlineLinearReadWithWork (fun child => mass.get child)
      read eta kappa t (coordinates.get i)).1 G j
  unfold countedPreparedActionKernelAllocation countedPreparedActionReadWithWork
  dsimp only [coordinates] at hv hl hs ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCountedActionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

/-- All counted optimizer allocations, including coordinate construction. -/


theorem countedPreparedActionAllocation_le_work {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (h : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedPreparedActionAllocation mass read footprint eta kappa band G j t ≤
      3 * (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
  have hc := coordinateVectorAllocation_le_work band
  have hk := countedPreparedActionKernelAllocation_le_work mass read footprint eta kappa band G j t h
  have hlocal : (coordinateVectorWithWork band).2 ≤
      (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 := by
    unfold countedPreparedActionReadWithWork
    dsimp only
    omega
  unfold countedPreparedActionAllocation
  omega



theorem countedBandActionAllocation_le_work {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (initialAllocation : Fin M → TargetInterval n → ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ)
    (hi : ∀ i state, initialAllocation i state ≤ (initial i state).2)
    (hr : ∀ s coordinate, footprint s coordinate ≤ (read s coordinate).2) :
    countedBandActionAllocation b initial initialAllocation read footprint eta kappa band G j t ≤
      3 * (countedBandActionReadWithWork b initial read eta kappa band G j t).2 := by
  have he := envelopeVectorReadAllocation_le_work b band initial initialAllocation (fun i action _ => hi i (action i))
  have hc := countedPreparedActionAllocation_le_work (envelopeVectorReadWithWork b band initial).1
    read footprint eta kappa band G j t hr
  unfold countedBandActionAllocation countedBandActionReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery



def keys {ι β : Type*} (oracle : ι → BinaryFraction) : BitQuery ι β → List ι
  | .done _ => []
  | .read key next => key :: keys oracle (next (oracle key))
  | .charge _ next => keys oracle next





/-- Branches of the reference query are selected only by the values of
answers actually read. The relation can therefore be composed stage by stage. -/
inductive Refines {ι β : Type*} (relation : β → ℚ → Prop) :
    BitQuery ι β → FiniteQuery ι → Prop where
  | done {result : β} {expected : ℚ} (h : relation result expected) :
      Refines relation (.done result) (.done expected)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β) (expected : ℚ → FiniteQuery ι)
      (h : ∀ word, Refines relation (next word) (expected word.value)) :
      Refines relation (.read key next) (.read key expected)
  | charge (steps : ℕ) {program : BitQuery ι β} {expected : FiniteQuery ι}
      (h : Refines relation program expected) : Refines relation (.charge steps program) expected

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoMap
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof-only view of a binary-word memo as its rational-value memo.
The tree shape and every lookup/insertion path are preserved. -/

namespace EditApproximation
namespace BinaryMemo

def mapValues {α β : Type*} (f : α → β) : BinaryMemo α → BinaryMemo β
  | .empty => .empty
  | .node v l r => .node (v.map f) (mapValues f l) (mapValues f r)

@[simp] theorem mapValues_value {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).value = tree.value.map f := by cases tree <;> rfl

@[simp] theorem mapValues_left {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).left = tree.left.mapValues f := by cases tree <;> rfl

@[simp] theorem mapValues_right {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).right = tree.right.mapValues f := by cases tree <;> rfl

@[simp] theorem mapValues_lookup {α β : Type*} (f : α → β) (tree : BinaryMemo α) (key : List Bool) :
    (tree.mapValues f).lookup key = (tree.lookup key).map f := by
  induction key generalizing tree with
  | nil => exact mapValues_value f tree
  | cons bit rest ih => cases bit <;> simp only [lookup, mapValues_left, mapValues_right, ih]

@[simp] theorem mapValues_insert {α β : Type*} (f : α → β) (tree : BinaryMemo α)
    (key : List Bool) (value : α) :
    (tree.insert key value).mapValues f = (tree.mapValues f).insert key (f value) := by
  induction key generalizing tree with
  | nil => simp only [insert, mapValues, mapValues_left, mapValues_right, Option.map_some]
  | cons bit rest ih =>
    cases bit <;> simp only [insert, mapValues, ih, mapValues_value, mapValues_left, mapValues_right]

@[simp] theorem mapValues_nodes {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).nodes = tree.nodes := by
  induction tree with
  | empty => rfl
  | node v l r ihl ihr => simp only [mapValues, nodes, ihl, ihr]

end BinaryMemo
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Execution of charged adaptive queries on actual binary-word memos.
The rational view is used only to prove preservation of the
memo trace; Boolean local work is retained as an additional counter. -/

namespace EditApproximation



def BitRecursiveMemoResult.decode {κ : Type*} (result : BitRecursiveMemoResult κ) :
    RecursiveMemoResult κ :=
  ⟨result.value.value, result.memory.mapValues BinaryFraction.value,
    result.freshKeys, result.dictionaryVisits, result.requests⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simulation along a fixed reachable oracle. This allows a checked
normalization at the end of a local query: its denominator invariant is
required only for the values that the ranked execution actually reaches. -/

namespace EditApproximation.BitQuery

inductive RefinesOn {ι β : Type*} (oracle : ι → BinaryFraction) (relation : β → ℚ → Prop) :
    BitQuery ι β → FiniteQuery ι → Prop where
  | done {result : β} {expected : ℚ} (h : relation result expected) :
      RefinesOn oracle relation (.done result) (.done expected)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β) (expected : ℚ → FiniteQuery ι)
      (h : RefinesOn oracle relation (next (oracle key)) (expected (oracle key).value)) :
      RefinesOn oracle relation (.read key next) (.read key expected)
  | charge (steps : ℕ) {program : BitQuery ι β} {expected : FiniteQuery ι}
      (h : RefinesOn oracle relation program expected) :
      RefinesOn oracle relation (.charge steps program) expected

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuerySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Allocation annotations for the actual adaptive query. Charge annotations
carry the concrete routine's allocation bound; reads reserve three cells for
its suspended continuation and result pointer. Charge transitions are tail
transitions. Summing all allocations bounds simultaneously live cells even
if no temporary cell is reclaimed until the query returns. -/

namespace EditApproximation.BitQuery

inductive Heap {ι β : Type*} : BitQuery ι β → Type _ where
  | done (value : β) : Heap (.done value)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β)
      (continuation : ∀ word, Heap (next word)) : Heap (.read key next)
  | charge {steps : ℕ} {next : BitQuery ι β} (cells : ℕ)
      (bound : cells ≤ 3 * steps) (continuation : Heap next) : Heap (.charge steps next)

namespace Heap

def cells {ι β : Type*} {program : BitQuery ι β} (oracle : ι → BinaryFraction) : Heap program → ℕ
  | .done _ => 0
  | .read key _ next => 3 + cells oracle (next (oracle key))
  | .charge localCells _ next => localCells + cells oracle next

def bind {ι α β : Type*} {program : BitQuery ι α} (heap : Heap program)
    (next : α → BitQuery ι β) (allocation : ∀ value, Heap (next value)) : Heap (program.bind next) :=
  match heap with
  | .done result => allocation result
  | .read key continuation stored => .read key _ (fun word => (stored word).bind next allocation)
  | .charge localCells bound tail => .charge localCells bound (tail.bind next allocation)

def compute {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ 3 * execution.2) : Heap (BitQuery.compute (ι := ι) execution) :=
  .charge allocation bound (.done execution.1)

def chargeOf {ι β : Type*} {steps : ℕ} {program : BitQuery ι β} (allocation : ℕ)
    (bound : allocation ≤ steps) (tail : Heap program) : Heap (.charge steps program) :=
  .charge allocation (by omega) tail

def computeOf {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ execution.2) : Heap (BitQuery.compute (ι := ι) execution) :=
  compute execution allocation (by omega)

def collect {ι κ β : Type*} (reader : κ → BitQuery ι BinaryFraction)
    (allocation : ∀ key, Heap (reader key)) :
    (inputs : List κ) → (next : List BinaryFraction → BitQuery ι β) →
      (∀ words, Heap (next words)) → Heap (BitQuery.collect reader inputs next)
  | [], _, continuation => continuation []
  | key :: rest, next, continuation =>
    (allocation key).bind _ fun word => .charge 1 (by decide)
      (collect reader allocation rest (fun words => next (word :: words))
        (fun words => continuation (word :: words)))

end Heap
end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryTriangularSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem triangularMassAllocation_le_work (K : ℕ) :
    triangularMassAllocation K ≤ (triangularMassWithWork K).2 := by
  have ha := bitAddAllocation_le_work K.bits (1 : ℕ).bits false
  have hm := bitMulAllocation_le_work K.bits (bitWordValue (binaryNaturalAddWithWork K 1).1).bits
  have hd := bitDivModAllocation_le_work (2 : ℕ).bits
    (bitWordValue (binaryNaturalMulWithWork K (bitWordValue (binaryNaturalAddWithWork K 1).1)).1).bits
  unfold triangularMassAllocation triangularMassWithWork binaryNaturalAddWithWork
    binaryNaturalMulWithWork binaryNaturalDivModWithWork at *
  dsimp only at *
  omega

/-- Allocate the exact threshold words visited by the triangular sampler.
The sampled integer and thresholds are already bounded finite words. -/


theorem triangularChoiceAllocation_le_work (K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    triangularChoiceAllocation K integer ≤ (triangularChoiceWithWork K integer).2 := by
  induction K with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    have ht := triangularMassAllocation_le_work K
    have hc := bitCompareWithWork_input_cells integer.val.bits
      (bitWordValue (triangularMassWithWork K).1).bits
    change _ ≤ (binaryNaturalCompareWithWork integer.val (bitWordValue (triangularMassWithWork K).1)).2 at hc
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      let localCells := triangularMassAllocation K + integer.val.bits.length +
        (bitWordValue threshold.1).bits.length
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using hp
        localCells + triangularChoiceAllocation K ⟨integer.val, hsmall⟩
      else localCells) ≤
      (let threshold := triangularMassWithWork K
       let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
       if h : test.1 = .lt then
         let hsmall : integer.val < optimizerTriangularMass K := by
           have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
           simpa only [threshold, triangularMassWithWork_value] using hp
         let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
         (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
       else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).2
    dsimp only
    split_ifs with h
    · have hsmall : integer.val < optimizerTriangularMass K := by
        have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
        simpa only [triangularMassWithWork_value] using hp
      have hnext := ih ⟨integer.val, hsmall⟩
      dsimp only
      exact (Nat.add_le_add
        ((Nat.add_assoc _ _ _).le.trans (Nat.add_le_add ht hc)) hnext).trans
        (Nat.le_add_right _ 2)
    · dsimp only
      exact ((Nat.add_assoc _ _ _).le.trans (Nat.add_le_add ht hc)).trans (Nat.le_succ _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineRangeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem onlineIndexSetupAllocation_le_work {M n : ℕ} (H : ℕ) (band : List (Fin M → TargetInterval n)) :
    onlineIndexSetupAllocation H band ≤ (onlineIndexSetupWithWork H band).2 := by
  have hc := bandCoordinatesAllocation_le_work band
  have hs := binaryNaturalAddAllocation_le_work H (bandCoordinatesWithWork band).1.length
  have ho := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalAddWithWork H
    (bandCoordinatesWithWork band).1.length).1) 2
  have hp := bitPowerAllocation_le_work (binaryNaturalAddWithWork
    (bitWordValue (binaryNaturalAddWithWork H (bandCoordinatesWithWork band).1.length).1) 2).1 80
  unfold onlineIndexSetupAllocation onlineIndexSetupWithWork
  dsimp only
  omega



theorem queryOnlineRangeAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (P exponent H : ℕ) (tau : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (key : ℕ × TargetInterval ny)
    (h : ∀ i q, allocation i q ≤ (child i q).2) :
    queryOnlineRangeAllocation parent P exponent H tau child allocation key ≤
      (queryOnlineRangeWithWork parent P exponent H tau child key).2 := by
  let width := (saturatingSubtractWithWork parent.hi parent.lo).1
  let band := (preparedRepresentativeReadWithWork parent key.2 (bitWordValue width) key.1 P
    tau (inversePowerTwo exponent) child).1
  let setup := (onlineIndexSetupWithWork H band).1
  have hw := saturatingSubtractAllocation_le_work parent.hi parent.lo
  have hb := preparedRepresentativeReadAllocation_le_work parent key.2 (bitWordValue width) key.1 P
    tau (inversePowerTwo exponent) child allocation h
  have hs := onlineIndexSetupAllocation_le_work H band
  have hp := bitPowerAllocation_le_work setup.bits 80
  have hm := triangularMassAllocation_le_work (bitWordValue (bitPowerWithWork setup.bits 80).1)
  unfold queryOnlineRangeAllocation queryOnlineRangeWithWork
  dsimp only [width, band, setup] at hb hs hp hm ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryNormalizationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem powerDenominatorAllocation_le_work (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n : ℕ) :
    powerDenominatorAllocation a base hbase n ≤ (powerDenominatorWithWork a base hbase n).2 := by
  have hp := bitPowerAllocation_le_work base n
  have hf := fixedDenominatorAllocation_le_work a (bitPowerWithWork base n).1
    (by rw [bitPowerWithWork_value]; exact Nat.pow_pos hbase)
  unfold powerDenominatorAllocation powerDenominatorWithWork
  dsimp only
  omega



theorem finishCachedAllocation_le_work (raw : BinaryFraction × ℕ) (allocation : ℕ)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) (ha : allocation ≤ raw.2) :
    finishCachedAllocation raw allocation base hbase remaining ≤ (finishCachedWithWork raw base hbase remaining).2 := by
  have hp := powerDenominatorAllocation_le_work raw.1 base hbase remaining
  unfold finishCachedAllocation finishCachedWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

namespace EditApproximation.BitQuery.Heap

def normalize {ι : Type*} {program : BitQuery ι BinaryFraction} (heap : Heap program)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) :
    Heap (program.normalize base hbase remaining) :=
  heap.bind _ fun word => computeOf (BinaryFraction.finishCachedWithWork (word, 0) base hbase remaining)
    (BinaryFraction.finishCachedAllocation (word, 0) 0 base hbase remaining)
    (BinaryFraction.finishCachedAllocation_le_work (word, 0) 0 base hbase remaining le_rfl)

end EditApproximation.BitQuery.Heap

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialGuardSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem dyadicScalesAllocation_le_work (N : ℕ) :
    dyadicScalesAllocation N ≤ (dyadicScalesWithWork N).2 := by
  have h := arithmeticMapAllocation_le_work
    (fun e => (bitWordValue (powerTwoWord e), e + 3)) (fun e => e + 1)
    (List.range (max 1 N.bits.length)) (fun _ _ => by dsimp only; omega)
  unfold dyadicScalesAllocation dyadicScalesWithWork
  dsimp only
  omega

namespace BinaryFraction



theorem initialScaleGuardAllocation_le_work (U b : ℕ) (A : BinaryFraction) :
    initialScaleGuardAllocation U b A ≤ (initialScaleGuardWithWork U b A).2 := by
  have h1 := canonicalMulAllocation_le_work A A
  have h2 := canonicalMulAllocation_le_work (nat 16) (canonicalMulWithWork A A).1
  have h3 := divAllocation_le_work (nat U) (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1
  have h4 := canonicalMulAllocation_le_work (nat 4) A
  have h5 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 4) A).1 (nat U)
  have h6 := leAllocation_le_work (divWithWork (nat U) (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1).1 (nat b)
  have h7 := leAllocation_le_work (nat b) (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat U)).1
  unfold initialScaleGuardAllocation initialScaleGuardWithWork
  dsimp only
  omega



theorem initialCenterGuardAllocation_le_work (b U : ℕ) (A : BinaryFraction) :
    initialCenterGuardAllocation b U A ≤ (initialCenterGuardWithWork b U A).2 := by
  have h1 := divAllocation_le_work (nat b) (nat 2)
  have h2 := canonicalMulAllocation_le_work (nat 4) A
  have h3 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 4) A).1 (nat b)
  have h4 := leAllocation_le_work (divWithWork (nat b) (nat 2)).1 (nat U)
  have h5 := leAllocation_le_work (nat U) (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat b)).1
  unfold initialCenterGuardAllocation initialCenterGuardWithWork
  dsimp only
  omega



theorem scaledSeedAllocation_le_work (U : ℕ) (a gap : BinaryFraction) :
    scaledSeedAllocation U a gap ≤ (scaledSeedWithWork U a gap).2 := by
  have hd := divAllocation_le_work (nat U) a
  have hc := naturalCeilingAllocation_le_work (divWithWork (nat U) a).1
  have hm := maxAllocation_le_work (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1) gap.absolute
  unfold scaledSeedAllocation scaledSeedWithWork
  dsimp only
  omega



theorem initialConeAllocation_le_work {n : ℕ} (sourceLength U : ℕ) (a L : BinaryFraction)
    (query center : TargetInterval n) :
    initialConeAllocation sourceLength U a L query center ≤
      (initialConeWithWork sourceLength (fun _ => U) a L query center).2 := by
  have h1 := stateGapAllocation_le_work sourceLength center
  have h2 := scaledSeedAllocation_le_work U a (stateGapWithWork sourceLength center).1
  have h3 := endpointDistanceAllocation_le_work query center
  have h4 := canonicalMulAllocation_le_work L (endpointDistanceWithWork query center).1
  have h5 := canonicalAddAllocation_le_work (scaledSeedWithWork U a (stateGapWithWork sourceLength center).1).1
    (canonicalMulWithWork L (endpointDistanceWithWork query center).1).1
  unfold initialConeAllocation initialConeWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryInitialReadSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

section Reads
variable {n : ℕ} (read : TargetInterval n → List Bool × ℕ) (allocation : TargetInterval n → ℕ)



theorem initialGridReadAllocation_le_work (P : ℕ) (A : BinaryFraction) (radius : ℕ) (q : TargetInterval n) (b : ℕ)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialGridReadAllocation read allocation P A radius q b ≤ (initialGridReadWithWork P A read radius q b).2 := by
  let spacing := (seedGridSpacingWithWork b P).1
  have hs := seedGridSpacingAllocation_le_work b P
  have hg := gridStateBoxAllocation_le_work n (bitWordValue spacing) radius q.lo q.hi
  have hf := filterAllocation_le_work
    (fun r => ((initialCenterGuardWithWork b (bitWordValue (read r).1) A).1,
      (initialCenterGuardWithWork b (bitWordValue (read r).1) A).2 + (read r).2))
    (fun r => initialCenterGuardAllocation b (bitWordValue (read r).1) A + allocation r)
    (gridStateBoxWithWork n (bitWordValue spacing) radius q.lo q.hi).1
    (fun r _ => Nat.add_le_add (initialCenterGuardAllocation_le_work b (bitWordValue (read r).1) A) (ha r))
  unfold initialGridReadAllocation initialGridReadWithWork
  dsimp only [spacing] at hg hf ⊢
  omega



theorem initialCentersReadAllocation_le_work (N P : ℕ) (A : BinaryFraction) (q : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialCentersReadAllocation read allocation N P A q ≤ (initialCentersReadWithWork N P A read q).2 := by
  let Uq := bitWordValue (read q).1
  have hq := ha q
  have hd := dyadicScalesAllocation_le_work N
  have hf := filterAllocation_le_work (fun b => initialScaleGuardWithWork Uq b A)
    (fun b => initialScaleGuardAllocation Uq b A) (dyadicScalesWithWork N).1
    (fun b _ => initialScaleGuardAllocation_le_work Uq b A)
  have hm := arithmeticFlatMapAllocation_le_work (initialGridReadWithWork P A read Uq q)
    (initialGridReadAllocation read allocation P A Uq q)
    (filterWithWork (fun b => initialScaleGuardWithWork Uq b A) (dyadicScalesWithWork N).1).1
    (fun b _ => initialGridReadAllocation_le_work read allocation P A Uq q b ha)
  unfold initialCentersReadAllocation initialCentersReadWithWork
  dsimp only [Uq] at hf hm ⊢
  omega



theorem initialConeReadAllocation_le_work (sourceLength : ℕ) (a L : BinaryFraction) (query center : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialConeReadAllocation read allocation sourceLength a L query center ≤
      (initialConeReadWithWork sourceLength read a L query center).2 := by
  have hr := ha center
  have hc := initialConeAllocation_le_work sourceLength (bitWordValue (read center).1) a L query center
  unfold initialConeReadAllocation initialConeReadWithWork
  dsimp only
  omega



theorem initialMinimumReadAllocation_le_work (sourceLength N F : ℕ) (a : BinaryFraction)
    (query : TargetInterval n) (centers : List (TargetInterval n)) (ha : ∀ r, allocation r ≤ (read r).2) :
    initialMinimumReadAllocation read allocation sourceLength N F a query centers ≤
      (initialMinimumReadWithWork sourceLength read N F a query centers).2 := by
  let L := (canonicalMulWithWork (nat 32) (nat F)).1
  let coefficient := (canonicalAddWithWork L one).1
  have hq := ha query
  have hz := naturalEqualAllocation_le_work (bitWordValue (read query).1) 0
  have hL := canonicalMulAllocation_le_work (nat 32) (nat F)
  have hc := canonicalAddAllocation_le_work L one
  have hf := canonicalMulAllocation_le_work coefficient (nat N)
  have hs := arithmeticMapAllocation_le_work (initialConeReadWithWork sourceLength read a L query)
    (initialConeReadAllocation read allocation sourceLength a L query) centers
    (fun center _ => initialConeReadAllocation_le_work read allocation sourceLength a L query center ha)
  have hm := minimumAllocation_le_work (canonicalMulWithWork coefficient (nat N)).1
    (arithmeticMapWithWork (initialConeReadWithWork sourceLength read a L query) centers).1
  unfold initialMinimumReadAllocation initialMinimumReadWithWork
  dsimp only
  split_ifs <;> dsimp only [L, coefficient] at hc hf hs hm ⊢ <;> omega



theorem initialProgramReadAllocation_le_work (sourceLength N P F : ℕ) (A a : BinaryFraction) (query : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialProgramReadAllocation read allocation sourceLength N P F A a query ≤
      (initialProgramReadWithWork sourceLength N P F A a read query).2 := by
  have hc := initialCentersReadAllocation_le_work read allocation N P A query ha
  have hm := initialMinimumReadAllocation_le_work read allocation sourceLength N F a query
    (initialCentersReadWithWork N P A read query).1 ha
  unfold initialProgramReadAllocation initialProgramReadWithWork
  dsimp only
  omega



theorem cachedInitialProgramReadAllocation_le_work (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (query : TargetInterval n) (ha : ∀ r, allocation r ≤ (read r).2) :
    cachedInitialProgramReadAllocation read allocation sourceLength N P F A a query ≤
      (cachedInitialProgramReadWithWork sourceLength N P F A a read query).2 :=
  finishCachedAllocation_le_work _ _ _ _ _ (initialProgramReadAllocation_le_work read allocation sourceLength N P F A a query ha)

end Reads
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical query's outer whole-cell loops use the same dyadic
scales and exact Fin-count draws, with explicit initial-table lookups. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

def preparedComputedCellReadWithWork (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := preparedCellGroupReadWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi scales.1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  (result.1, scales.2 + result.2 + 1)

def preparedLocalGroupScaleReadWithWork (eb : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let word := parentInitial query
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork word.1
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    preparedComputedCellReadWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, word.2 + side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

def preparedLocalCellGroupsReadWithWork (N : ℕ)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let word := parentInitial query
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a word.1
    if guard.1 then
      let selected := preparedLocalGroupScaleReadWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, word.2 + groups.2 + count + N.bits.length + 2)

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation





namespace BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

def preparedComputedCellSourceWithWork (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := preparedCellGroupSourceWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
    R R hc hi scales.1 (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  (result.1, scales.2 + result.2 + 1)

def preparedLocalGroupScaleSourceWithWork (eb : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ eb
  let word := parentInitial query
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let radius := naturalCeilingWithWork word.1
  let cells := targetCellsWithWork side.1 (bitWordValue radius.1) query
  let selected := filterMapWithWork (fun cell =>
    preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell) cells.1
  (selected.1, word.2 + side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

/-- Every admitted scale uses the source-aware whole-cell loop. -/
def preparedLocalCellGroupsSourceWithWork (N : ℕ)
    (draw : CellGroupReadDraws M F Q) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let word := parentInitial query
  let groups := arithmeticFlatMapWithWork (fun eb =>
    let guard := refinementScaleGuardWithWork F (2 ^ eb) a word.1
    if guard.1 then
      let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, word.2 + groups.2 + count + N.bits.length + 2)

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryEraseLoopAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs seen : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    queryEraseLoopAllocation equal allocation xs seen ≤ (queryEraseLoopWithWork equal xs seen).2 := by
  induction xs generalizing seen with
  | nil => exact Nat.le_succ _
  | cons a xs ih =>
    have hm := memberByAllocation_le_work equal allocation a seen (fun b _ => h a b)
    have ht := ih (if (memberByWithWork equal a seen).1 then seen else a :: seen)
    unfold queryEraseLoopAllocation queryEraseLoopWithWork
    dsimp only
    exact Nat.add_le_add (Nat.add_le_add hm ht) (by split <;> decide)



theorem queryEraseAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    queryEraseAllocation equal allocation xs ≤ (queryEraseWithWork equal xs).2 :=
  queryEraseLoopAllocation_le_work equal allocation xs [] h



theorem queryInsertAllocation_le_work {α : Type*} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (a : α) (xs : List α) (h : ∀ b, allocation a b ≤ (le a b).2) :
    queryInsertAllocation le allocation a xs ≤ (queryInsertWithWork le a xs).2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hb := h b
    simp only [queryInsertAllocation, queryInsertWithWork]
    split_ifs <;> dsimp only
    · exact Nat.add_le_add_right hb 2
    · calc
        _ = (allocation a b + queryInsertAllocation le allocation a xs) + 1 := (Nat.add_assoc _ _ _).symm
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add hb ih) (by decide : 1 ≤ 2)



theorem querySortAllocation_le_work {α : Type*} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs : List α) (h : ∀ a b, allocation a b ≤ (le a b).2) :
    querySortAllocation le allocation xs ≤ (querySortWithWork le xs).2 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have hi := queryInsertAllocation_le_work le allocation a (querySortWithWork le xs).1 (h a)
    simp only [querySortAllocation, querySortWithWork]
    exact (Nat.add_le_add ih hi).trans (Nat.le_succ _)



theorem queryOrderedInputsAllocation_le_work {α : Type*} (equal le : α → α → Bool × ℕ)
    (equalAllocation leAllocation : α → α → ℕ) (xs : List α)
    (he : ∀ a b, equalAllocation a b ≤ (equal a b).2)
    (hl : ∀ a b, leAllocation a b ≤ (le a b).2) :
    queryOrderedInputsAllocation equal le equalAllocation leAllocation xs ≤
      (queryOrderedInputsWithWork equal le xs).2 := by
  have he' := queryEraseAllocation_le_work equal equalAllocation xs he
  have hl' := querySortAllocation_le_work le leAllocation (queryEraseWithWork equal xs).1 hl
  unfold queryOrderedInputsAllocation queryOrderedInputsWithWork
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryChildCodeAllocation_le_work {M n : ℕ} (input : Fin M × TargetInterval n) :
    queryChildCodeAllocation input ≤ (queryChildCodeWithWork input).2 := by
  have h1 := binaryNaturalAddAllocation_le_work n 1
  have h2 := binaryNaturalMulAllocation_le_work (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi
  have h3 := binaryNaturalAddAllocation_le_work input.2.lo
    (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)
  have h4 := binaryNaturalMulAllocation_le_work M
    (bitWordValue (binaryNaturalAddWithWork input.2.lo
      (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)).1)
  have h5 := binaryNaturalAddAllocation_le_work input.1.val
    (bitWordValue (binaryNaturalMulWithWork M (bitWordValue (binaryNaturalAddWithWork input.2.lo
      (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)).1)).1)
  unfold queryChildCodeAllocation queryChildCodeWithWork
  dsimp only
  omega



theorem queryPairAllocation_le_work (a b : ℕ) : queryPairAllocation a b ≤ (queryPairWithWork a b).2 := by
  have hc := bitCompareWithWork_input_cells a.bits b.bits
  have h1 := binaryNaturalMulAllocation_le_work b b
  have h2 := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalMulWithWork b b).1) a
  have h3 := binaryNaturalMulAllocation_le_work a a
  have h4 := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalMulWithWork a a).1) a
  have h5 := binaryNaturalAddAllocation_le_work
    (bitWordValue (binaryNaturalAddWithWork (bitWordValue (binaryNaturalMulWithWork a a).1) a).1) b
  change a.bits.length + b.bits.length ≤ (binaryNaturalCompareWithWork a b).2 at hc
  unfold queryPairAllocation queryPairWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega



theorem queryHistoryCodeAllocation_le_work {M n : ℕ} (input : Fin M × ℕ × TargetInterval n) :
    queryHistoryCodeAllocation input ≤ (queryHistoryCodeWithWork input).2 := by
  have hc := queryChildCodeAllocation_le_work (input.1, input.2.2)
  have hp := queryPairAllocation_le_work input.2.1 (queryChildCodeWithWork (input.1, input.2.2)).1
  unfold queryHistoryCodeAllocation queryHistoryCodeWithWork
  dsimp only
  omega



theorem queryEncodedLEAllocation_le_work {α : Type*} (code : α → ℕ × ℕ) (allocation : α → ℕ)
    (a b : α) (h : ∀ x, allocation x ≤ (code x).2) :
    queryEncodedLEAllocation code allocation a b ≤ (queryEncodedLEWithWork code a b).2 := by
  have ha := h a
  have hb := h b
  have hc := naturalWordLEAllocation_le_work (code a).1.bits (code b).1.bits
  unfold queryEncodedLEAllocation queryEncodedLEWithWork
  dsimp only
  omega



theorem queryOrderedChildInputsAllocation_le_work {M n : ℕ} (inputs : List (Fin M × TargetInterval n)) :
    queryOrderedChildInputsAllocation inputs ≤ (queryOrderedChildInputsWithWork inputs).2 :=
  queryOrderedInputsAllocation_le_work _ _ _ _ inputs coordinateEqualAllocation_le_work
    (fun a b => queryEncodedLEAllocation_le_work _ _ a b queryChildCodeAllocation_le_work)



theorem queryOrderedHistoryInputsAllocation_le_work {M n : ℕ} (inputs : List (Fin M × ℕ × TargetInterval n)) :
    queryOrderedHistoryInputsAllocation inputs ≤ (queryOrderedHistoryInputsWithWork inputs).2 :=
  queryOrderedInputsAllocation_le_work _ _ _ _ inputs queryHistoryEqualAllocation_le_work
    (fun a b => queryEncodedLEAllocation_le_work _ _ a b queryHistoryCodeAllocation_le_work)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedGeometrySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryGapStatesAllocation_le_work (n g anchor radius sourceLength gapRadius : ℕ) :
    queryGapStatesAllocation n g anchor radius sourceLength gapRadius ≤
      (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).2 := by
  let lo := (saturatingSubtractWithWork anchor radius).1
  let hi := (binaryNaturalAddWithWork anchor radius).1
  let build := fun first =>
    let center := binaryNaturalAddWithWork first sourceLength
    let lower := saturatingSubtractWithWork (bitWordValue center.1) gapRadius
    let upper := binaryNaturalAddWithWork (bitWordValue center.1) gapRadius
    let right := gridPointsWithWork g (bitWordValue lower.1) (bitWordValue upper.1)
    let valid := filterMapWithWork (makeStateWithWork n first) right.1
    (valid.1, center.2 + lower.2 + upper.2 + right.2 + valid.2 + 4)
  let allocation := fun first =>
    let center := (binaryNaturalAddWithWork first sourceLength).1
    let lower := (saturatingSubtractWithWork (bitWordValue center) gapRadius).1
    let upper := (binaryNaturalAddWithWork (bitWordValue center) gapRadius).1
    let right := (gridPointsWithWork g (bitWordValue lower) (bitWordValue upper)).1
    binaryNaturalAddAllocation first sourceLength + saturatingSubtractAllocation (bitWordValue center) gapRadius +
      binaryNaturalAddAllocation (bitWordValue center) gapRadius + gridPointsAllocation g (bitWordValue lower) (bitWordValue upper) +
      filterMapAllocation (makeStateWithWork n first) (makeStateAllocation n first) right
  have hl := saturatingSubtractAllocation_le_work anchor radius
  have hh := binaryNaturalAddAllocation_le_work anchor radius
  have hg := gridPointsAllocation_le_work g (bitWordValue lo) (bitWordValue hi)
  have hb := arithmeticFlatMapAllocation_le_work build allocation
    (gridPointsWithWork g (bitWordValue lo) (bitWordValue hi)).1 (by
      intro first _
      let center := (binaryNaturalAddWithWork first sourceLength).1
      let lower := (saturatingSubtractWithWork (bitWordValue center) gapRadius).1
      let upper := (binaryNaturalAddWithWork (bitWordValue center) gapRadius).1
      have hc := binaryNaturalAddAllocation_le_work first sourceLength
      have hl := saturatingSubtractAllocation_le_work (bitWordValue center) gapRadius
      have hu := binaryNaturalAddAllocation_le_work (bitWordValue center) gapRadius
      have hg := gridPointsAllocation_le_work g (bitWordValue lower) (bitWordValue upper)
      have hf := filterMapAllocation_le_work (makeStateWithWork n first) (makeStateAllocation n first)
        (gridPointsWithWork g (bitWordValue lower) (bitWordValue upper)).1 (fun last _ => makeStateAllocation_le_work n first last)
      dsimp only [build, allocation, center, lower, upper] at hl hu hg hf ⊢
      omega)
  unfold queryGapStatesAllocation queryGapStatesWithWork
  dsimp only [lo, hi, build, allocation] at hg hb ⊢
  omega

namespace BinaryFraction



theorem queryGroupRoundedStatesAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : BinaryFraction) :
    queryGroupRoundedStatesAllocation (ny := ny) parent b exponent cell i h ≤
      (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 := by
  let theta := inversePowerTwo exponent
  let spacing := (roundedSpacingWithWork theta h).1
  let child := (sourceChildWithWork parent i).1
  let offset := (saturatingSubtractWithWork child.lo parent.lo).1
  let base := (canonicalMulWithWork (nat cell.1) theta).1
  let position := (canonicalMulWithWork base (nat b)).1
  let floor := (naturalFloorWithWork position).1
  let anchor := (binaryNaturalAddWithWork (bitWordValue floor) (bitWordValue offset)).1
  let radius := (binaryNaturalMulWithWork 12 b).1
  let length := (saturatingSubtractWithWork child.hi child.lo).1
  let twice := (canonicalMulWithWork (nat 2) h).1
  let gap := (naturalCeilingWithWork twice).1
  have h1 := roundedSpacingAllocation_le_work theta h
  have h2 := sourceChildAllocation_le_work parent i
  have h3 := saturatingSubtractAllocation_le_work child.lo parent.lo
  have h4 := canonicalMulAllocation_le_work (nat cell.1) theta
  have h5 := canonicalMulAllocation_le_work base (nat b)
  have h6 := naturalFloorAllocation_le_work position
  have h7 := binaryNaturalAddAllocation_le_work (bitWordValue floor) (bitWordValue offset)
  have h8 := binaryNaturalMulAllocation_le_work 12 b
  have h9 := saturatingSubtractAllocation_le_work child.hi child.lo
  have h10 := canonicalMulAllocation_le_work (nat 2) h
  have h11 := naturalCeilingAllocation_le_work twice
  have h12 := queryGapStatesAllocation_le_work ny (bitWordValue spacing) (bitWordValue anchor)
    (bitWordValue radius) (bitWordValue length) (bitWordValue gap)
  unfold queryGroupRoundedStatesAllocation queryGroupRoundedStatesWithWork
  dsimp only [theta, spacing, child, offset, base, position, floor, anchor, radius, length, twice, gap]
    at h1 h3 h4 h5 h6 h7 h9 h11 h12 ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSetupSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem signedPowerTwoAllocation_le_work (e : ℤ) :
    signedPowerTwoAllocation e ≤ (signedPowerTwoWithWork e).2 := by
  unfold signedPowerTwoAllocation signedPowerTwoWithWork
  split_ifs <;> dsimp only <;> exact Nat.le_succ _



theorem groupScalesAllocation_le_work (eM eb eF : ℕ) :
    groupScalesAllocation eM eb eF ≤ (groupScalesWithWork eM eb eF).2 := by
  have h := arithmeticMapAllocation_le_work signedPowerTwoWithWork signedPowerTwoAllocation
    (integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ))
    (fun e _ => signedPowerTwoAllocation_le_work e)
  unfold groupScalesAllocation groupScalesWithWork
  dsimp only
  omega



theorem queryGroupLabelsAllocation_le_work (M Q b : ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b h.value) → ℕ)
    (ha : ∀ i, allocation i ≤ (draw i).2) :
    queryGroupLabelsAllocation M Q b h draw allocation ≤ (queryGroupLabelsWithWork M Q b h draw).2 := by
  have costBound (c c' t t' a a' l : ℕ) (hc : c ≤ c') (ht : t ≤ t')
      (ha : a + l ≤ a') : c + t + (a + 2 * l) ≤ c' + t' + a' + l + 2 := by
    omega
  have hc := groupSampleCountAllocation_le_work M Q b h
  have ht := naturalEqualAllocation_le_work (bitWordValue (groupSampleCountWithWork M Q b h).1) M
  have hm := arithmeticMapAllocation_with_spine draw allocation
    (queryFinRange (bitWordValue (groupSampleCountWithWork M Q b h).1)
      (groupSampleCount M Q b h.value) (groupSampleCountWithWork_value M Q b h)) (fun i _ => ha i)
  unfold queryGroupLabelsAllocation queryGroupLabelsWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact (Nat.add_le_add_right (Nat.add_le_add hc ht) M).trans (Nat.le_add_right _ 2)
  · exact costBound _ _ _ _ _ _ _ hc ht hm



theorem queryGroupInputsAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b h.value) → ℕ)
    (ha : ∀ i, allocation i ≤ (draw i).2) :
    queryGroupInputsAllocation (ny := ny) parent b exponent Q cell h draw allocation ≤
      (queryGroupInputsWithWork (ny := ny) parent b exponent Q cell h draw).2 := by
  let build := fun i : Fin M =>
    let states := queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h
    let tagged := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (tagged.1, states.2 + tagged.2 + 1)
  have hl := queryGroupLabelsAllocation_le_work M Q b h draw allocation ha
  have hg := arithmeticFlatMapAllocation_le_work build
    (fun i => queryGroupRoundedStatesAllocation (ny := ny) parent b exponent cell i h +
      arithmeticMapAllocation (fun _ => 1) (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1)
    (queryGroupLabelsWithWork M Q b h draw).1 (by
      intro i _
      have hs := queryGroupRoundedStatesAllocation_le_work (ny := ny) parent b exponent cell i h
      have hm := arithmeticMapAllocation_le_work (fun r => ((i, r), 1)) (fun _ => 1)
        (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1 (fun _ _ => le_rfl)
      dsimp only [build]
      omega)
  unfold queryGroupInputsAllocation queryGroupInputsWithWork
  dsimp only [build] at hg ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGroupSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem transportedSourceAllocation_le {M b Q : ℕ} {f g : ℚ} (h : f = g)
    (draw : cellScaleReadDraw M b Q g)
    (allocation : ∀ t : Fin (groupDyadicScales M b g).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b g t)) → ℕ)
    (ha : ∀ t i, allocation t i ≤ (draw t i).2) :
    ∀ t i, (Eq.mpr (congrArg (fun f => ∀ t : Fin (groupDyadicScales M b f).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → ℕ) h) allocation) t i ≤
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) h) draw t i).2 := by
  cases h
  exact ha

namespace BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ)
  (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P)
  (tau a : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

def preparedComputedCellSourceAllocation (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value)
    (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)
    (cell : ℕ × ℕ) : ℕ :=
  groupScalesAllocation eM eb eF +
    preparedCellGroupSourceAllocation source target parent b P F exponent Q
      (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
      R R hc hi (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
      draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell

theorem preparedComputedCellSourceAllocation_le_work (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : cellScaleReadDraw M b Q (nat F).value)
    (drawAllocation : ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ)
    (cell : ℕ × ℕ)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb hb draw drawAllocation cell ≤
      (preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb hb draw cell).2 := by
  have hs := groupScalesAllocation_le_work eM eb eF
  have ha := preparedCellGroupSourceAllocation_le_work source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current R R hc hi
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell hp hca hia hcur hd
  unfold preparedComputedCellSourceAllocation preparedComputedCellSourceWithWork
  dsimp only
  omega

variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)

def castGroupSourceAllocation (b : ℕ) (cell : ℕ × ℕ) :
    ∀ t : Fin (groupDyadicScales M b (nat F).value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b (nat F).value t)) → ℕ :=
  Eq.mpr (congrArg (fun f => ∀ t : Fin (groupDyadicScales M b f).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b f t)) → ℕ) (nat_value F)) (drawAllocation b cell)

theorem castGroupSourceAllocation_le (b : ℕ) (cell : ℕ × ℕ)
    (hd : ∀ t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    ∀ t i, castGroupSourceAllocation F Q drawAllocation b cell t i ≤
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell) t i).2 := by
  exact transportedSourceAllocation_le (nat_value F) (draw b cell) (drawAllocation b cell) hd

def preparedLocalGroupScaleSourceAllocation (eb : ℕ) (query : TargetInterval target.length) : ℕ :=
  let b := 2 ^ eb
  let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
  let radius := (naturalCeilingWithWork (parentInitial query).1).1
  let cells := (targetCellsWithWork side (bitWordValue radius) query).1
  parentAllocation query + canonicalMulAllocation (inversePowerTwo exponent) (nat b) +
    naturalCeilingAllocation (parentInitial query).1 + targetCellsAllocation side (bitWordValue radius) query +
    filterMapAllocation (fun cell =>
      preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb rfl
        (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell)
      (fun cell => preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        b eb rfl (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell))
        (castGroupSourceAllocation F Q drawAllocation b cell) cell) cells + eb

theorem preparedLocalGroupScaleSourceAllocation_le_work (eb : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    preparedLocalGroupScaleSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query ≤
      (preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi eb draw query).2 := by
  let b := 2 ^ eb
  let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
  let cells := (targetCellsWithWork side (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query).1
  have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat b)
  have hr := naturalCeilingAllocation_le_work (parentInitial query).1
  have ht := targetCellsAllocation_le_work side (bitWordValue (naturalCeilingWithWork (parentInitial query).1).1) query
  have hf := filterMapAllocation_le_work
    (fun cell => preparedComputedCellSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi b eb rfl
      (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell)) cell)
    (fun cell => preparedComputedCellSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb rfl (Eq.mpr (congrArg (cellScaleReadDraw M b Q) (nat_value F)) (draw b cell))
      (castGroupSourceAllocation F Q drawAllocation b cell) cell) cells
    (fun cell _ => preparedComputedCellSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      b eb rfl _ _ cell hp hca hia hcur (castGroupSourceAllocation_le F Q draw drawAllocation b cell (hd b cell)))
  have hq := hp query
  unfold preparedLocalGroupScaleSourceAllocation preparedLocalGroupScaleSourceWithWork
  dsimp only [b, side, cells] at hm ht hf ⊢
  omega

def localGroupSourceScaleBlock (eb : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ :=
  let guard := refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
  if guard.1 then
    let selected := preparedLocalGroupScaleSourceWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    (selected.1, guard.2 + selected.2 + eb + 4)
  else ([], guard.2 + eb + 4)

def localGroupSourceScaleBlockAllocation (eb : ℕ) (query : TargetInterval target.length) : ℕ :=
  refinementScaleGuardAllocation F (2 ^ eb) a (parentInitial query).1 + eb +
    if (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).1 then
      preparedLocalGroupScaleSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query
    else 0

theorem localGroupSourceScaleBlockAllocation_le_work (eb : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query ≤
      (localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi draw eb query).2 := by
  have costBound (g g' s s' e : ℕ) (hg : g ≤ g') (hs : s ≤ s') :
      g + e + s ≤ g' + s' + e + 4 := by
    omega
  have hg := refinementScaleGuardAllocation_le_work F (2 ^ eb) a (parentInitial query).1
  have hs := preparedLocalGroupScaleSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
    draw drawAllocation eb query hp hca hia hcur hd
  unfold localGroupSourceScaleBlockAllocation localGroupSourceScaleBlock
  dsimp only
  split_ifs <;> dsimp only
  · exact costBound _ _ _ _ _ hg hs
  · exact (Nat.add_le_add_right hg eb).trans (Nat.le_add_right _ 4)

def preparedLocalCellGroupsSourceAllocation (N : ℕ) (query : TargetInterval target.length) : ℕ :=
  let count := max 1 N.bits.length
  parentAllocation query + count + N.bits.length +
    arithmeticFlatMapAllocation
      (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi draw eb query)
      (fun eb => localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query) (List.range count)

theorem preparedLocalCellGroupsSourceAllocation_le_work (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hcur : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    preparedLocalCellGroupsSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation N query ≤
      (preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi N draw query).2 := by
  have hm := arithmeticFlatMapAllocation_le_work
    (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi draw eb query)
    (fun eb => localGroupSourceScaleBlockAllocation source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query) (List.range (max 1 N.bits.length))
    (fun eb _ => localGroupSourceScaleBlockAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
      draw drawAllocation eb query hp hca hia hcur hd)
  have hq := hp query
  change _ ≤ (parentInitial query).2 +
    (arithmeticFlatMapWithWork (fun eb => localGroupSourceScaleBlock source target parent P F exponent Q eM eF hM hF hP tau a
      parentInitial child initial current R hc hi draw eb query) (List.range (max 1 N.bits.length))).2 +
    max 1 N.bits.length + N.bits.length + 2
  unfold preparedLocalCellGroupsSourceAllocation
  dsimp only
  omega

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let band := preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    let guard := preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center
    if guard.1.isSome then
      let sampled := countedSampledOnlineReadWithWork center b initial table eta kappa band.1 hband
        G (G ^ 80) t accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

def preparedOnlineReadExtra {nx n : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (center : TargetInterval n) (b P exponent R t : ℕ) (tau : BinaryFraction)
    (child : Fin M → TargetInterval n → BinaryFraction) : ℕ :=
  let band := (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  2 * representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
    3 * (M * (band.length * (R + 3))) +
    (listedBandCoordinates band).length * ((3 * t + 1) * R)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Query-local online scales explicitly read the initial value at the
query and at each rounded center before running the full band kernel. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

def preparedLocalOnlineScaleReadWithWork (e : ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let word := parentInitial center.1
  let eligible := centerEligibilityWithWork b F a word.1
  if eligible.1 then
    let selected := preparedOnlineReadWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table R hc hi t center.1 (integer b center.1)
    (selected.1, spacing.2 + center.2 + word.2 + eligible.2 + selected.2 + e + 4)
  else (none, spacing.2 + center.2 + word.2 + eligible.2 + e + 3)

def preparedLocalOnlineActionsReadWithWork (N : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let word := parentInitial query
  let scales := queryExponentsWithWork N F a word.1
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query) scales.1
  (selected.1, word.2 + scales.2 + selected.2 + 1)

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online candidate selection charges the finite source-buffer decoder
at the point where its integer is consumed. Ineligible centers do not
read a random coordinate. -/

namespace EditApproximation.BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

def preparedLocalOnlineScaleSourceWithWork (e : ℕ) (query : TargetInterval target.length) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let b := 2 ^ e
  let spacing := seedGridSpacingWithWork b P
  let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) query
  let word := parentInitial center.1
  let eligible := centerEligibilityWithWork b F a word.1
  if eligible.1 then
    let sample := integer b center.1
    let selected := preparedOnlineReadWithWork source target parent P F exponent H b (Nat.two_pow_pos e) hP
      tau eta kappa child initial table R hc hi t center.1 sample.1
    (selected.1, spacing.2 + center.2 + word.2 + eligible.2 + selected.2 + sample.2 + e + 5)
  else (none, spacing.2 + center.2 + word.2 + eligible.2 + e + 3)

def preparedLocalOnlineActionsSourceWithWork (N : ℕ) (query : TargetInterval target.length) :
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let word := parentInitial query
  let scales := queryExponentsWithWork N F a word.1
  let selected := filterMapWithWork
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query) scales.1
  (selected.1, word.2 + scales.2 + selected.2 + 1)

end Local
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnlineSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Concrete allocated cells of the sampled labeled online action, including
threshold search, envelopes, coordinate arrays and all optimizer arithmetic. -/


theorem countedSampledOnlineAllocation_le_work {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (initialAllocation : Fin M → TargetInterval n → ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (readAllocation : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i state, initialAllocation i state ≤ (initial i state).2)
    (hr : ∀ s coordinate, readAllocation s coordinate ≤ (read s coordinate).2) :
    countedSampledOnlineAllocation center b initial initialAllocation read readAllocation eta kappa band hne
      G K t integer ≤ 3 * (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 := by
  have ht := triangularChoiceAllocation_le_work K integer
  have ha := countedBandActionAllocation_le_work b initial initialAllocation read readAllocation
    eta kappa band G (triangularChoiceWithWork K integer).1.val t hi hr
  unfold countedSampledOnlineAllocation countedSampledOnlineReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem reduceOnlineIntegerAllocation_le_work (K integer : ℕ) (hK : 0 < K) :
    reduceOnlineIntegerAllocation K integer ≤ (BinaryFraction.reduceOnlineIntegerWithWork K hK integer).2 := by
  have ht := triangularMassAllocation_le_work K
  have hd := bitDivModAllocation_le_work (bitWordValue (triangularMassWithWork K).1).bits integer.bits
  unfold reduceOnlineIntegerAllocation BinaryFraction.reduceOnlineIntegerWithWork binaryNaturalDivModWithWork
  dsimp only
  omega

/-- The only multiplicative allowance needed by the labeled optimizer. -/
theorem filterMapAllocation_le_three_work {α β : Type*} (f : α → Option β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ 3 * (f x).2) :
    filterMapAllocation f allocation xs ≤ 3 * (filterMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterMapAllocation, filterMapWithWork]
    cases he : (f x).1 <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte] <;> omega

namespace BinaryFraction
section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
  (tau eta kappa : BinaryFraction)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ)

def preparedOnlineReadAllocation (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) : ℕ :=
  let band := (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  let G := (onlineIndexSetupWithWork H band).1
  let accepted := (reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G]; rw [onlineIndexSetupWithWork_value]; positivity) integer).1
  preparedRepresentativeReadAllocation parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child childAllocation +
    onlineIndexSetupAllocation H band + reduceOnlineIntegerAllocation (G ^ 80) integer +
    if hband : band = [] then 0 else
      preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation +
      if (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).1.isSome then
        countedSampledOnlineAllocation center b initial initialAllocation table tableAllocation eta kappa
          band hband G (G ^ 80) t accepted + 1
      else 0

theorem preparedOnlineReadAllocation_le_work (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2) :
    preparedOnlineReadAllocation source target parent P F exponent H b hb hP tau eta kappa child initial table
      R hc hi childAllocation initialAllocation tableAllocation t center integer ≤
      3 * (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
        child initial table R hc hi t center integer).2 := by
  have emptyBound (b b' s s' r r' : ℕ) (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') :
      b + s + r + 0 ≤ 3 * (b' + s' + r' + 1) := by
    omega
  have selectedBound (b b' s s' r r' g g' a a' : ℕ)
      (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') (hg : g ≤ g') (ha : a ≤ 3 * a') :
      b + s + r + (g + (a + 1)) ≤ 3 * (b' + s' + r' + g' + a' + 2) := by
    omega
  have rejectedBound (b b' s s' r r' g g' : ℕ)
      (hb : b ≤ b') (hs : s ≤ s') (hr : r ≤ r') (hg : g ≤ g') :
      b + s + r + (g + 0) ≤ 3 * (b' + s' + r' + g' + 1) := by
    omega
  let band := (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  let G := (onlineIndexSetupWithWork H band).1
  have hG : 0 < G ^ 80 := by dsimp only [G]; rw [onlineIndexSetupWithWork_value]; positivity
  let accepted := (reduceOnlineIntegerWithWork (G ^ 80) hG integer).1
  have hbnd := preparedRepresentativeReadAllocation_le_work parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child childAllocation hca
  have hsetup := onlineIndexSetupAllocation_le_work H band
  have hreduce := reduceOnlineIntegerAllocation_le_work (G ^ 80) integer hG
  have hguard := preparedUnskippedReadAllocation_le_work source target parent center b P exponent hb hP
    tau (nat F) child initial childAllocation initialAllocation R R hc hi hca hia
  unfold preparedOnlineReadAllocation preparedOnlineReadWithWork
  dsimp only
  split_ifs with he hg
  · dsimp only [band, G] at hsetup hreduce
    exact emptyBound _ _ _ _ _ _ hbnd hsetup hreduce
  · have hsample := countedSampledOnlineAllocation_le_work center b initial initialAllocation table tableAllocation
      eta kappa band he G (G ^ 80) t accepted hia hta
    dsimp only [band, G, accepted] at hsetup hreduce hsample
    exact selectedBound _ _ _ _ _ _ _ _ _ _ hbnd hsetup hreduce hguard hsample
  · dsimp only [band, G] at hsetup hreduce
    exact rejectedBound _ _ _ _ _ _ _ _ hbnd hsetup hreduce hguard

end Online
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ)
  (integerAllocation : ℕ → TargetInterval target.length → ℕ)

def preparedLocalOnlineScaleSourceAllocation (e : ℕ) (query : TargetInterval target.length) : ℕ :=
  let b := 2 ^ e
  let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query).1
  seedGridSpacingAllocation b P + roundStateAllocation (bitWordValue (seedGridSpacingWithWork b P).1) query +
    parentAllocation center + centerEligibilityAllocation b F a (parentInitial center).1 + e +
    if (centerEligibilityWithWork b F a (parentInitial center).1).1 then
      integerAllocation b center + preparedOnlineReadAllocation source target parent P F exponent H b
        (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi
        childAllocation initialAllocation tableAllocation t center (integer b center).1
    else 0

theorem preparedLocalOnlineScaleSourceAllocation_le_work (e : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2)
    (hint : ∀ b q, integerAllocation b q ≤ (integer b q).2) :
    preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query ≤
      3 * (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer e query).2 := by
  have costBound (s s' r r' p p' g g' i i' a a' e k : ℕ)
      (hs : s ≤ s') (hr : r ≤ r') (hp : p ≤ p') (hg : g ≤ g')
      (hi : i ≤ i') (ha : a ≤ 3 * a') :
      s + r + p + g + e + (i + a) ≤ 3 * (s' + r' + p' + g' + a' + i' + e + k) := by
    omega
  have emptyBound (s s' r r' p p' g g' e : ℕ)
      (hs : s ≤ s') (hr : r ≤ r') (hp : p ≤ p') (hg : g ≤ g') :
      s + r + p + g + e + 0 ≤ 3 * (s' + r' + p' + g' + e + 3) := by
    omega
  let b := 2 ^ e
  let center := (roundStateWithWork (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query).1
  have hs := seedGridSpacingAllocation_le_work b P
  have hr := roundStateAllocation_le_work (bitWordValue (seedGridSpacingWithWork b P).1)
    (seedGridSpacingWithWork_pos b P hP) query
  have hg := centerEligibilityAllocation_le_work b F a (parentInitial center).1
  have hp' := hp center
  have hint' := hint b center
  have hsample := preparedOnlineReadAllocation_le_work source target parent P F exponent H b
    (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi
    childAllocation initialAllocation tableAllocation t center (integer b center).1 hca hia hta
  unfold preparedLocalOnlineScaleSourceAllocation preparedLocalOnlineScaleSourceWithWork
  dsimp only
  split_ifs <;> dsimp only [b, center] at hs hr hg hp' hint' hsample ⊢
  · exact costBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs hr hp' hg hint' hsample
  · exact emptyBound _ _ _ _ _ _ _ _ _ hs hr hp' hg

def preparedLocalOnlineActionsSourceAllocation (N : ℕ) (query : TargetInterval target.length) : ℕ :=
  parentAllocation query + queryExponentsAllocation N F a (parentInitial query).1 +
    filterMapAllocation
      (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer e query)
      (fun e => preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
        tableAllocation integerAllocation e query)
      (queryExponentsWithWork N F a (parentInitial query).1).1

theorem preparedLocalOnlineActionsSourceAllocation_le_work (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ q, parentAllocation q ≤ (parentInitial q).2)
    (hca : ∀ i q, childAllocation i q ≤ (child i q).2)
    (hia : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hta : ∀ s q, tableAllocation s q ≤ (table s q).2)
    (hint : ∀ b q, integerAllocation b q ≤ (integer b q).2) :
    preparedLocalOnlineActionsSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation N query ≤
      3 * (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer N query).2 := by
  have hq := hp query
  have he := queryExponentsAllocation_le_work N F a (parentInitial query).1
  have hm := filterMapAllocation_le_three_work
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleSourceAllocation source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query)
    (queryExponentsWithWork N F a (parentInitial query).1).1
    (fun e _ => preparedLocalOnlineScaleSourceAllocation_le_work source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
      tableAllocation integerAllocation e query hp hca hia hta hint)
  unfold preparedLocalOnlineActionsSourceAllocation preparedLocalOnlineActionsSourceWithWork
  dsimp only
  omega

end Local
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemoSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-width binary memo has bounded height on every execution,
including failed approximation events and repeated lookups. This bound
uses the actual returned tree and does not count a complete table allocation. -/

namespace EditApproximation

namespace BinaryMemo

def height {α : Type*} : BinaryMemo α → ℕ
  | .empty => 0
  | .node _ left right => max left.height right.height + 1

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineSetupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate enumeration, index construction and range reduction
preceding the online optimizer, counted in Boolean operations. -/

namespace EditApproximation
namespace BinaryFraction

def onlineIndexBitBudget (M vertices B : ℕ) : ℕ :=
  bandCoordinatesBitBudget M vertices B + 40 * (B + 4) +
    bitPowerBitBudget 80 (B + 4) + 3

def reduceOnlineBitBudget (B : ℕ) : ℕ :=
  10000 * (B + 3) ^ 2 + 200 * (4 * B + 6) ^ 2 + B + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full bit cost of the sampled member continuation. All its internal
counting, envelope, rounding and summation callbacks are discharged here. -/

namespace EditApproximation
namespace BinaryFraction

def sampledMemberInputBudget (M b B : ℕ) : ℕ :=
  B + (3 * bandEnvelopeWordBudget b M B + 1) + connectionWordBudget M B + 1

def sampledMemberWordBudget (M T b B : ℕ) : ℕ :=
  let S := sampledMemberInputBudget M b B
  groupMemberWordBudget T S (boundedScaleWordBudget M S)

def sampledMemberBitBudget (M T exponent b vertices B : ℕ) : ℕ :=
  M * (bandEnvelopeBitBudget b M vertices B + 6) +
    roundedBandBitBudget exponent b M vertices B + 7 * M +
    (connectionBitBudget M B + 2 * B + M + 2) +
    countedGroupBitBudget M T (sampledMemberInputBudget M b B) + 5

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySelectedGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete group selection cost, including every sampled member estimate
and reconstruction of the selected rounded action. -/

namespace EditApproximation
namespace BinaryFraction

def selectedGroupBitBudget (M T e b members vertices B : ℕ) : ℕ :=
  members * (sampledMemberBitBudget M T e b vertices B +
    1000 * (sampledMemberWordBudget M T b B + 1) ^ 2 + 3) + 1 +
    roundedBandBitBudget e b M vertices B + connectionBitBudget M B + 2 * B + 2 * M + 6

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedGuardWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All post-construction band guards, including rounded wide membership
and the child imbalance scan, have explicit Boolean arithmetic costs. -/

namespace EditApproximation
namespace BinaryFraction

def unskippedGuardInputBudget (b M B : ℕ) : ℕ :=
  let E := 3 * bandEnvelopeWordBudget b M B + 1
  B + E + bandMassTotalStorageBudget M E + stateGapWordBudget B + 10

def unskippedGuardBitBudget (e b M v w B : ℕ) : ℕ :=
  let E := 3 * bandEnvelopeWordBudget b M B + 1
  let W := unskippedGuardInputBudget b M B
  M * (bandEnvelopeBitBudget b M v B + 6) + storedSumBitBudget M E +
    2000 * (W + 1) ^ 2 + 2000 * (4 * W + 3) ^ 2 +
    (1000 * (16 * W + 11) ^ 2 + 1) + roundedBandBitBudget e b M v B +
    (1 + w * (M * (16 * B + 8) + 1)) +
    M * (18 * B + 1 + stateGapBitBudget B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 6) + 5

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedUnskippedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete unskipped-band constructor pays for both actual wide
grids, every prefix predicate, all child envelopes, and the final guards. -/

namespace EditApproximation
namespace BinaryFraction

def preparedUnskippedBitBudget (e b M P v w B : ℕ) : ℕ :=
  2 * wideMaterializationBitBudget M P B +
    representativeCompleteBitBudget M w (4 * B + 20) +
    unskippedGuardBitBudget e b M v w B + 2 * w + 4

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedCellGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete per-cell arithmetic. The count includes construction and
testing of every candidate, and the actual finite-count sampled selector. -/

namespace EditApproximation
namespace BinaryFraction

def preparedCellGroupBitBudget (M T e b P B : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  cellCentersBitBudget P P B +
    (P + 1) ^ 2 * (preparedUnskippedBitBudget e b M P V V B + 3) +
    selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalGroupWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit work of the literal query-local whole-cell loops.  The tested scale
inequality bounds both coordinate ranges; every generated cell invokes the
complete counted band and sampled-action routine. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalGroupScaleBitBudget (M P F exponent eM eF eb B : ℕ) : ℕ :=
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let C := 16 * B + 200
  2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (groupScalesBitBudget eM eb eF +
      preparedCellGroupBitBudget M (7 + eM + eF) exponent (2 ^ eb) P C + 4) + eb + 4

def preparedLocalGroupsBitBudget (N M P F exponent eM eF B : ℕ) : ℕ :=
  let count := max 1 N.bits.length
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  ((List.range count).map fun eb => localEligibilityBitBudget (B + 3) +
    preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + cells + 3).sum +
    count + N.bits.length + 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree envelope for the full labeled action selector, including
its final logarithm-gradient and argmax, after the iterative optimizer. -/

namespace EditApproximation

abbrev CE_p0 := FiniteBitPolynomial (Fin 12)
def baSize (a : CE_p0) : CE_p0 := .bitLength a
def baMax (a b : CE_p0) : CE_p0 := .maximum a b

def expressionLogStorage_p0 (B K : CE_p0) : CE_p0 :=
  baSize (2 * K) + 2 * (K * K * (4 * B + 18) + K * (baSize (2 * K + 1) + 1) + 1) + 1

def expressionGradientStorage_p0 (G P L : CE_p0) : CE_p0 :=
  4 * expressionLogStorage_p0 (2 * P + 2 * (5 + 50 * (baSize G + 2)) + 2) (G ^ 60) + 2 * L + 18

def expressionPoint_p0 (K B Bv : CE_p0) : CE_p0 :=
  Bv + 2 * (B + K * (2 * baSize (K + 1) + B)) + 2

def expressionLogUniversal_p0 (B K : CE_p0) : CE_p0 :=
  B + (baSize K + 2 * (K * K * B + K * (baSize (2 * K + 1) + 1) + 1) + 1) +
    (2 * ((2 * K + 1) * B + 1) + 2) + baSize (2 * K + 1) + 10

def expressionLogStep_p0 (W K : CE_p0) : CE_p0 :=
  (2 * K + 1) * (2000 * (W + 1) ^ 2 + 1) + 2100 * (W + 2) ^ 2 +
    6000 * (W + 1) ^ 2 + baSize (2 * K + 1) + 6

def expressionLogBit_p0 (B K : CE_p0) : CE_p0 :=
  let W := expressionLogUniversal_p0 (8 * B + 22) K
  12000 * (B + 4) ^ 2 + 2100 * (4 * B + 12) ^ 2 +
    K * expressionLogStep_p0 W K + 2000 * (W + 5) ^ 2 + 10

def expressionGradientBit_p0 (G P L : CE_p0) : CE_p0 :=
  let S := 3 + 50 * (baSize G + 2)
  let R := 4 * P + 2 * S + 8
  let logBits := expressionLogStorage_p0 R (G ^ 60)
  let natWidth := baMax (baSize G) 1
  let powerWidth := natWidth + 3 + 50 * (2 * natWidth + 1)
  (1 + 50 * (2000 * (powerWidth + 1) ^ 2 + 1)) + (4 * S + 3) +
    6000 * (P + S + 2) ^ 2 + expressionLogBit_p0 R (G ^ 60) +
    (6000 * (logBits + 4) ^ 2 + 1) + 6000 * (L + 2 * logBits + 9) ^ 2 + baSize G + 70

def expressionMaximizer_p0 (d v B V : CE_p0) : CE_p0 :=
  let W := B + baSize (d * V * V) + 2 * (1 + d * (B + B)) + 1
  v * (1 + d * (100000 * (W + 1) ^ 2) + 1000 * (W + 1) ^ 2 + 2) + d + 1

def expressionUpdate_p0 (d K P : CE_p0) : CE_p0 :=
  let C := baSize (K + 2) + 8
  let W := P + 2 * C + 8
  2100 * (baSize (K + 2) + 6) ^ 2 + (6000 * (C + 4) ^ 2 + 1) +
    d * (110000 * (W + 1) ^ 2 + 6) + baSize (K + 2) + 4

def expressionOptimizer_p0 (d v G K B Bv L V : CE_p0) : CE_p0 :=
  let P := expressionPoint_p0 K B Bv
  let W := expressionGradientStorage_p0 G (2 * P + 1) (2 * L + 1)
  d + 1 + K * (d * (expressionGradientBit_p0 G P L + 6) +
    expressionMaximizer_p0 d v (baMax P W) (2 * G ^ 60 + 1 + V + 1) + expressionUpdate_p0 d K P + 3)

def expressionBandSumStorage_p0 (n B : CE_p0) : CE_p0 :=
  baSize n + B + 2 * (1 + n * (B + 1)) + 2

def expressionBandVertexWord_p0 (M B : CE_p0) : CE_p0 :=
  2 * B + expressionBandSumStorage_p0 M B + 3

def expressionStoredSumWord_p0 (n B : CE_p0) : CE_p0 :=
  (B + 1) + baSize n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

def expressionStoredSumBit_p0 (n B : CE_p0) : CE_p0 :=
  1 + n * (100000 * (expressionStoredSumWord_p0 n B + 1) ^ 2)

def expressionBandCoordinateBit_p0 (M B : CE_p0) : CE_p0 :=
  2100 * (B + expressionBandSumStorage_p0 M B + 2) ^ 2

def expressionBandPreparation_p0 (M d v B : CE_p0) : CE_p0 :=
  expressionStoredSumBit_p0 M B + v * (d * (expressionBandCoordinateBit_p0 M B + 6)) + 6 * v

def expressionOptimisticStorage_p0 (Bm Bt Bc : CE_p0) : CE_p0 := 20 * Bt + 8 * Bm + 4 * Bc + 30

def expressionOnlineStorage_p0 (Be Bk Bm Bt t : CE_p0) : CE_p0 :=
  2 * Be + 2 * expressionBandSumStorage_p0 t (expressionOptimisticStorage_p0 Bm Bt (4 * Bk + 18)) +
    2 * (2 * Bt + 2 * Bm + 4) + 3

def expressionGainBit_p0 (Bm Bt : CE_p0) : CE_p0 := 2100 * (Bm + Bt + 2) ^ 2 + 1

def expressionDecrementBit_p0 (Bm Bt : CE_p0) : CE_p0 :=
  6000 * (Bt + 1) ^ 2 + 2100 * (8 * Bt + Bm + 8) ^ 2 + 2

def expressionCoefficientBit_p0 (Bk : CE_p0) : CE_p0 :=
  2000 * (Bk + 3) ^ 2 + 6000 * (2 * Bk + 7) ^ 2 + 2

def expressionOptimisticBit_p0 (Bm Bt Bc : CE_p0) : CE_p0 :=
  let W := 8 * Bt + 2 * Bm + 2 * Bc + 12
  expressionGainBit_p0 Bm Bt + expressionDecrementBit_p0 Bm Bt +
    2000 * (W + 1) ^ 2 + 6000 * (W + 1) ^ 2 + 2

def expressionOnlineBit_p0 (Be Bk Bm Bt t : CE_p0) : CE_p0 :=
  let storage := expressionOptimisticStorage_p0 Bm Bt (4 * Bk + 18)
  let W := Be + expressionBandSumStorage_p0 t storage + (2 * Bt + 2 * Bm + 4) + 2
  expressionCoefficientBit_p0 Bk + t * (expressionOptimisticBit_p0 Bm Bt (4 * Bk + 18) + 6) +
    expressionStoredSumBit_p0 t storage + expressionGainBit_p0 Bm Bt +
    6000 * (W + 1) ^ 2 + 2000 * (2 * W + 3) ^ 2 + 3

def expressionSelection (d v G K B Bv L V : CE_p0) : CE_p0 :=
  let P := expressionPoint_p0 K B Bv
  let W := expressionGradientStorage_p0 G (2 * P + 1) (2 * L + 1)
  expressionOptimizer_p0 d v G K B Bv L V + d * (expressionGradientBit_p0 G P L + 6) +
    expressionMaximizer_p0 d v (baMax P W) (2 * G ^ 60 + 1 + V + 1)

def expressionEnvelopeWord (M bb B : CE_p0) : CE_p0 := B + bb + baSize M + 8
def expressionEnvelopeWork (M bb v B : CE_p0) : CE_p0 :=
  let W := expressionEnvelopeWord M bb B
  2100 * (bb + baSize M + 6) ^ 2 +
    (1 + v * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + v + 4

def bandActionExpression : CE_p0 :=
  let M := .input 0
  let d := .input 1
  let bb := .input 2
  let v := .input 3
  let G := .input 4
  let K := .input 5
  let t := .input 6
  let Be := .input 7
  let Bk := .input 8
  let Bi := .input 9
  let Bt := .input 10
  let E := .input 11
  let Bm := 3 * expressionEnvelopeWord M bb Bi + 1
  M * (expressionEnvelopeWork M bb v Bi + 6) +
    (expressionBandPreparation_p0 M d v Bm + 2 * v +
      d * (expressionOnlineBit_p0 Be Bk Bm Bt t + 6) +
      expressionSelection d v G K (expressionBandVertexWord_p0 M Bm) (expressionBandVertexWord_p0 M Bm)
        (expressionOnlineStorage_p0 Be Bk Bm Bt t) (E * (2 * t + 1)) + 2) + 1

def bandActionBitDegree : ℕ := bandActionExpression.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnlinePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete sampled online action, including the triangular search,
coordinate equality tests, final logarithm-gradient and labeled argmax. -/

namespace EditApproximation

abbrev SP_p0 := FiniteBitPolynomial (Fin 5)
def sampledOnlineOverhead : SP_p0 :=
  let M := .input 0
  let v := .input 1
  let d := .input 2
  let K := .input 3
  let B := .input 4
  (K + 1) * (10000 * (B + 3) ^ 2 + 30 * (B + 3)) + M + 2 +
    (v * (5 * M + 3) + (v * M + 1) ^ 2 * (24 * B + 12) + 1) + d +
    v * d * (24 * B + 9) + 2

def sampledOnlineBitDegree : ℕ := max bandActionBitDegree sampledOnlineOverhead.degree + 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedBandPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

abbrev BP := FiniteBitPolynomial (Fin 8)
def bpSumStorage (n B : BP) : BP := .bitLength n + B + 2 * (1 + n * (B + 1)) + 2
def bpSumWord (n B : BP) : BP :=
  (B + 1) + .bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
def bpSumWork (n B : BP) : BP := 1 + n * (100000 * (bpSumWord n B + 1) ^ 2)
def bpConnectionWord (M B : BP) : BP := bpSumStorage (M + 1) (8 * B + 6)
def bpConnectionWork (M B : BP) : BP :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    bpSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
def bpEndpointWord (M B : BP) : BP :=
  8 * (bpConnectionWord M B + bpSumStorage M B) + 6
def bpEndpointWork (M B : BP) : BP :=
  bpConnectionWork M B + 2 * B + M + 2 + bpSumWork M B + 6 * M +
    6000 * (bpConnectionWord M B + bpSumStorage M B + 1) ^ 2 + 2
def bpMinimum (M n B : BP) : BP :=
  bpEndpointWork M B + n * (bpEndpointWork M B + 3) +
    (1 + n * (1000 * (bpEndpointWord M B + 1) ^ 2 + 2)) + 2
def bpGapWord (B : BP) : BP := 64 * B + 54
def bpGapWork (B : BP) : BP :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2
def bpNaturalDistance (B : BP) : BP :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3
def bpAnchor (B : BP) : BP :=
  2 * (36 * B + 4) + 80 * (B + 4) + 2 * bpNaturalDistance B + 3
def bpTolerance (B : BP) : BP :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 + 2 * B + 3
def bpPredicate (M B C : BP) : BP :=
  (M + 1) * (8 * B + 3) + M * (bpAnchor B + 3) + bpTolerance B + M * (C + 3) + 4
def bpBand (n B C : BP) : BP :=
  6000 * (B + 1) ^ 2 + 1000 * (8 * B + 7) ^ 2 + n * (C + 3) + 4
def bpRepresentative (M n B : BP) : BP :=
  let W := B + bpEndpointWord M B + bpGapWord B + 1
  let S := 4 * W + 4 + B + M + n + 2
  bpMinimum M n B + 1000 * (W + 1) ^ 2 + bpGapWork B + 2100 * (W + 2) ^ 2 +
    bpBand n (4 * W + 4) (bpPredicate M S (S ^ prefixArithmeticDegree)) + 3
def bpGridPoints (n B : BP) : BP :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)
def bpGridBox (n B : BP) : BP :=
  96 * (B + 1) + 2 * bpGridPoints n (B + 2) +
    n * (n * (16 * (B + 2) + 11) + n + 3) + 6
def bpWide (M P B C : BP) : BP :=
  M * (10000 * (B + 12) ^ 2 + bpGridBox (40 * P + 2) (B + 12) + 6) +
    (M + 1) * (6 * M + 10) * C + 1
def bpEnvelopeWord (M bb B : BP) : BP := B + bb + .bitLength M + 8
def bpEnvelopeWork (M bb n B : BP) : BP :=
  let W := bpEnvelopeWord M bb B
  2100 * (bb + .bitLength M + 6) ^ 2 +
    (1 + n * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + n + 4
def bpRound (M e bb n B : BP) : BP :=
  let W := e + 2 + 3 * bpEnvelopeWord M bb B + B
  M * (bpEnvelopeWork M bb n B +
    (2000 * (W + 1) ^ 2 + 1500 * (4 * W + 3) ^ 2 + 3) +
    500 * (4 * W + 4 + B + 1) ^ 2 + e + 11)
def bpGuard (e bb M v w B : BP) : BP :=
  let E := 3 * bpEnvelopeWord M bb B + 1
  let W := B + E + bpSumStorage M E + bpGapWord B + 10
  M * (bpEnvelopeWork M bb v B + 6) + bpSumWork M E +
    2000 * (W + 1) ^ 2 + 2000 * (4 * W + 3) ^ 2 +
    (1000 * (16 * W + 11) ^ 2 + 1) + bpRound M e bb v B +
    (1 + w * (M * (16 * B + 8) + 1)) +
    M * (18 * B + 1 + bpGapWork B + 2000 * (W + 1) ^ 2 +
      (1000 * (4 * W + 3) ^ 2 + 1) + 6) + 5
def preparedBandPolynomial : BP :=
  let M := .input 0
  let P := .input 1
  let e := .input 2
  let bb := .input 3
  let v := .input 4
  let w := .input 5
  let B := .input 6
  let C := .input 7
  2 * bpWide M P B C + bpRepresentative M w (4 * B + 20) + bpGuard e bb M v w B + 2 * w + 4

def preparedBandBitDegree : ℕ := preparedBandPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete local online call: materialized endpoint grids, all band
guards, explicit index/range construction and the actual sampled optimizer. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineBitBudget (M P B S : ℕ) : ℕ :=
  2 * S ^ preparedBandBitDegree +
    onlineIndexBitBudget M ((40 * P + 2) ^ (2 * M)) B +
    reduceOnlineBitBudget B + S ^ sampledOnlineBitDegree + 3

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalOnlineWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All selected scales execute rounding, the center guard, and the complete
sampled optimizer. The list contains at most one action per tested scale. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalOnlineScaleBitBudget (M P B S : ℕ) : ℕ :=
  let W := B + 4
  100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
    localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4

def preparedLocalOnlineBitBudget (M P B S : ℕ) : ℕ :=
  queryExponentsBitBudget B + (B + 1) * (preparedLocalOnlineScaleBitBudget M P B S + 3) + 1

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete prepared refinement kernel has a single arithmetic bound.
All generated grids, guards, selected actions and the returned value are
charged. The premises below describe only stored input words and numeric
parameters; action geometry and output-list bounds are derived. -/

namespace EditApproximation
namespace BinaryFraction

structure PreparedKernelInputBounds {nx ny M : ℕ}
    (N P F exponent H Q eM eF B E S t : ℕ)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval ny → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval ny → BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (integer : ℕ → TargetInterval ny → ℕ) : Prop where
  largeBits : 10 ≤ B
  inputSize : Nat.size N ≤ B
  sourceSize : Nat.size nx + 2 ≤ B
  targetSize : Nat.size ny + 2 ≤ B
  aritySize : Nat.size M + 2 ≤ B
  precisionSize : Nat.size P ≤ B
  factorSize : Nat.size F + 2 ≤ B
  sampleSize : Nat.size Q + 2 ≤ B
  thetaSize : exponent + 1 ≤ B
  scaleSizes : eM + eF + 7 ≤ B
  heightSize : Nat.size H ≤ B
  coordinateSize : Nat.size (M * (40 * P + 2) ^ 2) ≤ B
  iterationSize : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B
  drawSize : ∀ b r, Nat.size (integer b r) ≤ B
  tauSize : tau.width ≤ B
  factorWidth : a.width ≤ B
  rateSize : eta.width ≤ B
  optimismSize : kappa.width ≤ B
  decrementSize : delta.width ≤ B
  parentSize : ∀ r, (parentInitial r).width ≤ B
  massSize : ∀ i r, (childMass i r).width ≤ B
  initialSize : ∀ i r, (childInitial i r).width ≤ B
  oldSize : ∀ s, (old s).width ≤ B
  currentSize : ∀ s, (current s).width ≤ B
  historySize : ∀ s ≤ t + 1, ∀ i r, (history s (i, r)).width ≤ B
  parentNonneg : ∀ r, 0 ≤ (parentInitial r).value
  rateMagnitude : |eta.value| ≤ E
  optimismRange : 0 ≤ kappa.value ∧ kappa.value ≤ 1
  historyRange : ∀ s ≤ t + 1, ∀ i r, 0 ≤ (history s (i, r)).value ∧
    (history s (i, r)).value ≤ (childInitial i r).value
  scalePositive : 2 ≤ S
  arityCap : M ≤ S
  precisionCap : P ≤ S
  rateCap : E ≤ S
  timeCap : t ≤ S
  wordCap : 3 * (B + 4) + 4 ≤ S
  actionCap : (40 * P + 2) ^ (2 * M) ≤ S
  cartesianCap : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S
  iterationCap : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S

def preparedKernelWordBudget (M B : ℕ) : ℕ :=
  localContinuationWordBudget M (physicalContinuationInputBudget M (B + 4))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRefinementParameters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The decrement is constructed on the same Boolean words as the online
constants. In particular no rational literal or uncharged inversion is
needed at a local refinement entry. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem refinementDecrementWithWork_value (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (refinementDecrementWithWork ell hell).1.value = 1 / (bitWordValue ell : ℚ) ^ 10 := by
  simp [refinementDecrementWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoHeap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A cumulative allocation counter for the actual memo execution. It keeps
all local allocations until the entire run finishes, so it also bounds peak
space. A read retains three continuation/result cells. Each memo call reserves
its address workspace, key bits, traversal frames and the possible new trie
path; existing values and input words are shared by reference. -/

namespace EditApproximation
namespace BitQuery.Heap

def runCells {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ)
    {program : BitQuery ι BinaryFraction} : Heap program → BinaryMemo BinaryFraction → ℕ
  | .done _, _ => 0
  | .read key _ continuation, memory =>
    let first := ask key memory
    3 + childCells key memory + (continuation first.value).runCells ask childCells first.memory
  | .charge cells _ next, memory => cells + next.runCells ask childCells memory

end BitQuery.Heap

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryKeysSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery.Heap

def mapKeysWithWork {ι κ β : Type*} (f : ι → κ × ℕ) (allocation : ι → ℕ)
    (ha : ∀ key, allocation key ≤ (f key).2)
    {program : BitQuery ι β} (heap : Heap program) : Heap (program.mapKeysWithWork f) :=
  match heap with
  | .done result => .done result
  | .read key next continuation =>
    chargeOf (allocation key) (ha key)
      (.read (f key).1 _ (fun word => (continuation word).mapKeysWithWork f allocation ha))
  | .charge localCells bound next => .charge localCells bound (next.mapKeysWithWork f allocation ha)

def restrictWithWork {ι : Type*} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (test key).2)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) :
    Heap (program.restrictWithWork P test htest) :=
  match heap with
  | .done result => .done result
  | .charge localCells bound next => .charge localCells bound (next.restrictWithWork P test htest allocation ha)
  | .read key next continuation =>
    chargeOf (allocation key) (ha key)
      (by
        split
        · exact .read _ _ (fun word => (continuation word).restrictWithWork P test htest allocation ha)
        · exact (continuation (BinaryFraction.nat 0)).restrictWithWork P test htest allocation ha)


end EditApproximation.BitQuery.Heap

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





def capacity (M J n passes copies T S : ℕ) : ℕ :=
  (T + S + 1) * (copies * (entryCapacity M J n * passes))

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 def capacity (M J ny passes copies T S : ℕ) : ℕ :=
  2 * (PhysicalTableRequest.entryCapacity M J ny +
    PhysicalTableRequest.capacity M J ny passes copies T S)

 def bits (M J ny passes copies T S : ℕ) : ℕ :=
  Nat.clog 2 (capacity M J ny passes copies T S + 1)

 theorem table_rank_lt {M J ny passes copies T S : ℕ}
    (parent child : {request : PhysicalTableRequest M J ny // request.Bounded passes copies T S})
    (h : child.val.combinedRank T S < parent.val.combinedRank T S) :
    rank (Sum.inr child : ChargedPhysicalRequest M J ny passes copies T S) < rank (Sum.inr parent) := by
  simpa only [rank, depth, index, ← Nat.add_assoc, PhysicalTableRequest.combinedRank] using
    Nat.add_lt_add_right h 1

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

abbrev ComparisonState (nx ny : ℕ) := Option (TargetInterval nx × TargetInterval ny)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalConditionalNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional expected regret in a fixed child environment

Finite Bernstein bounds control the parent product draws. Agreement of
deeper selection functions fixes all child histories by locality, and
list membership connects the sampled actions to the refinement recurrence.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

abbrev BandParentSpace (R M b F Q K : ℕ) :=
  ParentRandomSpace R (optimizerTriangularMass K) M (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtree
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison paths below an arbitrary physical node retain their original
global table labels. No refinement program or random law is changed. -/

namespace EditApproximation

def treeLayerAppend {M k : ℕ} (initialPath : TreeLayer M k) :
    (d : ℕ) → TreeLayer M d → TreeLayer M (k + d)
  | 0, _ => initialPath
  | d + 1, path => (treeLayerAppend initialPath d path.1, path.2)

def physicalSubtreeNode {M J : ℕ} (root : PhysicalNode M J) (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d ≤ J) : PhysicalNode M J :=
  ⟨⟨root.1.val + d, by omega⟩, treeLayerAppend root.2 d path⟩

@[simp] theorem physicalSubtreeNode_zero {M J : ℕ} (root : PhysicalNode M J)
    (hd : root.1.val + 0 ≤ J) : physicalSubtreeNode root 0 PUnit.unit hd = root := by
  cases root
  rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedMedian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed update uses the actual integer ceilings, upper median and clamp.
Copies share an entire table within each run and are independent between runs. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

def finiteMedianSeed {Ω : Type*} (N copies : ℕ) (output : Ω → ℕ) (draws : Fin copies → Ω) : ℕ :=
  min N (upperMedian (List.ofFn fun i => output (draws i)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_UnifiedPhysicalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cache's unified index uses warmup indices through T and then
refinement indices T+t. Refinement zero is exactly warmup T, including
terminal physical nodes and short source intervals. -/

namespace EditApproximation

section Unified

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
  (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
  (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
    TargetInterval target.length → List (PhysicalRationalAction M target.length))

def unifiedPhysicalValue (node : PhysicalNode M J) (index : ℕ) (q : TargetInterval target.length) : ℚ :=
  if index ≤ T then physicalLocalWarmup source target U N P F A index (node, q)
  else physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node (index - T) q

end Unified

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical values for the actual local seed passes. This complete
function is a specification for the lazy program, not a table allocated
by the implementation. Copy streams are kept distinct at every pass. -/

namespace EditApproximation

section Sequence

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

def localPassValue (seed : PhysicalEntry M J target.length → ℕ) (pass copy : ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  physicalLocalRefinement source target seed N P F exponent Q (factor pass) tau delta T
    (fun node t => group pass copy node (Fin.ofNat R (t - 1)))
    (physicalLocalOnline source target seed N P F exponent H T (factor pass) tau eta kappa
      (integer pass copy)) node t q

def localSeedSequence (initial : PhysicalEntry M J target.length → ℕ) :
    ℕ → PhysicalEntry M J target.length → ℕ
  | 0 => initial
  | pass + 1 => fun state => min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier pass : ℚ) * localPassValue source target N P F exponent H Q T factor
        tau eta kappa delta group integer (localSeedSequence initial pass) pass copy.val state.1 S state.2⌉₊))

def localRequestValue (initial : PhysicalEntry M J target.length → ℕ)
    (request : PhysicalTableRequest M J target.length) : ℚ :=
  let seed := localSeedSequence source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial request.pass
  unifiedPhysicalValue source target seed N P F exponent Q (factor request.pass) tau delta T
    (fun node t => group request.pass request.copy node (Fin.ofNat R (t - 1)))
    (physicalLocalOnline source target seed N P F exponent H T (factor request.pass) tau eta kappa
      (integer request.pass request.copy)) request.node request.index request.state

end Sequence

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryProgress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency split for keys actually emitted by the adaptive local
queries. Current-index edges descend in the physical tree; older reads
decrease the table rank and never move to an ancestor. -/

namespace EditApproximation

namespace PhysicalTableRequest

def DependencyProgress {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) : Prop :=
  (child.remainingDepth < parent.remainingDepth ∧ child.rank T S ≤ parent.rank T S) ∨
    (child.remainingDepth ≤ parent.remainingDepth ∧ child.rank T S < parent.rank T S)

end PhysicalTableRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u















noncomputable def CoarseInitialAccuracyEvent {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D) : Prop :=
  ∀ i, let k := coarseGuess (coarseEntryWidth x y) i
    CoarseAccuracyEvent k Q lam
      (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
      (coarseEntryTree B D x y) (draws i) k 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def CoarseFullSeedAccuracyEvent (N B : ℕ) {I α : Type*} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α) (draws : CoarseFullSeedDraws B depth x y) : Prop :=
  ∀ i, CoarseInitialAccuracyEvent B (depth i)
    (initialThresholdQ N) (initialLambda N) (x i) (y i) (draws i)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonSeedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adaptive seed passes driven by common per-pass random sources. The
trace stores one source for the actual pass, with no seed-indexed family.
Its returned seed has the original adaptive law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

def CommonSeedTrace (Seed : Type) (Ω : ℕ → Type) : ℕ → Type
  | 0 => Seed
  | pass + 1 => CommonSeedTrace Seed Ω pass × Ω pass

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveSeedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the finite draw history of adaptive seed passes. The final
seed has exactly the existing sequential law, while the history remains
available to the lazy evaluator when it asks for an earlier pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

def AdaptiveSeedTrace (Seed : Type) (Draw : ℕ → Seed → Type) : ℕ → Type
  | 0 => Seed
  | pass + 1 => AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUniformAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

section Uniform

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

abbrev PhysicalUniformOutcome := Unit ⊕ PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R)
  target N P H

end Uniform

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory









abbrev ComputedPhysicalOutcome (source target : List ℕ) (N : ℕ) :=
  PhysicalUniformOutcome (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
    target N (integerParameters N).P (inputHeight N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyWeightedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Width-sensitive work summed over an actual finite dependency expansion.
The bound uses its per-layer counts, including earlier edges that descend. -/

namespace EditApproximation

open Finset Filter

namespace DependencyExpansion

def widthWork (M n : ℕ) (tree : DependencyExpansion) : ℕ :=
  tree.depthWeightedCount (fun d => 1 + n ⌈/⌉ M ^ (tree.depth - d))

end DependencyExpansion

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedQueryProgress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual charged edge either descends at the current index or
uses a strictly earlier index without moving to an ancestor. Coarse
leaves retain their physical depth for source-width accounting. -/

namespace EditApproximation

namespace ChargedPhysicalRequest

def DependencyProgress {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : Prop :=
  (child.depth < parent.depth ∧ child.index ≤ parent.index) ∨
    (child.depth ≤ parent.depth ∧ child.index < parent.index)

theorem table_progress {M J ny passes copies T S : ℕ}
    (parent child : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (h : PhysicalTableRequest.DependencyProgress T S parent.val child.val) :
    DependencyProgress (Sum.inr parent) (Sum.inr child) := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, Nat.add_le_add_right h.2 1⟩
  · exact Or.inr ⟨h.1, Nat.add_lt_add_right h.2 1⟩

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform algorithm on explicitly stored integer symbols, together
with its conditional accuracy theorem. The hypothesis is a finite scalar
Bernstein bound for the two computed finite product laws. -/

namespace EditApproximation

open MeasureTheory

def ComputedBernsteinInputs (N : ℕ) : Prop :=
  FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
    (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure) ∧
  ∀ b : ℕ, ∀ h : Fin (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
        (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseArrayArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse penalty sweep executed on shared-denominator Boolean cells.
Each transition performs a numerator addition and a rational comparison. -/

namespace EditApproximation
namespace BinaryFraction

/-- Invariant of a stored coarse cell on the common denominator. -/
def CoarseGridCell (two a : BinaryFraction) (V D B : ℕ) : Prop :=
  a.representation.den = two.representation.den ∧ a.denominator.length ≤ D ∧
    0 ≤ a.value ∧ a.value ≤ V ∧ a.width ≤ B

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseCompactCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Leading-zero removal is enough: this property does not assert that a
stored rational is reduced by a gcd. -/
def CoarseCompact (a : BinaryFraction) : Prop :=
  a.width ≤ a.representation.storageBits

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- A zero marker or one full shift array on the execution's common grid. -/
def CoarseBinaryBox (two : BinaryFraction) (n V D A : ℕ) (array : CoarseBinaryArray) : Prop :=
  ∀ cells, array = some cells → cells.length = n ∧ ∀ a ∈ cells, CoarseGridCell two a V D A

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Shared evaluation of each child, followed by its exact two-pass
penalty transform, threshold contribution and fixed-grid addition. -/
def coarseBinaryChildren {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ) (allowance : BinaryFraction) :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ → CoarseBinaryArray × ℕ
  | [], _ => (none, 0)
  | (child, draw, below) :: rest, start =>
    let threshold := coarseChildThresholdWithWork B q allowance draw
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate child below childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)
    let total := coarseBinaryAddWithWork contribution.1 remainder.1
    (total.1, threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
      remainder.2 + total.2 + Nat.size start + Nat.size child.word.length + 9)

/-- Binary implementation of the pruning-stopped shared-array evaluator.
The complete tree is a semantic indexed source; visited child descriptors
carry their source offset and length, charged in `coarseBinaryChildren`. -/
def coarseBinaryEval {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (two : BinaryFraction) :
    {d : ℕ} → CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ
  | _, tree, draws, allowance, start =>
    let prune := leWithWork (nat tree.word.length) allowance
    if prune.1 then (none, prune.2 + Nat.size tree.word.length + 1) else
    match tree, draws with
    | .leaf letter, _ =>
      let cells := arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
        coarseGridNatWithWork allowance.denominator allowance.denominator_pos
          (coarseShiftCost k frame (.leaf (B := B) letter) start shift)) (List.finRange (2 * k + 1))
      (some cells.1, prune.2 + cells.2 + Nat.size tree.word.length + 3 * (2 * k + 1) + 1)
    | .branch children, (draws, below) =>
      let result := coarseBinaryChildren k q L two
        (fun child => coarseBinaryEval k q L frame two child) allowance
        (List.ofFn fun i => (children i, draws i, below i)) start
      (result.1, result.2 + prune.2 + Nat.size tree.word.length + B + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Sum the weights of exactly those child calls made by the binary loop. -/
def coarseBinaryChildrenWeight {B d : ℕ} {α : Type*} (q L : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (allowance : BinaryFraction) :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ
  | [] => 0
  | (child, draw, below) :: rest =>
    weight child below (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance draw).1).1 +
    coarseBinaryChildrenWeight q L weight allowance rest

/-- One array unit per expanded child shift and one unit per visited node.
This counter follows the executed pruning and threshold branches. -/
def coarseBinaryWeight {B : ℕ} {α : Type*} (k q L : ℕ) :
    {d : ℕ} → CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ
  | _, tree, draws, allowance =>
    if (leWithWork (nat tree.word.length) allowance).1 then 1 else
    match tree, draws with
    | .leaf _, _ => B * (2 * k + 1) + 1
    | .branch children, (draws, below) => B * (2 * k + 1) + 1 +
      coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child) allowance
        (List.ofFn fun i => (children i, draws i, below i))

def coarseChildrenSpan {B d : ℕ} {α : Type*} :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ
  | [] => 0
  | (child, _, _) :: rest => child.word.length + coarseChildrenSpan rest

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseIndexAdditionalWork {B : ℕ} (q L : ℕ) (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (extra : Fin B → BinaryFraction → ℕ → ℕ) (allowance : BinaryFraction) :
    List (Fin B) → ℕ → ℕ
  | [], _ => 0
  | i :: rest, start =>
    extra i (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance (draw i)).1).1 start +
      coarseIndexAdditionalWork q L width draw extra allowance rest (start + width i)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseIndexSpan {B : ℕ} (width : Fin B → ℕ) : List (Fin B) → ℕ
  | [] => 0
  | i :: rest => width i + coarseIndexSpan width rest

def coarseIndexWeight {B : ℕ} (q L : ℕ) (draw : Fin B → Fin B)
    (weight : Fin B → BinaryFraction → ℕ) (allowance : BinaryFraction) : List (Fin B) → ℕ
  | [] => 0
  | i :: rest => weight i (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance (draw i)).1).1 +
      coarseIndexWeight q L draw weight allowance rest

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseRootExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem coarseRootDenominator_value (B q L d : ℕ) :
    bitWordValue (coarseRootDenominator B q L d).1 = coarseCommonDenominator 1 q L B d := by
  simp only [coarseRootDenominator, coarseDenominatorWithWork_value, bitWordValue_bits]

 theorem coarseRootDenominator_pos (B q L d : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) :
    0 < bitWordValue (coarseRootDenominator B q L d).1 := by
  rw [coarseRootDenominator_value]
  unfold coarseCommonDenominator
  positivity

/-- Counted root setup and array lookup around the complete binary coarse
recursion. The common denominator is built from bits, not a free conversion. -/
def coarseRootWithWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1)) :
    BinaryFraction × ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  let evaluated := coarseBinaryEval k q L frame two.1 tree draws allowance.1 start
  (coarseBinaryRead evaluated.1 shift.val,
    den.2 + two.2 + allowance.2 + evaluated.2 + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- A candidate executes the whole root recurrence, then adds its literal
guess and doubles the result using Boolean arithmetic. -/
def coarseCandidateWithWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    BinaryFraction × ℕ :=
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseRootWithWork k q L hB hq hL
    (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
    (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
  let shifted := canonicalAddWithWork root.1 (nat k)
  let doubled := canonicalMulWithWork (nat 2) shifted.1
  (doubled.1, root.2 + shifted.2 + doubled.2 + Nat.size k + 3)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- Padding and framing are index calculations over the original stored
input. These views do not allocate a padded string. -/
def coarsePaddedRead {α : Type*} (n : ℕ) (word : List α) (i : ℕ) : Option (Option α) :=
  if i < n then some word[i]? else none

def coarseFramedRead {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) : Option (Option α) :=
  if k ≤ i ∧ i < k + n then some word[i - k]? else none

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- Cached length of a descriptor into a virtually padded source. -/
def coarseDescriptorLength (B d n start : ℕ) : ℕ := min (B ^ d) (n - start)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseReadShiftCost {α : Type*} [DecidableEq α] (k n : ℕ) (target : List α)
    (letter : Option (Option α)) (start : ℕ) (shift : Fin (2 * k + 1)) : ℕ :=
  match letter with
  | none => 0
  | some letter => if coarseFramedRead k n target (start + shift.val) = some letter then 0 else 1

/-- Core arithmetic over source descriptors. The separate descriptor/read
counter charges address arithmetic and original-array accesses. -/
def coarseReadCore {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L n : ℕ) (source target : List α) (two : BinaryFraction) :
    (d : ℕ) → (offset : ℕ) → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ
  | 0, offset, _, allowance, start =>
    let size := coarseDescriptorLength B 0 n offset
    let prune := leWithWork (nat size) allowance
    if prune.1 then (none, prune.2 + Nat.size size + 1) else
    let cells := arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
      coarseGridNatWithWork allowance.denominator allowance.denominator_pos
        (coarseReadShiftCost k n target (coarsePaddedRead n source offset) start shift))
      (List.finRange (2 * k + 1))
    (some cells.1, prune.2 + cells.2 + Nat.size size + 3 * (2 * k + 1) + 1)
  | d + 1, offset, (draws, below), allowance, start =>
    let size := coarseDescriptorLength B (d + 1) n offset
    let prune := leWithWork (nat size) allowance
    if prune.1 then (none, prune.2 + Nat.size size + 1) else
    let result := coarseIndexChildren k q L two
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d))
      (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
      draws allowance (List.finRange B) start
    (result.1, result.2 + prune.2 + Nat.size size + B + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- All descriptor and original-input operations alongside the core
arithmetic. Threshold decisions are exactly those of the evaluated call. -/
def coarseIndexedExtra {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) : (d offset : ℕ) → CoarseThresholdDraws B d →
    BinaryFraction → ℕ → ℕ
  | 0, offset, _, allowance, start =>
    let descriptor := coarseDescriptorWithWork B 0 n offset
    if (leWithWork (nat (coarseDescriptorLength B 0 n offset)) allowance).1 then descriptor.2 else
    let letter := coarsePaddedReadWithWork n source offset
    descriptor.2 + letter.2 + ((List.finRange (2 * k + 1)).map fun shift =>
      (coarseReadShiftWithWork k n target letter.1 start shift).2).sum
  | d + 1, offset, (draws, below), allowance, start =>
    let descriptor := coarseDescriptorWithWork B (d + 1) n offset
    if (leWithWork (nat (coarseDescriptorLength B (d + 1) n offset)) allowance).1 then descriptor.2 else
    let capacity := bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B => coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B => coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
    descriptor.2 + capacity.2 + coarseIndexAdditionalWork q L
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws
      (fun i a s => coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s +
        3 * ((childOffset i).2 + (childSize i).2 +
          (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 + 3))
      allowance (List.finRange B) start

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



/-- Entire dyadic initial estimator, including direct cases, every root
execution, binary minimum, ceiling, and final integer clamp. -/
def coarseInitialWithWork {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ × ℕ :=
  let long := binaryNaturalCompareWithWork (2 * x.length) y.length
  if long.1 = .lt then (min N y.length, long.2 + Nat.size N + Nat.size y.length + 4) else
  let equal := naturalListEqualWithWork x y
  if equal.1 then (0, long.2 + equal.2 + 3) else
  let roots := arithmeticMapWithWork (fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i))
    (List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1))
  let smallest := coarseMinimumWithWork roots.1
  let rounded := naturalCeilingWithWork smallest.1
  let result := wordMinWithWork N.bits rounded.1
  (bitWordValue result.1, long.2 + equal.2 + roots.2 + smallest.2 + rounded.2 + result.2 +
    Nat.size N + 6)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseLevelMagnitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Loose magnitude bound for all partial child sums. Its bit length is
linear in the depth and parameter bit lengths. -/
def coarseLevelMagnitude (N k B d : ℕ) : ℕ :=
  (N + k + 1) * (2 * B + 2) ^ (d + 1)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrencePrefix
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cached binary position counts. Inserting a position and counting positions
strictly below a boundary both follow one root-to-leaf path. Counts are stored
at internal nodes, so a prefixCount query does not traverse a whole interval. -/

namespace EditApproximation



namespace PositionCounts









@[simp] theorem count_add (tree : PositionCounts) (d i : ℕ) :
    (tree.add d i).count = tree.count + 1 := by
  cases d with
  | zero => rfl
  | succ d =>
    simp only [add]
    split_ifs <;> rfl

def prefixCount (tree : PositionCounts) : ℕ → ℕ → ℕ
  | 0, t => if t = 0 then 0 else tree.count
  | d + 1, t =>
    if t ≤ 2 ^ d then tree.left.prefixCount d t
    else tree.left.count + tree.right.prefixCount d (t - 2 ^ d)

@[simp] theorem prefix_empty (d t : ℕ) : prefixCount .empty d t = 0 := by
  induction d generalizing t with
  | zero => simp only [prefixCount, count, ite_self]
  | succ d ih => simp only [prefixCount, left, right, count, ih, zero_add, ite_self]

end PositionCounts

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseNumericalUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseNumericalUnit (H : ℕ) : ℕ :=
  bitPowerBitBudget H (7 * H ^ 3 + 3) +
    1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2 +
    100001000 * (H ^ 3 + 1) ^ 2

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- A finite uniform bound on the actually executed source-index operations.
The depth and offset ranges are the original padded source capacity. -/
structure CoarseReadBudget (B R k n : ℕ) (source target : List ℕ) (K : ℕ) : Prop where
  descriptor : ∀ d ≤ R, ∀ offset ≤ B ^ R, (coarseDescriptorWithWork B d n offset).2 ≤ K
  power : ∀ d ≤ R, (bitPowerWithWork B.bits d).2 ≤ K
  offset : ∀ offset ≤ B ^ R, ∀ i : Fin B,
    ∀ d ≤ R, (coarseChildOffsetWithWork offset (B ^ d) i.val).2 ≤ K
  advance : ∀ s ≤ n, ∀ width ≤ n, (binaryNaturalAddWithWork s width).2 ≤ K
  sourceRead : ∀ offset ≤ B ^ R, (coarsePaddedReadWithWork n source offset).2 ≤ K
  mismatch : ∀ offset ≤ B ^ R, ∀ s ≤ n, ∀ shift : Fin (2 * k + 1),
    (BinaryFraction.coarseReadShiftWithWork k n target
      (coarsePaddedRead n source offset) s shift).2 ≤ K

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRootCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseRootReadExtra {B d : ℕ} (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (x y : List ℕ) (draws : CoarseThresholdDraws B d) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  coarseIndexedExtra k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedInitialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedCandidateWithWork coarseCandidateWithWork coarseRootReadExtra
  arithmeticMapWithWork coarseMinimumWithWork naturalCeilingWithWork wordMinWithWork

def coarseInitialReadExtra {B d : ℕ} (q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (x y : List ℕ) (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  if (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = .lt then 0 else
  if (naturalListEqualWithWork x y).1 then 0 else
  ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map fun i =>
    coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y (draws i)).sum

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted register loops for the global integer parameters. Multiplication
and division here are word operations; the word-cap theorem below supplies
room for their intermediate integers. -/
namespace EditApproximation
open Filter



 @[simp] theorem parameterPowerWithWork_spec (a k : ℕ) :
    parameterPowerWithWork a k = (a ^ k, 2 * k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [parameterPowerWithWork, ih, pow_succ]; congr 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 @[simp] theorem naturalPairWithWork_value (a b : ℕ) :
    (naturalPairWithWork a b).1 = Nat.pair a b := by
  unfold naturalPairWithWork Nat.pair
  split_ifs <;> rfl



 @[simp] theorem treeLayerCodeWithWork_value (M d : ℕ) (path : TreeLayer M d) :
    (treeLayerCodeWithWork M d path).1 = treeLayerCode M d path := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [treeLayerCodeWithWork, treeLayerCode, ih]



 @[simp] theorem physicalNodeCodeWithWork_value {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).1 = physicalNodeCode node := by
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_value,
    parameterPowerWithWork_spec, physicalNodeCode]



 @[simp] theorem physicalEntryCodeWithWork_value {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).1 = physicalEntryCode entry := by
  simp only [physicalEntryCodeWithWork, physicalNodeCodeWithWork_value,
    physicalEntryCode, childInputCode, Fin.val_zero, zero_add, one_mul, pow_two]



 @[simp] theorem physicalTableCodeWithWork_value {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).1 = PhysicalTableRequest.code copies T S request := by
  simp only [physicalTableCodeWithWork, physicalEntryCodeWithWork_value,
    parameterPowerWithWork_spec, PhysicalTableRequest.code, PhysicalTableRequest.entryCapacity, pow_two]



 @[simp] theorem chargedPhysicalCodeWithWork_value {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).1 = request.code := by
  cases request <;> simp only [chargedPhysicalCodeWithWork, ChargedPhysicalRequest.code,
    physicalEntryCodeWithWork_value, physicalTableCodeWithWork_value]



 @[simp] theorem physicalScalarCodeWithWork_value {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).1 = physicalScalarCode key := by
  rcases key with ⟨online | group, index⟩ <;>
    simp only [physicalScalarCodeWithWork, naturalPairWithWork_value,
      physicalEntryCodeWithWork_value, physicalNodeCodeWithWork_value, physicalScalarCode]

section Family
variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 @[simp] theorem physicalFamilyCodeWithWork_value
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).1 =
      physicalFamilyCode target N P F exponent H Q passes copies key := by
  simp only [physicalFamilyCodeWithWork, physicalScalarCodeWithWork_value,
    naturalPairWithWork_value, physicalFamilyCode]

end Family



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedCachedKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete refinement return includes literal power-denominator
construction, multiplication, division and trimming before cache insertion. -/

namespace EditApproximation

abbrev CachePoly := FiniteBitPolynomial (Fin 4)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every value retained by the actual binary dictionary obeys the
semantic value bound. This includes every allocated path, not only keys
queried after the computation. -/

namespace EditApproximation
namespace BinaryMemo

def AllValues {α : Type*} (P : α → Prop) (memory : BinaryMemo α) : Prop :=
  ∀ key value, memory.lookup key = some value → P value

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActionInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the final adaptive child gather.  The temporary list and
its sorting work depend on emitted actions, rather than the full table. -/

namespace EditApproximation

def queryNeededInputsBitBudget (actions M B : ℕ) : ℕ :=
  actions * (5 * M + 3) + 2 * M + actions * M +
    (actions * M + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 4

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGridCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scale guard bounds the number of grid points even when the center
radius is as large as the input.  These bounds include construction of
all points, before subsequent eligibility filtering. -/

namespace EditApproximation

def queryGridPointsBitBudget (P K B : ℕ) : ℕ :=
  100 * (B + 2) ^ 2 + gridStateBoxBitBudget (4 * K * P + 2) (B + 1) + 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRawCenterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete work of scale enumeration and unfiltered center construction.
Quadratic duplicate removal is bounded by the actual local grid sizes. -/

namespace EditApproximation.BinaryFraction

def queryScalesBitBudget (B : ℕ) : ℕ :=
  queryExponentsBitBudget B + (B + 1) * (B + 6) + 1

def queryRawCentersBitBudget (P F B : ℕ) : ℕ :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCellCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the actual cell scan at an accepted query scale.
The scale-window test controls its count; the binary arithmetic controls
its coordinate widths independently of the numeric target length. -/

namespace EditApproximation.BinaryFraction

def queryCellScanBitBudget (F exponent B : ℕ) : ℕ :=
  let K := (32 * F + 2) * 2 ^ exponent + 2
  2000 * (B + 4) ^ 2 + targetCellsBitBudget K K (4 * B + 40)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupKeyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, construction work and coordinate widths of the actual group
key list, including the binary dyadic scale enumeration. -/

namespace EditApproximation.BinaryFraction

def queryGroupKeysBitBudget (F exponent B : ℕ) : ℕ :=
  let L := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryCellScanBitBudget F exponent B + 5 * L + 5) + exponent + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCellStateCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryCellStatesWithWork (n P b exponent : ℕ) (cell : ℕ × ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  (states.1, spacing.2 + side.2 + states.2 + exponent + 3)

def queryCellStatesBitBudget (P exponent B : ℕ) : ℕ :=
  100 * (B + 5) ^ 2 + 2000 * (B + 4) ^ 2 +
    cellStatesBitBudget P P (16 * B + 200) + exponent + 3

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineKeyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryOnlineKeysBitBudget (B : ℕ) : ℕ :=
  queryScalesBitBudget B + (B + 1) * (600 * (B + 3) ^ 2 + 6) + 1

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupportCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete initial-support gather, including repeated cells and
unfiltered raw centers, has a local-parameter bound. -/

namespace EditApproximation.BinaryFraction

def queryInitialSupportLength (P F exponent B : ℕ) : ℕ :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  1 + raw + groups * P ^ 2 + (B + 1)

def queryInitialSupportBitBudget (P F exponent B : ℕ) : ℕ :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  queryRawCentersBitBudget P F B + queryGroupKeysBitBudget F exponent B +
    groups * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
    queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * raw + groups * P ^ 2 + 5

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentativeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryEarlierRepresentativesLength (P F exponent B : ℕ) : ℕ :=
  (B + 1) * ((64 * F * P + 2) ^ 2 +
    ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1)

def queryEarlierRepresentativesBitBudget (P F exponent B R : ℕ) : ℕ :=
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let L := (P + 1) ^ 2
  R + localRepresentativesBitBudget P F B * (R + 2) + queryGroupKeysBitBudget F exponent B +
    groups * (cellCentersBitBudget P P (16 * B + 200) * (R + 1) + 5 * L + 4) +
    queryOnlineKeysBitBudget B + 2 * ((B + 1) * (64 * F * P + 2) ^ 2) + groups * L + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBandInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryWideInputsBitBudget (M P count B : ℕ) : ℕ :=
  let G := (40 * P + 2) ^ 2
  let C := wideChildGridBitBudget P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

def queryBandInputsBitBudget (M P F exponent B R : ℕ) : ℕ :=
  queryEarlierRepresentativesBitBudget P F exponent B R +
    queryWideInputsBitBudget M P (queryEarlierRepresentativesLength P F exponent B) B + 1

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedBody
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.physicalTableCodeWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite-domain guards execute binary comparisons on table coordinates.
Random-source coordinates pass through the guard unchanged. -/

namespace EditApproximation

@[simp] theorem queryNaturalLEWithWork_value (a b : ℕ) :
    (wordLEWithWork a.bits b.bits).1 = true ↔ a ≤ b := by
  simp only [wordLEWithWork_value, bitWordValue_bits]



@[simp] theorem queryPhysicalBoundedWithWork_value {M J n : ℕ}
    (passes copies T S : ℕ) (request : PhysicalTableRequest M J n) :
    (queryPhysicalBoundedWithWork passes copies T S request).1 = true ↔
      request.Bounded passes copies T S := by
  simp only [queryPhysicalBoundedWithWork, Bool.and_eq_true, decide_eq_true_eq,
    binaryNaturalCompareWithWork_lt, wordLEWithWork_value, bitWordValue_bits,
    binaryNaturalAddWithWork_value, PhysicalTableRequest.Bounded]
  tauto

section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})





@[simp] theorem querySupportedChildWithWork_value
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent) :
    (querySupportedChildWithWork passes copies T S parent key).1 = true ↔
      SourceRanked.supportedChild (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) parent.val key := by
  cases key with
  | inl source => exact iff_of_true rfl trivial
  | inr child => exact queryPhysicalBoundedWithWork_value passes copies T S child.val



end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRestrictionCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

/-- A failed domain test supplies the same zero word to the adaptive continuation. -/
def restrictedOracle {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (oracle : {key // P key} → BinaryFraction) (key : ι) : BinaryFraction :=
  if h : (test key).1 = true then oracle ⟨key, (htest key).mp h⟩ else BinaryFraction.nat 0

def restrictedReadWork {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (readWork : {key // P key} → ℕ) (key : ι) : ℕ :=
  (test key).2 + if h : (test key).1 = true then readWork ⟨key, (htest key).mp h⟩ else 0

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

abbrev QueryBoundedChild := Sum σ {child : {r : PhysicalTableRequest M J n //
  r.Bounded passes copies T S} // child.val.combinedRank T S < parent.val.combinedRank T S}

def queryRestrictedPhysicalOracle (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) :
    QueryPhysicalChild (σ := σ) passes copies T S parent → BinaryFraction :=
  BitQuery.restrictedOracle _ (querySupportedChildWithWork passes copies T S parent)
    (querySupportedChildWithWork_value passes copies T S parent)
    (fun key => oracle (SourceRanked.supportedChildMap (PhysicalTableRequest.combinedRank T S)
      (PhysicalTableRequest.Bounded passes copies T S) parent key))

@[simp] theorem queryRestrictedPhysicalOracle_source
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) (source : σ) :
    queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inl source) = oracle (Sum.inl source) := rfl

end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSampleCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source-key builder executes all scale/sample loops. Their cost
is bounded using the computed count, which is capped by the arity. -/

namespace EditApproximation.BinaryFraction

def queryGroupSamplesBitBudget (M eM eb eF B : ℕ) : ℕ :=
  let L := 7 + eM + eF
  groupScalesBitBudget eM eb eF + 4 * L +
    L * (L + groupSampleCountBitBudget B + 7 * M + 6) + eb + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSourceCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryGroupSourceKeysLength (M F exponent eM eF B : ℕ) : ℕ :=
  (B + 1) * ((((32 * F + 2) * 2 ^ exponent + 2) ^ 2) * ((7 + eM + eF) * M))

def queryGroupSourceKeysBitBudget (M F exponent eM eF B : ℕ) : ℕ :=
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let samples := (7 + eM + eF) * M
  let sampleWork := queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let scaleWork := queryCellScanBitBudget F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (scaleWork + cells * samples + 3) + 2

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScopedSourceCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source ports are bounded only at keys visited by the adaptive local
loops. Unused natural-number coordinates require no uniform size assumption. -/

namespace EditApproximation.BinaryFraction

def queryGroupBufferReadBudget (count B V : ℕ) : ℕ :=
  count * (40 * (40 * B + 500) + 15) + 200 * (V + 1) ^ 2 +
    30 * (V + 1) * (V + (40 * B + 500) + 1) + 4

def queryOnlineBufferReadBudget (count B V : ℕ) : ℕ :=
  count * (24 * (B + 1) + 9) + 200 * (V + 1) ^ 2 + 2

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupLabelCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryGroupLabelsBitBudget (M B R : ℕ) : ℕ :=
  groupSampleCountBitBudget B + 8 * (groupSampleCountWordBudget B) +
    M * (R + 4) + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGapStateCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

def queryGapStatesBitBudget (left right B : ℕ) : ℕ :=
  let C := 1000 * (B + 10) ^ 2
  C + gridPointsBitBudget left (B + 2) +
    left * (C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + right + 7) + 3

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRoundedStateCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryRoundedStatesBitBudget (left right exponent B : ℕ) : ℕ :=
  100000 * (32 * B + 210) ^ 2 + queryGapStatesBitBudget left right (32 * B + 200) + exponent + 12

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryGroupInputsLength (M exponent : ℕ) : ℕ :=
  M * ((24 * 2 ^ exponent * M + 2) * (4 * 2 ^ exponent + 4))

def queryGroupInputsBitBudget (M exponent B R : ℕ) : ℕ :=
  let L := (24 * 2 ^ exponent * M + 2) * (4 * 2 ^ exponent + 4)
  queryGroupLabelsBitBudget M B R +
    M * (queryRoundedStatesBitBudget (24 * 2 ^ exponent * M + 2) (4 * 2 ^ exponent + 4) exponent B +
      5 * L + 4) + 1

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedCellCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def querySharedCellInputsLength (M exponent eM eF : ℕ) : ℕ :=
  (7 + eM + eF) * queryGroupInputsLength M exponent

def querySharedCellInputsBitBudget (M exponent eM eb eF B R : ℕ) : ℕ :=
  let L := 7 + eM + eF
  groupScalesBitBudget eM eb eF + 4 * L +
    L * (queryGroupInputsBitBudget M exponent B R + L + queryGroupInputsLength M exponent + 4) + eb + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def querySharedInputsLength (M F exponent eM eF B : ℕ) : ℕ :=
  (B + 1) * ((((32 * F + 2) * 2 ^ exponent + 2) ^ 2) * querySharedCellInputsLength M exponent eM eF)

def querySharedInputsBitBudget (M F exponent eM eF B R : ℕ) : ℕ :=
  let cells := ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let samples := querySharedCellInputsLength M exponent eM eF
  let sampleWork := querySharedCellInputsBitBudget M exponent eM B eF (16 * B + 200) R
  let scaleWork := queryCellScanBitBudget F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 + (B + 1) * (scaleWork + cells * samples + 3) +
    (querySharedInputsLength M F exponent eM eF B + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 3

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBufferedSharedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared-state generation using the actual gathered scalar buffer.
The lookup bound is instantiated at visited keys, including discarded cells. -/

namespace EditApproximation.BinaryFraction

def queryBufferedGroupReadBudget (M F exponent eM eF B V : ℕ) : ℕ :=
  queryGroupBufferReadBudget (queryGroupSourceKeysLength M F exponent eM eF B) B V

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedSeed
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Seed values are computed by actual coarse-cache or previous-pass
requests.  The copy median and the pass-zero test have explicit work. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem querySeedMedianWithWork_value (N multiplier : ℕ) (words : List BinaryFraction) :
    (querySeedMedianWithWork N multiplier words).1.value =
      (min N (upperMedian (words.map fun word => ⌈(multiplier : ℚ) * word.value⌉₊)) : ℕ) := by
  simp only [querySeedMedianWithWork, ofNaturalWord_value, seedMedianWithWork_value]

end BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBuffers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



theorem queryChildReadWithWork_budget {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (words : List BinaryFraction) (i : Fin M) (r : TargetInterval n) :
    (queryChildReadWithWork keys words i r).2 ≤ queryDataReadBudget M n keys := by
  exact queryChildReadWithWork_cost keys words i r _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)



end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete selectors of the adaptive local program. Source and table
lookups are evaluated by their counted finite-buffer routines. Their value
identities hold even for arbitrary gathered answer lists. -/

namespace EditApproximation
namespace BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

def queryOnlineSelectWithWork (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :=
  preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer N q

def queryGroupSelectWithWork (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :=
  preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi N draw q

end Selectors
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete charged local refinement request: earlier history, shared
samples, selected current inputs and the final binary continuation. -/

namespace EditApproximation

section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRefinement : BitQuery ι BinaryFraction :=
  queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF a t parentInitial draw q
    readEarlier readCurrent
    (fun keys words => BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP
      tau a eta kappa parentInitial child initial R hc hi t integer keys words q)
    (fun keys words => BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
      eM eF hP hM hF tau a parentInitial child initial R hc hi draw keys words q)
    (fun earlierKeys earlierWords groups online currentKeys currentWords =>
      BitQuery.compute (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta parentInitial
        t earlierKeys earlierWords groups online currentKeys currentWords q))

end Local
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random words are gathered before the adaptive local selectors run.
The online sampling range is computed from the gathered mass words. -/

namespace EditApproximation

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRandomSources : BitQuery ι BinaryFraction :=
  queryGroupSourceGather M N F Q exponent eM eF hM hF a parentInitial q readGroup
    fun groupKeys groupWords =>
      queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
        fun onlineKeys onlineWords =>
          queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
            tau a eta kappa delta t parentInitial child initial R hc hi
            (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
            (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords)
            q readEarlier readCurrent

end Sources
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass and initial words are read into counted finite buffers before
any random source range or local action is constructed. -/

namespace EditApproximation

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalBand : BitQuery ι BinaryFraction :=
  queryBandGather M parent N P F exponent hP a parentInitial q readMass readInitial
    fun keys massWords initialWords =>
      queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial
        (BinaryFraction.queryChildReadWithWork keys massWords)
        (BinaryFraction.queryChildReadWithWork keys initialWords)
        (BinaryFraction.queryDataReadBudget M target.length keys)
        (BinaryFraction.queryChildReadWithWork_budget keys massWords)
        (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
        q readGroup readInteger readEarlier readCurrent

end Band
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete adaptive local program, beginning with the parent query.
Every intermediate buffer is constructed after the answers determining
its support, and every scalar source range is computed before its read. -/

namespace EditApproximation

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalProgram : BitQuery ι BinaryFraction :=
  queryInitialGather N P F exponent hP a q readParent fun keys words =>
    queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t (BinaryFraction.queryParentReadWithWork keys words)
      readMass readInitial readGroup readInteger q readEarlier readCurrent

end Program
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryMeanRead
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted averaging of the warmup words actually requested. The fixed
requested denominator is retained even in the simulation of arbitrary
intermediate answer lists. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryMeanWithWork_value (count : ℕ) (words : List BinaryFraction) :
    (queryMeanWithWork count words).1.value = (words.map value).sum / count := by
  simp only [queryMeanWithWork, divWithWork_value, sumListWithWork_value, nat_value]

end BinaryFraction



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full charged refinement program on physical ranked requests and
scalar source requests.  This connects the local Boolean implementation
to the same adaptive query used in the accuracy and dependency proofs. -/

namespace EditApproximation

section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)

def queryPhysicalRandomDataRequest :
    BitQuery (Sum σ {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S})
      BinaryFraction :=
  queryLocalProgram source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    (fun r => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalWarmupRead copies pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T) r))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2))
    (fun key => BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readGroup key))
    (fun key range => BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readInteger key range)) q
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input))
    (fun input => BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input))

end Physical
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged local refinement uses the independent source
family, with computed scalar guards and pass/copy addresses. -/

namespace EditApproximation

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R)
  (q : TargetInterval target.length)

def queryFamilyRefinement :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S}) BinaryFraction :=
  queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta copies pass copy T S t ht node hbelow
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive internal refinement steps expose exactly the independent
scalar family and smaller physical table requests of the reference body. -/

namespace EditApproximation

section Active
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)

include hindex in
omit [DecidableEq α] [NeZero M] in
theorem active_request_eq :
    PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold PhysicalTableRequest.refinement
  rw [hi]

def queryFamilyActive :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < request.combinedRank T S}) BinaryFraction :=
  BitQuery.mapKeysWithWork
    (fun key => (Sum.map id (fun child => ⟨child.val, by
      simpa only [active_request_eq (target := target) (T := T) (request := request) (hindex := hindex)] using child.property⟩) key, 1))
    (queryFamilyRefinement (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
      request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state)

end Active

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

def queryFamilyBoundedActive :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        child.val.combinedRank T S < parent.val.combinedRank T S}) BinaryFraction :=
  queryRestrictPhysicalBody (passes + 1) copies T S parent
    (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      T S passes copies parent.val hindex hbelow)

end Bounded
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyReaderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryFamilySourceReadBudget (J B W : ℕ) : ℕ :=
  200 * (1000 * (B + 1) + 1000 + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFinishCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryRefinementFinishBitBudget (M P F B R G O : ℕ) : ℕ :=
  R + localRepresentativesBitBudget P F B * (R + 2) +
    physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2) G O (B + 4) * tableReadFactor R + 2

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryScalesAllocation_le_work (N F : ℕ) (a value : BinaryFraction) :
    queryScalesAllocation N F a value ≤ (queryScalesWithWork N F a value).2 := by
  have he := queryExponentsAllocation_le_work N F a value
  have hm := arithmeticMapAllocation_le_work (fun e => (bitWordValue (powerTwoWord e), e + 3))
    (fun e => e + 1) (queryExponentsWithWork N F a value).1 (fun _ _ => by dsimp only; omega)
  unfold queryScalesAllocation queryScalesWithWork
  dsimp only
  omega



theorem queryRawCentersAllocation_le_work {n : ℕ} (N P F : ℕ) (a value : BinaryFraction) (q : TargetInterval n) :
    queryRawCentersAllocation N P F a value q ≤ (queryRawCentersWithWork N P F a value q).2 := by
  let build := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let states := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi
    (states.1, spacing.2 + states.2 + 1)
  have hs := queryScalesAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hc := arithmeticFlatMapAllocation_le_work build (fun b => seedGridSpacingAllocation b P +
    gridStateBoxAllocation n (bitWordValue (seedGridSpacingWithWork b P).1)
      (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi) (queryScalesWithWork N F a value).1 (by
      intro b _
      have hg := gridStateBoxAllocation_le_work n (bitWordValue (seedGridSpacingWithWork b P).1)
        (bitWordValue (naturalCeilingWithWork value).1) q.lo q.hi
      have hs := seedGridSpacingAllocation_le_work b P
      dsimp only [build]
      omega)
  have he := queryEraseAllocation_le_work queryIntervalEqualWithWork queryIntervalEqualAllocation
    (arithmeticFlatMapWithWork build (queryScalesWithWork N F a value).1).1 queryIntervalEqualAllocation_le_work
  unfold queryRawCentersAllocation queryRawCentersWithWork
  dsimp only [build] at hc he ⊢
  omega



theorem queryGroupKeysAllocation_le_work {n : ℕ} (N F exponent : ℕ) (a value : BinaryFraction) (q : TargetInterval n) :
    queryGroupKeysAllocation N F exponent a value q ≤ (queryGroupKeysWithWork N F exponent a value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun b =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
    let cells := targetCellsWithWork side.1 (bitWordValue radius) q
    let labeled := arithmeticMapWithWork (fun cell => ((b, cell), 1)) cells.1
    (labeled.1, side.2 + cells.2 + labeled.2 + 2)
  have hs := queryScalesAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hk := arithmeticFlatMapAllocation_le_work build (fun b =>
      let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
      canonicalMulAllocation (inversePowerTwo exponent) (nat b) + targetCellsAllocation side (bitWordValue radius) q +
        arithmeticMapAllocation (fun _ => 1) (targetCellsWithWork side (bitWordValue radius) q).1)
      (queryScalesWithWork N F a value).1 (by
        intro b _
        have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat b)
        have hc := targetCellsAllocation_le_work (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1
          (bitWordValue radius) q
        have hl := arithmeticMapAllocation_le_work (fun cell => ((b, cell), 1)) (fun _ => 1)
          (targetCellsWithWork (canonicalMulWithWork (inversePowerTwo exponent) (nat b)).1 (bitWordValue radius) q).1
          (fun _ _ => le_rfl)
        dsimp only [build]
        omega)
  unfold queryGroupKeysAllocation queryGroupKeysWithWork
  dsimp only [radius, build] at hk ⊢
  omega



theorem queryOnlineKeysAllocation_le_work {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    queryOnlineKeysAllocation N P F hP a value q ≤ (queryOnlineKeysWithWork N P F hP a value q).2 := by
  have hs := queryScalesAllocation_le_work N F a value
  have hk := arithmeticMapAllocation_le_work (fun b =>
    let spacing := seedGridSpacingWithWork b P
    let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) q
    ((b, center.1), spacing.2 + center.2 + 2)) (fun b =>
    seedGridSpacingAllocation b P + roundStateAllocation (bitWordValue (seedGridSpacingWithWork b P).1) q + 1)
      (queryScalesWithWork N F a value).1 (by
        intro b _
        have hs := seedGridSpacingAllocation_le_work b P
        have hr := roundStateAllocation_le_work (bitWordValue (seedGridSpacingWithWork b P).1)
          (seedGridSpacingWithWork_pos b P hP) q
        dsimp only
        omega)
  dsimp only at hk
  unfold queryOnlineKeysAllocation queryOnlineKeysWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSourceSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction





theorem groupKeySampleBlockAllocation_le_work {M F Q : ℕ} (b : ℕ) (raw : List BinaryFraction)
    (hs : raw.map value = groupDyadicScales M b F) (cell : ℕ × ℕ)
    (scale : Fin (groupDyadicScales M b F).length) :
    groupKeySampleBlockAllocation (Q := Q) b raw hs cell scale ≤ (groupKeySampleBlock (Q := Q) b raw hs cell scale).2 := by
  let word := queryScaleAt raw (groupDyadicScales M b F) hs scale
  let count := groupSampleCountWithWork M Q b word
  have hc : bitWordValue count.1 = groupSampleCount M Q b (groupDyadicScaleAt M b F scale) := by
    rw [groupSampleCountWithWork_value, queryScaleAt_value]
    rfl
  let coordinates := queryFinRange (bitWordValue count.1)
    (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) hc
  have hg := groupSampleCountAllocation_le_work M Q b word
  have hm := arithmeticMapAllocation_with_spine (fun sample =>
    ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2)) (fun _ => 2) coordinates (fun _ _ => le_rfl)
  unfold groupKeySampleBlockAllocation groupKeySampleBlock
  dsimp only [word, count, coordinates] at hg hm ⊢
  omega



theorem queryGroupKeySamplesAllocation_le_work (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    queryGroupKeySamplesAllocation M F Q eM eb eF hM hF cell ≤
      (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF cell).2 := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hM rfl hF
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  have hg := groupScalesAllocation_le_work eM eb eF
  have hm := arithmeticFlatMapAllocation_le_work (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
    (groupKeySampleBlockAllocation (Q := Q) b scales.1 hs cell)
    (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen)
    (fun scale _ => groupKeySampleBlockAllocation_le_work (Q := Q) b scales.1 hs cell scale)
  change groupScalesAllocation eM eb eF + 2 * scales.1.length + eb + 1 +
    arithmeticFlatMapAllocation (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
      (groupKeySampleBlockAllocation (Q := Q) b scales.1 hs cell)
      (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen) ≤
    scales.2 + 4 * scales.1.length +
      (arithmeticFlatMapWithWork (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
        (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen)).2 + eb + 4
  change groupScalesAllocation eM eb eF ≤ scales.2 at hg
  omega



theorem queryGroupSourceKeysAllocation_le_work {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n) :
    queryGroupSourceKeysAllocation M N F Q exponent eM eF hM hF a value q ≤
      (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    let cells := targetCellsWithWork side.1 (bitWordValue radius) q
    let sources := arithmeticFlatMapWithWork (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF) cells.1
    (sources.1, side.2 + cells.2 + sources.2 + eb + exponent + 4)
  let allocation := fun eb =>
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    let cells := (targetCellsWithWork side (bitWordValue radius) q).1
    canonicalMulAllocation (inversePowerTwo exponent) (nat (2 ^ eb)) + targetCellsAllocation side (bitWordValue radius) q +
      arithmeticFlatMapAllocation (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF)
        (queryGroupKeySamplesAllocation M F Q eM eb eF hM hF) cells + eb + exponent + 2
  have he := queryExponentsAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hg := arithmeticFlatMapAllocation_le_work build allocation (queryExponentsWithWork N F a value).1 (by
    intro eb _
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    have hs := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat (2 ^ eb))
    have hc := targetCellsAllocation_le_work side (bitWordValue radius) q
    have hm := arithmeticFlatMapAllocation_le_work (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF)
        (queryGroupKeySamplesAllocation M F Q eM eb eF hM hF)
        (targetCellsWithWork side (bitWordValue radius) q).1
        (fun cell _ => queryGroupKeySamplesAllocation_le_work M F Q eM eb eF hM hF cell)
    dsimp only [build, allocation, side] at hc hm ⊢
    omega)
  unfold queryGroupSourceKeysAllocation queryGroupSourceKeysWithWork
  dsimp only [build, allocation, radius] at hg ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistorySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryEarlierRepresentativesAllocation_le_work {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (allocation : TargetInterval n → ℕ) (q : TargetInterval n)
    (h : ∀ r, allocation r ≤ (initial r).2) :
    queryEarlierRepresentativesAllocation N P F exponent hP a initial allocation q ≤
      (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).2 := by
  let build := fun key : ℕ × ℕ × ℕ =>
    let centers := cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2
    let labeled := arithmeticMapWithWork (fun r => ((key.1, r), 1)) centers.1
    (labeled.1, centers.2 + labeled.2 + 1)
  have hq := h q
  have hr := localRepresentativeReadAllocation_le_work N P F a initial allocation q h
  have hg := queryGroupKeysAllocation_le_work N F exponent a (initial q).1 q
  have hc := arithmeticFlatMapAllocation_le_work build (fun key =>
      cellCentersReadAllocation P F key.1 a (inversePowerTwo exponent) initial allocation key.2 +
      arithmeticMapAllocation (fun _ => 1)
        (cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2).1)
      (queryGroupKeysWithWork N F exponent a (initial q).1 q).1 (by
        intro key _
        have hh := cellCentersReadAllocation_le_work P F key.1 a (inversePowerTwo exponent) initial allocation key.2 h
        have hm := arithmeticMapAllocation_le_work (fun r => ((key.1, r), 1)) (fun _ => 1)
          (cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2).1 (fun _ _ => le_rfl)
        dsimp only [build]
        omega)
  have ho := queryOnlineKeysAllocation_le_work N P F hP a (initial q).1 q
  unfold queryEarlierRepresentativesAllocation queryEarlierRepresentativesWithWork
  dsimp only [build] at hc ⊢
  omega



theorem queryWideInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) :
    queryWideInputsAllocation M parent P representatives ≤ (queryWideInputsWithWork M parent P representatives).2 := by
  let child := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
      let states := wideChildGridWithWork parent br.2 br.1 P i
      let labeled := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
      (labeled.1, states.2 + labeled.2 + 1)
  let one := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    wideChildGridAllocation parent br.2 br.1 P i +
      arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1
  have hchild (br : ℕ × TargetInterval ny) (i : Fin M) : one br i ≤ (child br i).2 := by
    have hw := wideChildGridAllocation_le_work parent br.2 br.1 P i
    have hm := arithmeticMapAllocation_le_work (fun r => ((i, r), 1)) (fun _ => 1)
      (wideChildGridWithWork parent br.2 br.1 P i).1 (fun _ _ => le_rfl)
    dsimp only [one, child]
    omega
  have hw := arithmeticFlatMapAllocation_le_work
    (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M))
    (fun br => arithmeticFlatMapAllocation (child br) (one br) (List.finRange M)) representatives
    (fun br _ => arithmeticFlatMapAllocation_le_work (child br) (one br) (List.finRange M) (fun i _ => hchild br i))
  have he := queryEraseAllocation_le_work coordinateEqualWithWork coordinateEqualAllocation
    (arithmeticFlatMapWithWork (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M)) representatives).1
    coordinateEqualAllocation_le_work
  unfold queryWideInputsAllocation queryWideInputsWithWork
  dsimp only [child, one] at hw he ⊢
  omega



theorem queryRawHistoryInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × TargetInterval ny)) :
    queryRawHistoryInputsAllocation M parent P history representatives ≤
      (queryRawHistoryInputsWithWork M parent P history representatives).2 := by
  let child := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    let states := wideChildGridWithWork parent br.2 br.1 P i
    let times := arithmeticFlatMapWithWork (fun t =>
      arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
    (times.1, states.2 + times.2 + history + 2)
  let one := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    wideChildGridAllocation parent br.2 br.1 P i + history +
      arithmeticFlatMapAllocation (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1))
        (wideChildGridWithWork parent br.2 br.1 P i).1)
        (fun _ => arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1)
        (List.range history)
  have hchild (br : ℕ × TargetInterval ny) (i : Fin M) : one br i ≤ (child br i).2 := by
    have hw := wideChildGridAllocation_le_work parent br.2 br.1 P i
    have ht := arithmeticFlatMapAllocation_le_work
      (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) (wideChildGridWithWork parent br.2 br.1 P i).1)
      (fun _ => arithmeticMapAllocation (fun _ => 1) (wideChildGridWithWork parent br.2 br.1 P i).1)
      (List.range history) (fun _ _ => arithmeticMapAllocation_le_work _ _ _ (fun _ _ => le_rfl))
    dsimp only [one, child]
    omega
  have hall := arithmeticFlatMapAllocation_le_work
    (fun br => arithmeticFlatMapWithWork (child br) (List.finRange M))
    (fun br => arithmeticFlatMapAllocation (child br) (one br) (List.finRange M)) representatives
    (fun br _ => arithmeticFlatMapAllocation_le_work (child br) (one br) (List.finRange M) (fun i _ => hchild br i))
  unfold queryRawHistoryInputsAllocation queryRawHistoryInputsWithWork
  dsimp only [child, one] at hall ⊢
  omega



theorem queryEarlierInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (h : ∀ r, allocation r ≤ (initial r).2) :
    queryEarlierInputsAllocation M parent N P F exponent history hP a initial allocation q ≤
      (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).2 := by
  have hr := queryEarlierRepresentativesAllocation_le_work N P F exponent hP a initial allocation q h
  have hw := queryRawHistoryInputsAllocation_le_work M parent P history
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1
  have ho := queryOrderedHistoryInputsAllocation_le_work
    (queryRawHistoryInputsWithWork M parent P history (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1).1
  unfold queryEarlierInputsAllocation queryEarlierInputsWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupportSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem initialCellAllocation_le_work (n P exponent : ℕ) (key : ℕ × ℕ × ℕ) :
    initialCellAllocation n P exponent key ≤
      (seedGridSpacingWithWork key.1 P).2 +
      (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).2 +
      (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork key.1 P).1)
        (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).1 key.2).2 + exponent + 3 := by
  have hs := seedGridSpacingAllocation_le_work key.1 P
  have hm := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat key.1)
  have hc := cellStatesAllocation_le_work n (bitWordValue (seedGridSpacingWithWork key.1 P).1)
    (canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)).1 key.2
  unfold initialCellAllocation
  omega



theorem queryInitialSupportAllocation_le_work {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    queryInitialSupportAllocation N P F exponent hP a value q ≤
      (queryInitialSupportWithWork N P F exponent hP a value q).2 := by
  let build := fun key : ℕ × ℕ × ℕ =>
    let spacing := seedGridSpacingWithWork key.1 P
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat key.1)
    let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 key.2
    (states.1, spacing.2 + side.2 + states.2 + exponent + 3)
  have hr := queryRawCentersAllocation_le_work N P F a value q
  have hg := queryGroupKeysAllocation_le_work N F exponent a value q
  have hc := arithmeticFlatMapAllocation_le_work build (initialCellAllocation n P exponent)
    (queryGroupKeysWithWork N F exponent a value q).1 (fun key _ => initialCellAllocation_le_work n P exponent key)
  have ho := queryOnlineKeysAllocation_le_work N P F hP a value q
  have hm := arithmeticMapAllocation_le_work (fun key : ℕ × TargetInterval n => (key.2, 1)) (fun _ => 1)
    (queryOnlineKeysWithWork N P F hP a value q).1 (fun _ _ => le_rfl)
  unfold queryInitialSupportAllocation queryInitialSupportWithWork
  dsimp only [build] at hc ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGatherSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem queryParentReadAllocation_le_work {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    queryParentReadAllocation keys words r ≤ (queryParentReadWithWork keys words r).2 :=
  gatheredLookupAllocation_le_work _ _ _ _ _ (fun k _ => queryIntervalEqualAllocation_le_work r k)



theorem queryBandInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (ha : ∀ r, allocation r ≤ (initial r).2) :
    queryBandInputsAllocation M parent N P F exponent hP a initial allocation q ≤
      (queryBandInputsWithWork M parent N P F exponent hP a initial q).2 := by
  have hr := queryEarlierRepresentativesAllocation_le_work N P F exponent hP a initial allocation q ha
  have hw := queryWideInputsAllocation_le_work M parent P
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1
  unfold queryBandInputsAllocation queryBandInputsWithWork
  dsimp only
  omega



theorem queryWarmupInputsAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (q : TargetInterval ny) (ha : ∀ r, allocation r ≤ (initial r).2) :
    queryWarmupInputsAllocation M parent N P F a initial allocation q ≤
      (queryWarmupInputsWithWork M parent N P F a initial q).2 := by
  have hr := localRepresentativeReadAllocation_le_work N P F a initial allocation q ha
  have hw := queryWideInputsAllocation_le_work M parent P (localRepresentativeReadWithWork N P F a initial q).1
  unfold queryWarmupInputsAllocation queryWarmupInputsWithWork
  dsimp only
  omega

end BinaryFraction

open BitQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryHistoryInputsLength (M P history count : ℕ) : ℕ :=
  count * (M * (history * (40 * P + 2) ^ 2))

def queryRawHistoryInputsBitBudget (M P history count B : ℕ) : ℕ :=
  let G := (40 * P + 2) ^ 2
  let C := wideChildGridBitBudget P (B + 1)
  count * (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
    M * (history * G) + 3) + M + 1

def queryEarlierInputsBitBudget (M P F exponent history B R : ℕ) : ℕ :=
  let count := queryEarlierRepresentativesLength P F exponent B
  queryEarlierRepresentativesBitBudget P F exponent B R +
    queryRawHistoryInputsBitBudget M P history count B +
    (queryHistoryInputsLength M P history count + 1) ^ 2 * (2002000 * (B + 1) ^ 2) + 2

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryIndexedSlice
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A terminal source interval is accessed through its stored endpoint.
Its substring is used only in the specification, never materialized. -/

namespace EditApproximation



@[simp] theorem querySliceHeadWithWork_value {α : Type*} (source : List α)
    (interval : TargetInterval source.length) :
    (querySliceHeadWithWork source interval).1 = (substring source interval.lo interval.hi).head? := by
  unfold querySliceHeadWithWork substring
  dsimp only
  rw [List.head?_drop, List.getElem?_take]
  by_cases h : interval.lo < interval.hi
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((binaryNaturalCompareWithWork_lt _ _).mp hc)), ite_eq_right h]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialConeCenters
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The initial-cone gather uses the unfiltered center list: a seed at a
center must be read before the eligibility test at that center is known. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryInitialConeCentersWithWork_value {n : ℕ} (N P : ℕ) (hP : 0 < P)
    (A value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialConeCentersWithWork N P A value q).1 =
      rawInitialConeCenters N P A.value ⌈value.value⌉₊ q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P) ⌈value.value⌉₊ q.lo q.hi).1 =
      localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  have hguard (b : ℕ) : (initialScaleGuardWithWork ⌈value.value⌉₊ b A).1 =
      decide ((⌈value.value⌉₊ : ℚ) / (16 * A.value ^ 2) ≤ b ∧
        (b : ℚ) ≤ 4 * A.value * ⌈value.value⌉₊) :=
    Bool.eq_iff_iff.mpr (by simp only [initialScaleGuardWithWork_value, decide_eq_true_eq])
  simp only [queryInitialConeCentersWithWork, naturalCeilingWithWork_value,
    arithmeticFlatMapWithWork_value, filterWithWork_value, dyadicScalesWithWork_value,
    hguard, seedGridSpacingWithWork_value _ _ hP, hg,
    rawInitialConeCenters]



end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialCenterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial gather pays for all candidate centers, including those
whose eligibility is tested only after their seed value has been read. -/

namespace EditApproximation.BinaryFraction

def queryInitialCentersBitBudget (P Amax B : ℕ) : ℕ :=
  let L := (64 * Amax ^ 2 * P + 2) ^ 2
  500 * (B + 1) ^ 2 + (B + 1) * (B + 9) + 2 +
    (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2) + L + 3) + 2

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialConeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryInitialConeCentersAllocation_le_work {n : ℕ} (N P : ℕ) (A value : BinaryFraction)
    (q : TargetInterval n) :
    queryInitialConeCentersAllocation N P A value q ≤ (queryInitialConeCentersWithWork N P A value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun b =>
    let spacing := (seedGridSpacingWithWork b P).1
    let states := gridStateBoxWithWork n (bitWordValue spacing) (bitWordValue radius) q.lo q.hi
    (states.1, (seedGridSpacingWithWork b P).2 + states.2 + 1)
  have hr := naturalCeilingAllocation_le_work value
  have hd := dyadicScalesAllocation_le_work N
  have hf := filterAllocation_le_work (fun b => initialScaleGuardWithWork (bitWordValue radius) b A)
    (fun b => initialScaleGuardAllocation (bitWordValue radius) b A) (dyadicScalesWithWork N).1
    (fun b _ => initialScaleGuardAllocation_le_work (bitWordValue radius) b A)
  have hm := arithmeticFlatMapAllocation_le_work build
    (fun b => seedGridSpacingAllocation b P + gridStateBoxAllocation n
      (bitWordValue (seedGridSpacingWithWork b P).1) (bitWordValue radius) q.lo q.hi)
    (filterWithWork (fun b => initialScaleGuardWithWork (bitWordValue radius) b A) (dyadicScalesWithWork N).1).1 (by
      intro b _
      have hs := seedGridSpacingAllocation_le_work b P
      have hg := gridStateBoxAllocation_le_work n (bitWordValue (seedGridSpacingWithWork b P).1) (bitWordValue radius) q.lo q.hi
      dsimp only [build]
      omega)
  unfold queryInitialConeCentersAllocation queryInitialConeCentersWithWork
  dsimp only [build, radius] at hf hm ⊢
  omega



theorem queryInitialSeedReadAllocation_le_work {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    queryInitialSeedReadAllocation value q keys words r ≤ (queryInitialSeedReadWithWork value q keys words r).2 := by
  have he := queryIntervalEqualAllocation_le_work r q
  have hv := naturalCeilingAllocation_le_work value
  have hp := queryParentReadAllocation_le_work keys words r
  have hc := naturalCeilingAllocation_le_work (queryParentReadWithWork keys words r).1
  unfold queryInitialSeedReadAllocation queryInitialSeedReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryInitialSeedReadBudget (count B : ℕ) : ℕ :=
  16 * B + 7 + count * (16 * B + 6) + 500 * (B + 1) ^ 2

def queryInitialProgramBitBudget (P Amax B C : ℕ) : ℕ :=
  let count := (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2
  C + queryInitialCentersBitBudget P Amax B + count * (C + 3) +
    cachedInitialProgramBitBudget P Amax (B + 2) * (queryInitialSeedReadBudget count B + 2)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalPreparedInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Numeric register and loop bounds, independent of previously cached values. -/
structure PreparedKernelNumericBounds {nx ny M : ℕ}
    (N P F exponent H Q eM eF B E S t : ℕ)
    (tau a eta kappa delta : BinaryFraction)
    (integer : ℕ → TargetInterval ny → ℕ) : Prop where
  largeBits : 10 ≤ B
  inputSize : Nat.size N ≤ B
  sourceSize : Nat.size nx + 2 ≤ B
  targetSize : Nat.size ny + 2 ≤ B
  aritySize : Nat.size M + 2 ≤ B
  precisionSize : Nat.size P ≤ B
  factorSize : Nat.size F + 2 ≤ B
  sampleSize : Nat.size Q + 2 ≤ B
  thetaSize : exponent + 1 ≤ B
  scaleSizes : eM + eF + 7 ≤ B
  heightSize : Nat.size H ≤ B
  coordinateSize : Nat.size (M * (40 * P + 2) ^ 2) ≤ B
  iterationSize : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B
  drawSize : ∀ b r, Nat.size (integer b r) ≤ B
  tauSize : tau.width ≤ B
  factorWidth : a.width ≤ B
  rateSize : eta.width ≤ B
  optimismSize : kappa.width ≤ B
  decrementSize : delta.width ≤ B
  rateMagnitude : |eta.value| ≤ E
  optimismRange : 0 ≤ kappa.value ∧ kappa.value ≤ 1
  scalePositive : 2 ≤ S
  arityCap : M ≤ S
  precisionCap : P ≤ S
  rateCap : E ≤ S
  timeCap : t ≤ S
  wordCap : 3 * (B + 4) + 4 ≤ S
  actionCap : (40 * P + 2) ^ (2 * M) ≤ S
  cartesianCap : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S
  iterationCap : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S

end BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalFinishCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executed refinement tail, with its actual selected actions and
its final deduplicated current-input buffer. -/

namespace EditApproximation.BinaryFraction

def queryFinishReadBudget (M B Rp earlierCount groups online : ℕ) : ℕ :=
  Rp + 2 + earlierCount * (32 * B + 12) + (groups + online) * M * (24 * B + 9)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementWorkBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of the seven executed refinement stages. Recursive reads,
list construction, sorting, both selectors and the final continuation are
all included in this counter. -/

namespace EditApproximation

namespace BinaryFraction

def queryRefinementStagesBudget (M B readCost earlierLength earlierCost onlineLength onlineCost
    sharedLength sharedCost groupLength groupCost parentCost finishCost : ℕ) : ℕ :=
  earlierCost + earlierLength * (readCost + 3) + onlineCost + parentCost + sharedCost +
    sharedLength * (readCost + 3) + groupCost +
    queryNeededInputsBitBudget (groupLength + onlineLength) M B +
    (groupLength + onlineLength) * M * (readCost + 3) + finishCost

end BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalRefinementCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryRefinementReadBudget (B Rp R earlier shared : ℕ) : ℕ :=
  R + Rp + (1 + earlier * (32 * B + 12)) + (1 + shared * (24 * B + 9))

def queryLocalRefinementBitBudget (M N P F exponent eM eF B S t Rp R W Dg Do : ℕ) : ℕ :=
  let earlier := queryHistoryInputsLength M P t (queryEarlierRepresentativesLength P F exponent B)
  let shared := querySharedInputsLength M F exponent eM eF B
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let U := queryRefinementReadBudget B Rp R earlier shared
  queryRefinementStagesBudget M B W earlier (queryEarlierInputsBitBudget M P F exponent t B Rp)
    (B + 1) (preparedLocalOnlineBitBudget M P B S * tableReadFactor U * (Do + 4))
    shared (querySharedInputsBitBudget M F exponent eM eF B Dg)
    groups (preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor U * (Dg + 4)) Rp
    (queryRefinementFinishBitBudget M P F B (queryFinishReadBudget M B Rp earlier groups (B + 1)) groups (B + 1))

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineRangeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online source ranges are computed before their random draws. This
charges the actual band, coordinate set, two powers, and triangular mass. -/

namespace EditApproximation.BinaryFraction

def queryOnlineRangeBitBudget (M P B R : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  26 * B + 4 +
    (wideMaterializationBitBudget M P B + representativeCompleteBitBudget M V (4 * B + 20) + V + 1) *
      tableReadFactor R + onlineIndexBitBudget M V B + bitPowerBitBudget 80 (B + 4) +
      10000 * (80 * (B + 4) + 4) ^ 2 + 4

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceGatherCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace BinaryFraction

def queryGroupGatherBitBudget (M F exponent eM eF B Rp W K : ℕ) : ℕ :=
  Rp + queryGroupSourceKeysBitBudget M F exponent eM eF B +
    queryGroupSourceKeysLength M F exponent eM eF B * (W + 3) + K

def queryOnlineGatherBitBudget (M P B Rp R W K : ℕ) : ℕ :=
  Rp + queryOnlineKeysBitBudget B +
    (B + 1) * (queryOnlineRangeBitBudget M P (B + 1) R + W + 3) + K

end BinaryFraction

open BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSourcesCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete random-source stage: source enumeration and range construction,
physical source reads, finite-buffer scans, and the inner local refinement. -/

namespace EditApproximation.BinaryFraction

def queryLocalSourcesBitBudget (M N P F exponent eM eF B S t Rp R W : ℕ) : ℕ :=
  queryGroupGatherBitBudget M F exponent eM eF B Rp W
    (queryOnlineGatherBitBudget M P B Rp R W
      (queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W
        (queryBufferedGroupReadBudget M F exponent eM eF B B)
        (queryOnlineBufferReadBudget (B + 1) B B)))

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOuterGatherCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace BinaryFraction

def queryInitialGatherBitBudget (P F exponent B R K : ℕ) : ℕ :=
  R + queryInitialSupportBitBudget P F exponent B + queryInitialSupportLength P F exponent B * (R + 3) + K

def queryBandGatherBitBudget (M P F exponent B Rp W K : ℕ) : ℕ :=
  queryBandInputsBitBudget M P F exponent B Rp +
    2 * (queryEarlierRepresentativesLength P F exponent B * (M * (40 * P + 2) ^ 2) * (W + 3)) + K

end BinaryFraction
open BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBandCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryBandReadBudget (M P F exponent B : ℕ) : ℕ :=
  1 + queryEarlierRepresentativesLength P F exponent B * (M * (40 * P + 2) ^ 2) * (24 * B + 9)

def queryLocalBandBitBudget (M N P F exponent eM eF B S t Rp W : ℕ) : ℕ :=
  queryBandGatherBitBudget M P F exponent B Rp W
    (queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp
      (queryBandReadBudget M P F exponent B) W)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete work bound for the actual adaptive local program. Premises
are numeric parameter bounds, stored-word sizes, and the existing history
range invariant; all intermediate enumeration and scans are included. -/

namespace EditApproximation.BinaryFraction

def queryParentBufferReadBudget (P F exponent B : ℕ) : ℕ :=
  1 + queryInitialSupportLength P F exponent B * (16 * B + 6)

def queryLocalProgramBitBudget (M N P F exponent eM eF B S t W : ℕ) : ℕ :=
  queryInitialGatherBitBudget P F exponent B W
    (queryLocalBandBitBudget M N P F exponent eM eF B S t
      (queryParentBufferReadBudget P F exponent B) W)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSelectorSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)

def queryOnlineSelectAllocation (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) : ℕ :=
  preparedLocalOnlineActionsSourceAllocation source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer
    parentAllocation childAllocation initialAllocation (queryHistoryReadAllocation keys words)
    integerAllocation N q

theorem queryOnlineSelectAllocation_le_work (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length)
    (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
    (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
    (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
    (hint : ∀ b r, integerAllocation b r ≤ (integer b r).2) :
    queryOnlineSelectAllocation source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
      t integer integerAllocation keys words q ≤
      3 * (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
        parentInitial child initial R hc hi t integer keys words q).2 :=
  preparedLocalOnlineActionsSourceAllocation_le_work source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer
    parentAllocation childAllocation initialAllocation (queryHistoryReadAllocation keys words)
    integerAllocation N q hp hca hia (queryHistoryReadAllocation_le_work keys words) hint

def queryGroupSelectAllocation (draw : CountedCellGroupDraws M F Q)
    (drawAllocation : CellGroupSourceAllocations M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) : ℕ :=
  preparedLocalCellGroupsSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi
    parentAllocation childAllocation initialAllocation (queryChildReadAllocation keys words)
    draw drawAllocation N q

theorem queryGroupSelectAllocation_le_work (draw : CountedCellGroupDraws M F Q)
    (drawAllocation : CellGroupSourceAllocations M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length)
    (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
    (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
    (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    queryGroupSelectAllocation source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
      draw drawAllocation keys words q ≤
      (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
        parentInitial child initial R hc hi draw keys words q).2 :=
  preparedLocalCellGroupsSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi
    parentAllocation childAllocation initialAllocation (queryChildReadAllocation keys words)
    draw drawAllocation N q hp hca hia (queryChildReadAllocation_le_work keys words) hd

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryPhysicalDataBudget (T J B V C W : ℕ) : ℕ :=
  W + (T + 1 + T * (7 * J + 30 + (C + 1) + 3) + warmupAverageBitBudget T V) +
    (8 * B + 7 * J + 32 + (C + 1)) + 1

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupInputsTransportAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (word : BinaryFraction) (scale : ℚ)
    (hv : word.value = scale) (draw : Fin (groupSampleCount M Q b scale) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b scale) → ℕ)
    (ha : ∀ sample, allocation sample ≤ (draw sample).2) :
    queryGroupInputsTransportAllocation (ny := ny) parent b exponent Q cell word scale hv draw allocation ≤
      (queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word scale hv draw).2 :=
  queryGroupInputsAllocation_le_work _ _ _ _ _ _ _ _ (fun _ => ha _)



theorem querySharedCellInputsAllocation_le_work {nx ny : ℕ} (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : TargetInterval nx)
    (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ)
    (allocation : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → ℕ)
    (ha : ∀ scale sample, allocation scale sample ≤ (draw scale sample).2) :
    querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell draw allocation ≤
      (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell draw).2 := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hM rfl hF
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  let indices := queryFinRange scales.1.length (groupDyadicScales M b F).length hlen
  let build := fun scale =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let hv : word.value = groupDyadicScaleAt M b F scale := queryGroupScaleAt_value M b F _ hs scale
    let states := queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word
      (groupDyadicScaleAt M b F scale) hv (draw scale)
    (states.1, states.2 + scales.1.length + 1)
  let alloc := fun scale =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let hv : word.value = groupDyadicScaleAt M b F scale := queryGroupScaleAt_value M b F _ hs scale
    queryGroupInputsTransportAllocation (ny := ny) parent b exponent Q cell word
      (groupDyadicScaleAt M b F scale) hv (draw scale) (allocation scale)
  have hg := groupScalesAllocation_le_work eM eb eF
  have hi := arithmeticFlatMapAllocation_le_work build alloc indices (by
    intro scale _
    have hh := queryGroupInputsTransportAllocation_le_work (ny := ny) parent b exponent Q cell
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale) (groupDyadicScaleAt M b F scale)
      (queryGroupScaleAt_value M b F _ hs scale) (draw scale) (allocation scale) (ha scale)
    dsimp only [alloc, build]
    omega)
  unfold querySharedCellInputsAllocation querySharedCellInputsWithWork
  dsimp only [build, alloc, b, scales, indices] at hi ⊢
  omega



theorem querySharedInputsAllocation_le_work {nx ny : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : TargetInterval nx)
    (a value : BinaryFraction) (query : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
    (allocation : CountedCellGroupAllocations M F Q)
    (ha : ∀ b cell scale sample, allocation b cell scale sample ≤ (draw b cell scale sample).2) :
    querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a value query draw allocation ≤
      (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a value query draw).2 := by
  let scales := (queryExponentsWithWork N F a value).1
  let radius := (naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    let cells := targetCellsWithWork side.1 (bitWordValue radius) query
    let states := arithmeticFlatMapWithWork (fun cell =>
      querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell)) cells.1
    (states.1, side.2 + cells.2 + states.2 + eb + exponent + 4)
  let alloc := fun eb =>
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    let cells := (targetCellsWithWork side (bitWordValue radius) query).1
    canonicalMulAllocation (inversePowerTwo exponent) (nat (2 ^ eb)) + targetCellsAllocation side (bitWordValue radius) query +
      arithmeticFlatMapAllocation
        (fun cell => querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell))
        (fun cell => querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell
          (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell)) cells + eb + exponent + 2
  have he := queryExponentsAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hi := arithmeticFlatMapAllocation_le_work build alloc scales (by
    intro eb _
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    have hs := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat (2 ^ eb))
    have hc := targetCellsAllocation_le_work side (bitWordValue radius) query
    have hm := arithmeticFlatMapAllocation_le_work
      (fun cell => querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell))
      (fun cell => querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell
        (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell)) (targetCellsWithWork side (bitWordValue radius) query).1
      (fun cell _ => querySharedCellInputsAllocation_le_work (ny := ny) M F Q eM eb eF hM hF parent exponent cell
        (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell) (ha (2 ^ eb) cell))
    dsimp only [build, alloc, side] at hc hm ⊢
    omega)
  have ho := queryOrderedChildInputsAllocation_le_work (arithmeticFlatMapWithWork build scales).1
  unfold querySharedInputsAllocation querySharedInputsWithWork
  dsimp only [build, alloc, scales, radius] at hi ho ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

def queryWarmupRepresentatives (P F B : ℕ) : ℕ := (B + 1) * (64 * F * P + 2) ^ 2

def queryWarmupInputsBitBudget (M P F B I : ℕ) : ℕ :=
  localRepresentativesBitBudget P F B * (I + 2) +
    queryWideInputsBitBudget M P (queryWarmupRepresentatives P F B) B + 1

def queryWarmupParentReadBudget (P F B : ℕ) : ℕ :=
  16 * B + 7 + queryWarmupRepresentatives P F B * (16 * B + 6)

def queryWarmupChildReadBudget (M P F B : ℕ) : ℕ :=
  1 + (queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (24 * B + 9)

def queryWarmupProgramBitBudget (M P F B C : ℕ) : ℕ :=
  C + queryRawCentersBitBudget P F B + queryWarmupRepresentatives P F B * (C + 3) +
    queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) +
    (queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
    localWarmupBitBudget M P F B *
      (queryWarmupParentReadBudget P F B + M * (queryWarmupChildReadBudget M P F B + 3) + 4)

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem queryOverrideParentReadAllocation_le_work {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    queryOverrideParentReadAllocation q keys words r ≤
      (queryOverrideParentReadWithWork value q keys words r).2 := by
  have he := queryIntervalEqualAllocation_le_work r q
  have hp := queryParentReadAllocation_le_work keys words r
  unfold queryOverrideParentReadAllocation queryOverrideParentReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

end BinaryFraction
open BitQuery BinaryFraction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_Footprint
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.EditApproximation.BitQuery

/- The allocation trace of a query, without a proof relating allocations to work.
The trace retains every allocation and every adaptive continuation. -/


namespace Heap

/-- Forget only the local allocation/work certificates, preserving the exact trace. -/
def footprint {ι β : Type*} {program : BitQuery ι β} : Heap program → Footprint program
  | .done value => .done value
  | .read key next continuation => .read key next (fun word => (continuation word).footprint)
  | .charge localCells _ next => .charge localCells next.footprint

@[simp] theorem footprint_done {ι β : Type*} (value : β) :
    (Heap.done (ι := ι) value).footprint = .done value := rfl

@[simp] theorem footprint_read {ι β : Type*} (key : ι) (next : BinaryFraction → BitQuery ι β)
    (continuation : ∀ word, Heap (next word)) :
    (Heap.read key next continuation).footprint =
      .read key next (fun word => (continuation word).footprint) := rfl

@[simp] theorem footprint_charge {ι β : Type*} {steps : ℕ} {program : BitQuery ι β}
    (allocation : ℕ) (bound : allocation ≤ 3 * steps) (heap : Heap program) :
    (Heap.charge allocation bound heap).footprint = .charge allocation heap.footprint := rfl

@[simp] theorem footprint_bind {ι α β : Type*} {program : BitQuery ι α} (heap : Heap program)
    (next : α → BitQuery ι β) (allocation : ∀ value, Heap (next value)) :
    (heap.bind next allocation).footprint =
      heap.footprint.bind next (fun value => (allocation value).footprint) := by
  induction heap with
  | done => rfl
  | read key continuation stored ih =>
    simp only [bind, footprint, Footprint.bind]
    congr 1
    funext word
    exact ih word
  | charge localCells bound tail ih =>
    exact congrArg (Footprint.charge localCells) ih

@[simp] theorem footprint_compute {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ 3 * execution.2) :
    (Heap.compute (ι := ι) execution allocation bound).footprint =
      Footprint.compute execution allocation := rfl

@[simp] theorem footprint_chargeOf {ι β : Type*} {steps : ℕ} {program : BitQuery ι β}
    (allocation : ℕ) (bound : allocation ≤ steps) (heap : Heap program) :
    (Heap.chargeOf allocation bound heap).footprint = Footprint.chargeOf allocation heap.footprint := rfl

@[simp] theorem footprint_computeOf {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ execution.2) :
    (Heap.computeOf (ι := ι) execution allocation bound).footprint =
      Footprint.computeOf execution allocation := rfl

@[simp] theorem footprint_collect {ι κ β : Type*} (reader : κ → BitQuery ι BinaryFraction)
    (allocation : ∀ key, Heap (reader key)) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) (continuation : ∀ words, Heap (next words)) :
    (Heap.collect reader allocation inputs next continuation).footprint =
      Footprint.collect reader (fun key => (allocation key).footprint) inputs next
        (fun words => (continuation words).footprint) := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key rest ih =>
    change ((allocation key).bind _ _).footprint = _
    rw [footprint_bind]
    apply congrArg (Footprint.bind (allocation key).footprint _)
    funext word
    exact congrArg (Footprint.charge 1) (ih _ _)

@[simp] theorem footprint_mapKeysWithWork {ι κ β : Type*} (f : ι → κ × ℕ)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (f key).2)
    {program : BitQuery ι β} (heap : Heap program) :
    (heap.mapKeysWithWork f allocation ha).footprint = heap.footprint.mapKeysWithWork f allocation := by
  induction heap with
  | done => rfl
  | read key next continuation ih =>
    change Footprint.charge (allocation key)
      (Footprint.read (f key).1 _ (fun word => (mapKeysWithWork f allocation ha (continuation word)).footprint)) =
      Footprint.charge (allocation key)
      (Footprint.read (f key).1 _ (fun word => Footprint.mapKeysWithWork f allocation (continuation word).footprint))
    apply congrArg (Footprint.charge (allocation key))
    apply congrArg (Footprint.read (f key).1 _)
    funext word
    exact ih word
  | charge localCells bound next ih =>
    exact congrArg (Footprint.charge localCells) ih

@[simp] theorem footprint_normalize {ι : Type*} {program : BitQuery ι BinaryFraction}
    (heap : Heap program) (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) :
    (heap.normalize base hbase remaining).footprint = heap.footprint.normalize base hbase remaining := by
  exact footprint_bind heap _ _

@[simp] theorem footprint_runCells {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) (memory : BinaryMemo BinaryFraction) :
    heap.footprint.runCells ask childCells memory = heap.runCells ask childCells memory := by
  induction heap generalizing memory with
  | done => rfl
  | read key next continuation ih => simp only [footprint, Footprint.runCells, runCells, ih]
  | charge localCells bound next ih => simp only [footprint, Footprint.runCells, runCells, ih]

end Heap
end OAI.EditApproximation.BitQuery
end



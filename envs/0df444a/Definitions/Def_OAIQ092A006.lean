-- Prove2me | Definitions.Def_OAIQ092A006
-- name    : OAIQ092A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:49:50.814746+00:00
-- url     : https://prove2.me/theorems/7ad33f5d-3ca5-4a7a-a4eb-6074772de187
-- title:
--   Definitions bundle OAIQ092A006 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1236 declarations of OpenAI's Lean: 841 definitions, 4 inductive types or structures and 391 theorems. The definitions and types are `OAI.ContinuumCoulomb.QMAPropagationBasis`, `OAI.ContinuumCoulomb.QMARationalExchangeGraph.CoefficientBound`, `OAI.ContinuumCoulomb.QMARationalExchangeGraph.Simple`, `OAI.ContinuumCoulomb.QMARationalExchangeGraph.energy`, `OAI.ContinuumCoulomb.QMARealLocalModel`, `OAI.ContinuumCoulomb.QMARealLocalModel.energy`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.Incident`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.bufferedHeight`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.bufferedWidth`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmLength`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmPoint`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmSupport`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmWalk`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointColors`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointPorts`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.energy`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.laneColor`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.laneSupport`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.placedVertex`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeLeft`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeLength`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeRight`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeSites`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeVertex`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.spacedColor`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.spacedSupport`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.coefficientBudget`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.delta`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.finalPrecision`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.finalPrecisionProgram`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.gate`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.historyHeight`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.lift`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.localY`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.pairY`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.rebit`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.referenceEdge`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.samplePrecision` and 805 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2`, `ContinuumCoulomb_ManyBody_MediatorSpectrum`, `ContinuumCoulomb_OneParticle_ContactTemplates`, `ContinuumCoulomb_Quantum_QuantumAdjacentCnot`, `ContinuumCoulomb_Quantum_QuantumAdjacentProgram`, `ContinuumCoulomb_Quantum_QuantumAlgebraicHistory`, `ContinuumCoulomb_Quantum_QuantumAlgebraicScalar`, `ContinuumCoulomb_Quantum_QuantumAnchorDensity`, `ContinuumCoulomb_Quantum_QuantumAxisSample`, `ContinuumCoulomb_Quantum_QuantumAxisSampleProgram`, `ContinuumCoulomb_Quantum_QuantumBitTransfer`, `ContinuumCoulomb_Quantum_QuantumBlockEdges`, `ContinuumCoulomb_Quantum_QuantumBufferedArmProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedArms`, `ContinuumCoulomb_Quantum_QuantumBufferedBounds`, `ContinuumCoulomb_Quantum_QuantumBufferedDetour`, `ContinuumCoulomb_Quantum_QuantumBufferedDogleg`, `ContinuumCoulomb_Quantum_QuantumBufferedEndpointWalk`, `ContinuumCoulomb_Quantum_QuantumBufferedExtent`, `ContinuumCoulomb_Quantum_QuantumBufferedGridEdge`, `ContinuumCoulomb_Quantum_QuantumBufferedIntersections`, `ContinuumCoulomb_Quantum_QuantumBufferedLanes`, `ContinuumCoulomb_Quantum_QuantumBufferedListProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedPortChain`, `ContinuumCoulomb_Quantum_QuantumBufferedSharedEdge`, `ContinuumCoulomb_Quantum_QuantumBufferedSupport`, `ContinuumCoulomb_Quantum_QuantumCellCatalogProgram`, `ContinuumCoulomb_Quantum_QuantumCircuitCode`, `ContinuumCoulomb_Quantum_QuantumCircuitPadding`, `ContinuumCoulomb_Quantum_QuantumClockAnchor`, `ContinuumCoulomb_Quantum_QuantumCoefficientEnvelopeProgram`, `ContinuumCoulomb_Quantum_QuantumCoefficientPrograms`, `ContinuumCoulomb_Quantum_QuantumComputedAccuracy`, `ContinuumCoulomb_Quantum_QuantumComputedRoutingTable`, `ContinuumCoulomb_Quantum_QuantumCountertermSample`, `ContinuumCoulomb_Quantum_QuantumCrossingListBlock`, `ContinuumCoulomb_Quantum_QuantumCrossingListFamily`, `ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram`, `ContinuumCoulomb_Quantum_QuantumDescriptorSiteProgram`, `ContinuumCoulomb_Quantum_QuantumDescriptorSites`, `ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram`, `ContinuumCoulomb_Quantum_QuantumDiagonalTensor`, `ContinuumCoulomb_Quantum_QuantumDistributedClock`, `ContinuumCoulomb_Quantum_QuantumDistributedFamily`, `ContinuumCoulomb_Quantum_QuantumDistributedInput`, `ContinuumCoulomb_Quantum_QuantumDistributedMatrix`, `ContinuumCoulomb_Quantum_QuantumDistributedRebit`, `ContinuumCoulomb_Quantum_QuantumEndpointListProgram`, `ContinuumCoulomb_Quantum_QuantumEndpointPorts`, `ContinuumCoulomb_Quantum_QuantumEndpointRelabel`, `ContinuumCoulomb_Quantum_QuantumEvenListPieces`, `ContinuumCoulomb_Quantum_QuantumEvenTapeOrder`, `ContinuumCoulomb_Quantum_QuantumExchangeLanes`, `ContinuumCoulomb_Quantum_QuantumExchangeRounding`, `ContinuumCoulomb_Quantum_QuantumExchangeRoutes`, `ContinuumCoulomb_Quantum_QuantumExchangeSample`, `ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram`, `ContinuumCoulomb_Quantum_QuantumFieldSample`, `ContinuumCoulomb_Quantum_QuantumFinalPrecision`, `ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumFineRoute`, `ContinuumCoulomb_Quantum_QuantumFiniteMembership`, `ContinuumCoulomb_Quantum_QuantumFirstUseProgram`, `ContinuumCoulomb_Quantum_QuantumForkBackground`, `ContinuumCoulomb_Quantum_QuantumForkDegreeBound`, `ContinuumCoulomb_Quantum_QuantumForkGridInitial`, `ContinuumCoulomb_Quantum_QuantumForkGridProgram`, `ContinuumCoulomb_Quantum_QuantumForkInitial`, `ContinuumCoulomb_Quantum_QuantumForkInitialCells`, `ContinuumCoulomb_Quantum_QuantumForkListActive`, `ContinuumCoulomb_Quantum_QuantumForkListBackground`, `ContinuumCoulomb_Quantum_QuantumForkListBoundProgram`, `ContinuumCoulomb_Quantum_QuantumForkListCellLocality`, `ContinuumCoulomb_Quantum_QuantumForkListCellMass`, `ContinuumCoulomb_Quantum_QuantumForkListCells`, `ContinuumCoulomb_Quantum_QuantumForkListData`, `ContinuumCoulomb_Quantum_QuantumForkListDegree`, `ContinuumCoulomb_Quantum_QuantumForkListDegreeIteration`, `ContinuumCoulomb_Quantum_QuantumForkListFinalDegree`, `ContinuumCoulomb_Quantum_QuantumForkListFullCells`, `ContinuumCoulomb_Quantum_QuantumForkListFullDegree`, `ContinuumCoulomb_Quantum_QuantumForkListGraph`, `ContinuumCoulomb_Quantum_QuantumForkListInitial`, `ContinuumCoulomb_Quantum_QuantumForkListInitialCalibration`, `ContinuumCoulomb_Quantum_QuantumForkListInitialCellMass`, `ContinuumCoulomb_Quantum_QuantumForkListInitialCells`, `ContinuumCoulomb_Quantum_QuantumForkListInitialDegree`, `ContinuumCoulomb_Quantum_QuantumForkListInitialMatrix`, `ContinuumCoulomb_Quantum_QuantumForkListInitialPairs`, `ContinuumCoulomb_Quantum_QuantumForkListInitialPhysical`, `ContinuumCoulomb_Quantum_QuantumForkListInitialProgram`, `ContinuumCoulomb_Quantum_QuantumForkListInitialRealization`, `ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial`, `ContinuumCoulomb_Quantum_QuantumForkListInitialStateProgram`, `ContinuumCoulomb_Quantum_QuantumForkListInitialSum`, `ContinuumCoulomb_Quantum_QuantumForkListMatrix`, `ContinuumCoulomb_Quantum_QuantumForkListNext`, `ContinuumCoulomb_Quantum_QuantumForkListNextBackground`, `ContinuumCoulomb_Quantum_QuantumForkListNextDegree`, `ContinuumCoulomb_Quantum_QuantumForkListNextValid`, `ContinuumCoulomb_Quantum_QuantumForkListPoints`, `ContinuumCoulomb_Quantum_QuantumForkListProgram`, `ContinuumCoulomb_Quantum_QuantumForkListRealization`, `ContinuumCoulomb_Quantum_QuantumForkListRound`, `ContinuumCoulomb_Quantum_QuantumForkListScale`, `ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage`, `ContinuumCoulomb_Quantum_QuantumForkListWeights`, `ContinuumCoulomb_Quantum_QuantumForkRoutingData`, `ContinuumCoulomb_Quantum_QuantumFourSpatial`, `ContinuumCoulomb_Quantum_QuantumGateCode`, `ContinuumCoulomb_Quantum_QuantumGateEntryProgram`, `ContinuumCoulomb_Quantum_QuantumGraphDegree`, `ContinuumCoulomb_Quantum_QuantumGridCoordinates`, `ContinuumCoulomb_Quantum_QuantumGridMidpoint`, `ContinuumCoulomb_Quantum_QuantumGridNeighbors`, `ContinuumCoulomb_Quantum_QuantumGridWalk`, `ContinuumCoulomb_Quantum_QuantumHistoryBitProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryCellProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryCells`, `ContinuumCoulomb_Quantum_QuantumHistoryComparison`, `ContinuumCoulomb_Quantum_QuantumHistoryDegree`, `ContinuumCoulomb_Quantum_QuantumHistoryDelta`, `ContinuumCoulomb_Quantum_QuantumHistoryDeltaProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDescriptors`, `ContinuumCoulomb_Quantum_QuantumHistoryDiagonal`, `ContinuumCoulomb_Quantum_QuantumHistoryDiagonalProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryEnumeration`, `ContinuumCoulomb_Quantum_QuantumHistoryFork`, `ContinuumCoulomb_Quantum_QuantumHistoryHeight`, `ContinuumCoulomb_Quantum_QuantumHistoryMatrix`, `ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds`, `ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySampling`, `ContinuumCoulomb_Quantum_QuantumHistorySiteProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryTableProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryXZPromise`, `ContinuumCoulomb_Quantum_QuantumInflatedListProgram`, `ContinuumCoulomb_Quantum_QuantumLaneUnaryProgram`, `ContinuumCoulomb_Quantum_QuantumLatticeEncoding`, `ContinuumCoulomb_Quantum_QuantumLatticeEnvelope`, `ContinuumCoulomb_Quantum_QuantumLatticeSerialization`, `ContinuumCoulomb_Quantum_QuantumLatticeSource`, `ContinuumCoulomb_Quantum_QuantumListGraph`, `ContinuumCoulomb_Quantum_QuantumListLattice`, `ContinuumCoulomb_Quantum_QuantumListLatticeProgram`, `ContinuumCoulomb_Quantum_QuantumListMerge`, `ContinuumCoulomb_Quantum_QuantumListMergeProgram`, `ContinuumCoulomb_Quantum_QuantumListMergeProperties`, `ContinuumCoulomb_Quantum_QuantumListPathAccuracy`, `ContinuumCoulomb_Quantum_QuantumListPathMatrix`, `ContinuumCoulomb_Quantum_QuantumListPathProgram`, `ContinuumCoulomb_Quantum_QuantumListPathStep`, `ContinuumCoulomb_Quantum_QuantumListRouteLattice`, `ContinuumCoulomb_Quantum_QuantumListRoutePathOrder`, `ContinuumCoulomb_Quantum_QuantumListRouteProgram`, `ContinuumCoulomb_Quantum_QuantumListRouteRepresentation`, `ContinuumCoulomb_Quantum_QuantumListRouteSelection`, `ContinuumCoulomb_Quantum_QuantumListSchedule`, `ContinuumCoulomb_Quantum_QuantumListScheduleGeometry`, `ContinuumCoulomb_Quantum_QuantumListScheduleGraph`, `ContinuumCoulomb_Quantum_QuantumListScheduleLabels`, `ContinuumCoulomb_Quantum_QuantumListScheduleOrder`, `ContinuumCoulomb_Quantum_QuantumListScheduleProgram`, `ContinuumCoulomb_Quantum_QuantumLocalAction`, `ContinuumCoulomb_Quantum_QuantumLocalCoordinates`, `ContinuumCoulomb_Quantum_QuantumLocalLift`, `ContinuumCoulomb_Quantum_QuantumLocalModel`, `ContinuumCoulomb_Quantum_QuantumLocalPathClearance`, `ContinuumCoulomb_Quantum_QuantumLocalPenalties`, `ContinuumCoulomb_Quantum_QuantumLocalPropagation`, `ContinuumCoulomb_Quantum_QuantumLocalTensor`, `ContinuumCoulomb_Quantum_QuantumManhattanListProgram`, `ContinuumCoulomb_Quantum_QuantumManhattanSupport`, `ContinuumCoulomb_Quantum_QuantumMappedGate`, `ContinuumCoulomb_Quantum_QuantumMergedSupport`, `ContinuumCoulomb_Quantum_QuantumNearestCircuit`, `ContinuumCoulomb_Quantum_QuantumNearestGate`, `ContinuumCoulomb_Quantum_QuantumNearestProgram`, `ContinuumCoulomb_Quantum_QuantumOffsetSample`, `ContinuumCoulomb_Quantum_QuantumOrderedCellProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedCellTable`, `ContinuumCoulomb_Quantum_QuantumOrderedCoefficient`, `ContinuumCoulomb_Quantum_QuantumOrderedDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedDescriptors`, `ContinuumCoulomb_Quantum_QuantumOrderedHistory`, `ContinuumCoulomb_Quantum_QuantumOrderedIncidence`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelBlocks`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelPacking`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedOutputSpatial`, `ContinuumCoulomb_Quantum_QuantumOrderedRawBlock`, `ContinuumCoulomb_Quantum_QuantumOrderedRawCells`, `ContinuumCoulomb_Quantum_QuantumOrderedRawPacking`, `ContinuumCoulomb_Quantum_QuantumOrderedRawPackingProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedReference`, `ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex`, `ContinuumCoulomb_Quantum_QuantumOrderedSupport`, `ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram`, `ContinuumCoulomb_Quantum_QuantumOrdinalPlacement`, `ContinuumCoulomb_Quantum_QuantumOrdinalProgram`, `ContinuumCoulomb_Quantum_QuantumOrdinalSpatial`, `ContinuumCoulomb_Quantum_QuantumPaddedHistory`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumPairDedup`, `ContinuumCoulomb_Quantum_QuantumPathPolynomialBound`, `ContinuumCoulomb_Quantum_QuantumPathProgram`, `ContinuumCoulomb_Quantum_QuantumPathScaleProgram`, `ContinuumCoulomb_Quantum_QuantumPathTable`, `ContinuumCoulomb_Quantum_QuantumPathVisitProgram`, `ContinuumCoulomb_Quantum_QuantumPauliMonomial`, `ContinuumCoulomb_Quantum_QuantumPolynomialUnary`, `ContinuumCoulomb_Quantum_QuantumPortChainProgram`, `ContinuumCoulomb_Quantum_QuantumPortRankProgram`, `ContinuumCoulomb_Quantum_QuantumPrefix`, `ContinuumCoulomb_Quantum_QuantumPreparedVerifier`, `ContinuumCoulomb_Quantum_QuantumPropagationSampler`, `ContinuumCoulomb_Quantum_QuantumPropagationTable`, `ContinuumCoulomb_Quantum_QuantumRationalPathStep`, `ContinuumCoulomb_Quantum_QuantumRationalSpatialPackage`, `ContinuumCoulomb_Quantum_QuantumRawCellDensity`, `ContinuumCoulomb_Quantum_QuantumRawCellLocality`, `ContinuumCoulomb_Quantum_QuantumRawCompiler`, `ContinuumCoulomb_Quantum_QuantumRawCorrectness`, `ContinuumCoulomb_Quantum_QuantumRawExchange`, `ContinuumCoulomb_Quantum_QuantumRawFamilyCorrectness`, `ContinuumCoulomb_Quantum_QuantumRawFamilyProgram`, `ContinuumCoulomb_Quantum_QuantumRawIncidence`, `ContinuumCoulomb_Quantum_QuantumRawProgram`, `ContinuumCoulomb_Quantum_QuantumRawSchedule`, `ContinuumCoulomb_Quantum_QuantumReferenceBlocks`, `ContinuumCoulomb_Quantum_QuantumReferenceComparison`, `ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable`, `ContinuumCoulomb_Quantum_QuantumReferenceEdges`, `ContinuumCoulomb_Quantum_QuantumReferenceLocal`, `ContinuumCoulomb_Quantum_QuantumReferencePenalty`, `ContinuumCoulomb_Quantum_QuantumReferenceReal`, `ContinuumCoulomb_Quantum_QuantumReferenceTensor`, `ContinuumCoulomb_Quantum_QuantumReferenceTerms`, `ContinuumCoulomb_Quantum_QuantumRouteCongestion`, `ContinuumCoulomb_Quantum_QuantumRouteLeafProgram`, `ContinuumCoulomb_Quantum_QuantumRouteProgram`, `ContinuumCoulomb_Quantum_QuantumRouteSelectorProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest`, `ContinuumCoulomb_Quantum_QuantumRoutingInputProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingTable`, `ContinuumCoulomb_Quantum_QuantumRowStageSupport`, `ContinuumCoulomb_Quantum_QuantumSampleAssembly`, `ContinuumCoulomb_Quantum_QuantumSampleBudget`, `ContinuumCoulomb_Quantum_QuantumSamplePrecision`, `ContinuumCoulomb_Quantum_QuantumSortedTime`, `ContinuumCoulomb_Quantum_QuantumSpacedListProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialCrossingProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialExchange`, `ContinuumCoulomb_Quantum_QuantumSpatialPortProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialReference`, `ContinuumCoulomb_Quantum_QuantumStagePath`, `ContinuumCoulomb_Quantum_QuantumSupportLookup`, `ContinuumCoulomb_Quantum_QuantumSwapConjugation`, `ContinuumCoulomb_Quantum_QuantumSweepCellProgram`, `ContinuumCoulomb_Quantum_QuantumSweepCells`, `ContinuumCoulomb_Quantum_QuantumSweepCongestion`, `ContinuumCoulomb_Quantum_QuantumSweepIndex`, `ContinuumCoulomb_Quantum_QuantumSweepListProgram`, `ContinuumCoulomb_Quantum_QuantumSweepProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedTransfer`, `ContinuumCoulomb_Quantum_QuantumTermTime`, `ContinuumCoulomb_Quantum_QuantumTransferIndex`, `ContinuumCoulomb_Quantum_QuantumTransferSweep`, `ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation`, `ContinuumCoulomb_Quantum_QuantumUnaryEnergy`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefix`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefixCertificate`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefixRun`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefixTransfers`, `ContinuumCoulomb_Quantum_QuantumWalkErasure`, `ContinuumCoulomb_Quantum_QuantumWalkSeek`, `ContinuumCoulomb_Quantum_QuantumWireSwap`, `ContinuumCoulomb_Quantum_QuantumXZSample`, `ContinuumCoulomb_Quantum_QuantumXZScalarSample`, `ContinuumCoulomb_Reduction_SourceBondLists`, `ContinuumCoulomb_Reduction_SourcePauli`, `MinUncut_Machines_Runtime`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackBoundedUnary`, `QuantumFactoring_BitStackListLength`, `QuantumFactoring_BitStackOptions`, `QuantumFactoring_BitStackSumInjection`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A000`, `OAIQ092A001` and `OAIQ092A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A008`, `OAIQ092A009`, `OAIQ092A012`, `OAIQ092A013`, `OAIQ092A014`, `OAIQ092A015`, `OAIQ092A016` and `OAIQ092A017`; the statements `OAI_ContinuumCoulomb_CalibratedEvaluation_approximation_error`, `OAI_ContinuumCoulomb_CalibrationRationalBracket_exists_coulomb_brackets`, `OAI_ContinuumCoulomb_ComputableHopping_approximation_error`, `OAI_ContinuumCoulomb_ContactCalibratedGeometry_nonedge_separation`, `OAI_ContinuumCoulomb_CoulombEvaluation_approximation_error`, `OAI_ContinuumCoulomb_RawCoulombSample_value_error`, `OAI_ContinuumCoulomb_localizedCoulombProfile_gap` and `RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`; the proofs of `OAI_ContinuumCoulomb_CalibratedEvaluation_approximation_error`, `OAI_ContinuumCoulomb_CoulombNormalization_approximation_error`, `OAI_ContinuumCoulomb_HubbardGlobal_actualHubbard_effectiveBottom`, `OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget`, `OAI.ContinuumCoulomb.qmaFourTensorFull_effective` and `RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A000
import Definitions.Def_OAIQ092A001
import Definitions.Def_OAIQ092A002

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateL2_r500ffa_1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2_r500ffa_1 :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateL2_r500ffa_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

abbrev μI : Measure ℝ := (volume.restrict (Icc (0 : ℝ) 1))

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-site Pauli matrices on the complete source spin basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem sourceTensor_one (n : ℕ) : sourceTensor n (fun _ => 1) = 1 := by
  classical
  ext s t
  by_cases hst : s = t
  · subst t
    simp [sourceTensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
    simp only [Matrix.one_apply, ite_eq_right hst, sourceTensor]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sourceSpectatorDelta_eq_one (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n)
    (hst : ∀ k, k ≠ i → k ≠ j → s k = t k) : sourceSpectatorDelta n i j s t = 1 := by
  classical
  apply Finset.prod_eq_one
  intro k hk
  exact ite_eq_left (hst k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    (Finset.mem_erase.mp hk).1)

theorem sourceLocalPauli_product_entry (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (μ ν : Fin 3) (s t : SourceSpinBasis n) :
    (sourceLocalPauli n i μ * sourceLocalPauli n j ν) s t =
      pauli μ (s i) (t i) * pauli ν (s j) (t j) * sourceSpectatorDelta n i j s t := by
  classical
  unfold sourceLocalPauli
  rw [sourceTensor_mul]
  unfold sourceTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  simp only [ite_true, if_true, ite_eq_right hij, ite_eq_right hij.symm, mul_one, one_mul]
  rw [← mul_assoc]
  congr 1
  unfold sourceSpectatorDelta
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  simp only [ite_eq_right hki, ite_eq_right hkj, one_mul, Matrix.one_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variational bottoms for the complete simultaneous-mediator spin
Hamiltonian and its effective source matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def sourceMatrixBottom (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) : ℝ :=
  sInf {e | ∃ p : MediatorLowSpace n, ‖p‖ = 1 ∧ e = ⟪p, spinMatrixOperator M p⟫_ℝ}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fixed nine-link contact templates used after spin subdivision.
Coordinates use the Euclidean plane. The link lengths and separation
bounds are stable under small movements of the sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def contactPathVertex (c : ℝ) (k : ℕ) : ContactPoint :=
  contactPoint (∑ j ∈ Finset.range k, contactStepX c j)
    (∑ j ∈ Finset.range k, contactStepY c j)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact circuit prefixes and their unitary changes of coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

def qmaStepMatrix (c : QMACircuit) (t : ℕ) :
    Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ :=
  qmaGateMatrix c.work (c.gates.getD t (.hadamard 0))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Hermitian circuit-history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAPropagationBasis (c : QMACircuit) :=
  Fin c.gates.length × SourceSpinBasis (c.work+1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local endpoint penalties dominate the finite history penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaInputMarker (c : QMACircuit) : Fin (c.gates.length+2) := ⟨1,by omega⟩
def qmaOutputMarker (c : QMACircuit) : Fin (c.gates.length+2) := ⟨c.gates.length,by omega⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tensor-local operators, with explicit finite supports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalLift_one (S : Finset ι) : qmaLocalLift S 1 = 1 := by
  unfold qmaLocalLift
  rw [Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalTensor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor products with identity spectators are actual finite-support
operators, with their small matrix given explicitly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalOn_permutation (S : Finset ι) (F : (ι → Fin 2) → (ι → Fin 2))
    (f : QMASupportBasis S → QMASupportBasis S)
    (hcore : ∀ t, (qmaSupportSplit S (F t)).1 = f (qmaSupportSplit S t).1)
    (hrest : ∀ t, (qmaSupportSplit S (F t)).2 = (qmaSupportSplit S t).2) :
    QMALocalOn S (fun s t => if s = F t then (1:ℂ) else 0) := by
  refine ⟨(fun s t => if s = f t then 1 else 0),?_⟩
  ext s t
  change (if s = F t then (1:ℂ) else 0) =
    (if (qmaSupportSplit S s).1 = f (qmaSupportSplit S t).1 then 1 else 0)*
      if (qmaSupportSplit S s).2 = (qmaSupportSplit S t).2 then 1 else 0
  by_cases hr : (qmaSupportSplit S s).2 = (qmaSupportSplit S t).2
  · have he : (qmaSupportSplit S s).1 = f (qmaSupportSplit S t).1 ↔ s = F t := by
      constructor
      · intro hc
        apply (qmaSupportSplit S).injective
        exact Prod.ext (hc.trans (hcore t).symm) (hr.trans (hrest t).symm)
      · intro h
        subst s
        exact hcore t
    simp [hr,he]
  · have he : s ≠ F t := by
      intro h
      subst s
      exact hr (hrest t)
    simp [hr,he]

theorem qmaLocalOn_sourceTensor (n : ℕ) (S : Finset (Fin n))
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hM : ∀ i, i ∉ S → M i = 1) :
    QMALocalOn S (sourceTensor n M) := by
  refine ⟨(fun s t => ∏ i : {i // i ∈ S}, M i.val (s i) (t i)),?_⟩
  ext s t
  change (∏ i, M i (s i) (t i)) =
    (∏ i : {i // i ∈ S}, M i.val (s i.val) (t i.val))*
      if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0
  by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
  · rw [ite_eq_left hr,mul_one]
    have he (i : Fin n) (_hi : i ∈ Finset.univ) (hi : i ∉ S) : M i (s i) (t i) = 1 := by
      rw [hM i hi]
      have ht := congrFun hr ⟨i,hi⟩
      exact ite_eq_left ht
    have hp := Finset.prod_subset (Finset.subset_univ S) he
    have hs := Finset.prod_subtype (F := inferInstance) S
      (by simp : ∀ i, i ∈ S ↔ i ∈ S) (fun i => M i (s i) (t i))
    exact hp.symm.trans hs
  · rw [ite_eq_right hr,mul_zero]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    rw [hM i.val i.property]
    exact ite_eq_right hi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input checks may occur at separate history times before their qubits are changed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaInputCheck (c : QMACircuit) (i : Fin (c.work+1)) (s : SourceSpinBasis (c.work+1)) : Prop :=
  c.witness ≤ i.val ∧ s i ≠ 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact three-CNOT transfers for a circuit whose active wires move through a grid. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaWireSwapGates {work : ℕ} (i j : Fin (work+1)) : List QMAGate :=
  [.controlledNot i.val j.val,.controlledNot j.val i.val,.controlledNot i.val j.val]

theorem qmaWireSwapGates_wellFormed {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j) :
    ∀ g ∈ qmaWireSwapGates i j, g.WellFormed (work+1) := by
  intro g hg
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨i.isLt,j.isLt,hval⟩
  · exact ⟨j.isLt,i.isLt,hval.symm⟩
  · exact ⟨i.isLt,j.isLt,hval⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sweeps of disjoint three-CNOT wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaTransferGates {work : ℕ} : List (Fin (work+1) × Fin (work+1)) → List QMAGate
  | [] => []
  | (i,j)::ps => qmaWireSwapGates i j ++ qmaTransferGates ps

theorem qmaTransferGates_length {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1))) :
    (qmaTransferGates ps).length = 3*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    simp only [qmaTransferGates,List.length_append,qmaWireSwapGates,List.length_cons,
      List.length_nil,ih]
    omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMappedGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit gate addresses for a logical register embedded in a larger wire grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaMapGate (sourceWork targetWork : ℕ) (f : Fin (sourceWork+1) → Fin (targetWork+1)) :
    QMAGate → QMAGate
  | .hadamard i => .hadamard (f (qmaQubit sourceWork i)).val
  | .phaseT i => .phaseT (f (qmaQubit sourceWork i)).val
  | .controlledNot i j =>
      .controlledNot (f (qmaQubit sourceWork i)).val (f (qmaQubit sourceWork j)).val

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSwapConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conjugation by the three-CNOT adjacent-swap program. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaOrderedCnot (i j : ℕ) (forward : Bool) : QMAGate :=
  if forward then .controlledNot i j else .controlledNot j i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAdjacentCnot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size adjacent-CNOT program for one arbitrarily separated CNOT. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaAdjacentCnot (work : ℕ) : (a d : ℕ) → a+d+1 < work+1 → Bool → List QMAGate
  | a,0,_,forward => [qmaOrderedCnot a (a+1) forward]
  | a,d+1,h,forward =>
      qmaWireSwapGates (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ ++
      qmaAdjacentCnot work (a+1) d (by omega) forward ++
      qmaWireSwapGates (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBooleans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

noncomputable def boolOr : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 || x.2) := ofBool₂ boolCode or
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackSumInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def sumLeft {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure ea (sumCode ea eb) Sum.inl:=
  (prepend ea [false]).result (by intro a;rfl)
noncomputable def sumRight {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure eb (sumCode ea eb) Sum.inr:=
  (prepend eb [true]).result (by intro a;rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackOptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def binaryEq : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1=x.2)) := by
  let swap:=(second Nat.bits Nat.bits).pair (first Nat.bits Nat.bits)
  exact (boolAnd.comp (binaryLe.pair (binaryLe.comp swap))).congrFun
    (by intro x;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq];omega)
noncomputable def prodEq [DecidableEq α] [DecidableEq β]
    (pa : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2)))
    (pb : Procedure (prodCode eb eb) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode (prodCode ea eb) (prodCode ea eb)) boolCode
      (fun x=>decide (x.1=x.2)) := by
  let l:=first (prodCode ea eb) (prodCode ea eb)
  let r:=second (prodCode ea eb) (prodCode ea eb)
  let a:=pa.comp (((first ea eb).comp l).pair ((first ea eb).comp r))
  let b:=pb.comp (((second ea eb).comp l).pair ((second ea eb).comp r))
  exact (boolAnd.comp (a.pair b)).congrFun (by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.mk.injEq])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackListLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
namespace Procedure
noncomputable def listLength (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) Nat.bits List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) unaryCode 0)
  exact (unaryToBits.comp (rep.comp start)).congrFun (by intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBoundedUnary
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def unaryDecodeStepP : Procedure (prodCode Nat.bits unaryCode) (prodCode Nat.bits unaryCode)
    unaryDecodeStep := by
  let x:=first Nat.bits unaryCode
  let y:=second Nat.bits unaryCode
  let next:=(binarySub.comp (x.pair (Procedure.constant _ Nat.bits 1))).pair (unarySuccessor.comp y)
  exact (conditional (binaryZero.comp x) (identity _) next).congrFun (by
    intro s;unfold unaryDecodeStep;split <;> simp_all)
noncomputable def clippedUnary : Procedure (prodCode unaryCode Nat.bits) unaryCode (fun x=>min x.1 x.2) := by
  let rep:=unaryDecodeStepP.iterate Polynomial.X (by
    intro n s i hi
    rw [unaryDecodeStep_iterate]
    have hbits:=bits_length_mono (Nat.sub_le s.1 i)
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  let inp:=(first unaryCode Nat.bits).pair
    ((second unaryCode Nat.bits).pair (Procedure.constant _ unaryCode 0))
  exact ((second Nat.bits unaryCode).comp (rep.comp inp)).congrFun (by
    intro x;dsimp only [Function.comp_def];rw [unaryDecodeStep_iterate];simp)
noncomputable def boundedUnary {α : Type} {ea : α→List Bool} {f B : α→ℕ}
    (p : Procedure ea Nat.bits f) (b : Procedure ea unaryCode B) (h : ∀a,f a ≤ B a) :
    Procedure ea unaryCode f :=
  (clippedUnary.comp (b.pair p)).congrFun (by intro a;exact min_eq_right (h a))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal controls and changes between explicit qubit coordinate sets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalOn_diagonal (S : Finset ι) (d : (ι → Fin 2) → ℂ)
    (hd : ∀ s t, (∀ i ∈ S, s i = t i) → d s = d t) :
    QMALocalOn S (Matrix.diagonal d) := by
  refine ⟨Matrix.diagonal (fun u => d (qmaSupportExtend S u)),?_⟩
  ext s t
  rw [qmaLocalLift_apply]
  by_cases hs : (fun i : {i // i ∈ S} => s i.val) = (fun i : {i // i ∈ S} => t i.val)
  · by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
    · have hst : s = t := by
        funext i
        by_cases hi : i ∈ S
        · exact congrFun hs ⟨i,hi⟩
        · exact congrFun hr ⟨i,hi⟩
      subst t
      simp only [Matrix.diagonal_apply_eq,ite_true, if_true,mul_one]
      apply hd
      intro i hi
      simp [qmaSupportExtend,hi]
    · have hst : s ≠ t := by intro h; apply hr; rw [h]
      simp only [Matrix.diagonal_apply_ne _ hst,ite_eq_right hr,mul_zero]
  · have hst : s ≠ t := by intro h; apply hs; rw [h]
    simp only [Matrix.diagonal_apply_ne _ hst,Matrix.diagonal_apply_ne _ hs,zero_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalAction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actions of local flips and spectator-identity tensor factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaBitFlipMatrix_local (i : ι) : QMALocalOn {i} (qmaBitFlipMatrix i) := by
  apply qmaLocalOn_permutation {i} (qmaBitFlip i)
    (fun s j => Equiv.swap (0:Fin 2) 1 (s j))
  · intro s
    funext j
    have hj : j.val = i := Finset.mem_singleton.mp j.property
    simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaBitFlip,hj]
  · intro s
    funext j
    have hj : j.val ≠ i := by simpa using j.property
    simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaBitFlip,hj]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every guarded propagation term acts on three clock bits and at most two
computation bits. This is the actual unary-clock operator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaGuardProjection (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  Matrix.diagonal (fun s => if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
    s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then 1 else 0)

def qmaLocalPropagationDelta (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaGuardProjection c t *
    (qmaBitFlipMatrix (Sum.inl (qmaClockMiddle c.gates.length t))-
      qmaJoinMatrix 1 (qmaStepMatrix c t.val))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPenalties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The clock and endpoint penalties are explicit one- and two-qubit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaBitDiagonal_local (i : ι) (f : Fin 2 → ℂ) :
    QMALocalOn {i} (qmaBitDiagonal i f) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h i (by simp)]

theorem qmaPairDiagonal_local (i j : ι) (f : Fin 2 → Fin 2 → ℂ) :
    QMALocalOn {i,j} (qmaPairDiagonal i j f) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h i (by simp),h j (by simp)]

def qmaClockFaultTerm (c : QMACircuit) (i : Fin (c.gates.length+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl i.castSucc) (Sum.inl i.succ)
    (fun a b => if a = 0 ∧ b = 1 then 1 else 0)

def qmaClockLeftTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaBitDiagonal (Sum.inl 0) (fun a => if a = 1 then 0 else 1)

def qmaClockRightTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaBitDiagonal (Sum.inl (Fin.last (c.gates.length+1))) (fun a => if a = 0 then 0 else 1)

def qmaInputTerm (c : QMACircuit) (i : Fin (c.work+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl (qmaInputMarker c)) (Sum.inr i)
    (fun a b => if a = 0 then if c.witness ≤ i.val ∧ b ≠ 0 then 7 else 0 else 0)

def qmaOutputTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl (qmaOutputMarker c)) (Sum.inr (Fin.last c.work))
    (fun a b => if a = 1 ∧ b ≠ 1 then 1 else 0)

theorem qmaClockFaultTerm_local (c : QMACircuit) (i : Fin (c.gates.length+1)) :
    QMALocalOn {Sum.inl i.castSucc,Sum.inl i.succ} (qmaClockFaultTerm c i) :=
  qmaPairDiagonal_local _ _ _

theorem qmaClockLeftTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl 0} (qmaClockLeftTerm c) := qmaBitDiagonal_local _ _

theorem qmaClockRightTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl (Fin.last (c.gates.length+1))} (qmaClockRightTerm c) :=
  qmaBitDiagonal_local _ _

theorem qmaOutputTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)} (qmaOutputTerm c) :=
  qmaPairDiagonal_local _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite real local families and the three gadget stages used by the
circuit-to-spin reduction. This records mathematical families, not a compiler. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMARealLocalModel (d : ℕ) where
  Q : Type
  Term : Type
  [qFinite : Fintype Q]
  [qDecidable : DecidableEq Q]
  [termFinite : Fintype Term]
  matrix : Term → Matrix (Q → Fin 2) (Q → Fin 2) ℂ
  sites : Term → Finset Q
  localOn : ∀ a, QMALocalOn (sites a) (matrix a)
  card : ∀ a, (sites a).card ≤ d
  hermitian : ∀ a, (matrix a).IsHermitian
  real : ∀ a, QMAEntryParity false (matrix a)

attribute [instance] QMARealLocalModel.qFinite QMARealLocalModel.qDecidable QMARealLocalModel.termFinite

def QMARealLocalModel.energy {d : ℕ} (M : QMARealLocalModel d) : ℝ :=
  MediatorGraph.normalizedBottom (∑ a, M.matrix a)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliMonomial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse actions of the physical Pauli matrices, retaining a rational part. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaLocalPauli_monomial (n : ℕ) (i : Fin n) (μ : Fin 3)
    (s t : SourceSpinBasis n) :
    sourceLocalPauli n i μ s t = qmaPauliPhase μ*(qmaPhysicalPauliSign μ (s i):ℂ)*
      (if Function.update s i (qmaPauliBit μ (s i)) = t then 1 else 0) := by
  unfold sourceLocalPauli sourceTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, if_true,qmaPauli_monomial]
  have hrest (k : Fin n) (hk : k ∈ Finset.univ.erase i) :
      (if k = i then pauli μ else 1) (s k) (t k) = if s k = t k then 1 else 0 := by
    simp [(Finset.mem_erase.mp hk).1,Matrix.one_apply]
  rw [Finset.prod_congr rfl hrest]
  by_cases h : Function.update s i (qmaPauliBit μ (s i)) = t
  · have hi := congrFun h i
    have hk (k : Fin n) (hki : k ≠ i) : s k = t k := by
      simpa only [Function.update_of_ne hki] using congrFun h k
    simp only [Function.update_self] at hi
    rw [ite_eq_left h,ite_eq_left hi,Finset.prod_eq_one (fun k hk' =>
      ite_eq_left (hk k (Finset.mem_erase.mp hk').1))]
    simp
  · rw [ite_eq_right h]
    by_cases hi : qmaPauliBit μ (s i) = t i
    · have hbad : ∃ k ∈ Finset.univ.erase i, s k ≠ t k := by
        by_contra hn
        push Not at hn
        apply h
        funext k
        by_cases hki : k = i
        · subst k
          simpa only [Function.update_self] using hi
        · simpa only [Function.update_of_ne hki] using
            hn k (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
      obtain ⟨k,hk,hne⟩ := hbad
      rw [ite_eq_left hi,Finset.prod_eq_zero hk (ite_eq_right hne)]
      simp
    · simp [hi]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local initialization checks at arbitrary unary-clock positions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaClockAt (T : ℕ) (t : Fin (T+1)) (s : SourceSpinBasis (T+2)) : Prop :=
  s t.castSucc = 1 ∧ s t.succ = 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distributed-input history is an actual Hermitian matrix on all unary strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaDistributedInputSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    Finset (QMACircuitQubit c) :=
  {Sum.inl (τ i).castSucc,Sum.inl (τ i).succ,Sum.inr i}

def qmaDistributedInputTerm (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  Matrix.diagonal (fun s => if qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
    qmaInputCheck c i (s ∘ Sum.inr) then 14 else 0)

theorem qmaDistributedInputTerm_local (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    QMALocalOn (qmaDistributedInputSites c τ i) (qmaDistributedInputTerm c τ i) := by
  apply qmaLocalOn_diagonal
  intro s r h
  have hl := h (Sum.inl (τ i).castSucc) (by simp [qmaDistributedInputSites])
  have hr := h (Sum.inl (τ i).succ) (by simp [qmaDistributedInputSites])
  have hi := h (Sum.inr i) (by simp [qmaDistributedInputSites])
  apply ite_congr
  · simp only [qmaClockAt,qmaInputCheck,Function.comp_apply,hl,hr,hi]
  · intro _; rfl
  · intro _; rfl

theorem qmaDistributedInputSites_card (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    (qmaDistributedInputSites c τ i).card = 3 := by
  have ht : (τ i).castSucc ≠ (τ i).succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [qmaDistributedInputSites,ht]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size, five-local term family with distributed initialization checks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaDistributedTermMatrix (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c →
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ
  | .inl i => qmaClockFaultTerm c i
  | .inr (.inl b) => if b = 0 then qmaClockLeftTerm c else qmaClockRightTerm c
  | .inr (.inr (.inl i)) => qmaDistributedInputTerm c τ i
  | .inr (.inr (.inr (.inl _))) => qmaOutputTerm c
  | .inr (.inr (.inr (.inr t))) =>
    ((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestGate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing a gate by an exact bounded-length nearest-neighbor gate sequence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaAdjacentCnot_valid (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    ∀ g ∈ qmaAdjacentCnot work a d h b, g.WellFormed (work+1) ∧ g.Adjacent := by
  induction d generalizing a with
  | zero =>
    intro g hg
    have he : g = qmaOrderedCnot a (a+1) b := by simpa [qmaAdjacentCnot] using hg
    subst g
    cases b <;> simp only [qmaOrderedCnot,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
      QMAGate.WellFormed,QMAGate.Adjacent]
    · exact ⟨⟨h,by omega,by omega⟩,by simp⟩
    · exact ⟨⟨by omega,h,by omega⟩,by simp⟩
  | succ d ih =>
    intro g hg
    simp only [qmaAdjacentCnot,List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · have hs : g.WellFormed (work+1) := qmaWireSwapGates_wellFormed
        (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ (by intro he; cases he) g hg
      refine ⟨hs,?_⟩
      simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [QMAGate.Adjacent]
    · exact ih (a+1) (by omega) g hg
    · have hs : g.WellFormed (work+1) := qmaWireSwapGates_wellFormed
        (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ (by intro he; cases he) g hg
      refine ⟨hs,?_⟩
      simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [QMAGate.Adjacent]

def qmaNearestGate (work : ℕ) : QMAGate → List QMAGate
  | .controlledNot i j =>
      if h : i < j ∧ j < work+1 then
        qmaAdjacentCnot work i (j-i-1) (by omega) true
      else if h : j < i ∧ i < work+1 then
        qmaAdjacentCnot work j (i-j-1) (by omega) false
      else [.controlledNot i j]
  | g => [g]

theorem qmaNearestGate_valid (work : ℕ) (g : QMAGate) (hg : g.WellFormed (work+1)) :
    ∀ k ∈ qmaNearestGate work g, k.WellFormed (work+1) ∧ k.Adjacent := by
  cases g with
  | hadamard i => simpa [qmaNearestGate,QMAGate.Adjacent] using hg
  | phaseT i => simpa [qmaNearestGate,QMAGate.Adjacent] using hg
  | controlledNot i j =>
    rcases hg with ⟨hi,hj,hne⟩
    by_cases h : i < j ∧ j < work+1
    · simp only [qmaNearestGate,dite_eq_left h]
      exact qmaAdjacentCnot_valid _ _ _ _ _
    · have h' : j < i ∧ i < work+1 := by omega
      simp only [qmaNearestGate,dite_eq_right h,dite_eq_left h']
      exact qmaAdjacentCnot_valid _ _ _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact nearest-neighbor compilation with an explicit polynomial size bound. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

abbrev qmaNearestCircuit (c : QMACircuit) : QMACircuit :=
  ⟨c.work,c.witness,c.gates.flatMap (qmaNearestGate c.work)⟩

theorem qmaNearestCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaNearestCircuit c).WellFormed := by
  refine ⟨hc.1,?_⟩
  intro g hg
  obtain ⟨k,hk,hg⟩ := List.mem_flatMap.mp hg
  exact (qmaNearestGate_valid c.work k (hc.2 k hk) g hg).1

theorem qmaNearestCircuit_adjacent (c : QMACircuit) (hc : c.WellFormed) :
    ∀ g ∈ (qmaNearestCircuit c).gates, g.Adjacent := by
  intro g hg
  obtain ⟨k,hk,hg⟩ := List.mem_flatMap.mp hg
  exact (qmaNearestGate_valid c.work k (hc.2 k hk) g hg).2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowStageSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each sweep stage uses only vertical transfers and its single horizontal gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTransferGates_member {work : ℕ}
    (ps : List (Fin (work+1) × Fin (work+1))) (g : QMAGate) :
    g ∈ qmaTransferGates ps ↔ ∃ p ∈ ps, g ∈ qmaWireSwapGates p.1 p.2 := by
  induction ps with
  | nil => simp [qmaTransferGates]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    simp only [qmaTransferGates,List.mem_append,ih,List.mem_cons]
    aesop

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full reference-register basis diagonalizes every local Y operator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaReferenceTensor (n : ℕ) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceTensor n (fun _ => qmaReferenceBasis)

theorem qmaReferenceTensor_gram (n : ℕ) :
    (qmaReferenceTensor n).conjTranspose*qmaReferenceTensor n = 1 := by
  unfold qmaReferenceTensor
  rw [sourceTensor_conjTranspose,sourceTensor_mul]
  simp only [qmaReferenceBasis_gram]
  exact sourceTensor_one n

theorem qmaReferenceTensor_cogram (n : ℕ) :
    qmaReferenceTensor n*(qmaReferenceTensor n).conjTranspose = 1 := by
  exact mul_eq_one_comm.mp (qmaReferenceTensor_gram n)

theorem qmaReferenceTensor_y (n : ℕ) (i : Fin n) :
    (qmaReferenceTensor n).conjTranspose*sourceLocalPauli n i 1*qmaReferenceTensor n =
      sourceLocalPauli n i 2 := by
  unfold qmaReferenceTensor sourceLocalPauli
  rw [sourceTensor_conjTranspose,sourceTensor_mul,sourceTensor_mul]
  congr 1
  funext k
  by_cases hk : k = i
  · simp only [hk,ite_true, if_true]
    exact qmaReferenceBasis_y
  · simp only [hk,ite_false, if_false,mul_one,qmaReferenceBasis_gram]

theorem qmaReferenceTensor_yy (n : ℕ) (i j : Fin n) :
    (qmaReferenceTensor n).conjTranspose*
        (sourceLocalPauli n i 1*sourceLocalPauli n j 1)*qmaReferenceTensor n =
      sourceLocalPauli n i 2*sourceLocalPauli n j 2 := by
  rw [←qmaReferenceTensor_y n i,←qmaReferenceTensor_y n j]
  simp only [mul_assoc]
  rw [←mul_assoc (qmaReferenceTensor n),qmaReferenceTensor_cogram,one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTensor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact diagonal tensors and the computational-basis reference-chain penalty. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem sourceTensor_diagonal (n : ℕ) (d : Fin n → Fin 2 → ℂ) :
    sourceTensor n (fun i => Matrix.diagonal (d i)) =
      Matrix.diagonal (fun s => ∏ i, d i (s i)) := by
  ext s t
  by_cases h : s = t
  · subst t
    simp [sourceTensor]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sourceLocalPauli_z_diagonal (n : ℕ) (i : Fin n) :
    sourceLocalPauli n i 2 = Matrix.diagonal (fun s => qmaZSign (s i)) := by
  have hlocal (k : Fin n) : (if k = i then pauli 2 else (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      Matrix.diagonal (fun b => if k = i then qmaZSign b else 1) := by
    by_cases hk : k = i
    · simp only [hk,ite_true, if_true]
      exact pauliZ_diagonal
    · simp [hk]
  unfold sourceLocalPauli
  simp_rw [hlocal]
  rw [sourceTensor_diagonal]
  congr 1
  funext s
  simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferencePenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nearest-neighbor real YY penalty has a unit complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaReferenceYEdge_diagonalized (n : ℕ) (i j : Fin n) :
    (qmaReferenceTensor n).conjTranspose*
      ((1/2 : ℂ) • (1-sourceLocalPauli n i 1*sourceLocalPauli n j 1))*
        qmaReferenceTensor n =
    (1/2 : ℂ) • (1-sourceLocalPauli n i 2*sourceLocalPauli n j 2) := by
  rw [mul_smul_comm,smul_mul_assoc,Matrix.mul_sub,Matrix.sub_mul,mul_one,
    qmaReferenceTensor_gram,qmaReferenceTensor_yy]

theorem sourcePauli_yy_real (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (s t : SourceSpinBasis n) : ((sourceLocalPauli n i 1*sourceLocalPauli n j 1) s t).im = 0 := by
  have hY (a b c d : Fin 2) : (pauli 1 a b*pauli 1 c d).im = 0 := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [pauli,pauliY]
  rw [sourceLocalPauli_product_entry n i j hij]
  by_cases hs : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [sourceSpectatorDelta_eq_one n i j s t hs,mul_one]
    exact hY _ _ _ _
  · rw [sourceSpectatorDelta_eq_zero n i j s t hs,mul_zero]
    rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedRebit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each complex term uses its own local Y reference; uniform sectors recover it exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaDistributedRebitTerm (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ qmaEntryReal A +
    (-Complex.I) • (sourceLocalPauli n i 1 ⊗ₖ qmaEntryImag A)

def qmaReferenceExtension (n : ℕ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  qmaReferenceTensor n ⊗ₖ (1 : Matrix α α ℂ)

theorem qmaDistributedRebitTerm_diagonalized (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n =
    (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ qmaEntryReal A +
      (-Complex.I) • (sourceLocalPauli n i 2 ⊗ₖ qmaEntryImag A) := by
  unfold qmaReferenceExtension qmaDistributedRebitTerm
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.mul_add,Matrix.add_mul,
    mul_smul_comm,smul_mul_assoc]
  simp only [←Matrix.mul_kronecker_mul,mul_one,one_mul,qmaReferenceTensor_gram,
    qmaReferenceTensor_y]

theorem qmaDistributedRebitTerm_block (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (s t : SourceSpinBasis n) (a b : α) :
    ((qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n) (s,a) (t,b) =
    if s = t then (if s i = 0 then star (A a b) else A a b) else 0 := by
  rw [qmaDistributedRebitTerm_diagonalized,sourceLocalPauli_z_diagonal]
  by_cases h : s = t
  · subst t
    simp only [Matrix.add_apply,Matrix.kronecker_apply,Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,one_mul,qmaEntryReal,qmaEntryImag]
    simp only [ite_true, if_true]
    generalize hb : s i = c
    fin_cases c <;> apply Complex.ext <;> simp [qmaZSign,Complex.mul_re,Complex.mul_im]
  · simp [Matrix.add_apply,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sector decomposition for distributed realification. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaReferenceBlocks (n : ℕ) (B : SourceSpinBasis n → Matrix α α ℂ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  fun p q => if p.1 = q.1 then B p.1 p.2 q.2 else 0

def qmaReferenceSectorTerm (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (s : SourceSpinBasis n) : Matrix α α ℂ :=
  if s i = 0 then qmaConjugateMatrix A else A

theorem qmaDistributedRebitTerm_blocks (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n =
        qmaReferenceBlocks n (qmaReferenceSectorTerm n i A) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  rw [qmaDistributedRebitTerm_block]
  by_cases hs : s = t
  · subst t
    by_cases hz : s i = 0 <;> simp [qmaReferenceBlocks,qmaReferenceSectorTerm,qmaConjugateMatrix,hz]
  · simp [qmaReferenceBlocks,hs]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space variational comparison for the actual distributed reference family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaReferenceExtension_gram (n : ℕ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaReferenceExtension (α := α) n = 1 := by
  unfold qmaReferenceExtension
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,←Matrix.mul_kronecker_mul,
    qmaReferenceTensor_gram,one_mul,Matrix.one_kronecker_one]

theorem qmaReferenceExtension_cogram (n : ℕ) :
    qmaReferenceExtension (α := α) n*(qmaReferenceExtension (α := α) n).conjTranspose = 1 :=
  mul_eq_one_comm.mp (qmaReferenceExtension_gram n)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit consecutive labels for every term in the distributed history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaHistoryTermIndex (c : QMACircuit) : QMACircuitTerm c ≃ Fin (qmaHistoryReferenceWork c+1) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumCongr (Equiv.refl _)
        ((Equiv.sumCongr qmaUnitFin (Equiv.refl _)).trans finSumFinEquiv)).trans
          finSumFinEquiv)).trans finSumFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr (by unfold qmaHistoryReferenceWork; omega)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distributed reference terms are actual real Hermitian matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaLocalY_real_zero (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    (sourceLocalPauli n i 1 s t).re = 0 := by
  rw [qmaLocalPauli_monomial]
  simp only [qmaPauliPhase,Fin.isValue,ite_true, if_true]
  split_ifs <;> simp

omit [Fintype α] [DecidableEq α] in
theorem qmaDistributedRebitTerm_real (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (p q : SourceSpinBasis n × α) : (qmaDistributedRebitTerm n i A p q).im = 0 := by
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [qmaDistributedRebitTerm,Matrix.add_apply,Matrix.kronecker_apply,
    Matrix.smul_apply,smul_eq_mul,qmaEntryReal,qmaEntryImag,Complex.add_im,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
    qmaLocalY_real_zero,zero_mul,mul_zero,add_zero,sub_zero]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype α] [DecidableEq α] in
theorem qmaReferenceBlocks_hermitian (n : ℕ) (A : SourceSpinBasis n → Matrix α α ℂ)
    (hA : ∀ s, (A s).IsHermitian) : (qmaReferenceBlocks n A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t
  · subst t
    simpa only [qmaReferenceBlocks,ite_true, if_true] using (hA s).apply a b
  · simp [qmaReferenceBlocks,hs,Ne.symm hs]

theorem qmaDistributedRebitTerm_hermitian (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (hA : A.IsHermitian) : (qmaDistributedRebitTerm n i A).IsHermitian := by
  apply qmaHermitian_of_conjugated (qmaReferenceExtension (α := α) n) _
    (qmaReferenceExtension_cogram n)
  rw [qmaDistributedRebitTerm_blocks]
  apply qmaReferenceBlocks_hermitian
  intro s
  unfold qmaReferenceSectorTerm
  split_ifs
  · exact qmaConjugateMatrix_hermitian A hA
  · exact hA

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A separate reference qubit adds exactly one site to each original support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalY_local (n : ℕ) (i : Fin n) :
    QMALocalOn {i} (sourceLocalPauli n i 1) := by
  apply qmaLocalOn_sourceTensor
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [hk]

def qmaDistributedRebitOnQubits (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    Matrix (Fin n ⊕ ι → Fin 2) (Fin n ⊕ ι → Fin 2) ℂ :=
  (qmaDistributedRebitTerm n i A).submatrix
    (Equiv.sumArrowEquivProdArrow (Fin n) ι (Fin 2))
    (Equiv.sumArrowEquivProdArrow (Fin n) ι (Fin 2))

theorem qmaDistributedRebitOnQubits_eq (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    qmaDistributedRebitOnQubits n i A =
      qmaJoinMatrix (ι := Fin n) 1 (qmaEntryReal A)+
      (-Complex.I) • qmaJoinMatrix (sourceLocalPauli n i 1) (qmaEntryImag A) := by
  ext s t
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem qmaDistributedRebitOnQubits_real (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (s t : Fin n ⊕ ι → Fin 2) :
    (qmaDistributedRebitOnQubits n i A s t).im = 0 :=
  qmaDistributedRebitTerm_real _ _ _ _ _

theorem qmaDistributedRebitOnQubits_hermitian (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : A.IsHermitian) :
    (qmaDistributedRebitOnQubits n i A).IsHermitian :=
  (qmaDistributedRebitTerm_hermitian n i A hA).submatrix _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdges
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference alignment penalty is a sum of real two-site interactions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaReferenceYEdge (n : ℕ) (i : Fin n) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 1*sourceLocalPauli (n+1) i.succ 1)

theorem qmaReferenceYEdge_real (n : ℕ) (i : Fin n) (s t : SourceSpinBasis (n+1)) :
    (qmaReferenceYEdge n i s t).im = 0 := by
  have hi : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  simp only [qmaReferenceYEdge,Matrix.smul_apply,smul_eq_mul,Complex.mul_im,
    Matrix.sub_apply,Complex.sub_im,sourcePauli_yy_real _ _ _ hi,Matrix.one_apply]
  split_ifs <;> norm_num

theorem qmaReferenceYEdge_hermitian (n : ℕ) (i : Fin n) :
    (qmaReferenceYEdge n i).IsHermitian := by
  apply qmaHermitian_of_conjugated (qmaReferenceTensor (n+1)) _
    (qmaReferenceTensor_cogram _)
  rw [qmaReferenceYEdge,qmaReferenceYEdge_diagonalized,sourceLocalPauli_z_diagonal,
    sourceLocalPauli_z_diagonal,Matrix.diagonal_mul_diagonal]
  apply Matrix.IsHermitian.ext
  intro s t
  by_cases h : s = t
  · subst t
    simp [Matrix.smul_apply,smul_eq_mul,qmaZSign]
    split_ifs <;> norm_num
  · simp [Matrix.smul_apply,smul_eq_mul,h,Ne.symm h]

def qmaReferenceEdgeOnQubits (n : ℕ) (i : Fin n) :
    Matrix (Fin (n+1) ⊕ ι → Fin 2) (Fin (n+1) ⊕ ι → Fin 2) ℂ :=
  qmaJoinMatrix (qmaReferenceYEdge n i) (ι := Fin (n+1)) (κ := ι) 1

theorem qmaReferenceEdgeOnQubits_real (n : ℕ) (i : Fin n)
    (s t : Fin (n+1) ⊕ ι → Fin 2) : (qmaReferenceEdgeOnQubits n i s t).im = 0 := by
  change (qmaReferenceYEdge n i (s ∘ Sum.inl) (t ∘ Sum.inl)*
    (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (s ∘ Sum.inr) (t ∘ Sum.inr)).im = 0
  simp only [Complex.mul_im,qmaReferenceYEdge_real,zero_mul,add_zero,Matrix.one_apply]
  split_ifs <;> simp

theorem qmaReferenceEdgeOnQubits_hermitian (n : ℕ) (i : Fin n) :
    (qmaReferenceEdgeOnQubits (ι := ι) n i).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  simp only [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,
    (qmaReferenceYEdge_hermitian n i).eq,Matrix.conjTranspose_one]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full reference Hamiltonian as explicit bounded-support real terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaReferenceTermMatrix (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    QMAReferenceTerm n → Matrix (Fin (n+1) ⊕ ι → Fin 2) (Fin (n+1) ⊕ ι → Fin 2) ℂ
  | .inl i => qmaDistributedRebitOnQubits (n+1) i (A i)
  | .inr i => qmaReferenceEdgeOnQubits n i

def qmaReferenceTermSites (n : ℕ) (S : Fin (n+1) → Finset ι) :
    QMAReferenceTerm n → Finset (Fin (n+1) ⊕ ι)
  | .inl i => qmaDistributedRebitSites (n+1) i (S i)
  | .inr i => qmaReferenceEdgeSites n i

omit [Fintype ι] in
theorem qmaReferenceTerm_card (n : ℕ) (S : Fin (n+1) → Finset ι)
    (hS : ∀ i, (S i).card ≤ 5) (t : QMAReferenceTerm n) :
    (qmaReferenceTermSites n S t).card ≤ 6 := by
  cases t with
  | inl i =>
    change (qmaDistributedRebitSites (n+1) i (S i)).card ≤ 6
    rw [qmaDistributedRebitSites_card]
    have := hS i
    omega
  | inr i =>
    change ({Sum.inl i.castSucc,Sum.inl i.succ} : Finset (Fin (n+1) ⊕ ι)).card ≤ 6
    have h := Finset.card_insert_le (Sum.inl i.castSucc)
      ({Sum.inl i.succ} : Finset (Fin (n+1) ⊕ ι))
    simp only [Finset.card_singleton] at h
    omega

theorem qmaReferenceTerm_hermitian (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (t : QMAReferenceTerm n) :
    (qmaReferenceTermMatrix n A t).IsHermitian := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_hermitian _ _ _ (hA i)
  | inr i => exact qmaReferenceEdgeOnQubits_hermitian _ _

theorem qmaReferenceTerm_real (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (t : QMAReferenceTerm n) (s u : Fin (n+1) ⊕ ι → Fin 2) :
    (qmaReferenceTermMatrix n A t s u).im = 0 := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_real _ _ _ _ _
  | inr i => exact qmaReferenceEdgeOnQubits_real _ _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedTransfer
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column-labelled transfers retain the exact gates and have three gates per column. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaColumnTransfer {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) : List (QMAGate × Fin (width+1)) :=
  cols.flatMap (fun i => (qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)))

theorem qmaColumnTransfer_gates {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) :
    (qmaColumnTransfer l r cols).map Prod.fst =
      qmaTransferGates (cols.map (fun i => (l i,r i))) := by
  induction cols with
  | nil => rfl
  | cons i cols ih =>
    change ((qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)) ++
      qmaColumnTransfer l r cols).map Prod.fst =
      qmaWireSwapGates (l i) (r i) ++ qmaTransferGates (cols.map (fun i => (l i,r i)))
    simp only [List.map_append,List.map_map,Function.comp_def,List.map_id',ih]

theorem qmaColumnTransfer_count {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (j : Fin (width+1)) :
    ((qmaColumnTransfer l r cols).filter (fun p => decide (p.2 = j))).length =
      3*(cols.filter (fun i => decide (i = j))).length := by
  induction cols with
  | nil => simp [qmaColumnTransfer]
  | cons i cols ih =>
    change (((qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)) ++
      qmaColumnTransfer l r cols).filter (fun p => decide (p.2 = j))).length = _
    rw [List.filter_append,List.length_append,ih]
    by_cases hij : i = j <;> simp [qmaWireSwapGates,hij,Nat.mul_add,Nat.add_comm]

theorem qmaColumnTransfer_member {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (g : QMAGate) (j : Fin (width+1))
    (h : (g,j) ∈ qmaColumnTransfer l r cols) :
    j ∈ cols ∧ g ∈ qmaWireSwapGates (l j) (r j) := by
  obtain ⟨i,hi,hh⟩ := List.mem_flatMap.mp h
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hh
  have hij : i = j := congrArg Prod.snd he
  have hkg : k = g := congrArg Prod.fst he
  subst i
  subst k
  exact ⟨hi,hk⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferIndex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact time-to-column indexing for the three-gate transfer blocks. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaColumnTransfer_length {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) : (qmaColumnTransfer l r cols).length = 3*cols.length := by
  have h := congrArg List.length (qmaColumnTransfer_gates l r cols)
  simpa only [List.length_map,qmaTransferGates_length] using h

theorem qmaColumnTransfer_get_column {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (t : ℕ) (ht : t < 3*cols.length) :
    ((qmaColumnTransfer l r cols)[t]'(by rw [qmaColumnTransfer_length]; exact ht)).2 =
      cols[t/3]'(by omega) := by
  induction cols generalizing t with
  | nil => simp at ht
  | cons a cols ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        cases t with
        | zero => rfl
        | succ t =>
          have ht' : t < 3*cols.length := by simp only [List.length_cons] at ht; omega
          have hd : (t+1+1+1)/3 = t/3+1 := by omega
          change ((qmaColumnTransfer l r cols)[t]'(by rw [qmaColumnTransfer_length]; exact ht')).2 =
            (a::cols)[(t+1+1+1)/3]
          simpa only [hd,List.getElem_cons_succ] using ih t ht'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCongestion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal sweep has at most four gates assigned to any grid cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTagRow_count (rows width : ℕ) (ps : List (QMAGate × Fin (width+1)))
    (r q : Fin (rows+1)) (j : Fin (width+1)) :
    (((ps.map (fun p => (p.1,(r,p.2)))).filter
      (fun p => decide (p.2 = (q,j)))).length) =
      if r = q then (ps.filter (fun p => decide (p.2 = j))).length else 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨g,i⟩
    by_cases hr : r = q
    · subst q
      by_cases hi : i = j <;> simp [hi,ih]
    · simp [hr,ih]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumStagePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row-labelled stages form bounded-step spatial paths with explicit endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaRowLift {rows width : ℕ} (r : Fin (rows+1)) (ps : List (QMAGate × Fin (width+1))) :
    List (QMAGate × QMAGridCell rows width) := ps.map (fun p => (p.1,(r,p.2)))

theorem qmaRowLift_chain {rows width : ℕ} (r : Fin (rows+1))
    (ps : List (QMAGate × Fin (width+1))) (h : ps.IsChain QMALabeledColumnNear) :
    (qmaRowLift r ps).IsChain QMAGridTagNear := by
  apply (List.isChain_map _).mpr
  exact h.imp (fun p q hh => by
    change r.val ≤ r.val+1 ∧ r.val ≤ r.val+1 ∧ p.2.val ≤ q.2.val+1 ∧ q.2.val ≤ p.2.val+1
    exact ⟨by omega,by omega,hh⟩)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint clock bits and each internal clock bit have a local time anchor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridTagNear_refl {rows width : ℕ} (p : QMAGate × QMAGridCell rows width) :
    QMAGridTagNear p p := by
  unfold QMAGridTagNear
  omega

theorem qmaGridTagNear_symm {rows width : ℕ} {p q : QMAGate × QMAGridCell rows width}
    (h : QMAGridTagNear p q) : QMAGridTagNear q p := ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

theorem qmaGridTagChain_near {rows width : ℕ} (ps : List (QMAGate × QMAGridCell rows width))
    (hp : ps.IsChain QMAGridTagNear) (i j : Fin ps.length)
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    QMAGridTagNear ps[i.val] ps[j.val] := by
  have h : i.val = j.val ∨ i.val+1 = j.val ∨ j.val+1 = i.val := by omega
  rcases h with h | h | h
  · have he : i = j := Fin.ext h
    subst j
    exact qmaGridTagNear_refl _
  · have hh := (List.isChain_iff_getElem.mp hp) i.val (by omega)
    simpa only [h] using hh
  · apply qmaGridTagNear_symm
    have hh := (List.isChain_iff_getElem.mp hp) j.val (by omega)
    simpa only [h] using hh

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit row/column coordinates for every physical computation qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridCoordinates (rows width : ℕ) (k : Fin (qmaGridWork rows width+1)) : QMAGridCell rows width :=
  (⟨k.val/(width+1),by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < width+1)).mpr
    have hk := k.isLt
    change k.val < width+rows*(width+1)+1 at hk
    nlinarith⟩,
   ⟨k.val%(width+1),Nat.mod_lt _ (by omega)⟩)

theorem qmaGridCoordinates_right (rows width : ℕ) (k : Fin (qmaGridWork rows width+1)) :
    qmaGridQubit rows width (qmaGridCoordinates rows width k).1 (qmaGridCoordinates rows width k).2 = k := by
  apply Fin.ext
  change k.val/(width+1)*(width+1)+k.val%(width+1) = k.val
  simpa only [Nat.mul_comm] using Nat.div_add_mod k.val (width+1)

theorem qmaGridCoordinates_left (rows width : ℕ) (r : Fin (rows+1)) (j : Fin (width+1)) :
    qmaGridCoordinates rows width (qmaGridQubit rows width r j) = (r,j) :=
  qmaGridQubit_injective rows width (qmaGridCoordinates_right _ _ _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTermTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign every actual history term to its clock time and enumerate by time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaHistoryTermTime (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c → Fin c.gates.length
  | .inl i => qmaBoundedClockTime _ hT i.val
  | .inr (.inl b) => if b = 0 then ⟨0,hT⟩ else qmaBoundedClockTime _ hT c.gates.length
  | .inr (.inr (.inl i)) => qmaBoundedClockTime _ hT (τ i).val
  | .inr (.inr (.inr (.inl _))) => qmaBoundedClockTime _ hT c.gates.length
  | .inr (.inr (.inr (.inr t))) => t

def qmaHistoryTermList (c : QMACircuit) : List (QMACircuitTerm c) :=
  List.ofFn (qmaHistoryTermIndex c).symm

theorem qmaHistoryTermList_mem (c : QMACircuit) (a : QMACircuitTerm c) :
    a ∈ qmaHistoryTermList c := by
  apply List.mem_ofFn.mpr
  exact ⟨qmaHistoryTermIndex c a,(qmaHistoryTermIndex c).symm_apply_apply a⟩

theorem qmaHistoryTermList_nodup (c : QMACircuit) : (qmaHistoryTermList c).Nodup :=
  List.nodup_ofFn.mpr (qmaHistoryTermIndex c).symm.injective

def qmaOrderedHistoryTerms (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : List (QMACircuitTerm c) :=
  qmaGroupByTime c.gates.length (qmaHistoryTermTime c hT τ) (qmaHistoryTermList c)

theorem qmaOrderedHistoryTerms_mem (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    a ∈ qmaOrderedHistoryTerms c hT τ :=
  (qmaGroupByTime_perm _ _ _).mem_iff.mpr (qmaHistoryTermList_mem c a)

theorem qmaOrderedHistoryTerms_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).Nodup :=
  qmaGroupByTime_nodup _ _ _ (qmaHistoryTermList_nodup c)

theorem qmaOrderedHistoryTerms_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).length = qmaHistoryReferenceWork c+1 := by
  rw [qmaOrderedHistoryTerms,qmaGroupByTime_length]
  exact List.length_ofFn

theorem qmaOrderedHistoryTerms_sorted (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).Pairwise
      (fun a b => qmaHistoryTermTime c hT τ a ≤ qmaHistoryTermTime c hT τ b) :=
  qmaGroupByTime_sorted _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSortedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coverage at every clock time bounds jumps in the ordered interaction list. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

variable {α : Type*}

theorem qmaOrderedHistoryTerms_cover (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : Fin c.gates.length) :
    ∃ a ∈ qmaOrderedHistoryTerms c hT τ, qmaHistoryTermTime c hT τ a = t := by
  refine ⟨.inr (.inr (.inr (.inr t))),qmaOrderedHistoryTerms_mem c hT τ _,rfl⟩

theorem qmaOrderedHistoryTerms_step (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i j : Fin (qmaOrderedHistoryTerms c hT τ).length) (hj : j.val = i.val+1) :
    (qmaHistoryTermTime c hT τ (qmaOrderedHistoryTerms c hT τ)[j.val]).val ≤
      (qmaHistoryTermTime c hT τ (qmaOrderedHistoryTerms c hT τ)[i.val]).val+1 :=
  qmaSortedTime_step _ _ (qmaOrderedHistoryTerms_sorted c hT τ)
    (qmaOrderedHistoryTerms_cover c hT τ) i j hj

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A consecutive reference label for the time-ordered actual interaction family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaOrderedTermEquiv (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Fin (qmaHistoryReferenceWork c+1) ≃ QMACircuitTerm c :=
  (finCongr (qmaOrderedHistoryTerms_length c hT τ).symm).trans
    (List.Nodup.getEquivOfForallMemList _ (qmaOrderedHistoryTerms_nodup c hT τ)
      (qmaOrderedHistoryTerms_mem c hT τ))

theorem qmaOrderedTermEquiv_get (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    qmaOrderedTermEquiv c hT τ i = (qmaOrderedHistoryTerms c hT τ)[i.val]'(by
      rw [qmaOrderedHistoryTerms_length]; exact i.isLt) := rfl

def qmaOrderedReferenceTime (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) : Fin c.gates.length :=
  qmaHistoryTermTime c hT τ (qmaOrderedTermEquiv c hT τ i)

theorem qmaOrderedReferenceTime_step (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (qmaHistoryReferenceWork c)) :
    (qmaOrderedReferenceTime c hT τ i.castSucc).val ≤
        (qmaOrderedReferenceTime c hT τ i.succ).val ∧
      (qmaOrderedReferenceTime c hT τ i.succ).val ≤
        (qmaOrderedReferenceTime c hT τ i.castSucc).val+1 := by
  let j : Fin (qmaOrderedHistoryTerms c hT τ).length :=
    i.castSucc.cast (qmaOrderedHistoryTerms_length c hT τ).symm
  let k : Fin (qmaOrderedHistoryTerms c hT τ).length :=
    i.succ.cast (qmaOrderedHistoryTerms_length c hT τ).symm
  have hjk : k.val = j.val+1 := rfl
  have hle := List.pairwise_iff_getElem.1 (qmaOrderedHistoryTerms_sorted c hT τ) _ _ j.isLt k.isLt
    (by change i.val < i.val+1; omega)
  have hstep := qmaOrderedHistoryTerms_step c hT τ j k hjk
  simp only [qmaOrderedReferenceTime,qmaOrderedTermEquiv_get]
  exact ⟨hle,hstep⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering actual history terms preserves the full-space reference gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaOrderedReferenceTerms (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) :=
  qmaDistributedTermMatrix c τ (qmaOrderedTermEquiv c hT τ i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All terms of the real reference model are localized in the actual clock grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridCellsNear_refl {rows width : ℕ} (p : QMAGridCell rows width) :
    QMAGridCellsNear p p := by
  unfold QMAGridCellsNear
  omega

theorem qmaGridCellsNear_symm {rows width : ℕ} {p q : QMAGridCell rows width}
    (h : QMAGridCellsNear p q) : QMAGridCellsNear q p :=
  ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridNeighbors
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring-cell geometry gives a constant interaction-degree bound. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaGridNeighbors {rows width : ℕ} (p : QMAGridCell rows width) :
    Finset (QMAGridCell rows width) := qmaLineNeighbors p.1 ×ˢ qmaLineNeighbors p.2

theorem qmaGridNeighbors_mem {rows width : ℕ} (p q : QMAGridCell rows width) :
    q ∈ qmaGridNeighbors p ↔ QMAGridCellsNear q p := by
  simp only [qmaGridNeighbors,Finset.mem_product,qmaLineNeighbors,Finset.mem_filter,
    Finset.mem_univ,true_and,QMAGridCellsNear]
  tauto

theorem qmaGridNeighbors_card {rows width : ℕ} (p : QMAGridCell rows width) :
    (qmaGridNeighbors p).card ≤ 9 := by
  rw [qmaGridNeighbors,Finset.card_product]
  exact (Nat.mul_le_mul (qmaLineNeighbors_card p.1) (qmaLineNeighbors_card p.2)).trans (by decide)

theorem qmaGrid_incidence_bound {Q E : Type*} [Fintype E] [DecidableEq Q]
    {rows width B : ℕ} (cell : Q → QMAGridCell rows width)
    (anchor : E → QMAGridCell rows width) (sites : E → Finset Q)
    (hlocal : ∀ a, ∀ q ∈ sites a, QMAGridCellsNear (cell q) (anchor a))
    (hdensity : ∀ p, (Finset.univ.filter (fun a => anchor a = p)).card ≤ B) (q : Q) :
    (Finset.univ.filter (fun a => q ∈ sites a)).card ≤ 9*B := by
  let near := qmaGridNeighbors (cell q)
  let fiber := fun p => Finset.univ.filter (fun a => anchor a = p)
  have hs : Finset.univ.filter (fun a => q ∈ sites a) ⊆ near.biUnion fiber := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨anchor a,?_,?_⟩
    · apply (qmaGridNeighbors_mem _ _).mpr
      exact qmaGridCellsNear_symm (hlocal a q (Finset.mem_filter.mp ha).2)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  calc
    _ ≤ (near.biUnion fiber).card := Finset.card_le_card hs
    _ ≤ ∑ p ∈ near, (fiber p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ near, B := Finset.sum_le_sum (fun p _ => hdensity p)
    _ = near.card*B := by simp
    _ ≤ 9*B := Nat.mul_le_mul_right B (qmaGridNeighbors_card _)


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two cancelling Hadamards remove the empty-circuit exception without changing acceptance. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaNonemptyCircuit (c : QMACircuit) : QMACircuit :=
  ⟨c.work,c.witness,c.gates++[.hadamard 0,.hadamard 0]⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual parsing of the verifier's prefix circuit encoding. Register sizes
are clipped to supplied unary bounds before later finite enumerations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram
open PrefixPrograms

def gateCode (g : QMAGate) : List Bool :=
  sumCode (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) (qmaGateEquiv g)

def circuitCode (c : QMACircuit) : List Bool :=
  prodCode unaryCode (prodCode unaryCode (listCode gateCode)) (qmaCircuitEquiv c)

theorem gate_length_pos (g : QMAGate) : 0 < (qmaGateCodec.encode g).length := by
  cases g <;> exact Nat.succ_pos _

def tailCodec := BinaryEncoding.pair BinaryEncoding.natural
  (BinaryEncoding.list qmaGateCodec)

def cap (x : ℕ × QMACircuit) : QMACircuit :=
  ⟨min x.1 x.2.work,min x.1 x.2.witness,x.2.gates⟩

theorem cap_eq (b : ℕ) (c : QMACircuit) (hw : c.work ≤ b) (hv : c.witness ≤ b) :
    cap (b,c)=c := by
  cases c
  simp only [cap,min_eq_right hw,min_eq_right hv]

theorem cap_eq_of_wellFormed (b : ℕ) (c : QMACircuit) (hc : c.WellFormed)
    (hw : c.work ≤ b) : cap (b,c)=c :=
  cap_eq b c hw (hc.1.trans hw)

noncomputable def workProgram : Procedure circuitCode unaryCode QMACircuit.work :=
  (Procedure.first unaryCode (prodCode unaryCode (listCode gateCode))).precompose qmaCircuitEquiv

noncomputable def tailProgram :
    Procedure circuitCode (prodCode unaryCode (listCode gateCode))
      (fun c => (c.witness,c.gates)) :=
  (Procedure.second unaryCode (prodCode unaryCode (listCode gateCode))).precompose qmaCircuitEquiv

noncomputable def witnessProgram : Procedure circuitCode unaryCode QMACircuit.witness :=
  (Procedure.first unaryCode (listCode gateCode)).comp tailProgram

noncomputable def gatesProgram : Procedure circuitCode (listCode gateCode) QMACircuit.gates :=
  (Procedure.second unaryCode (listCode gateCode)).comp tailProgram

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal constructors and coordinate selectors for the fixed H/T/CNOT
alphabet used by the nearest-neighbor circuit preprocessor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def gateTag : QMAGate → ℕ
  | .hadamard _ => 0
  | .phaseT _ => 1
  | .controlledNot _ _ => 2

def gateLeft : QMAGate → ℕ
  | .hadamard i => i
  | .phaseT i => i
  | .controlledNot i _ => i

def gateRight : QMAGate → ℕ
  | .hadamard i => i
  | .phaseT i => i
  | .controlledNot _ j => j

noncomputable def hadamardProgram : Procedure Nat.bits gateCode QMAGate.hadamard :=
  ((Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp
    (Procedure.sumLeft Nat.bits Nat.bits)).result (by intro i; rfl)

noncomputable def phaseProgram : Procedure Nat.bits gateCode QMAGate.phaseT :=
  ((Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp
    (Procedure.sumRight Nat.bits Nat.bits)).result (by intro i; rfl)

noncomputable def cnotProgram : Procedure (prodCode Nat.bits Nat.bits) gateCode
    (fun p => QMAGate.controlledNot p.1 p.2) :=
  (Procedure.sumRight (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).result
    (by intro p; rfl)

noncomputable def gateTagProgram : Procedure gateCode Nat.bits gateTag := by
  let h := Procedure.constant Nat.bits Nat.bits 0
  let t := Procedure.constant Nat.bits Nat.bits 1
  let c := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 2
  exact ((Procedure.casesSum (Procedure.casesSum h t) c).precompose qmaGateEquiv).congrFun
    (by intro g; cases g <;> rfl)

noncomputable def gateLeftProgram : Procedure gateCode Nat.bits gateLeft :=
  ((Procedure.casesSum (Procedure.casesSum (Procedure.identity Nat.bits) (Procedure.identity Nat.bits))
    (Procedure.first Nat.bits Nat.bits)).precompose qmaGateEquiv).congrFun
      (by intro g; cases g <;> rfl)

noncomputable def gateRightProgram : Procedure gateCode Nat.bits gateRight :=
  ((Procedure.casesSum (Procedure.casesSum (Procedure.identity Nat.bits) (Procedure.identity Nat.bits))
    (Procedure.second Nat.bits Nat.bits)).precompose qmaGateEquiv).congrFun
      (by intro g; cases g <;> rfl)

def swapList (a : ℕ) : List QMAGate :=
  [.controlledNot a (a+1),.controlledNot (a+1) a,.controlledNot a (a+1)]

theorem swapList_reverse (a : ℕ) : (swapList a).reverse=swapList a := rfl

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite list of physical exchanges, with no implicit many-body terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFourExchangeLeft (left right : κ → Fin n) (site : τ → Fin n) :
    QMAFourExchangeIndex n κ τ → Fin (n*4)
  | .inl (i,k) => finProdFinEquiv (i,qmaFourEdgeLeft k)
  | .inr (.inl (e,p,_)) => finProdFinEquiv (left e,p)
  | .inr (.inr (.inl (e,s,_))) => finProdFinEquiv ((if s = 0 then left e else right e),0)
  | .inr (.inr (.inr (e,_))) => finProdFinEquiv (site e,0)

def qmaFourExchangeRight (left right : κ → Fin n) (site : τ → Fin n) :
    QMAFourExchangeIndex n κ τ → Fin (n*4)
  | .inl (i,k) => finProdFinEquiv (i,qmaFourEdgeRight k)
  | .inr (.inl (e,_,q)) => finProdFinEquiv (right e,q)
  | .inr (.inr (.inl (e,s,k))) => finProdFinEquiv ((if s = 0 then left e else right e),qmaFieldEdgeRight k)
  | .inr (.inr (.inr (e,k))) => finProdFinEquiv (site e,qmaFieldEdgeRight k)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient rounding controls the full physical ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaExchangeMatrix (left right : κ → Fin n) (J : κ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e))+(constant:ℂ) • 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational sampling of the fixed algebraic constants in the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

def value (k : ℕ) (a : Fin 2) : ℚ :=
  if a = 0 then RationalSquareRoot.value (k,3)/384 else 3/4

def radicand (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ := (8/3)*|t| *value k a*value k b

def coupling (k l : ℕ) (a b : Fin 2) (t : ℚ) : ℚ :=
  RationalSquareRoot.value (l,radicand k a b t)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the algebraic four-spin coupling samples. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

def radialCode : (ℕ × ℚ) → List Bool := prodCode unaryCode ratCode

def couplingCode : (ℕ × (ℕ × ℚ)) → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

def calibrated (a b : Fin 2) (x : ℕ × ℚ) : ℚ := coupling (2*x.1+6) x.1 a b x.2

noncomputable opaque inputPrecisionProgram : Procedure radialCode unaryCode Prod.fst :=
  Procedure.first unaryCode ratCode

noncomputable opaque inputCoefficientProgram : Procedure radialCode ratCode Prod.snd :=
  Procedure.second unaryCode ratCode

noncomputable opaque doubledPrecisionProgram : Procedure radialCode unaryCode (fun x => 2*x.1) :=
  Procedure.unaryMul.comp ((Procedure.constant radialCode unaryCode 2).pair inputPrecisionProgram)

noncomputable opaque innerPrecisionProgram : Procedure radialCode unaryCode (fun x => 2*x.1+6) :=
  Procedure.unaryAdd.comp (doubledPrecisionProgram.pair (Procedure.constant radialCode unaryCode 6))

noncomputable opaque calibratedArgumentsProgram : Procedure radialCode couplingCode
    (fun x => (2*x.1+6,x.1,x.2)) :=
  innerPrecisionProgram.pair (inputPrecisionProgram.pair inputCoefficientProgram)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCountertermSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterms use only rational arithmetic and the fixed inverse-scale sample. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

def factor (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ := |t| *value k a*value k b
def counterA (k : ℕ) (_a b : Fin 2) (t : ℚ) : ℚ := |t| *value k b*shift b (decide (t ≤ 0))
def counterB (k : ℕ) (a _b : Fin 2) (t : ℚ) : ℚ := |t| *value k a*polarity t*shift a true

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFieldSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational evaluation of each internal physical field coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open Matrix

def fieldX (k : ℕ) (t : ℚ) : ℚ := 64*t*value k 0

def fieldValue (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) : ℚ :=
  if a = 0 then ![fieldX k t,-fieldX k t,0] e else ![0,0,-t/2] e

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOffsetSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error bounds for the sampled counterterm fields and their scalar shifts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

def offset (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ :=
  shiftValue a (counterA k a b t)+shiftValue b (counterB k a b t)-
    factor k a b t*shift a true*shift b (decide (t ≤ 0))

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational values for every edge of the actual physical exchange family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped Classical BigOperators

def crossValue (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) : ℚ :=
  r*calibrated a b (k,t)*(stencil a true p*stencil b (decide (t ≤ 0)) q)

variable {n : ℕ} {κ τ : Type*}

def weightValue (k : ℕ) (r : ℚ) (a b : κ → Fin 2) (t : κ → ℚ)
    (axis : τ → Fin 2) (weight : τ → ℚ) : QMAFourExchangeIndex n κ τ → ℚ
  | .inl _ => r^2
  | .inr (.inl (e,p,q)) => crossValue k r (a e) (b e) (t e) p q
  | .inr (.inr (.inl (e,s,j))) => if s = 0 then
      fieldValue k (a e) (counterA k (a e) (b e) (t e)) j else
      fieldValue k (b e) (counterB k (a e) (b e) (t e)) j
  | .inr (.inr (.inr (e,j))) => fieldValue k (axis e) (weight e) j

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation of each cross-block physical exchange coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

def crossCode : CrossInput → List Bool := prodCode (prodCode unaryCode ratCode) ratCode

noncomputable opaque crossParametersProgram : Procedure crossCode (prodCode unaryCode ratCode) Prod.fst :=
  Procedure.first _ _

noncomputable opaque crossPrecisionProgram : Procedure crossCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode ratCode).comp crossParametersProgram

noncomputable opaque crossScaleProgram : Procedure crossCode ratCode (fun x => x.1.2) :=
  (Procedure.second unaryCode ratCode).comp crossParametersProgram

noncomputable opaque crossCoefficientProgram : Procedure crossCode ratCode Prod.snd :=
  Procedure.second _ _

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawExchange
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw, rational finite-list instructions for the four-spin compiler. -/

namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

def rawCode : Raw → List Bool :=
  prodCode (prodCode Procedure.boolCode Procedure.boolCode)
    (prodCode (prodCode Nat.bits Nat.bits) (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode))

def environmentCode : Environment → List Bool := prodCode unaryCode ratCode
def inputCode : Input → List Bool := prodCode environmentCode rawCode

def field (k : ℕ) (i : ℕ) (a : Fin 2) (J : ℚ) : List Bond :=
  List.ofFn fun e : Fin 3 => (4*i,4*i+(qmaFieldEdgeRight e).val,fieldValue k a J e)

def cross (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ) : List Bond :=
  List.ofFn fun e : Fin 16 =>
    let pq := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e
    (4*i+pq.1.val,4*j+pq.2.val,crossValue k r a b J pq.1 pq.2)

def bonds (x : Input) : List Bond :=
  let k := x.1.1
  let r := x.1.2
  let t := x.2
  let i := t.2.1.1
  let j := t.2.1.2
  let a := axis t.2.2.1.1
  let b := axis t.2.2.1.2
  let J := t.2.2.2
  if t.1.1 then cross k r i j a b J ++
      field k i a (counterA k a b J) ++ field k j b (counterB k a b J)
  else if t.1.2 then field k i a J else []

def scalar (x : Input) : ℚ :=
  let t := x.2
  if t.1.1 then -offset x.1.1 (axis t.2.2.1.1) (axis t.2.2.1.2) t.2.2.2
  else if t.1.2 then -shiftValue (axis t.2.2.1.1) t.2.2.2 else t.2.2.2

theorem bonds_length (x : Input) : (bonds x).length ≤ 22 := by
  simp only [bonds]
  split <;> rename_i h
  · simp [cross,field]
  · split <;> simp [field]

end ContinuumCoulomb.QuantumRawExchange

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for fixed-size physical exchange instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable def selectAxis {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {flag : α → Bool} {f : Fin 2 → α → β} (test : Procedure ea Procedure.boolCode flag)
    (p : ∀ a, Procedure ea eb (f a)) :
    Procedure ea eb (fun x => f (axis (flag x)) x) :=
  (Procedure.conditional test (p 0) (p 1)).congrFun (by
    intro x
    cases flag x <;> simp [axis])

noncomputable opaque envProgram : Procedure inputCode environmentCode Prod.fst := Procedure.first _ _
noncomputable opaque rawProgram : Procedure inputCode rawCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp envProgram
noncomputable opaque flagsProgram : Procedure inputCode (prodCode Procedure.boolCode Procedure.boolCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp rawProgram
noncomputable opaque pairFlagProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp flagsProgram
noncomputable opaque fieldFlagProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1.2) :=
  (Procedure.second _ _).comp flagsProgram
noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode Nat.bits Nat.bits) (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp rawProgram
noncomputable opaque sitesProgram : Procedure inputCode (prodCode Nat.bits Nat.bits)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque leftProgram : Procedure inputCode Nat.bits (fun x => x.2.2.1.1) :=
  (Procedure.first _ _).comp sitesProgram
noncomputable opaque rightProgram : Procedure inputCode Nat.bits (fun x => x.2.2.1.2) :=
  (Procedure.second _ _).comp sitesProgram
noncomputable opaque axesWeightProgram : Procedure inputCode
    (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque axesProgram : Procedure inputCode (prodCode Procedure.boolCode Procedure.boolCode)
    (fun x => x.2.2.2.1) := (Procedure.first _ _).comp axesWeightProgram
noncomputable opaque axisLeftProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1.1) :=
  (Procedure.first _ _).comp axesProgram
noncomputable opaque axisRightProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1.2) :=
  (Procedure.second _ _).comp axesProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp axesWeightProgram
noncomputable opaque radialProgram : Procedure inputCode radialCode (fun x => (x.1.1,x.2.2.2.2)) :=
  precisionProgram.pair weightProgram
noncomputable opaque crossInputProgram : Procedure inputCode crossCode (fun x => (x.1,x.2.2.2.2)) :=
  envProgram.pair weightProgram

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawFamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite rational edge list and offset are computed in polynomial time. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

theorem flatten_code_bound {α : Type} (ea : α → List Bool) (xs : List (List α)) :
    (listCode ea xs.flatten).length ≤ (listCode (listCode ea) xs).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    have h := listCode_length_append ea x xs.flatten
    simp only [List.flatten_cons,listCode_length_cons]
    omega

def familyCode : FamilyInput → List Bool := prodCode environmentCode (listCode rawCode)

def termBondsList (x : FamilyInput) : List Bond := (x.2.map (fun t => bonds (x.1,t))).flatten
def termScalarList (x : FamilyInput) : ℚ := (x.2.map (fun t => scalar (x.1,t))).sum

def penaltyCode : PenaltyInput → List Bool := prodCode unaryCode ratCode

def penaltyBlock (r : ℚ) (i : ℕ) : List Bond :=
  List.ofFn fun e : Fin 6 => (4*i+(qmaFourEdgeLeft e).val,
    4*i+(qmaFourEdgeRight e).val,r^2)

def penalty (n : ℕ) (r : ℚ) : List Bond := ((List.range n).map (penaltyBlock r)).flatten

noncomputable opaque penaltyIndexProgram : Procedure penaltyCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first _ _)
noncomputable opaque penaltyScaleProgram : Procedure penaltyCode ratCode Prod.snd := Procedure.second _ _
def fullCode : FullInput → List Bool := prodCode unaryCode familyCode

def fullBonds (x : FullInput) : List Bond := penalty x.1 x.2.1.2 ++ termBondsList x.2
def fullScalar (x : FullInput) : ℚ := x.2.1.2^2*(x.1*6)+termScalarList x.2

noncomputable opaque fullCountProgram : Procedure fullCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque fullFamilyProgram : Procedure fullCode familyCode Prod.snd := Procedure.second _ _
noncomputable opaque fullScaleProgram : Procedure fullCode ratCode (fun x => x.2.1.2) :=
  (Procedure.second unaryCode ratCode).comp ((Procedure.first _ _).comp fullFamilyProgram)
noncomputable opaque fullPenaltyInputProgram : Procedure fullCode penaltyCode (fun x => (x.1,x.2.1.2)) :=
  fullCountProgram.pair fullScaleProgram
noncomputable opaque fullCountRatProgram : Procedure fullCode ratCode (fun x => (x.1:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp fullCountProgram)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAdjacentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive adjacent-CNOT construction is a literal finite prefix,
one central gate, and its reversed prefix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def swapPrefix (a d : ℕ) : List QMAGate :=
  ((List.range d).map (fun k => swapList (a+k))).flatten

theorem swapPrefix_succ (a d : ℕ) :
    swapPrefix a (d+1)=swapList a++swapPrefix (a+1) d := by
  have hf : (fun k => swapList (a+Nat.succ k))=(fun k => swapList (a+1+k)) := by
    funext k
    congr 1
    omega
  simp only [swapPrefix,List.range_succ_eq_map,List.map_cons,List.flatten_cons,
    Nat.add_zero,List.map_map,Function.comp_def]
  rw [hf]

def adjacentList (a d : ℕ) (b : Bool) : List QMAGate :=
  swapPrefix a d++[qmaOrderedCnot (a+d) (a+d+1) b]++(swapPrefix a d).reverse

theorem adjacentList_eq (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    qmaAdjacentCnot work a d h b=adjacentList a d b := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    change swapList a++qmaAdjacentCnot work (a+1) d _ b++swapList a=adjacentList a (d+1) b
    rw [ih]
    unfold adjacentList
    rw [swapPrefix_succ,List.reverse_append,swapList_reverse]
    have ha : a+1+d=a+(d+1) := by omega
    rw [ha]
    simp only [List.append_assoc]

noncomputable def orderedCnotProgram :
    Procedure (prodCode (prodCode Nat.bits Nat.bits) Procedure.boolCode) gateCode
      (fun x => qmaOrderedCnot x.1.1 x.1.2 x.2) := by
  let p := Procedure.first (prodCode Nat.bits Nat.bits) Procedure.boolCode
  let b := Procedure.second (prodCode Nat.bits Nat.bits) Procedure.boolCode
  let forward := cnotProgram.comp p
  let backward := cnotProgram.comp
    (((Procedure.second Nat.bits Nat.bits).comp p).pair
      ((Procedure.first Nat.bits Nat.bits).comp p))
  exact (Procedure.conditional b forward backward).congrFun (by intro x; rfl)

def adjacentInputCode : AdjacentInput → List Bool :=
  prodCode unaryCode (prodCode Nat.bits Procedure.boolCode)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar arithmetic for the H,T,CNOT history compiler.  A real
scalar is a+b/sqrt(2); a complex scalar consists of two such pairs.  The
representation is rational data throughout, including multiplication. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

def sample (k : ℕ) (x : RealScalar) : ℚ :=
  x.1+x.2*RationalSquareRoot.value (k,1/2)

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) : Scalar :=
  match g with
  | .hadamard i => finiteProduct (fun k =>
      if k = qmaQubit work i then hadamard (s k) (t k) else identity (s k) (t k))
  | .phaseT i => finiteProduct (fun k =>
      if k = qmaQubit work i then phaseT (s k) (t k) else identity (s k) (t k))
  | .controlledNot i j => rat
      (if s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0)

def delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) : Scalar :=
  if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then
    sub (identity s (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) r))
      (mul (identity (s ∘ Sum.inl) (r ∘ Sum.inl))
        (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr)))
  else rat 0

def lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (s t : ι → Fin 2) : Scalar :=
  mul (A (fun i => s i.val) (fun i => t i.val))
    (identity (fun i : {i // i ∉ S} => s i.val) (fun i => t i.val))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGraphDegree
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence counts for the actual ordinary-spin routing graphs. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

theorem qmaParallelGraph_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (v : Fin n) :
    qmaGraphDegree (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member) (old n r v) =
      qmaGraphDegree left right v + ∑ e, ∑ a, if site e a = v then 1 else 0 := by
  have ho := old_injective n r
  have hf (e : Fin r) (b : Fin 2) : fresh n r e b ≠ old n r v := (old_ne_fresh n r v e b).symm
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp [qmaParallelGraphLeft,qmaParallelGraphRight,ho.eq_iff,hf]

theorem qmaParallelGraph_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member) (fresh n r e b) =
      1 + ∑ a, if member e a = b then 1 else 0 := by
  have hf := fresh_injective n r
  have ho (v : Fin n) : old n r v ≠ fresh n r e b := old_ne_fresh n r v e b
  have heq (f : Fin r) (a : Fin 2) : fresh n r f a = fresh n r e b ↔ f = e ∧ a = b := by
    constructor
    · intro h
      have hh : (f,a) = (e,b) := hf h
      exact Prod.mk.inj hh
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [qmaParallelGraphLeft,qmaParallelGraphRight,ho,false_or,heq,ite_false, if_false,
    Finset.sum_const_zero,zero_add]
  have hc : (∑ f : Fin r, if f = e ∧ (0:Fin 2) = b ∨ f = e ∧ (1:Fin 2) = b then 1 else 0) = 1 := by
    fin_cases b <;> simp
  rw [hc]
  apply congrArg (1+·)
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [hfe]
  · simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAnchorDensity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded vertex density and degree bound the number of nearby edge anchors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaNearVertexCard_bound {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A) (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p)).card ≤ 9*A := by
  let fiber := fun q => Finset.univ.filter (fun v => cell v = q)
  have heq : Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p) =
      (qmaGridNeighbors p).biUnion fiber := by
    ext v
    simp [fiber]
  rw [heq]
  calc
    _ ≤ ∑ q ∈ qmaGridNeighbors p, (fiber q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ qmaGridNeighbors p, A := Finset.sum_le_sum (fun q _ => hc q)
    _ = (qmaGridNeighbors p).card*A := by simp
    _ ≤ 9*A := Nat.mul_le_mul_right A (qmaGridNeighbors_card p)

theorem qmaLeftIncidence_le_degree {ν : Type*} [Fintype ν] {n : ℕ}
    (left right : ν → Fin n) (v : Fin n) :
    (Finset.univ.filter (fun e => left e = v)).card ≤ qmaGraphDegree left right v := by
  have heq : (Finset.univ.filter (fun e => left e = v)).card =
      (∑ e, if left e = v then 1 else 0 : ℕ) := by simp
  rw [heq]
  apply Finset.sum_le_sum
  intro e _
  by_cases h : left e = v
  · simp [h]
  · simp [h]

theorem qmaAnchor_density {ν : Type*} [Fintype ν] {n rows width A D : ℕ}
    (left right : ν → Fin n) (cell : Fin n → QMAGridCell rows width)
    (anchor : ν → QMAGridCell rows width)
    (hnear : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e))
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A)
    (hd : ∀ v, qmaGraphDegree left right v ≤ D) (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e => anchor e = p)).card ≤ 9*A*D := by
  let near := Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p)
  let fiber := fun v => Finset.univ.filter (fun e => left e = v)
  have hsub : Finset.univ.filter (fun e => anchor e = p) ⊆ near.biUnion fiber := by
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    apply Finset.mem_biUnion.mpr
    refine ⟨left e,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,(qmaGridNeighbors_mem p _).mpr ?_⟩
      simpa only [hp] using hnear e
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  calc
    _ ≤ (near.biUnion fiber).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ near, (fiber v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ near, D := Finset.sum_le_sum (fun v _ =>
      (qmaLeftIncidence_le_degree left right v).trans (hd v))
    _ = near.card*D := by simp
    _ ≤ (9*A)*D := Nat.mul_le_mul_right D (qmaNearVertexCard_bound cell hc p)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.MinUncut_Machines_Runtime
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

variable [DecidableEq K] [DecidableEq E]

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end MinUncutGames.Foundations.Complexity.MachineEmbedding

namespace MinUncutGames.Foundations.Complexity.MachineComposition

def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

end MinUncutGames.Foundations.Complexity.MachineComposition

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBitTransfer
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a bit-coded word between the verifier machine and the Boolean
prefix tapes. Only the bit register is added to the finite control. -/

namespace ContinuumCoulomb.QuantumBitTransfer
open Turing
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

theorem update_src (src dst : K) (hne : src ≠ dst)
    (base : ∀ k, List (Γ k)) (xs ys : List (Γ src)) (zs : List (Γ dst)) :
    Function.update (tapesAt src dst base xs zs) src ys = tapesAt src dst base ys zs := by
  funext k
  by_cases hs : k=src
  · subst k
    simp [tapesAt,hne]
  · by_cases hd : k=dst
    · subst k
      simp [tapesAt,Ne.symm hne]
    · simp [tapesAt,hs,hd]

theorem update_dst (src dst : K) (base : ∀ k, List (Γ k))
    (xs : List (Γ src)) (ys zs : List (Γ dst)) :
    Function.update (tapesAt src dst base xs ys) dst zs = tapesAt src dst base xs zs := by
  funext k
  by_cases h : k=dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt,h]

theorem step_empty (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (ys : List (Γ dst)) (state : σ) (r : Option Bool) :
    TM2.step program ⟨some label,(state,r),tapesAt src dst base [] ys⟩=
      some ⟨exit,(state,none),tapesAt src dst base [] ys⟩ := by
  change some (TM2.stepAux (program label) _ _)=_
  rw [hl]
  cases exit <;> simp [loop,TM2.stepAux,tapesAt_src,hne,update_src]

theorem step_cons (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (x : Γ src) (xs : List (Γ src)) (ys : List (Γ dst))
    (state : σ) (r : Option Bool) :
    TM2.step program ⟨some label,(state,r),tapesAt src dst base (x::xs) ys⟩=
      some ⟨some label,(state,some (read x)),
        tapesAt src dst base xs (write (read x)::ys)⟩ := by
  change some (TM2.stepAux (program label) _ _)=_
  rw [hl]
  simp [loop,TM2.stepAux,tapesAt_src,tapesAt_dst,hne,update_src,update_dst]

theorem transfer_steps (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (xs : List (Γ src)) (ys : List (Γ dst))
    (state : σ) (r : Option Bool) :
    (fun c => c.bind (TM2.step program))^[xs.length+1]
      (some ⟨some label,(state,r),tapesAt src dst base xs ys⟩)=
      some ⟨exit,(state,none),
        tapesAt src dst base [] (xs.reverse.map (write ∘ read)++ys)⟩ := by
  induction xs generalizing ys r with
  | nil =>
    simpa only [List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some,
      List.reverse_nil,List.map_nil,List.nil_append] using
      step_empty src dst hne read write label exit program hl base ys state r
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (fun c => c.bind (TM2.step program))^[xs.length+1]
      (TM2.step program ⟨some label,(state,r),tapesAt src dst base (x::xs) ys⟩)=_
    rw [step_cons src dst hne read write label exit program hl,ih]
    simp only [List.reverse_cons,List.map_append,List.map_singleton,
      List.append_assoc,List.singleton_append,Function.comp_apply]

def transfer (src dst : K) (hne : src ≠ dst)
    (read : Γ src → Bool) (write : Bool → Γ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option Bool))
    (hl : program label=loop src dst read write label exit)
    (base : ∀ k, List (Γ k)) (state : σ) (r : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label,(state,r),base⟩
      (some ⟨exit,(state,none),tapesAt src dst base []
        ((base src).reverse.map (write ∘ read)++base dst)⟩) ((base src).length+1) where
  steps := (base src).length+1
  evals_in_steps := by
    change (fun c : Option (TM2.Cfg Γ Λ (σ × Option Bool)) => c.bind (TM2.step program))^[
      (base src).length+1] (some ⟨some label,(state,r),base⟩)=_
    simpa only [tapesAt_self] using
      transfer_steps src dst hne read write label exit program hl base (base src) (base dst) state r
  steps_le_m := le_rfl

end ContinuumCoulomb.QuantumBitTransfer

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support of the two-segment lattice route. -/

namespace ContinuumCoulomb

theorem qmaAxisWalk_at_between {a b x : ℕ} (h : qmaBetween a b x) :
    qmaAxisWalk a b (Nat.dist a x) = x ∧ Nat.dist a x ≤ Nat.dist a b := by
  unfold qmaBetween qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaManhattanSupport_point {p q z : ℕ × ℕ} (hz : qmaManhattanSupport p q z) :
    ∃ k, k ≤ qmaManhattanLength p q ∧ qmaManhattanPoint p q k = z := by
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · obtain ⟨he,hk⟩ := qmaAxisWalk_at_between hx
    refine ⟨Nat.dist p.1 z.1,by unfold qmaManhattanLength; omega,?_⟩
    simp only [qmaManhattanPoint,ite_eq_left hk,he]
    exact Prod.ext rfl hy.symm
  · obtain ⟨he,hk⟩ := qmaAxisWalk_at_between hy
    refine ⟨Nat.dist p.1 q.1+Nat.dist p.2 z.2,by unfold qmaManhattanLength; omega,?_⟩
    by_cases hzero : Nat.dist p.2 z.2 = 0
    · have hyz := Nat.eq_of_dist_eq_zero hzero
      simp only [qmaManhattanPoint,hzero,add_zero,le_refl,ite_true, if_true,qmaAxisWalk_last]
      exact Prod.ext hx.symm hyz
    · have hn : ¬Nat.dist p.1 q.1+Nat.dist p.2 z.2 ≤ Nat.dist p.1 q.1 := by omega
      simp only [qmaManhattanPoint,ite_eq_right hn,Nat.add_sub_cancel_left,he]
      exact Prod.ext hx.symm rfl

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedDogleg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two direct buffered endpoint arms, including their one-step joins. -/

namespace ContinuumCoulomb

theorem qmaBufferedDogleg_last (u v : ℕ) :
    qmaBufferedDoglegPoint u v (qmaBufferedDoglegLength u v) = (u,u) := by
  unfold qmaBufferedDoglegPoint qmaBufferedDoglegLength
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedDetour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit western detour for the third buffered endpoint arm. -/

namespace ContinuumCoulomb

theorem qmaBufferedDetour_last {u v : ℕ} (hu : 24 ≤ u) : qmaBufferedDetourPoint u v (u+v+1) = (u,u) := by
  unfold qmaBufferedDetourPoint
  by_cases h : u+v+1 ≤ 8
  · omega
  · rw [ite_eq_right h,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite unit-step route has a simple subroute with no larger length. -/

namespace ContinuumCoulomb

def qmaGridWalk (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    qmaSquareGrid.Walk (p 0) (p L) :=
  match L with
  | 0 => .nil
  | L+1 => .cons (hstep 0 (by omega))
      (qmaGridWalk (fun k => p (k+1)) L (fun k hk => hstep (k+1) (by omega)))

theorem qmaGridWalk_length (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaGridWalk p L hstep).length = L := by
  induction L generalizing p with
  | zero => rfl
  | succ L ih => simp only [qmaGridWalk,SimpleGraph.Walk.length_cons,ih]

theorem qmaGridWalk_support (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) {z : ℕ × ℕ}
    (hz : z ∈ (qmaGridWalk p L hstep).support) : ∃ k ≤ L, p k = z := by
  induction L generalizing p with
  | zero =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    exact ⟨0,le_rfl,hz.symm⟩
  | succ L ih =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with hz | hz
    · exact ⟨0,by omega,hz.symm⟩
    · obtain ⟨k,hk,he⟩ := ih (fun k => p (k+1)) _ hz
      exact ⟨k+1,by omega,he⟩


theorem qmaGridPath_getVert_step {u v : ℕ × ℕ} (P : qmaSquareGrid.Path u v)
    (i : Fin P.val.length) :
    qmaSquareGrid.Adj (P.val.getVert i.castSucc.val) (P.val.getVert i.succ.val) :=
  P.val.adj_getVert_succ i.isLt

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-walk interface for all three buffered endpoint arms. -/

namespace ContinuumCoulomb

@[simp] theorem qmaBufferedArm_last (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedArmPoint c side a (qmaBufferedArmLength c side a) =
      (qmaBufferedPort c a,qmaBufferedPort c a) := by
  have hu : 24 ≤ qmaBufferedPort c 2 := by unfold qmaBufferedPort; omega
  fin_cases a <;> simp [qmaBufferedArmPoint,qmaBufferedArmLength,
    qmaBufferedDogleg_last,qmaBufferedDetour_last hu]

theorem qmaBufferedArm_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (k : ℕ) :
    qmaBufferedFanoutSupport c side a (qmaBufferedArmPoint c side a k) := by
  have hu : 24 ≤ qmaBufferedPort c 1 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 1 := by
    have h := qmaBufferedOffset_bounds c side 1
    omega
  fin_cases a
  · exact qmaBufferedFanout_direct_support c side k
  · have h := qmaBufferedDogleg_support hu hv k
    simpa [qmaBufferedFanoutSupport,qmaBufferedDoglegSupport,qmaBufferedArmPoint] using h
  · exact qmaBufferedFanout_detour_support c side k

theorem qmaBufferedArm_step (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3)
    (k : ℕ) (hk : k < qmaBufferedArmLength c side a) :
    qmaSquareGrid.Adj (qmaBufferedArmPoint c side a k) (qmaBufferedArmPoint c side a (k+1)) := by
  have hu : 24 ≤ qmaBufferedPort c a := by unfold qmaBufferedPort; omega
  have hc := qmaBufferedOffset_bounds c side a
  have hv : 23 ≤ qmaBufferedOffset c side a := by omega
  have hn := qmaBufferedOffset_ne c side a
  fin_cases a
  · simpa [qmaBufferedArmPoint,qmaSquareGrid] using
      qmaBufferedDogleg_step hu hv hc hn k hk
  · simpa [qmaBufferedArmPoint,qmaSquareGrid,Nat.add_comm] using
      qmaBufferedDogleg_step hu hv hc hn k hk
  · simpa [qmaBufferedArmPoint,qmaSquareGrid] using
      qmaBufferedDetour_step hu hv hc hn k hk

theorem qmaBufferedArm_length_bound (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    {C : ℕ} (hC : ∀ a, c a < C) (a : Fin 3) : qmaBufferedArmLength c side a ≤ 16*(C+3)+2 := by
  have hu : qmaBufferedPort c a ≤ 8*(C+3) := by
    have h := hC a
    unfold qmaBufferedPort
    omega
  have hc := qmaBufferedOffset_bounds c side a
  unfold qmaBufferedArmLength
  split_ifs
  · omega
  · exact (qmaBufferedDogleg_length_bound hu hc.2).trans (by omega)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the lattice route length and each route point. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

def pairCode : Pair → List Bool := prodCode Nat.bits Nat.bits
abbrev AxisInput := Pair × ℕ
def axisCode : AxisInput → List Bool := prodCode pairCode Nat.bits

noncomputable opaque axisPairProgram : Procedure axisCode pairCode Prod.fst := Procedure.first _ _
noncomputable opaque axisStartProgram : Procedure axisCode Nat.bits (fun x => x.1.1) :=
  (Procedure.first _ _).comp axisPairProgram
noncomputable opaque axisEndProgram : Procedure axisCode Nat.bits (fun x => x.1.2) :=
  (Procedure.second _ _).comp axisPairProgram
noncomputable opaque axisCursorProgram : Procedure axisCode Nat.bits Prod.snd := Procedure.second _ _

abbrev RouteInput := (Pair × Pair) × ℕ
def routeCode : RouteInput → List Bool := prodCode (prodCode pairCode pairCode) Nat.bits
noncomputable opaque endsProgram : Procedure routeCode (prodCode pairCode pairCode) Prod.fst :=
  Procedure.first _ _
noncomputable opaque startProgram : Procedure routeCode pairCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp endsProgram
noncomputable opaque endProgram : Procedure routeCode pairCode (fun x => x.1.2) :=
  (Procedure.second _ _).comp endsProgram
noncomputable opaque cursorProgram : Procedure routeCode Nat.bits Prod.snd := Procedure.second _ _
noncomputable opaque startXProgram : Procedure routeCode Nat.bits (fun x => x.1.1.1) :=
  (Procedure.first _ _).comp startProgram
noncomputable opaque startYProgram : Procedure routeCode Nat.bits (fun x => x.1.1.2) :=
  (Procedure.second _ _).comp startProgram
noncomputable opaque endXProgram : Procedure routeCode Nat.bits (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp endProgram
noncomputable opaque endYProgram : Procedure routeCode Nat.bits (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp endProgram

end ContinuumCoulomb.QuantumRouteCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArmProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def sub {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x-g x) := Procedure.binarySub.comp (p.pair q)
noncomputable def le {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Procedure.boolCode (fun x => decide (f x ≤ g x)) :=
  Procedure.binaryLe.comp (p.pair q)

noncomputable def u : Procedure axisCode Nat.bits (fun x => x.1.1) := axisStartProgram
noncomputable def v : Procedure axisCode Nat.bits (fun x => x.1.2) := axisEndProgram
noncomputable def k : Procedure axisCode Nat.bits (fun x => x.2) := axisCursorProgram
noncomputable def c (n : ℕ) : Procedure axisCode Nat.bits (fun _ => n) :=
  Procedure.constant _ _ n

def point (a : Fin 3) (color j : ℕ) : Pair :=
  let u := 8*(color+3)
  if a = 0 then qmaBufferedDoglegPoint u (u-1) j
  else if a = 1 then (qmaBufferedDoglegPoint u (u-1) j).swap
  else qmaBufferedDetourPoint u (u-1) j

noncomputable def lengthProgram (a : Fin 3) : Procedure unaryCode unaryCode (length a) :=
  (Procedure.unaryAdd.comp
    ((Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 16).pair
      (Procedure.identity unaryCode))).pair
        (Procedure.constant unaryCode unaryCode (if a=2 then 48 else 14)))).congrFun (by
          intro color
          simp only [Function.comp_apply,id_eq,length]
          split_ifs <;> rfl)

end ContinuumCoulomb.QuantumBufferedArmProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFineRoute
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite lattice routes stay in the neighboring coarse cells of their endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaFineRoute_local {rows width A : ℕ} (hA : 0 < A)
    (p q : QMAFineGrid rows width A) (a : QMAGridCell rows width)
    (hp : QMAGridCellsNear (qmaFineGridCell hA p) a)
    (hq : QMAGridCellsNear (qmaFineGridCell hA q) a)
    (k : Fin (qmaManhattanLength (qmaFineGridNat p) (qmaFineGridNat q)+1)) :
    QMAGridCellsNear (qmaFineGridCell hA (qmaFineRoute p q k)) a := by
  have hb := qmaManhattanPoint_bounds (qmaFineGridNat p) (qmaFineGridNat q) k.val (by omega)
  have hd := qmaQuotient_bounds p.1.val q.1.val
    (qmaManhattanPoint (qmaFineGridNat p) (qmaFineGridNat q) k.val).1 A hb.1 hb.2.1
  dsimp [QMAGridCellsNear,qmaFineGridCell] at hp hq ⊢
  change _/A ≤ _ ∧ _ ≤ _/A+1 ∧ _ ≤ _ ∧ _ ≤ _
  dsimp only [qmaFineRoute]
  dsimp [qmaFineGridNat] at hb hd ⊢
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteCongestion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Routing whole interactions retains constant congestion and the same color schedule. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaFineRouteSites {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    Finset (QMAFineGrid rows width A) := Finset.univ.image (qmaFineRoute p q)

theorem qmaFineRouteSites_local {rows width A : ℕ} (hA : 0 < A)
    (p q : QMAFineGrid rows width A) (a : QMAGridCell rows width)
    (hp : QMAGridCellsNear (qmaFineGridCell hA p) a)
    (hq : QMAGridCellsNear (qmaFineGridCell hA q) a)
    (z : QMAFineGrid rows width A) (hz : z ∈ qmaFineRouteSites p q) :
    QMAGridCellsNear (qmaFineGridCell hA z) a := by
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
  exact qmaFineRoute_local hA p q a hp hq k

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-spin encoding preserves neighboring-cell geometry and constant density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {n rows width : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFourBlockCell (cell : Fin n → QMAGridCell rows width) (i : Fin (n*4)) :
    QMAGridCell rows width := cell (finProdFinEquiv.symm i).1

theorem qmaFourBlockCell_density (cell : Fin n → QMAGridCell rows width) {A : ℕ}
    (hcell : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun i => qmaFourBlockCell cell i = p)).card ≤ 4*A := by
  have he : (Finset.univ.filter (fun i => qmaFourBlockCell cell i = p)).card =
      (Finset.univ.filter (fun x : Fin n × Fin 4 => cell x.1 = p)).card := by
    apply Finset.card_equiv finProdFinEquiv.symm
    intro i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  rw [he,qmaProdFilter_card (α := Fin n) 4 (fun i => cell i = p)]
  exact Nat.mul_le_mul_left 4 (hcell p)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rational four-spin simulator retains bounded spatial density. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

attribute [instance] QMASpatialExchangeModel.termFinite

def QMASpatialExchangeModel.energy {A B : ℕ} (M : QMASpatialExchangeModel A B) : ℝ :=
  MediatorGraph.normalizedBottom (qmaExchangeMatrix M.left M.right (fun e => (M.weight e:ℝ)) M.constant)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeRoutes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit constant-length routes for the actual bounded-density exchange model. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def routeLeft (e : M.Term) : QMAFineGrid M.rows M.width A := M.qubitSlots.site (M.left e)
def routeRight (e : M.Term) : QMAFineGrid M.rows M.width A := M.qubitSlots.site (M.right e)
def routeLength (e : M.Term) : ℕ := qmaManhattanLength (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e))
def routeSites (e : M.Term) : Finset (QMAFineGrid M.rows M.width A) := qmaFineRouteSites (M.routeLeft e) (M.routeRight e)

theorem routeLength_bound (e : M.Term) : M.routeLength e ≤ 3*A+2 :=
  M.qubitSlots.route_length _ _ (M.anchor e) (M.geometry e).1 (M.geometry e).2

theorem route_local (hA : 0 < A) (e : M.Term) :
    QMAGridCellsNear (qmaFineGridCell hA (M.routeLeft e)) (M.anchor e) ∧
    QMAGridCellsNear (qmaFineGridCell hA (M.routeRight e)) (M.anchor e) := by
  simpa only [routeLeft,routeRight,QMACellSlots.site_cell] using M.geometry e

theorem routes_of_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.termSlots.color e = M.termSlots.color f) :
    Disjoint (M.routeSites e) (M.routeSites f) :=
  by
    apply M.termSlots.color_disjoint (qmaFineGridCell hA) M.routeSites _ hef hcolor
    intro e z hz
    exact qmaFineRouteSites_local hA _ _ _ (M.route_local hA e).1 (M.route_local hA e).2 z hz

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeLanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated lanes for the actual spatial exchange family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaFineGridNat_injective {rows width A : ℕ} :
    Function.Injective (@qmaFineGridNat rows width A) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem qmaLane_length {C : ℕ} (c : Fin C) (p q : ℕ × ℕ) :
    qmaManhattanLength (qmaLanePoint c p) (qmaLanePoint c q) = C*qmaManhattanLength p q := by
  simp only [qmaManhattanLength,qmaLanePoint,Nat.dist_add_add_right,Nat.dist_mul_left,Nat.mul_add]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def laneColor (e : M.Term) : Fin (9*B) := qmaGridColorEquiv B (M.termSlots.color e)
def laneSupport (e : M.Term) (z : ℕ × ℕ) : Prop :=
  qmaLaneSupport (M.laneColor e) (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointPorts
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The at-most-three incident edges are assigned distinct, ordered buffered ports. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaPaddedPortSlot_increasing {C : ℕ} (s : Finset (Fin C)) :
    StrictMono (qmaPaddedPortSlot s) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  by_cases ha : a.val < s.card <;> by_cases hb : b.val < s.card
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_left ha,dite_eq_left hb,Fin.val_castAdd]
    exact (s.orderEmbOfFin rfl).strictMono hab'
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_left ha,dite_eq_right hb,Fin.val_castAdd]
    have hu := (s.orderEmbOfFin rfl ⟨a.val,ha⟩).isLt
    omega
  · omega
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_right ha,dite_eq_right hb]
    omega

def qmaCanonicalSortedPorts {κ : Type} [Fintype κ] {C : ℕ} (color : κ → Fin C)
    (hc : Fintype.card κ ≤ 3) : QMASortedPorts C color := by
  let s := Finset.univ.image color
  have hs : s.card ≤ 3 := (Finset.card_image_le).trans (by simpa using hc)
  let iso := s.orderIsoOfFin rfl
  let rank := fun e => iso.symm ⟨color e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩
  let assign := fun e => (⟨(rank e).val,lt_of_lt_of_le (rank e).isLt hs⟩ : Fin 3)
  refine ⟨qmaPaddedPortSlot s,qmaPaddedPortSlot_increasing s,assign,?_⟩
  intro e
  have hi : (assign e).val < s.card := (rank e).isLt
  simp only [qmaPaddedPortSlot,dite_eq_left hi]
  apply congrArg (Fin.castAdd 3)
  exact congrArg Subtype.val (iso.apply_symm_apply _)


namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

abbrev Incident (v : Fin M.n) := {e : M.Term // M.left e = v ∨ M.right e = v}

theorem incident_card (v : Fin M.n) :
    Fintype.card (M.Incident v) = qmaGraphDegree M.left M.right v := by
  rw [Fintype.card_subtype]
  symm
  exact Finset.sum_boole _ _

theorem incident_lane_support (v : Fin M.n) (e : M.Incident v) :
    M.laneSupport e.val (qmaLanePoint (M.laneColor e.val)
      (qmaFineGridNat (M.qubitSlots.site v))) := by
  rcases e.property with h | h
  · left
    dsimp [laneSupport,qmaLaneSupport,routeLeft,routeRight]
    rw [h]
    exact ⟨rfl,min_le_left _ _,le_max_left _ _⟩
  · right
    dsimp [laneSupport,qmaLaneSupport,routeLeft,routeRight]
    rw [h]
    exact ⟨rfl,min_le_right _ _,le_max_right _ _⟩

def endpointPorts (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) :
    QMASortedPorts (9*B) (fun e : M.Incident v => M.laneColor e.val) :=
  qmaCanonicalSortedPorts _ ((M.incident_card v).trans_le (hd v))

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedLanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eightfold lane spacing leaves room for the buffered endpoint arms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def spacedColor (e : M.Term) : Fin (8*(9*B+9)) :=
  qmaSpacedLaneColor ((M.laneColor e).castAdd 3)

def spacedSupport (e : M.Term) (z : ℕ × ℕ) : Prop :=
  qmaLaneSupport (M.spacedColor e) (qmaFineGridNat (M.routeLeft e))
    (qmaFineGridNat (M.routeRight e)) z

theorem spacedColor_eq {e f : M.Term} (h : M.spacedColor e = M.spacedColor f) :
    M.laneColor e = M.laneColor f := by
  have hc := qmaSpacedLaneColor_injective (9*B+3) h
  apply Fin.ext
  exact congrArg (fun c : Fin (9*B+3) => c.val) hc

theorem spaced_length (e : M.Term) :
    qmaManhattanLength (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeLeft e)))
      (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeRight e))) ≤
        8*(9*B+9)*(3*A+2) := by
  rw [qmaLane_length]
  exact Nat.mul_le_mul_left _ (M.routeLength_bound e)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedEndpointWalk
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unit-step walks join the degree-three vertices through their separated lanes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def routeVertex (v : Fin M.n) : ℕ × ℕ :=
  qmaFineGridNat (M.qubitSlots.site v)

def placedVertex (v : Fin M.n) : ℕ × ℕ :=
  qmaBufferedCellPoint (9*B+3) (M.routeVertex v) (17,17)

def endpointColors (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n)
    (a : Fin 3) : ℕ := ((M.endpointPorts hd v).slot a).val

theorem endpointColors_assigned (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    M.endpointColors hd v ((M.endpointPorts hd v).assign e) = (M.laneColor e.val).val :=
  congrArg Fin.val ((M.endpointPorts hd v).aligned e)

def endpointArmLength (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : ℕ :=
  qmaBufferedArmLength (M.endpointColors hd v) (fun _ => false) ((M.endpointPorts hd v).assign e)

def endpointArmPoint (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (k : ℕ) : ℕ × ℕ :=
  qmaBufferedCellPoint (9*B+3) (M.routeVertex v)
    (qmaBufferedArmPoint (M.endpointColors hd v) (fun _ => false) ((M.endpointPorts hd v).assign e) k)

@[simp] theorem endpointArm_zero (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : M.endpointArmPoint hd v e 0 = M.placedVertex v := by
  simp [endpointArmPoint,placedVertex]

@[simp] theorem endpointArm_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    M.endpointArmPoint hd v e (M.endpointArmLength hd v e) =
      qmaLanePoint (M.spacedColor e.val) (M.routeVertex v) := by
  dsimp only [endpointArmPoint,endpointArmLength]
  rw [qmaBufferedArm_last]
  change qmaBufferedCellPoint (9*B+3) (M.routeVertex v)
    (8*(M.endpointColors hd v ((M.endpointPorts hd v).assign e)+3),
     8*(M.endpointColors hd v ((M.endpointPorts hd v).assign e)+3)) = _
  rw [M.endpointColors_assigned]
  exact (qmaSpacedEndpoint (M.routeVertex v) ((M.laneColor e.val).castAdd 3)).symm

theorem endpointArm_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (k : ℕ) (hk : k < M.endpointArmLength hd v e) :
    qmaSquareGrid.Adj (M.endpointArmPoint hd v e k) (M.endpointArmPoint hd v e (k+1)) := by
  have h := qmaBufferedArm_step (M.endpointColors hd v) (fun _ => false)
    ((M.endpointPorts hd v).assign e) k hk
  simpa only [endpointArmPoint,qmaBufferedCellPoint,qmaSquareGrid,Nat.dist_add_add_left] using h

theorem endpointArm_length_bound (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : M.endpointArmLength hd v e ≤ 16*(9*B+6)+2 :=
  qmaBufferedArm_length_bound (M.endpointColors hd v) (fun _ => false)
    (fun a => ((M.endpointPorts hd v).slot a).isLt) _

def endpointArmWalk (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    qmaSquareGrid.Walk (M.placedVertex v) (qmaLanePoint (M.spacedColor e.val) (M.routeVertex v)) :=
  (qmaGridWalk (M.endpointArmPoint hd v e) (M.endpointArmLength hd v e)
    (M.endpointArm_step hd v e)).copy (M.endpointArm_zero hd v e) (M.endpointArm_last hd v e)

@[simp] theorem endpointArmWalk_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    (M.endpointArmWalk hd v e).length = M.endpointArmLength hd v e := by
  simp [endpointArmWalk,SimpleGraph.Walk.length_copy,qmaGridWalk_length]

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The routed paths visit original graph vertices only at their own endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem routeVertex_injective : Function.Injective M.routeVertex := by
  intro v w h
  exact M.qubitSlots.site_injective (qmaFineGridNat_injective h)

theorem placedVertex_injective : Function.Injective M.placedVertex := by
  intro v w h
  have hh := congrArg (fun z : ℕ × ℕ =>
    (z.1/(8*(9*B+3+6)),z.2/(8*(9*B+3+6)))) h
  dsimp only [placedVertex] at hh
  rw [qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega),
    qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega)] at hh
  exact M.routeVertex_injective hh

def endpointArmSupport (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (z : ℕ × ℕ) : Prop :=
  ∃ p, qmaBufferedCellPoint (9*B+3) (M.routeVertex v) p = z ∧
    qmaBufferedFanoutSupport (M.endpointColors hd v) (fun _ => false)
      ((M.endpointPorts hd v).assign e) p

theorem endpointArmWalk_support (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ}
    (hz : z ∈ (M.endpointArmWalk hd v e).support) : M.endpointArmSupport hd v e z := by
  simp only [endpointArmWalk,SimpleGraph.Walk.support_copy] at hz
  obtain ⟨k,_,hk⟩ := qmaGridWalk_support _ _ _ hz
  exact ⟨_,hk,qmaBufferedArm_support _ _ _ k⟩

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered routes lie strictly inside the nonnegative lattice quadrant. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointArmSupport_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ} (hz : M.endpointArmSupport hd v e z) :
    0 < z.1 ∧ 0 < z.2 := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  rw [← hp]
  dsimp [qmaBufferedCellPoint]
  omega

theorem spacedSupport_positive (e : M.Term) {z : ℕ × ℕ} (hz : M.spacedSupport e z) :
    0 < z.1 ∧ 0 < z.2 := by
  have hc : 0 < (M.spacedColor e).val := by
    dsimp [spacedColor,qmaSpacedLaneColor]
    omega
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩ <;>
    dsimp [qmaLanePoint,qmaBetween] at * <;> omega

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedIntersections
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered arms are mutually disjoint away from their common graph vertex. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointLocal_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (a : Fin 3) {p : ℕ × ℕ}
    (hs : qmaBufferedFanoutSupport (M.endpointColors hd v) (fun _ => false) a p) :
    0 < p.1 ∧ p.1 < 8*(9*B+9) ∧ 0 < p.2 ∧ p.2 < 8*(9*B+9) :=
  qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) a hs

theorem endpointArmSupport_grid (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e z) (hz : z.1 % 8 = 0 ∧ z.2 % 8 = 0) :
    z = qmaLanePoint (M.spacedColor e.val) (M.routeVertex v) := by
  obtain ⟨p,hp,hs⟩ := he
  have hx : p.1 % 8 = 0 := by
    have h := congrArg (fun z : ℕ × ℕ => z.1 % 8) hp
    simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hz.1] using h
  have hy : p.2 % 8 = 0 := by
    have h := congrArg (fun z : ℕ × ℕ => z.2 % 8) hp
    simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hz.2] using h
  have hx' : 8*(p.1/8) = p.1 := by omega
  have hy' : 8*(p.2/8) = p.2 := by omega
  have hg := qmaBufferedFanout_grid_point (M.endpointColors hd v) (fun _ => false)
    ((M.endpointPorts hd v).assign e) (p.1/8) (p.2/8) (by simpa only [hx',hy'] using hs)
  have hg' : p = (qmaBufferedPort (M.endpointColors hd v) ((M.endpointPorts hd v).assign e),
      qmaBufferedPort (M.endpointColors hd v) ((M.endpointPorts hd v).assign e)) := by
    simpa only [hx',hy'] using hg
  rw [hg'] at hp
  have halign := M.endpointArm_last hd v e
  simp only [endpointArmPoint,endpointArmLength,qmaBufferedArm_last] at halign
  exact hp.symm.trans halign

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedExtent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rectangular bounds for every vertex and every buffered route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def bufferedWidth : ℕ := 8*(9*B+9)*((M.rows+1)*A)
def bufferedHeight : ℕ := 8*(9*B+9)*(M.width+1)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedGridEdge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An arm can overlap a grid-aligned unit edge only at its terminal grid point. -/

namespace ContinuumCoulomb

theorem qmaBufferedFanout_horizontal_grid_edge (c : Fin 3 → ℕ) (a : Fin 3)
    {p q : ℕ × ℕ} (hp : qmaBufferedFanoutSupport c (fun _ => false) a p)
    (hq : qmaBufferedFanoutSupport c (fun _ => false) a q)
    (hy : p.2 = q.2) (hm : p.2 % 8 = 0) (hd : Nat.dist p.1 q.1 = 1) :
    p.1 % 8 = 0 ∨ q.1 % 8 = 0 := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  fin_cases a <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedOffset,qmaBufferedPort,qmaBetween,Nat.dist] at * <;> omega

theorem qmaBufferedFanout_vertical_grid_edge (c : Fin 3 → ℕ) (a : Fin 3)
    {p q : ℕ × ℕ} (hp : qmaBufferedFanoutSupport c (fun _ => false) a p)
    (hq : qmaBufferedFanoutSupport c (fun _ => false) a q)
    (hx : p.1 = q.1) (hm : p.1 % 8 = 0) (hd : Nat.dist p.2 q.2 = 1) :
    p.2 % 8 = 0 ∨ q.2 % 8 = 0 := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  fin_cases a <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedOffset,qmaBufferedPort,qmaBetween,Nat.dist] at * <;> omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSharedEdge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different routes do not share lattice edges, including at buffered endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSquareGrid_not_eightfold {p q : ℕ × ℕ}
    (hp : p.1 % 8 = 0 ∧ p.2 % 8 = 0) (hq : q.1 % 8 = 0 ∧ q.2 % 8 = 0) :
    ¬qmaSquareGrid.Adj p q := by
  intro h
  change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at h
  unfold Nat.dist at h
  omega

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem spaced_incident_support (v : Fin M.n) (e : M.Incident v) :
    M.spacedSupport e.val (qmaLanePoint (M.spacedColor e.val) (M.routeVertex v)) := by
  rcases e.property with h | h
  · left
    dsimp [spacedSupport,qmaLaneSupport,routeLeft,routeRight,routeVertex]
    rw [h]
    exact ⟨rfl,min_le_left _ _,le_max_left _ _⟩
  · right
    dsimp [spacedSupport,qmaLaneSupport,routeLeft,routeRight,routeVertex]
    rw [h]
    exact ⟨rfl,min_le_right _ _,le_max_right _ _⟩

theorem spaced_unit_direction (e : M.Term) {p q : ℕ × ℕ}
    (hp : M.spacedSupport e p) (hq : M.spacedSupport e q) (ha : qmaSquareGrid.Adj p q) :
    (p.1 = q.1 ∧ p.1 % 8 = 0) ∨ (p.2 = q.2 ∧ p.2 % 8 = 0) := by
  have haxis : p.1 = q.1 ∨ p.2 = q.2 := by
    change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at ha
    unfold Nat.dist at ha
    omega
  have hxm : (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeRight e))).1 % 8 = 0 := by
    simp [qmaLanePoint,spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
  have hym : (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeLeft e))).2 % 8 = 0 := by
    simp [qmaLanePoint,spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
  rcases hp with ⟨hpy,_⟩ | ⟨hpx,_⟩ <;> rcases hq with ⟨hqy,_⟩ | ⟨hqx,_⟩
  · exact Or.inr ⟨hpy.trans hqy.symm,by rw [hpy]; exact hym⟩
  · rcases haxis with hx | hy
    · exact Or.inl ⟨hx,by rw [hx,hqx]; exact hxm⟩
    · exact Or.inr ⟨hy,by rw [hpy]; exact hym⟩
  · rcases haxis with hx | hy
    · exact Or.inl ⟨hx,by rw [hpx]; exact hxm⟩
    · exact Or.inr ⟨hy,by rw [hy,hqy]; exact hym⟩
  · exact Or.inl ⟨hpx.trans hqx.symm,by rw [hpx]; exact hxm⟩

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

def tripleCode : Triple → List Bool := prodCode ratCode (prodCode ratCode ratCode)

noncomputable opaque firstProgram : Procedure tripleCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque tailProgram : Procedure tripleCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque secondProgram : Procedure tripleCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque thirdProgram : Procedure tripleCode ratCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp tailProgram

end ContinuumCoulomb.QuantumRoutingCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

def inputCode : Input → List Bool := prodCode Procedure.boolCode (prodCode ratCode ratCode)
noncomputable opaque evenProgram : Procedure inputCode Procedure.boolCode Prod.fst := Procedure.first _ _
noncomputable opaque tailProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd := Procedure.second _ _
noncomputable opaque radiusProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp tailProgram

end ContinuumCoulomb.QuantumPathCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalPathStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational graph data for a selected path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

attribute [instance] QMARationalExchangeGraph.edgeFinite

namespace QMARationalExchangeGraph

def energy (G : QMARationalExchangeGraph) : ℝ :=
  sourceMatrixBottom G.n (qmaExchangeMatrix G.left G.right (fun e => G.weight e) G.constant)

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedPortChain
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bounded spatial routes give distinct physical spin locations at every
cell port, including cells at which two coarse routes cross. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

abbrev exchangeGraph : QMARationalExchangeGraph where
  n := M.n
  Edge := M.Term
  left := M.left
  right := M.right
  distinct := M.distinct
  weight := M.weight
  constant := M.constant

@[simp] theorem exchangeGraph_energy : M.exchangeGraph.energy = M.energy := rfl

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal membership tests for the finite geometry tables used by the
140-candidate planar route selector. The Boolean fold has constant-size state. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteMembership
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable opaque anyProgram : Procedure (listCode Procedure.boolCode) Procedure.boolCode
    (fun xs => xs.any id) := by
  let p := Procedure.foldList false Procedure.boolOr (Polynomial.C 1) (by
    intro xs b i
    simp only [Procedure.boolCode,List.length_singleton,Polynomial.eval_C]
    exact le_rfl)
  exact (p.comp ((Procedure.identity _).pair (Procedure.constant _ _ false))).congrFun (by
    intro xs
    simp only [Function.comp_apply,fold_or,Bool.or_false,id_eq])

noncomputable opaque pairEqProgram : Procedure (prodCode pairCode pairCode) Procedure.boolCode
    (fun x => decide (x.1=x.2)) := Procedure.prodEq Procedure.binaryEq Procedure.binaryEq

end ContinuumCoulomb.QuantumFiniteMembership

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse route's library loop erasure is the explicit right-to-left
finite-list algorithm. This identifies the actual path data needed by the
literal spatial compiler. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb
namespace QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem listCode_length_sublist (ea : α → List Bool) {xs ys : List α} (h : xs <+ ys) :
    (listCode ea xs).length ≤ (listCode ea ys).length := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih =>
    rw [listCode_length_cons]
    omega
  | cons_cons a h ih =>
    simp only [listCode_length_cons]
    omega

end QuantumWalkErasure

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm list is computed from its ordinal port, lane color and
coarse vertex. All three quantities are supplied by the explicit slot and
incident-rank programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def armCode : ArmInput → List Bool := prodCode unaryCode unaryCode

def armList (x : ArmInput) : List Pair :=
  if x.1=0 then (List.range (QuantumBufferedArmProgram.length 0 x.2+1)).map
    (QuantumBufferedArmProgram.point 0 x.2)
  else if x.1=1 then (List.range (QuantumBufferedArmProgram.length 1 x.2+1)).map
    (QuantumBufferedArmProgram.point 1 x.2)
  else (List.range (QuantumBufferedArmProgram.length 2 x.2+1)).map
    (QuantumBufferedArmProgram.point 2 x.2)

def translate (B : ℕ) (p z : Pair) : Pair := qmaBufferedCellPoint (9*B+3) p z

abbrev Input := Pair × ArmInput
def inputCode : Input → List Bool := prodCode pairCode armCode
def value (B : ℕ) (x : Input) : List Pair := (armList x.2).map (translate B x.1)

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the Manhattan segment with an explicit fixed route budget.
The cap makes enumeration polynomial on every input, and disappears for
the spatial routes satisfying the proved length bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumManhattanListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode

def value (K : ℕ) (x : Ends) : List Pair :=
  (List.range (min K (qmaManhattanLength x.1 x.2)+1)).map (qmaManhattanPoint x.1 x.2)

end ContinuumCoulomb.QuantumManhattanListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpacedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the bounded Manhattan portion of each actual buffered route.
The horizontal and vertical translations are literal binary arithmetic. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpacedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def point (B color : ℕ) (p : Pair) : Pair :=
  qmaBufferedCellPoint (9*B+3) p (8*(color+3),8*(color+3))

abbrev PointInput := ℕ × Pair
def pointCode : PointInput → List Bool := prodCode unaryCode pairCode

abbrev Input := ℕ × (Pair × Pair)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode pairCode pairCode)
def value (A B : ℕ) (x : Input) : List Pair :=
  QuantumManhattanListProgram.value (budget A B) (point B x.1 x.2.1,point B x.1 x.2.2)

end ContinuumCoulomb.QuantumSpacedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkSeek
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded scan finds the first occurrence of a cell in a route list.
It only removes list heads, so the machine state never grows. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkSeek
open ExactQuantumFactoring.BitStackProgram
variable {α : Type} [DecidableEq α]

noncomputable def scanProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (prodCode ea (listCode ea)) (scan d) := by
  let a := Procedure.first ea (listCode ea)
  let xs := Procedure.second ea (listCode ea)
  let same := eqp.comp (a.pair ((Procedure.listHead ea d).comp xs))
  exact (Procedure.conditional same (Procedure.identity _) (a.pair ((Procedure.listTail ea).comp xs))).congrFun
    (by intro x; simp only [Function.comp_apply,scan,decide_eq_true_eq,id_eq])

noncomputable def program (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (listCode ea) (fun x => x.2.drop (x.2.idxOf x.1)) := by
  let rep := (scanProgram ea d eqp).iterate Polynomial.X (by
    intro n x i _
    simp only [prodCode,pairBits_length,Polynomial.eval_X,iterate_first]
    have h := QuantumWalkErasure.listCode_length_sublist ea (iterate_sublist d x i)
    omega)
  let count := (Procedure.length.precompose (listCode ea)).comp (Procedure.second ea (listCode ea))
  exact ((Procedure.second ea (listCode ea)).comp
    (rep.comp (count.pair (Procedure.identity _)))).congrFun (by
      intro x
      exact scan_drop_idx d x.1 x.2 _ (list_length_le_code ea x.2))

end ContinuumCoulomb.QuantumWalkSeek

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal construction and loop erasure of the complete buffered route.
The input consists of two computed fine-grid endpoints, one lane color and
the two computed incident port ranks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Input := (Pair × Pair) × (ℕ × (ℕ × ℕ))
def inputCode : Input → List Bool :=
  prodCode (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))

def value (A B : ℕ) (x : Input) : List Pair :=
  QuantumEndpointListProgram.value B (x.1.1,x.2.2.1,x.2.1) ++
    (QuantumSpacedListProgram.value A B (x.2.1,x.1.1,x.1.2)).tail ++
    (QuantumEndpointListProgram.value B (x.1.2,x.2.2.2,x.2.1)).reverse.tail

def path (A B : ℕ) (x : Input) : List Pair := QuantumWalkErasure.erase (value A B x)

end ContinuumCoulomb.QuantumBufferedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial evaluation of all 140 path candidates. Every template
is constant-sized, and only its endpoint cell coordinates vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCellPathProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable opaque pointCellProgram : Procedure pairCode pairCode qmaPointCell := by
  let c := Procedure.constant pairCode Nat.bits 32
  exact (Procedure.binaryDiv.comp ((Procedure.first Nat.bits Nat.bits).pair c)).pair
    (Procedure.binaryDiv.comp ((Procedure.second Nat.bits Nat.bits).pair c))

end ContinuumCoulomb.QuantumCellPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceBondLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete matrix semantics for the literal bond registers. Removing zero
terms preserves the actual Hamiltonian, while valid bounded indices give
the exact finite family used in the mediator comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceBondLists
open Matrix MediatorIteration MediatorListProgram
open scoped BigOperators

def bondMatrix (n : ℕ) (e : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  if h : e.1 < n ∧ e.2.1 < n then (e.2.2 : ℂ) •
    sourceHeisenbergMatrix n ⟨e.1, h.1⟩ ⟨e.2.1, h.2⟩ else 0

def matrix (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (xs.map (bondMatrix n)).sum

theorem bonds_noLoops (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (h : bounded n xs)
    (hloop : ∀ e ∈ xs, e.1 ≠ e.2.1) : (bonds n xs h).NoLoops := by
  intro i hi
  exact hloop _ (List.get_mem xs i) (congrArg Fin.val hi)

end ContinuumCoulomb.SourceBondLists

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathPolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial coefficient envelopes for the actual selected path
subdivision, uniform in the selected set and its parity choices. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

def CoefficientBound (L : ℝ) : Prop :=
  |(G.constant:ℝ)| ≤ L ∧ ∀ e, |(G.weight e:ℝ)| ≤ L

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs for the actual routing coefficient envelopes.
Their output lengths give polynomial bounds without choosing giant exponents. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)
noncomputable def constant {α : Type} (ea : α → List Bool) (n : ℕ) :
    Procedure ea unaryCode (fun _ => n) := Procedure.constant ea unaryCode n
noncomputable def square {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^2) :=
  (mul p p).congrFun (by intro x; simp only [pow_two])
noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (mul p p) p).congrFun (by intro x; simp only [pow_succ,pow_zero,one_mul])

noncomputable opaque pathBudgetProgram {α : Type} {ea : α → List Bool} {m L : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => pathBudget (m x) (L x)) := by
  let c := constant ea
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 3) pm) (add (c 1) (mul (c 2) pl))))
    (mul (mul (c 4) pm) (square (add (c 1) pl)))) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque pathRadiusProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => pathRadius (m x) (L x) (T x)) := by
  let c := constant ea
  let pb := pathBudgetProgram pm pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt))
    (mul (c 4) pb)) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque pathCoefficientProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => pathCoefficient (m x) (L x) (T x)) := by
  let c := constant ea
  exact (add (add (c 1) pl) (mul (add (mul (c 7) pm) (c 2))
    (square (pathRadiusProgram pm pl pt)))).congrFun (by intro x; rfl)

noncomputable opaque mProgram : Procedure inputCode unaryCode (fun x => x.1) := Procedure.first _ _
noncomputable opaque lProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque tProgram : Procedure inputCode unaryCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable opaque crossingBudgetProgram {α : Type} {ea : α → List Bool} {m r L : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => crossingBudget (m x) (r x) (L x)) := by
  let c := constant ea
  let p := add (c 1) (mul (c 2) pl)
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 6) pr) p)) (mul (mul (c 12) pr) (square p))) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque crossingRadiusProgram {α : Type} {ea : α → List Bool} {m r L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r)
    (pl : Procedure ea unaryCode L) (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => crossingRadius (m x) (r x) (L x) (T x)) := by
  let c := constant ea
  let pb := crossingBudgetProgram pm pr pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt))
    (mul (c 4) pb)) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque crossingCoefficientProgram {α : Type} {ea : α → List Bool} {m r L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r)
    (pl : Procedure ea unaryCode L) (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => crossingCoefficient (m x) (r x) (L x) (T x)) := by
  let c := constant ea
  exact (add (add (c 1) pl) (mul (add (mul (c 11) pr) (c 2))
    (square (crossingRadiusProgram pm pr pl pt)))).congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPathClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact endpoint clearance inside one cell. These finite facts separate
external corridors from the rays, ordinary pairs and nine gadget paths. -/

namespace ContinuumCoulomb

theorem qmaCellPair_half (e : Fin 6) (a : Fin 4) :
    Disjoint (((qmaCellPairPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath false a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

theorem qmaCellRay_half (e a : Fin 4) :
    Disjoint (((qmaCellRayPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath false a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

theorem qmaLocalPatch_half (e : Fin 9) (a : Fin 4) :
    Disjoint (((qmaLocalPatchPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath true a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell-local disjointness extends to the actual translated physical paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRoute_interior_finset (R : QMACellRoute) :
    ((R.path.drop 1).dropLast).toFinset = ((R.body.path.drop 1).dropLast).toFinset := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact qmaInterior_reverse b.path

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert an actual simple rational grid graph into the field-free source
Hamiltonian, retaining the exact scalar shift in its thresholds. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaGridCoordinate_adj {p q : ℕ × ℕ} (h : qmaSquareGrid.Adj p q) :
    Int.natAbs ((qmaGridCoordinate p).1-(qmaGridCoordinate q).1)+
      Int.natAbs ((qmaGridCoordinate p).2-(qmaGridCoordinate q).2) = 1 := by
  simpa only [qmaGridCoordinate,qmaNatDistance] using (show Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 from h)

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

def Simple : Prop := ∀ e f : G.Edge, e ≠ f →
  ¬(G.left e = G.left f ∧ G.right e = G.right f) ∧
  ¬(G.left e = G.right f ∧ G.right e = G.left f)

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program computes the final coefficient envelope;
the exponent in the source promise is uniform over all inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

noncomputable def addP {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
noncomputable def mulP {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)

noncomputable def iteratedOfProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) (k : ℕ) :
    Procedure ea unaryCode (fun x => iterated (m x) (L x) (T x) k) := by
  induction k with
  | zero => exact pl
  | succ k ih =>
    exact pathCoefficientProgram (mulP (Procedure.constant ea unaryCode (3^k)) pm) ih pt

def latticeInputCode : LatticeInput → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

noncomputable opaque latticeM : Procedure latticeInputCode unaryCode (fun x => x.1) := Procedure.first _ _
noncomputable opaque latticeTail : Procedure latticeInputCode (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x => x.2) := Procedure.second _ _
noncomputable opaque latticeR : Procedure latticeInputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp latticeTail
noncomputable opaque latticeLT : Procedure latticeInputCode (prodCode unaryCode unaryCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp latticeTail
noncomputable opaque latticeL : Procedure latticeInputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp latticeLT
noncomputable opaque latticeT : Procedure latticeInputCode unaryCode (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp latticeLT

noncomputable opaque latticeBoundProgram (D : ℕ) :
    Procedure latticeInputCode unaryCode (fun x => latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let c := Procedure.constant latticeInputCode unaryCode
  let m₁ := mulP (c (3^D)) latticeM
  let L₁ := iteratedOfProgram latticeM latticeL latticeT D
  let m₂ := addP m₁ (mulP (c 9) latticeR)
  let L₂ := crossingCoefficientProgram m₁ latticeR (mulP (addP m₁ (c 1)) L₁) latticeT
  let L₃ := mulP (addP m₂ (c 1)) L₂
  let L₄ := iteratedOfProgram (mulP (c 3) m₂) (pathCoefficientProgram m₂ L₃ latticeT) latticeT 80
  exact (mulP (addP (mulP (c (3^81)) m₂) (c 1)) L₄).congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw scalar/field/pair instructions read directly from the ordered
site-label list. Only two entries are inspected at the final X/Z stage. -/

namespace ContinuumCoulomb.QuantumOrderedRawPacking

theorem value_pack {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) (j : ℚ) :
    value (xs.map (fun i => (i.val,(w i).val)),j) =
      QuantumRawExchange.pack (QuantumOrderedXZTerm.ofSites xs w) j := by
  cases xs with
  | nil => rfl
  | cons i xs =>
    cases xs with
    | nil => exact field_pack w i j
    | cons k xs =>
      by_cases hik : i=k
      · subst k
        simp only [List.map_cons,value,ite_true, if_true,QuantumOrderedXZTerm.ofSites,dite_true]
        exact field_pack w i j
      · have hv : i.val ≠ k.val := fun h => hik (Fin.ext h)
        have hi : (w i).val=0 ↔ w i=0 := Fin.val_eq_zero_iff
        have hk : (w k).val=0 ↔ w k=0 := Fin.val_eq_zero_iff
        simp only [List.map_cons,value,hv,ite_false, if_false,QuantumOrderedXZTerm.ofSites,
          dite_eq_right hik,hi,hk]
        split_ifs with hi hk
        · exact field_pack w k j
        · exact field_pack w i j
        · simp only [pair,QuantumRawExchange.pack,axis_zero]

end ContinuumCoulomb.QuantumOrderedRawPacking

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

def gateSites (work : ℕ) : QMAGate → List (Fin (work+1))
  | .hadamard i => [qmaQubit work i]
  | .phaseT i => [qmaQubit work i]
  | .controlledNot i j => [qmaQubit work i,qmaQubit work j]

def propagationSites (c : QMACircuit) (t : Fin c.gates.length) : List (QMACircuitQubit c) :=
  [Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
    Sum.inl (qmaClockRight c.gates.length t)] ++
    (gateSites c.work (c.gates.getD t.val (.hadamard 0))).map Sum.inr

def distributedSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    QMACircuitTerm c → List (QMACircuitQubit c)
  | .inl i => [Sum.inl i.castSucc,Sum.inl i.succ]
  | .inr (.inl b) => if b = 0 then [Sum.inl 0]
      else [Sum.inl (Fin.last (c.gates.length+1))]
  | .inr (.inr (.inl i)) => [Sum.inl (τ i).castSucc,Sum.inl (τ i).succ,Sum.inr i]
  | .inr (.inr (.inr (.inl _))) =>
      [Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)]
  | .inr (.inr (.inr (.inr t))) => propagationSites c t

abbrev Qubit (c : QMACircuit) := Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c

def siteNumber (c : QMACircuit) : Qubit c → ℕ
  | .inl i => i.val
  | .inr (.inl i) => qmaHistoryReferenceWork c+1+i.val
  | .inr (.inr i) => qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program for the final ordered X/Z classifier.
It reads two site-label pairs and never enumerates a spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawPacking
open ExactQuantumFactoring.BitStackProgram

def letterCode : Letter → List Bool := prodCode Nat.bits Nat.bits
def inputCode : Input → List Bool := prodCode (listCode letterCode) ratCode

noncomputable opaque weightProgram : Procedure inputCode ratCode Prod.snd := Procedure.second _ _
noncomputable opaque entriesProgram : Procedure inputCode (listCode letterCode) Prod.fst :=
  Procedure.first _ _
noncomputable opaque lengthProgram : Procedure inputCode Nat.bits (fun x => x.1.length) :=
  Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength letterCode (0,0)).comp entriesProgram)
noncomputable opaque lengthTest (k : ℕ) : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.1.length=k)) :=
  Procedure.binaryEq.comp (lengthProgram.pair (Procedure.constant inputCode Nat.bits k))

noncomputable opaque scalarProgram : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => scalar x.2) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (false,false)).pair
    ((Procedure.constant inputCode (prodCode Nat.bits Nat.bits) (0,0)).pair
      ((Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode)
        (false,false)).pair weightProgram))

end ContinuumCoulomb.QuantumOrderedRawPacking

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial list programs for the literal support-label operations.
Only constant-length prefixes are split in the early gadget compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

abbrev labelCode := QuantumOrderedRawPacking.letterCode
abbrev labelsCode := listCode labelCode

abbrev blockCode := prodCode Nat.bits labelsCode
noncomputable opaque mediatorProgram : Procedure blockCode Nat.bits Prod.fst := Procedure.first _ _
noncomputable opaque labelsProgram : Procedure blockCode labelsCode Prod.snd := Procedure.second _ _

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-size programs for the triple partition and YY/private
blocks. The branch tests inspect only the stored support labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque lengthTest (n : ℕ) : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (xs.length=n)) :=
  Procedure.binaryEq.comp ((Procedure.unaryToBits.comp
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength labelCode (0,0))).pair
    (Procedure.constant labelsCode Nat.bits n))

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational calibration from the retained and selected edge weights.
The sums are computed by the proved polynomial rational-list accumulator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

def inputCode : Input → List Bool :=
  prodCode (prodCode ratCode ratCode) (prodCode (listCode ratCode) (listCode ratCode))

end ContinuumCoulomb.QuantumPathScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform literal rational-list programs for all five early gadget stages.
The lists retain input order and emit each fixed block in its word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedWeightProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

def pairCode : Pair → List Bool := prodCode ratCode ratCode
noncomputable opaque radius : Procedure pairCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque coupling : Procedure pairCode ratCode Prod.snd := Procedure.second _ _
def inputCode : Input → List Bool := prodCode unaryCode (listCode ratCode)

end ContinuumCoulomb.QuantumOrderedWeightProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal indexed list stage, shared by the six fixed local reductions.
New mediator indices are the old qubit count plus the input term index.
Unary counts bound the output size; rational coefficients stay binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelFamily
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData

def entryCode : Entry → List Bool := prodCode labelsCode ratCode
def stateCode : State → List Bool := prodCode unaryCode (listCode entryCode)
def inputCode : Input → List Bool := prodCode unaryCode stateCode
def blockCode : BlockInput → List Bool := prodCode (prodCode Nat.bits ratCode) entryCode

noncomputable opaque stateProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp stateProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp stateProgram
noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode ([],0)).comp entriesProgram

end ContinuumCoulomb.QuantumOrderedLabelFamily

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZScalarSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed scalar correction for the complete private-pair X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def scalarValue (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℚ :=
  r^2*(n*6)+(∑ e : QMAXZScalarIndex t, J e.val)-
    (∑ e : QMAXZPairIndex t, offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val))-
    ∑ e : QMAXZFieldIndex t, shiftValue (qmaXZFieldData t e).axis (J e.val)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled rational exchange Hamiltonian approximates the entire logical X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def matrixValue (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaExchangeMatrix
    (qmaFourExchangeLeft (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZFieldData t e).site))
    (qmaFourExchangeRight (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZFieldData t e).site))
    (fun x => (weightValue k r
      (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
      (fun e => J e.val) (fun e => (qmaXZFieldData t e).axis) (fun e => J e.val) x:ℝ))
    (scalarValue k r t J:ℝ)

def matrixErrorBudget (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℝ :=
  3*(Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)):ℝ)*
    weightErrorBudget (r:ℝ) (qmaXZInputSize (fun e => (J e:ℝ)))+320800*(∑ e, |(J e:ℝ)|)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSamplePrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic precision, computed from binary numerators, suffices for the physical error budget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

def precisionCode : (ℚ × ℕ) → List Bool := prodCode ratCode Nat.bits

noncomputable opaque numeratorMagnitudeProgram : Procedure precisionCode Nat.bits
    (fun x => x.1.num.natAbs) :=
  Procedure.intAbs.comp (Procedure.ratNum.comp (Procedure.first ratCode Nat.bits))

noncomputable opaque numeratorSizeProgram : Procedure precisionCode unaryCode
    (fun x => x.1.num.natAbs.size) :=
  ((Procedure.length.precompose Nat.bits).comp numeratorMagnitudeProgram).congrFun
    (by intro x; exact Nat.size_eq_bits_len _)

noncomputable opaque denominatorSizeProgram : Procedure precisionCode unaryCode (fun x => x.2.size) :=
  ((Procedure.length.precompose Nat.bits).comp (Procedure.second ratCode Nat.bits)).congrFun
    (by intro x; exact Nat.size_eq_bits_len _)

noncomputable opaque precisionProgram : Procedure precisionCode unaryCode (fun x => precision x.1 x.2) :=
  Procedure.unaryAdd.comp (numeratorSizeProgram.pair denominatorSizeProgram)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computable binary-precision choice closes the full rational four-spin error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def rationalErrorBudget (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℚ :=
  3*Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t))*
    (1568*|r| *(1+rationalInputSize J)+26064*rationalInputSize J)+320800*(∑ e, |J e|)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact termwise assembly of the computed physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

def typedBondMatrix {m : ℕ} (b : TypedBond m) : Matrix (SourceSpinBasis m) (SourceSpinBasis m) ℂ :=
  (b.2.2:ℂ) • sourceHeisenbergMatrix m b.1 b.2.1

def fieldBonds {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) : List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin 3 => (finProdFinEquiv (i,0),
    finProdFinEquiv (i,qmaFieldEdgeRight e),fieldValue k a J e)

def crossBonds {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin 16 =>
    let pq := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e
    (finProdFinEquiv (i,pq.1),finProdFinEquiv (j,pq.2),crossValue k r a b J pq.1 pq.2)

def termBonds {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) : List (TypedBond (n*4)) :=
  match t with
  | .scalar => []
  | .field i a => fieldBonds k i a J
  | .pair i j _ a b => crossBonds k r i j a b J ++
      fieldBonds k i a (counterA k a b J) ++ fieldBonds k j b (counterB k a b J)

def termScalar {n : ℕ} (k : ℕ) (t : QMAXZTerm n) (J : ℚ) : ℚ :=
  match t with
  | .scalar => J
  | .field _ a => -shiftValue a J
  | .pair _ _ _ a b => -offset k a b J

variable {n : ℕ} {κ : Type*} [Fintype κ]

def pairBondMatrix (k : ℕ) (r : ℚ) (d : QMAXZPair n) (J : ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ p : Fin 4, ∑ q : Fin 4, (crossValue k r d.axisLeft d.axisRight J p q:ℂ) •
    sourceHeisenbergMatrix (n*4) (finProdFinEquiv (d.left,p)) (finProdFinEquiv (d.right,q)))+
  ((fieldBonds k d.left d.axisLeft (counterA k d.axisLeft d.axisRight J)).map typedBondMatrix).sum+
  ((fieldBonds k d.right d.axisRight (counterB k d.axisLeft d.axisRight J)).map typedBondMatrix).sum

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal raw edge instructions encode the proved physical matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

def erase {m : ℕ} (b : TypedBond m) : Bond := (b.1.val,b.2.1.val,b.2.2)

theorem field_erase {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) :
    (fieldBonds k i a J).map erase = field k i.val a J := by
  simp [fieldBonds,field,erase,finProdFinEquiv,Nat.add_comm]

theorem cross_erase {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    (crossBonds k r i j a b J).map erase = cross k r i.val j.val a b J := by
  simp only [crossBonds,cross,List.map_ofFn]
  apply congrArg List.ofFn
  funext e
  dsimp only [Function.comp_apply]
  generalize (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e = pq
  change (pq.1.val+4*i.val,pq.2.val+4*j.val,crossValue k r a b J pq.1 pq.2) = _
  simp only [Nat.add_comm]

theorem bonds_pack {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) :
    bonds ((k,r),pack t J) = (termBonds k r t J).map erase := by
  cases t <;> simp [bonds,pack,axis_pack,termBonds,List.map_append,field_erase,cross_erase]

theorem fieldBonds_distinct {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ fieldBonds k i a J) : b.1 ≠ b.2.1 := by
  obtain ⟨e,he⟩ := List.mem_ofFn.mp hb
  subst b
  intro h
  exact qmaFieldEdgeRight_ne e (congrArg Prod.snd (finProdFinEquiv.injective h))

theorem crossBonds_distinct {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (hij : i ≠ j)
    (a b : Fin 2) (J : ℚ) (e : TypedBond (n*4))
    (he : e ∈ crossBonds k r i j a b J) : e.1 ≠ e.2.1 := by
  obtain ⟨p,hp⟩ := List.mem_ofFn.mp he
  subst e
  intro h
  exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))

theorem termBonds_distinct {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ termBonds k r t J) : b.1 ≠ b.2.1 := by
  cases t with
  | scalar => simp [termBonds] at hb
  | field i a => exact fieldBonds_distinct k i a J b hb
  | pair i j hij a c =>
    simp only [termBonds,List.mem_append] at hb
    rcases hb with (hb|hb)|hb
    · exact crossBonds_distinct k r i j hij a c J b hb
    · exact fieldBonds_distinct _ _ _ _ b hb
    · exact fieldBonds_distinct _ _ _ _ b hb

def family {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    List (TypedBond (n*4)) :=
  penaltyBonds n r ++ (List.ofFn (fun e => termBonds k r (t e) (J e))).flatten

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computable budget uses only the qubit count, term count and coefficient mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

variable {n : ℕ} {κ : Type*} [Fintype κ]

def boundedMatrix (N : ℕ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  matrixValue (boundedPrecision N t J) (rationalPenalty N J) t J

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawFamilyCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact correspondence between the emitted raw family and its certified finite Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem penalty_erase (n : ℕ) (r : ℚ) :
    (penaltyBonds n r).map erase = penalty n r := by
  have hrange : (List.range n).map (penaltyBlock r) =
      List.ofFn (fun i : Fin n => penaltyBlock r i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range n) (penaltyBlock r)).symm
  rw [penalty,hrange,penaltyBonds,List.map_ofFn,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*6+j.val,by omega⟩ : Fin (n*6)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*6+j.val = j.val+6*i.val
    omega
  simp only [he,Equiv.symm_apply_apply,Function.comp_apply,erase]
  change ((qmaFourEdgeLeft j).val+4*i.val,(qmaFourEdgeRight j).val+4*i.val,r^2) = _
  simp only [Nat.add_comm]

theorem fullBonds_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    fullBonds (n,(k,r),packed t J) = (family k r t J).map erase := by
  simp only [fullBonds,family,List.map_append,penalty_erase,termBondsList,packed,
    List.map_flatten,List.map_ofFn,Function.comp_def,bonds_pack]

theorem family_distinct {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ family k r t J) : b.1 ≠ b.2.1 := by
  rcases List.mem_append.mp hb with h | h
  · exact penaltyBonds_distinct n r b h
  · obtain ⟨xs,hxs,hb⟩ := List.mem_flatten.mp h
    obtain ⟨e,he⟩ := List.mem_ofFn.mp hxs
    subst xs
    exact termBonds_distinct k r (t e) (J e) b hb

theorem fullBonds_valid {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : Bond) (hb : b ∈ fullBonds (n,(k,r),packed t J)) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 := by
  rw [fullBonds_packed] at hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  refine ⟨a.1.isLt,a.2.1.isLt,?_⟩
  exact fun h => family_distinct k r t J a ha (Fin.ext h)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All four-spin scales and precisions are computed from the raw finite input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

def scheduleCode : ScheduleInput → List Bool :=
  prodCode unaryCode (prodCode Nat.bits (listCode rawCode))

def compile (x : ScheduleInput) : List Bond × ℚ := (fullBonds (scheduled x),fullScalar (scheduled x))

noncomputable opaque rawWeightProgram : Procedure rawCode ratCode (fun t => t.2.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _))

noncomputable opaque scheduleCountProgram : Procedure scheduleCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque scheduleTailProgram : Procedure scheduleCode
    (prodCode Nat.bits (listCode rawCode)) Prod.snd := Procedure.second _ _
noncomputable opaque accuracyProgram : Procedure scheduleCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp scheduleTailProgram
noncomputable opaque scheduleTermsProgram : Procedure scheduleCode (listCode rawCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp scheduleTailProgram
noncomputable opaque scheduleLengthProgram : Procedure scheduleCode unaryCode (fun x => x.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength rawCode zeroRaw).comp scheduleTermsProgram
noncomputable opaque scheduleLengthRatProgram : Procedure scheduleCode ratCode (fun x => (x.2.2.length:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp scheduleLengthProgram)
noncomputable opaque accuracyRatProgram : Procedure scheduleCode ratCode (fun x => (x.2.1:ℚ)) :=
  Procedure.natToRat.comp accuracyProgram
noncomputable opaque countRatProgram : Procedure scheduleCode ratCode (fun x => (x.1:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp scheduleCountProgram)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw four-spin compiler with its full-space spectral guarantee. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open Matrix
open scoped BigOperators Classical

def rawBondMatrix (n : ℕ) (b : Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  if hi : b.1 < n then if hj : b.2.1 < n then
    (b.2.2:ℂ) • sourceHeisenbergMatrix n ⟨b.1,hi⟩ ⟨b.2.1,hj⟩ else 0 else 0

def rawMatrix (n : ℕ) (out : List Bond × ℚ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (out.1.map (rawBondMatrix n)).sum+out.2 • 1

theorem compile_valid {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : Bond) (hb : b ∈ (compile (n,N,packed t J)).1) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 :=
  fullBonds_valid (bits (n,N,packed t J)) (scale N (packed t J)) t J b hb

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing literal rational four-spin compiler applied to the actual
ordered X/Z words. Its input list preserves term and endpoint order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawBlock
open scoped BigOperators Classical

def output {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ) :=
  QuantumRawExchange.compile (n,N,QuantumRawExchange.packed (terms xs w) J)

theorem output_valid {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (output N xs w J).1) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 :=
  QuantumRawExchange.compile_valid N (terms xs w) J b hb

end ContinuumCoulomb.QuantumOrderedRawBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of the actual ordered sparse labels into the literal raw
X/Z instructions, including the explicit finite relabeling of their energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped BigOperators Classical

variable {ι κ : Type} {n m : ℕ}

theorem packed_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) :
    (table e (index q) xs w J).map QuantumOrderedRawPacking.value =
      QuantumRawExchange.packed (QuantumOrderedRawBlock.terms
        (numberedSites q e xs) (numberedWord q e w)) (fun i => J (e i)) := by
  simp only [table,List.map_ofFn,Function.comp_def,QuantumRawExchange.packed]
  apply congrArg List.ofFn
  funext i
  rw [tag_numbered]
  exact QuantumOrderedRawPacking.value_pack _ _ _

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal six-local sparse-word compiler followed by the rational
four-spin compiler.  Its only input is a precision, a unary qubit count,
and the ordered rational sparse-word list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open ExactQuantumFactoring.BitStackProgram QuantumOrderedLabelFamily
open QuantumOrderedLabelTable
open scoped Classical

def output : Input → List MediatorListProgram.Bond × ℚ :=
  QuantumRawExchange.compile ∘ rawInput

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

theorem output_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    output (N,n,table e (index q) xs w J) =
      QuantumOrderedRawBlock.output N
        (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
        (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
        (fun i => finalCoefficient J N (terms6 e i)) := by
  unfold output rawInput outputCount rawEntries labelEntries classify
  simp only [Function.comp_apply]
  simp only [QuantumOrderedLabelTable.output_table q e xs w J hlen hx N]
  rw [packed_table]
  rfl

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientEnvelopeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs for the logical and physical coefficient bounds.
The only arguments are qubit count, term count, initial magnitude and precision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientEnvelopeProgram
open ExactQuantumFactoring.BitStackProgram

noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)
noncomputable def constant {α : Type} (ea : α → List Bool) (n : ℕ) :
    Procedure ea unaryCode (fun _ => n) := Procedure.constant ea unaryCode n
noncomputable def square {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^2) :=
  (mul p p).congrFun (by intro x; exact (pow_two _).symm)
noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (square p) p).congrFun (by intro x; exact (pow_succ _ 2).symm)
noncomputable def fourth {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^4) :=
  (square (square p)).congrFun (by intro x; simp only [← pow_mul])

noncomputable opaque weightProgram {α : Type} {ea : α → List Bool} {R B : α → ℕ}
    (pr : Procedure ea unaryCode R) (pb : Procedure ea unaryCode B) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.weightNat (R x) (B x)) := by
  let c := constant ea
  exact (add (add (add (add (add (cube pr) (mul (square pr) pb)) (square pr))
    (mul pr (add (c 1) (square pb)))) (c 1)) (square pb)).congrFun (by intro x; rfl)

noncomputable opaque logicalScaleProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.scaleNat (m x) (B x) (N x)) := by
  let c := constant ea
  exact (mul (mul (c 8) (fourth (mul (c 4) (add (c 1)
    (mul pm (square (add (c 1) pb))))))) pn).congrFun (by intro x; rfl)

noncomputable opaque stepProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.stepNat (m x) (B x) (N x)) :=
  weightProgram (logicalScaleProgram pm pb pn) pb

noncomputable def logicalProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) (k : ℕ) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.pipelineNat (m x) (B x) (N x) k) := by
  induction k with
  | zero => exact pb
  | succ k ih => exact stepProgram (mul (constant ea 3136) pm) ih pn

noncomputable opaque rawBudgetProgram {α : Type} {ea : α → List Bool} {m B : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.budgetNat (m x) (B x)) := by
  let c := constant ea
  let s := add pm (mul pm pb)
  exact (add (add (c 1) (mul (c 2000000) s)) (square (mul (c 7056) s))).congrFun
    (by intro x; rfl)

noncomputable opaque rawScaleProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.scaleNat (m x) (B x) (N x)) :=
  mul (mul (constant ea 9) (cube (rawBudgetProgram pm pb))) pn

noncomputable opaque rawOutputProgram {α : Type} {ea : α → List Bool} {n m B N : α → ℕ}
    (pc : Procedure ea unaryCode n) (pm : Procedure ea unaryCode m)
    (pb : Procedure ea unaryCode B) (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.outputNat (n x) (m x) (B x) (N x)) := by
  let c := constant ea
  let r := rawScaleProgram pm pb pn
  exact (add (add (add (mul (add (mul (c 6) pc) (c 1)) (square r))
    (mul (mul (c 3920) r) (add (c 1) pb)))
      (mul (add (mul (c 685600) pm) (c 26000)) pb)) (c 1)).congrFun (by intro x; rfl)

def inputCode : Input → List Bool := QuantumCoefficientPrograms.latticeInputCode

noncomputable opaque program : Procedure inputCode unaryCode value := by
  let n := Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let rest := Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let m := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp rest
  let bn := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp rest
  let b := (Procedure.first unaryCode unaryCode).comp bn
  let p := (Procedure.second unaryCode unaryCode).comp bn
  exact rawOutputProgram (add n (mul (constant inputCode 3717) m))
    (mul (constant inputCode 12544) m) (logicalProgram m b p 6) p

end ContinuumCoulomb.QuantumCoefficientEnvelopeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source cells, internal visits and crossing cells determine every
routing permission. These tests inspect finite encoded lists, including both
orientations of each internal port pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumFiniteMembership

def visitCode : Visit → List Bool := prodCode pairCode pairCode
def tableCode : Table → List Bool :=
  prodCode (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode))
def inputCode : (Table × Pair) → List Bool := prodCode tableCode pairCode

def allowed (t : Table) : QMACellRouteBody → Bool
  | .ray p _ => decide (p ∈ t.1) && !decide (p ∈ t.2.2)
  | .pair p e => !decide (p ∈ t.2.2) &&
      decide ((p,((qmaCellPairLeft e).val,(qmaCellPairRight e).val)) ∈ t.2.1)
  | .patch p _ => decide (p ∈ t.2.2)
  | .corridor p a b c => decide (b = decide (p ∈ t.2.2)) &&
      decide (c = decide (qmaGridNeighbor p a ∈ t.2.2))

noncomputable opaque cellProgram : Procedure inputCode pairCode Prod.snd := Procedure.second _ _
noncomputable opaque tableProgram : Procedure inputCode tableCode Prod.fst := Procedure.first _ _
noncomputable opaque sourcesProgram : Procedure inputCode (listCode pairCode) (fun x => x.1.1) :=
  (Procedure.first _ _).comp tableProgram
noncomputable opaque visitsProgram : Procedure inputCode (listCode visitCode) (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp tableProgram)
noncomputable opaque crossingsProgram : Procedure inputCode (listCode pairCode) (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp tableProgram)

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Crossing cells are detected from the two opposite port pairs in the finite
visit table. No search over a proof-level finite type is needed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable
namespace QuantumRoutingTable

def crossingTest (t : Table) (p : Pair) : Bool :=
  decide ((p,(0,2)) ∈ t.2.1) && decide ((p,(1,3)) ∈ t.2.1)

def computedCrossings (t : Table) : List Pair :=
  (t.2.1.map Prod.fst).filter (crossingTest t)

 theorem mem_computedCrossings (t : Table) (p : Pair) :
    p ∈ computedCrossings t ↔ crossingTest t p = true := by
  simp only [computedCrossings,List.mem_filter]
  constructor
  · exact And.right
  · intro h
    have hv : (p,(0,2)) ∈ t.2.1 := by
      have hh : decide ((p,(0,2)) ∈ t.2.1) = true ∧
          decide ((p,(1,3)) ∈ t.2.1) = true := by
        simpa only [crossingTest,Bool.and_eq_true] using h
      exact of_decide_eq_true hh.1
    exact ⟨List.mem_map.mpr ⟨(p,(0,2)),hv,rfl⟩,h⟩

end QuantumRoutingTable
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedRoutingTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compute the crossing list from encoded visits, and preserve exactly the
routing permissions of the geometric construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def computedTable (t : Table) : Table := (t.1,t.2.1,computedCrossings t)

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exchange-graph semantics for the finite bond lists manipulated by
the routing compiler. The scalar offset stays part of the full Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListGraph
open Matrix MediatorListProgram
open scoped BigOperators Classical

def packed (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) : List Bond :=
  List.ofFn fun i => ((G.left (labels.symm i)).val,(G.right (labels.symm i)).val,
    G.weight (labels.symm i))

theorem packed_bounded (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    SourceBondLists.bounded G.n (packed G labels) := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact ⟨(G.left (labels.symm i)).isLt,(G.right (labels.symm i)).isLt⟩

theorem packed_noLoops (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    ∀ e ∈ packed G labels, e.1 ≠ e.2.1 := by
  intro e he h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact G.distinct (labels.symm i) (Fin.ext h)

end ContinuumCoulomb.QuantumListGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal three-edge output for one selected path subdivision. Fresh spin
labels are assigned in the input list order; both path parities are supported. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def parametersCode : Parameters → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode ratCode)
abbrev Input := Parameters × (ℕ × Bond)

def left (x : Input) : Fin 3 → ℕ :=
  ![x.1.1+2*x.2.1,x.2.2.1,x.2.2.2.1]
def right (x : Input) : Fin 3 → ℕ :=
  ![x.1.1+2*x.2.1+1,x.1.1+2*x.2.1,
    x.1.1+2*x.2.1+(if x.1.2.1 then 0 else 1)]
def coefficient (x : Input) (k : Fin 4) : ℚ :=
  QuantumPathCode.coefficients (x.1.2.1,x.1.2.2,x.2.2.2.2) k
def bond (x : Input) (k : Fin 3) : Bond :=
  (left x k,right x k,coefficient x k.castSucc)
def block (x : Input) : List Bond := List.ofFn (bond x)
def offset (x : Input) : ℚ := coefficient x 3

abbrev FamilyInput := Parameters × List Bond
def indexed (x : ℕ × FamilyInput) : Input :=
  (x.2.1,x.1,(x.2.2.drop x.1).headD zeroBond)
def family (x : FamilyInput) : List Bond :=
  ((List.range x.2.length).map (fun i => block (indexed (i,x)))).flatten
def familyOffset (x : FamilyInput) : ℚ :=
  (x.2.map (fun e => offset (x.1,0,e))).sum

theorem block_bounded (x : Input) (r : ℕ) (hi : x.2.1 < r)
    (hl : x.2.2.1 < x.1.1) (hr : x.2.2.2.1 < x.1.1) :
    SourceBondLists.bounded (x.1.1+r*2) (block x) := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  fin_cases k <;> dsimp [bond,left,right]
  all_goals first | omega | (split_ifs <;> omega)

theorem block_noLoops (x : Input) (hl : x.2.2.1 < x.1.1) (hr : x.2.2.2.1 < x.1.1) :
    ∀ e ∈ block x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  fin_cases k <;> dsimp [bond,left,right]
  all_goals omega

theorem indexed_mem (p : Parameters) (xs : List Bond) (i : ℕ) (hi : i < xs.length) :
    (indexed (i,(p,xs))).2.2 ∈ xs := by
  have he : (xs.drop i).headD zeroBond = xs[i] := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
    rfl
  change (xs.drop i).headD zeroBond ∈ xs
  rw [he]
  exact List.getElem_mem hi

theorem family_bounded (x : FamilyInput) (hb : SourceBondLists.bounded x.1.1 x.2) :
    SourceBondLists.bounded (x.1.1+x.2.length*2) (family x) := by
  intro b hb'
  obtain ⟨bs,hbs,hb'⟩ := List.mem_flatten.mp hb'
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  have hsource := hb _ (indexed_mem x.1 x.2 i hi')
  exact block_bounded (indexed (i,x)) x.2.length hi' hsource.1 hsource.2 b hb'

theorem family_noLoops (x : FamilyInput) (hb : SourceBondLists.bounded x.1.1 x.2) :
    ∀ b ∈ family x, b.1 ≠ b.2.1 := by
  intro b hb'
  obtain ⟨bs,hbs,hb'⟩ := List.mem_flatten.mp hb'
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  have hsource := hb _ (indexed_mem x.1 x.2 i hi')
  exact block_noLoops (indexed (i,x)) hsource.1 hsource.2 b hb'

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListBlock
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine ordinary exchange interactions in a crossing gadget, serialized
in a fixed order. Every endpoint and rational coefficient is computed literally. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def sitesCode : Sites → List Bool :=
  prodCode (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)
def crossingCode : Crossing → List Bool := prodCode (prodCode ratCode ratCode) sitesCode
def parametersCode : Parameters → List Bool := prodCode unaryCode ratCode
def inputCode : Input → List Bool := prodCode parametersCode (prodCode unaryCode crossingCode)

def bond (x : Input) (k : Fin 9) : Bond := (left x k,right x k,coefficient x k)
def block (x : Input) : List Bond := List.ofFn (bond x)

noncomputable opaque crossingProgram : Procedure inputCode crossingCode (fun x => x.2.2) :=
  (Procedure.second unaryCode crossingCode).comp (Procedure.second parametersCode _)
noncomputable opaque sitesProgram : Procedure inputCode sitesCode (fun x => x.2.2.2) :=
  (Procedure.second (prodCode ratCode ratCode) sitesCode).comp crossingProgram
noncomputable opaque siteProgram (k : Fin 4) : Procedure inputCode Nat.bits (fun x => site x.2.2.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits Nat.bits).comp
      ((Procedure.first (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.second Nat.bits Nat.bits).comp
      ((Procedure.first (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits Nat.bits).comp
      ((Procedure.second (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.second Nat.bits Nat.bits).comp
      ((Procedure.second (prodCode Nat.bits Nat.bits) _).comp sitesProgram)

noncomputable opaque radiusProgram : Procedure inputCode ratCode (fun x => x.1.2) :=
  (Procedure.second unaryCode ratCode).comp (Procedure.first parametersCode _)

theorem block_bounded (x : Input) (r : ℕ) (hi : x.2.1 < r)
    (hs : ∀ a, site x.2.2.2 a < x.1.1) :
    SourceBondLists.bounded (x.1.1+2*r) (block x) := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  fin_cases k <;> simp [bond,left,right,base,site] at * <;> omega

theorem block_noLoops (x : Input) (hs : ∀ a, site x.2.2.2 a < x.1.1)
    (hinj : Function.Injective (site x.2.2.2)) :
    ∀ e ∈ block x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  have h01 := hinj.ne (by decide : (0 : Fin 4) ≠ 1)
  have h03 := hinj.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 := hinj.ne (by decide : (1 : Fin 4) ≠ 2)
  have h23 := hinj.ne (by decide : (2 : Fin 4) ≠ 3)
  fin_cases k <;> simp [bond,left,right,base,site] at * <;> omega

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal simultaneous crossing layer: nine bonds and two fresh spins per
crossing, with every scalar correction retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def familyCode : FamilyInput → List Bool := prodCode parametersCode (listCode crossingCode)
def family (x : FamilyInput) : List Bond :=
  ((List.range x.2.length).map (fun i => block (indexed (i,x)))).flatten

theorem family_bounded (x : FamilyInput)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.1) :
    SourceBondLists.bounded (x.1.1+2*x.2.length) (family x) := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  exact block_bounded (indexed (i,x)) x.2.length hi'
    (hs _ (indexed_mem x i hi')) b hb

theorem family_noLoops (x : FamilyInput)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) :
    ∀ e ∈ family x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨bs,hbs,he⟩ := List.mem_flatten.mp he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hc := indexed_mem x i (List.mem_range.mp hi)
  exact block_noLoops (indexed (i,x)) (hs _ hc) (hinj _ hc) e he

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational scale for a simultaneous crossing layer, computed from
its retained coefficients and the two crossing coefficients at each cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

def pairCode : Pair → List Bool := prodCode ratCode ratCode
def inputCode : Input → List Bool :=
  prodCode pairCode (prodCode (listCode ratCode) (listCode pairCode))

end ContinuumCoulomb.QuantumCrossingScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix semantics of the literal path-subdivision block. Its fresh labels
are exactly the two ordinary-spin labels in the singlet gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open Matrix MediatorGraph MediatorListProgram
open scoped BigOperators

def physicalLeft {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) : Fin 3 → Fin (n+r*2) :=
  ![fresh n r i 0,old n r (site 0),old n r (site 1)]

def physicalRight {n r : ℕ} (i : Fin r) (even : Bool) : Fin 3 → Fin (n+r*2) :=
  ![fresh n r i 1,fresh n r i 0,fresh n r i (qmaPathMember even 1)]

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A calibrated selected-subdivision step acting directly on finite bond
lists. The selected list order fixes the labels of every new mediator pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Input := (ℕ × (Bool × (ℚ × ℚ))) × (List Bond × List Bond)
def headCode : (ℕ × (Bool × (ℚ × ℚ))) → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode (prodCode ratCode ratCode))

def scaleInput (x : Input) : QuantumPathScaleProgram.Input :=
  (x.1.2.2,(x.2.1.map (fun e => e.2.2),x.2.2.map (fun e => e.2.2)))
def parameters (x : Input) : QuantumListPathProgram.Parameters :=
  (x.1.1,x.1.2.1,QuantumPathScaleProgram.value (scaleInput x))
def count (x : Input) : ℕ := x.1.1+x.2.2.length*2
def bonds (x : Input) : List Bond := x.2.1++QuantumListPathProgram.family (parameters x,x.2.2)
def constant (x : Input) : ℚ := x.1.2.2.2+QuantumListPathProgram.familyOffset (parameters x,x.2.2)

theorem bonds_bounded (x : Input)
    (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) :
    SourceBondLists.bounded (count x) (bonds x) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨hl,hr⟩ := hk e h
    exact ⟨hl.trans_le (Nat.le_add_right _ _),hr.trans_le (Nat.le_add_right _ _)⟩
  · exact QuantumListPathProgram.family_bounded (parameters x,x.2.2) hs e h

theorem bonds_noLoops (x : Input)
    (hk : ∀ e ∈ x.2.1, e.1 ≠ e.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) : ∀ e ∈ bonds x, e.1 ≠ e.2.1 := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hk e h
  · exact QuantumListPathProgram.family_noLoops (parameters x,x.2.2) hs e h

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select crossing interactions directly from the finite bond tape.
Both orientations contribute to each rational coupling; every other bond is
retained. All scans are literal polynomial programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode
open QuantumCrossingListBlock

def hits (x : Bond × Pair) : Bool :=
  decide ((x.1.1,x.1.2.1)=x.2) || decide ((x.1.2.1,x.1.1)=x.2)
def terminalPair (a : Fin 2) (s : Sites) : Pair :=
  (site s (if a=0 then 0 else 1),site s (if a=0 then 2 else 3))
def pairs (ss : List Sites) : List Pair :=
  (ss.map (fun s => [terminalPair 0 s,terminalPair 1 s])).flatten
def contribution (x : Bond × Pair) : ℚ := if hits x then x.1.2.2 else 0
def weight (x : List Bond × Pair) : ℚ := (x.1.map (fun e => contribution (e,x.2))).sum
def keep (x : List Pair × Bond) : Bool := !(x.1.any (fun p => hits (x.2,p)))
def retained (x : List Pair × List Bond) : List Bond := x.2.filter (fun e => keep (x.1,e))
def crossing (x : List Bond × Sites) : Crossing :=
  ((weight (x.1,terminalPair 0 x.2),weight (x.1,terminalPair 1 x.2)),x.2)
def crossings (x : List Bond × List Sites) : List Crossing := x.2.map (fun s => crossing (x.1,s))

noncomputable opaque terminalProgram (a : Fin 2) : Procedure sitesCode pairCode (terminalPair a) := by
  let input : Procedure sitesCode QuantumCrossingListBlock.inputCode
      (fun s => ((0,0),0,(0,0),s)) :=
    (Procedure.constant sitesCode parametersCode (0,0)).pair
      ((Procedure.constant sitesCode unaryCode 0).pair
        ((Procedure.constant sitesCode (prodCode ratCode ratCode) (0,0)).pair
          (Procedure.identity sitesCode)))
  exact ((siteProgram (if a=0 then 0 else 1)).comp input).pair
    ((siteProgram (if a=0 then 2 else 3)).comp input)

theorem hits_iff (e : Bond) (p : Pair) :
    hits (e,p)=true ↔ (e.1,e.2.1)=p ∨ (e.2.1,e.1)=p := by
  simp only [hits,Bool.or_eq_true,decide_eq_true_eq]

theorem keep_iff (ps : List Pair) (e : Bond) :
    keep (ps,e)=true ↔ ∀ p ∈ ps, (e.1,e.2.1)≠p ∧ (e.2.1,e.1)≠p := by
  simp only [keep,Bool.not_eq_true_eq_eq_false,List.any_eq_false,hits_iff,not_or]

theorem retained_mem (x : List Pair × List Bond) (e : Bond) :
    e ∈ retained x ↔ e ∈ x.2 ∧ ∀ p ∈ x.1, (e.1,e.2.1)≠p ∧ (e.2.1,e.1)≠p := by
  simp only [retained,List.mem_filter,keep_iff]

theorem retained_bounded {n : ℕ} (ps : List Pair) (es : List Bond)
    (hb : SourceBondLists.bounded n es) : SourceBondLists.bounded n (retained (ps,es)) := by
  intro e he
  exact hb e ((retained_mem (ps,es) e).mp he).1

theorem retained_noLoops (ps : List Pair) (es : List Bond)
    (hn : ∀ e ∈ es, e.1 ≠ e.2.1) : ∀ e ∈ retained (ps,es), e.1 ≠ e.2.1 := by
  intro e he
  exact hn e ((retained_mem (ps,es) e).mp he).1

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev GateInput := ℕ × QMAGate
def gateInputCode : GateInput → List Bool := prodCode Nat.bits gateCode

def gateLabels (x : GateInput) : List ℕ :=
  let left := gateLeft x.2 % (x.1+1)
  let right := gateRight x.2 % (x.1+1)
  if gateTag x.2=2 then [left,right] else [left]

def distributedNumber (c : QMACircuit) : QMACircuitQubit c → ℕ :=
  Sum.elim Fin.val (fun i => c.gates.length+2+i.val)

abbrev Input := QMACircuit × ℕ
def inputCode : Input → List Bool := prodCode circuitCode Nat.bits

def gateAt (x : Input) : QMAGate := x.1.gates.getD x.2 (.hadamard 0)

def propagationLabels (x : Input) : List ℕ :=
  [x.2,x.2+1,x.2+2] ++
    (gateLabels (x.1.work,gateAt x)).map (fun i => x.1.gates.length+2+i)

end ContinuumCoulomb.QuantumHistorySiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFirstUseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal first-use indices for the actual circuit gates. The fold stores a
unary index bounded by the gate-list length, including the no-use case. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFirstUseProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev TouchInput := ℕ × (ℕ × QMAGate)
def touchCode : TouchInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits gateCode)

def touches (x : TouchInput) : Bool :=
  decide (gateLeft x.2.2 % (x.1+1)=x.2.1) ||
    decide (gateRight x.2.2 % (x.1+1)=x.2.1)

noncomputable def touchesProgram : Procedure touchCode Procedure.boolCode touches := by
  let work := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let site := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let modulus := Procedure.successor.comp work
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  exact Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (left.pair site)).pair
      (Procedure.binaryEq.comp (right.pair site)))

noncomputable def stepProgram :
    Procedure (prodCode Procedure.boolCode unaryCode) unaryCode step :=
  (Procedure.conditional (Procedure.first Procedure.boolCode unaryCode)
    (Procedure.constant _ unaryCode 0)
    (Procedure.unarySuccessor.comp (Procedure.second Procedure.boolCode unaryCode))).congrFun
      (by intro x; rfl)

noncomputable def foldProgram :
    Procedure (prodCode (listCode Procedure.boolCode) unaryCode) unaryCode
      (fun x => x.1.foldl (fun n b => step (b,n)) x.2) :=
  Procedure.foldList false stepProgram Polynomial.X (by
    intro xs n i
    have h := fold_le (xs.take i) n
    have ht := List.length_take_le' i xs
    have hs := list_length_le_code Procedure.boolCode xs
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)

abbrev Input := QMACircuit × ℕ
def inputCode : Input → List Bool := prodCode circuitCode Nat.bits

def touchList (x : Input) : List Bool :=
  x.1.gates.map (fun g => touches (x.1.work,x.2,g))

def value : Input → ℕ := first ∘ touchList

end ContinuumCoulomb.QuantumFirstUseProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal numeric descriptors for the actual history terms, in the exact
finite-sum order used before time grouping. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def descriptorCode : Descriptor → List Bool := prodCode Nat.bits Nat.bits

def encode (c : QMACircuit) : QMACircuitTerm c → Descriptor
  | .inl i => (0,i.val)
  | .inr (.inl b) => (1,b.val)
  | .inr (.inr (.inl i)) => (2,i.val)
  | .inr (.inr (.inr (.inl _))) => (3,0)
  | .inr (.inr (.inr (.inr t))) => (4,t.val)

theorem atIndex_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    atIndex c.work c.gates.length ((qmaHistoryTermIndex c) a).val = encode c a := by
  rcases a with i | (b | (i | (u | t)))
  · have hi := i.isLt
    change atIndex c.work c.gates.length i.val=(0,i.val)
    simp only [atIndex,ite_eq_left hi]
  · have hb := b.isLt
    change atIndex c.work c.gates.length (c.gates.length+1+b.val)=(1,b.val)
    have h₁ : ¬c.gates.length+1+b.val < c.gates.length+1 := by omega
    have h₂ : c.gates.length+1+b.val < c.gates.length+1+2 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_left h₂,Nat.add_sub_cancel_left]
  · have hi := i.isLt
    change atIndex c.work c.gates.length (c.gates.length+1+(2+i.val))=(2,i.val)
    have h₁ : ¬c.gates.length+1+(2+i.val) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+i.val) < c.gates.length+1+2 := by omega
    have h₃ : c.gates.length+1+(2+i.val) < c.gates.length+1+2+(c.work+1) := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_left h₃]
    congr 1
    omega
  · cases u
    change atIndex c.work c.gates.length (c.gates.length+1+(2+(c.work+1)+0))=(3,0)
    have h₁ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2 := by omega
    have h₃ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2+(c.work+1) := by omega
    have h₄ : c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2+(c.work+1)+1 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃,ite_eq_left h₄]
  · have ht := t.isLt
    change atIndex c.work c.gates.length
      (c.gates.length+1+(2+((c.work+1)+(1+t.val))))=(4,t.val)
    have h₁ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2 := by omega
    have h₃ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2+(c.work+1) := by omega
    have h₄ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2+(c.work+1)+1 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃,ite_eq_right h₄]
    congr 1
    omega

def source (c : QMACircuit) : List Descriptor :=
  (List.range (2*c.gates.length+c.work+5)).map (atIndex c.work c.gates.length)

theorem source_actual (c : QMACircuit) :
    source c=(qmaHistoryTermList c).map (encode c) := by
  apply List.ext_getElem
  · simp only [source,List.length_map,List.length_range,qmaHistoryTermList,List.length_ofFn,
      qmaHistoryReferenceWork]
  · intro i hi hj
    simp only [source,List.getElem_map,List.getElem_range,qmaHistoryTermList,
      List.getElem_ofFn]
    have he := atIndex_actual c ((qmaHistoryTermIndex c).symm ⟨i,by
      simpa only [List.length_map,qmaHistoryTermList,List.length_ofFn] using hj⟩)
    simpa only [Equiv.apply_symm_apply] using he

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDescriptorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial generation of the literal history-term descriptor list.  Only
the circuit's unary work count and gate-list length control enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def indexCode : IndexInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits Nat.bits)

noncomputable opaque timeProgram : Procedure circuitCode unaryCode
    (fun c => c.gates.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength gateCode (.hadamard 0)).comp
    gatesProgram

noncomputable opaque countProgram : Procedure circuitCode unaryCode
    (fun c => 2*c.gates.length+c.work+5) := by
  let twice := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 2).pair timeProgram)
  exact Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (twice.pair workProgram)).pair
      (Procedure.constant circuitCode unaryCode 5))

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def timeValue (c : QMACircuit) (a : Descriptor) : ℕ :=
  if a.1=0 then min a.2 (c.gates.length-1) else
  if a.1=1 then (if a.2=0 then 0 else c.gates.length-1) else
  if a.1=2 then min (QuantumFirstUseProgram.value (c,a.2)) (c.gates.length-1) else
  if a.1=3 then c.gates.length-1 else a.2

def bucket (c : QMACircuit) (t : ℕ) : List Descriptor :=
  (source c).filter (fun a => decide (timeValue c a=t))

def ordered (c : QMACircuit) : List Descriptor :=
  (List.range c.gates.length).flatMap (bucket c)

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) : Scalar :=
  finiteProduct (fun k => if k = i then QuantumFixedPauli.pauli 2 (s k) (t k) else identity (s k) (t k))

def rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) : Scalar :=
  add (mul (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))))
    (mul (neg imaginary) (mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
      (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))))

def pairY (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) : Scalar :=
  mul (mul (QuantumFixedPauli.pauli 2 (s i) (t i)) (QuantumFixedPauli.pauli 2 (s j) (t j)))
    (rat (if ∀ k, k ≠ i → k ≠ j → s k = t k then 1 else 0))

def referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (s t : Fin (n+1) ⊕ ι → Fin 2) : Scalar :=
  mul (mul (rat (1/2)) (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl))))
    (identity (s ∘ Sum.inr) (t ∘ Sum.inr))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal 4096-word family for each actual ordered history term.  The
term type is a product, so its emitted order requires no filtered finite type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicHistory
open scoped BigOperators Classical

abbrev Term (c : QMACircuit) :=
  QMAReferenceTerm (qmaHistoryReferenceWork c) × (Fin 6 → Fin 4)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

def qubitCount (c : QMACircuit) : ℕ :=
  qmaHistoryReferenceWork c+1+((c.gates.length+2)+(c.work+1))

def qubits (c : QMACircuit) : Fin (qubitCount c) ≃ QuantumOrderedSupport.Qubit c :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm))

theorem qubitCount_eq (c : QMACircuit) : qubitCount c=3*c.gates.length+2*c.work+8 := by
  simp only [qubitCount,qmaHistoryReferenceWork]
  omega

def referenceCount (c : QMACircuit) : ℕ :=
  (qmaHistoryReferenceWork c+1)+qmaHistoryReferenceWork c

def reference (c : QMACircuit) :
    Fin (referenceCount c) ≃ QMAReferenceTerm (qmaHistoryReferenceWork c) :=
  finSumFinEquiv.symm

theorem referenceCount_eq (c : QMACircuit) :
    referenceCount c=4*c.gates.length+2*c.work+9 := by
  simp only [referenceCount,qmaHistoryReferenceWork]
  omega

def termCount (c : QMACircuit) : ℕ := referenceCount c*patternCount

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The descriptor compiler computes the very same ordered support labels
as the mathematical local-history construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open QuantumHistorySiteProgram

def distributedLabels (c : QMACircuit) (a : Descriptor) : List ℕ :=
  if a.1=0 then [a.2,a.2+1] else
  if a.1=1 then (if a.2=0 then [0] else [c.gates.length+1]) else
  if a.1=2 then
    let t := QuantumFirstUseProgram.value (c,a.2)
    [t,t+1,c.gates.length+2+a.2] else
  if a.1=3 then [c.gates.length,c.gates.length+2+c.work] else
    propagationLabels (c,a.2)

def referenceWork (c : QMACircuit) : ℕ := 2*c.gates.length+c.work+4

def orderedAt (c : QMACircuit) (i : ℕ) : Descriptor :=
  ((ordered c).drop i).headD (0,0)

def rebitLabels (c : QMACircuit) (i : ℕ) : List ℕ :=
  i :: (distributedLabels c (orderedAt c i)).map (fun j => referenceWork c+1+j)

def referenceLabels (c : QMACircuit) (i : ℕ) : List ℕ :=
  if i < referenceWork c+1 then rebitLabels c i else
    [i-(referenceWork c+1),i-(referenceWork c+1)+1]

def supportLabels (c : QMACircuit) (i : ℕ) : List ℕ := (referenceLabels c i).dedup

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptorProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program for the exact time-grouped descriptor list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev TimeInput := QMACircuit × Descriptor
def timeCode : TimeInput → List Bool := prodCode circuitCode descriptorCode

abbrev BucketInput := QMACircuit × ℕ
def bucketCode : BucketInput → List Bool := prodCode circuitCode Nat.bits
abbrev ChunkInput := BucketInput × Descriptor
def chunkCode : ChunkInput → List Bool := prodCode bucketCode descriptorCode

def chunk (x : ChunkInput) : List Descriptor :=
  if timeValue x.1.1 x.2=x.1.2 then [x.2] else []

theorem chunks_eq (c : QMACircuit) (t : ℕ) (xs : List Descriptor) :
    (xs.map (fun d => chunk ((c,t),d))).flatten =
      xs.filter (fun d => decide (timeValue c d=t)) := by
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    simp only [List.map_cons,List.flatten_cons,ih,List.filter_cons]
    by_cases h : timeValue c d=t
    · simp [chunk,h]
    · simp [chunk,h]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial programs for the exact numeric support lists of every
time-ordered rebit term and reference edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev ReferenceInput := QMACircuit × ℕ
def referenceCode : ReferenceInput → List Bool := prodCode circuitCode Nat.bits

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))

open QuantumOrderedSupport
open scoped Classical

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryBitProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

def dataCode : Data → List Bool :=
  prodCode (listCode Nat.bits) (prodCode (listCode Nat.bits) (listCode Nat.bits))
def queryCode : Query → List Bool := prodCode Nat.bits dataCode

noncomputable opaque allProgram :
    Procedure (listCode Procedure.boolCode) Procedure.boolCode allBits := by
  let p := Procedure.foldList false Procedure.boolAnd (Polynomial.C 1) (by
    intro xs b i
    norm_num [Procedure.boolCode])
  exact (p.comp ((Procedure.identity (listCode Procedure.boolCode)).pair
    (Procedure.constant (listCode Procedure.boolCode) Procedure.boolCode true))).congrFun
      (by intro xs; simp only [Function.comp_apply,id_eq,fold_and,Bool.true_and,allBits])

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

def clockRow (c : QMACircuit) (d : Data) (i : ℕ) : Fin 2 :=
  row d (referenceWork c+1+i)

def workRow (c : QMACircuit) (d : Data) (i : ℕ) : Fin 2 :=
  row d (referenceWork c+1+(c.gates.length+2)+i)

def readRow (c : QMACircuit) (d : Data) : QMACircuitQubit c → Fin 2 :=
  fun q => row d (QuantumOrderedSupport.siteNumber c (.inr q))

def readColumn (c : QMACircuit) (d : Data) : QMACircuitQubit c → Fin 2 :=
  fun q => column d (QuantumOrderedSupport.siteNumber c (.inr q))

def weight (c : QMACircuit) (a : Descriptor) (d : Data) : ℚ :=
  if a.1=0 then
    (if clockRow c d a.2=0 ∧ clockRow c d (a.2+1)=1 then 1 else 0) else
  if a.1=1 then
    (if a.2=0 then (if clockRow c d 0=1 then 0 else 1)
      else (if clockRow c d (c.gates.length+1)=0 then 0 else 1)) else
  if a.1=2 then
    let time := QuantumFirstUseProgram.value (c,a.2)
    if clockRow c d time=1 ∧ clockRow c d (time+1)=0 ∧
        c.witness ≤ a.2 ∧ workRow c d a.2≠0 then 14 else 0 else
  if a.1=3 then
    (if clockRow c d c.gates.length=1 ∧ workRow c d c.work≠1 then 1 else 0) else 0

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar-register evaluation of the diagonal history descriptors. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumCircuitCode QuantumHistoryDescriptors QuantumHistoryBitProgram

abbrev Input := QMACircuit × (Descriptor × Data)
def inputCode : Input → List Bool := prodCode circuitCode (prodCode descriptorCode dataCode)

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.fst := Procedure.first _ _
noncomputable opaque descriptorProgram : Procedure inputCode descriptorCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)
noncomputable opaque tagProgram : Procedure inputCode Nat.bits (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp descriptorProgram
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1.2) :=
  (Procedure.second _ _).comp descriptorProgram
noncomputable opaque timeProgram : Procedure inputCode Nat.bits (fun x => x.1.gates.length) :=
  Procedure.unaryToBits.comp (QuantumHistoryDescriptors.timeProgram.comp circuitProgram)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

abbrev TableInput := QMACircuit × (Descriptor × List ℕ)
def tableCode : TableInput → List Bool :=
  prodCode circuitCode (prodCode descriptorCode (listCode Nat.bits))

def tableData (n : ℕ) (s t : Fin n → Fin 2) (x : TableInput) : QuantumHistoryBitProgram.Data :=
  (x.2.2,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (t i).val))

def table (n : ℕ) (x : TableInput) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => if s=t then rat (weight x.1 x.2.1 (tableData n s t x)) else rat 0

def tableList (n : ℕ) (x : TableInput) : List Scalar := matrixData (table n x)

noncomputable opaque tableEntryInputProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure tableCode inputCode (fun x => (x.1,x.2.1,tableData n s t x)) := by
  let c := Procedure.first circuitCode (prodCode descriptorCode (listCode Nat.bits))
  let rest := Procedure.second circuitCode (prodCode descriptorCode (listCode Nat.bits))
  let a := (Procedure.first descriptorCode (listCode Nat.bits)).comp rest
  let labels := (Procedure.second descriptorCode (listCode Nat.bits)).comp rest
  let rows := Procedure.constant tableCode (listCode Nat.bits) (List.ofFn (fun i => (s i).val))
  let columns := Procedure.constant tableCode (listCode Nat.bits) (List.ofFn (fun i => (t i).val))
  exact c.pair (a.pair (labels.pair (rows.pair columns)))

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unordered endpoint support determines the edge permutation of a
simple graph, including the possible reversal of each edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointRelabel
open scoped Classical

variable {G H : QMARationalExchangeGraph} (vertex : Fin H.n ≃ Fin G.n)
    (hH : H.Simple) (hG : G.Simple)
    (source : ∀ e : H.Edge, ∃ f : G.Edge,
      s(vertex (H.left e),vertex (H.right e))=s(G.left f,G.right f))
    (target : ∀ f : G.Edge, ∃ e : H.Edge,
      s(vertex (H.left e),vertex (H.right e))=s(G.left f,G.right f))

def chooseEdge (e : H.Edge) : G.Edge := Classical.choose (source e)

theorem chooseEdge_spec (e : H.Edge) :
    s(vertex (H.left e),vertex (H.right e))=
      s(G.left (chooseEdge vertex source e),G.right (chooseEdge vertex source e)) :=
  Classical.choose_spec (source e)

include hH in
theorem chooseEdge_injective : Function.Injective (chooseEdge vertex source) := by
  intro e f hef
  by_contra hne
  have hp := (chooseEdge_spec vertex source e).trans
    ((congrArg (fun k => s(G.left k,G.right k)) hef).trans
      (chooseEdge_spec vertex source f).symm)
  rcases Sym2.eq_iff.mp hp with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact (hH e f hne).1 ⟨vertex.injective hl,vertex.injective hr⟩
  · exact (hH e f hne).2 ⟨vertex.injective hl,vertex.injective hr⟩

include hG in
theorem endpoint_injective : Function.Injective (fun e : G.Edge => s(G.left e,G.right e)) := by
  intro e f hef
  by_contra hne
  rcases Sym2.eq_iff.mp hef with h | h
  · exact (hG e f hne).1 h
  · exact (hG e f hne).2 h

include hG target in
theorem chooseEdge_surjective : Function.Surjective (chooseEdge vertex source) := by
  intro f
  obtain ⟨e,he⟩ := target f
  refine ⟨e,endpoint_injective hG ?_⟩
  exact (chooseEdge_spec vertex source e).symm.trans he

def edge : H.Edge ≃ G.Edge := Equiv.ofBijective (chooseEdge vertex source)
  ⟨chooseEdge_injective vertex hH source,chooseEdge_surjective vertex hG source target⟩

end ContinuumCoulomb.QuantumEndpointRelabel

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkDegreeBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree control for many fork centers sharing a retained background graph. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

theorem qmaForkOuter_count {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (houter : Function.Injective (qmaForkOuter site)) (v : Fin n) :
    (∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0) : ℕ)) ≤ 1 := by
  have h := qmaCount_eq_le_one (qmaForkOuter site) houter v
  simpa [qmaForkOuter,Fintype.sum_prod_type,Fin.sum_univ_two] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkBackground
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmWalk_length _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_last _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The part of a fork layer left after its new active center edges are removed. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

def qmaForkBackgroundLeft {n r : ℕ} (left : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) :=
  qmaParallelGraphLeft (qmaForksBaseLeft left site)
    (fun e b => qmaForkOuter site (e,b))

def qmaForkBackgroundRight {n r : ℕ} (right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) :=
  qmaParallelGraphRight (qmaForksBaseRight right site)
    (fun (_ : Fin r) (_ : Fin 2) => (1 : Fin 2))

theorem qmaForkBackground_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (v : Fin n) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (old n r v) = qmaGraphDegree left right v +
        2 * ∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0)) := by
  unfold qmaForkBackgroundLeft qmaForkBackgroundRight
  rw [qmaParallelGraph_old_degree]
  simp only [qmaForksBaseLeft,qmaForksBaseRight]
  rw [qmaGraphDegree_sum]
  have hc : qmaGraphDegree (fun e => site e 1) (fun e => site e 2) v =
      ∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro e _
    have hne : site e 1 ≠ site e 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (hsite e h)
    by_cases h1 : site e 1 = v <;> by_cases h2 : site e 2 = v <;> simp_all
  change qmaGraphDegree left right v + qmaGraphDegree (fun e => site e 1) (fun e => site e 2) v + _ = _
  rw [hc]
  simp only [Fin.sum_univ_two,qmaForkOuter,ite_true, if_true]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide]
  simp only [ite_false, if_false]
  omega

theorem qmaForkBackground_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (fresh n r e b) = if b = 0 then 1 else 3 := by
  unfold qmaForkBackgroundLeft qmaForkBackgroundRight
  rw [qmaParallelGraph_new_degree]
  simp only [Fin.sum_univ_two]
  fin_cases b <;> norm_num

theorem qmaForkBackground_away_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (v : Fin n) (hv : ∀ e, site e 1 ≠ v ∧ site e 2 ≠ v) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (old n r v) = qmaGraphDegree left right v := by
  rw [qmaForkBackground_old_degree left right site hsite]
  simp [hv]

theorem qmaForkBackground_degree_le_three {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (houter : Function.Injective (qmaForkOuter site))
    (hbase : ∀ v, qmaGraphDegree left right v ≤ 3)
    (hport : ∀ e b, qmaGraphDegree left right (qmaForkOuter site (e,b)) ≤ 1)
    (v : Fin (n+r*2)) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site) v ≤ 3 := by
  obtain ⟨v,rfl⟩ := (vertexEquiv n r).surjective v
  rcases v with v | ⟨e,b⟩
  · change qmaGraphDegree (qmaForkBackgroundLeft left site)
      (qmaForkBackgroundRight right site) (old n r v) ≤ 3
    by_cases hp : ∃ e b, qmaForkOuter site (e,b) = v
    · obtain ⟨e,b,rfl⟩ := hp
      rw [qmaForkBackground_old_degree left right site hsite]
      have hc := qmaForkOuter_count site houter (qmaForkOuter site (e,b))
      have hb := hport e b
      omega
    · have hv : ∀ e, site e 1 ≠ v ∧ site e 2 ≠ v := by
        intro e
        constructor
        · intro h
          exact hp ⟨e,0,by simpa [qmaForkOuter] using h⟩
        · intro h
          exact hp ⟨e,1,by simpa [qmaForkOuter] using h⟩
      rw [qmaForkBackground_away_degree left right site hsite v hv]
      exact hbase v
  · change qmaGraphDegree (qmaForkBackgroundLeft left site)
      (qmaForkBackgroundRight right site) (fresh n r e b) ≤ 3
    rw [qmaForkBackground_new_degree]
    split <;> omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmWalk_length _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_last _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd subdivision gives every original incidence its own private fork port. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

theorem qmaOriginalPortCount_eq_degree {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (i : Fin n) :
    qmaOriginalPortCount left right i = qmaGraphDegree left right i := by
  unfold qmaOriginalPortCount
  rw [Fintype.card_subtype]
  have hc : (∑ p : Fin m × Fin 2, if qmaOriginalEndpoint left right p = i then 1 else 0 : ℕ) =
      (Finset.univ.filter (fun p => qmaOriginalEndpoint left right p = i)).card := by simp
  rw [← hc]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,qmaOriginalEndpoint]
  apply Finset.sum_congr rfl
  intro e _
  have h := hneq e
  by_cases hl : left e = i <;> by_cases hr : right e = i <;> simp_all

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered rational data for the degree-three fork compiler. Original centers
retain their numbers. Each pair of active ports receives two consecutive new
spin numbers, and an unpaired port remains active at its original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

abbrev State := ℕ × (List Bond × (ℚ × Groups))

def retained (s : State) : List ℚ :=
  s.2.1.map (fun b => b.2.2) ++ ((s.2.2.2.map unpaired).flatten.map Prod.snd)

def scale (N : ℚ) (s : State) : ℚ :=
  let ps := (catalog s.2.2.2).map Prod.snd
  let B := 3*(retained s |>.map abs).sum+|s.2.2.1|
  let A := 3*(ps.map pairLinear).sum
  let D := B+12*(ps.map pairSquare).sum
  16*(A+D+1)^3*N+4*(A+D+1)+1

def pairBonds (n i : ℕ) (R : ℚ) (p : Pair) : List Bond :=
  [(p.1.1,p.2.1,2*p.1.2*p.2.2),
   (n+2*i,n+2*i+1,R^2),
   (p.1.1,n+2*i+1,2*R*p.1.2),
   (p.2.1,n+2*i+1,2*R*p.2.2)]

def addedBonds (s : State) (R : ℚ) : List Bond :=
  let ps := catalog s.2.2.2
  ((List.range ps.length).map (fun i => pairBonds s.1 i R
    ((ps.drop i).headD (0,((0,0),(0,0)))).2)).flatten

def next (N : ℚ) (s : State) : State :=
  let R := scale N s
  let ps := (catalog s.2.2.2).map Prod.snd
  (s.1+2*pairCount s.2.2.2,
    s.2.1++addedBonds s R,
    s.2.2.1+(ps.map pairOffset).sum+3*(pairCount s.2.2.2:ℚ)*R^2,
    (List.range s.2.2.2.length).map (nextGroup s.1 R s.2.2.2))

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => next N (iterate N k s)

theorem catalog_length (gs : Groups) : (catalog gs).length=pairCount gs := by
  unfold catalog
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,List.length_map,pairs_length]
  change ((List.range gs.length).map (fun i => ((gs.drop i).headD []).length/2)).sum = _
  rw [ExactQuantumFactoring.BitStackProgram.map_range_getD gs [] (fun ps => ps.length/2)]
  rfl

theorem next_centers (N : ℚ) (s : State) : (next N s).2.2.2.length=s.2.2.2.length := by
  simp [next]

theorem next_count (N : ℚ) (s : State) : (next N s).1=s.1+2*pairCount s.2.2.2 := rfl

theorem iterate_centers (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.2.2.length=s.2.2.2.length := by
  induction k with
  | zero => rfl
  | succ k ih => exact (next_centers N (iterate N k s)).trans ih

theorem next_group_length (N : ℚ) (s : State) (i : ℕ) (hi : i < s.2.2.2.length) :
    (groupAt (next N s).2.2.2 i).length=
      (groupAt s.2.2.2 i).length/2+(groupAt s.2.2.2 i).length%2 := by
  change (groupAt ((List.range s.2.2.2.length).map
    (nextGroup s.1 (scale N s) s.2.2.2)) i).length=_
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,nextGroup_length]

theorem iterate_group_length (N : ℚ) (s : State) (k i : ℕ) (hi : i < s.2.2.2.length) :
    (groupAt (iterate N k s).2.2.2 i).length=
      qmaForkDegreeAfter (groupAt s.2.2.2 i).length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate,next_group_length N (iterate N k s) i (by rwa [iterate_centers]),ih]
    rfl

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four literal bonds emitted for one port pair are exactly its
correction, singlet penalty and two outer couplings in the fork Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample

def typedPairBonds (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    List (TypedBond (n+r*2)) :=
  [(old n r a,old n r b,2*J*K),
   (fresh n r e 0,fresh n r e 1,R^2),
   (old n r a,fresh n r e 1,2*R*J),
   (old n r b,fresh n r e 1,2*R*K)]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact active-star matrices of the ordered compiler state. The pairing
identity applies to every matrix entry, including the retained odd port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

def starBonds (i : ℕ) (ps : List Port) : List Bond :=
  ps.map (fun p => (i,p.1,p.2))

def activeBonds (gs : Groups) : List Bond :=
  ((List.range gs.length).map (fun i => starBonds i (groupAt gs i))).flatten

def unpairedBonds (gs : Groups) : List Bond :=
  ((List.range gs.length).map (fun i => starBonds i (unpaired (groupAt gs i)))).flatten

def pairedBonds (gs : Groups) : List Bond :=
  (catalog gs).flatMap (fun p => [(p.1,p.2.1.1,p.2.1.2),(p.1,p.2.2.1,p.2.2.2)])

def matrix (s : State) := rawMatrix s.1 (s.2.1++activeBonds s.2.2.2,s.2.2.1)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained part of a literal fork state has exactly the coefficient
budget and finite exchange matrix used by the parallel-fork estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

def background (s : State) : List Bond := s.2.1++unpairedBonds s.2.2.2

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bond packet emitted for parallel forks has the exact full-space
Hamiltonian used in the calibrated perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def packetBonds {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n) (J K R : ℚ) :
    List MediatorListProgram.Bond :=
  pairBonds n e.val R ((site 1 |>.val,J),(site 2 |>.val,K)) ++
    [((site 0).val,n+2*e.val,R)]

def graphBonds {n r m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℚ) (R : ℚ) :
    List MediatorListProgram.Bond :=
  List.ofFn (fun a => erase (old n r (left a),old n r (right a),w a)) ++
    (List.ofFn (fun e => packetBonds e (site e) (J e) (K e) R)).flatten

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal round is the retained matrix plus the calibrated
five-bond packets, including the newly active center-to-mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

def freshBonds (s : State) (R : ℚ) : List Bond :=
  (List.range (pairCount s.2.2.2)).map (fun e =>
    ((((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).1,s.1+2*e,R))

def packets (s : State) (R : ℚ) : List Bond :=
  ((List.range (pairCount s.2.2.2)).map (fun e =>
    pairBonds s.1 e R (((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).2 ++
      [((((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).1,s.1+2*e,R)])).flatten

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact correspondence between the emitted ordered state and the finite
parallel-fork Hamiltonian. The mediator numbering is the proved prefix index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumAxisSample QuantumRawExchange
open scoped BigOperators Classical

def rawBottom (n : ℕ) (out : List MediatorListProgram.Bond × ℚ) : ℝ :=
  normalizedBottom (rawMatrix n out)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every literal fork round keeps the active ports distinct from one another
and from the original centers. Fresh ports use the injective prefix index;
retained ports inherit the preceding round's separation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem next_validPorts (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2) :
    ValidPorts (next N s).1 (next N s).2.2.2 := by
  constructor
  · rw [next_centers,next_count]
    exact le_trans h.centers (Nat.le_add_right _ _)
  · intro i j
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 i.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hi] using j.isLt
    change (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) i.val) j.val).1 < _
    rw [next_groupAt _ _ _ _ hi]
    exact nextGroup_bounded h (scale N s) i.val j.val hi hj
  · intro i k j
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hk : k.val < s.2.2.2.length := by simpa only [next_centers] using k.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 k.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hk] using j.isLt
    change i.val ≠ (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) k.val) j.val).1
    rw [next_groupAt _ _ _ _ hk]
    exact nextGroup_disjoint h (scale N s) i.val k.val j.val hi hk hj
  · intro i k j l he
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hk : k.val < s.2.2.2.length := by simpa only [next_centers] using k.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 i.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hi] using j.isLt
    have hl : l.val < (nextGroup s.1 (scale N s) s.2.2.2 k.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hk] using l.isLt
    change (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) i.val) j.val).1=
      (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) k.val) l.val).1 at he
    rw [next_groupAt _ _ _ _ hi,next_groupAt _ _ _ _ hk] at he
    obtain ⟨hik,hjl⟩ := nextGroup_injective h (scale N s) i.val k.val j.val l.val
      hi hk hj hl he
    exact ⟨Fin.ext hik,hjl⟩

theorem iterate_validPorts (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2)
    (k : ℕ) : ValidPorts (iterate N k s).1 (iterate N k s).2.2.2 := by
  induction k with
  | zero => exact h
  | succ k ih => exact next_validPorts N _ ih

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextBackground
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded, loop-free ordinary bonds survive the actual list transformation.
Together with port separation this supplies every hypothesis of the next
full-space fork comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem pairBonds_valid (n r i a b : ℕ) (R J K : ℚ)
    (hi : i < r) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (e : Bond) (he : e ∈ pairBonds n i R ((a,J),(b,K))) :
    e.1 < n+2*r ∧ e.2.1 < n+2*r ∧ e.1 ≠ e.2.1 := by
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem addedBonds_valid (s : State) (h : ValidPorts s.1 s.2.2.2) (R : ℚ)
    (b : Bond) (hb : b ∈ addedBonds s R) :
    b.1 < s.1+2*pairCount s.2.2.2 ∧ b.2.1 < s.1+2*pairCount s.2.2.2 ∧
      b.1 ≠ b.2.1 := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' : i < pairCount s.2.2.2 := by
    simpa only [catalog_length] using List.mem_range.mp hi
  rw [catalog_actualSite h ⟨i,hi'⟩] at hb
  have hne : actualSite h ⟨i,hi'⟩ 1 ≠ actualSite h ⟨i,hi'⟩ 2 := by
    intro he
    have := actualSite_injective h ⟨i,hi'⟩ he
    norm_num [Fin.ext_iff] at this
  exact pairBonds_valid s.1 (pairCount s.2.2.2) i _ _ R _ _ hi'
    (actualSite h ⟨i,hi'⟩ 1).isLt (actualSite h ⟨i,hi'⟩ 2).isLt
    (fun he => hne (Fin.ext he)) b hb

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal odd subdivision that initializes the bounded-degree compiler.
Each edge owns two consecutive mediator sites, and each original vertex keeps
the increasing list of its incident mediator ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

def initialBond (bs : List Bond) (j : ℕ) : Bond :=
  (bs.drop (j/2)).headD (0,0,0)

def initialEndpoint (bs : List Bond) (j : ℕ) : ℕ :=
  if j%2=0 then (initialBond bs j).1 else (initialBond bs j).2.1

def initialWeight (bs : List Bond) (R : ℚ) (j : ℕ) : ℚ :=
  if j%2=0 then R else 2*R*(initialBond bs j).2.2

def initialIndices (bs : List Bond) (i : ℕ) : List ℕ :=
  (List.range (2*bs.length)).filter (fun j => decide (initialEndpoint bs j=i))

def initialGroup (n : ℕ) (bs : List Bond) (R : ℚ) (i : ℕ) : List Port :=
  (initialIndices bs i).map (fun j => (n+j,initialWeight bs R j))

def initialScale (N : ℚ) (bs : List Bond) (c : ℚ) : ℚ :=
  let A := 3*(bs.map (fun b => 1+2*|b.2.2|)).sum
  let B := |c|+4*(bs.map (fun b => (1+|b.2.2|)^2)).sum
  16*(A+B+1)^3*N+4*(A+B+1)+1

def initial (n : ℕ) (bs : List Bond) (c N : ℚ) : State :=
  let R := initialScale N bs c
  (n+2*bs.length,
    (List.range bs.length).map (fun e => (n+2*e,n+2*e+1,R^2)),
    c+(bs.map (fun b => 3/4+3*b.2.2^2)).sum+3*(bs.length:ℚ)*R^2,
    (List.range n).map (initialGroup n bs R))

theorem initialGroup_portAt (n : ℕ) (bs : List Bond) (R : ℚ) (i j : ℕ)
    (hj : j < (initialIndices bs i).length) :
    portAt (initialGroup n bs R i) j=
      (n+(initialIndices bs i)[j],initialWeight bs R (initialIndices bs i)[j]) := by
  rw [portAt_eq_getElem _ _ (by simpa only [initialGroup,List.length_map] using hj)]
  simp only [initialGroup,List.getElem_map]

theorem initialIndices_mem (bs : List Bond) (i j : ℕ) (hj : j ∈ initialIndices bs i) :
    j < 2*bs.length ∧ initialEndpoint bs j=i := by
  simpa only [initialIndices,List.mem_filter,List.mem_range,decide_eq_true_eq] using hj

theorem initialIndices_nodup (bs : List Bond) (i : ℕ) : (initialIndices bs i).Nodup :=
  (List.nodup_range : (List.range (2*bs.length)).Nodup).filter _

theorem initialGroup_bounded (n : ℕ) (bs : List Bond) (R : ℚ) (i j : ℕ)
    (hj : j < (initialGroup n bs R i).length) :
    (portAt (initialGroup n bs R i) j).1 < n+2*bs.length := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  rw [initialGroup_portAt n bs R i j hj']
  have hm := initialIndices_mem bs i _ (List.getElem_mem hj')
  dsimp only
  omega

theorem initialGroup_disjoint (n : ℕ) (bs : List Bond) (R : ℚ) (k i j : ℕ)
    (hk : k < n) (hj : j < (initialGroup n bs R i).length) :
    k ≠ (portAt (initialGroup n bs R i) j).1 := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  rw [initialGroup_portAt n bs R i j hj']
  dsimp only
  omega

theorem initialGroup_injective (n : ℕ) (bs : List Bond) (R : ℚ) (i k j l : ℕ)
    (hj : j < (initialGroup n bs R i).length)
    (hl : l < (initialGroup n bs R k).length)
    (he : (portAt (initialGroup n bs R i) j).1=
      (portAt (initialGroup n bs R k) l).1) : i=k ∧ j=l := by
  have hj' : j < (initialIndices bs i).length := by
    simpa only [initialGroup,List.length_map] using hj
  have hl' : l < (initialIndices bs k).length := by
    simpa only [initialGroup,List.length_map] using hl
  rw [initialGroup_portAt n bs R i j hj',initialGroup_portAt n bs R k l hl'] at he
  have he' : (initialIndices bs i)[j]=(initialIndices bs k)[l] := by
    dsimp only at he
    omega
  have hmj := (initialIndices_mem bs i _ (List.getElem_mem hj')).2
  have hml := (initialIndices_mem bs k _ (List.getElem_mem hl')).2
  have hik : i=k := by rw [he',hml] at hmj; exact hmj.symm
  refine ⟨hik,?_⟩
  subst k
  exact (List.Nodup.getElem_inj_iff (initialIndices_nodup bs i) (hi := hj') (hj := hl')).1 he'

theorem initial_validPorts (n : ℕ) (bs : List Bond) (c N : ℚ) :
    ValidPorts (initial n bs c N).1 (initial n bs c N).2.2.2 := by
  have hg (i : ℕ) (hi : i < n) :
      groupAt (initial n bs c N).2.2.2 i=initialGroup n bs (initialScale N bs c) i := by
    change groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i=_
    rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
      List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some,List.getElem_map,List.getElem_range]
  have hlen : (initial n bs c N).2.2.2.length=n := by simp only [initial,List.length_map,List.length_range]
  constructor
  · rw [hlen]
    exact Nat.le_add_right _ _
  · intro i j
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) i.val).length := by
      simpa only [hg i.val hi] using j.isLt
    change (portAt (groupAt (initial n bs c N).2.2.2 i.val) j.val).1 < n+2*bs.length
    simpa only [hg i.val hi] using initialGroup_bounded n bs _ i.val j.val hj
  · intro i k j
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hk : k.val < n := by simpa only [hlen] using k.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) k.val).length := by
      simpa only [hg k.val hk] using j.isLt
    simpa only [hg k.val hk] using initialGroup_disjoint n bs _ i.val k.val j.val hi hj
  · intro i k j l he
    have hi : i.val < n := by simpa only [hlen] using i.isLt
    have hk : k.val < n := by simpa only [hlen] using k.isLt
    have hj : j.val < (initialGroup n bs (initialScale N bs c) i.val).length := by
      simpa only [hg i.val hi] using j.isLt
    have hl : l.val < (initialGroup n bs (initialScale N bs c) k.val).length := by
      simpa only [hg k.val hk] using l.isLt
    have he' : (portAt (initialGroup n bs (initialScale N bs c) i.val) j.val).1=
        (portAt (initialGroup n bs (initialScale N bs c) k.val) l.val).1 := by
      simpa only [hg i.val hi,hg k.val hk] using he
    obtain ⟨hik,hjl⟩ := initialGroup_injective n bs _ i.val k.val j.val l.val hj hl he'
    exact ⟨Fin.ext hik,hjl⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialIndices_sum {M : Type*} [AddCommMonoid M] (bs : List Bond) (i : ℕ)
    (f : ℕ → M) : ((initialIndices bs i).map f).sum =
      ((List.range (2*bs.length)).map (fun j =>
        if initialEndpoint bs j=i then f j else 0)).sum := by
  unfold initialIndices
  generalize List.range (2*bs.length)=xs
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases h : initialEndpoint bs j=i <;> simp [h,ih]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The even and odd entries in the initial endpoint table are precisely
the two couplings belonging to each physical singlet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_pair (bs : List Bond) (e : Fin bs.length) (b : Fin 2) :
    initialBond bs (2*e.val+b.val)=bs[e.val] := by
  have hd : (2*e.val+b.val)/2=e.val := by have := b.isLt; omega
  simp only [initialBond,hd,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem e.isLt,Option.getD_some]

theorem initialEndpoint_even (bs : List Bond) (e : Fin bs.length) :
    initialEndpoint bs (2*e.val)=bs[e.val].1 := by
  have hm : (2*e.val)%2=0 := by omega
  simp only [initialEndpoint,hm,ite_true, if_true]
  simpa only [Fin.val_zero,add_zero] using
    congrArg Prod.fst (initialBond_pair bs e 0)

theorem initialEndpoint_odd (bs : List Bond) (e : Fin bs.length) :
    initialEndpoint bs (2*e.val+1)=bs[e.val].2.1 := by
  have hm : (2*e.val+1)%2≠0 := by omega
  simp only [initialEndpoint,hm,ite_false, if_false]
  exact congrArg (fun p : Bond => p.2.1) (initialBond_pair bs e 1)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact matrix semantics of the emitted initial singlet/port lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

theorem initial_groupAt (n : ℕ) (bs : List Bond) (R : ℚ) (i : ℕ) (hi : i < n) :
    groupAt ((List.range n).map (initialGroup n bs R)) i=initialGroup n bs R i := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial emitted couplings are the simultaneous odd-path singlet
Hamiltonian used by the already proved full-space perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def initialPhysicalBonds {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℚ)
    (R : ℚ) : List MediatorListProgram.Bond :=
  (List.ofFn (fun e => erase (fresh n m e 0,fresh n m e 1,R^2)))++
    (List.ofFn (fun e => [erase (old n m (left e),fresh n m e 0,R),
      erase (old n m (right e),fresh n m e 1,2*R*J e)])).flatten

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering the actual initial bond list gives exactly the typed physical
singlet Hamiltonian, including its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

def initialSourceBonds (n : ℕ) (bs : List Bond) (R : ℚ) : List Bond :=
  (List.range bs.length).map (fun e => (n+2*e,n+2*e+1,R^2))++
    activeBonds ((List.range n).map (initialGroup n bs R))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial scale has exactly the coefficient budget used in
the rational simultaneous path estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initial_list_sum {M : Type*} [AddCommMonoid M] (bs : List Bond) (f : Bond → M) :
    (bs.map f).sum=∑ e : Fin bs.length, f (bs.get e) := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map bs f).symm

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence counts for the literal ordinary-bond list. The four newly emitted
bonds have exactly the graph used by the physical fork degree estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph MediatorListProgram
open scoped BigOperators Classical

def degree (bs : List Bond) (v : ℕ) : ℕ :=
  (bs.map (fun b => incident v b.1 b.2.1)).sum

theorem graph_degree_incident {ν : Type*} [Fintype ν] {n : ℕ}
    (left right : ν → Fin n) (v : Fin n) :
    qmaGraphDegree left right v=∑ e, incident v.val (left e).val (right e).val := by
  unfold qmaGraphDegree
  apply Finset.sum_congr rfl
  intro e _
  simp only [incident,Fin.ext_iff]

theorem degree_append (bs cs : List Bond) (v : ℕ) :
    degree (bs++cs) v=degree bs v+degree cs v := by
  simp only [degree,List.map_append,List.sum_append]

theorem degree_eq_graph (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (v : Fin n) :
    degree bs v.val=qmaGraphDegree (SourceBondLists.bonds n bs hb).left
      (SourceBondLists.bonds n bs hb).right v := by
  unfold degree
  rw [initial_list_sum]
  rw [graph_degree_incident]
  rfl

theorem added_sum {M : Type*} [AddCommMonoid M] (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (R : ℚ) (f : Bond → M) :
    ((addedBonds s R).map f).sum = ∑ e : Fin (pairCount s.2.2.2),
      (f ((actualSite hs e 1).val,(actualSite hs e 2).val,
          2*actualJ s.2.2.2 e*actualK s.2.2.2 e)+
       f (s.1+2*e.val,s.1+2*e.val+1,R^2)+
       f ((actualSite hs e 1).val,s.1+2*e.val+1,2*R*actualJ s.2.2.2 e)+
       f ((actualSite hs e 2).val,s.1+2*e.val+1,2*R*actualK s.2.2.2 e)) := by
  simp only [addedBonds,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def,
    catalog_length,range_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [catalog_actualSite hs e]
  simp only [pairBonds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  ac_rfl

theorem next_ordinary_degree (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (v : Fin (s.1+pairCount s.2.2.2*2)) :
    degree (next N s).2.1 v.val =
      qmaGraphDegree
        (qmaForkBackgroundLeft (SourceBondLists.bonds s.1 s.2.1 hb).left (actualSite hs))
        (qmaForkBackgroundRight (SourceBondLists.bonds s.1 s.2.1 hb).right (actualSite hs)) v := by
  change degree (s.2.1++addedBonds s (scale N s)) v.val=_
  rw [degree_append]
  unfold degree
  rw [initial_list_sum,added_sum s hs]
  rw [graph_degree_incident]
  simp only [qmaForkBackgroundLeft,qmaForkBackgroundRight,
    Fintype.sum_sum_type,Fintype.sum_prod_type,qmaParallelGraphLeft,qmaParallelGraphRight,
    qmaForksBaseLeft,qmaForksBaseRight,Sum.elim_inl,Sum.elim_inr,
    qmaForkOuter,Fin.sum_univ_two,ite_true, if_true,show (1:Fin 2) ≠ 0 by decide,ite_false, if_false,
    SourceBondLists.bonds,MediatorIteration.old_val,MediatorIteration.fresh_val,
    Fin.val_zero,Fin.val_one,Nat.add_zero,Finset.sum_add_distrib]
  simp only [Nat.mul_comm]
  omega

structure DegreeBounds (s : State) : Prop where
  ordinary : ∀ v : Fin s.1, degree s.2.1 v.val ≤ 3
  center : ∀ i, i < s.2.2.2.length → degree s.2.1 i=0
  port : ∀ (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length),
    degree s.2.1 (portAt (groupAt s.2.2.2 i.val) j.val).1 ≤ 1

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial mediator singlets have degree one and avoid every original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

def singletBonds (n m : ℕ) (R : ℚ) : List Bond :=
  (List.range m).map (fun e => (n+2*e,n+2*e+1,R^2))

theorem singlet_degree_le_one (n m : ℕ) (R : ℚ) (v : ℕ) :
    degree (singletBonds n m R) v ≤ 1 := by
  have hinj : Function.Injective (fun p : Fin m × Fin 2 => n+2*p.1.val+p.2.val) := by
    rintro ⟨e,b⟩ ⟨f,c⟩ h
    change n+2*e.val+b.val=n+2*f.val+c.val at h
    have hb := b.isLt
    have hc := c.isLt
    apply Prod.ext
    · apply Fin.ext
      change e.val=f.val
      omega
    · apply Fin.ext
      change b.val=c.val
      omega
  have hh := qmaCount_eq_le_one _ hinj v
  have he : degree (singletBonds n m R) v=
      ∑ p : Fin m × Fin 2, if n+2*p.1.val+p.2.val=v then 1 else 0 := by
    simp only [degree,incident,singletBonds,List.map_map,Function.comp_def,range_sum,
      Fintype.sum_prod_type,Fin.sum_univ_two,Nat.add_zero,Fin.val_zero,Fin.val_one]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> omega
  rw [he]
  exact hh

theorem singlet_degree_center (n m : ℕ) (R : ℚ) (v : ℕ) (hv : v<n) :
    degree (singletBonds n m R) v=0 := by
  simp only [degree,incident,singletBonds,List.map_map,Function.comp_def,range_sum]
  apply Finset.sum_eq_zero
  intro e _
  have h0 : n+2*e.val ≠ v := by omega
  have h1 : n+2*e.val+1 ≠ v := by omega
  simp only [h0,h1,false_or,ite_false, if_false]

theorem initial_degreeBounds (n : ℕ) (bs : List Bond) (c N : ℚ) :
    DegreeBounds (initial n bs c N) where
  ordinary := by
    intro v
    exact (singlet_degree_le_one n bs.length (initialScale N bs c) v.val).trans (by decide)
  center := by
    intro i hi
    have hi' : i<n := by simpa only [initial,List.length_map,List.length_range] using hi
    exact singlet_degree_center n bs.length (initialScale N bs c) i hi'
  port := by
    intro i j
    exact singlet_degree_le_one n bs.length (initialScale N bs c) _

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextDegree
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmWalk_length _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_last _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_zero _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal fork transformation preserves the ordinary degree bound,
isolated centers, and degree-one active ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph
open scoped Classical

theorem next_degreeBounds (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hd : DegreeBounds s) :
    DegreeBounds (next N s) := by
  let left := (SourceBondLists.bonds s.1 s.2.1 hb).left
  let right := (SourceBondLists.bonds s.1 s.2.1 hb).right
  have hbase (v : Fin s.1) : qmaGraphDegree left right v ≤ 3 := by
    rw [← degree_eq_graph]
    exact hd.ordinary v
  have hport (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
      qmaGraphDegree left right (qmaForkOuter (actualSite hs) (e,b)) ≤ 1 := by
    rw [← degree_eq_graph,actual_outer_eq]
    exact hd.port (outerPort s.2.2.2 (e,b)).1 (outerPort s.2.2.2 (e,b)).2
  refine ⟨?_,?_,?_⟩
  · intro v
    have hv : v.val < s.1+pairCount s.2.2.2*2 := by have := v.isLt; change _ < s.1+2*pairCount s.2.2.2 at this; omega
    rw [next_ordinary_degree N s hs hb ⟨v.val,hv⟩]
    exact qmaForkBackground_degree_le_three left right (actualSite hs)
      (actualSite_injective hs) (actual_outer_injective hs) hbase hport _
  · intro i hi
    have hi' : i < s.2.2.2.length := by simpa only [next_centers] using hi
    let v : Fin s.1 := ⟨i,lt_of_lt_of_le hi' hs.centers⟩
    have hv := next_ordinary_degree N s hs hb (old s.1 (pairCount s.2.2.2) v)
    simp only [MediatorIteration.old_val] at hv
    change degree (next N s).2.1 v.val=0
    rw [hv]
    rw [qmaForkBackground_away_degree left right (actualSite hs)
      (actualSite_injective hs) v (actual_outer_away_center hs ⟨i,hi'⟩)]
    rw [← degree_eq_graph]
    exact hd.center i hi'
  · intro i j
    have hj₀ := j.isLt
    generalize hkj : j.val=k at hj₀ ⊢
    clear hkj j
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hgroup : groupAt (next N s).2.2.2 i.val=nextGroup s.1 (scale N s) s.2.2.2 i.val :=
      next_groupAt s.1 (scale N s) s.2.2.2 i.val hi
    have hj : k<(groupAt s.2.2.2 i.val).length/2+(groupAt s.2.2.2 i.val).length%2 := by
      have h := hj₀
      rw [hgroup,nextGroup_length] at h
      exact h
    rw [hgroup]
    by_cases hf : k<(groupAt s.2.2.2 i.val).length/2
    · rw [nextGroup_portAt_fresh _ _ _ _ _ hf]
      let p : LocalPair s.2.2.2 := ⟨⟨i.val,hi⟩,⟨k,hf⟩⟩
      let e := pairEquiv s.2.2.2 p
      have he : e.val=pairStart s.2.2.2 i.val+k := pairEquiv_val _ p
      have hv : (fresh s.1 (pairCount s.2.2.2) e 0).val=
          s.1+2*(pairStart s.2.2.2 i.val+k) := by
        simp only [MediatorIteration.fresh_val,Fin.val_zero,Nat.add_zero,he]
      rw [← hv,next_ordinary_degree N s hs hb]
      rw [qmaForkBackground_new_degree left right (actualSite hs)]
      norm_num
    · rw [nextGroup_portAt_retained _ _ _ _ _ (by omega)]
      let t := 2*((groupAt s.2.2.2 i.val).length/2)+
        (k-(groupAt s.2.2.2 i.val).length/2)
      have ht : t<(groupAt s.2.2.2 i.val).length := retained_index_lt _ _ hj (by omega)
      let v : Fin s.1 := ⟨(portAt (groupAt s.2.2.2 i.val) t).1,hs.bounded ⟨i.val,hi⟩ ⟨t,ht⟩⟩
      have haway (e : Fin (pairCount s.2.2.2)) :
          actualSite hs e 1 ≠ v ∧ actualSite hs e 2 ≠ v := by
        constructor
        · exact actual_outer_away_retained hs ⟨i.val,hi⟩ ⟨t,ht⟩ (by dsimp [t]; omega) (e,0)
        · exact actual_outer_away_retained hs ⟨i.val,hi⟩ ⟨t,ht⟩ (by dsimp [t]; omega) (e,1)
      have hv := next_ordinary_degree N s hs hb (old s.1 (pairCount s.2.2.2) v)
      simp only [MediatorIteration.old_val] at hv
      change degree (next N s).2.1 v.val ≤ 1
      rw [hv]
      rw [qmaForkBackground_away_degree left right (actualSite hs) (actualSite_injective hs) v haway]
      rw [← degree_eq_graph]
      exact hd.port ⟨i.val,hi⟩ ⟨t,ht⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListDegreeIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent degree bounds along the actual list iteration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem next_ordinary_bounded (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) :
    SourceBondLists.bounded (next N s).1 (next N s).2.1 := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | ha
  · have h := hb b ho
    change b.1 < s.1+2*pairCount s.2.2.2 ∧ b.2.1 < s.1+2*pairCount s.2.2.2
    exact ⟨lt_of_lt_of_le h.1 (Nat.le_add_right _ _),lt_of_lt_of_le h.2 (Nat.le_add_right _ _)⟩
  · have h := addedBonds_valid s hs (scale N s) b ha
    exact ⟨h.1,h.2.1⟩

theorem iterate_ordinary_bounded (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (k : ℕ) :
    SourceBondLists.bounded (iterate N k s).1 (iterate N k s).2.1 := by
  induction k with
  | zero => exact hb
  | succ k ih => exact next_ordinary_bounded N _ (iterate_validPorts N s hs k) ih

theorem iterate_degreeBounds (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hd : DegreeBounds s) (k : ℕ) :
    DegreeBounds (iterate N k s) := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    exact next_degreeBounds N _ (iterate_validPorts N s hs k)
      (iterate_ordinary_bounded N s hs hb k) ih

theorem initial_ordinary_bounded (n : ℕ) (bs : List Bond) (c N : ℚ) :
    SourceBondLists.bounded (initial n bs c N).1 (initial n bs c N).2.1 := by
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  have he' := List.mem_range.mp he
  change n+2*e<n+2*bs.length ∧ n+2*e+1<n+2*bs.length
  constructor <;> omega

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListFullDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal exchange list has degree at most three once each
active group has at most three ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

def asForkPorts {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    QMAForkPorts n gs.length (fun i => (groupAt gs i.val).length) where
  center i := ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩
  port := portSite h
  center_injective := by
    intro i j he
    exact Fin.ext (congrArg (fun v : Fin n => v.val) he)
  port_injective := portSite_injective h
  center_ne_port := fun i p he => h.disjoint i p.1 p.2 (congrArg Fin.val he)

def asForkState (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s) :
    QMAForkState s.1 s.2.2.2.length (fun i => (groupAt s.2.2.2 i.val).length)
      (Fin s.2.1.length) where
  ports := asForkPorts hs
  left := (SourceBondLists.bonds s.1 s.2.1 hb).left
  right := (SourceBondLists.bonds s.1 s.2.1 hb).right
  distinct e := fun he => hn (s.2.1.get e) (List.get_mem _ e) (congrArg Fin.val he)
  degree_le := fun v => (degree_eq_graph s.1 s.2.1 hb v) ▸ hd.ordinary v
  center_degree := by
    intro i
    rw [← degree_eq_graph]
    exact hd.center i.val i.isLt
  port_degree := by
    intro p
    rw [← degree_eq_graph]
    exact hd.port p.1 p.2

theorem active_index_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : Bond → M) :
    ((activeBonds gs).map f).sum =
      ∑ p : PortIndex gs, f (p.1.val,(portAt (groupAt gs p.1.val) p.2.val).1,
        (portAt (groupAt gs p.1.val) p.2.val).2) := by
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,range_sum,PortIndex,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hp (j : Fin (groupAt gs i.val).length) :
      portAt (groupAt gs i.val) j.val=(groupAt gs i.val).get j := by
    simpa only [List.get_eq_getElem] using portAt_eq_getElem _ _ j.isLt
  simp only [hp]
  rw [← List.sum_ofFn]
  simpa only [List.get_eq_getElem] using congrArg List.sum
    (List.ofFn_getElem_eq_map (groupAt gs i.val) (fun p => f (i.val,p.1,p.2))).symm

theorem full_degree_eq (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s) (v : Fin s.1) :
    degree (s.2.1++activeBonds s.2.2.2) v.val =
      qmaGraphDegree (asForkState s hs hb hn hd).fullLeft
        (asForkState s hs hb hn hd).fullRight v := by
  rw [degree_append]
  rw [graph_degree_incident]
  simp only [degree,active_index_sum,QMAForkState.fullLeft,QMAForkState.fullRight,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    asForkState,asForkPorts,portSite,SourceBondLists.bonds]
  rw [initial_list_sum]

theorem full_degree_le_three (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s)
    (hl : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ 3) (v : Fin s.1) :
    degree (s.2.1++activeBonds s.2.2.2) v.val ≤ 3 := by
  rw [full_degree_eq s hs hb hn hd]
  exact (asForkState s hs hb hn hd).full_degree_le_three hl v

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListFinalDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded initial star lengths suffice for degree three after a fixed number
of literal fork rounds. This statement concerns the actual emitted bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem next_ordinary_noLoops (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) :
    ∀ b ∈ (next N s).2.1, b.1 ≠ b.2.1 := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | ha
  · exact hn b ho
  · exact (addedBonds_valid s hs (scale N s) b ha).2.2

theorem iterate_ordinary_noLoops (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (k : ℕ) :
    ∀ b ∈ (iterate N k s).2.1, b.1 ≠ b.2.1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact next_ordinary_noLoops N _ (iterate_validPorts N s hs k) ih

theorem iterate_full_degree_le_three (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1 ≠ b.2.1) (hd : DegreeBounds s)
    (D : ℕ) (hD : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D)
    (v : Fin (iterate N D s).1) :
    degree ((iterate N D s).2.1++activeBonds (iterate N D s).2.2.2) v.val ≤ 3 := by
  apply full_degree_le_three _ (iterate_validPorts N s hs D)
    (iterate_ordinary_bounded N s hs hb D) (iterate_ordinary_noLoops N s hs hn D)
    (iterate_degreeBounds N s hs hb hd D) _ v
  intro i
  have hi : i.val < s.2.2.2.length := by simpa only [iterate_centers] using i.isLt
  rw [iterate_group_length N s D i.val hi]
  exact (qmaForkDegreeAfter_constant _ D (hD ⟨i.val,hi⟩)).trans (by decide)

theorem initial_ordinary_noLoops (n : ℕ) (bs : List Bond) (c N : ℚ) :
    ∀ b ∈ (initial n bs c N).2.1, b.1 ≠ b.2.1 := by
  intro b hb
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hb
  dsimp only
  omega

theorem initial_iterate_full_degree_le_three (n : ℕ) (bs : List Bond) (c N : ℚ)
    (D : ℕ) (hD : ∀ i : Fin n, (initialIndices bs i.val).length ≤ D)
    (v : Fin (iterate N D (initial n bs c N)).1) :
    degree ((iterate N D (initial n bs c N)).2.1++
      activeBonds (iterate N D (initial n bs c N)).2.2.2) v.val ≤ 3 := by
  apply iterate_full_degree_le_three N _ (initial_validPorts n bs c N)
    (initial_ordinary_bounded n bs c N) (initial_ordinary_noLoops n bs c N)
    (initial_degreeBounds n bs c N) D _ v
  intro i
  have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
  change (groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i.val).length ≤ D
  rw [initial_groupAt n bs (initialScale N bs c) i.val hi]
  simpa only [initialGroup,List.length_map] using hD ⟨i.val,hi⟩

theorem initialIndices_length_eq_degree (bs : List Bond)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (i : ℕ) :
    (initialIndices bs i).length=degree bs i := by
  have hone (xs : List ℕ) : (xs.map (fun _ => (1:ℕ))).sum=xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
      omega
  rw [← hone (initialIndices bs i),initialIndices_sum,initial_evenodd_sum]
  simp only [initialEndpoint_even,initialEndpoint_odd]
  unfold degree
  rw [initial_list_sum]
  unfold incident
  apply Finset.sum_congr rfl
  intro e _
  have he := hn (bs.get e) (List.get_mem bs e)
  simp only [List.get_eq_getElem] at he ⊢
  split_ifs <;> omega

theorem initial_iterate_full_degree_of_bound (n : ℕ) (bs : List Bond)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (D : ℕ)
    (hD : ∀ i : Fin n, degree bs i.val ≤ D)
    (v : Fin (iterate N D (initial n bs c N)).1) :
    degree ((iterate N D (initial n bs c N)).2.1++
      activeBonds (iterate N D (initial n bs c N)).2.2.2) v.val ≤ 3 := by
  apply initial_iterate_full_degree_le_three n bs c N D _ v
  intro i
  rw [initialIndices_length_eq_degree bs hn]
  exact hD i

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse-cell labels for the actual ordered fork output. Both members of a
fresh mediator pair stay in their actual active center's cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped Classical

def CellAligned {β : Type*} (s : State) (cell : ℕ → β) : Prop :=
  ∀ (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length),
    cell (portAt (groupAt s.2.2.2 i.val) j.val).1=cell i.val

def nextCell {β : Type*} (s : State) (cell : ℕ → β) (v : ℕ) : β :=
  if v < s.1 then cell v else
    cell (((catalog s.2.2.2).drop ((v-s.1)/2)).headD (0,((0,0),(0,0)))).1

theorem nextCell_old {β : Type*} (s : State) (cell : ℕ → β)
    (v : ℕ) (hv : v < s.1) : nextCell s cell v=cell v := by
  simp only [nextCell,hv,ite_true, if_true]

theorem nextCell_fresh {β : Type*} (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
    nextCell s cell (s.1+2*e.val+b.val)=cell (actualSite h e 0).val := by
  have hn : ¬s.1+2*e.val+b.val < s.1 := by omega
  have hd : (s.1+2*e.val+b.val-s.1)/2=e.val := by have := b.isLt; omega
  simp only [nextCell,hn,ite_false, if_false,hd,catalog_actualSite h e]

theorem cellAligned_actualSite {β : Type*} (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) (e : Fin (pairCount s.2.2.2)) (a : Fin 3) :
    cell (actualSite h e a).val=cell (actualSite h e 0).val := by
  fin_cases a
  · rfl
  · exact ha (localPair s.2.2.2 e).1 (localFirst s.2.2.2 e)
  · exact ha (localPair s.2.2.2 e).1 (localSecond s.2.2.2 e)

theorem next_cellAligned {β : Type*} (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) : CellAligned (next N s) (nextCell s cell) := by
  intro i j
  have hj₀ := j.isLt
  generalize hkj : j.val=k at hj₀ ⊢
  clear hkj j
  have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
  have hn : i.val < s.1 := lt_of_lt_of_le hi h.centers
  rw [nextCell_old s cell i.val hn]
  have hg : groupAt (next N s).2.2.2 i.val=nextGroup s.1 (scale N s) s.2.2.2 i.val :=
    next_groupAt _ _ _ _ hi
  have hj : k<(groupAt s.2.2.2 i.val).length/2+(groupAt s.2.2.2 i.val).length%2 := by
    have hj := hj₀
    rw [hg,nextGroup_length] at hj
    exact hj
  rw [hg]
  by_cases hf : k<(groupAt s.2.2.2 i.val).length/2
  · rw [nextGroup_portAt_fresh _ _ _ _ _ hf]
    let p : LocalPair s.2.2.2 := ⟨⟨i.val,hi⟩,⟨k,hf⟩⟩
    let e := pairEquiv s.2.2.2 p
    have he : e.val=pairStart s.2.2.2 i.val+k := pairEquiv_val _ p
    have hh := nextCell_fresh s h cell e 0
    simp only [Fin.val_zero,Nat.add_zero,he] at hh
    rw [hh]
    change cell (localPair s.2.2.2 e).1.val=cell i.val
    have hl : localPair s.2.2.2 e=p := (pairEquiv s.2.2.2).symm_apply_apply p
    rw [hl]
  · rw [nextGroup_portAt_retained _ _ _ _ _ (by omega)]
    let t := 2*((groupAt s.2.2.2 i.val).length/2)+(k-(groupAt s.2.2.2 i.val).length/2)
    have ht : t<(groupAt s.2.2.2 i.val).length := retained_index_lt _ _ hj (by omega)
    rw [nextCell_old s cell _ (h.bounded ⟨i.val,hi⟩ ⟨t,ht⟩)]
    exact ha ⟨i.val,hi⟩ ⟨t,ht⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCellLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every new ordinary bond remains within its original coarse cell. Old
ordinary bonds retain their cells, so arbitrary reflexive locality relations
are preserved by the actual list transformation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def BondLocal {β : Type*} (bs : List Bond) (cell : ℕ → β) (R : β → β → Prop) : Prop :=
  ∀ b ∈ bs, R (cell b.1) (cell b.2.1)

theorem addedBonds_cellLocal {β : Type*} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) (R : β → β → Prop)
    (hr : ∀ x, R x x) (scale : ℚ) : BondLocal (addedBonds s scale) (nextCell s cell) R := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' : i<pairCount s.2.2.2 := by
    simpa only [catalog_length] using List.mem_range.mp hi
  let e : Fin (pairCount s.2.2.2) := ⟨i,hi'⟩
  rw [catalog_actualSite hs e] at hb
  have hc (a : Fin 3) : nextCell s cell (actualSite hs e a).val=
      cell (actualSite hs e 0).val :=
    (nextCell_old s cell _ (actualSite hs e a).isLt).trans
      (cellAligned_actualSite s hs cell ha e a)
  have hf0 : nextCell s cell (s.1+2*i)=cell (actualSite hs e 0).val := by
    simpa only [Fin.val_zero,Nat.add_zero] using nextCell_fresh s hs cell e 0
  have hf1 : nextCell s cell (s.1+2*i+1)=cell (actualSite hs e 0).val := by
    simpa only [Fin.val_one] using nextCell_fresh s hs cell e 1
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    simpa only [hc,hf0,hf1] using hr (cell (actualSite hs e 0).val)

theorem next_cellLocal {β : Type*} (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (cell : ℕ → β) (ha : CellAligned s cell)
    (R : β → β → Prop) (hr : ∀ x, R x x) (hl : BondLocal s.2.1 cell R) :
    BondLocal (next N s).2.1 (nextCell s cell) R := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | hn
  · rw [nextCell_old s cell _ (hb b ho).1,nextCell_old s cell _ (hb b ho).2]
    exact hl b ho
  · exact addedBonds_cellLocal s hs cell ha R hr (scale N s) b hn

def iterateCell {β : Type*} (N : ℚ) : ℕ → State → (ℕ → β) → ℕ → β
  | 0,_,cell => cell
  | k+1,s,cell => nextCell (iterate N k s) (iterateCell N k s cell)

theorem iterate_cellAligned {β : Type*} (N : ℚ) (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (cell : ℕ → β) (ha : CellAligned s cell) (k : ℕ) :
    CellAligned (iterate N k s) (iterateCell N k s cell) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact next_cellAligned N _ (iterate_validPorts N s hs k) _ ih

theorem iterate_cellLocal {β : Type*} (N : ℚ) (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (cell : ℕ → β) (ha : CellAligned s cell) (R : β → β → Prop)
    (hr : ∀ x, R x x) (hl : BondLocal s.2.1 cell R) (k : ℕ) :
    BondLocal (iterate N k s).2.1 (iterateCell N k s cell) R := by
  induction k with
  | zero => exact hl
  | succ k ih =>
    exact next_cellLocal N _ (iterate_validPorts N s hs k)
      (iterate_ordinary_bounded N s hs hb k) _ (iterate_cellAligned N s hs cell ha k) R hr ih

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite-list programs for the active-port pairs in a fork round.
Only the finite input lists are enumerated; spin Hilbert-space bases are absent. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def portCode : Port → List Bool := prodCode Nat.bits ratCode
def pairCode : Pair → List Bool := prodCode portCode portCode
def groupsCode : Groups → List Bool := listCode (listCode portCode)
def taggedCode : TaggedPair → List Bool := prodCode Nat.bits pairCode

noncomputable def halfProgram : Procedure unaryCode unaryCode (fun n => n/2) := by
  let n := Procedure.identity unaryCode
  let half := Procedure.binaryDiv.comp
    (Procedure.unaryToBits.pair (Procedure.constant unaryCode Nat.bits 2))
  exact (Procedure.clippedUnary.comp (n.pair half)).congrFun (by
    intro n
    exact Nat.min_eq_right (Nat.div_le_self n 2))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational calibration for the ordered fork list. The perturbation
scale includes the unpaired active ports in its retained-energy bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def leftWeight : Procedure pairCode ratCode (fun p => p.1.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.first portCode portCode)
noncomputable def rightWeight : Procedure pairCode ratCode (fun p => p.2.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.second portCode portCode)

abbrev ScaleInput := ℚ × State

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal numbering of the new active ports. A prefix sum of pair counts
gives each center its contiguous block of fresh mediator indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def pointCode : PointInput → List Bool := prodCode (prodCode Nat.bits Nat.bits) ratCode

def groupCode : GroupInput → List Bool := prodCode Nat.bits (prodCode ratCode groupsCode)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete literal rational fork round, including all four background
bonds, the scalar offset and the remaining active ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def bondInputCode : BondInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
def bond (x : BondInput) (k : Fin 4) : MediatorListProgram.Bond :=
  ![(x.2.2.2.1.1,x.2.2.2.2.1,2*x.2.2.2.1.2*x.2.2.2.2.2),
    (x.1+2*x.2.1,x.1+2*x.2.1+1,x.2.2.1^2),
    (x.2.2.2.1.1,x.1+2*x.2.1+1,2*x.2.2.1*x.2.2.2.1.2),
    (x.2.2.2.2.1,x.1+2*x.2.1+1,2*x.2.2.1*x.2.2.2.2.2)] k

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal lookup, parity and rational coefficient programs for the
initial odd subdivision. Endpoint queries read the actual input bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable def initialParityProgram : Procedure Nat.bits Procedure.boolCode
    (fun j => decide (j%2=0)) :=
  Procedure.binaryZero.comp (Procedure.binaryMod.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2)))

def initialMatch (x : ℕ × (ℕ × List Bond)) : List ℕ :=
  if initialEndpoint x.2.2 x.1=x.2.1 then [x.1] else []

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialStateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program emits the complete initial odd-subdivision
state, with its rational scale, singlet bonds and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev InitialInput := ℚ × (ℕ × (List Bond × ℚ))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathVisitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encoded path lists determine the two directional ports of every internal
cell. The output contains both orientations, as required by the route table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathVisitProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

end ContinuumCoulomb.QuantumPathVisitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal ordinal-slot program. For an encoded cell list and a unary
label it counts earlier labels in the same cell; the result agrees with the
bounded injective slots used by the spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def incrementProgram :
    Procedure (prodCode Procedure.boolCode unaryCode) unaryCode increment := by
  let k := Procedure.second Procedure.boolCode unaryCode
  exact (Procedure.conditional (Procedure.first Procedure.boolCode unaryCode)
    (Procedure.unarySuccessor.comp k) k).congrFun (by intro x; rfl)

noncomputable def countProgram :
    Procedure (listCode Procedure.boolCode) unaryCode (fun xs => xs.countP id) := by
  let fold := Procedure.foldList false incrementProgram Polynomial.X (by
    intro xs k i
    rw [fold_increment]
    have hc := List.countP_le_length (p := id) (l := xs.take i)
    have ht : (xs.take i).length ≤ xs.length := List.length_take_le' _ _
    have hs := list_length_le_code Procedure.boolCode xs
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  exact (fold.comp ((Procedure.identity _).pair
    (Procedure.constant _ unaryCode 0))).congrFun (by
      intro xs
      simp only [Function.comp_apply,id_eq,fold_increment,zero_add])

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply explicit ordinal ranks to the cell-slot interface used by geometry. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalPlacement

theorem coordinates_eq {rows width : ℕ} (p q : QMAGridCell rows width) :
    (p.1.val,p.2.val) = (q.1.val,q.2.val) ↔ p=q := by
  constructor
  · intro h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  · rintro rfl; rfl

 def coordinates {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width) : Fin n → ℕ × ℕ :=
  fun q => ((cell q).1.val,(cell q).2.val)

 theorem fiber_card {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width) (q : Fin n) :
    (Finset.univ.filter (fun r => coordinates cell r = coordinates cell q)).card =
      (Finset.univ.filter (fun r => cell r = cell q)).card := by
  congr 1
  apply Finset.filter_congr
  intro r _
  exact coordinates_eq _ _

 def slots {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hd : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) : QMACellSlots cell A where
  index q := ⟨QuantumOrdinalSlots.rank (coordinates cell) q,
    (QuantumOrdinalSlots.rank_lt_fiber (coordinates cell) q).trans_le
      (by rw [fiber_card]; exact hd (cell q))⟩
  injective := by
    intro q r hc hs
    apply QuantumOrdinalSlots.rank_injective_on_cell (coordinates cell)
    · exact (coordinates_eq _ _).mpr hc
    · exact congrArg Fin.val hs

end ContinuumCoulomb.QuantumOrdinalPlacement

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalSpatial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArmWalk_length _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_last _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.endpointArm_zero _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph_energy _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the abstract default slots by the explicit ordinal choice on the
encoded spin and interaction labels. The finite Hamiltonian is unchanged. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem relabel_density {Q R : Type*} [Fintype Q] [Fintype R]
    {rows width A : ℕ} (cell : Q → QMAGridCell rows width)
    (hd : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) (e : Q ≃ R)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun r => (cell ∘ e.symm) r=p)).card ≤ A := by
  let f : {q // cell q=p} ≃ {r // (cell ∘ e.symm) r=p} :=
    Equiv.subtypeEquiv e (by intro q; simp)
  have hh := Fintype.card_congr f
  simp only [Fintype.card_subtype] at hh
  rw [← hh]
  exact hd p

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

 def withOrdinalSlots {m : ℕ} (labels : M.Term ≃ Fin m) : QMASpatialExchangeModel A B :=
  { M with
    qubitSlots := QuantumOrdinalPlacement.slots M.cell M.qubitDensity
    termSlots := (QuantumOrdinalPlacement.slots (M.anchor ∘ labels.symm)
      (relabel_density M.anchor M.termDensity labels)).transport labels }

@[simp] theorem withOrdinalSlots_energy {m : ℕ} (labels : M.Term ≃ Fin m) :
    (M.withOrdinalSlots labels).energy = M.energy := rfl

@[simp] theorem withOrdinalSlots_qubit_index {m : ℕ} (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    ((M.withOrdinalSlots labels).qubitSlots.index q).val =
      QuantumOrdinalSlots.rank (QuantumOrdinalPlacement.coordinates M.cell) q := rfl

@[simp] theorem withOrdinalSlots_term_index {m : ℕ} (labels : M.Term ≃ Fin m) (e : M.Term) :
    ((M.withOrdinalSlots labels).termSlots.index e).val =
      QuantumOrdinalSlots.rank (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))
        (labels e) := rfl

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLaneUnaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lane colors can be produced in unary without expanding the binary cell
coordinates: only their residues modulo three enter the lane formula. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLaneUnaryProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

noncomputable def residue {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea Nat.bits f) : Procedure ea unaryCode (fun x => f x%3) :=
  Procedure.boundedUnary
    (Procedure.binaryMod.comp (p.pair (Procedure.constant ea Nat.bits 3)))
    (Procedure.constant ea unaryCode 3)
    (by intro x; exact (Nat.mod_lt (f x) (by decide)).le)

end ContinuumCoulomb.QuantumLaneUnaryProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sorted endpoint port is evaluated by counting incident edges whose
lane color is smaller. Each record contains the two endpoints and lane color. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def entryCode : Entry → List Bool := prodCode Nat.bits pairCode

def below (vc : Pair) (e : Entry) : Bool :=
  decide ((e.1=vc.1 ∨ e.2.1=vc.1) ∧ e.2.2<vc.2)

abbrev Input := Pair × List Entry
def inputCode : Input → List Bool := prodCode pairCode (listCode entryCode)
def value (x : Input) : ℕ := (x.2.map (below x.1)).countP id

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compile cell arrays and an edge array into the registers needed by the
buffered-route evaluator. Binary endpoint labels are clipped by the explicit
qubit array length before their conversion to unary loop bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Data := (List Pair × List Pair) × List Pair
def dataCode : Data → List Bool :=
  prodCode (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
abbrev Input := ℕ × Data
def inputCode : Input → List Bool := prodCode unaryCode dataCode

noncomputable def dataProgram : Procedure inputCode dataCode Prod.snd := Procedure.second _ _
noncomputable def indexProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable def qubitsProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.1.1) :=
  (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram)
noncomputable def anchorsProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.1.2) :=
  (Procedure.second (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram)
noncomputable def edgesProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.2) :=
  (Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev State := List Pair × List Pair
def stateCode : State → List Bool := prodCode (listCode pairCode) (listCode pairCode)

def anchors (d : ℕ) (xs : List Pair) : List Pair :=
  (xs.map (fun p => List.replicate d p)).flatten

def value (d : ℕ) (x : State) : State := (x.1++x.2,anchors d x.2)

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedIncidence
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform incidence bounds for the actual ordered local reductions.  Every
new site belongs to one input term, while old sites remain in that term's
stored support.  The bound counts zero-coefficient terms as well. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedIncidence
open scoped BigOperators Classical

variable {ι κ : Type} [Fintype κ]

theorem extension_bound {d D : ℕ} (xs : κ → List ι)
    (ys : κ × Fin d → List (ι ⊕ κ)) (hD : 1 ≤ D) (hx : Bounded xs D)
    (hy : ∀ p q, q ∈ ys p → Origin xs p.1 q) : Bounded ys (d*D) := by
  intro q
  cases q with
  | inl q =>
    calc
      count ys (Sum.inl q) ≤ ∑ p : κ × Fin d, if q ∈ xs p.1 then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases h : Sum.inl q ∈ ys p
        · have ho : q ∈ xs p.1 := hy p _ h
          simp only [h,ho,ite_true, if_true,le_refl]
        · simp only [h,ite_false, if_false,Nat.zero_le]
      _ = d*count xs q := by
        rw [Fintype.sum_prod_type]
        have hi (e : κ) : (∑ _k : Fin d, if q ∈ xs e then 1 else 0) =
            d*(if q ∈ xs e then 1 else 0) := by
          by_cases h : q ∈ xs e <;> simp [h]
        simp_rw [hi]
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ d*D := Nat.mul_le_mul_left d (hx q)
  | inr q =>
    calc
      count ys (Sum.inr q) ≤ ∑ p : κ × Fin d, if q=p.1 then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases h : Sum.inr q ∈ ys p
        · have ho : q=p.1 := hy p _ h
          rw [ite_eq_left h,ite_eq_left ho]
        · simp only [h,ite_false, if_false,Nat.zero_le]
      _ = d := by
        rw [Fintype.sum_prod_type]
        have hi (e : κ) : (∑ _k : Fin d, if q=e then 1 else 0) =
            if q=e then d else 0 := by
          by_cases h : q=e <;> simp [h]
        simp_rw [hi]
        simp
      _ ≤ d*D := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hD

theorem subdivision_bound {D : ℕ} (xs : κ → List ι) (d : ℕ)
    (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedSubdivision.outputSites xs d) (4*D) :=
  extension_bound xs _ hD hx (subdivision_origin xs d)

theorem yy_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedYY.outputSites xs) (4*D) :=
  extension_bound xs _ hD hx (yy_origin xs)

theorem third_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedThird.outputSites xs w) (7*D) :=
  extension_bound xs _ hD hx (third_origin xs w hlen)

theorem xz_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedXZ.sites xs w) (3136*D) := by
  have h1 := subdivision_bound xs 3 hD hx
  have h2 := subdivision_bound (QuantumOrderedSubdivision.outputSites xs 3) 2
    (by omega : 1 ≤ 4*D) h1
  have h3 := third_bound (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeSites_length xs hlen) (by omega : 1 ≤ 4*(4*D)) h2
  have h4 := yy_bound (QuantumOrderedXZ.twoSites xs w) (by omega : 1 ≤ 7*(4*(4*D))) h3
  have h5 := third_bound (QuantumOrderedXZ.xzThreeSites xs w)
    (QuantumOrderedXZ.xzThreeWord xs w) (QuantumOrderedXZ.xzThreeSites_length xs w hlen)
    (by omega : 1 ≤ 4*(7*(4*(4*D)))) h4
  change Bounded (QuantumOrderedXZ.sites xs w) (7*(4*(7*(4*(4*D))))) at h5
  convert h5 using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem private_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedPrivate.outputSites xs) (4*D) :=
  subdivision_bound xs 1 hD hx

theorem complete_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w)) (12544*D) := by
  have h := private_bound (QuantumOrderedXZ.sites xs w)
    (by omega : 1 ≤ 3136*D) (xz_bound xs w hlen hD hx)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

end ContinuumCoulomb.QuantumOrderedIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

def complete (x : State) : State := value 4 (value 7 (value 4 (value 7 (value 4 (value 4 x)))))

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

def value (x : State) : List Pair := anchors 4 (complete x).1

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual row/column arrays for the fork compiler. The scale remains an
input register; only the number of fork rounds is fixed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Cells := QuantumForkList.State × List QuantumRouteCode.Pair
def lookup (xs : List QuantumRouteCode.Pair) (i : ℕ) : QuantumRouteCode.Pair := (xs.drop i).headD (0,0)

def nextCells (x : Cells) : List QuantumRouteCode.Pair :=
  (List.range (x.1.1+2*pairCount x.1.2.2.2)).map (nextCell x.1 (lookup x.2))

abbrev Input := ℚ × Cells
def step (x : Input) : Cells := (next x.1 x.2.1,nextCells x.2)

def run : ℕ → Input → Cells
  | 0,x => x.2
  | k+1,x => step (x.1,run k x)

def Represents (x : Cells) (cell : ℕ → QuantumRouteCode.Pair) : Prop :=
  ∀ v, v<x.1.1 → lookup x.2 v=cell v

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal bond-list subdivision has the same full-space ground-energy
estimate as the calibrated singlet construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open Matrix
open scoped BigOperators

def encodedInput {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) : Input :=
  ((n,even,N,c),(List.ofFn fun i => ((left i).val,(right i).val,w i),
    List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)))

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-round routing compiler on literal bond/work lists. Each active
edge receives one singlet pair; its unfinished tail retains one less work unit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Entry := ℕ × Bond
def zeroEntry : Entry := (0,zeroBond)
def selected (active : Bool) (e : Entry) : Bool := if e.1=0 then !active else active
def partition (active : Bool) (xs : List Entry) : List Entry := xs.filter (selected active)
def erase (xs : List Entry) : List Bond := xs.map Prod.snd

abbrev State := ℕ × (ℚ × List Entry)
abbrev Input := ℚ × State

def stepInput (x : Input) : QuantumListPathStep.Input :=
  ((x.2.1,false,x.1,x.2.2.1),(erase (partition false x.2.2.2),erase (partition true x.2.2.2)))

abbrev BlockInput := QuantumListPathProgram.Parameters × (ℕ × Entry)
def blockBondInput (x : BlockInput) : QuantumListPathProgram.Input := (x.1,x.2.1,x.2.2.2)
def blockWork (x : BlockInput) (k : Fin 3) : ℕ := if k=2 then x.2.2.1-1 else 0
def block (x : BlockInput) : List Entry :=
  List.ofFn fun k => (blockWork x k,QuantumListPathProgram.bond (blockBondInput x) k)

def indexed (x : ℕ × Input) : BlockInput :=
  (QuantumListPathStep.parameters (stepInput x.2),x.1,
    ((partition true x.2.2.2.2).drop x.1).headD zeroEntry)
def family (x : Input) : List Entry :=
  ((List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x)))).flatten

def value (x : Input) : State :=
  (QuantumListPathStep.count (stepInput x),QuantumListPathStep.constant (stepInput x),
    partition false x.2.2.2++family x)

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => value (N,iterate N k s)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal route lists accompanying the bond/work scheduler. Every new pair
is placed at the first two internal points of its selected route. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumListSchedule

abbrev Routed := Entry × List Pair
abbrev State := QuantumListSchedule.State × (List Pair × List (List Pair))
abbrev Input := ℚ × State

def indexed (x : ℕ × Input) : Routed :=
  (((x.2.2.1.2.2.drop x.1).headD zeroEntry),((x.2.2.2.2.drop x.1).headD []))
def decorated (x : Input) : List Routed :=
  (List.range x.2.1.2.2.length).map (fun i => indexed (i,x))
def selectedRoutes (b : Bool) (x : Input) : List Routed :=
  (decorated x).filter (fun r => selected b r.1)
def lookup (p : List Pair) (i : ℕ) : Pair := (p.drop i).headD (0,0)
def freshPoints (r : Routed) : List Pair := [lookup r.2 1,lookup r.2 2]
def pathBlock (r : Routed) : List (List Pair) :=
  [[lookup r.2 1,lookup r.2 2],[lookup r.2 0,lookup r.2 1],(r.2.drop 2).reverse]
def positions (x : Input) : List Pair :=
  x.2.2.1++((selectedRoutes true x).map freshPoints).flatten
def paths (x : Input) : List (List Pair) :=
  (selectedRoutes false x).map Prod.snd++((selectedRoutes true x).map pathBlock).flatten
def value (x : Input) : State := (QuantumListSchedule.value (x.1,x.2.1),positions x,paths x)

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => value (N,iterate N k s)

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLeafProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial TM2 evaluators for scaled centers and reserved leaves. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteLeafCode
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode
noncomputable opaque firstProgram : Procedure endsCode pairCode Prod.fst := Procedure.first _ _
noncomputable opaque secondProgram : Procedure endsCode pairCode Prod.snd := Procedure.second _ _
noncomputable def axisProgram (left xAxis : Bool) : Procedure endsCode Nat.bits
    (fun x => if xAxis then (if left then x.1 else x.2).1 else (if left then x.1 else x.2).2) := by
  let p : Procedure endsCode pairCode (fun x => if left then x.1 else x.2) := by
    cases left
    · exact secondProgram
    · exact firstProgram
  let q : Procedure pairCode Nat.bits (fun x => if xAxis then x.1 else x.2) := by
    cases xAxis
    · exact Procedure.second Nat.bits Nat.bits
    · exact Procedure.first Nat.bits Nat.bits
  exact (q.comp p).congrFun (by intro x; cases left <;> cases xAxis <;> rfl)

end ContinuumCoulomb.QuantumRouteLeafCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInflatedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eightfold scaled route is an explicit list computation. Its loop
bound is eight times the input route length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumInflatedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode Nat.bits (listCode pairCode)

end ContinuumCoulomb.QuantumInflatedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenListPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal reserved-leaf and tail arrays for an even route subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenListPieces
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def leaf (xs : List Pair) : Pair := qmaRouteLeaf
  (QuantumForkGridProgram.lookup xs 0)
  (qmaGridNeighborIndex (QuantumForkGridProgram.lookup xs 0)
    (QuantumForkGridProgram.lookup xs 1))

end ContinuumCoulomb.QuantumEvenListPieces

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Validity, fixed-round termination and full-space energy bounds for the
literal list-work routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open Matrix MediatorListProgram

theorem erase_append (xs ys : List Entry) : erase (xs++ys)=erase xs++erase ys := List.map_append

theorem erase_block (x : BlockInput) :
    erase (block x) = QuantumListPathProgram.block (blockBondInput x) := by
  simp only [erase,block,QuantumListPathProgram.block,List.map_ofFn]
  rfl

theorem erase_head (xs : List Entry) (i : ℕ) :
    ((xs.drop i).headD zeroEntry).2 = ((erase xs).drop i).headD zeroBond := by
  simp only [erase,← List.map_drop]
  cases xs.drop i <;> rfl

theorem indexed_erase (x : Input) (i : ℕ) :
    blockBondInput (indexed (i,x)) = QuantumListPathProgram.indexed
      (i,(QuantumListPathStep.parameters (stepInput x),erase (partition true x.2.2.2))) := by
  dsimp only [indexed,blockBondInput,QuantumListPathProgram.indexed]
  rw [erase_head]

theorem erase_family (x : Input) :
    erase (family x) = QuantumListPathProgram.family
      (QuantumListPathStep.parameters (stepInput x),erase (partition true x.2.2.2)) := by
  calc
    _ = ((List.range (partition true x.2.2.2).length).map
        (fun i => erase (block (indexed (i,x))))).flatten := by
      simp only [erase,family,List.map_flatten,List.map_map,Function.comp_def]
    _ = _ := by
      simp_rw [erase_block,indexed_erase]
      simp only [QuantumListPathProgram.family,erase,List.length_map]

theorem erase_value (x : Input) : erase (value x).2.2 = QuantumListPathStep.bonds (stepInput x) := by
  change erase (partition false x.2.2.2++family x) = _
  rw [erase_append,erase_family]
  rfl

def Valid (s : State) : Prop := SourceBondLists.bounded s.1 (erase s.2.2) ∧
  ∀ e ∈ erase s.2.2, e.1 ≠ e.2.1

theorem partition_valid (s : State) (hs : Valid s) (b : Bool) :
    SourceBondLists.bounded s.1 (erase (partition b s.2.2)) ∧
      ∀ e ∈ erase (partition b s.2.2), e.1 ≠ e.2.1 := by
  have hm : ∀ e ∈ erase (partition b s.2.2), e ∈ erase s.2.2 := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨a,(List.mem_filter.mp ha).1,rfl⟩
  exact ⟨fun e he => hs.1 e (hm e he),fun e he => hs.2 e (hm e he)⟩

theorem value_valid (x : Input) (hx : Valid x.2) : Valid (value x) := by
  have hk := partition_valid x.2 hx false
  have hs := partition_valid x.2 hx true
  constructor
  · change SourceBondLists.bounded (QuantumListPathStep.count (stepInput x)) (erase (value x).2.2)
    rw [erase_value]
    exact QuantumListPathStep.bonds_bounded (stepInput x) hk.1 hs.1
  · rw [erase_value]
    exact QuantumListPathStep.bonds_noLoops (stepInput x) hk.2 hs.1

def energy (s : State) : ℝ :=
  sourceMatrixBottom s.1 (SourceBondLists.matrix s.1 (erase s.2.2)+(s.2.1:ℂ) • 1)

theorem iterate_valid (N : ℚ) (s : State) (hs : Valid s) (k : ℕ) : Valid (iterate N k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact value_valid (N,iterate N k s) ih

theorem family_length (x : Input) : (family x).length=(partition true x.2.2.2).length*3 := by
  have hl (is : List ℕ) : (is.map (fun i => block (indexed (i,x)))).flatten.length=is.length*3 := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons,List.flatten_cons,List.length_append,block,List.length_ofFn,
        List.length_cons] at *
      omega
  simpa only [family,List.length_range] using hl (List.range (partition true x.2.2.2).length)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical merging of a finite bond tape. A quadratic table of vertex pairs
gives a deterministic order and retains exactly the pairs occurring in the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

def ordered (e : Bond) : Pair := (min e.1 e.2.1,max e.1 e.2.1)
def support (n : ℕ) (xs : List Bond) : List Pair :=
  (pairs n).filter (fun p => decide (p ∈ xs.map ordered))
def weight (xs : List Bond) (p : Pair) : ℚ :=
  (xs.map (fun e => if ordered e=p then e.2.2 else 0)).sum
def value (n : ℕ) (xs : List Bond) : List Bond :=
  (support n xs).map (fun p => (p.1,p.2,weight xs p))

theorem support_nodup (n : ℕ) (xs : List Bond) : (support n xs).Nodup :=
  (pairs_nodup n).filter _

theorem ordered_bounded {n : ℕ} {e : Bond} (h : e.1<n ∧ e.2.1<n) :
    (ordered e).1<n ∧ (ordered e).2<n := by
  exact ⟨(min_le_left _ _).trans_lt h.1,max_lt h.1 h.2⟩

theorem mem_support {n : ℕ} {xs : List Bond} (hb : SourceBondLists.bounded n xs) (p : Pair) :
    p ∈ support n xs ↔ p ∈ xs.map ordered := by
  simp only [support,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have h := ordered_bounded (hb e he)
    exact ⟨List.mem_product.mpr ⟨List.mem_range.mpr h.1,List.mem_range.mpr h.2⟩,
      List.mem_map.mpr ⟨e,he,rfl⟩⟩

theorem bounded (n : ℕ) (xs : List Bond) : SourceBondLists.bounded n (value n xs) := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hp' := (List.mem_filter.mp hp).1
  exact ⟨List.mem_range.mp (List.mem_product.mp hp').1,
    List.mem_range.mp (List.mem_product.mp hp').2⟩

theorem noLoops {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) : ∀ e ∈ value n xs, e.1≠e.2.1 := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨b,hb,hbp⟩ := List.mem_map.mp hm
  subst p
  change min b.1 b.2.1≠max b.1 b.2.1
  exact (min_lt_max.mpr (h b hb)).ne

theorem value_get (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    (value n xs).get i =
      let p := (support n xs).get ⟨i.val,by simpa only [value,List.length_map] using i.isLt⟩
      (p.1,p.2,weight xs p) := by
  exact List.getElem_map _

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial pair-table enumeration and rational accumulation for
canonical bond merging. The vertex count is represented in unary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Input := ℕ × List Bond

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluate each candidate together with its finite permission bit. Keeping
that bit attached to the path preserves the exact catalog order during the
bounded search, including reversed paths. -/

noncomputable section
namespace ContinuumCoulomb.QuantumTaggedRouteProgram
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumRoutingTable

abbrev Tagged := Bool × List Pair
def taggedCode : Tagged → List Bool := prodCode Procedure.boolCode (listCode pairCode)
def bodyPermitted (t : Table) (B : QMACellRouteBody) : Bool := allowed t B && decide B.Valid

theorem bodyPermitted_eq_true (t : Table) (B : QMACellRouteBody) :
    bodyPermitted t B = true ↔ allowed t B = true ∧ B.Valid := by
  simp only [bodyPermitted,Bool.and_eq_true]
  exact and_congr_right (fun _ => ⟨of_decide_eq_true,decide_eq_true⟩)

def tagged (t : Table) (R : QMACellRoute) : Tagged := (bodyPermitted t R.body,R.path)

def oriented (b : Bool) (xs : List Pair) : List Tagged := [(b,xs),(b,xs.reverse)]

noncomputable opaque cellPositiveProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (0 < x.2.1 ∧ 0 < x.2.2)) := by
  let one := Procedure.constant inputCode Nat.bits 1
  let px := (Procedure.first Nat.bits Nat.bits).comp cellProgram
  let py := (Procedure.second Nat.bits Nat.bits).comp cellProgram
  exact (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp (one.pair px)).pair (Procedure.binaryLe.comp (one.pair py)))).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq]
      omega)

end ContinuumCoulomb.QuantumTaggedRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteSelectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal 140-entry selector checks finite permissions and both physical
endpoints. No unbounded search or choice occurs in the resulting program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteSelectorProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumTaggedRouteProgram QuantumFiniteRouteSearch

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode
def accepts (ends : Ends) (v : Tagged) : Bool :=
  v.1 && decide (v.2.headD (0,0) = ends.1) && decide (v.2.reverse.headD (0,0) = ends.2)

def choose (x : Ends × List Tagged) : List Pair :=
  (selectParallelValue (false,[]) (x.2,x.2.map (accepts x.1))).2

abbrev Input := QuantumRoutingTable.Table × Ends
def inputCode : Input → List Bool := prodCode QuantumRoutingTable.tableCode endsCode

end ContinuumCoulomb.QuantumRouteSelectorProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation of the physical port chain on a computed coarse path.
The output enumerates both endpoint centers and every incoming/outgoing port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def offset (p : Pair) (x y : ℕ) : Pair := (32*p.1+x,32*p.2+y)

def port (p : Pair) (a : ℕ) : Pair :=
  if a=0 then offset p 23 16 else if a=1 then offset p 16 23
  else if a=2 then offset p 9 16 else offset p 16 9

theorem port_fin (p : Pair) (a : Fin 4) : port p a.val = qmaGridPort p a := by
  fin_cases a <;> rfl

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPairDedup
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The crossing compiler retains one occurrence of each coordinate pair,
with an output bound from the original list. -/

noncomputable section
open scoped List Classical
namespace ContinuumCoulomb.QuantumPairDedup
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def insertPair (a : Pair) (xs : List Pair) : List Pair := if a ∈ xs then xs else a::xs

theorem insert_sublist (a : Pair) (xs : List Pair) : insertPair a xs <+ a::xs := by
  unfold insertPair
  split
  · exact List.sublist_cons_self _ _
  · exact List.Sublist.refl _

theorem fold_sublist (xs ys : List Pair) :
    xs.foldl (fun zs a => insertPair a zs) ys <+ xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (insertPair a ys)).trans ((insert_sublist a ys).append_left xs.reverse)

theorem foldr_eq (xs : List Pair) : xs.foldr insertPair []=xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,ih,List.dedup_cons']
    by_cases h : a ∈ xs.dedup <;> simp [insertPair,h]

end ContinuumCoulomb.QuantumPairDedup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite lists of actual routes produce a routing table with exactly
the permissions of the physical graph proof. Lists may use any complete edge
order; this does not change a routing decision. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram
namespace QuantumPathTable

abbrev Input := List Pair × List (List Pair)
def inputCode : Input → List Bool :=
  prodCode (listCode pairCode) (listCode (listCode pairCode))

end QuantumPathTable
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial subdivision assigns its two new spins to the original
endpoints. Its singlet bonds therefore have exactly the original cell locality. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def initialCell {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β) (v : ℕ) : β :=
  if v<n then cell v else cell (initialEndpoint bs (v-n))

theorem initialCell_old {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β)
    (v : ℕ) (hv : v<n) : initialCell n bs cell v=cell v := by
  simp only [initialCell,hv,ite_true, if_true]

theorem initialCell_new {β : Type*} (n : ℕ) (bs : List Bond) (cell : ℕ → β) (j : ℕ) :
    initialCell n bs cell (n+j)=cell (initialEndpoint bs j) := by
  have hn : ¬n+j<n := by omega
  simp only [initialCell,hn,ite_false, if_false,Nat.add_sub_cancel_left]

theorem initial_cellAligned {β : Type*} (n : ℕ) (bs : List Bond) (c N : ℚ)
    (cell : ℕ → β) : CellAligned (initial n bs c N) (initialCell n bs cell) := by
  intro i j
  have hj₀ := j.isLt
  generalize hkj : j.val=k at hj₀ ⊢
  clear hkj j
  have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
  have hg : groupAt (initial n bs c N).2.2.2 i.val=
      initialGroup n bs (initialScale N bs c) i.val := initial_groupAt _ _ _ _ hi
  have hj : k<(initialIndices bs i.val).length := by
    have hh := hj₀
    rw [hg] at hh
    simpa only [initialGroup,List.length_map] using hh
  rw [hg,initialGroup_portAt _ _ _ _ _ hj,initialCell_new,initialCell_old _ _ _ _ hi]
  have he := (initialIndices_mem bs i.val _ (List.getElem_mem hj)).2
  rw [he]

theorem initial_cellLocal {β : Type*} (n : ℕ) (bs : List Bond) (c N : ℚ)
    (cell : ℕ → β) (R : β → β → Prop) (hl : BondLocal bs cell R) :
    BondLocal (initial n bs c N).2.1 (initialCell n bs cell) R := by
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  have he' : e<bs.length := List.mem_range.mp he
  have hh := hl (bs[e]) (List.getElem_mem he')
  have hleft := initialEndpoint_even bs ⟨e,he'⟩
  have hright := initialEndpoint_odd bs ⟨e,he'⟩
  change R (initialCell n bs cell (n+2*e)) (initialCell n bs cell (n+2*e+1))
  rw [initialCell_new,show n+2*e+1=n+(2*e+1) by omega,initialCell_new,hleft,hright]
  exact hh

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial subdivision computes its row/column array from the actual
endpoint list, before the same fixed-round grid program is applied. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList MediatorListProgram ExactQuantumFactoring.BitStackProgram

abbrev InitialCells := ℕ × (List Bond × List QuantumRouteCode.Pair)

def initialCells (x : InitialCells) : List QuantumRouteCode.Pair :=
  (List.range (x.1+2*x.2.1.length)).map (initialCell x.1 x.2.1 (lookup x.2.2))

abbrev PreparedInput := InitialInput × List QuantumRouteCode.Pair

def prepare (x : PreparedInput) : Input :=
  (x.1.1,(initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1,
    initialCells (x.1.2.1,x.1.2.2.1,x.2)))

def output (k : ℕ) (x : PreparedInput) : Cells := run k (prepare x)

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitialCells
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial private ports and all subsequent fork vertices retain bounded cell density. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {n m : ℕ} {β : Type*}

def qmaSubdivisionCell (left right : Fin m → Fin n) (cell : Fin n → β) : Fin (n+m*2) → β :=
  Sum.elim cell (fun p => cell (qmaOriginalEndpoint left right p)) ∘ (vertexEquiv n m).symm

@[simp] theorem qmaSubdivisionCell_old (left right : Fin m → Fin n) (cell : Fin n → β)
    (i : Fin n) : qmaSubdivisionCell left right cell (old n m i) = cell i := by
  simp [qmaSubdivisionCell,old]

@[simp] theorem qmaSubdivisionCell_fresh (left right : Fin m → Fin n) (cell : Fin n → β)
    (e : Fin m) (b : Fin 2) :
    qmaSubdivisionCell left right cell (fresh n m e b) = cell (qmaOriginalEndpoint left right (e,b)) := by
  simp [qmaSubdivisionCell,fresh]

theorem qmaSubdivisionCell_mass [DecidableEq β] (left right : Fin m → Fin n)
    (cell : Fin n → β) (x : β) :
    qmaCellMass (qmaSubdivisionCell left right cell) x = qmaCellMass cell x +
      ∑ p : Fin m × Fin 2, if cell (qmaOriginalEndpoint left right p) = x then 1 else 0 := by
  unfold qmaCellMass
  rw [← (vertexEquiv n m).sum_comp,Fintype.sum_sum_type]
  simp only [qmaSubdivisionCell,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

theorem qmaSubdivisionCell_mass_le [DecidableEq β] (left right : Fin m → Fin n)
    (cell : Fin n → β) (D : ℕ) (hd : ∀ i, qmaOriginalPortCount left right i ≤ D) (x : β) :
    qmaCellMass (qmaSubdivisionCell left right cell) x ≤ (D+1)*qmaCellMass cell x := by
  rw [qmaSubdivisionCell_mass]
  have hs := (qmaOriginalPortEquiv left right).sum_comp
    (fun p => if cell (qmaOriginalEndpoint left right p) = x then (1:ℕ) else 0)
  simp only [qmaOriginalPortEquiv_endpoint,Fintype.sum_sigma] at hs
  have hb : (∑ i : Fin n, ∑ _j : Fin (qmaOriginalPortCount left right i),
      if cell i = x then (1:ℕ) else 0) ≤ D*qmaCellMass cell x := by
    unfold qmaCellMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hx : cell i = x
    · simpa only [hx,ite_true, if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        smul_eq_mul,Nat.mul_one] using hd i
    · simp [hx]
  rw [← hs]
  calc
    _ ≤ qmaCellMass cell x+D*qmaCellMass cell x := Nat.add_le_add_left hb _
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCellMass
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal fork round has bounded density in the original coarse cells.
The proof counts its actual fresh indices through the ordered pair catalog. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph
open scoped BigOperators Classical
variable {β : Type*} [DecidableEq β]

theorem next_cell_mass (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (p : β) :
    qmaCellMass (fun v : Fin (next N s).1 => nextCell s cell v.val) p =
      qmaCellMass (fun v : Fin s.1 => cell v.val) p+
      2*∑ e : Fin (pairCount s.2.2.2), if cell (localPair s.2.2.2 e).1.val=p then 1 else 0 := by
  unfold qmaCellMass
  change (∑ v : Fin (s.1+2*pairCount s.2.2.2), if nextCell s cell v.val=p then 1 else 0)=_
  rw [show s.1+2*pairCount s.2.2.2=s.1+pairCount s.2.2.2*2 by omega]
  rw [← (vertexEquiv s.1 (pairCount s.2.2.2)).sum_comp]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two]
  have ho (v : Fin s.1) :
      nextCell s cell (vertexEquiv s.1 (pairCount s.2.2.2) (Sum.inl v)).val=cell v.val := by
    change nextCell s cell (old s.1 (pairCount s.2.2.2) v).val=cell v.val
    simpa only [MediatorIteration.old_val] using nextCell_old s cell v.val v.isLt
  have hf (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
      nextCell s cell (vertexEquiv s.1 (pairCount s.2.2.2) (Sum.inr (e,b))).val=
        cell (localPair s.2.2.2 e).1.val := by
    change nextCell s cell (fresh s.1 (pairCount s.2.2.2) e b).val=_
    simpa only [MediatorIteration.fresh_val,Nat.mul_comm,actualSite,Matrix.cons_val_zero] using
      nextCell_fresh s hs cell e b
  simp_rw [ho,hf]
  rw [Finset.sum_add_distrib]
  omega

theorem pair_cell_mass_le (s : State) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D) (p : β) :
    (∑ e : Fin (pairCount s.2.2.2), if cell (localPair s.2.2.2 e).1.val=p then 1 else 0) ≤
      D*qmaCellMass (fun i : Fin s.2.2.2.length => cell i.val) p := by
  have he := (pairEquiv s.2.2.2).symm.sum_comp
    (fun q : LocalPair s.2.2.2 => if cell q.1.val=p then (1:ℕ) else 0)
  change (∑ e : Fin (pairCount s.2.2.2),
    (fun q : LocalPair s.2.2.2 => if cell q.1.val=p then (1:ℕ) else 0)
      ((pairEquiv s.2.2.2).symm e)) ≤ _
  rw [he]
  simp only [LocalPair,Fintype.sum_sigma,qmaCellMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : cell i.val=p
  · simp only [hi,ite_true, if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one]
    exact (Nat.div_le_self _ _).trans (hd i)
  · simp [hi]

theorem next_cell_mass_le (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D) (p : β) :
    qmaCellMass (fun v : Fin (next N s).1 => nextCell s cell v.val) p ≤
      (1+2*D)*qmaCellMass (fun v : Fin s.1 => cell v.val) p := by
  rw [next_cell_mass s hs N cell p]
  have hp := pair_cell_mass_le s cell D hd p
  have hc := prefix_cell_mass_le s.2.2.2.length s.1 hs.centers cell p
  calc
    _ ≤ qmaCellMass (fun v : Fin s.1 => cell v.val) p+
        2*(D*qmaCellMass (fun i : Fin s.2.2.2.length => cell i.val) p) := by omega
    _ ≤ qmaCellMass (fun v : Fin s.1 => cell v.val) p+
        2*(D*qmaCellMass (fun i : Fin s.1 => cell i.val) p) := by gcongr
    _ = _ := by ring

theorem iterate_group_le (s : State) (N : ℚ) (k i : ℕ) (hi : i < s.2.2.2.length) :
    (groupAt (iterate N k s).2.2.2 i).length ≤ (groupAt s.2.2.2 i).length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterate,next_group_length N (iterate N k s) i (by rwa [iterate_centers])]
    omega

theorem iterate_cell_mass_le (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (N : ℚ) (cell : ℕ → β) (D : ℕ)
    (hd : ∀ i : Fin s.2.2.2.length, (groupAt s.2.2.2 i.val).length ≤ D)
    (k : ℕ) (p : β) :
    qmaCellMass (fun v : Fin (iterate N k s).1 => iterateCell N k s cell v.val) p ≤
      (1+2*D)^k*qmaCellMass (fun v : Fin s.1 => cell v.val) p := by
  induction k with
  | zero => simp only [iterate,iterateCell,pow_zero,one_mul,le_refl]
  | succ k ih =>
    have hd' : ∀ i : Fin (iterate N k s).2.2.2.length,
        (groupAt (iterate N k s).2.2.2 i.val).length ≤ D := by
      intro i
      have hi : i.val < s.2.2.2.length := by simpa only [iterate_centers] using i.isLt
      exact (iterate_group_le s N k i.val hi).trans (hd ⟨i.val,hi⟩)
    have hn := next_cell_mass_le (iterate N k s) (iterate_validPorts N s hs k)
      N (iterateCell N k s cell) D hd' p
    change qmaCellMass (fun v : Fin (next N (iterate N k s)).1 =>
      nextCell (iterate N k s) (iterateCell N k s cell) v.val) p ≤ _
    calc
      _ ≤ (1+2*D)*qmaCellMass (fun v : Fin (iterate N k s).1 =>
          iterateCell N k s cell v.val) p := hn
      _ ≤ (1+2*D)*((1+2*D)^k*qmaCellMass (fun v : Fin s.1 => cell v.val) p) :=
        Nat.mul_le_mul_left _ ih
      _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial cell array has the original endpoint multiplicities.
Together with fixed fork rounds this gives a constant coarse-cell density. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph MediatorListProgram
open scoped BigOperators Classical
variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
theorem initialCell_eq_subdivision (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (cell : ℕ → β) (v : Fin (n+bs.length*2)) :
    initialCell n bs cell v.val=
      qmaSubdivisionCell (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun i => cell i.val) v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv n bs.length).surjective v
  rcases v with i | ⟨e,b⟩
  · change initialCell n bs cell (old n bs.length i).val=_
    rw [MediatorIteration.old_val,initialCell_old n bs cell i.val i.isLt]
    exact (qmaSubdivisionCell_old (SourceBondLists.bonds n bs hb).left
      (SourceBondLists.bonds n bs hb).right (fun j => cell j.val) i).symm
  · change initialCell n bs cell (fresh n bs.length e b).val=_
    refine Eq.trans ?_ (qmaSubdivisionCell_fresh
      (SourceBondLists.bonds n bs hb).left (SourceBondLists.bonds n bs hb).right
      (fun j => cell j.val) e b).symm
    rw [MediatorIteration.fresh_val]
    fin_cases b
    · simp only [Nat.add_zero]
      rw [initialCell_new,initialEndpoint_even]
      rfl
    · rw [Nat.add_assoc,initialCell_new,initialEndpoint_odd]
      rfl

theorem initial_cell_mass_le (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ b ∈ bs, b.1 ≠ b.2.1)
    (c N : ℚ) (cell : ℕ → β) (D : ℕ) (hd : ∀ i : Fin n, degree bs i.val ≤ D) (p : β) :
    qmaCellMass (fun v : Fin (initial n bs c N).1 => initialCell n bs cell v.val) p ≤
      (D+1)*qmaCellMass (fun v : Fin n => cell v.val) p := by
  change qmaCellMass (fun v : Fin (n+2*bs.length) => initialCell n bs cell v.val) p ≤ _
  rw [show n+2*bs.length=n+bs.length*2 by omega]
  have he : (fun v : Fin (n+bs.length*2) => initialCell n bs cell v.val)=
      qmaSubdivisionCell (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun v => cell v.val) :=
    funext (initialCell_eq_subdivision n bs hb cell)
  rw [he]
  apply qmaSubdivisionCell_mass_le
  intro i
  rw [qmaOriginalPortCount_eq_degree _ _ (SourceBondLists.bonds_noLoops n bs hb hn),
    ← degree_eq_graph]
  exact hd i

theorem initial_iterate_cell_mass_le (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ b ∈ bs, b.1 ≠ b.2.1)
    (c N : ℚ) (cell : ℕ → β) (D : ℕ) (hd : ∀ i : Fin n, degree bs i.val ≤ D)
    (k : ℕ) (p : β) :
    qmaCellMass (fun v : Fin (iterate N k (initial n bs c N)).1 =>
      iterateCell N k (initial n bs c N) (initialCell n bs cell) v.val) p ≤
        ((1+2*D)^k*(D+1))*qmaCellMass (fun v : Fin n => cell v.val) p := by
  have hg : ∀ i : Fin (initial n bs c N).2.2.2.length,
      (groupAt (initial n bs c N).2.2.2 i.val).length ≤ D := by
    intro i
    have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
    change (groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i.val).length ≤ D
    rw [initial_groupAt _ _ _ _ hi]
    simp only [initialGroup,List.length_map,initialIndices_length_eq_degree bs hn]
    exact hd ⟨i.val,hi⟩
  have h := iterate_cell_mass_le (initial n bs c N) (initial_validPorts n bs c N) N
    (initialCell n bs cell) D hg k p
  calc
    _ ≤ (1+2*D)^k*qmaCellMass
        (fun v : Fin (initial n bs c N).1 => initialCell n bs cell v.val) p := h
    _ ≤ (1+2*D)^k*((D+1)*qmaCellMass (fun v : Fin n => cell v.val) p) :=
      Nat.mul_le_mul_left _ (initial_cell_mass_le n bs hb hn c N cell D hd p)
    _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListFullCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full emitted bond list, including active ports, keeps the original
common-cell locality relation through initial subdivision and all fork rounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

theorem activeBonds_mem {gs : Groups} {b : Bond} (hb : b ∈ activeBonds gs) :
    ∃ (i : Fin gs.length) (j : Fin (groupAt gs i.val).length),
      b=(i.val,(portAt (groupAt gs i.val) j.val).1,
        (portAt (groupAt gs i.val) j.val).2) := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  obtain ⟨j,hj⟩ := List.get_of_mem hp
  refine ⟨⟨i,List.mem_range.mp hi⟩,j,?_⟩
  have he : portAt (groupAt gs i) j.val=p := by
    rw [portAt_eq_getElem _ _ j.isLt]
    exact hj
  rw [he]

theorem activeBonds_valid {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (b : Bond) (hb : b ∈ activeBonds gs) :
    b.1<n ∧ b.2.1<n ∧ b.1≠b.2.1 := by
  obtain ⟨i,j,rfl⟩ := activeBonds_mem hb
  exact ⟨lt_of_lt_of_le i.isLt h.centers,h.bounded i j,h.disjoint i i j⟩

theorem activeBonds_cellLocal {β : Type*} (s : State) (cell : ℕ → β)
    (ha : CellAligned s cell) (R : β → β → Prop) (hr : ∀ x, R x x) :
    BondLocal (activeBonds s.2.2.2) cell R := by
  intro b hb
  obtain ⟨i,j,rfl⟩ := activeBonds_mem hb
  change R (cell i.val) (cell (portAt (groupAt s.2.2.2 i.val) j.val).1)
  rw [ha i j]
  exact hr _

theorem full_cellLocal {β : Type*} (s : State) (cell : ℕ → β)
    (ha : CellAligned s cell) (R : β → β → Prop) (hr : ∀ x, R x x)
    (hl : BondLocal s.2.1 cell R) :
    BondLocal (s.2.1++activeBonds s.2.2.2) cell R := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hl b hb
  · exact activeBonds_cellLocal s cell ha R hr b hb

theorem initial_iterate_full_cellLocal {β : Type*} (n : ℕ) (bs : List Bond)
    (c N : ℚ) (cell : ℕ → β) (R : β → β → Prop) (hr : ∀ x, R x x)
    (hl : BondLocal bs cell R) (k : ℕ) :
    BondLocal ((iterate N k (initial n bs c N)).2.1++
      activeBonds (iterate N k (initial n bs c N)).2.2.2)
      (iterateCell N k (initial n bs c N) (initialCell n bs cell)) R := by
  apply full_cellLocal
  · exact iterate_cellAligned N _ (initial_validPorts n bs c N) _
      (initial_cellAligned n bs c N cell) k
  · exact hr
  · exact iterate_cellLocal N _ (initial_validPorts n bs c N)
      (initial_ordinary_bounded n bs c N) _ (initial_cellAligned n bs c N cell)
      R hr (initial_cellLocal n bs c N cell R hl) k

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridMidpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer midpoints choose a common neighboring cell deterministically.
Their coordinate map has a literal polynomial register program. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def qmaGridMidpoint {rows width : ℕ} (p q : QMAGridCell rows width) :
    QMAGridCell rows width :=
  (⟨(p.1.val+q.1.val)/2,by have := p.1.isLt; have := q.1.isLt; omega⟩,
   ⟨(p.2.val+q.2.val)/2,by have := p.2.isLt; have := q.2.isLt; omega⟩)

theorem qmaGridMidpoint_near {rows width : ℕ} (p q a : QMAGridCell rows width)
    (hp : QMAGridCellsNear p a) (hq : QMAGridCellsNear q a) :
    QMAGridCellsNear p (qmaGridMidpoint p q) ∧
      QMAGridCellsNear q (qmaGridMidpoint p q) := by
  rcases hp with ⟨hp₁,hp₂,hp₃,hp₄⟩
  rcases hq with ⟨hq₁,hq₂,hq₃,hq₄⟩
  unfold QMAGridCellsNear qmaGridMidpoint
  dsimp only
  omega

namespace QuantumGridMidpoint

def value (x : Pair × Pair) : Pair :=
  ((x.1.1+x.2.1)/2,(x.1.2+x.2.2)/2)

end QuantumGridMidpoint
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalSpatialPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package the rational degree-three graph with its proved coarse-grid placement. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaDegreeThreeSpatialModel {ν : Type} [Fintype ν] {n rows width A : ℕ}
    (left right : ν → Fin n) (distinct : ∀ e, left e ≠ right e)
    (weight : ν → ℚ) (constant : ℚ)
    (cell : Fin n → QMAGridCell rows width) (anchor : ν → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A)
    (hd : ∀ v, qmaGraphDegree left right v ≤ 3)
    (hl : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e) ∧
      QMAGridCellsNear (cell (right e)) (anchor e)) : QMASpatialExchangeModel A (27*A) where
  n := n
  Term := ν
  left := left
  right := right
  distinct := distinct
  weight := weight
  constant := constant
  rows := rows
  width := width
  cell := cell
  anchor := anchor
  geometry := hl
  qubitDensity := hc
  termDensity := by
    intro p
    have h := qmaAnchor_density left right cell anchor (fun e => (hl e).1) hc hd p
    simpa only [show 9*A*3 = 27*A by omega] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package the literal full fork graph with deterministic midpoint anchors.
The package keeps its actual spin indices, coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def fullList (s : State) : List Bond := s.2.1++activeBonds s.2.2.2

theorem fullList_bounded (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) : SourceBondLists.bounded s.1 (fullList s) := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hb b hm
  · exact ⟨(activeBonds_valid hs b hm).1,(activeBonds_valid hs b hm).2.1⟩

theorem fullList_noLoops (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) : ∀ b ∈ fullList s, b.1≠b.2.1 := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hn b hm
  · exact (activeBonds_valid hs b hm).2.2

def CommonCell {rows width : ℕ} (p q : QMAGridCell rows width) : Prop :=
  ∃ a, QMAGridCellsNear p a ∧ QMAGridCellsNear q a

theorem commonCell_refl {rows width : ℕ} (p : QMAGridCell rows width) : CommonCell p p :=
  ⟨p,qmaGridCellsNear_refl p,qmaGridCellsNear_refl p⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkRoutingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal routing-input tape from the full fork state. Active-star bonds
are retained, and each anchor is the integer midpoint of its endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingData
open ExactQuantumFactoring.BitStackProgram QuantumForkList MediatorListProgram

def star (x : ℕ × Port) : Bond := (x.1,x.2.1,x.2.2)

def endpoint (b : Bond) : QuantumRouteCode.Pair := (b.1,b.2.1)

abbrev Query := Bond × List QuantumRouteCode.Pair

def anchor (x : Query) : QuantumRouteCode.Pair := QuantumGridMidpoint.value
  (QuantumForkGridProgram.lookup x.2 x.1.1,QuantumForkGridProgram.lookup x.2 x.1.2.1)

def value (x : QuantumForkGridProgram.Cells) : QuantumRoutingInputProgram.Data :=
  ((x.2,(fullList x.1).map (fun b => anchor (b,x.2))),
    (fullList x.1).map endpoint)

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual edge-indexed schedule represented by a literal bond/work tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram
open scoped Classical

def graph (s : State) (hs : Valid s) : QMARationalExchangeGraph where
  n := s.1
  Edge := Fin s.2.2.length
  left i := ⟨(s.2.2.get i).2.1,
    (hs.1 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩)).1⟩
  right i := ⟨(s.2.2.get i).2.2.1,
    (hs.1 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩)).2⟩
  weight i := (s.2.2.get i).2.2.2
  constant := s.2.1
  distinct i h := hs.2 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩) (congrArg Fin.val h)

def schedule (s : State) (hs : Valid s) : QMAPathSchedule where
  graph := graph s hs
  work i := (s.2.2.get i).1

theorem schedule_active (s : State) (hs : Valid s) (i : (schedule s hs).graph.Edge) :
    i ∈ (schedule s hs).active ↔ 0<(s.2.2.get i).1 :=
  QMAPathSchedule.mem_active (schedule s hs) i

def indices (b : Bool) (xs : List Entry) : List (Fin xs.length) :=
  (List.finRange xs.length).filter (fun i => selected b (xs.get i))

theorem indices_nodup (b : Bool) (xs : List Entry) : (indices b xs).Nodup :=
  (List.nodup_finRange _).filter _

theorem indices_map (b : Bool) (xs : List Entry) :
    (indices b xs).map xs.get = partition b xs := by
  unfold indices partition
  have h : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map,List.ofFn_get]
  calc
    _ = ((List.finRange xs.length).map xs.get).filter (selected b) := List.filter_map.symm
    _ = _ := congrArg (List.filter (selected b)) h

theorem mem_indices (b : Bool) (xs : List Entry) (i : Fin xs.length) :
    i ∈ indices b xs ↔ selected b (xs.get i) = true := by
  simp only [indices,List.mem_filter,List.mem_finRange,true_and]

theorem indices_length (b : Bool) (xs : List Entry) :
    (indices b xs).length=(partition b xs).length := by
  have h := congrArg List.length (indices_map b xs)
  simpa only [List.length_map] using h

def indexEquiv (b : Bool) (xs : List Entry) :
    Fin (partition b xs).length ≃ {i : Fin xs.length // selected b (xs.get i)=true} :=
  (finCongr (indices_length b xs).symm).trans
    (((indices_nodup b xs).getEquiv (indices b xs)).trans
      (Equiv.subtypeEquivRight (mem_indices b xs)))

theorem indexEquiv_get (b : Bool) (xs : List Entry) (i : Fin (partition b xs).length) :
    xs.get (indexEquiv b xs i).val=(partition b xs).get i := by
  change xs.get ((indices b xs).get (Fin.cast (indices_length b xs).symm i)) = _
  have hil : i.val<(indices b xs).length := by rw [indices_length]; exact i.isLt
  have h := congrArg (fun ys : List Entry => ys[i.val]?) (indices_map b xs)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hil,List.getElem?_eq_getElem i.isLt,
    Option.map_some,Option.some.injEq,List.get_eq_getElem,Fin.val_cast] using h

theorem selected_true_iff (e : Entry) : selected true e=true ↔ 0<e.1 := by
  by_cases h : e.1=0
  · simp [selected,h]
  · simp [selected,h]
    omega

theorem selected_false_iff (e : Entry) : selected false e=true ↔ e.1=0 := by
  by_cases h : e.1=0 <;> simp [selected,h]

def activeEquiv (s : State) (hs : Valid s) :
    Fin (partition true s.2.2).length ≃ {i : (graph s hs).Edge // i ∈ (schedule s hs).active} :=
  (indexEquiv true s.2.2).trans (Equiv.subtypeEquivRight (fun i =>
    (selected_true_iff (s.2.2.get i)).trans (schedule_active s hs i).symm))

def activePermutation (s : State) (hs : Valid s) :
    Fin (partition true s.2.2).length ≃ Fin (schedule s hs).active.card :=
  (activeEquiv s hs).trans (schedule s hs).active.equivFin

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The route-array filter selects exactly the same source indices as the
literal work-list filter, preserving their order. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule

def decoratedEntry (x : Input) (i : Fin x.2.1.2.2.length) : Routed :=
  (x.2.1.2.2.get i,(x.2.2.2.drop i.val).headD [])

theorem decorated_eq (x : Input) : decorated x=List.ofFn (decoratedEntry x) := by
  have h := (List.ofFn_getElem_eq_map (List.range x.2.1.2.2.length)
    (fun i => indexed (i,x))).symm
  simp only [List.length_range,List.getElem_range] at h
  rw [decorated,h]
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun e => (e,(x.2.2.2.drop i.val).headD []))
    (headD_drop x.2.1.2.2 zeroEntry i)

theorem selectedRoutes_eq (b : Bool) (x : Input) :
    selectedRoutes b x=(QuantumListSchedule.indices b x.2.1.2.2).map (decoratedEntry x) := by
  rw [selectedRoutes,decorated_eq,List.ofFn_eq_map,List.filter_map]
  rfl

theorem selectedRoutes_length (b : Bool) (x : Input) :
    (selectedRoutes b x).length=(partition b x.2.1.2.2).length := by
  rw [selectedRoutes_eq,List.length_map,indices_length]

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-list ordering gives an explicit correspondence with the
abstract schedule's fresh spins. Retained source spins keep their labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph

theorem active_source (s : State) (hs : Valid s) (i : Fin (partition true s.2.2).length) :
    s.2.2.get (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) =
      (partition true s.2.2).get i := by
  have he : qmaSelectedIndex (schedule s hs).active (activePermutation s hs i) =
      (activeEquiv s hs i).val :=
    congrArg Subtype.val ((schedule s hs).active.equivFin.symm_apply_apply (activeEquiv s hs i))
  exact (congrArg (fun j : (schedule s hs).graph.Edge => s.2.2.get j) he).trans
    (indexEquiv_get true s.2.2 i)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact edge order in the emitted next-round list: retained edges followed
by three consecutive edges for each selected source edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram

abbrev Tags (x : Input) := Fin (partition false x.2.2.2).length ⊕
  (Fin (partition true x.2.2.2).length × Fin 3)

def flatTagEquiv (x : Input) :
    Fin ((partition false x.2.2.2).length+(partition true x.2.2.2).length*3) ≃ Tags x :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)

theorem family_ofFn (x : Input) : family x =
    (List.ofFn fun i : Fin (partition true x.2.2.2).length => block (indexed (i.val,x))).flatten := by
  have h : (List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x))) =
      List.ofFn (fun i : Fin (partition true x.2.2.2).length => block (indexed (i.val,x))) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range (partition true x.2.2.2).length)
        (fun i => block (indexed (i,x)))).symm
  exact congrArg List.flatten h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact emitted edge order realizes the abstract scheduled subdivision.
This transfers the disjoint-route invariant to the literal list compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph
open scoped Classical

theorem oldValue (n r : ℕ) (i : Fin n) : (old n r i).val=i.val := rfl

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation of a scheduled embedding by finite position and route arrays. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

def Represents (x : State) (hx : Valid x.1)
    (P : QMAPathEmbedding (schedule x.1 hx) Γ) : Prop :=
  x.2.1=List.ofFn P.position ∧
    x.2.2=List.ofFn (fun e => (List.range (2*(schedule x.1 hx).work e+2)).map (P.point e))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePathOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output path array has exactly the output bond array's tag order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode

def pathPiece (r : Routed) : Fin 3 → List Pair :=
  ![[lookup r.2 1,lookup r.2 2],[lookup r.2 0,lookup r.2 1],(r.2.drop 2).reverse]

def tagPath (x : Input) : Tags (x.1,x.2.1) → List Pair
  | .inl i => (decoratedEntry x (indexEquiv false x.2.1.2.2 i).val).2
  | .inr (i,k) => pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val) k

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-density local input list yields the actual degree-three
spatial output, with its full Hamiltonian and fixed density constant. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

structure SpatialInput (rows width A D : ℕ) where
  n : ℕ
  bonds : List Bond
  constant : ℚ
  precision : ℚ
  cell : ℕ → QMAGridCell rows width
  bounded : SourceBondLists.bounded n bonds
  noLoops : ∀ b ∈ bonds, b.1≠b.2.1
  degree : ∀ v : Fin n, QuantumForkList.degree bonds v.val ≤ D
  density : ∀ p, qmaCellMass (fun v : Fin n => cell v.val) p ≤ A
  locality : BondLocal bonds cell CommonCell

namespace SpatialInput
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

def state : State := iterate I.precision D (initial I.n I.bonds I.constant I.precision)

def cells : ℕ → QMAGridCell rows width :=
  iterateCell I.precision D (initial I.n I.bonds I.constant I.precision)
    (initialCell I.n I.bonds I.cell)

theorem validPorts : ValidPorts I.state.1 I.state.2.2.2 :=
  iterate_validPorts _ _ (initial_validPorts _ _ _ _) _

theorem state_bounded : SourceBondLists.bounded I.state.1 I.state.2.1 :=
  iterate_ordinary_bounded _ _ (initial_validPorts _ _ _ _) (initial_ordinary_bounded _ _ _ _) _

theorem state_noLoops : ∀ b ∈ I.state.2.1, b.1≠b.2.1 :=
  iterate_ordinary_noLoops _ _ (initial_validPorts _ _ _ _) (initial_ordinary_noLoops _ _ _ _) _

theorem state_density (p : QMAGridCell rows width) :
    qmaCellMass (fun v : Fin I.state.1 => I.cells v.val) p ≤ spatialDensity A D := by
  have h := initial_iterate_cell_mass_le I.n I.bonds I.bounded I.noLoops
    I.constant I.precision I.cell D I.degree D p
  exact h.trans (Nat.mul_le_mul_left _ (I.density p))

theorem state_degree (v : Fin I.state.1) : QuantumForkList.degree (fullList I.state) v.val ≤ 3 :=
  initial_iterate_full_degree_of_bound I.n I.bonds I.noLoops I.constant I.precision D I.degree v

theorem state_locality : BondLocal (fullList I.state) I.cells CommonCell :=
  initial_iterate_full_cellLocal I.n I.bonds I.constant I.precision I.cell CommonCell
    commonCell_refl I.locality D

end SpatialInput
end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-round realization of the computed spatial graph on its port
paths. The finite tape carries the actual spin positions throughout subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialPortProgram
open ExactQuantumFactoring.BitStackProgram QuantumForkList QuantumRouteCode

abbrev Input := ℚ × QuantumForkGridProgram.PreparedInput

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialCrossingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal composition from the prepared spatial input to the crossing
Hamiltonian, its physical positions, and the finite routing permission table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumForkList (spatialDensity)

abbrev Input := QuantumSpatialPortProgram.Input

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact three-entry order of the literal even-subdivision output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeProgram
open QuantumListSchedule
open scoped Classical

theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → Entry) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k))=
      (List.ofFn (fun i : Fin m => List.ofFn (fun k : Fin 3 => f (i,k)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumEvenTapeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual rational-register history entries.
The only matrix multiplication takes place on the five-site propagation
core, with at most32 intermediate configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def historyHeight (c : QMACircuit) : ℚ :=
  14+288*((14*(c.work+1)+8)*c.gates.length)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit unary precision controls the total error of all actual
ordered-history coefficients.  The precision is polynomial in the circuit
size and the requested inverse error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators Classical

def coefficientBudget (c : QMACircuit) : ℕ :=
  128*(14+288*((14*(c.work+1)+8)*c.gates.length))

def termBudget (c : QMACircuit) : ℕ := 4096*(4*c.gates.length+2*c.work+9)

def samplePrecision (c : QMACircuit) (N : ℕ) : ℕ :=
  (termBudget c+1)*(coefficientBudget c+1)*N

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryXZPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit inverse-polynomial thresholds for the actual two-local X/Z
history output. The precision is a fixed linear unary function of clock length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory

def xzYesThreshold (c : QMACircuit) : ℚ := 7/(20*(c.gates.length+1:ℚ))
def xzNoThreshold (c : QMACircuit) : ℚ := 23/(60*(c.gates.length+1:ℚ))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeSerialization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal serialization of rational lattice graphs into the published source
format. The constant matrix offset is subtracted from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLatticeSerialization
open ExactQuantumFactoring.BitStackProgram
open MediatorListProgram

abbrev Input := List Coordinate × (List Bond × (ℚ × (ℚ × ℚ)))
def coordinateCode : Coordinate → List Bool := prodCode intCode intCode
def thresholdCode : (ℚ × (ℚ × ℚ)) → List Bool := prodCode ratCode (prodCode ratCode ratCode)

def edge (b : Bond) : BinaryHeisenbergEdge := ⟨b.1,b.2.1,BinaryRational.ofRat b.2.2⟩
def value (x : Input) : BinaryHeisenberg where
  coordinate := x.1
  edges := x.2.1.map edge
  lower := BinaryRational.ofRat (x.2.2.1-x.2.2.2.2)
  upper := BinaryRational.ofRat (x.2.2.2.1-x.2.2.2.2)

@[simp] theorem lower_value (x : Input) : (value x).lower.value = x.2.2.1-x.2.2.2.2 :=
  BinaryRational.value_ofRat _
@[simp] theorem upper_value (x : Input) : (value x).upper.value = x.2.2.2.1-x.2.2.2.2 :=
  BinaryRational.value_ofRat _
@[simp] theorem edges_length (x : Input) : (value x).edges.length = x.2.1.length := by simp [value]

end ContinuumCoulomb.QuantumLatticeSerialization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEncoding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source objects serialize to valid binary instances with canonical
rational coefficients and the same physical sites and thresholds. -/

namespace ContinuumCoulomb.SquareLatticeHeisenberg

def binaryEdge (d : SquareLatticeHeisenberg) (i : Fin d.edges) : BinaryHeisenbergEdge :=
  ⟨d.left i,d.right i,BinaryRational.ofRat (d.coefficient i)⟩

def binary (d : SquareLatticeHeisenberg) : BinaryHeisenberg where
  coordinate := List.ofFn d.coordinate
  edges := List.ofFn d.binaryEdge
  lower := BinaryRational.ofRat d.lower
  upper := BinaryRational.ofRat d.upper

@[simp] theorem binary_vertices (d : SquareLatticeHeisenberg) : d.binary.coordinate.length = d.vertices :=
  List.length_ofFn
@[simp] theorem binary_edges (d : SquareLatticeHeisenberg) : d.binary.edges.length = d.edges :=
  List.length_ofFn

@[simp] theorem binary_lower (d : SquareLatticeHeisenberg) : d.binary.lower.value = d.lower :=
  BinaryRational.value_ofRat _
@[simp] theorem binary_upper (d : SquareLatticeHeisenberg) : d.binary.upper.value = d.upper :=
  BinaryRational.value_ofRat _

end ContinuumCoulomb.SquareLatticeHeisenberg

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The merged tape has one strictly ordered edge per occurring vertex pair,
and its coefficients grow by at most the original edge count. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

def supportIndex (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    Fin (support n xs).length := ⟨i.val,by simpa only [value,List.length_map] using i.isLt⟩

theorem value_pair (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    (((value n xs).get i).1, ((value n xs).get i).2.1) =
      (support n xs).get (supportIndex n xs i) := by
  exact congrArg (fun e : Bond => (e.1,e.2.1)) (value_get n xs i)

theorem value_pair_injective (n : ℕ) (xs : List Bond) :
    Function.Injective (fun i : Fin (value n xs).length =>
      (((value n xs).get i).1,((value n xs).get i).2.1)) := by
  intro i j h
  have hp := (value_pair n xs i).symm.trans (h.trans (value_pair n xs j))
  exact Fin.ext (congrArg (fun k : Fin (support n xs).length => k.val)
    ((support_nodup n xs).injective_get hp))

theorem value_ordered {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) : ∀ e ∈ value n xs, e.1<e.2.1 := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨b,hb,hbp⟩ := List.mem_map.mp hm
  subst p
  exact min_lt_max.mpr (h b hb)

theorem value_simple {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) (i j : Fin (value n xs).length) (hij : i≠j) :
    ¬(((value n xs).get i).1=((value n xs).get j).1 ∧
      ((value n xs).get i).2.1=((value n xs).get j).2.1) ∧
    ¬(((value n xs).get i).1=((value n xs).get j).2.1 ∧
      ((value n xs).get i).2.1=((value n xs).get j).1) := by
  constructor
  · rintro ⟨hl,hr⟩
    exact hij (value_pair_injective n xs (Prod.ext hl hr))
  · rintro ⟨hl,hr⟩
    have hi := value_ordered h _ (List.get_mem _ i)
    have hj := value_ordered h _ (List.get_mem _ j)
    omega

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed coordinate and bond tapes define a valid lattice
source. Canonical merging preserves its full matrix and scalar threshold shift. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open MediatorListProgram
open QuantumListMerge

def Adjacent (ps : List Pair) (xs : List Bond) (hb : SourceBondLists.bounded ps.length xs) : Prop :=
  ∀ e (he : e ∈ xs), qmaSquareGrid.Adj
    (ps.get ⟨e.1,(hb e he).1⟩) (ps.get ⟨e.2.1,(hb e he).2⟩)

theorem merge_adjacent (ps : List Pair) (xs : List Bond)
    (hb : SourceBondLists.bounded ps.length xs) (ha : Adjacent ps xs hb)
    (e : Bond) (he : e ∈ _root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs) :
    qmaSquareGrid.Adj
      (ps.get ⟨e.1,(bounded ps.length xs e he).1⟩)
      (ps.get ⟨e.2.1,(bounded ps.length xs e he).2⟩) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  obtain ⟨b,hb',hbp⟩ := List.mem_map.mp ((mem_support hb p).mp hp)
  subst p
  by_cases h : b.1 ≤ b.2.1
  · simpa only [ordered,min_eq_left h,max_eq_right h] using ha b hb'
  · have h' : b.2.1 ≤ b.1 := by omega
    simpa only [ordered,min_eq_right h',max_eq_left h'] using (ha b hb').symm

def source (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) : SquareLatticeHeisenberg where
  vertices := ps.length
  vertices_pos := hp
  coordinate i := qmaGridCoordinate (ps.get i)
  coordinate_injective := qmaGridCoordinate_injective.comp hn.injective_get
  edges := (_root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs).length
  left i := ⟨((_root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs).get i).1,
    (bounded ps.length xs _ (List.get_mem _ i)).1⟩
  right i := ⟨((_root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs).get i).2.1,
    (bounded ps.length xs _ (List.get_mem _ i)).2⟩
  coefficient i := ((_root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs).get i).2.2
  adjacent i := qmaGridCoordinate_adj (merge_adjacent ps xs hb ha _ (List.get_mem _ i))
  edge_simple i j hij := by
    have h := value_simple hl i j hij
    constructor
    · rintro ⟨h1,h2⟩
      exact h.1 ⟨congrArg Fin.val h1,congrArg Fin.val h2⟩
    · rintro ⟨h1,h2⟩
      exact h.2 ⟨congrArg Fin.val h1,congrArg Fin.val h2⟩
  lower := a-c
  upper := b-c
  gap_pos := sub_lt_sub_right hab c

end ContinuumCoulomb.QuantumListLattice

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListLatticeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source serialization from the computed coordinate and bond tapes. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Input := List Pair × (List Bond × (ℚ × (ℚ × ℚ)))

def packet (x : Input) : QuantumLatticeSerialization.Input :=
  (x.1.map qmaGridCoordinate,QuantumListMerge.value x.1.length x.2.1,x.2.2)
def value (x : Input) : BinaryHeisenberg := QuantumLatticeSerialization.value (packet x)

noncomputable def coordinateProgram : Procedure pairCode QuantumLatticeSerialization.coordinateCode
    qmaGridCoordinate :=
  (Procedure.natToInt.comp (Procedure.first Nat.bits Nat.bits)).pair
    (Procedure.natToInt.comp (Procedure.second Nat.bits Nat.bits))

end ContinuumCoulomb.QuantumListLattice

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final literal route tape is itself the serialized lattice source.
Its coordinate and edge order are the computed orders, and its exact scalar
offset is removed from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

def latticePacket (s : State) (a b : ℚ) : QuantumListLattice.Input :=
  (s.2.1,erase s.1.2.2,a,b,s.1.2.1)

def latticeOutput (s : State) (a b : ℚ) : BinaryHeisenberg :=
  QuantumListLattice.value (latticePacket s a b)

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision for all nine early simulation errors and the subsequent
routing errors, retaining the exact final inverse-polynomial promise gap. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram

def finalPrecision (rounds : ℕ) (c : QMACircuit) : ℕ :=
  60*(rounds+9)*(c.gates.length+1)

noncomputable def finalPrecisionProgram (rounds : ℕ) :
    Procedure unaryCode unaryCode (fun t => 60*(rounds+9)*(t+1)) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (60*(rounds+9))).pair
    Procedure.unarySuccessor)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-round routing to the serialized square-lattice source. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := QuantumSpatialPortProgram.Input × (ℚ × ℚ)

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient bounds for the actual ordered lists, including every active
port and the scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

structure CoefficientBound (s : State) (L : ℝ) : Prop where
  scalar : |(s.2.2.1:ℝ)| ≤ L
  ordinary : ∀ b ∈ s.2.1, |(b.2.2:ℝ)| ≤ L
  active : ∀ ps ∈ s.2.2.2, ∀ p ∈ ps, |(p.2:ℝ)| ≤ L

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs compute the coefficient envelopes. For each fixed
number of rounds, the complete numerical envelope is polynomial in its inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)
noncomputable def konst {α : Type} (ea : α → List Bool) (n : ℕ) :
    Procedure ea unaryCode (fun _ => n) := Procedure.constant ea unaryCode n
noncomputable def sq {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^2) :=
  (mul p p).congrFun (by intro x; simp only [pow_two])
noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (mul p p) p).congrFun (by intro x; simp only [pow_succ,pow_zero,one_mul])

noncomputable def budgetNatProgram {α : Type} {ea : α → List Bool} {M L : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => budgetNat (M x) (L x)) := by
  let c := konst ea
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 3) pm) (add (c 1) (mul (c 4) pl))))
    (mul (mul (c 12) pm) (sq (add (c 1) (mul (c 2) pl))))) (c 1)).congrFun
      (by intro x; rfl)

noncomputable def radiusNatProgram {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => radiusNat (M x) (L x) (T x)) := by
  let c := konst ea
  let pb := budgetNatProgram pm pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt)) (mul (c 4) pb)) (c 1)).congrFun
    (by intro x; rfl)

noncomputable def coefficientNatProgram {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => coefficientNat (M x) (L x) (T x)) := by
  let c := konst ea
  exact (add (add (c 1) pl) (mul (add (mul (c 10) pm) (c 2))
    (sq (radiusNatProgram pm pl pt)))).congrFun (by intro x; rfl)

noncomputable def envelopeNatProgram (k : ℕ) {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => envelopeNat (M x) (L x) (T x) k) := by
  induction k with
  | zero => exact pl
  | succ k ih => exact coefficientNatProgram pm ih pt

noncomputable def outputCoefficientNatProgram (D : ℕ) :
    Procedure QuantumCoefficientPrograms.inputCode unaryCode
      (fun x => outputCoefficientNat x.1 D x.2.1 x.2.2) := by
  let pm := mul (konst QuantumCoefficientPrograms.inputCode (8*D+3))
    QuantumCoefficientPrograms.mProgram
  let pl := coefficientNatProgram pm QuantumCoefficientPrograms.lProgram QuantumCoefficientPrograms.tProgram
  exact envelopeNatProgram D pm pl QuantumCoefficientPrograms.tProgram

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateEntryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

abbrev Input := ℕ × (ℕ × (QMAGate × QuantumHistoryBitProgram.Data))
def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))

def left (x : Input) : ℕ := gateLeft x.2.2.1 % (x.1+1)
def right (x : Input) : ℕ := gateRight x.2.2.1 % (x.1+1)
def row (x : Input) (k : ℕ) : Fin 2 := QuantumHistoryBitProgram.row x.2.2.2 (x.2.1+k)
def column (x : Input) (k : ℕ) : Fin 2 := QuantumHistoryBitProgram.column x.2.2.2 (x.2.1+k)

def point (x : Input) (k : ℕ) : Bool :=
  if gateTag x.2.2.1 = 2 then
    decide ((row x k).val =
      if k = right x ∧ (column x (left x)).val = 1 then
        1-(column x k).val else (column x k).val)
  else decide (k=left x) || decide ((row x k).val=(column x k).val)

def allWork (x : Input) : Bool := ((List.range (x.1+1)).map (point x)).all id

def entry (x : Input) : Scalar :=
  if allWork x then
    if gateTag x.2.2.1=0 then
      QuantumAlgebraicHistory.hadamard (row x (left x)) (column x (left x))
    else if gateTag x.2.2.1=1 then
      QuantumAlgebraicHistory.phaseT (row x (left x)) (column x (left x))
    else rat 1
  else rat 0

noncomputable opaque leftProgram : Procedure inputCode Nat.bits left := by
  let work := Procedure.unaryToBits.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let tail' := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let gate := (Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp tail'
  exact Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair
    (Procedure.successor.comp work))

noncomputable opaque rightProgram : Procedure inputCode Nat.bits right := by
  let work := Procedure.unaryToBits.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let tail' := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let gate := (Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp tail'
  exact Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair
    (Procedure.successor.comp work))

abbrev PointInput := Input × ℕ
def pointCode : PointInput → List Bool := prodCode inputCode Nat.bits

noncomputable opaque tagProgram : Procedure inputCode Nat.bits (fun x => gateTag x.2.2.1) := by
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let rest := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  exact gateTagProgram.comp
    ((Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp rest)

end ContinuumCoulomb.QuantumGateEntryProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

def entry (n m : ℕ) (w : Fin (n+m) → Fin 4) (x : Input) : QuantumOrderedLabelFamily.Entry :=
  (labels n m w x.2.1,sample x.1 (QuantumPaddedTable.coefficient n m x.2.2 w))

def packet (n m : ℕ) (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  (enumerate (Fin (n+m) → Fin 4)).map (fun w => entry n m w x)

def uniformPacket (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  if x.2.1.length=0 then packet 0 6 x else
  if x.2.1.length=1 then packet 1 5 x else
  if x.2.1.length=2 then packet 2 4 x else
  if x.2.1.length=3 then packet 3 3 x else
  if x.2.1.length=4 then packet 4 2 x else
  if x.2.1.length=5 then packet 5 1 x else packet 6 0 x

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal nearest-neighbor gate compilation. All finite loops use the
unary work bound; malformed gate indices take the original singleton branch. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

abbrev NearestInput := ℕ × QMAGate
def nearestInputCode : NearestInput → List Bool := prodCode unaryCode gateCode

def forwardGuard (x : NearestInput) : Bool :=
  decide (gateLeft x.2+1 ≤ gateRight x.2 ∧ gateRight x.2 ≤ x.1)
def backwardGuard (x : NearestInput) : Bool :=
  decide (gateRight x.2+1 ≤ gateLeft x.2 ∧ gateLeft x.2 ≤ x.1)

def nearestValue (x : NearestInput) : List QMAGate :=
  if gateTag x.2=2 then
    if forwardGuard x then
      adjacentList (gateLeft x.2) (min x.1 (gateRight x.2-gateLeft x.2-1)) true
    else if backwardGuard x then
      adjacentList (gateRight x.2) (min x.1 (gateLeft x.2-gateRight x.2-1)) false
    else [x.2]
  else [x.2]

theorem nearestValue_eq (x : NearestInput) : nearestValue x=qmaNearestGate x.1 x.2 := by
  rcases x with ⟨work,g⟩
  cases g with
  | hadamard i => rfl
  | phaseT i => rfl
  | controlledNot i j =>
    by_cases h : i < j ∧ j < work+1
    · have hg : forwardGuard (work,.controlledNot i j)=true := by
        change decide (i+1 ≤ j ∧ j ≤ work) = true
        simp only [decide_eq_true_eq]
        omega
      have hd : j-i-1 ≤ work := by omega
      simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true, if_true,hg,min_eq_right hd,
        qmaNearestGate,dite_eq_left h]
      exact (adjacentList_eq work i (j-i-1) (by omega) true).symm
    · have hg : forwardGuard (work,.controlledNot i j)=false := by
        change decide (i+1 ≤ j ∧ j ≤ work) = false
        simp only [decide_eq_false_iff_not]
        omega
      by_cases h' : j < i ∧ i < work+1
      · have hr : backwardGuard (work,.controlledNot i j)=true := by
          change decide (j+1 ≤ i ∧ i ≤ work) = true
          simp only [decide_eq_true_eq]
          omega
        have hd : i-j-1 ≤ work := by omega
        simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true, if_true,hg,Bool.false_eq_true,ite_false, if_false,hr,min_eq_right hd,
          qmaNearestGate,dite_eq_right h,dite_eq_left h']
        exact (adjacentList_eq work j (i-j-1) (by omega) false).symm
      · have hr : backwardGuard (work,.controlledNot i j)=false := by
          change decide (j+1 ≤ i ∧ i ≤ work) = false
          simp only [decide_eq_false_iff_not]
          omega
        simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true, if_true,hg,hr,Bool.false_eq_true,ite_false, if_false,
          qmaNearestGate,dite_eq_right h,dite_eq_right h']

noncomputable def workBits : Procedure nearestInputCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode gateCode)
noncomputable def leftBits : Procedure nearestInputCode Nat.bits (fun x => gateLeft x.2) :=
  gateLeftProgram.comp (Procedure.second unaryCode gateCode)
noncomputable def rightBits : Procedure nearestInputCode Nat.bits (fun x => gateRight x.2) :=
  gateRightProgram.comp (Procedure.second unaryCode gateCode)

noncomputable def forwardGuardProgram : Procedure nearestInputCode Procedure.boolCode forwardGuard :=
  (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp ((Procedure.successor.comp leftBits).pair rightBits)).pair
      (Procedure.binaryLe.comp (rightBits.pair workBits)))).congrFun (by
        intro x
        simp [forwardGuard,Function.comp_apply])

noncomputable def backwardGuardProgram : Procedure nearestInputCode Procedure.boolCode backwardGuard :=
  (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp ((Procedure.successor.comp rightBits).pair leftBits)).pair
      (Procedure.binaryLe.comp (leftBits.pair workBits)))).congrFun (by
        intro x
        simp [backwardGuard,Function.comp_apply])

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-number formulas for the checked row sweep. These formulas keep
the same operand order and insertion point as the physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode

def rowCut (width row : ℕ) (g : QMAGate) : ℕ :=
  let i := sweepIndex width row (gateLeft g%(width+1))
  let j := sweepIndex width row (gateRight g%(width+1))
  if gateTag g=2 then max i j+1 else i+1

def mapToRow (width row : ℕ) : QMAGate → QMAGate
  | .hadamard i => .hadamard (rowAddress width row i)
  | .phaseT i => .phaseT (rowAddress width row i)
  | .controlledNot i j => .controlledNot (rowAddress width row i) (rowAddress width row j)

theorem mapToRow_eq (rows width : ℕ) (row : Fin (rows+1)) (g : QMAGate) :
    qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width row) g=
      mapToRow width row.val g := by
  cases g <;> rfl

def transferList (ps : List (ℕ × ℕ)) : List QMAGate :=
  ps.flatMap (fun p => [.controlledNot p.1 p.2,.controlledNot p.2 p.1,.controlledNot p.1 p.2])

theorem transferList_eq {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1))) :
    qmaTransferGates ps=transferList (ps.map (fun p => (p.1.val,p.2.val))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [qmaTransferGates,List.map_cons,transferList,List.flatMap_cons,qmaWireSwapGates]
    rw [ih]
    rfl

def rowStage (rows width start : ℕ) (g : QMAGate) : List QMAGate :=
  let order := rows-1-start
  let ps := rowPairs width start order
  let cut := rowCut width order g
  transferList (ps.take cut)++[mapToRow width (start+1) g]++transferList (ps.drop cut)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal arithmetic and finite lists for the alternating row sweep. The
row width is supplied in unary exactly where a list is enumerated. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def tripleNatCode : TripleNat → List Bool := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

noncomputable def sweepIndexProgram : Procedure tripleNatCode Nat.bits
    (fun x => sweepIndex x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let row := (Procedure.first Nat.bits Nat.bits).comp rest
  let k := (Procedure.second Nat.bits Nat.bits).comp rest
  let parity := Procedure.binaryZero.comp (Procedure.binaryMod.comp
    (row.pair (Procedure.constant tripleNatCode Nat.bits 2)))
  exact (Procedure.conditional parity k (Procedure.binarySub.comp (w.pair k))).congrFun
    (by intro x; simp only [Function.comp_apply,sweepIndex,decide_eq_true_eq])

abbrev RowGate := ℕ × (ℕ × QMAGate)
def rowGateCode : RowGate → List Bool := prodCode Nat.bits (prodCode Nat.bits gateCode)

noncomputable def rowCutProgram : Procedure rowGateCode Nat.bits
    (fun x => rowCut x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let row := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let modulus := Procedure.successor.comp w
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  let i := sweepIndexProgram.comp (w.pair (row.pair left))
  let j := sweepIndexProgram.comp (w.pair (row.pair right))
  let maximum := Procedure.conditional (Procedure.binaryLe.comp (i.pair j)) j i
  let tag := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant rowGateCode Nat.bits 2))
  exact (Procedure.successor.comp (Procedure.conditional tag maximum i)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,rowCut]
    split <;> simp only [max_def])

def wirePairCode : (ℕ × ℕ) → List Bool := prodCode Nat.bits Nat.bits
def rowPairsInputCode : TripleNat → List Bool :=
  prodCode unaryCode (prodCode Nat.bits Nat.bits)

abbrev StageInput := ℕ × (ℕ × (ℕ × QMAGate))
def stageInputCode : StageInput → List Bool :=
  prodCode Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete sweep is a finite table of the literal row stages, followed
by concatenation. It agrees with the recursive physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def readGate (gs : List QMAGate) (i : ℕ) : QMAGate :=
  (gs.drop i).headD (.hadamard 0)

def sweepList (rows width start : ℕ) (gs : List QMAGate) : List QMAGate :=
  (List.range gs.length).flatMap (fun i => rowStage rows width (start+i) (readGate gs i))

theorem sweepList_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepList rows width start (g::gs)=
      rowStage rows width start g++sweepList rows width (start+1) gs := by
  simp only [sweepList,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,
    Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowStage rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowStage rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

noncomputable def gateLengthProgram : Procedure (listCode gateCode) unaryCode List.length :=
  Procedure.boundedUnary (Procedure.listLength gateCode (.hadamard 0))
    (Procedure.length.precompose (listCode gateCode)) (list_length_le_code gateCode)

abbrev SweepInput := ℕ × (ℕ × (ℕ × List QMAGate))
def sweepInputCode : SweepInput → List Bool :=
  prodCode Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

def rowColumns (width order : ℕ) (g : QMAGate) : List ℕ :=
  let xs := columns width order
  let cut := rowCut width order g
  repeatColumns (xs.take cut) ++ [sweepIndex width order (cut-1)] ++
    repeatColumns (xs.drop cut)

def rowCells (rows width start : ℕ) (g : QMAGate) : List (ℕ × ℕ) :=
  (rowColumns width (rows-1-start) g).map (fun j => (start,j))

def sweepCells (rows width start : ℕ) (gs : List QMAGate) : List (ℕ × ℕ) :=
  (List.range gs.length).flatMap (fun i =>
    rowCells rows width (start+i) (readGate gs i))

def value (c : QMACircuit) : List (ℕ × ℕ) :=
  sweepCells (qmaNearestCircuit c).gates.length c.work 0 (qmaNearestCircuit c).gates

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

def encodeCell {rows width : ℕ} (p : QMAGridCell rows width) : ℕ × ℕ :=
  (p.1.val,p.2.val)

def gateCell (c : QMACircuit) (t : ℕ) : ℕ × ℕ :=
  ((QuantumSweepCells.value c).drop t).headD (0,0)

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode Nat.bits (prodCode Procedure.boolCode (prodCode Nat.bits dataCode)))

def pointCode : PointInput → List Bool := prodCode inputCode Nat.bits

noncomputable opaque countProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque baseProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque flipProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _))
noncomputable opaque targetProgram : Procedure inputCode Nat.bits (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp
    ((Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _)))
noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp
    ((Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _)))

end ContinuumCoulomb.QuantumHistoryComparison

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact register evaluation of the propagation delta.  The equality scans
are bounded by the unary circuit size; every bit is read from the supplied
local support table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open QuantumAlgebraicScalar QuantumHistoryDescriptors QuantumHistoryBitProgram
open QuantumHistoryDiagonal QuantumHistorySiteProgram

def guard (c : QMACircuit) (t : ℕ) (d : Data) : Bool :=
  decide (clockRow c d t=1 ∧ clockRow c d (t+2)=0 ∧ clockRow c d (t+1)=0)

def flipped (c : QMACircuit) (t : ℕ) (d : Data) : Bool :=
  QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t+1),d)

def sameClock (c : QMACircuit) (d : Data) : Bool :=
  QuantumHistoryComparison.value (c.gates.length+2,referenceWork c+1,false,0,d)

def entry (c : QMACircuit) (t : ℕ) (d : Data) : Scalar :=
  if guard c t d then
    sub (rat (if flipped c t d then 1 else 0))
      (mul (rat (if sameClock c d then 1 else 0))
        (QuantumGateEntryProgram.entry
          (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)))
  else rat 0

def qubitEquiv (c : QMACircuit) :
    QMACircuitQubit c ≃ Fin (c.gates.length+2+(c.work+1)) := finSumFinEquiv

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDeltaProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial exact-arithmetic program for the propagation delta entry.
Only equality scans depend on circuit size; the matrix arity stays local. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumHistoryDiagonal QuantumCircuitCode QuantumHistoryDescriptors

noncomputable opaque clockCountProgram : Procedure inputCode unaryCode
    (fun x : Input => x.1.gates.length+2) :=
  Procedure.unaryAdd.comp
    ((QuantumHistoryDescriptors.timeProgram.comp circuitProgram).pair
      (Procedure.constant inputCode unaryCode 2))

noncomputable opaque allCountProgram : Procedure inputCode unaryCode
    (fun x : Input => x.1.gates.length+2+(x.1.work+1)) :=
  Procedure.unaryAdd.comp (clockCountProgram.pair
    (Procedure.unarySuccessor.comp (workProgram.comp circuitProgram)))

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

abbrev Input := QMACircuit × (ℕ × List ℕ)
def inputCode : Input → List Bool :=
  prodCode circuitCode (prodCode Nat.bits (listCode Nat.bits))

def data (n : ℕ) (s t : Fin n → Fin 2) (x : Input) : QuantumHistoryBitProgram.Data :=
  (x.2.2,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (t i).val))

def table (n : ℕ) (x : Input) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => QuantumHistoryDelta.entry x.1 x.2.1 (data n s t x)

noncomputable opaque entryInputProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode QuantumHistoryDiagonal.inputCode
      (fun x => (x.1,(4,x.2.1),data n s t x)) := by
  let c := Procedure.first circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let tail := Procedure.second circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let time := (Procedure.first Nat.bits (listCode Nat.bits)).comp tail
  let labels := (Procedure.second Nat.bits (listCode Nat.bits)).comp tail
  let a := (Procedure.constant inputCode Nat.bits 4).pair time
  let rows := Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun i => (s i).val))
  let columns := Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun i => (t i).val))
  exact c.pair (a.pair (labels.pair (rows.pair columns)))

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

abbrev Input := QuantumPropagationTable.Input
abbrev inputCode := QuantumPropagationTable.inputCode

def coefficient (c : QMACircuit) : ℚ := (14*(c.work+1)+8)*c.gates.length

def table (m : ℕ) (x : Input) : Matrix (Fin (m+1) → Fin 2) (Fin (m+1) → Fin 2) Scalar :=
  fun s t => oneReference (s 0) (t 0) (mul (rat (coefficient x.1))
    (matMul (adjoint (QuantumPropagationTable.table m x))
      (QuantumPropagationTable.table m x) (fun j => s j.succ) (fun j => t j.succ)))

def tableList : ℕ → Input → List Scalar
  | 0 => fun _ => matrixData (fun _ _ : Fin 0 → Fin 2 => rat 0)
  | m+1 => fun x => matrixData (table m x)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

def inputCode : Input → List Bool := prodCode Nat.bits (listCode Nat.bits)

noncomputable opaque dataProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode dataCode (data n s t) :=
  (Procedure.second Nat.bits (listCode Nat.bits)).pair
    ((Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun j => (s j).val))).pair
      (Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun j => (t j).val))))

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

abbrev Input := QMACircuit × (ℕ × List ℕ)
def inputCode : Input → List Bool :=
  prodCode circuitCode (prodCode Nat.bits (listCode Nat.bits))

def localTable (n : ℕ) (x : Input) : List Scalar :=
  if x.2.1 < referenceWork x.1+1 then
    let a := orderedAt x.1 x.2.1
    if a.1<4 then QuantumHistoryDiagonal.tableList n (x.1,a,x.2.2)
    else QuantumPropagationSampler.tableList n (x.1,a.2,x.2.2.tail)
  else matrixData (QuantumReferenceEdgeTable.table n
    (x.2.1-(referenceWork x.1+1),x.2.2))

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque restProgram : Procedure inputCode
    (prodCode Nat.bits (listCode Nat.bits)) Prod.snd := Procedure.second _ _
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp restProgram
noncomputable opaque labelsProgram : Procedure inputCode (listCode Nat.bits) (fun x => x.2.2) :=
  (Procedure.second _ _).comp restProgram

def table (x : Input) : List Scalar :=
  if x.2.2.length=0 then localTable 0 x else
  if x.2.2.length=1 then localTable 1 x else
  if x.2.2.length=2 then localTable 2 x else
  if x.2.2.length=3 then localTable 3 x else
  if x.2.2.length=4 then localTable 4 x else
  if x.2.2.length=5 then localTable 5 x else localTable 6 x

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

abbrev Input := ℕ × QMACircuit
def inputCode : Input → List Bool := prodCode unaryCode circuitCode

def packet (x : Input) (i : ℕ) : List QuantumOrderedLabelFamily.Entry :=
  let labels := supportLabels x.2 i
  QuantumPaddedLabelProgram.uniformPacket
    (x.1,labels,QuantumHistoryTableProgram.table (x.2,i,labels))

def entries (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  (List.ofFn (fun i : Fin (QuantumOrderedSourceIndex.referenceCount x.2) => packet x i.val)).flatten

attribute [local instance] OAI.ContinuumCoulomb.QuantumHistorySamplerProgram.finDecision
noncomputable opaque countProgram : Procedure circuitCode unaryCode
    QuantumOrderedSourceIndex.referenceCount := by
  let t := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 4).pair timeProgram)
  let w := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 2).pair workProgram)
  exact (Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (t.pair w)).pair
      (Procedure.constant circuitCode unaryCode 9))).congrFun (by
        intro c
        simpa only [Function.comp_apply] using (QuantumOrderedSourceIndex.referenceCount_eq c).symm)

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

abbrev Input := ℕ × QMACircuit
abbrev inputCode := QuantumHistorySamplerProgram.inputCode

noncomputable opaque coefficientBudgetProgram : Procedure circuitCode unaryCode coefficientBudget := by
  let const (n : ℕ) := Procedure.constant circuitCode unaryCode n
  let inner := Procedure.unaryMul.comp
    ((Procedure.unaryAdd.comp
      ((Procedure.unaryMul.comp ((const 14).pair
        (Procedure.unarySuccessor.comp workProgram))).pair (const 8))).pair
      QuantumHistoryDescriptors.timeProgram)
  exact Procedure.unaryMul.comp ((const 128).pair
    (Procedure.unaryAdd.comp ((const 14).pair
      (Procedure.unaryMul.comp ((const 288).pair inner)))))

noncomputable opaque termBudgetProgram : Procedure circuitCode unaryCode termBudget :=
  (Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 4096).pair
      QuantumHistorySamplerProgram.countProgram)).congrFun (by
        intro c
        simp only [termBudget,Function.comp_apply,QuantumOrderedSourceIndex.referenceCount_eq])

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.snd :=
  Procedure.second _ _
noncomputable opaque inverseErrorProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first _ _

noncomputable opaque termAllowanceProgram : Procedure inputCode unaryCode
    (fun x : Input => termBudget x.2+1) :=
  Procedure.unarySuccessor.comp (termBudgetProgram.comp circuitProgram)

noncomputable opaque coefficientAllowanceProgram : Procedure inputCode unaryCode
    (fun x : Input => coefficientBudget x.2+1) :=
  Procedure.unarySuccessor.comp (coefficientBudgetProgram.comp circuitProgram)

noncomputable opaque precisionFactorProgram : Procedure inputCode unaryCode
    (fun x : Input => (termBudget x.2+1)*(coefficientBudget x.2+1)) :=
  Procedure.unaryMul.comp (termAllowanceProgram.pair coefficientAllowanceProgram)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x : Input => samplePrecision x.2 x.1) :=
  (Procedure.unaryMul.comp (precisionFactorProgram.pair inverseErrorProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque sourceQubitsProgram : Procedure circuitCode unaryCode
    QuantumOrderedSourceIndex.qubitCount := by
  let const (n : ℕ) := Procedure.constant circuitCode unaryCode n
  let clocks := Procedure.unaryMul.comp ((const 3).pair QuantumHistoryDescriptors.timeProgram)
  let work := Procedure.unaryMul.comp ((const 2).pair workProgram)
  exact (Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (clocks.pair work)).pair (const 8))).congrFun (by
      intro c
      simpa only [Function.comp_apply] using (QuantumOrderedSourceIndex.qubitCount_eq c).symm)

def prepare (x : Input) : QuantumOrderedLabelFamily.Input :=
  (x.1,QuantumOrderedSourceIndex.qubitCount x.2,
    QuantumHistorySamplerProgram.entries (samplePrecision x.2 x.1,x.2))

def output (x : Input) : List MediatorListProgram.Bond × ℚ :=
  QuantumOrderedLabelCompile.output (prepare x)

def physicalQubits (x : Input) : ℕ := QuantumOrderedLabelCompile.qubitCount (prepare x)

theorem physicalQubits_eq (x : Input) :
    physicalQubits x=4*QuantumOrderedLabelCompile.outputCount (prepare x) := by
  simp only [physicalQubits,QuantumOrderedLabelCompile.qubitCount,
    QuantumOrderedLabelCompile.outputCount,Function.comp_apply]

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial program for the exact sweep tag list.  Only unary width
and the actual gate-list length control list generation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def pairCode : (ℕ × ℕ) → List Bool := prodCode Nat.bits Nat.bits

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial generation of the exact ordered history cell arrays.  All
list loops are bounded by unary circuit counts; coordinate arithmetic is
binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumOrderedCellProgram QuantumRouteCode

abbrev inputCode := QuantumHistoryDescriptors.referenceCode

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryFork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual history compiler produces a bounded loop-free exchange list.
Its initial subdivision and ordered fork rounds preserve the full-space
ground energy with the accumulated explicit error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph QuantumRawExchange
open scoped BigOperators Classical

namespace QuantumOrderedLabelCompile
open QuantumOrderedLabelTable

theorem output_valid {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (output (N,n,table e (index q) xs w J)).1) :
    b.1 < qubitCount (N,n,table e (index q) xs w J) ∧
      b.2.1 < qubitCount (N,n,table e (index q) xs w J) ∧ b.1 ≠ b.2.1 := by
  rw [output_table q e xs w J hlen hx N] at hb
  have hv := QuantumOrderedRawBlock.output_valid N
    (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
    (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
    (fun i => finalCoefficient J N (terms6 e i)) b hb
  have hn : qubitCount (N,n,table e (index q) xs w J)=finalCount n m*4 := by
    rw [qubitCount_table,finalCount_eq]
    omega
  simpa only [hn,finalCount] using hv

end QuantumOrderedLabelCompile

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawIncidence
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal four-spin exchange list preserves a uniform incidence bound.
All bonds are counted, including bonds with zero weight. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawIncidence
open QuantumForkList QuantumOrderedIncidence QuantumRawExchange MediatorListProgram
open scoped BigOperators Classical

theorem degree_le_length (bs : List Bond) (v : ℕ) : degree bs v ≤ bs.length := by
  induction bs with
  | nil => simp [degree]
  | cons b bs ih =>
    simp only [degree,List.map_cons,List.sum_cons,List.length_cons,incident] at ih ⊢
    split_ifs <;> omega

theorem degree_zero (bs : List Bond) (v : ℕ)
    (h : ∀ b ∈ bs, b.1 ≠ v ∧ b.2.1 ≠ v) : degree bs v = 0 := by
  unfold degree
  apply List.sum_eq_zero
  intro k hk
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hk
  simp [incident,(h b hb).1,(h b hb).2]

theorem degree_flatten (bss : List (List Bond)) (v : ℕ) :
    degree bss.flatten v = (bss.map (fun bs => degree bs v)).sum := by
  simp only [degree,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]

theorem field_origin (k i : ℕ) (a : Fin 2) (J : ℚ) (b : Bond)
    (hb : b ∈ field k i a J) (v : ℕ) (hv : b.1=v ∨ b.2.1=v) : v/4=i := by
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  rcases hv with hv | hv
  · change 4*i=v at hv
    omega
  · change 4*i+(qmaFieldEdgeRight e).val=v at hv
    rw [← hv]
    exact slot_div i _

theorem cross_origin (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ)
    (e : Bond) (he : e ∈ cross k r i j a b J) (v : ℕ)
    (hv : e.1=v ∨ e.2.1=v) : v/4=i ∨ v/4=j := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp he
  rcases hv with hv | hv
  · left
    change 4*i+((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm p).1.val=v at hv
    rw [← hv]
    exact slot_div i _
  · right
    change 4*j+((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm p).2.val=v at hv
    rw [← hv]
    exact slot_div j _

theorem packed_origin {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ)
    (b : Bond) (hb : b ∈ bonds ((k,r),pack t J)) (v : ℕ)
    (hv : b.1=v ∨ b.2.1=v) : ∃ i ∈ sites t, i.val=v/4 := by
  cases t with
  | scalar => simp [bonds,pack] at hb
  | field i a =>
    have hi := field_origin k i.val (axis (decide (a=0))) J b hb v hv
    exact ⟨i,by simp [sites],hi.symm⟩
  | pair i j hij a b' =>
    change b ∈ cross k r i.val j.val _ _ J ++ field k i.val _ _ ++ field k j.val _ _ at hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · rcases cross_origin k r i.val j.val _ _ J b hb v hv with hi | hj
      · exact ⟨i,by simp [sites],hi.symm⟩
      · exact ⟨j,by simp [sites],hj.symm⟩
    · exact ⟨i,by simp [sites],(field_origin _ _ _ _ b hb v hv).symm⟩
    · exact ⟨j,by simp [sites],(field_origin _ _ _ _ b hb v hv).symm⟩

theorem term_degree {n : ℕ} (k : ℕ) (r : ℚ) (xs : List (Fin n))
    (w : Fin n → Fin 4) (J : ℚ) (v : ℕ) (q : Fin n) (hq : q.val=v/4) :
    degree (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J)) v ≤
      22*(if q ∈ xs then 1 else 0) := by
  by_cases h : q ∈ xs
  · simpa only [h,ite_true, if_true,Nat.mul_one] using
      (degree_le_length _ v).trans (bonds_length _)
  · have hz : degree (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J)) v=0 := by
      apply degree_zero
      intro b hb
      have hn : ¬(b.1=v ∨ b.2.1=v) := by
        intro hv
        obtain ⟨i,hi,he⟩ := packed_origin k r _ J b hb v hv
        have hiq : i=q := Fin.ext (he.trans hq.symm)
        exact h (hiq ▸ ofSites_subset xs w i hi)
      exact not_or.mp hn
    simp only [h,ite_false, if_false,Nat.mul_zero,hz,le_refl]

theorem penalty_degree (n : ℕ) (r : ℚ) (v : ℕ) : degree (penalty n r) v ≤ 6 := by
  have hb (i : ℕ) : degree (penaltyBlock r i) v ≤ 6*(if v/4=i then 1 else 0) := by
    by_cases hi : v/4=i
    · simpa only [hi,ite_true, if_true,Nat.mul_one,penaltyBlock,List.length_ofFn] using
        degree_le_length (penaltyBlock r i) v
    · have hz : degree (penaltyBlock r i) v=0 := by
        apply degree_zero
        intro b hb
        obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
        have hl : 4*i+(qmaFourEdgeLeft e).val ≠ v := by
          intro he
          exact hi (by rw [← he]; exact slot_div i _)
        have hr : 4*i+(qmaFourEdgeRight e).val ≠ v := by
          intro he
          exact hi (by rw [← he]; exact slot_div i _)
        exact ⟨hl,hr⟩
      simp [hz,hi]
  unfold penalty
  rw [degree_flatten,List.map_map,range_sum]
  calc
    _ ≤ ∑ i : Fin n, 6*(if v/4=i.val then 1 else 0) :=
      Finset.sum_le_sum (fun i _ => hb i.val)
    _ = 6*∑ i : Fin n, if v/4=i.val then 1 else 0 := (Finset.mul_sum _ _ _).symm
    _ ≤ 6*1 := by
      apply Nat.mul_le_mul_left
      simpa only [eq_comm] using qmaCount_eq_le_one Fin.val Fin.val_injective (v/4)
    _ = 6 := by omega

theorem raw_degree {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ) {D : ℕ}
    (hx : Bounded xs D) (v : ℕ) (hv : v<n*4) :
    degree (QuantumOrderedRawBlock.output N xs w J).1 v ≤ 6+22*D := by
  let q : Fin n := ⟨v/4,by omega⟩
  let env : Environment :=
    (bits (n,N,packed (QuantumOrderedRawBlock.terms xs w) J),
      scale N (packed (QuantumOrderedRawBlock.terms xs w) J))
  change degree (penalty n env.2 ++ termBondsList (env,
    packed (QuantumOrderedRawBlock.terms xs w) J)) v ≤ _
  rw [degree_append]
  have hp := penalty_degree n env.2 v
  have ht : degree (termBondsList (env,packed (QuantumOrderedRawBlock.terms xs w) J)) v ≤
      22*D := by
    unfold termBondsList packed
    rw [degree_flatten,List.map_map,List.map_ofFn,List.sum_ofFn]
    calc
      _ ≤ ∑ e : Fin m, 22*(if q ∈ xs e then 1 else 0) := by
        apply Finset.sum_le_sum
        intro e _
        exact term_degree env.1 env.2 (xs e) (w e) (J e) v q rfl
      _ = 22*count xs q := by
        rw [count,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : q ∈ xs e <;> simp only [h,ite_true, if_true,ite_false, if_false]
      _ ≤ 22*D := Nat.mul_le_mul_left 22 (hx q)
  omega

end ContinuumCoulomb.QuantumRawIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed degree bound for the literal raw history output. Consequently a
constant number of literal fork rounds suffices. -/

noncomputable section
namespace ContinuumCoulomb
open QuantumOrderedIncidence QuantumRawIncidence QuantumOrderedLabelTable
open scoped Classical

namespace QuantumOrderedLabelCompile

theorem output_degree {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {n m D : ℕ}
    (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (hD : 1 ≤ D) (hinc : Bounded xs D) (N v : ℕ)
    (hv : v<qubitCount (N,n,table e (index q) xs w J)) :
    QuantumForkList.degree (output (N,n,table e (index q) xs w J)).1 v ≤
      6+22*(12544*D) := by
  rw [output_table q e xs w J hlen hdup N]
  have hb := numbered_bound (qubits6 q e) (terms6 e) (finalSites xs w)
    (complete_bound xs w hlen hD hinc)
  apply raw_degree N _ _ _ hb v
  rw [qubitCount_table] at hv
  change v<finalCount n m*4
  rw [finalCount_eq]
  omega

end QuantumOrderedLabelCompile

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCellLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual four-spin output list has a common neighboring coarse cell
for both endpoints of every bond, including all zero-weight terms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawCellLocality
open QuantumRawExchange QuantumRawIncidence QuantumForkList MediatorListProgram
open scoped Classical

def blockCell {rows width : ℕ} (cell : ℕ → QMAGridCell rows width) (v : ℕ) := cell (v/4)

theorem penalty_local {rows width : ℕ} (n : ℕ) (r : ℚ)
    (cell : ℕ → QMAGridCell rows width) :
    BondLocal (penalty n r) (blockCell cell) CommonCell := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  change CommonCell (cell ((4*i+(qmaFourEdgeLeft e).val)/4))
    (cell ((4*i+(qmaFourEdgeRight e).val)/4))
  rw [slot_div,slot_div]
  exact commonCell_refl _

theorem term_local {n rows width : ℕ} (k : ℕ) (r : ℚ) (xs : List (Fin n))
    (w : Fin n → Fin 4) (J : ℚ) (cell : ℕ → QMAGridCell rows width)
    (anchor : QMAGridCell rows width)
    (hx : ∀ i ∈ xs, QMAGridCellsNear (cell i.val) anchor) :
    BondLocal (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J))
      (blockCell cell) CommonCell := by
  intro b hb
  obtain ⟨i,hi,he⟩ := packed_origin k r _ J b hb b.1 (Or.inl rfl)
  obtain ⟨j,hj,hf⟩ := packed_origin k r _ J b hb b.2.1 (Or.inr rfl)
  refine ⟨anchor,?_,?_⟩
  · have h := hx i (ofSites_subset xs w i hi)
    simpa only [blockCell,he] using h
  · have h := hx j (ofSites_subset xs w j hj)
    simpa only [blockCell,hf] using h

theorem output_local {n m rows width : ℕ} (N : ℕ)
    (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (cell : ℕ → QMAGridCell rows width) (anchor : Fin m → QMAGridCell rows width)
    (hx : ∀ e i, i ∈ xs e → QMAGridCellsNear (cell i.val) (anchor e)) :
    BondLocal (QuantumOrderedRawBlock.output N xs w J).1 (blockCell cell) CommonCell := by
  let env : Environment :=
    (bits (n,N,packed (QuantumOrderedRawBlock.terms xs w) J),
      scale N (packed (QuantumOrderedRawBlock.terms xs w) J))
  change BondLocal (penalty n env.2 ++ termBondsList
    (env,packed (QuantumOrderedRawBlock.terms xs w) J)) (blockCell cell) CommonCell
  intro b hb
  rcases List.mem_append.mp hb with hp | ht
  · exact penalty_local n env.2 cell b hp
  · obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp ht
    obtain ⟨raw,hraw,rfl⟩ := List.mem_map.mp hbs
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hraw
    exact term_local env.1 env.2 (xs e) (w e) (J e) cell (anchor e) (hx e) b hb

end ContinuumCoulomb.QuantumRawCellLocality

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCellDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal four-spin vertex numbers have exactly four copies of each
logical cell. This connects the emitted numeric list to bounded cell density. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawCellLocality
open QuantumForkList
open scoped Classical

def extendCell {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (v : ℕ) : QMAGridCell rows width :=
  if h : v<n then cell ⟨v,h⟩ else (0,0)

theorem extendCell_fin {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (i : Fin n) : extendCell cell i.val=cell i := by
  simp only [extendCell,i.isLt,↓reduceDIte]

theorem blockCell_fin {n rows width : ℕ} (cell : Fin n → QMAGridCell rows width)
    (i : Fin (n*4)) : blockCell (extendCell cell) i.val=qmaFourBlockCell cell i := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (finProdFinEquiv : Fin n × Fin 4 ≃ Fin (n*4)).surjective i
  rw [qmaFourBlockCell,Equiv.symm_apply_apply]
  change extendCell cell ((b.val+4*q.val)/4)=cell q
  have hd : (b.val+4*q.val)/4=q.val := by have := b.isLt; omega
  rw [hd,extendCell_fin]

theorem blockCell_density {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (p : QMAGridCell rows width) :
    qmaCellMass (fun i : Fin (n*4) => blockCell (extendCell cell) i.val) p ≤ 4*A := by
  have he : (fun i : Fin (n*4) => blockCell (extendCell cell) i.val)=qmaFourBlockCell cell :=
    funext (blockCell_fin cell)
  rw [he]
  simpa only [qmaCellMass,Finset.card_filter] using qmaFourBlockCell_density cell hc p

end ContinuumCoulomb.QuantumRawCellLocality

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedOutputSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial input data for the actual six-stage and four-spin compiler,
using the exact numeric qubit order and full emitted bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedOutputSpatial
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete QuantumRawCellLocality
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n m rows width : ℕ}

local instance gridDecision (r w : ℕ) : DecidableEq (QMAGridCell r w) := Classical.decEq _

def logicalCell (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :
    Fin (finalCount n m) → QMAGridCell rows width :=
  fun i => cell6 cell anchor (qubits6 q e i)

def physicalCell (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :
    ℕ → QMAGridCell rows width := blockCell (QuantumRawCellLocality.extendCell (logicalCell q e cell anchor))

omit [DecidableEq ι] [DecidableEq κ] in
theorem logical_density (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    {A B : ℕ} (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun i => anchor i=p)).card ≤ B)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun i => logicalCell q e cell anchor i=p)).card ≤ A+3717*B := by
  have he : (Finset.univ.filter (fun i => logicalCell q e cell anchor i=p)).card =
      (Finset.univ.filter (fun i => cell6 cell anchor i=p)).card := by
    apply Finset.card_equiv (qubits6 q e)
    intro i
    constructor <;> intro h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
  rw [he]
  exact (complete_density (ι := ι) (κ := κ) (A := A) (B := B) cell anchor hc ha).1 p

theorem output_local (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (hx : ∀ a i, i ∈ xs a → QMAGridCellsNear (cell i) (anchor a)) (N : ℕ) :
    QuantumForkList.BondLocal
      (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).1
      (physicalCell q e cell anchor) QuantumForkList.CommonCell := by
  rw [QuantumOrderedLabelCompile.output_table q e xs w J hlen hdup N]
  apply QuantumRawCellLocality.output_local N _ _ _ _ (fun a => anchor6 anchor (terms6 e a))
  intro a i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  rw [extendCell_fin (logicalCell q e cell anchor) ((qubits6 q e).symm j)]
  change QMAGridCellsNear (cell6 cell anchor (qubits6 q e ((qubits6 q e).symm j))) _
  rw [Equiv.apply_symm_apply]
  exact complete_geometry xs w hlen cell anchor QMAGridCellsNear
    qmaGridCellsNear_refl hx (terms6 e a) j hj

def input (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    {A B D : ℕ} (hc : ∀ p, (Finset.univ.filter (fun i => cell i=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun i => anchor i=p)).card ≤ B)
    (hx : ∀ a i, i ∈ xs a → QMAGridCellsNear (cell i) (anchor a))
    (hD : 1 ≤ D) (hi : QuantumOrderedIncidence.Bounded xs D) (N : ℕ) :
    QuantumForkList.SpatialInput rows width (4*(A+3717*B)) (6+22*(12544*D)) where
  n := QuantumOrderedLabelCompile.qubitCount (N,n,table e (index q) xs w J)
  bonds := (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).1
  constant := (QuantumOrderedLabelCompile.output (N,n,table e (index q) xs w J)).2
  precision := N
  cell := physicalCell q e cell anchor
  bounded := fun b hb => ⟨(QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).1,
    (QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).2.1⟩
  noLoops := fun b hb => (QuantumOrderedLabelCompile.output_valid q e xs w J hlen hdup N b hb).2.2
  degree := fun v => QuantumOrderedLabelCompile.output_degree q e xs w J hlen hdup hD hi N v.val v.isLt
  density := by
    intro p
    have hn : QuantumOrderedLabelCompile.qubitCount (N,n,table e (index q) xs w J)=
        finalCount n m*4 := by
      rw [QuantumOrderedLabelCompile.qubitCount_table,finalCount_eq]
      omega
    rw [hn]
    apply blockCell_density (logicalCell q e cell anchor) ?_ p
    intro a
    convert logical_density q e cell anchor hc ha a using 1 <;> first | (with_reducible_and_instances rfl) | (congr)
  locality := output_local q e xs w J hlen hdup cell anchor hx N

end ContinuumCoulomb.QuantumOrderedOutputSpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

def historyCoefficientBudget (c : QMACircuit) (N : ℕ) : ℕ :=
  QuantumOrderedLabelCompile.coefficientEnvelope (qubitCount c) (termCount c)
    (QuantumAlgebraicHistory.coefficientBudget c) N

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

abbrev Input := QuantumHistoryPrecisionProgram.Input
abbrev inputCode := QuantumHistoryPrecisionProgram.inputCode

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev FinalInput := (ℚ × QuantumForkGridProgram.PreparedInput) × (ℚ × ℚ)

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical merging preserves exactly the unordered endpoint support.
This includes edges whose merged coefficient is zero. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumListMerge
open MediatorListProgram

theorem ordered_endpointPair (e : Bond) :
    s((ordered e).1,(ordered e).2) = s(e.1,e.2.1) := by
  rcases le_total e.1 e.2.1 with h | h
  · simp only [ordered,min_eq_left h,max_eq_right h]
  · simpa only [ordered,min_eq_right h,max_eq_left h] using
      (Sym2.eq_swap : s(e.2.1,e.1) = s(e.1,e.2.1))

theorem value_edge_source (n : ℕ) (xs : List Bond) {e : Bond}
    (he : e ∈ value n xs) :
    ∃ f ∈ xs, s(e.1,e.2.1) = s(f.1,f.2.1) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨f,hf,hfp⟩ := List.mem_map.mp hm
  refine ⟨f,hf,?_⟩
  rw [← hfp]
  exact ordered_endpointPair f

theorem value_edge_target {n : ℕ} {xs : List Bond}
    (hb : SourceBondLists.bounded n xs) {f : Bond} (hf : f ∈ xs) :
    ∃ e ∈ value n xs, s(e.1,e.2.1) = s(f.1,f.2.1) := by
  have hp : ordered f ∈ support n xs :=
    (mem_support hb _).mpr (List.mem_map.mpr ⟨f,hf,rfl⟩)
  refine ⟨((ordered f).1,(ordered f).2,weight xs (ordered f)),?_,ordered_endpointPair f⟩
  exact List.mem_map.mpr ⟨ordered f,hp,rfl⟩

end QuantumListMerge

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPolynomialUnary
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed natural polynomial has a literal unary evaluation program. The
polynomial is compiled by Horner recursion, using unary addition and multiplication. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolynomialUnary
open ExactQuantumFactoring.BitStackProgram

noncomputable def program (p : Polynomial ℕ) :
    Procedure unaryCode unaryCode p.eval := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact (Procedure.constant unaryCode unaryCode 0).congrFun (by intro n; simp)
  · intro q a _ _ hq
    exact (Procedure.unaryAdd.comp
      (hq.pair (Procedure.constant unaryCode unaryCode a))).congrFun (by
        intro n
        simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_C])
  · intro q _ hq
    exact (Procedure.unaryMul.comp (hq.pair (Procedure.identity unaryCode))).congrFun (by
      intro n
      simp only [Function.comp_apply,id_eq,Polynomial.eval_mul,Polynomial.eval_X])

end ContinuumCoulomb.QuantumPolynomialUnary

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the unary size bound while calling the given verifier generator.
The extra tapes hold only Boolean words; the original machine is embedded
without changing any of its instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

abbrev Alphabet (h : TM2ComputableInPolyTime ea eb f) : Tape h → Type :=
  MachineEmbedding.Alphabet h.tm.Γ (fun _ : Fin 3 => Bool)

def program (h : TM2ComputableInPolyTime ea eb f) :
    Label h → TM2.Stmt (Alphabet h) (Label h) (State h)
  | .inl l => MachineEmbedding.statement (some (.inr 3)) (h.tm.m l)
  | .inr i =>
    if i=0 then
      .pop (.inr 0) (fun s b => (s.1,b))
        (.branch (fun s => s.2.getD false)
          (.pop (.inr 0) (fun s _ => s)
            (.push (.inr 1) (fun _ => true) (.goto fun _ => .inr 0)))
          (.load (fun s => (s.1,none)) (.goto fun _ => .inr 1)))
    else if i=1 then
      QuantumBitTransfer.loop (.inr 0) (.inr 2) id id (.inr 1) (some (.inr 2))
    else if i=2 then
      QuantumBitTransfer.loop (.inr 2) (.inl h.tm.k₀) id h.inputAlphabet.invFun
        (.inr 2) (some (.inl h.tm.main))
    else if i=3 then
      QuantumBitTransfer.loop (.inl h.tm.k₁) (.inr 2) h.outputAlphabet id
        (.inr 3) (some (.inr 4))
    else if i=4 then
      QuantumBitTransfer.loop (.inr 2) (.inr 0) id id (.inr 4) (some (.inr 5))
    else if i=5 then
      .push (.inr 0) (fun _ => false)
        (.load (fun s => (s.1,none)) (.goto fun _ => .inr 6))
    else
      .pop (.inr 1) (fun s b => (s.1,b))
        (.branch (fun s => s.2.isSome)
          (.push (.inr 0) (fun _ => true)
            (.push (.inr 0) (fun _ => true) (.goto fun _ => .inr 6)))
          (.load (fun _ => (h.tm.initialState,none)) .halt))

def machine (h : TM2ComputableInPolyTime ea eb f) : FinTM2 where
  K := Tape h
  kFin := by letI := h.tm.kFin; exact inferInstance
  k₀ := .inr 0
  k₁ := .inr 0
  Γ := Alphabet h
  Λ := Label h
  ΛFin := by letI := h.tm.ΛFin; exact inferInstance
  main := .inr 0
  σ := State h
  σFin := by letI := h.tm.σFin; exact inferInstance
  initialState := (h.tm.initialState,none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program h

def tapes (h : TM2ComputableInPolyTime ea eb f) (source : ∀ k, List (h.tm.Γ k))
    (input saved temp : List Bool) : ∀ k, List (Alphabet h k) :=
  MachineEmbedding.tapes source (extraTapes input saved temp)

def configuration (h : TM2ComputableInPolyTime ea eb f) (label : Option (Label h))
    (state : h.tm.σ) (r : Option Bool) (source : ∀ k, List (h.tm.Γ k))
    (input saved temp : List Bool) : (machine h).Cfg :=
  ⟨label,(state,r),tapes h source input saved temp⟩

def next (h : TM2ComputableInPolyTime ea eb f) (c : Option (machine h).Cfg) :=
  c.bind (machine h).step

theorem embedded_program (h : TM2ComputableInPolyTime ea eb f) :
    program h = MachineEmbedding.program (some (.inr 3)) h.tm.m
      (fun i => program h (.inr i)) := by
  funext l
  cases l <;> rfl

def source_execution (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    StateTransition.EvalsToInTime (machine h).step
      (MachineEmbedding.configuration (some (.inr 3)) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (initList h.tm ((ea x).map h.inputAlphabet.invFun)))
      (some (MachineEmbedding.configuration (some (.inr 3)) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (haltList h.tm ((eb (f x)).map h.outputAlphabet.invFun))))
      (h.time.eval (ea x).length) := by
  have hh := MachineComposition.embeddedExecution (some (Sum.inr (3 : Fin 7)))
    (none : Option Bool) (extraTapes [] (unaryCode b) []) h.tm.m
    (fun i => program h (.inr i)) (h.outputsFun x)
  rw [← embedded_program h] at hh
  exact hh

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefixRun
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prefix parsing and emission for the verifier wrapper. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

@[simp] theorem next_some (h : TM2ComputableInPolyTime ea eb f) (c : (machine h).Cfg) :
    next h (some c)=(machine h).step c := rfl

@[simp] theorem tapes_input (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 0)=xs := rfl

@[simp] theorem tapes_saved (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 1)=bs := rfl

@[simp] theorem tapes_temp (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) :
    tapes h s xs bs ts (.inr 2)=ts := rfl

@[simp] theorem tapes_source (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) (k : h.tm.K) :
    tapes h s xs bs ts (.inl k)=s k := rfl

@[simp] theorem update_input (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 0) ys=tapes h s ys bs ts := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

@[simp] theorem update_saved (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 1) ys=tapes h s xs ys ts := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

@[simp] theorem update_temp (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts ys : List Bool) :
    Function.update (tapes h s xs bs ts) (.inr 2) ys=tapes h s xs bs ys := by
  classical
  funext k
  cases k with
  | inl k => simp [tapes,MachineEmbedding.tapes]
  | inr k => fin_cases k <;> simp [tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_cons (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode (n+1)) xs) (unaryCode k) [])=
      some (configuration h (some (.inr 0)) h.tm.initialState (some true)
        (fun _ => []) (pairBits (unaryCode n) xs) (unaryCode (k+1)) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode,List.replicate_succ,quoteBits_cons]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_zero (h : TM2ComputableInPolyTime ea eb f) (k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode 0) xs) (unaryCode k) [])=
      some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode k) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem parse_steps (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (xs : List Bool) (r : Option Bool) :
    (next h)^[n+1] (some (configuration h (some (.inr 0)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode n) xs) (unaryCode k) []))=
      some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode (k+n)) []) := by
  induction n generalizing k r with
  | zero => simpa only [Nat.add_zero,Nat.zero_add,Function.iterate_one,next_some] using
      parse_zero h k xs r
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [next_some,parse_cons,ih]
    rw [show k+1+n = k+(n+1) by omega]

theorem emit_delimiter (h : TM2ComputableInPolyTime ea eb f) (n : ℕ)
    (ys : List Bool) :
    (machine h).step (configuration h (some (.inr 5)) h.tm.initialState none
      (fun _ => []) ys (unaryCode n) [])=
      some (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode n) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,pairBits,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_cons (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode (n+1)) [])=
      some (configuration h (some (.inr 6)) h.tm.initialState (some true)
        (fun _ => []) (pairBits (unaryCode (k+1)) ys) (unaryCode n) []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,
    pairBits,unaryCode,List.replicate_succ,quoteBits_cons]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_zero (h : TM2ComputableInPolyTime ea eb f) (k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (machine h).step (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode 0) [])=
      some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode k) ys) [] []) := by
  simp [FinTM2.step,TM2.step,machine,configuration,program,TM2.stepAux,unaryCode]
  congr 2
  funext j
  cases j with
  | inl j => simp [Function.update,tapes,MachineEmbedding.tapes]
  | inr j => fin_cases j <;> simp [Function.update,tapes,MachineEmbedding.tapes,extraTapes]

theorem emit_steps (h : TM2ComputableInPolyTime ea eb f) (n k : ℕ)
    (ys : List Bool) (r : Option Bool) :
    (next h)^[n+1] (some (configuration h (some (.inr 6)) h.tm.initialState r
      (fun _ => []) (pairBits (unaryCode k) ys) (unaryCode n) []))=
      some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode (k+n)) ys) [] []) := by
  induction n generalizing k r with
  | zero => simpa only [Nat.add_zero,Nat.zero_add,Function.iterate_one,next_some] using
      emit_zero h k ys r
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [next_some,emit_cons,ih]
    rw [show k+1+n = k+(n+1) by omega]

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefixTransfers
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four word transfers surrounding the original verifier computation.
The saved unary prefix is untouched throughout these phases. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity
open MinUncutGames.Reduction.MachineTransfer

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

@[simp] theorem update_source (h : TM2ComputableInPolyTime ea eb f)
    (s : ∀ k, List (h.tm.Γ k)) (xs bs ts : List Bool) (k : h.tm.K)
    (ys : List (h.tm.Γ k)) :
    Function.update (tapes h s xs bs ts) (.inl k) ys=
      tapes h (Function.update s k ys) xs bs ts := by
  classical
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=k
    · subst j; simp [tapes,MachineEmbedding.tapes,Function.update]
    · simp [tapes,MachineEmbedding.tapes,Function.update,hj]
  | inr j => simp [tapes,MachineEmbedding.tapes,Function.update]

def input_reverse (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode b) [])
      (some (configuration h (some (.inr 2)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) xs.reverse)) (xs.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (0 : Fin 3) : Tape h)
    (.inr 2) (by simp) id id (.inr 1) (some (.inr 2)) (program h) rfl
    (tapes h (fun _ => []) xs (unaryCode b) []) h.tm.initialState none
  simp only [tapes_input,tapes_temp,tapesAt,update_input,update_temp,
    Function.comp_def,id_eq,List.map_id',List.append_nil] at hr
  exact hr

def input_restore (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 2)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) xs.reverse)
      (some (MachineEmbedding.configuration (some (Sum.inr (3 : Fin 7))) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (initList h.tm (xs.map h.inputAlphabet.invFun)))) (xs.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (2 : Fin 3) : Tape h)
    (.inl h.tm.k₀) (by simp) id h.inputAlphabet.invFun (.inr 2) (some (.inl h.tm.main))
    (program h) rfl (tapes h (fun _ => []) [] (unaryCode b) xs.reverse) h.tm.initialState none
  simp only [tapes_temp,tapes_source,tapesAt,update_temp,update_source,
    Function.comp_def,id_eq,List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hs : Function.update (fun k => ([] : List (h.tm.Γ k))) h.tm.k₀
      (xs.map h.inputAlphabet.invFun) = (initList h.tm (xs.map h.inputAlphabet.invFun)).stk := by
    funext k
    by_cases hk : k=h.tm.k₀
    · subst k
      simp [initList]
    · simp [initList,Function.update,hk]
  rw [hs] at hr
  exact hr

def output_reverse (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (MachineEmbedding.configuration (some (Sum.inr (3 : Fin 7))) (none : Option Bool)
        (extraTapes [] (unaryCode b) [])
        (haltList h.tm (ys.map h.outputAlphabet.invFun)))
      (some (configuration h (some (.inr 4)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) ys.reverse)) (ys.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inl h.tm.k₁ : Tape h)
    (.inr 2) (by simp) h.outputAlphabet id (.inr 3) (some (.inr 4)) (program h) rfl
    (tapes h (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk [] (unaryCode b) [])
    h.tm.initialState none
  have hs : Function.update (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk h.tm.k₁ []=
      fun k => ([] : List (h.tm.Γ k)) := by
    funext k
    by_cases hk : k=h.tm.k₁
    · subst k
      simp
    · simp [haltList,Function.update,hk]
  have ht : (haltList h.tm (ys.map h.outputAlphabet.invFun)).stk h.tm.k₁ =
      ys.map h.outputAlphabet.invFun := by simp [haltList]
  simp only [tapes_source,tapes_temp,tapesAt,update_source,update_temp,ht,hs,
    List.length_map,Function.comp_def,id_eq,List.map_reverse,List.map_map,
    List.append_nil] at hr
  have he : (fun x => h.outputAlphabet (h.outputAlphabet.invFun x)) = id :=
    funext h.outputAlphabet.right_inv
  rw [he,List.map_id] at hr
  exact hr

def output_restore (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 4)) h.tm.initialState none
        (fun _ => []) [] (unaryCode b) ys.reverse)
      (some (configuration h (some (.inr 5)) h.tm.initialState none
        (fun _ => []) ys (unaryCode b) [])) (ys.length+1) := by
  have hr := QuantumBitTransfer.transfer (Sum.inr (2 : Fin 3) : Tape h)
    (.inr 0) (by simp) id id (.inr 4) (some (.inr 5)) (program h) rfl
    (tapes h (fun _ => []) [] (unaryCode b) ys.reverse) h.tm.initialState none
  simp only [tapes_input,tapes_temp,tapesAt,update_input,update_temp,
    Function.comp_def,id_eq,List.map_id',List.append_nil,List.length_reverse,
    List.reverse_reverse] at hr
  exact hr

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefixCertificate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial time for retaining a unary size certificate around an arbitrary
Boolean-input/Boolean-output TM2 computation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram
open MinUncutGames.Foundations.Complexity

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

theorem initial_eq (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    initList (machine h) (pairBits (unaryCode b) xs)=
      configuration h (some (.inr 0)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) xs) [] [] := by
  classical
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k => simp [machine,tapes,MachineEmbedding.tapes]
  | inr k =>
    fin_cases k
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
      rfl
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]

theorem final_eq (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    haltList (machine h) (pairBits (unaryCode b) ys)=
      configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) ys) [] [] := by
  classical
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k => simp [machine,tapes,MachineEmbedding.tapes]
  | inr k =>
    fin_cases k
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
      rfl
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]
    · simp [machine,tapes,MachineEmbedding.tapes,extraTapes]

def parse_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (xs : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 0)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) xs) [] [])
      (some (configuration h (some (.inr 1)) h.tm.initialState none
        (fun _ => []) xs (unaryCode b) [])) (b+1) where
  steps := b+1
  evals_in_steps := by
    change (next h)^[b+1] _=_
    simpa only [unaryCode,List.replicate_zero,Nat.zero_add] using parse_steps h b 0 xs none
  steps_le_m := le_rfl

def delimiter_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 5)) h.tm.initialState none
        (fun _ => []) ys (unaryCode b) [])
      (some (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode b) [])) 1 where
  steps := 1
  evals_in_steps := by
    change (next h)^[1] _=_
    simpa only [Function.iterate_one,next_some] using emit_delimiter h b ys
  steps_le_m := le_rfl

def emit_run (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (ys : List Bool) :
    StateTransition.EvalsToInTime (machine h).step
      (configuration h (some (.inr 6)) h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode 0) ys) (unaryCode b) [])
      (some (configuration h none h.tm.initialState none
        (fun _ => []) (pairBits (unaryCode b) ys) [] [])) (b+1) where
  steps := b+1
  evals_in_steps := by
    change (next h)^[b+1] _=_
    simpa only [unaryCode,List.replicate_zero,Nat.zero_add] using emit_steps h b 0 ys none
  steps_le_m := le_rfl

def execution (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    TM2OutputsInTime (machine h) (pairBits (unaryCode b) (ea x))
      (some (pairBits (unaryCode b) (eb (f x))))
      (h.time.eval (ea x).length+2*b+2*(ea x).length+2*(eb (f x)).length+7) := by
  let r₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (parse_run h b (ea x)) (input_reverse h b (ea x))
  let r₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁ (input_restore h b (ea x))
  let r₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₂ (source_execution h b x)
  let r₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₃ (output_reverse h b (eb (f x)))
  let r₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₄ (output_restore h b (eb (f x)))
  let r₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₅ (delimiter_run h b (eb (f x)))
  let r₇ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₆ (emit_run h b (eb (f x)))
  change StateTransition.EvalsToInTime (machine h).step
    (initList (machine h) (pairBits (unaryCode b) (ea x)))
    (some (haltList (machine h) (pairBits (unaryCode b) (eb (f x))))) _
  rw [initial_eq,final_eq]
  refine ⟨r₇.toEvalsTo,?_⟩
  have hr := r₇.steps_le_m
  exact hr.trans (by omega)

theorem execution_bound (h : TM2ComputableInPolyTime ea eb f) (b : ℕ) (x : α) :
    h.time.eval (ea x).length+2*b+2*(ea x).length+2*(eb (f x)).length+7 ≤
      (time h).eval (pairBits (unaryCode b) (ea x)).length := by
  have hl : (pairBits (unaryCode b) (ea x)).length=2*b+1+(ea x).length := by
    simp [pairBits,quoteBits_length,unaryCode]
  have hm := MachineComposition.natPolynomial_eval_mono h.time
    (show (ea x).length ≤ (pairBits (unaryCode b) (ea x)).length by omega)
  have ho := TM2Size.output_length h x
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  nlinarith

def computable (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime (prodCode unaryCode ea) (prodCode unaryCode eb)
      (fun x : ℕ × α => (x.1,f x.2)) where
  tm := machine h
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time h
  outputsFun x := by
    have hr := execution h x.1 x.2
    have run : TM2OutputsInTime (machine h)
        (pairBits (unaryCode x.1) (ea x.2))
        (some (pairBits (unaryCode x.1) (eb (f x.2))))
        ((time h).eval (pairBits (unaryCode x.1) (ea x.2)).length) :=
      ⟨hr.toEvalsTo,hr.steps_le_m.trans (execution_bound h x.1 x.2)⟩
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPreparedVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual verifier generator followed by the sparse-circuit compiler.
The unary size certificate is computed from the original input and retained
through the arbitrary given generator before its binary registers are parsed. -/

noncomputable section
namespace ContinuumCoulomb
open Turing ExactQuantumFactoring.BitStackProgram BinaryEncoding

namespace QuantumVerifier

noncomputable def prefixProgram (V : QuantumVerifier) :
    Procedure (id : BitString → List Bool) (prodCode unaryCode id)
      (fun x => (V.size.eval x.length,x)) :=
  ((QuantumPolynomialUnary.program V.size).comp Procedure.length).pair
    (Procedure.identity id)

end QuantumVerifier
end ContinuumCoulomb

end

end OAI
end



-- Prove2me | Definitions.Def_Q146C002
-- name    : Q146C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:04:05.987308+00:00
-- url     : https://prove2.me/theorems/6239d1ec-2b2b-46b0-87ef-08f9b1d721e6
-- title:
--   Definitions bundle Q146C002 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 965 declarations of OpenAI's Lean: 425 definitions, 9 inductive types or structures, 22 instances and 509 theorems. The definitions and types are `OAI.CircleDomainRigidity.BoundedBlockPattern`, `OAI.CircleDomainRigidity.BoundedDensityBudget`, `OAI.CircleDomainRigidity.ClosedFusionScheme`, `OAI.CircleDomainRigidity.ClosedFusionScheme.limit`, `OAI.CircleDomainRigidity.ClosedUpperHalfPlane`, `OAI.CircleDomainRigidity.ClosedUpperHalfPlane.translate`, `OAI.CircleDomainRigidity.CollarFragmentIndex`, `OAI.CircleDomainRigidity.CompactRegularPieceFlow`, `OAI.CircleDomainRigidity.CompactRegularPieceFlow.levelTrajectory`, `OAI.CircleDomainRigidity.CompactRegularPieceFlow.returnSubgroup`, `OAI.CircleDomainRigidity.ComponentImageSmall`, `OAI.CircleDomainRigidity.ComponentQuotient`, `OAI.CircleDomainRigidity.CountableSquareLawBounds`, `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.ExteriorOmittedAreaBound`, `OAI.CircleDomainRigidity.ExteriorOmittedAreaTheorem`, `OAI.CircleDomainRigidity.FiniteJordanConfiguration.cyclicSchedule`, `OAI.CircleDomainRigidity.FiniteJumpSystem`, `OAI.CircleDomainRigidity.FiniteJumpSystem.append`, `OAI.CircleDomainRigidity.FiniteJumpSystem.empty`, `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.FiniteTransfer.IsFilledCircleFamily`, `OAI.CircleDomainRigidity.FiniteTransfer.IsFilledCoordinateFamily`, `OAI.CircleDomainRigidity.FiniteTransfer.IsMaskedFilledCircleFamily`, `OAI.CircleDomainRigidity.FiniteTransfer.OrderedGraphGridCompatibility`, `OAI.CircleDomainRigidity.FiniteTransfer.PlanarMetric`, `OAI.CircleDomainRigidity.FiniteTransfer.SmoothCircleOn`, `OAI.CircleDomainRigidity.FiniteTransfer.UpperPairs`, `OAI.CircleDomainRigidity.FiniteTransfer.blendMetric`, `OAI.CircleDomainRigidity.FiniteTransfer.circleBranch`, `OAI.CircleDomainRigidity.FiniteTransfer.circleCut`, `OAI.CircleDomainRigidity.FiniteTransfer.circleCutoff`, `OAI.CircleDomainRigidity.FiniteTransfer.circleCutoffFamily`, `OAI.CircleDomainRigidity.FiniteTransfer.circleFDeriv`, `OAI.CircleDomainRigidity.FiniteTransfer.circleGradient`, `OAI.CircleDomainRigidity.FiniteTransfer.circlePathIncrement`, `OAI.CircleDomainRigidity.FiniteTransfer.circlePathPrefix`, `OAI.CircleDomainRigidity.FiniteTransfer.circleRepresentative`, `OAI.CircleDomainRigidity.FiniteTransfer.circleWedges`, `OAI.CircleDomainRigidity.FiniteTransfer.covectorDet` and 394 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CircleDomains_LengthArea`, `CircleDomains_Modulus_BandIncidence`, `CircleDomains_Modulus_BarrierJumpLosses`, `CircleDomains_Modulus_BarrierTrialMetric`, `CircleDomains_Modulus_ChainPotentialOscillation`, `CircleDomains_Modulus_CircleWedgeCost`, `CircleDomains_Modulus_ComponentBarriers`, `CircleDomains_Modulus_ConfigurationAtomicNorm`, `CircleDomains_Modulus_CostPerturbation`, `CircleDomains_Modulus_CostSummands`, `CircleDomains_Modulus_CountableImageIncidence`, `CircleDomains_Modulus_DiskLinePayment`, `CircleDomains_Modulus_FiniteBandNorm`, `CircleDomains_Modulus_FiniteWedgeCosts`, `CircleDomains_Modulus_FixedCapacityCutoffs`, `CircleDomains_Modulus_GridIncidence`, `CircleDomains_Modulus_HitNormTopology`, `CircleDomains_Modulus_HyperspaceIncidence`, `CircleDomains_Modulus_LaurentNormalization`, `CircleDomains_Modulus_LevelIncidence`, `CircleDomains_Modulus_LoopOscillationMinimum`, `CircleDomains_Modulus_MobiusNormalization`, `CircleDomains_Modulus_NormalFamilyInputs`, `CircleDomains_Modulus_NormalizedArgumentBasic`, `CircleDomains_Modulus_PathCostReference`, `CircleDomains_Modulus_PathIntervalOscillation`, `CircleDomains_Modulus_PriorityWeights`, `CircleDomains_Modulus_RealSequencePayment`, `CircleDomains_Modulus_RecursiveTestBudget`, `CircleDomains_Modulus_RegularCurveNormalStrip`, `CircleDomains_Modulus_RotatedLocalizedPayment`, `CircleDomains_Modulus_SmallMeanBudget`, `CircleDomains_Modulus_TerminalNormBudget`, `CircleDomains_Modulus_TupleIncidence`, `CircleDomains_Modulus_VerticalCirclePayment`, `CircleDomains_Modulus_WeightedCurveLength`, `CircleDomains_Modulus_WeightedScalarTests`, `CircleDomains_Probability_ArcNullImage`, `CircleDomains_Probability_BandMeasure`, `CircleDomains_Probability_BorelDensityBudget`, `CircleDomains_Probability_BorelFiberCounts`, `CircleDomains_Probability_ClosedFusionScheme`, `CircleDomains_Probability_CompactArcLaw`, `CircleDomains_Probability_CompactLawSplit`, `CircleDomains_Probability_CompactMeasureBarycenter`, `CircleDomains_Probability_CompactMeasureMajorantCost`, `CircleDomains_Probability_CompactMeasureMajorants`, `CircleDomains_Probability_CompactMeasureSeparation`, `CircleDomains_Probability_CompactPlanTestDensity`, `CircleDomains_Probability_ConfigurationMeasures`, `CircleDomains_Probability_ContinuousLawMeasurable`, `CircleDomains_Probability_CountableSquareLawBounds`, `CircleDomains_Probability_CountableVisitNorm`, `CircleDomains_Probability_DensityMassBound`, `CircleDomains_Probability_ExactBandMeasure`, `CircleDomains_Probability_FiniteChoiceLaw`, `CircleDomains_Probability_FiniteMeasureCoordinates`, `CircleDomains_Probability_FusionSmallSets`, `CircleDomains_Probability_FusionTrajectory`, `CircleDomains_Probability_IncreasingMeasureLimit`, `CircleDomains_Probability_LevelPaymentMeasure`, `CircleDomains_Probability_MeasurableArcIndex`, `CircleDomains_Probability_MeasurablePieceInverse`, `CircleDomains_Probability_NullLevelTuples`, `CircleDomains_Probability_ParametricNullTuples`, `CircleDomains_Probability_PathCostMeasure`, `CircleDomains_Probability_PathHitLaws`, `CircleDomains_Probability_PathLawMixtures`, `CircleDomains_Probability_PhysicalOccupationPushforward`, `CircleDomains_Probability_ProbabilityMixtureMap`, `CircleDomains_Probability_PublishedMeasureDuality`, `CircleDomains_Probability_PublishedProbabilityTopology`, `CircleDomains_Probability_RandomShifts`, `CircleDomains_Probability_RecursiveCodeLaw`, `CircleDomains_Probability_ScalarPairNull`, `CircleDomains_Probability_SupportedProbability`, `CircleDomains_Probability_TagTupleMeasure`, `CircleDomains_Reflection_AnalyticJordanParametrization`, `CircleDomains_Reflection_CayleyBoundaryOrder`, `CircleDomains_Reflection_HolomorphicCircleCoefficients`, `CircleDomains_Reflection_ReflectionCoefficientWords`, `CircleDomains_Reflection_ReflectionTileAction`, `CircleDomains_Reflection_ReflectionTiles`, `CircleDomains_Reflection_ReflectionWeightedL2`, `CircleDomains_Rigidity_AxialChordGeometry`, `CircleDomains_Rigidity_AxialLineIntegral`, `CircleDomains_Rigidity_BoundaryTrace`, `CircleDomains_Rigidity_CircleProjectionFlux`, `CircleDomains_Rigidity_ComponentTrace`, `CircleDomains_Rigidity_ConductivityAlgebra`, `CircleDomains_Rigidity_ConductivityCoefficient`, `CircleDomains_Rigidity_CountableAxialDiskTolls`, `CircleDomains_Rigidity_CountableTraceEnumeration`, `CircleDomains_Rigidity_ExteriorMaskReplacement`, `CircleDomains_Rigidity_FiniteTraceMask`, `CircleDomains_Rigidity_IntervalTraceExtension`, `CircleDomains_Rigidity_MaskTopology`, `CircleDomains_Rigidity_MaskedCircleFillings`, `CircleDomains_Rigidity_MaskedCircleMetric`, `CircleDomains_Rigidity_MaskedWedgeCost`, `CircleDomains_Rigidity_PrincipalOuterFlux`, `CircleDomains_Rigidity_PriorityPointTrace`, `CircleDomains_Rigidity_QuadrantFlux`, `CircleDomains_Rigidity_RealBeltramiCoefficientReduction`, `CircleDomains_Rigidity_SignedTraceTruncation`, `CircleDomains_Rigidity_SmoothTraceTruncation`, `CircleDomains_Rigidity_TraceBalloonPacking`, `CircleDomains_Rigidity_TraceBalloonRadii`, `CircleDomains_Rigidity_TraceBalloonSystem`, `CircleDomains_Rigidity_TraceCompression`, `CircleDomains_Rigidity_TraceLineTails`, `CircleDomains_Rigidity_TraceMaskPrimitive`, `CircleDomains_Rigidity_TraceTruncationLimits`, `CircleDomains_Selection_AnalyticWordBranch`, `CircleDomains_Selection_AnnularRadii`, `CircleDomains_Selection_AtomicHitTests`, `CircleDomains_Selection_BandGraph`, `CircleDomains_Selection_ChordTolls`, `CircleDomains_Selection_ContinuousRunningMaximum`, `CircleDomains_Selection_CrossingChords`, `CircleDomains_Selection_DelayedSelection`, `CircleDomains_Selection_DyadicTimes`, `CircleDomains_Selection_ExclusionTolls`, `CircleDomains_Selection_ExpectedWedges`, `CircleDomains_Selection_ExtendedAtomicToll`, `CircleDomains_Selection_FillRegionPotential`, `CircleDomains_Selection_FiniteChainPotential`, `CircleDomains_Selection_FiniteConvexSplit`, `CircleDomains_Selection_FiniteGapGeometry`, `CircleDomains_Selection_FiniteGapIntegration`, `CircleDomains_Selection_FiniteGateObstacles`, `CircleDomains_Selection_FiniteJumpSystems`, `CircleDomains_Selection_FiniteLineGaps`, `CircleDomains_Selection_FinitePatching`, `CircleDomains_Selection_FiniteTupleCompatibility`, `CircleDomains_Selection_FinitelySuslinian`, `CircleDomains_Selection_FirstUncountableRecursion`, `CircleDomains_Selection_FourSampleBound`, `CircleDomains_Selection_GateForbiddenSet`, `CircleDomains_Selection_GeometricIndexPeriod`, `CircleDomains_Selection_HitConfigurations`, `CircleDomains_Selection_JumpBlockCodes`, `CircleDomains_Selection_JumpBlockCountBound`, `CircleDomains_Selection_JumpTollLowerBound`, `CircleDomains_Selection_LiftedMeanBands`, `CircleDomains_Selection_LocalizedSmallPerturbation`, `CircleDomains_Selection_LusinInput`, `CircleDomains_Selection_MeanGeometricIndex`, `CircleDomains_Selection_OuterContours`, `CircleDomains_Selection_ParallelLineIntegration`, `CircleDomains_Selection_PrependNewBlockJump`, `CircleDomains_Selection_PrependOldBlockJump`, `CircleDomains_Selection_PrincipalExteriorGerm`, `CircleDomains_Selection_PrincipalInversionGerm`, `CircleDomains_Selection_PriorityFinite`, `CircleDomains_Selection_PriorityInterpolation`, `CircleDomains_Selection_ProtrusionProjection`, `CircleDomains_Selection_PuncturedHitProduct`, `CircleDomains_Selection_RankedSelectedLevels`, `CircleDomains_Selection_RankedTupleCompatibility`, `CircleDomains_Selection_RankedTuplePairs`, `CircleDomains_Selection_RayProjection`, `CircleDomains_Selection_RegularContours`, `CircleDomains_Selection_RegularLevelFlow`, `CircleDomains_Selection_RegularMapPieces`, `CircleDomains_Selection_RegularPieceFlow`, `CircleDomains_Selection_RegularPieceFlowOrbit`, `CircleDomains_Selection_RegularPieceLeastPeriod`, `CircleDomains_Selection_ScaledExteriorBounds`, `CircleDomains_Selection_ScaledGraphCover`, `CircleDomains_Selection_ShiftedStaircase`, `CircleDomains_Selection_ShrinkingJumpTolls`, `CircleDomains_Selection_SinglePieceBlock`, `CircleDomains_Selection_SortedCrossingChords`, `CircleDomains_Selection_Staircase`, `CircleDomains_Selection_SubfamilyOverride`, `CircleDomains_Selection_TagContainment`, `CircleDomains_Selection_TagLevelSingleton`, `CircleDomains_Selection_TerminalCounts`, `CircleDomains_Selection_TupleExclusions`, `CircleDomains_Selection_TuplePairCompatibility`, `CircleDomains_Selection_TupleReference`, `CircleDomains_Selection_TwoEndedFragmentGeometry`, `CircleDomains_Selection_TwoTerminalHitBound`, `CircleDomains_Selection_UpperPairs`, `CircleDomains_Selection_WedgeEstimate`, `CircleDomains_Sobolev_AdmissibleL2Convex`, `CircleDomains_Sobolev_ArgumentCircleIntegral`, `CircleDomains_Sobolev_AxisSwapEnergy`, `CircleDomains_Sobolev_BoundedLocalBranches`, `CircleDomains_Sobolev_BoundedUpperIntegral`, `CircleDomains_Sobolev_BoundedWeakIdentification`, `CircleDomains_Sobolev_BoundedWeakRange`, `CircleDomains_Sobolev_CircleDifferential`, `CircleDomains_Sobolev_CircleEnergy`, `CircleDomains_Sobolev_CircleEnergyChange`, `CircleDomains_Sobolev_ClippedDirectionalDerivative`, `CircleDomains_Sobolev_ClippedScalarEnergy`, `CircleDomains_Sobolev_CoareaInput`, `CircleDomains_Sobolev_ComplexCovectorEnergy`, `CircleDomains_Sobolev_ComplexCovectorWedge`, `CircleDomains_Sobolev_ComplexRealEnergy`, `CircleDomains_Sobolev_ComplexTangentFrame`, `CircleDomains_Sobolev_CoordinateEnergy`, `CircleDomains_Sobolev_CoordinateEstimates`, `CircleDomains_Sobolev_CoordinateSquares`, `CircleDomains_Sobolev_CovectorMetric`, `CircleDomains_Sobolev_CurveCoareaInput`, `CircleDomains_Sobolev_DustSmoothingTolerance`, `CircleDomains_Sobolev_EnergyChangeCoordinates`, `CircleDomains_Sobolev_EnergyTransportIntegrability`, `CircleDomains_Sobolev_ExteriorDerivativeMean`, `CircleDomains_Sobolev_ExteriorOmittedAreaInput`, `CircleDomains_Sobolev_FilledScalarL2`, `CircleDomains_Sobolev_FiniteEnergy`, `CircleDomains_Sobolev_FiniteSphericalArea`, `CircleDomains_Sobolev_GramMetric`, `CircleDomains_Sobolev_HilbertWeakSubsequence`, `CircleDomains_Sobolev_HolomorphicInjOnDerivative`, `CircleDomains_Sobolev_HolomorphicScalarEnergy`, `CircleDomains_Sobolev_InverseChartCoarea`, `CircleDomains_Sobolev_InversePieceJacobian`, `CircleDomains_Sobolev_L2WeakSubsequence`, `CircleDomains_Sobolev_LiftDifferentials`, `CircleDomains_Sobolev_LocalArgumentBranch`, `CircleDomains_Sobolev_LocalGradientMajorant`, `CircleDomains_Sobolev_MaximalTruncations`, `CircleDomains_Sobolev_MeasurableCircleGradient`, `CircleDomains_Sobolev_MetricChartEnergy`, `CircleDomains_Sobolev_MetricComposition`, `CircleDomains_Sobolev_MetricEnergy`, `CircleDomains_Sobolev_MetricInterpolation`, `CircleDomains_Sobolev_MetricTensor`, `CircleDomains_Sobolev_MollificationEnergy`, `CircleDomains_Sobolev_ParallelJumpIntegral`, `CircleDomains_Sobolev_PeriodizedLevels`, `CircleDomains_Sobolev_PlanarEnergyChange`, `CircleDomains_Sobolev_PlanarGradientDensity`, `CircleDomains_Sobolev_PlanarSliceIntegrals`, `CircleDomains_Sobolev_PositiveMollification`, `CircleDomains_Sobolev_PotentialRectangleACL`, `CircleDomains_Sobolev_PrincipalCircleArea`, `CircleDomains_Sobolev_PrincipalCircleAreaEstimate`, `CircleDomains_Sobolev_QuarterTurnEnergy`, `CircleDomains_Sobolev_RealCoordinateLines`, `CircleDomains_Sobolev_RescaledScalarBump`, `CircleDomains_Sobolev_ScalarFlattening`, `CircleDomains_Sobolev_ScalarFlatteningApproximation`, `CircleDomains_Sobolev_ScalarFlatteningEnergy`, `CircleDomains_Sobolev_ScalarLocalLp`, `CircleDomains_Sobolev_ScalarRegularCoordinates`, `CircleDomains_Sobolev_ScalarWeakLimits`, `CircleDomains_Sobolev_ScaledCutoffEnergy`, `CircleDomains_Sobolev_SmallEnergyCutoff`, `CircleDomains_Sobolev_SmoothCircleOscillation`, `CircleDomains_Sobolev_SmoothContours`, `CircleDomains_Sobolev_SmoothImageArea`, `CircleDomains_Sobolev_SmoothLocalWeakDerivative`, `CircleDomains_Sobolev_SmoothRadialShrink`, `CircleDomains_Sobolev_SourceArea`, `CircleDomains_Sobolev_SphereChartDerivativeDecay`, `CircleDomains_Sobolev_SphereChartLipschitz`, `CircleDomains_Sobolev_SphereRealDifferential`, `CircleDomains_Sobolev_SphericalAreaLocalization`, `CircleDomains_Sobolev_SphericalGradientEnergyNorm`, `CircleDomains_Sobolev_SupportedMetric`, `CircleDomains_Sobolev_TargetArea`, `CircleDomains_Sobolev_TensorEnergy`, `CircleDomains_Sobolev_ThreeL2WeakLimits`, `CircleDomains_Sobolev_VerticalFilledDerivative`, `CircleDomains_Sobolev_WeakPairEnergy`, `CircleDomains_Topology_AnnularCutoffs`, `CircleDomains_Topology_BallPairKernel`, `CircleDomains_Topology_BoundaryClosingArc`, `CircleDomains_Topology_BoundaryIndexMean`, `CircleDomains_Topology_CenteredBoundary`, `CircleDomains_Topology_CenteredSmallCutoffs`, `CircleDomains_Topology_CircleChainRule`, `CircleDomains_Topology_CircleCovectors`, `CircleDomains_Topology_CircleFillings`, `CircleDomains_Topology_CircleIncrementContinuity`, `CircleDomains_Topology_CircleIntervalTraversal`, `CircleDomains_Topology_CircleLifts`, `CircleDomains_Topology_CirclePathPrefixes`, `CircleDomains_Topology_CircleProjectionEndpoints`, `CircleDomains_Topology_CircleQuantileArcs`, `CircleDomains_Topology_CompactChartConjugation`, `CircleDomains_Topology_CompactDiskRayBounds`, `CircleDomains_Topology_CompactLevelTangent`, `CircleDomains_Topology_CompactLoopPathFamily`, `CircleDomains_Topology_CompactTransverseField`, `CircleDomains_Topology_CompactVectorFieldFlow`, `CircleDomains_Topology_ComponentControl`, `CircleDomains_Topology_ComponentQuotientModel`, `CircleDomains_Topology_CountableBallSynthesis`, `CircleDomains_Topology_CutoffStaircase`, `CircleDomains_Topology_DisjointCutoffAverages`, `CircleDomains_Topology_DiskCrossingInput`, `CircleDomains_Topology_DiskFractionalMap`, `CircleDomains_Topology_DyadicPathApproximation`, `CircleDomains_Topology_DyadicPathReplacement`, `CircleDomains_Topology_ExteriorCoefficientCircle`, `CircleDomains_Topology_FiniteBallSynthesis`, `CircleDomains_Topology_FiniteCircleGreen`, `CircleDomains_Topology_FiniteCircleStokes`, `CircleDomains_Topology_FiniteIntervalSplitting`, `CircleDomains_Topology_GreedyOpenSelection`, `CircleDomains_Topology_HalfPlaneDisk`, `CircleDomains_Topology_HalfPlaneDiskInverse`, `CircleDomains_Topology_HolomorphicPlaneChart`, `CircleDomains_Topology_InactiveCollars`, `CircleDomains_Topology_InterleavedCollarPieces`, `CircleDomains_Topology_JordanDiskImages`, `CircleDomains_Topology_JordanExteriors`, `CircleDomains_Topology_JordanFillLimits`, `CircleDomains_Topology_JordanIntersectionConnectivity`, `CircleDomains_Topology_LevelQuotient`, `CircleDomains_Topology_LooplessSeparatingCoordinate`, `CircleDomains_Topology_LooplessTimeCoordinate`, `CircleDomains_Topology_MarkedDiskLimits`, `CircleDomains_Topology_MontelCutoffExhaustion`, `CircleDomains_Topology_MontelCutoffFamily`, `CircleDomains_Topology_MooreReduction`, `CircleDomains_Topology_NextComponentShrink`, `CircleDomains_Topology_OrderedPhysicalCollar`, `CircleDomains_Topology_ParallelDiskTolls`, `CircleDomains_Topology_PathLoopErasure`, `CircleDomains_Topology_PeriodicBoundaryPairing`, `CircleDomains_Topology_PeriodicCircleDescent`, `CircleDomains_Topology_PlanarAxisSwap`, `CircleDomains_Topology_PlanarFormPullback`, `CircleDomains_Topology_PlanarMapChangeVariables`, `CircleDomains_Topology_PlanarMaximalInput`, `CircleDomains_Topology_PrincipalCircleRemainder`, `CircleDomains_Topology_QuotientTopology`, `CircleDomains_Topology_RadialDiskCompression`, `CircleDomains_Topology_RangePreservingCutoff`, `CircleDomains_Topology_RecursiveComponentShrink`, `CircleDomains_Topology_RegularPieceOpenOrbit`, `CircleDomains_Topology_RescaledPlaneBump`, `CircleDomains_Topology_RoundBoundaryStability`, `CircleDomains_Topology_RoundCircleParametrization`, `CircleDomains_Topology_RoundDiskCoordinates`, `CircleDomains_Topology_RoundDiskSlices`, `CircleDomains_Topology_SimpleArcToll`, `CircleDomains_Topology_SimpleLoopCircle`, `CircleDomains_Topology_SmallPerturbationHomeomorph`, `CircleDomains_Topology_SmallPerturbationJordan`, `CircleDomains_Topology_SmallPhysicalDisks`, `CircleDomains_Topology_SphereNeighborhoods`, `CircleDomains_Topology_TransportedCircleCoordinates`, `CircleDomains_Topology_VerticalFrontierCrossings`, `CircleDomains_Topology_VerticalLevelCurve`, `CircleDomains_Transfer_BoundedScalarFillings`, `CircleDomains_Transfer_CofiniteTransfer`, `CircleDomains_Transfer_CoreGeometry`, `CircleDomains_Transfer_FilledCoordinates`, `CircleDomains_Transfer_FilledGapIntegration`, `CircleDomains_Transfer_FiniteChartConnectivity`, `CircleDomains_Transfer_GraphGridCells`, `CircleDomains_Transfer_GraphGridCompatibility`, `CircleDomains_Transfer_GridCollisions`, `CircleDomains_Transfer_LogarithmicCutCharts`, `CircleDomains_Transfer_PeriodicFilling`, `CircleDomains_Transfer_RadialShrinkImages`, `CircleDomains_Transfer_RankOneFilling`, `CircleDomains_Transfer_ReciprocalGridSelection`, `CircleDomains_Transfer_RetainedScalarEstimates`, `CircleDomains_Transfer_RoundOuterCore`, `CircleDomains_Transfer_ShrinkingRealModels`, `CircleDomains_Transfer_SourceAnchor`, `CircleDomains_Transfer_TransportedRealCoordinates`, `CircleDomains_Uniformization_BandLimits`, `CircleDomains_Uniformization_ComplexRectangleLimit`, `CircleDomains_Uniformization_ConformalMetric`, `CircleDomains_Uniformization_CyclicCircularization`, `CircleDomains_Uniformization_ExteriorCoefficientBounds`, `CircleDomains_Uniformization_FiniteCoefficientRadial`, `CircleDomains_Uniformization_HurwitzUnivalentProof`, `CircleDomains_Uniformization_HurwitzZeroFreeProof`, `CircleDomains_Uniformization_LimitConformality`, `CircleDomains_Uniformization_MetricBeltramiCoefficient`, `CircleDomains_Uniformization_MontelAscoli`, `CircleDomains_Uniformization_MontelEquicontinuity`, `CircleDomains_Uniformization_PrincipalCoefficientConvergence`, `CircleDomains_Uniformization_RiemannDiskImprovement`, `CircleDomains_Uniformization_RiemannDiskSeed`, `CircleDomains_Uniformization_RiemannRootCompetitor`, `CircleDomains_Uniformization_SquareAverageLimit`, `DiskMaximal_MaximalEstimates`, `FiniteTransfer`, `GeneratedStructure`, `InitialPair`, `LimitMap`, `Line`, `LocalGrid`, `ModelCurve`, `QuantitativeRecursion`, `SquareMesh`, `SquareMeshClosed`, `SquareMeshConnected`, `SquareMover`, `Windows`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundle `OAIQ046C000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C004` and `Q146C005`; the statement `OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data`; the proofs of `OAI.CircleDomainRigidity.PrincipalSmoothApproximation.exists_principal_limit_data` and `OAI.CircleDomainRigidity.exists_principal_smooth_approximation`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_OAIQ046C000

section
-- module Solutions.Q146_CD.Compat
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_LengthArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle domains, conformal removability, and conditional analytic rigidity from length and area estimates. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

theorem IsConformalOn.mono {f : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsConformalOn f U) (hVU : V ⊆ U) : IsConformalOn f V :=
  fun p hp ↦ hf p (hVU hp)

theorem isCircleDomain_univ : IsCircleDomain (univ : Set Sphere) := by
  refine ⟨isOpen_univ, isConnected_univ, ?_⟩
  intro p hp
  simp only [compl_univ, mem_empty_iff_false] at hp

end CircleDomainRigidity

open MeasureTheory Filter Bornology
open scoped Topology

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BandIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted dust incidence

This is the dust part of `eq:weighted-level-bound` in Section 1 of
`047-02`. A point contributes its weight on a measurable set of levels.
Tonelli converts the expected total incidence to the sum of weights
times level probabilities; the band-incidence estimate bounds these
probabilities, and square summability makes the result finite.
-/

open Set MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def weightedBandIncidence {T ι : Type*}
    (E : ι → Set T) (m : ι → ℝ) (t : T) : ℝ≥0∞ :=
  ∑' s, (E s).indicator (fun _ => ENNReal.ofReal (m s)) t

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierJumpLosses
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed summable loss schedule for the compatible-barrier chain distance.
Its retained lower bound stays strictly above one quarter at every stage. -/

noncomputable section

namespace CircleDomainRigidity

def barrierStageLower (n : ℕ) : ℝ := 7/16 + 1/16 * (1/2)^n

def barrierStageLoss (n : ℕ) : ℝ := 1/32 * (1/2)^n

@[simp] theorem barrierStageLower_zero : barrierStageLower 0 = 1/2 := by
  norm_num [barrierStageLower]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentControl
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognition of the limiting circle domain

Complementary-component coverage, collapse of unmarked components, and filling
of marked components together identify the limiting image as a circle domain.
-/

namespace CircleDomainRigidity

/-- An actual connected component of the closed complement. -/
def IsComplementaryComponent (G K : Set Sphere) : Prop :=
  ∃ p ∈ Gᶜ, K = connectedComponentIn Gᶜ p

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitelySuslinian
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite bounds on disjoint continua imply local connectedness

This is the topological implication (ii) to (iii) in the generic-level
continua lemma of `047-02`, Section 1. Components of a closed ball that
meet its half-radius ball have uniformly positive diameter by boundary
bumping. There are only finitely many of them, so the component through
the center is a neighborhood of that center.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity

/-- A uniform finite bound on the number of pairwise disjoint subcontinua
having any fixed positive minimum diameter. -/
def HasFiniteLargeContinuumBound (X : Type*) [MetricSpace X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : Finset (Set X),
    (∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ ε ≤ diam C) →
    (∀ C ∈ S, ∀ D ∈ S, C ≠ D → Disjoint C D) → S.card ≤ N

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LevelQuotient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting the quotient to a compact level union

The original quotient acts on the whole compact physical space. For a
compact level union `H`, restrict it to `π ⁻¹' H → H`. Connected fibers
remain connected, omitted points still map into compact totally
disconnected dust, and the induced-metric Hausdorff length is exactly
the physical length of `(π ⁻¹' H) ∩ G`.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

def levelQuotientMap {X Y : Type*} (π : Y → X) (H : Set X) : (π ⁻¹' H) → H :=
  fun y => ⟨π y.val, y.property⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MooreReduction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published Moore input and its application

Published input: R. L. Moore, *Concerning upper semi-continuous collections
of continua*, Trans. Amer. Math. Soc. 27 (1925), 416–428.
The proposition `MooreSphereDecomposition` is the closed-equivalence-relation
form of the sphere decomposition theorem needed in §2 of the Koebe manuscript.
It is an explicit hypothesis, not a global axiom.  The application below
verifies its hypotheses for complementary components and proves the dust
conclusion separately.
-/

open Set Topology

namespace CircleDomainRigidity

/-- The equivalence relation collapsing exactly the complementary components. -/
def componentSetoid (G : Set Sphere) : Setoid Sphere where
  r x y := x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | ⟨hx, hxy⟩
      · exact Or.inl h.symm
      · refine Or.inr ⟨connectedComponentIn_subset _ _ hxy, ?_⟩
        rw [← connectedComponentIn_eq hxy]
        exact mem_connectedComponentIn hx
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hxy⟩
      · exact hyz
      rcases hyz with rfl | ⟨_, hyz⟩
      · exact Or.inr ⟨hx, hxy⟩
      · refine Or.inr ⟨hx, ?_⟩
        rw [connectedComponentIn_eq hxy]
        exact hyz }

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientTopology
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the component quotient

The quotient is a homeomorphism on the original open domain and has
connected inverse images of continua. Together with `MooreReduction`,
this proves the topological quotient lemma of the Koebe manuscript,
conditional on the precisely stated published Moore input.
-/

open Set Topology

namespace CircleDomainRigidity

/-- All fibers of a component-collapse quotient are connected. -/
theorem connected_fibers_of_component_collapse
    {X Y : Type*} [TopologicalSpace X] (G : Set X) (π : X → Y)
    (hs : Function.Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    ∀ y, IsConnected (π ⁻¹' {y}) := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  by_cases hx : x ∈ G
  · have heq : π ⁻¹' {π x} = {x} := by
      ext z
      constructor
      · intro hz
        rcases (hr x z).mp (show π x = π z from hz.symm) with heq | ⟨hx', _⟩
        · exact heq.symm
        · exact (hx' hx).elim
      · rintro rfl
        rfl
    rw [heq]
    exact isConnected_singleton
  · have heq : π ⁻¹' {π x} = connectedComponentIn Gᶜ x := by
      ext z
      constructor
      · intro hz
        rcases (hr x z).mp (show π x = π z from hz.symm) with heq | ⟨_, hz'⟩
        · exact heq ▸ mem_connectedComponentIn hx
        · exact hz'
      · intro hz
        exact ((hr x z).mpr (Or.inr ⟨hx, hz⟩)).symm
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathHitLaws
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

section ClosedRelation

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [TopologicalSpace Ω] [TopologicalSpace X]
  [BorelSpace Ω] [BorelSpace X]
  [SecondCountableTopology Ω] [SecondCountableTopology X]
  [PseudoMetrizableSpace Ω] [PseudoMetrizableSpace X]

omit [PseudoMetrizableSpace Ω] [PseudoMetrizableSpace X] in
theorem product_dirac_closed_section {H : Set (Ω × X)} (hH : IsClosed H)
    (μ : ProbabilityMeasure Ω) (x : X) :
    ((μ.prod (diracProba x) : ProbabilityMeasure (Ω × X)) : Measure (Ω × X)) H =
      (μ : Measure Ω) {ω | (ω, x) ∈ H} := by
  rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_apply_symm hH.measurableSet]
  change (∫⁻ y, (μ : Measure Ω) ((fun ω => (ω, y)) ⁻¹' H) ∂Measure.dirac x) = _
  rw [lintegral_dirac' _ (measurable_measure_prodMk_right hH.measurableSet)]
  rfl

/-- Closed incidence has jointly upper semicontinuous hit probability in the weak law
and the tested point. No regularity of individual path lengths is involved. -/
theorem closed_section_probability_upperSemicontinuous {H : Set (Ω × X)}
    (hH : IsClosed H) :
    UpperSemicontinuous (fun p : ProbabilityMeasure Ω × X =>
      (p.1 : Measure Ω) {ω | (ω, p.2) ∈ H}) := by
  have hc : Continuous (fun p : ProbabilityMeasure Ω × X => p.1.prod (diracProba p.2)) :=
    ProbabilityMeasure.continuous_prod.comp
      (continuous_fst.prodMk (continuous_diracProba.comp continuous_snd))
  apply upperSemicontinuous_iff_limsup_le.mpr
  intro p
  simpa only [product_dirac_closed_section hH] using
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hc.continuousAt hH

end ClosedRelation

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLawMixtures
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def probabilityMixture (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω)
    (hlaw : Measurable law) : ProbabilityMeasure Ω :=
  ⟨(P : Measure Z).bind (fun z => (law z : Measure Ω)),
    isProbabilityMeasure_bind
      (measurable_subtype_coe.comp hlaw).aemeasurable
      (Eventually.of_forall fun _ => inferInstance)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HitNormTopology
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- For compact configurations, a joint upper semicontinuous strict bound persists
on an open set of centers. This is the neighborhood step of the finite split. -/
theorem isOpen_forall_compact_upper_bound {Z T : Type*}
    [TopologicalSpace Z] [TopologicalSpace T] [CompactSpace T]
    {f : Z × T → ℝ} (hf : UpperSemicontinuous f) (C : ℝ) :
    IsOpen {z | ∀ t, f (z, t) < C} := by
  have hc : IsClosed {p : Z × T | C ≤ f p} := hf.isClosed_preimage C
  have hp := isClosedMap_fst_of_compactSpace _ hc
  convert hp.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_compl_iff, mem_image, mem_ofPred_eq, Prod.exists, exists_and_right,
    exists_eq_right, not_exists, not_le]

theorem upperSemicontinuous_nonnegative_mul {Z : Type*} [TopologicalSpace Z]
    {f g : Z → ℝ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    UpperSemicontinuous (fun z => f z * g z) := by
  intro z c hc
  have hcont : Continuous (fun δ : ℝ => (f z + δ) * (g z + δ)) := by fun_prop
  have he : ∀ᶠ δ : ℝ in 𝓝 0, (f z + δ) * (g z + δ) < c := by
    exact hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hc))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hr2 : 0 < r / 2 := half_pos hr
  have hm : (f z + r / 2) * (g z + r / 2) < c :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr2] using half_lt_self hr)
  filter_upwards [hf z (f z + r / 2) (by linarith),
    hg z (g z + r / 2) (by linarith)] with y hyf hyg
  exact lt_of_le_of_lt
    (mul_le_mul hyf.le hyg.le (hg0 y) (by linarith [hf0 z])) hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_HitConfigurations
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact spaces of separated weighted point configurations, and the actual
uniform-neighborhood estimate for weighted hit probabilities over each such space. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev HitConfigurationAmbient (X : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Icc (0 : ℝ) 1)

def hitConfigurationSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    Set (HitConfigurationAmbient X n) :=
  {p | (∑ i, (p.2 i : ℝ) ^ 2) ≤ 1 ∧
    ∀ i j, i ≠ j → r ≤ dist (p.1 i) (p.1 j)}

theorem isClosed_hitConfigurationSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    IsClosed (hitConfigurationSet (X := X) n r) := by
  have h1 : IsClosed {p : HitConfigurationAmbient X n | (∑ i, (p.2 i : ℝ) ^ 2) ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {p : HitConfigurationAmbient X n |
      ∀ i j, i ≠ j → r ≤ dist (p.1 i) (p.1 j)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
  exact h1.inter h2

abbrev HitConfiguration (X : Type*) [MetricSpace X] (n : ℕ) (r : ℝ) :=
  hitConfigurationSet (X := X) n r

instance instCompactSpaceElemHitConfigurationAmbientHitConfiguration {X : Type*} [MetricSpace X] [CompactSpace X] (n : ℕ) (r : ℝ) :
    CompactSpace (HitConfiguration X n r) :=
  isCompact_iff_compactSpace.mp (isClosed_hitConfigurationSet n r).isCompact

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagContainment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed level-containment tests for the actual finite unions in tag slots. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def labeledLevelGraph (H : ℕ → Set (UnitAddCircle × X)) :
    Set (ℕ × (UnitAddCircle × X)) := {q | q.2 ∈ H q.1}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def LevelTuple := Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)

instance instTopologicalSpaceLevelTuple : TopologicalSpace LevelTuple :=
  inferInstanceAs (TopologicalSpace (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)))
instance instMeasurableSpaceLevelTuple : MeasurableSpace LevelTuple := borel LevelTuple
instance instBorelSpaceLevelTuple : BorelSpace LevelTuple := ⟨rfl⟩
instance instSecondCountableTopologyLevelTuple : SecondCountableTopology LevelTuple :=
  inferInstanceAs (SecondCountableTopology
    (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)))
instance instIsCompletelyMetrizableSpaceLevelTuple : IsCompletelyMetrizableSpace LevelTuple := by
  change IsCompletelyMetrizableSpace
    (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
instance instPolishSpaceLevelTuple : PolishSpace LevelTuple := by infer_instance

def slotWeight (k : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ k

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_IncreasingMeasureLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise increasing limits of the finite-stage occupation measures. -/

open Set MeasureTheory Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem tsum_iSup_of_monotone (f : ℕ → ℕ → ℝ≥0∞) (hf : Monotone f) :
    (∑' i, ⨆ n, f n i) = ⨆ n, ∑' i, f n i := by
  simpa only [lintegral_count] using
    (lintegral_iSup (μ := Measure.count) (fun _ => measurable_of_countable _) hf)

variable {Y : Type*} [MeasurableSpace Y]

theorem increasingMeasureLimit_iUnion (μ : ℕ → Measure Y) (hμ : Monotone μ)
    {f : ℕ → Set Y} (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    (⨆ n, μ n (⋃ i, f i)) = ∑' i, ⨆ n, μ n (f i) := by
  simp_rw [measure_iUnion hd hf]
  symm
  exact tsum_iSup_of_monotone (fun n i => μ n (f i)) (fun n m h i => hμ h (f i))

def increasingMeasureLimit (μ : ℕ → Measure Y) (hμ : Monotone μ) : Measure Y :=
  Measure.ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp)
    (fun _ hf hd => increasingMeasureLimit_iUnion μ hμ hf hd)

theorem increasingMeasureLimit_apply (μ : ℕ → Measure Y) (hμ : Monotone μ)
    {s : Set Y} (hs : MeasurableSet s) :
    increasingMeasureLimit μ hμ s = ⨆ n, μ n s :=
  Measure.ofMeasurable_apply s hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DyadicTimes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def dyadicEven (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val, by rw [pow_succ]; omega⟩

def dyadicOdd (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val + 1, by rw [pow_succ]; omega⟩

def dyadicChildrenEquiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)

theorem dyadicChildrenEquiv_zero (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicChildrenEquiv n (i, 0) = dyadicEven n i := by
  apply Fin.ext
  simp [dyadicChildrenEquiv, dyadicEven, finProdFinEquiv]

theorem dyadicChildrenEquiv_one (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicChildrenEquiv n (i, 1) = dyadicOdd n i := by
  apply Fin.ext
  simp [dyadicChildrenEquiv, dyadicOdd, finProdFinEquiv, Nat.add_comm]

theorem sum_dyadic_children {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Fin (2 ^ (n + 1)) → M) :
    ∑ j, f j = ∑ i, (f (dyadicEven n i) + f (dyadicOdd n i)) := by
  rw [← (dyadicChildrenEquiv n).sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, dyadicChildrenEquiv_zero, dyadicChildrenEquiv_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationPushforward
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation is the pushforward of domain-time arclength, with
parameter multiplicity retained. The value assigned at dust times is irrelevant. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalValue (e : G ≃ₜ U) (y₀ : Y) (x : X) : Y :=
  if h : x ∈ U then (e.symm ⟨x, h⟩).val else y₀

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathCostMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def PathCostSpace (Y D : Type*) := Y ⊕ (D ⊕ LevelTuple)

instance instTopologicalSpacePathCostSpace {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    TopologicalSpace (PathCostSpace Y D) := inferInstanceAs (TopologicalSpace (Y ⊕ (D ⊕ LevelTuple)))
instance instMeasurableSpacePathCostSpaceOfTopologicalSpace {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    MeasurableSpace (PathCostSpace Y D) := borel (PathCostSpace Y D)
instance instBorelSpacePathCostSpace {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    BorelSpace (PathCostSpace Y D) := ⟨rfl⟩
instance instPolishSpacePathCostSpace {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D]
    [PolishSpace Y] [PolishSpace D] : PolishSpace (PathCostSpace Y D) :=
  inferInstanceAs (PolishSpace (Y ⊕ (D ⊕ LevelTuple)))

def costPhysical {Y D : Type*} : Y → PathCostSpace Y D := Sum.inl

def costAtomic {Y D : Type*} : D → PathCostSpace Y D := Sum.inr ∘ Sum.inl

def costTuple {Y D : Type*} : LevelTuple → PathCostSpace Y D := Sum.inr ∘ Sum.inr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleExclusions
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Excluding precisely the infinite tuple values makes every individual
slot integral finite. The exclusions remain Borel for a Borel metric. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def tupleInfiniteExclusions (f : LevelTuple → ℝ≥0∞) (n : ℕ)
    (l : Fin (n + 1) → ℕ) : Set (Fin (n + 1) → UnitAddCircle) :=
  {t | f ⟨n, l, t⟩ = ∞}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleReference
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tuple reference measure is a positive weighted sum of Lebesgue
measures on the finite tuple tori, indexed by label type rather than slot. -/

open Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

abbrev TupleType := Σ n : ℕ, Fin (n + 1) → ℕ

def tupleFiber (i : TupleType) (t : Fin (i.1 + 1) → UnitAddCircle) : LevelTuple :=
  ⟨i.1, i.2, t⟩

def tupleReference (ω : TupleType → ℝ≥0∞) : Measure LevelTuple :=
  Measure.sum (fun i => ω i • (volume.map (tupleFiber i)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TupleIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence of a tuple with a fixed dust point. A free point whose
individual level sections are null has a null incident-tuple set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def tupleIncident (H : ℕ → Set (UnitAddCircle × X)) (x : X) : Set LevelTuple :=
  {q | ∃ j : Fin (q.1 + 1), (q.2.2 j, x) ∈ H (q.2.1 j)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathCostReference
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite reference measure for modulus: physical area, squared
countable-point weights, and the weighted tuple tori. Its square integral
is exactly the sum of the three corresponding energies. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

def atomicReference (c : D → ℝ≥0∞) : Measure D :=
  Measure.sum (fun s => (c s) ^ 2 • Measure.dirac s)

def pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞) (τ : Measure LevelTuple) :
    Measure (PathCostSpace Y D) :=
  μ.map costPhysical + (atomicReference c).map costAtomic + τ.map costTuple

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CostSummands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three disjoint cost summands can be recovered from the total
measure. In particular a total barycenter density gives the physical
occupation density on the original domain. -/

open Set MeasureTheory Topology
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

def sumCostMeasures (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple) :
    Measure (PathCostSpace Y D) :=
  μ.map costPhysical + a.map costAtomic + τ.map costTuple

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableVisitNorm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the terminal visit adds at most one to the counting square
norm. The estimate is independent of the auxiliary positive atomic weights. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def countingSquareNorm {D : Type*} (a : D → ℝ≥0∞) : ℝ≥0∞ :=
  (∑' s, a s ^ 2) ^ (1 / 2 : ℝ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CostPerturbation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive perturbations of the physical density and atomic tolls.
Their norm increase is controlled by the finite physical area and the
chosen square-summable countable weights. -/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

def squareIntegralNorm {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ y, f y ^ 2 ∂μ) ^ (1 / 2 : ℝ)

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

def perturbedPhysicalDensity (h : PathCostSpace Y D → ℝ≥0∞) (δ : ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  h (costPhysical y) + δ

def perturbedAtomicToll (h : PathCostSpace Y D → ℝ≥0∞) (c : D → ℝ≥0∞)
    (δ : ℝ≥0∞) (s : D) : ℝ≥0∞ := c s * h (costAtomic s) + δ * c s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BandGraph
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Compact interval-band graphs for bounded real coordinates

Take the closure of the physical graph and fill the interval between
cluster values in each fiber. This constructs a compact band graph;
on the open physical domain it is exactly the original graph. Its
projection modulo one consequently gives compact level sets with the
correct physical fibers.
-/

open Set

namespace CircleDomainRigidity

def clusterGraph {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) : Set (X × ℝ) :=
  closure ((fun x => (x, f x)) '' G)

def intervalFiberHull {X : Type*} (K : Set (X × ℝ)) : Set (X × ℝ) :=
  (fun p : (X × ℝ) × (X × ℝ) × ℝ =>
    (p.1.1, (1 - p.2.2) * p.1.2 + p.2.2 * p.2.1.2)) ''
      ((K ×ˢ (K ×ˢ Icc 0 1)) ∩ {p | p.1.1 = p.2.1.1})

theorem isCompact_clusterGraph {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M) :
    IsCompact (clusterGraph G f) := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-M) M))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ (isClosed_univ.prod isClosed_Icc)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨mem_univ x, abs_le.mp (hM x hx)⟩

theorem isCompact_intervalFiberHull {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) : IsCompact (intervalFiberHull K) := by
  apply ((hK.prod (hK.prod isCompact_Icc)).inter_right
    (isClosed_eq (continuous_fst.fst) (continuous_snd.fst.fst))).image
  exact continuous_fst.fst.prodMk
    (((continuous_const.sub continuous_snd.snd).mul continuous_fst.snd).add
      (continuous_snd.snd.mul continuous_snd.fst.snd))

theorem mem_intervalFiberHull_iff {X : Type*} {K : Set (X × ℝ)} {x : X} {t : ℝ} :
    (x, t) ∈ intervalFiberHull K ↔
      ∃ a b s : ℝ, (x, a) ∈ K ∧ (x, b) ∈ K ∧ s ∈ Icc 0 1 ∧
        t = (1 - s) * a + s * b := by
  constructor
  · rintro ⟨⟨⟨y, a⟩, ⟨z, b⟩, s⟩, ⟨⟨ha, hb, hs⟩, heq⟩, hout⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj hout
    change y = z at heq
    subst z
    exact ⟨a, b, s, ha, hb, hs, ht.symm⟩
  · rintro ⟨a, b, s, ha, hb, hs, rfl⟩
    exact ⟨((x, a), (x, b), s), ⟨⟨ha, hb, hs⟩, rfl⟩, rfl⟩

theorem subset_intervalFiberHull {X : Type*} (K : Set (X × ℝ)) :
    K ⊆ intervalFiberHull K := by
  rintro ⟨x, t⟩ ht
  apply mem_intervalFiberHull_iff.mpr
  exact ⟨t, t, 0, ht, ht, by norm_num, by ring⟩

theorem isCompact_real_fiber {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) (x : X) :
    IsCompact {t : ℝ | (x, t) ∈ K} := by
  have hc : IsCompact (Prod.snd '' (K ∩ {p | p.1 = x})) :=
    (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · intro ht
    exact ⟨(x, t), ⟨ht, rfl⟩, rfl⟩
  · rintro ⟨⟨y, a⟩, ⟨ha, heq⟩, rfl⟩
    change y = x at heq
    change (x, a) ∈ K
    simpa only [heq] using ha

/-- The interpolated fiber is exactly the interval between the smallest
and largest cluster values, with the endpoints attained in the compact
original fiber. -/
theorem intervalFiberHull_fiber_eq_Icc
    {X : Type*} [TopologicalSpace X] [T2Space X] {K : Set (X × ℝ)}
    (hK : IsCompact K) (x : X) (hne : {t : ℝ | (x, t) ∈ K}.Nonempty) :
    {t : ℝ | (x, t) ∈ intervalFiberHull K} =
      Icc (sInf {t : ℝ | (x, t) ∈ K}) (sSup {t : ℝ | (x, t) ∈ K}) := by
  let F : Set ℝ := {t | (x, t) ∈ K}
  have hlo := (isCompact_real_fiber hK x).isLeast_sInf hne
  have hhi := (isCompact_real_fiber hK x).isGreatest_sSup hne
  ext t
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, rfl⟩ := mem_intervalFiberHull_iff.mp ht
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hlo.2 ha)),
        mul_nonneg hs.1 (sub_nonneg.mpr (hlo.2 hb))]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hhi.2 ha)),
        mul_nonneg hs.1 (sub_nonneg.mpr (hhi.2 hb))]
  · intro ht
    apply mem_intervalFiberHull_iff.mpr
    by_cases heq : sInf F = sSup F
    · have htEq : t = sInf F := le_antisymm (ht.2.trans_eq heq.symm) ht.1
      refine ⟨sInf F, sSup F, 0, hlo.1, hhi.1, by norm_num, ?_⟩
      rw [htEq]
      ring
    · have hlt : sInf F < sSup F := lt_of_le_of_ne (hlo.2 hhi.1) heq
      have hd : 0 < sSup F - sInf F := sub_pos.mpr hlt
      refine ⟨sInf F, sSup F, (t - sInf F) / (sSup F - sInf F), hlo.1, hhi.1,
        ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le, (div_le_one hd).mpr (by linarith [ht.2])⟩, ?_⟩
      field_simp
      ring

theorem clusterGraph_fiber_nonempty_of_mem_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    {x : X} (hx : x ∈ closure G) : {t : ℝ | (x, t) ∈ clusterGraph G f}.Nonempty := by
  have hsub : closure G ⊆ Prod.fst '' clusterGraph G f := by
    apply closure_minimal _ ((isCompact_clusterGraph hM).image continuous_fst).isClosed
    intro y hy
    exact ⟨(y, f y), subset_closure ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨⟨y, t⟩, ht, heq⟩ := hsub hx
  change y = x at heq
  exact ⟨t, heq ▸ ht⟩

theorem clusterGraph_fiber_eq_of_continuousAt
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : ℝ} (ht : (x, t) ∈ clusterGraph G f) : t = f x := by
  have hc : ContinuousAt (fun p : X × ℝ => p.2 - f p.1) (x, t) :=
    continuousAt_snd.sub (hf.comp continuousAt_fst)
  have hz : t - f x ∈ closure ({0} : Set ℝ) := hc.continuousWithinAt.mem_closure ht (by
    rintro _ ⟨y, hy, rfl⟩
    simp)
  simpa only [closure_singleton, mem_singleton_iff, sub_eq_zero] using hz

theorem intervalFiberHull_clusterGraph_on_open
    {X : Type*} [TopologicalSpace X] {G : Set X} (hG : IsOpen G) {f : X → ℝ}
    (hf : ContinuousOn f G) {x : X} (hx : x ∈ G) {t : ℝ} :
    (x, t) ∈ intervalFiberHull (clusterGraph G f) ↔ t = f x := by
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, _, ht⟩ := mem_intervalFiberHull_iff.mp ht
    have hfx := hf.continuousAt (hG.mem_nhds hx)
    rw [clusterGraph_fiber_eq_of_continuousAt hfx ha,
      clusterGraph_fiber_eq_of_continuousAt hfx hb] at ht
    nlinarith [ht]
  · rintro rfl
    exact subset_intervalFiberHull _ (subset_closure ⟨x, hx, rfl⟩)

def circleBandGraph {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) :
    Set (X × AddCircle (1 : ℝ)) :=
  (fun p : X × ℝ => (p.1, (p.2 : AddCircle (1 : ℝ)))) ''
    intervalFiberHull (clusterGraph G f)

theorem isCompact_circleBandGraph {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M) :
    IsCompact (circleBandGraph G f) := by
  exact (isCompact_intervalFiberHull (isCompact_clusterGraph hM)).image
    (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))

theorem circleBandGraph_on_open {X : Type*} [TopologicalSpace X]
    {G : Set X} (hG : IsOpen G) {f : X → ℝ} (hf : ContinuousOn f G)
    {x : X} (hx : x ∈ G) {t : AddCircle (1 : ℝ)} :
    (x, t) ∈ circleBandGraph G f ↔ (f x : AddCircle (1 : ℝ)) = t := by
  constructor
  · rintro ⟨⟨y, a⟩, ha, hout⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj hout
    rwa [(intervalFiberHull_clusterGraph_on_open hG hf hx).mp ha] at ht
  · intro ht
    exact ⟨(x, f x), (intervalFiberHull_clusterGraph_on_open hG hf hx).mpr rfl,
      Prod.ext rfl ht⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_BandLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the band with the lower and upper boundary limits

This connects the compact graph construction to the manuscript's
definition of a real coordinate band by liminf and limsup on the
physical domain.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem mem_clusterGraph_iff_mapClusterPt
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f : X → ℝ} {x : X} {t : ℝ} :
    (x, t) ∈ clusterGraph G f ↔ MapClusterPt t (𝓝[G] x) f := by
  constructor
  · intro ht
    obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp ht
    let v : ℕ → X := fun n => (z n).1
    have hvG : ∀ n, v n ∈ G := by
      intro n
      obtain ⟨y, hy, heq⟩ := hz n
      simpa only [v, ← heq] using hy
    have hv : Tendsto v atTop (𝓝[G] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuous_fst.tendsto (x, t) |>.comp hzt,
        Eventually.of_forall hvG⟩
    have hfz : Tendsto (f ∘ v) atTop (𝓝 t) := by
      convert continuous_snd.tendsto (x, t) |>.comp hzt using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      obtain ⟨y, hy, heq⟩ := hz n
      simp only [Function.comp_apply, v, ← heq]
    exact hfz.mapClusterPt.of_comp hv
  · intro ht
    obtain ⟨v, hfv, hv⟩ := ht.exists_seq_tendsto
    have hpair : Tendsto (fun n => (v n, f (v n))) atTop (𝓝 (x, t)) :=
      (tendsto_nhdsWithin_iff.mp hv).1.prodMk_nhds hfv
    apply mem_closure_of_tendsto hpair
    filter_upwards [(tendsto_nhdsWithin_iff.mp hv).2] with n hn
    exact ⟨v n, hn, rfl⟩

theorem intervalFiberHull_clusterGraph_eq_boundary_band
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    {x : X} (hx : x ∈ closure G) :
    {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph G f)} =
      Icc (liminf f (𝓝[G] x)) (limsup f (𝓝[G] x)) := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hbounds : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlower : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hbounds.mono (fun _ hy => hy.1))
  have hupper : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hbounds.mono (fun _ hy => hy.2))
  have hleast := isLeast_mapClusterPt_liminf hupper.isCoboundedUnder_ge hlower
  have hgreatest := isGreatest_mapClusterPt_limsup hlower.isCoboundedUnder_le hupper
  have heq : {t : ℝ | (x, t) ∈ clusterGraph G f} =
      {t | MapClusterPt t (𝓝[G] x) f} :=
    Set.ext (fun _ => mem_clusterGraph_iff_mapClusterPt)
  have hcompact := isCompact_real_fiber (isCompact_clusterGraph hM) x
  have hnonempty := clusterGraph_fiber_nonempty_of_mem_closure hM hx
  have hlo := hcompact.isLeast_sInf hnonempty
  have hhi := hcompact.isGreatest_sSup hnonempty
  rw [heq] at hlo hhi
  rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) x hnonempty]
  simpa only [heq] using congrArg₂ Icc (hlo.unique hleast) (hhi.unique hgreatest)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BandMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar measure of a projected band

The projection of a real interval of length `b - a` is contained in
the circle ball with midpoint `(a + b) / 2` and radius `(b - a) / 2`.
This gives the manuscript's band-incidence bound, including long bands.
-/

open Set MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem addCircle_image_Icc_subset_closedBall (a b : ℝ) :
    ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b ⊆
      closedBall (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ((b - a) / 2) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem volume_addCircle_image_Icc_le (a b : ℝ) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) ≤
      ENNReal.ofReal (min 1 (b - a)) := by
  calc
    _ ≤ volume (closedBall (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ((b - a) / 2)) :=
      measure_mono (addCircle_image_Icc_subset_closedBall a b)
    _ = _ := by rw [AddCircle.volume_closedBall]; congr 2; ring

theorem circleBandGraph_fiber_eq_image_realFiber
    {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) (x : X) :
    {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G f)} := by
  ext t
  constructor
  · rintro ⟨⟨y, r⟩, hr, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    exact ⟨r, hr, congrArg Prod.snd he⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(x, r), hr, rfl⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutoffStaircase
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joining a coordinate to a staircase outside a core

These are the differential and periodicity calculations for the actual
cutoff modification `u + χ (P ∘ u - u)` in finite transfer. They apply to
ordinary real branches and hence also to compatible periodic branches.
-/

open Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def cutoffStaircase {X : Type*} (u χ : X → ℝ) (P : ℝ → ℝ) (x : X) : ℝ :=
  u x + χ x * (P (u x) - u x)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_WedgeEstimate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Wedge estimate for cutoff staircase coordinates

The common cutoff differential makes the quadratic error term vanish.
The remaining terms have exactly the bounds used before taking independent
shift expectations in the finite-transfer construction.
-/

namespace CircleDomainRigidity.FiniteTransfer

def planarWedge (v w : ℝ × ℝ) : ℝ := v.1 * w.2 - v.2 * w.1

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RankOneFilling
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-one smooth filling of a collar

If at most one coordinate varies on a collar, extend that coordinate by
a smooth cutoff and all the others constantly. Every pairwise wedge of
the resulting coordinate gradients vanishes throughout the filling.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def planarGradient (f : (ℝ × ℝ) → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ f x (1, 0), fderiv ℝ f x (0, 1))

@[simp] theorem planarGradient_const (c : ℝ) (x : ℝ × ℝ) :
    planarGradient (fun _ => c) x = 0 := by
  simp [planarGradient]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveMollification
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smooth mollifiers preserve actual interval bounds and
constant plateaus. These are pointwise bounds on the input neighborhood. -/

open Set MeasureTheory Metric
open scoped Convolution

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem normed_convolution_mem_Icc
    (β : ContDiffBump (0 : E)) {u : E → ℝ} (hu : AEStronglyMeasurable u μ)
    {x : E} {a b : ℝ} (hb : ∀y ∈ ball x β.rOut, u y ∈ Icc a b) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) ∈ Icc a b := by
  have hab : a ≤ b := (hb x (mem_ball_self β.rOut_pos)).1.trans
    (hb x (mem_ball_self β.rOut_pos)).2
  have hr : 0 ≤ (b - a) / 2 := by linarith
  have hdist : ∀y ∈ ball x β.rOut, dist (u y) ((a + b) / 2) ≤ (b - a) / 2 := by
    intro y hy
    obtain ⟨hya, hyb⟩ := hb y hy
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have h := dist_convolution_le hr (β.support_normed_eq.subset)
    β.nonneg_normed β.integral_normed hu hdist
  rw [Real.dist_eq, abs_le] at h
  constructor <;> linarith [h.1, h.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_Staircase
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth periodic staircases

An explicit degree-one smooth staircase with spacing `h` and transition
half-width `δ`. The transition in the cell `[nh,(n+1)h]` is centered at
`(n+1/2)h`. The floor jumps cancel because the transition is flat near
the cell endpoints.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- A smooth staircase with transitions near the half-shifted `h` lattice. -/
def smoothStaircase (h δ x : ℝ) : ℝ :=
  h * ((⌊x / h⌋ : ℝ) + Real.smoothTransition
    ((x - h * (⌊x / h⌋ : ℝ) - (h / 2 - δ)) / (2 * δ)))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ShiftedStaircase
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The randomly shifted smooth staircase family

Translating the explicit staircase places its transition bands at
`θ + hℤ`. The resulting family has the exact derivative mean required
for uniform random shifts, and retains the displacement and period
properties needed for periodic coordinate branches.
-/

open MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The smooth staircase whose transition centers form `θ + hℤ`. -/
def shiftedStaircase (h δ θ x : ℝ) : ℝ :=
  smoothStaircase h δ ((x + h / 2) - θ) + θ - h / 2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RandomShifts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent uniform grid shifts

The shifts have normalized interval distribution. Any two distinct labels
have product law, so the two-shift integral equals their expected wedge cost.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def shiftLaw (h : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Icc 0 h)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_GridIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual probabilities that a shifted lattice meets a band

A grid of spacing `h` meets `[a,b]` exactly when the shift modulo `h`
lies in the projection of this interval. Haar measure of that projection
is at most `min h (b-a)`. Under the actual normalized interval law for
the shift, the probability is at most `min 1 ((b-a)/h)`.
-/

open Set MeasureTheory Metric

namespace CircleDomainRigidity.FiniteTransfer

def latticeBandIncidence (h a b : ℝ) : Set ℝ :=
  {θ | ∃ k : ℤ, θ + (k : ℝ) * h ∈ Icc a b}

theorem addCircle_eq_iff_exists_int (h a b : ℝ) :
    (a : AddCircle h) = (b : AddCircle h) ↔ ∃ k : ℤ, a = b + (k : ℝ) * h := by
  rw [← AddCommGroup.modEq_iff_eq_mod_zmultiples, AddCommGroup.modEq_comm,
    AddCommGroup.modEq_iff_eq_add_zsmul]
  simp only [zsmul_eq_mul]

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GridCollisions
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite terminal flags from actual independent grid shifts

For two different coordinate labels, their lattice-hit events have
product probability. Countably many flagged points and finitely many
label pairs can therefore be counted by Tonelli. Square-summable band
widths imply a finite expected collision count, hence only finitely many
flagged collisions for almost every choice of the grids.
-/

open Set MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

def pairedLatticeIncidence {n : ℕ} (h a b c d : ℝ) (i j : Fin n) :
    Set (Fin n → ℝ) :=
  {θ | θ i ∈ latticeBandIncidence h a b ∧ θ j ∈ latticeBandIncidence h c d}

noncomputable def gridCollisionCount {n : ℕ} {P S : Type*}
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : ℝ≥0∞ :=
  weightedBandIncidence
    (fun ps : P × S => pairedLatticeIncidence h (a (pairs ps.1).1 ps.2)
      (b (pairs ps.1).1 ps.2) (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2)
      (pairs ps.1).1 (pairs ps.1).2) (fun _ => 1) θ

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ReciprocalGridSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting an actual reciprocal-integer grid

The grid spacing must be `1/N` so that the staircases respect period one.
The laws of the uniform shifts change with the spacing. This selection
uses those actual product laws, keeps any prescribed conull compatibility
event, and makes both the wedge cost and scaled terminal count small.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def reciprocalGridStep (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

noncomputable def reciprocalGridLaw (n N : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => shiftLaw (reciprocalGridStep N))

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TerminalCounts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual terminal indices and their counting cost

Terminals consist of prescribed points together with points flagged by
two distinct grids. Their cardinality is bounded by the prescribed
cardinality plus the number of pair/flag incidences. This upper counting
cost is integrable and its expectation, scaled by the square of the
spacing, tends to zero for the actual reciprocal-grid laws.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

def gridTerminalIndices {n : ℕ} {P S : Type*} (F : Set S)
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : Set S :=
  F ∪ {s | ∃ p, θ ∈ pairedLatticeIncidence h
    (a (pairs p).1 s) (b (pairs p).1 s)
    (a (pairs p).2 s) (b (pairs p).2 s) (pairs p).1 (pairs p).2}

noncomputable def gridTerminalCost {n : ℕ} {P S : Type*} (F : Set S)
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : ℝ :=
  (F.ncard : ℝ) + (gridCollisionCount h pairs a b θ).toReal

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExpectedWedges
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Expected wedges for a finite family of actual random staircases

The product space has one uniform shift per coordinate. Distinct labels
have the two-shift law used in the analytic mean calculation.
-/

open MeasureTheory Set Finset

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def staircaseCovector (h δ χ θ x : ℝ) (u c : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - χ) + χ * deriv (shiftedStaircase h δ θ) x) • u +
    (shiftedStaircase h δ θ x - x) • c

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteWedgeCosts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The complete finite-list random wedge cost

The actual spatial wedge integrals are integrable random variables.
Summing their independent-pair estimates gives a mean bound uniform in
the staircase width, with an error proportional to the grid spacing.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def staircaseWidth (h : ℝ) (k : ℕ) : ℝ :=
  h / 8 * reciprocalGridStep k

noncomputable def staircasePairCost {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n : ℕ} (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (i j : Fin n) (θ : Fin n → ℝ) : ℝ :=
  ∫ z, |planarWedge
    (staircaseCovector h δ (χ z) (θ i) (x i z) (u i z) (c z))
    (staircaseCovector h δ (χ z) (θ j) (x j z) (u j z) (c z))| ∂μ

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitePatching
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patching the finite family of filling disks

On pairwise disjoint open disks, replace the old coordinate by its
smooth collar extension. Equality on full boundary neighborhoods gives
smoothness across every boundary, and local equality preserves the
rank-one wedge condition inside each filling disk.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def patchOpenRegions {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y) (x : X) : Y := by
  classical
  exact if h : ∃ i, x ∈ D i then g (Classical.choose h) x else f x

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- An actual smooth compactly supported planar cutoff, equal to one
on a neighborhood of the given compact set. -/
theorem exists_smooth_planar_cutoff {A O : Set ℂ}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧
      ∀ᶠ z in 𝓝ˢ A, f z = 1 := by
  obtain ⟨V, hV, hAV, hVO, hVc⟩ :=
    exists_open_between_and_isCompact_closure hA hO hAO
  have hdisj : Disjoint Vᶜ A :=
    Set.disjoint_left.mpr (fun z hz hzA => hz (hAV hzA))
  obtain ⟨f, hzero, hone, hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℂ))
      hV.isClosed_compl hA.isClosed hdisj (n := (⊤ : ℕ∞))
  have hsupp : Function.support (f : ℂ → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have htsupp : tsupport (f : ℂ → ℝ) ⊆ closure V := closure_mono hsupp
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, htsupp.trans hVO, hrange, hone⟩
  exact hVc.of_isClosed_subset isClosed_closure htsupp

/-- A positive superlevel of a compactly supported continuous function
has compact closure inside its topological support. -/
theorem closure_superlevel_subset_tsupport {f : ℂ → ℝ} {t : ℝ} (ht : 0 < t) :
    closure {z | t < f z} ⊆ tsupport f := by
  apply closure_mono
  intro z hz
  exact ne_of_gt (ht.trans hz)

theorem isCompact_nonzero_level {f : ℂ → ℝ} (hf : Continuous f)
    (hcompact : HasCompactSupport f) {t : ℝ} (ht : t ≠ 0) :
    IsCompact {z | f z = t} := by
  apply hcompact.of_isClosed_subset (isClosed_eq hf continuous_const)
  intro z hz
  apply subset_tsupport
  change f z ≠ 0
  rwa [hz]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The kernel of a nonzero real scalar differential on the plane is a line. -/
theorem finrank_ker_planar_functional {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker = 1 := by
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext z
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T z) h
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hlin
  rw [Complex.finrank_real_complex] at h
  change Module.finrank ℝ L.ker + 1 = 2 at h
  omega

/-- A genuine smooth ambient normal form for a regular planar scalar map.
The first chart coordinate is the original function, on its entire domain. -/
theorem exists_smooth_planar_level_chart {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z ∈ e.source ∧
      (∀ w, (e w).1 = f w) ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let L := fderiv ℝ f z
  have hL : L ≠ 0 := hz
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext w
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T w) h
  have hsurj : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hlin
  have hd : HasStrictFDerivAt f L z := hf.contDiffAt.hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let p := hd.implicitFunctionDataOfComplemented f L hsurj
    L.ker_closedComplemented_of_finiteDimensional_range
  let k : L.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_planar_functional hL, Module.finrank_self])
  let c : (ℝ × L.ker) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) k
  let g : ℂ → ℝ × ℝ := c ∘ p.prodFun
  have hp : ContDiff ℝ ∞ p.prodFun := by
    apply hf.prodMk
    exact (Classical.choose L.ker_closedComplemented_of_finiteDimensional_range).contDiff.comp
      (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ ∞ g := c.contDiff.comp hp
  let d : ℂ ≃L[ℝ] (ℝ × L.ker) :=
    p.leftDeriv.equivProdOfSurjectiveOfIsCompl p.rightDeriv
      p.range_leftDeriv p.range_rightDeriv p.isCompl_ker
  have hgd : HasFDerivAt g ((d.trans c : ℂ ≃L[ℝ] (ℝ × ℝ)) : ℂ →L[ℝ] (ℝ × ℝ)) z :=
    c.hasFDerivAt.comp z p.hasStrictFDerivAt.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hgd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let S := {w | (fderiv ℝ g w).IsInvertible}
  have hS : IsOpen S :=
    ContinuousLinearEquiv.isOpen.preimage (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hzS : z ∈ S := by
    change (fderiv ℝ g z).IsInvertible
    rw [hgd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  let e := e₀.restrOpen S hS
  have he : (e : ℂ → ℝ × ℝ) = g := rfl
  refine ⟨e, ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hgd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hzS⟩,
    ?_, he ▸ hg, ?_⟩
  · intro w
    rfl
  · intro y hy
    obtain ⟨d', hd'⟩ := (e.map_target hy).2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := d')
    · rw [he, hd']
      exact hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.differentiableAt.hasFDerivAt
    · rw [he]
      exact hg.contDiffAt

noncomputable def levelChartInverse {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t}) (y : ℝ) : {w // f w = t} := by
  classical
  exact if h : (t, y) ∈ e.target then
    ⟨e.symm (t, y), by
      rw [← he, e.right_inv h]⟩
  else z

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCovectorWedge
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Euclidean determinant bound for two real covectors on the
complex plane, with constant one. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem complexCovector_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

 theorem complexCovector_dualVector_norm_le (L : ℂ →L[ℝ] ℝ) :
    ‖(L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I‖ ≤ ‖L‖ := by
  let z : ℂ := (L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I
  have hzre : z.re = L 1 := by simp [z]
  have hzim : z.im = L Complex.I := by simp [z]
  have hnorm : ‖z‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hval : L z = ‖z‖ ^ 2 := by
    rw [complexCovector_apply, hzre, hzim, hnorm]
    ring
  have hle := L.le_opNorm z
  rw [hval, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hle
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ ‖L‖
    rw [hz]
    exact norm_nonneg _
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖z‖ ≤ ‖L‖
    nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactTransverseField
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit compactly supported smooth transverse field near a
compact regular scalar level, with a global Lipschitz bound. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

 def complexScalarGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 : ℂ) + (fderiv ℝ f z Complex.I : ℂ) * Complex.I

lemma complexScalarGradient_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexScalarGradient f) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).add
    ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).mul contDiff_const)

lemma complexScalarGradient_positive {f : ℂ → ℝ} {z : ℂ}
    (hz : fderiv ℝ f z ≠ 0) : 0 < fderiv ℝ f z (complexScalarGradient f z) := by
  have he : fderiv ℝ f z (complexScalarGradient f z) =
      (fderiv ℝ f z 1)^2 + (fderiv ℝ f z Complex.I)^2 := by
    rw [complexCovector_apply]
    simp only [complexScalarGradient, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [he]
  have hn : fderiv ℝ f z 1 ≠ 0 ∨ fderiv ℝ f z Complex.I ≠ 0 := by
    by_contra! hc
    apply hz
    ext v
    rw [complexCovector_apply, hc.1, hc.2]
    simp
  rcases hn with hn | hn <;> nlinarith [sq_pos_of_ne_zero hn,
    sq_nonneg (fderiv ℝ f z 1), sq_nonneg (fderiv ℝ f z Complex.I)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLevelTangent
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported smooth tangent field for an actual compact
regular planar level. This uses only the gradient of its defining scalar. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma complexScalarGradient_tangent (f : ℂ → ℝ) (z : ℂ) :
    (fderiv ℝ f z) (Complex.I * complexScalarGradient f z) = 0 := by
  rw [complexCovector_apply]
  simp only [complexScalarGradient,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma complexScalarGradient_ne_zero {f : ℂ → ℝ} {z : ℂ} (hz : fderiv ℝ f z ≠ 0) :
    complexScalarGradient f z ≠ 0 := by
  intro h
  have hp := complexScalarGradient_positive hz
  rw [h,map_zero] at hp
  exact (lt_irrefl 0) hp

lemma exists_compact_level_tangent {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set ℂ} (hK : IsCompact K) (hregular : ∀ z ∈ K, fderiv ℝ f z ≠ 0) :
    ∃ (V : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      LipschitzWith L V ∧ (∀ z, (fderiv ℝ f z) (V z) = 0) ∧
      (∀ z ∈ K, V z ≠ 0) := by
  obtain ⟨χ,hχ,hc,_,_,hone⟩ :=
    exists_smooth_planar_cutoff hK isOpen_univ (subset_univ _)
  let V : ℂ → ℂ := fun z => χ z • (Complex.I * complexScalarGradient f z)
  have hs : ContDiff ℝ ∞ V := hχ.smul (contDiff_const.mul (complexScalarGradient_smooth hf))
  have hVc : HasCompactSupport V := hc.smul_right
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  refine ⟨V,L,hs,hVc,hL,?_,?_⟩
  · intro z
    simp only [V,map_smul,complexScalarGradient_tangent,smul_zero]
  · intro z hz
    have hχz := hone.self_of_nhdsSet z hz
    simp only [V,hχz,one_smul]
    exact mul_ne_zero Complex.I_ne_zero (complexScalarGradient_ne_zero (hregular z hz))

lemma integral_curve_preserves_scalar {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {V : ℂ → ℂ} (htangent : ∀ z, (fderiv ℝ f z) (V z) = 0)
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) (s t : ℝ) :
    f (γ s) = f (γ t) := by
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) 0 t := by
    have h := (hf.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    simpa only [htangent] using h
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactVectorFieldFlow
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global integral curves of compactly supported smooth planar vector
fields, from a uniform Picard interval and the existing continuation theorem. -/
open Set Function Filter Metric
open scoped Topology ContDiff Manifold NNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_vector_field_global_curve {V : ℂ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) (x : ℂ) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hV.continuous
  let M : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hM (z : ℂ) : ‖V z‖ ≤ M := (hC z).trans (le_max_left _ _)
  have hlocal (z : ℂ) : ∃ γ : ℝ → ℂ, γ 0 = z ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt γ (V (γ t)) t := by
    let t₀ : Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    have hp : IsPicardLindelof (fun _ : ℝ => V) t₀ z (M+1) 0 M L := by
      refine ⟨fun _ _ => hL.lipschitzOnWith,fun _ _ => continuousOn_const,
        fun _ _ w _ => hM w,?_⟩
      simp only [t₀,NNReal.coe_add,NNReal.coe_one,NNReal.coe_zero,sub_zero,zero_sub,
        neg_neg,max_self]
      simp
    obtain ⟨γ,hγ0,hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self (show (0 : ℝ) ≤ (0 : ℝ≥0) from le_rfl))
    refine ⟨γ,hγ0,?_⟩
    intro t ht
    exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hv : ContMDiff (𝓘(ℝ,ℂ)) (𝓘(ℝ,ℂ)).tangent 1
      (fun z : ℂ => (⟨z,V z⟩ : TangentBundle (𝓘(ℝ,ℂ)) ℂ)) := by
    intro z
    apply (Bundle.contMDiffAt_section (IB := 𝓘(ℝ,ℂ))
      (E := TangentSpace (𝓘(ℝ,ℂ))) (s := fun z : ℂ => V z) z).mpr
    convert ((hV.of_le (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contMDiff).contMDiffAt using 1
    all_goals try with_reducible_and_instances rfl
    simp [mfld_simps]

  obtain ⟨γ,hγ0,hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hv
    (show (0 : ℝ) < 1 by norm_num) (fun z => by
      obtain ⟨γ,hγ0,hγ⟩ := hlocal z
      refine ⟨γ,hγ0,?_⟩
      intro t ht
      exact (hasMFDerivAt_iff_hasFDerivAt.mpr (hγ t ht).hasFDerivAt).hasMFDerivWithinAt) x
  refine ⟨γ,hγ0,?_⟩
  intro t
  exact hasDerivAt_iff_hasFDerivAt.mpr (hasMFDerivAt_iff_hasFDerivAt.mp (hγ t))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularLevelFlow
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

lemma smooth_integral_curve {V : ℂ → ℂ} (hV : ContDiff ℝ ∞ V)
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : ContDiff ℝ ∞ γ := by
  have hd : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  have he : deriv γ = V ∘ γ := funext fun t => (hγ t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨hd,by simp,?_⟩
    rw [he]
    exact (hV.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp ih

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedArgumentBasic
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary argument in turns on the punctured complex plane. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def normalizedArgument (z : ℂ) : UnitAddCircle :=
  AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero (Complex.arg z : Real.Angle)

theorem normalizedArgument_eq (z : ℂ) :
    normalizedArgument z = (Complex.arg z / (2 * Real.pi) : ℝ) := by
  change ((Complex.arg z * ((2 * Real.pi)⁻¹ * 1) : ℝ) : UnitAddCircle) = _
  congr 1
  simp only [mul_one, div_eq_mul_inv]

theorem continuousAt_normalizedArgument {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt normalizedArgument z :=
  ((AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).continuous.continuousAt).comp
    (Complex.continuousAt_arg_coe_angle hz)

theorem normalizedArgument_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    normalizedArgument (z * w) = normalizedArgument z + normalizedArgument w := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (z * w) : Real.Angle) = e (Complex.arg z) + e (Complex.arg w)
  rw [Complex.arg_mul_coe_angle hz hw]
  exact e.map_add _ _

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalArgumentBranch
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth local logarithmic branches of the circular argument. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def localArgumentBranch (a w : ℂ) : ℝ :=
  (Complex.log (w/a)).im / (2*Real.pi) + Complex.arg a / (2*Real.pi)

lemma localArgumentBranch_projects {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) :
    (localArgumentBranch a w : UnitAddCircle) = normalizedArgument w := by
  unfold localArgumentBranch
  rw [Complex.log_im, AddCircle.coe_add, ← normalizedArgument_eq,
    ← normalizedArgument_eq, ← normalizedArgument_mul (div_ne_zero hw ha) ha]
  rw [div_mul_cancel₀ _ ha]

lemma localArgumentBranch_smooth {a : ℂ} (ha : a ≠ 0) :
    ContDiffAt ℝ ∞ (localArgumentBranch a) a := by
  have hsl : a/a ∈ Complex.slitPlane := by simpa only [div_self ha] using Complex.one_mem_slitPlane
  have hv : ContDiffAt ℝ ∞ (fun w : ℂ => w/a) a := contDiffAt_id.div_const a
  have hh : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.log (w/a)) a :=
    ((Complex.contDiffAt_log hsl).restrict_scalars ℝ).comp (f := fun w : ℂ => w/a) a hv
  exact ((Complex.imCLM.contDiff.contDiffAt.comp a hh).div_const _).add contDiffAt_const

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PeriodicCircleDescent
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth period-one plane curve descends smoothly to the geometric
unit circle. The proof uses actual local logarithmic branches. -/
open Set Function Filter
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma toCircle_normalizedArgument (z : Circle) :
    AddCircle.toCircle (normalizedArgument (z : ℂ)) = z := by
  rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk]
  have he : 2 * Real.pi / (1 : ℝ) * (Complex.arg (z : ℂ) / (2*Real.pi)) =
      Complex.arg (z : ℂ) := by field_simp
  rw [he, Circle.exp_arg]

lemma normalizedArgument_circleExp (t : ℝ) :
    normalizedArgument (Circle.exp (2*Real.pi*t) : ℂ) = (t : UnitAddCircle) := by
  apply AddCircle.injective_toCircle one_ne_zero
  rw [toCircle_normalizedArgument, AddCircle.toCircle_apply_mk, div_one]

lemma normalizedArgument_injective_circle :
    Injective (fun z : Circle => normalizedArgument (z : ℂ)) := by
  intro z w h
  have he := congrArg AddCircle.toCircle h
  simpa only [toCircle_normalizedArgument] using he

def periodicCircleDescent {γ : ℝ → ℂ} (hγ : Periodic γ 1) (z : Circle) : ℂ :=
  hγ.lift (normalizedArgument (z : ℂ))

lemma periodicCircleDescent_exp {γ : ℝ → ℂ} (hγ : Periodic γ 1) (t : ℝ) :
    periodicCircleDescent hγ (Circle.exp (2*Real.pi*t)) = γ t := by
  rw [periodicCircleDescent, normalizedArgument_circleExp, hγ.lift_coe]

lemma periodicCircleDescent_smooth {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (hs : ContDiff ℝ ∞ γ) : ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ (periodicCircleDescent hγ) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by norm_num⟩
  have hcoe : ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  intro z
  let u : ℂ → ℂ := γ ∘ localArgumentBranch (z : ℂ)
  have hu : ContDiffAt ℝ ∞ u (z : ℂ) :=
    hs.contDiffAt.comp _ (localArgumentBranch_smooth z.coe_ne_zero)
  have he : periodicCircleDescent hγ =ᶠ[𝓝 z] (fun w : Circle => u (w : ℂ)) := by
    filter_upwards [] with w
    dsimp [periodicCircleDescent, u, Function.comp_def]
    rw [← localArgumentBranch_projects z.coe_ne_zero w.coe_ne_zero, hγ.lift_coe]
  exact (hu.contMDiffAt.comp z hcoe.contMDiffAt).congr_of_eventuallyEq he

lemma periodicCircleDescent_injective {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (hi : InjOn γ (Ico 0 1)) : Injective (periodicCircleDescent hγ) := by
  intro z w he
  let r := AddCircle.equivIco 1 0 (normalizedArgument (z : ℂ))
  let s := AddCircle.equivIco 1 0 (normalizedArgument (w : ℂ))
  have hr : (r.val : UnitAddCircle) = normalizedArgument (z : ℂ) := AddCircle.coe_equivIco
  have hs : (s.val : UnitAddCircle) = normalizedArgument (w : ℂ) := AddCircle.coe_equivIco
  have he' : γ r.val = γ s.val := by
    simpa only [periodicCircleDescent, ← hr, ← hs, hγ.lift_coe] using he
  have hrs := hi (by simpa only [zero_add] using r.property)
    (by simpa only [zero_add] using s.property) he'
  exact normalizedArgument_injective_circle
    (hr.symm.trans ((congrArg (fun t : ℝ => (t : UnitAddCircle)) hrs).trans hs))

lemma periodicCircleDescent_range {γ : ℝ → ℂ} (hγ : Periodic γ 1) :
    range (periodicCircleDescent hγ) = range γ := by
  apply Subset.antisymm
  · rintro y ⟨z,rfl⟩
    let r := AddCircle.equivIco 1 0 (normalizedArgument (z : ℂ))
    refine ⟨r.val,?_⟩
    have hr : (r.val : UnitAddCircle) = normalizedArgument (z : ℂ) := AddCircle.coe_equivIco
    rw [periodicCircleDescent, ← hr, hγ.lift_coe]
  · rintro y ⟨t,rfl⟩
    exact ⟨Circle.exp (2*Real.pi*t),periodicCircleDescent_exp hγ t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OuterContours
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem planar_unit_sphere_connected : IsConnected (Metric.sphere (0 : ℂ) 1) :=
  isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one

theorem planar_unit_exterior_connected :
    IsConnected (Metric.closedBall (0 : ℂ) 1)ᶜ := by
  let g : ℂ × ℝ → ℂ := fun p => p.2 • p.1
  have hg : Continuous g := continuous_snd.smul continuous_fst
  have heq : g '' (Metric.sphere (0 : ℂ) 1 ×ˢ Ioi (1 : ℝ)) =
      (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨w, r⟩, ⟨hw, hr⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hr0 : 0 < r := zero_lt_one.trans hr
      simpa [g, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hw'] using hr
    · intro hz
      have hz' : 1 < ‖z‖ := by simpa using hz
      have hn : ‖z‖ ≠ 0 := (zero_lt_one.trans hz').ne'
      refine ⟨(‖z‖⁻¹ • z, ‖z‖), ⟨?_, hz'⟩, ?_⟩
      · apply mem_sphere_zero_iff_norm.mpr
        simp [hn]
      · simp [g, hn]
  rw [← heq]
  exact (planar_unit_sphere_connected.prod isConnected_Ioi).image g hg.continuousOn

theorem subset_inside_or_exterior {S U : Set ℂ} (hU : IsOpen U)
    (hS : IsPreconnected S) (hdisj : Disjoint S (frontier U)) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
  · intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hzcl
      apply Set.disjoint_left.mp hdisj hz
      rw [frontier, hU.interior_eq]
      exact ⟨hzcl, hzU⟩

theorem exterior_not_bounded {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ¬ Bornology.IsBounded Uᶜ := by
  intro hUc
  apply NormedSpace.unbounded_univ ℝ ℂ
  simpa only [union_compl_self] using hU.union hUc

theorem closed_fill_subset_of_frontier_subset {U V : Set ℂ}
    (hU : IsOpen U) (_hV : IsOpen V)
    (hVregular : interior (closure V) = V)
    (hUcompact : IsCompact (closure U)) (hVcompact : IsCompact (closure V))
    (hVexterior : IsPreconnected (closure V)ᶜ)
    (hfront : frontier U ⊆ V) : closure U ⊆ V := by
  have hdisj : Disjoint (closure V)ᶜ (frontier U) :=
    Set.disjoint_left.mpr (fun z hz hz' => hz (subset_closure (hfront hz')))
  have hext : (closure V)ᶜ ⊆ (closure U)ᶜ := by
    rcases subset_inside_or_exterior hU hVexterior hdisj with h | h
    · exact False.elim (exterior_not_bounded hVcompact.isBounded
        ((hUcompact.isBounded.subset subset_closure).subset h))
    · exact h
  have hcl : closure U ⊆ closure V := compl_subset_compl.mp hext
  have hUV : U ⊆ V := by
    calc
      U = interior U := hU.interior_eq.symm
      _ ⊆ interior (closure V) := interior_mono (subset_closure.trans hcl)
      _ = V := hVregular
  rw [closure_eq_self_union_frontier]
  exact union_subset hUV hfront

theorem disjoint_or_nested_closed_fills {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVregular : interior (closure V) = V)
    (hUcompact : IsCompact (closure U)) (hVcompact : IsCompact (closure V))
    (hUfront : IsPreconnected (frontier U)) (hVconn : IsPreconnected V)
    (hVext : IsPreconnected (closure V)ᶜ)
    (hdisj : Disjoint (frontier U) (frontier V)) :
    Disjoint (closure U) (closure V) ∨ closure U ⊆ V ∨ closure V ⊆ U := by
  rcases subset_inside_or_exterior hV hUfront hdisj with hfront | hfront
  · exact Or.inr (Or.inl (closed_fill_subset_of_frontier_subset hU hV hVregular
      hUcompact hVcompact hVext hfront))
  · have hd : Disjoint V (frontier U) := Set.disjoint_left.mpr (fun z hz hz' =>
      hfront hz' (subset_closure hz))
    rcases subset_inside_or_exterior hU hVconn hd with hVU | hVout
    · right; right
      intro z hz
      have hzclU := closure_mono hVU hz
      by_contra hzU
      have hzfront : z ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hzclU, hzU⟩
      exact hfront hzfront hz
    · left
      have hVclout : closure V ⊆ Uᶜ := by
        apply closure_minimal _ hU.isClosed_compl
        intro z hz hzU
        exact hVout hz (subset_closure hzU)
      apply Set.disjoint_left.mpr
      intro z hzU hzV
      have hnotU := hVclout hzV
      have hzfront : z ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hzU, hnotU⟩
      exact hfront hzfront hzV

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InactiveCollars
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Staircases are constant on collars avoiding their grids

A compact connected collar has a compact connected real branch image.
If this image misses the translated lattice, it has positive distance
from that closed lattice. Every sufficiently narrow staircase therefore
has zero derivative on the image and is constant on the collar. The
width bound can be chosen simultaneously for finitely many collars.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

def shiftedLattice (h θ : ℝ) : Set ℝ := Set.range (fun k : ℤ => θ + h * k)

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FilledCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def IsFilledCoordinateFamily {I L : Type*}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ))
    (v F : L → (ℝ × ℝ) → ℝ) : Prop :=
  (∀ l, ContDiffOn ℝ ∞ (F l) Ω) ∧
  (∀ l x, (∀ i, x ∉ D i) → F l x = v l x) ∧
  (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l, F l x = v l x) ∧
  ∀ i l m, l ≠ m → ∀ x ∈ D i,
    planarWedge (planarGradient (F l) x) (planarGradient (F m) x) = 0

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The regularized metric energy in finite transfer

For the two eigenvalues of the positive semidefinite tensor formed by the
coordinate differentials, this is the energy density for the regularized
metric `A + τ g₀`. These estimates are the scalar analytic step in
the finite-transfer construction. In particular, rank-one fillings have
vanishing limiting energy.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable section

/-- Sum of the two coordinate energy contributions in an eigenframe. -/
def metricEnergy (a b τ : ℝ) : ℝ :=
  a * Real.sqrt (b + τ) / Real.sqrt (a + τ) +
    b * Real.sqrt (a + τ) / Real.sqrt (b + τ)

end

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TensorEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From a positive two-dimensional tensor to optimized energy

The trace and determinant determine the energy of `A + τ I`. The scalar
roots used below are the two nonnegative eigenvalues, constructed directly
from the characteristic polynomial. This connects the metric limit to
the Gram determinant of the actual finite list of coordinate differentials.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def upperRoot (T D : ℝ) : ℝ := (T + Real.sqrt (T ^ 2 - 4 * D)) / 2
def lowerRoot (T D : ℝ) : ℝ := (T - Real.sqrt (T ^ 2 - 4 * D)) / 2

/-- The coordinate-invariant expression for the regularized energy density. -/
def tensorEnergy (T D τ : ℝ) : ℝ :=
  (2 * D + τ * T) / Real.sqrt (D + τ * T + τ ^ 2)

/-- Trace of the Gram tensor formed from a finite list of planar covectors. -/
def covectorTrace (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i ^ 2) + (∑ i ∈ Finset.range n, y i ^ 2)

/-- Determinant of the same Gram tensor. -/
def covectorDet (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i ^ 2) * (∑ i ∈ Finset.range n, y i ^ 2) -
    (∑ i ∈ Finset.range n, x i * y i) ^ 2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the finite-transfer regularization

For a finite list of planar differentials, a small integral of absolute
pairwise wedges produces a regularized metric with small total energy.
This proves the energy optimization step of finite transfer, after the
geometric filling and staircase construction have supplied the differentials.
-/

open Filter MeasureTheory Finset
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Each unordered pair is counted exactly once. -/
def covectorWedges (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, |x i * y j - x j * y i|

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricTensor
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The regularized metric as a matrix

This identifies the scalar energy expression with
`trace ((A + τ I)⁻¹ A) sqrt (det (A + τ I))`, and proves that
regularizing a positive semidefinite tensor gives a positive definite
metric. Thus the energy optimization applies to the actual metric tensor.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def symmetricTensor (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

def regularizedTensor (a b c τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTensor a b c + τ • 1

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_GramMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the actual metric from the coordinate differentials

The Gram tensor is the sum of the rank-one coordinate tensors.
Regularization makes it a positive definite metric, and the integral
bound is for its actual inverse-matrix energy density.
-/

open Matrix MeasureTheory Finset
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def gramTensor (x y : ℕ → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTensor (∑ i ∈ range n, x i ^ 2) (∑ i ∈ range n, x i * y i)
    (∑ i ∈ range n, y i ^ 2)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricInterpolation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Keeping the original metric near the retained core

The interpolated metric is an actual positive definite matrix field.
Its coordinate energy is the inverse-matrix energy density, rather than
an independently supplied scalar surrogate.
-/

open Matrix Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

abbrev PlanarMetric := Matrix (Fin 2) (Fin 2) ℝ

def matrixEnergy (A g : PlanarMetric) : ℝ :=
  Matrix.trace (g⁻¹ * A) * Real.sqrt g.det

def blendMetric (g : PlanarMetric) (t : ℝ) : PlanarMetric :=
  (1 - t) • 1 + t • g

@[simp] theorem blendMetric_zero (g : PlanarMetric) : blendMetric g 0 = 1 := by
  simp [blendMetric]

@[simp] theorem blendMetric_one (g : PlanarMetric) : blendMetric g 1 = g := by
  simp [blendMetric]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The separate coordinate energies in the chosen metric

The inverse-matrix trace density is exactly the sum of the nonnegative
squared covector norms. Thus control of the Gram energy controls every
coordinate, and in the identity metric these are the usual squared
Euclidean differential norms.
-/

open Matrix Finset
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def covectorEnergy (v : Fin 2 → ℝ) (g : PlanarMetric) : ℝ :=
  v ⬝ᵥ (g⁻¹ *ᵥ v) * Real.sqrt g.det

theorem covectorEnergy_eq_matrixEnergy (v : Fin 2 → ℝ) (g : PlanarMetric) :
    covectorEnergy v g = matrixEnergy (Matrix.vecMulVec v v) g := by
  rw [matrixEnergy, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact congrArg (fun a : ℝ => a * Real.sqrt g.det) (dotProduct_comm _ _)

theorem covectorEnergy_nonneg (v : Fin 2 → ℝ) {g : PlanarMetric} (hg : g.PosDef) :
    0 ≤ covectorEnergy v g := by
  apply mul_nonneg _ (Real.sqrt_nonneg _)
  simpa only [star_trivial] using hg.inv.posSemidef.dotProduct_mulVec_nonneg v

@[simp] theorem covectorEnergy_identity (a b : ℝ) :
    covectorEnergy ![a,b] 1 = a ^ 2 + b ^ 2 := by
  simp [covectorEnergy, dotProduct, Fin.sum_univ_two, pow_two]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_UpperPairs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite wedge sum and its pair indexing

Each unordered coordinate pair occurs exactly once. This identifies the
spatial cost selected by the random-grid argument with the wedge sum of
the actual cutoff staircase differentials.
-/

open Set MeasureTheory Finset Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

abbrev UpperPairs (n : ℕ) := (j : Fin n) × Fin j.val

def upperPair {n : ℕ} (p : UpperPairs n) : Fin n × Fin n :=
  (⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SupportedMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric changes with compact support

The original core may be unbounded in a planar chart, as happens when
the retained spherical core contains infinity. Only its intersection
with a compact neighborhood of the completed piece is needed for the
interpolation. A second cutoff keeps the metric unchanged at infinity.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

@[simp] theorem blendMetric_identity (t : ℝ) : blendMetric 1 t = 1 := by
  rw [blendMetric, ← add_smul]
  simp

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restoring the spherical metric factor

In two dimensions positive scalar rescaling leaves the full Dirichlet
energy density unchanged. Thus a compactly supported metric modification
in a planar chart can retain the original spherical factor both near
the core and outside a compact set.
-/

open Matrix Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem matrixEnergy_pos_smul (A : PlanarMetric) {g : PlanarMetric}
    (hg : g.PosDef) {c : ℝ} (hc : 0 < c) :
    matrixEnergy A (c • g) = matrixEnergy A g := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  have hinv : (c • g)⁻¹ = c⁻¹ • g⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul (A := g) c
      (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  unfold matrixEnergy
  rw [hinv, smul_mul_assoc, Matrix.trace_smul, Matrix.det_smul]
  simp only [Fintype.card_fin, smul_eq_mul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  field_simp

def sphericalMetricFactor (z : ℝ × ℝ) : ℝ :=
  4 / (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2

theorem sphericalMetricFactor_pos (z : ℝ × ℝ) : 0 < sphericalMetricFactor z := by
  unfold sphericalMetricFactor
  positivity

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanExteriors
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- Fill connected boundary components into either side of a hypothetical
separation. Finiteness makes both enlarged sides closed. -/
theorem isPreconnected_compl_finite_open_disks
    {X I : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hfront : ∀ i, IsPreconnected (frontier (U i)))
    (hdisj : Pairwise (Disjoint on fun i => closure (U i))) :
    IsPreconnected (⋃ i, U i)ᶜ := by
  classical
  let C : Set X := (⋃ i, U i)ᶜ
  have hC : IsClosed C := (isOpen_iUnion hU).isClosed_compl
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hC).mpr
  intro A B hA hB hcover hAB
  let A₀ := A ∩ C
  let B₀ := B ∩ C
  have hfrontC (i : I) : frontier (U i) ⊆ C := by
    intro x hx hxU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
    by_cases hij : i = j
    · subst j
      rw [(hU i).frontier_eq] at hx
      exact hx.2 hj
    · exact Set.disjoint_left.mp (hdisj hij) (frontier_subset_closure hx)
        (subset_closure hj)
  have hchoice (i : I) : frontier (U i) ⊆ A₀ ∨ frontier (U i) ⊆ B₀ := by
    apply (isPreconnected_iff_subset_of_disjoint_closed.mp (hfront i)) A₀ B₀
      (hA.inter hC) (hB.inter hC)
    · intro x hx
      exact (hcover (hfrontC i hx)).imp (fun h => ⟨h, hfrontC i hx⟩)
        (fun h => ⟨h, hfrontC i hx⟩)
    · apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨_, hxA, hxB⟩
      exact Set.disjoint_left.mp hAB hxA.1 hxB.1
  let P : Set I := {i | frontier (U i) ⊆ A₀}
  have hBfront (i : I) (hi : i ∉ P) : frontier (U i) ⊆ B₀ :=
    (hchoice i).resolve_left hi
  let A' := A₀ ∪ ⋃ i ∈ P, closure (U i)
  let B' := B₀ ∪ ⋃ i ∈ Pᶜ, closure (U i)
  have hA' : IsClosed A' := (hA.inter hC).union
    (P.toFinite.isClosed_biUnion (fun _ _ => isClosed_closure))
  have hB' : IsClosed B' := (hB.inter hC).union
    (Pᶜ.toFinite.isClosed_biUnion (fun _ _ => isClosed_closure))
  have hclC (i : I) : closure (U i) ∩ C ⊆ frontier (U i) := by
    intro x hx
    rw [frontier, (hU i).interior_eq]
    exact ⟨hx.1, fun hxU => hx.2 (mem_iUnion.mpr ⟨i, hxU⟩)⟩
  have hA'B' : Disjoint A' B' := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
    · exact Set.disjoint_left.mp hAB hxA.1 hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      exact Set.disjoint_left.mp hAB hxA.1 (hBfront i hi (hclC i ⟨hxi, hxA.2⟩)).1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      exact Set.disjoint_left.mp hAB (hi (hclC i ⟨hxi, hxB.2⟩)).1 hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxB
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj hij) hxi hxj
  have htotal : (univ : Set X) ⊆ A' ∪ B' := by
    intro x _
    by_cases hx : x ∈ C
    · exact (hcover hx).imp (fun h => Or.inl ⟨h, hx⟩) (fun h => Or.inl ⟨h, hx⟩)
    · have hxU : x ∈ ⋃ i, U i := by simpa only [C, mem_compl_iff, not_not] using hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      by_cases hiP : i ∈ P
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, hiP, subset_closure hi⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨i, hiP, subset_closure hi⟩))
  have hside := (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ).mp
    isPreconnected_univ A' B' hA' hB' htotal hA'B'
  rcases hside with hside | hside
  · left
    intro x hx
    rcases hside (mem_univ x) with hxA | hxA
    · exact hxA.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      exact (hi (hclC i ⟨hxi, hx⟩)).1
  · right
    intro x hx
    rcases hside (mem_univ x) with hxB | hxB
    · exact hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      exact (hBfront i hi (hclC i ⟨hxi, hx⟩)).1

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- Closed sphere sets avoiding infinity have compact finite-coordinate
preimages. This is the concrete properness needed for the obstacle piece. -/
theorem isCompact_finite_preimage {K : Set Sphere} (hK : IsClosed K) (hinfty : OnePoint.infty ∉ K) :
    IsCompact (((↑) : ℂ → Sphere) ⁻¹' K) :=
  ((OnePoint.isClosed_iff_of_notMem hinfty).mp hK).2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FiniteChartConnectivity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing a connected exterior through the finite sphere chart

Deleting an interior point from a connected set preserves connectedness when
that point has a connected punctured neighborhood. Applied at infinity, this
turns the connected sphere inverse image of a quotient exterior into the
connected unbounded planar exterior needed for smooth contour filling.
-/

open Set Filter Function Metric
open scoped Topology OnePoint

namespace CircleDomainRigidity

theorem puncture_subset_of_boundary_color
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S A B U : Set X} {p : X} (hp : p ∉ S)
    (hconn : IsPreconnected (insert p S))
    (hA : IsClosed A) (hB : IsClosed B) (hcover : S ⊆ A ∪ B)
    (hAB : S ∩ (A ∩ B) = ∅) (hU : U ∈ 𝓝 p)
    (hcolor : U \ {p} ⊆ A) : S ⊆ A := by
  have hpB : p ∉ closure (S ∩ B) := by
    intro h
    obtain ⟨z, hzU, hzS, hzB⟩ := mem_closure_iff_nhds.mp h U hU
    have hzp : z ≠ p := fun heq => hp (heq ▸ hzS)
    have hzA := hcolor ⟨hzU, by simpa using hzp⟩
    have hbad : z ∈ S ∩ (A ∩ B) := ⟨hzS, hzA, hzB⟩
    simp only [hAB, mem_empty_iff_false] at hbad
  let A' := closure (S ∩ A) ∪ {p}
  let B' := closure (S ∩ B)
  have hcov : insert p S ⊆ A' ∪ B' := by
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Or.inr rfl)
    · rcases hcover hz with hzA | hzB
      · exact Or.inl (Or.inl (subset_closure ⟨hz, hzA⟩))
      · exact Or.inr (subset_closure ⟨hz, hzB⟩)
  have hdisj : insert p S ∩ (A' ∩ B') = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzA, hzB⟩
    rcases hz with rfl | hz
    · exact hpB hzB
    · have hzA' : z ∈ A := by
        rcases hzA with hzA | hzA
        · exact closure_minimal inter_subset_right hA hzA
        · exact (hp (mem_singleton_iff.mp hzA ▸ hz)).elim
      have hzB' : z ∈ B := closure_minimal inter_subset_right hB hzB
      have hbad : z ∈ S ∩ (A ∩ B) := ⟨hz, hzA', hzB'⟩
      simp only [hAB, mem_empty_iff_false] at hbad
  have hside := (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) A' B'
    (isClosed_closure.union isClosed_singleton) isClosed_closure hcov hdisj
  rcases hside with hside | hside
  · intro z hz
    rcases hside (Or.inr hz) with hzA | hzA
    · exact closure_minimal inter_subset_right hA hzA
    · exact (hp (mem_singleton_iff.mp hzA ▸ hz)).elim
  · exact (hpB (hside (Or.inl rfl))).elim

/-- A point with a connected punctured neighborhood is not a cut point
of any connected set containing that neighborhood. -/
theorem isPreconnected_puncture_of_connected_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S U : Set X} {p : X} (hp : p ∉ S)
    (hconn : IsPreconnected (insert p S)) (hU : U ∈ 𝓝 p)
    (hUS : U \ {p} ⊆ S) (hpuncture : IsPreconnected (U \ {p})) :
    IsPreconnected S := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro A B hA hB hcover hAB
  have hchoice := (isPreconnected_iff_subset_of_disjoint_closed.mp hpuncture)
    A B hA hB (hUS.trans hcover) (by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, hzA, hzB⟩
      have hbad : z ∈ S ∩ (A ∩ B) := ⟨hUS hz, hzA, hzB⟩
      simp only [hAB, mem_empty_iff_false] at hbad)
  rcases hchoice with hchoice | hchoice
  · exact Or.inl (puncture_subset_of_boundary_color hp hconn hA hB hcover hAB hU hchoice)
  · right
    apply puncture_subset_of_boundary_color hp hconn hB hA
      (by simpa only [union_comm] using hcover) _ hU hchoice
    simpa only [inter_comm A B] using hAB

theorem isConnected_complex_exterior_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (closedBall (0 : ℂ) R)ᶜ := by
  let g : ℂ × ℝ → ℂ := fun p => p.2 • p.1
  have hg : Continuous g := continuous_snd.smul continuous_fst
  have heq : g '' (sphere (0 : ℂ) 1 ×ˢ Ioi R) = (closedBall (0 : ℂ) R)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨w, r⟩, ⟨hw, hr⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hr0 : 0 < r := hR.trans_lt hr
      simpa [g, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hw'] using hr
    · intro hz
      have hz' : R < ‖z‖ := by simpa using hz
      have hn : ‖z‖ ≠ 0 := (hR.trans_lt hz').ne'
      refine ⟨(‖z‖⁻¹ • z, ‖z‖), ⟨?_, hz'⟩, ?_⟩
      · apply mem_sphere_zero_iff_norm.mpr
        simp [hn]
      · simp [g, hn]
  rw [← heq]
  exact ((isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num)
    (0 : ℂ) zero_le_one).prod isConnected_Ioi).image g hg.continuousOn

/-- The finite part of a connected sphere set containing a neighborhood
of infinity is preconnected and unbounded. -/
theorem finite_part_connected_unbounded {K : Set Sphere}
    (hK : IsPreconnected K) (hinfty : ∞ ∈ interior K) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' K) ∧
      ¬ Bornology.IsBounded (((↑) : ℂ → Sphere) ⁻¹' K) := by
  have hsmall := (OnePoint.isOpen_iff_of_mem hinfty).mp isOpen_interior
  obtain ⟨R, hR, hbound⟩ := hsmall.2.isBounded.exists_pos_norm_lt
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  let U : Set Sphere := (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ
  have hUopen : IsOpen U :=
    (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).isOpen_compl
  have hinftyU : (∞ : Sphere) ∈ U := OnePoint.infty_notMem_image_coe
  have hUeq : U \ {∞} = ((↑) : ℂ → Sphere) '' E := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [U]
    | coe z => simp [U, E, OnePoint.coe_injective.mem_set_image]
  have hEs : E ⊆ ((↑) : ℂ → Sphere) ⁻¹' K := by
    intro z hz
    by_contra hzK
    have hzsmall : z ∈ (((↑) : ℂ → Sphere) ⁻¹' interior K)ᶜ := by
      intro h
      apply hzK
      change (z : Sphere) ∈ K
      exact interior_subset h
    have hn : R < ‖z‖ := by simpa [E] using hz
    exact (not_lt_of_ge (hbound z hzsmall).le) hn
  have hpuncture : IsPreconnected (U \ {∞}) := by
    rw [hUeq]
    exact (isConnected_complex_exterior_closedBall hR.le).isPreconnected.image _
      OnePoint.continuous_coe.continuousOn
  have hset : insert (∞ : Sphere) (K \ {∞}) = K := by
    rw [insert_sdiff_singleton, insert_eq_of_mem (interior_subset hinfty)]
  have hfinite : IsPreconnected (K \ {∞}) := by
    apply isPreconnected_puncture_of_connected_neighborhood
      (by simp) (hset.symm ▸ hK) (hUopen.mem_nhds hinftyU) _ hpuncture
    rw [hUeq]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hEs hz, by simp⟩
  have himage : ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' K) = K \ {∞} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  refine ⟨OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    (himage.symm ▸ hfinite), ?_⟩
  intro hb
  have hball : Bornology.IsBounded (closedBall (0 : ℂ) R) := isBounded_closedBall
  have htotal := hball.union (hb.subset hEs)
  rw [union_compl_self] at htotal
  exact NormedSpace.unbounded_univ ℝ ℂ htotal

/-- A closed quotient with connected fibers pulls a closed connected
quotient exterior back to a connected unbounded physical exterior. -/
theorem physical_exterior_connected_unbounded_of_quotient
    {X : Type*} [TopologicalSpace X]
    (π : Sphere → X) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hsurj : Surjective π) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {V : Set X} (hV : IsOpen V) (hVconn : IsConnected Vᶜ)
    (hinfty : π ∞ ∉ closure V) :
    IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ ∧
      ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ := by
  have hK : IsConnected (π ⁻¹' Vᶜ) :=
    (hclosed.isQuotientMap hπ hsurj).isCoinducing.isConnected_preimage_of_isClosed
      hfibers hV.isClosed_compl hVconn
  have hnbd : π ⁻¹' (closure V)ᶜ ∈ 𝓝 (∞ : Sphere) :=
    (isClosed_closure.isOpen_compl.preimage hπ).mem_nhds hinfty
  have hnear : π ⁻¹' Vᶜ ∈ 𝓝 (∞ : Sphere) :=
    Filter.mem_of_superset hnbd (preimage_mono (compl_subset_compl.mpr subset_closure))
  have h := finite_part_connected_unbounded hK.isPreconnected
    (mem_interior_iff_mem_nhds.mpr hnear)
  simpa only [preimage_compl, preimage_preimage, Function.comp_def] using h

/-- Specialization to a component-collapse quotient. -/
theorem physical_exterior_connected_unbounded_of_component_collapse
    {X : Type*} [TopologicalSpace X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {V : Set X} (hV : IsOpen V) (hVconn : IsConnected Vᶜ)
    (hinfty : π ∞ ∉ closure V) :
    IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ ∧
      ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ :=
  physical_exterior_connected_unbounded_of_quotient π hπ hclosed hsurj
    (connected_fibers_of_component_collapse G π hsurj hr) hV hVconn hinfty

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereNeighborhoods
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected-complement neighborhoods on the concrete sphere

Finite points use ordinary round disks. Infinity uses complements of closed
round disks. Thus every open sphere neighborhood contains the closure of an
open neighborhood with connected complement, as needed for contour filling.
-/

open Set Filter Function Metric
open scoped Topology OnePoint

namespace CircleDomainRigidity

theorem infty_mem_closure_image_of_unbounded {S : Set ℂ}
    (hS : ¬ Bornology.IsBounded S) :
    (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
  by_contra h
  have hc := isCompact_finite_preimage isClosed_closure h
  apply hS
  apply hc.isBounded.subset
  intro z hz
  exact subset_closure (mem_image_of_mem _ hz)

theorem isConnected_complex_exterior_closedBall_center (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (closedBall c R)ᶜ := by
  have heq : (fun z : ℂ => z + c) '' (closedBall (0 : ℂ) R)ᶜ = (closedBall c R)ᶜ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mem_closedBall, dist_eq_norm] using hw
    · intro hz
      refine ⟨z - c, ?_, sub_add_cancel z c⟩
      simpa [mem_closedBall, dist_eq_norm] using hz
  rw [← heq]
  exact (isConnected_complex_exterior_closedBall hR).image _
    (continuous_id.add_const c).continuousOn

theorem unbounded_complex_exterior (c : ℂ) (R : ℝ) :
    ¬ Bornology.IsBounded (closedBall c R)ᶜ := by
  intro h
  have hb := (isBounded_closedBall (x := c) (r := R)).union h
  rw [union_compl_self] at hb
  exact NormedSpace.unbounded_univ ℝ ℂ hb

theorem isConnected_sphere_exterior_closedBall (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected ((((↑) : ℂ → Sphere) '' closedBall c R)ᶜ) := by
  let E : Set ℂ := (closedBall c R)ᶜ
  have hE : IsConnected (((↑) : ℂ → Sphere) '' E) :=
    (isConnected_complex_exterior_closedBall_center c hR).image _
      OnePoint.continuous_coe.continuousOn
  have hInf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' E) :=
    infty_mem_closure_image_of_unbounded (unbounded_complex_exterior c R)
  apply hE.subset_closure
  · rintro p ⟨z, hz, rfl⟩
    simpa [E, OnePoint.coe_injective.mem_set_image] using hz
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hInf
    | coe z =>
      apply subset_closure
      exact mem_image_of_mem _ (by simpa [E, OnePoint.coe_injective.mem_set_image] using hp)

theorem isConnected_sphere_exterior_ball (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsConnected ((((↑) : ℂ → Sphere) '' ball c R)ᶜ) := by
  have hE : IsConnected (ball c R)ᶜ := by
    have hc := (isConnected_complex_exterior_closedBall_center c hR.le).closure
    simpa only [closure_compl, interior_closedBall c hR.ne'] using hc
  have hi : IsConnected (((↑) : ℂ → Sphere) '' (ball c R)ᶜ) :=
    hE.image _ OnePoint.continuous_coe.continuousOn
  have hu : ¬ Bornology.IsBounded (ball c R)ᶜ := fun h =>
    unbounded_complex_exterior c R (h.subset (compl_subset_compl.mpr ball_subset_closedBall))
  have hInf := infty_mem_closure_image_of_unbounded hu
  apply hi.subset_closure
  · rintro p ⟨z, hz, rfl⟩
    simpa [OnePoint.coe_injective.mem_set_image] using hz
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hInf
    | coe z =>
      apply subset_closure
      exact mem_image_of_mem _ (by simpa [OnePoint.coe_injective.mem_set_image] using hp)

/-- A concrete sphere basis with compact containment and connected
complements. At finite points the neighborhoods are physical round disks;
at infinity they are exteriors of physical closed round disks. -/
theorem exists_sphere_neighborhood_connected_compl
    {W : Set Sphere} (hW : IsOpen W) {x : Sphere} (hx : x ∈ W) :
    ∃ V : Set Sphere, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧ IsConnected Vᶜ := by
  cases x using OnePoint.rec with
  | coe z =>
    have hn : ((↑) : ℂ → Sphere) ⁻¹' W ∈ 𝓝 z :=
      (hW.preimage OnePoint.continuous_coe).mem_nhds hx
    obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hn
    let V : Set Sphere := ((↑) : ℂ → Sphere) '' ball z r
    have hcl : closure V = ((↑) : ℂ → Sphere) '' closedBall z r := by
      apply Set.Subset.antisymm
      · apply closure_minimal (image_mono ball_subset_closedBall)
        exact OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩
      · rw [← closure_ball z hr.ne']
        exact image_closure_subset_closure_image OnePoint.continuous_coe
    refine ⟨V, OnePoint.isOpen_image_coe.mpr isOpen_ball,
      mem_image_of_mem _ (mem_ball_self hr), ?_, isConnected_sphere_exterior_ball z hr⟩
    rw [hcl]
    rintro p ⟨w, hw, rfl⟩
    exact hball hw
  | infty =>
    have hc := (OnePoint.isOpen_iff_of_mem hx).mp hW
    obtain ⟨R, hR, hbound⟩ := hc.2.isBounded.exists_pos_norm_lt
    let V : Set Sphere := (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ
    let T : Set Sphere := (((↑) : ℂ → Sphere) '' ball (0 : ℂ) R)ᶜ
    have hV : IsOpen V :=
      (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).isOpen_compl
    have hT : IsClosed T := (OnePoint.isOpen_image_coe.mpr isOpen_ball).isClosed_compl
    have hVT : V ⊆ T := compl_subset_compl.mpr (image_mono ball_subset_closedBall)
    have hTW : T ⊆ W := by
      intro p hp
      cases p using OnePoint.rec with
      | infty => exact hx
      | coe z =>
        by_contra hzW
        have hzR := hbound z hzW
        apply hp
        exact mem_image_of_mem _ (by simpa using hzR)
    refine ⟨V, hV, OnePoint.infty_notMem_image_coe,
      (closure_minimal hVT hT).trans hTW, ?_⟩
    change IsConnected (((((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ)ᶜ)
    rw [compl_compl]
    exact (Metric.isConnected_closedBall hR.le).image _ OnePoint.continuous_coe.continuousOn

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CoreGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Keeping the selected physical core away from all terminal disks

A closed planar core extends across infinity to a compact spherical
core. Its quotient image is disjoint from the quotient dust. Thus the
terminal and filling neighborhoods can be chosen away from the entire
retained core. Compact planar tail pieces suffice for the metric step.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- For a core containing a neighborhood of infinity the entire tail
integral can be computed on one compact part of the finite chart. -/
theorem exists_compact_tail_piece
    {Q K : Set (ℝ × ℝ)} (hQ : IsClosed Q) (hK : IsCompact (closure Kᶜ)) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (Q ∩ closedBall 0 R) ∧
      Q \ K = (Q ∩ closedBall 0 R) \ K := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    (hQ.inter isClosed_closedBall) inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨⟨hz.1, ?_⟩, hz.2⟩
    apply ball_subset_closedBall
    simpa only [mem_ball, dist_zero_right] using hbound z (subset_closure hz.2)
  · exact fun hz => ⟨hz.1.1, hz.2⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def sphericalAreaDensity (z : ℂ) : ℝ := 4 / (1 + ‖z‖ ^ 2) ^ 2

theorem sphericalAreaDensity_pos (z : ℂ) : 0 < sphericalAreaDensity z := by
  unfold sphericalAreaDensity
  positivity

theorem continuous_sphericalAreaDensity : Continuous sphericalAreaDensity := by
  unfold sphericalAreaDensity
  exact continuous_const.div ((continuous_const.add (continuous_norm.pow 2)).pow 2)
    (fun z => by positivity)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountableImageIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for the countable image exposed by discarded constant
tags. The estimate charges parameter times, and hence retains multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

def timeIncidence (R : Set (Z × X)) (γ : T → X) (A : Set T) : Set Z :=
  {z | ∃ t ∈ A, (z, γ t) ∈ R}

def timeToll (γ : T → X) (A : Set T) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : A, m (γ t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InterleavedCollarPieces
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interleaving actual retained fragments with their joining arcs preserves
the endpoint matches and adds exactly the two series of costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

def interleavePieces {α : Type*} (a b : ℕ → α) (n : ℕ) : α :=
  if n % 2 = 0 then a (n / 2) else b (n / 2)

@[simp] theorem interleavePieces_even {α : Type*} (a b : ℕ → α) (n : ℕ) :
    interleavePieces a b (2*n) = a n := by simp [interleavePieces]

@[simp] theorem interleavePieces_odd {α : Type*} (a b : ℕ → α) (n : ℕ) :
    interleavePieces a b (2*n+1) = b n := by simp [interleavePieces, Nat.add_div]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

abbrev RoundAmbient := EuclideanSpace ℝ (Fin 3)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialRectangleACL
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barrier pullback is absolutely continuous on almost every
horizontal and vertical segment in each compact physical chart rectangle. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

def closedComplexRectangle (a b c e : ℝ) : Set ℂ :=
  Complex.equivRealProdCLM.symm '' (Icc a b ×ˢ Icc c e)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateEstimates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual coordinate energies on the completed surface

The metric trace estimate controls the sum of the actual scalar
coordinate energies. Exact agreement near the retained core then gives
localized estimates against the original domain, even though the original
coordinates need not extend into the filled holes.
-/

open Set Filter MeasureTheory Finset Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def gradientEnergy (f : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) : ℝ :=
  covectorEnergy ![(planarGradient f z).1, (planarGradient f z).2] (g z)

theorem gradientEnergy_nonneg (f : (ℝ × ℝ) → ℝ) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : ∀ z, (g z).PosDef) (z : ℝ × ℝ) : 0 ≤ gradientEnergy f g z :=
  covectorEnergy_nonneg _ (hg z)

theorem gradientEnergy_spherical (f : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) :
    gradientEnergy f (fun z => sphericalMetricFactor z • 1) z =
      (planarGradient f z).1 ^ 2 + (planarGradient f z).2 ^ 2 := by
  unfold gradientEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

theorem continuousOn_matrixEnergy_local
    {X : Type*} [TopologicalSpace X] {D : Set X}
    {A g : X → PlanarMetric} (hA : ContinuousOn A D) (hg : ContinuousOn g D)
    (hPD : ∀ x ∈ D, (g x).PosDef) :
    ContinuousOn (fun x => matrixEnergy (A x) (g x)) D := by
  have hi : ContinuousOn (fun x => (g x).det⁻¹) D :=
    (continuous_id.matrix_det.comp_continuousOn hg).inv₀
      (fun x hx => (hPD x hx).det_pos.ne')
  have hiMat : ContinuousOn (fun x => (g x).det⁻¹ • (g x).adjugate) D :=
    hi.smul (continuous_id.matrix_adjugate.comp_continuousOn hg)
  have hm : ContinuousOn (fun x => ((g x).det⁻¹ • (g x).adjugate) * A x) D :=
    hiMat.mul hA
  have ht : ContinuousOn (fun x => Matrix.trace (((g x).det⁻¹ • (g x).adjugate) * A x)) D :=
    (continuous_id.matrix_trace : Continuous (Matrix.trace : PlanarMetric → ℝ)).comp_continuousOn hm
  simpa only [matrixEnergy, Matrix.inv_def, Ring.inverse_eq_inv, Pi.mul_def, Function.comp_apply, id_eq] using
    ht.mul (continuous_id.matrix_det.comp_continuousOn hg).sqrt

theorem continuousOn_gradientEnergy
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    ContinuousOn (gradientEnergy f g) Ω := by
  have hx : ContinuousOn (fun z => (planarGradient f z).1) Ω :=
    (hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hy : ContinuousOn (fun z => (planarGradient f z).2) Ω :=
    (hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hv : ContinuousOn (fun z => ![(planarGradient f z).1, (planarGradient f z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have hA : ContinuousOn (fun z => Matrix.vecMulVec
      ![(planarGradient f z).1, (planarGradient f z).2]
      ![(planarGradient f z).1, (planarGradient f z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp hv i).mul (continuousOn_pi.mp hv j)
  change ContinuousOn (fun z => covectorEnergy
    ![(planarGradient f z).1, (planarGradient f z).2] (g z)) Ω
  simpa only [covectorEnergy_eq_matrixEnergy] using
    continuousOn_matrixEnergy_local hA hg.continuousOn (fun z _ => hPD z)

theorem integrableOn_gradientEnergy
    {Ω Q : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (gradientEnergy f g) Q :=
  ((continuousOn_gradientEnergy hΩ hf hg hPD).mono hQΩ).integrableOn_compact hQ


theorem integrable_gradientEnergy_spherical_of_memLp
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (planarGradient f) 2 μ) :
    Integrable (gradientEnergy f (fun z => sphericalMetricFactor z • 1)) μ := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hf
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hf
  have hxx : MemLp (fun z => (planarGradient f z).1 * (planarGradient f z).1) 1 μ := hx.mul hx
  have hyy : MemLp (fun z => (planarGradient f z).2 * (planarGradient f z).2) 1 μ := hy.mul hy
  have hi := (memLp_one_iff_integrable.mp hxx).add (memLp_one_iff_integrable.mp hyy)
  refine hi.congr (Eventually.of_forall fun z => ?_)
  simpa only [pow_two, Pi.add_apply] using (gradientEnergy_spherical f z).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalGradientEnergyNorm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Express the actual spherical Dirichlet energy through its two L²
partial-derivative norms. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem integral_sq_eq_eLpNorm_toReal_sq
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f : A → ℝ} (hf : MemLp f 2 μ) :
    (∫x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    _ = ∫x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (L2.inner_def _ _).symm
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = _ := by rw [Lp.norm_toLp]

theorem spherical_gradient_energy_eq_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (FiniteTransfer.planarGradient f) 2 μ) :
    (∫x, FiniteTransfer.gradientEnergy f (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x ∂μ) =
      (eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ).toReal ^ 2 +
        (eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ).toReal ^ 2 := by
  have hx := hf.fst
  have hy := hf.snd
  calc
    _ = ∫x, (FiniteTransfer.planarGradient f x).1 ^ 2 +
        (FiniteTransfer.planarGradient f x).2 ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (FiniteTransfer.gradientEnergy_spherical f)
    _ = (∫x, (FiniteTransfer.planarGradient f x).1 ^ 2 ∂μ) +
        (∫x, (FiniteTransfer.planarGradient f x).2 ^ 2 ∂μ) :=
      integral_add hx.integrable_sq hy.integrable_sq
    _ = _ := by rw [integral_sq_eq_eLpNorm_toReal_sq hx, integral_sq_eq_eLpNorm_toReal_sq hy]; rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodizedLevels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Periodizing scalar coarea lengths

A scalar coarea estimate controls the integral of the physical length
of real level sets. Integer translates of `[0,1)` partition the real
line, so the sum of these lengths over all lifts of a mod-one level
has the same integral on `[0,1)`. Countable subadditivity then gives
finite physical length for almost every mod-one level.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Equality modulo one is equality up to an integer translation. -/
theorem unitAddCircle_eq_iff_exists_int {a b : ℝ} :
    (a : UnitAddCircle) = (b : UnitAddCircle) ↔ ∃ k : ℤ, a = b + (k : ℝ) := by
  rw [← AddCommGroup.modEq_iff_eq_mod_zmultiples, AddCommGroup.modEq_comm,
    AddCommGroup.modEq_iff_eq_add_zsmul]
  simp only [zsmul_eq_mul, mul_one]

noncomputable def periodizedLevelLength (L : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, L (t + (k : ℝ))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def weightedScalarLevelLength (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in D ∩ {z | f z = t}, q z ∂(μH[1] : Measure ℂ)

noncomputable def weightedCircleLevelLength (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in D ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)},
    q z ∂(μH[1] : Measure ℂ)

/-- Precisely the nonnegative weighted scalar coarea formula. -/
def WeightedScalarCoareaIdentity (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) : Prop :=
  AEMeasurable (weightedScalarLevelLength D f q) volume ∧
    (∫⁻ t, weightedScalarLevelLength D f q t) =
      ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖

/-- Federer (1969), §3.2.12, the nonnegative weighted
coarea formula specialized to a scalar `C¹` function on a planar open
set. This is the identity used by `eq:weighted-level-bound` in §1 of the
Koebe manuscript. -/
def WeightedPlanarScalarCoarea : Prop :=
  ∀ (D : Set ℂ), IsOpen D → ∀ (f : ℂ → ℝ), ContDiffOn ℝ 1 f D →
    ∀ (q : ℂ → ℝ≥0∞), Measurable q → WeightedScalarCoareaIdentity D f q

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleArcToll
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An injective arc pays each boundary weight at most once. The payment
is bounded by the actual atomic measure on any set containing the arc. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def atomicBoundaryMeasure {X : Type*} [MeasurableSpace X] (m : X → ℝ≥0∞) : Measure X :=
  Measure.sum (fun x => m x • Measure.dirac x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ArcNullImage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From simple-arc payment to null trace images

Distinct points of a connected open subset of a locally connected metric
continuum can be joined there by a simple arc. The arc-existence hypothesis
is the local arcwise-connectedness theorem used by Lorimer (1981),
*Locally compact Hjelmslev planes and rings*, proof of Lemma 3.2,
pp. 1002–1003, displayed (*), DOI 10.4153/CJM-1981-077-5.
The null-image criterion derives the measure-theoretic conclusion from
this topological hypothesis and the simple-arc payment inequality.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def HasSimpleArcsInConnectedOpens (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U → IsConnected U →
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y →
      ∃ γ : Path x y, Function.Injective γ ∧ Set.range γ ⊆ U

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LevelPaymentMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure used for the free-trace argument is constructed from
physical weighted length and actual boundary atoms on the prior level set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def levelPaymentMeasure {X Y : Type*} [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (G : Set Y) (H : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : Measure X :=
  (((μH[1] : Measure Y).restrict (G ∩ π ⁻¹' H)).withDensity g).map π +
    (atomicBoundaryMeasure m).restrict H

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HyperspaceIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed continuum incidences in compact level graphs

The compatibility condition quantifies over subcontinua of a finite
level union. The hyperspace of nonempty compact sets is compact, and
connectedness, point membership and containment in a closed level graph
are closed conditions. Projection therefore preserves closedness for
continuum incidences with a fixed positive size witness.
-/

open Set TopologicalSpace Metric

namespace CircleDomainRigidity

def positiveContinuumIncidence {X T : Type*} [PseudoMetricSpace X]
    (R : Set (X × T)) (ε : ℝ) : Set (X × T) :=
  {p | ∃ K : NonemptyCompacts X, IsConnected (K : Set X) ∧ p.1 ∈ (K : Set X) ∧
    (∀ x ∈ (K : Set X), (x, p.2) ∈ R) ∧
      ∃ u ∈ (K : Set X), ∃ v ∈ (K : Set X), ε ≤ dist u v}

def nontrivialFiberComponentRelation {X T : Type*} [TopologicalSpace X]
    (R : Set (X × T)) : Set (X × T) :=
  {p | (connectedComponentIn {x | (x, p.2) ∈ R} p.1).Nontrivial}

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LevelIncidence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite level unions and analytic compatibility failures

Repeated labels are allowed in a finite tuple of levels. Closed level
graphs give a closed union graph; its nondegenerate-component relation
is Borel by the compact hyperspace argument. After restriction to a
Borel set of free points, projection over the point is analytic.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def finiteLevelUnionGraph {X T J Λ : Type*} (R : Λ → Set (X × T))
    (labels : J → Λ) : Set (X × (J → T)) :=
  ⋃ j, (fun p : X × (J → T) => (p.1, p.2 j)) ⁻¹' R (labels j)

def freeComponentFailure {X T J Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ) :
    Set (T × (J → T)) :=
  Prod.snd '' {p : X × (T × (J → T)) |
    p.1 ∈ F ∧ (p.1, p.2.1) ∈ Rnew ∧
      (p.1, p.2.2) ∈ nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)}

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ComponentTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null traces on the nondegenerate components of a level union

Generic level unions have only countably many nondegenerate components.
Consequently a trace that is null on each such component is null on their
union. At free points the new coordinate has one trace value, so the
levels meeting this union form a Haar-null set. This is the fixed-prior-
tuple step in the manuscript's compatibility argument.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def nontrivialComponentLocus (X : Type*) [TopologicalSpace X] : Set X :=
  {x | (connectedComponent x).Nontrivial}

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LusinInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed-measure compatibility for finite level tuples

Lusin's universal-measurability theorem applies to the finite-dimensional
tori used for level choices:
A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
Theorem 21.10, p. 155. Every analytic subset of a standard Borel space is
measurable for the completion of each sigma-finite Borel measure.
Publisher: https://doi.org/10.1007/978-1-4612-4190-4

The compatibility statement uses analyticity of compact incidence sets
and nullity of the free trace image on each nondegenerate component.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

/-- The specialization of Kechris, Theorem 21.10, actually needed for
finite tuples of circle-valued levels. -/
def FiniteTorusAnalyticMeasurability : Prop :=
  ∀ (d : ℕ) (E : Set (UnitAddCircle × (Fin d → UnitAddCircle))),
    AnalyticSet E →
      NullMeasurableSet E (volume.prod (Measure.pi (fun _ : Fin d => volume)))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_BoundaryTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unique traces outside the countable band support

For a bounded real coordinate the interval band is the actual interval
between the lower and upper boundary limits. A zero band budget forces
these limits to agree and gives convergence from the physical domain.
Square summability of the budgets makes all exceptions countable.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

noncomputable def realBoundaryTrace {X : Type*} [TopologicalSpace X]
    (G : Set X) (f : X → ℝ) (x : X) : ℝ := liminf f (𝓝[G] x)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ShrinkingJumpTolls
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-summable dust tolls are upper semicontinuous in every T1
topology. Consequently, the supremum toll on shrinking jump neighborhoods
has limit superior at most the toll at the limiting dust point. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T1Space X]

def neighborhoodTollSup (m : X → ℝ≥0∞) (U : Set X) : ℝ≥0∞ := ⨆ x ∈ U, m x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteSphericalArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicitly defined stereographic spherical area has finite mass.
Only integrability, not the exact value of the total area, is needed here. -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem integrable_sphericalAreaDensity : Integrable sphericalAreaDensity := by
  have h : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖^2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num)
  apply (h.const_mul 4).congr
  filter_upwards with z
  have he : -(4 : ℝ) / 2 = -(2 : ℝ) := by norm_num
  rw [he, Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartDerivativeDecay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global inverse-quadratic derivative bound for the chosen finite sphere chart. -/

open Set Function

noncomputable section

namespace CircleDomainRigidity

def linearSphereChartMap (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) :
    ℂ →L[ℝ] RoundAmbient := (ℝ ∙ v)ᗮ.subtypeL.comp A.toContinuousLinearMap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GateForbiddenSet
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hit-location restrictions are avoidance of the union of forbidden
parts of the prescribed contours. No closedness is needed for this identity. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def gateForbiddenSet (C K : ℕ → Set X) : Set X := ⋃i, C i \ K i

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGateObstacles
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forbidden portions of finitely many prescribed gates form a compact
obstacle, and failure of those gates is exactly a hit of this obstacle. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def finiteGateForbiddenSet (k : ℕ) (C K : ℕ → Set X) : Set X :=
  ⋃i : Fin (k+1), C i.val \ K i.val

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteChainPotential
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-chain infimum used in the compatible barrier construction.
Costs may be infinite. In particular, truncation remains valid on components
unreachable by finite-cost chains. -/

open Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} (R : X → X → ℝ≥0∞ → Prop)

inductive PaidChain : X → X → ℝ≥0∞ → Prop where
  | refl (x : X) : PaidChain x x 0
  | cons {x y z : X} {a b : ℝ≥0∞} :
      R x y a → PaidChain y z b → PaidChain x z (a + b)

def chainDistance (E : Set X) (y : X) : ℝ≥0∞ :=
  ⨅ (x : X) (_ : x ∈ E) (a : ℝ≥0∞) (_ : PaidChain R x y a), a

def chainPotential (E : Set X) (x : X) : ℝ≥0∞ := min 1 (4 * chainDistance R E x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ChainPotentialOscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued oscillation and topological bands of the truncated chain
distance. The closure argument retains all cluster values. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

def realChainPotential (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) : ℝ :=
  (chainPotential R E x).toReal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExclusionTolls
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite auxiliary tolls enforce avoidance without changing the cost
of the original paths. They are used only inside the collar construction. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Y : Type*}

def exclusionToll (S : Set X) (m : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if x ∈ S then ∞ else m x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TwoEndedFragmentGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The middle interval and both families of endpoint fragments are
pairwise disjoint. This is the common budget geometry for two-ended splicing. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev CollarFragmentIndex := Option (ℕ ⊕ ℕ)

def collarFragmentLeft {α : Type*} (a b : ℕ → α) : CollarFragmentIndex → α
  | none => a 0
  | some (.inl j) => a (j+1)
  | some (.inr j) => b j

def collarFragmentRight {α : Type*} (a b : ℕ → α) : CollarFragmentIndex → α
  | none => b 0
  | some (.inl j) => a j
  | some (.inr j) => b (j+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpTollLowerBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive neighborhood width pays the limiting dust junction.
This is the lower bound used in removal of one shrinking jump level. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def fixedWidthJumpToll (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞)
    (τ : ℝ) (V : Set X) : ℝ≥0∞ :=
  max ρ (neighborhoodTollSup m (B ∩ thickening τ V))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCodes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

abbrev BoundedBlockPattern (I : Type*) (n : ℕ) :=
  Σq : Fin (n+1), (Fin q.val → I) × (Fin (q.val+1) → Fin (n+1))

def blockAnchors {X I : Type*} {n : ℕ} (F H : Set X) (O : I → Set X)
    (P : BoundedBlockPattern I n) : Fin (P.1.val+2) → Set X :=
  Fin.cons F (Fin.snoc (fun i => O (P.2.1 i)) H)

@[simp] theorem blockAnchors_zero {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) : blockAnchors F H O P 0 = F := by
  simp [blockAnchors]

@[simp] theorem blockAnchors_last {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) :
    blockAnchors F H O P (Fin.last (P.1.val+1)) = H := by
  simp [blockAnchors]

@[simp] theorem blockAnchors_internal {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) (i : Fin P.1.val) :
    blockAnchors F H O P i.succ.castSucc = O (P.2.1 i) := by
  simp [blockAnchors, Fin.castSucc_succ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependNewBlockJump
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend one new jump and its initial true piece to a grouped chain.
The original first true piece follows the new jump unchanged. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev prependNewJumpPattern {I : Type*} {n : ℕ} (P : BoundedBlockPattern I n) :
    BoundedBlockPattern I (n+1) :=
  ⟨⟨P.1.val, by omega⟩, P.2.1,
    Fin.cons ⟨(P.2.2 0).val+1, by omega⟩ (fun b => ⟨(P.2.2 b.succ).val, by omega⟩)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependOldBlockJump
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend an old jump, creating a new first block with one true piece.
The old disk label and its toll are retained exactly. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev prependOldJumpPattern {I : Type*} {n : ℕ} (P : BoundedBlockPattern I n) (i : I) :
    BoundedBlockPattern I (n+1) :=
  ⟨⟨P.1.val+1, by omega⟩, Fin.cons i P.2.1,
    Fin.cons ⟨0, by omega⟩ (fun b => ⟨(P.2.2 b).val, by omega⟩)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SinglePieceBlock
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

abbrev singlePiecePattern (I : Type*) : BoundedBlockPattern I 0 :=
  ⟨⟨0, by omega⟩, Fin.elim0, fun _ => ⟨0, by omega⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCountBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {X Y I : Type*}
  [MetricSpace X]
  [MetricSpace Y]
  [MeasurableSpace X]
  [MeasurableSpace Y]
  [BorelSpace Y]

def reboundBlockPattern {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) : BoundedBlockPattern I N :=
  ⟨⟨P.1.val, Nat.lt_succ_of_le hold⟩, P.2.1,
    fun b => ⟨(P.2.2 b).val, Nat.lt_succ_of_le (hnew b)⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteJumpSystems
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure FiniteJumpSystem (X : Type*) where
  Label : Type
  finite : Fintype Label
  region : Label → Set X
  toll : Label → ℝ≥0∞

namespace FiniteJumpSystem

variable {X : Type*}

def empty : FiniteJumpSystem X :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim⟩

def append (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) : FiniteJumpSystem X := by
  letI := A.finite
  exact ⟨A.Label ⊕ Fin n, inferInstance, Sum.elim A.region V, Sum.elim A.toll T⟩

end FiniteJumpSystem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FillRegionPotential
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filling the terminal collar with the constant value one preserves the
true-path cost inequality. At dust points away from its boundary, the band
is either unchanged or collapses to the constant value. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

def fillRegionOne (V : Set X) (u : X → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ V then 1 else u x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PublishedMeasureDuality
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure-family duality and probability lifting.

* Ambrosio–Di Marino–Savaré, JEMS 17 (2015), 1817–1853,
  DOI 10.4171/JEMS/546, Theorem 5.1 (p. 1830), Corollary 5.2(b)
  (p. 1833): positive modulus of a Suslin image yields a probability
  plan on finite measures with an L² barycenter. `MeasureImageDuality`
  is the p = 2 consequence for a Borel image of a standard Borel space.
* Bogachev, *Measure Theory*, vol. II (2007), Theorem 6.9.1 gives a
  measure-dependent measurable selector. `MeasurePlanLifting` states
  its probability-lifting consequence, used in the proof of ADMS,
  Theorem 7.2, p. 1839.

The two propositions separate measure-space duality from probability
lifting; neither assumes a compact-support conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
  [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- Pointwise admissibility, including infinite values on reference-null sets. -/
def measureFamilyModulus (σ : Measure Z) (K : A → FiniteMeasure Z) : ℝ≥0∞ :=
  ⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
    (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)), ∫⁻ z, h z ^ 2 ∂σ

/-- The measure-image conclusion of ADMS Theorem 5.1 and Corollary 5.2(b). -/
def MeasureImageDuality (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] : Prop :=
  ∀ (K : A → FiniteMeasure Z), Measurable K →
  ∀ (σ : Measure Z), IsFiniteMeasure σ →
  ∀ (c : ℝ≥0), 0 < c → (c : ℝ≥0∞) < measureFamilyModulus A Z σ K →
  ∃ (η : ProbabilityMeasure (FiniteMeasure Z)) (q : Z → ℝ≥0∞),
    Measurable q ∧
    (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ range K) ∧
    (∀ E, MeasurableSet E →
      (∫⁻ v, (v : Measure Z) E ∂(η : Measure (FiniteMeasure Z))) = σ.withDensity q E) ∧
    (∫⁻ z, q z ^ 2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹

/-- The probability-lifting consequence of the cited measurable selector. -/
def MeasurePlanLifting (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] : Prop :=
  ∀ (K : A → FiniteMeasure Z) (hK : Measurable K),
  ∀ (η : ProbabilityMeasure (FiniteMeasure Z)),
    (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ range K) →
    ∃ P : ProbabilityMeasure A, P.map (f := K) hK.aemeasurable = η

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExtendedAtomicToll
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a prescribed countable atomic metric by zero on the quotient.
Both its square norm and the full preterminal visit payment are preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def extendAtomicToll {D X : Type*} (p : D → X) (m : D → ℝ≥0∞) : X → ℝ≥0∞ :=
  Function.extend p m 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierTrialMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of a small actual compatible barrier gives a uniform lower
bound on every admissible coding metric. The excluded tuples and positive
perturbations are constructed from that metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

def barrierConstructionConstant (C : ℝ) : ℝ≥0∞ :=
  max (2 * ENNReal.ofReal (4 * (9 * C))) 4

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleLifts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real lifts of circle coordinates near filling disks

The quotient `ℝ → ℝ/ℤ` is a covering map in Mathlib. Its lifting theorem
therefore gives actual continuous real branches on simply connected open
sets. Smoothness is expressed in the ordinary real quotient charts
`AddCircle.equivIco`; a continuous lift is locally one of these charts plus
an integer, so the lift is smooth. No external lifting axiom is used.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Smoothness in every real quotient chart whose cut point is absent.
This uses the actual `ℝ/ℤ` charts, without requiring a separate manifold
instance for `AddCircle`. -/
def SmoothCircleOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → UnitAddCircle) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ a : ℝ, f x ≠ (a : UnitAddCircle) →
    ContDiffAt ℝ ∞ (fun y => (AddCircle.equivIco (1 : ℝ) a (f y) : ℝ)) x

/-- Ordinary smooth real coordinates project to smooth circle
coordinates in the explicit quotient-chart definition. -/
theorem smoothCircleOn_coe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    SmoothCircleOn (fun x => (u x : UnitAddCircle)) U := by
  intro x hx a ha
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] := AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hux.continuousAt
  have heq : (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ))
      =ᶠ[𝓝 x] (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [hconst] with y hy
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hy
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hy, zsmul_eq_mul, mul_one]
  exact (hux.sub contDiffAt_const).congr_of_eventuallyEq heq

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LiftDifferentials
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of differentials from the chosen real lift

Two continuous real lifts of one circle map differ locally by a fixed
integer. Their differentials, and those of the actual reciprocal-grid
cutoff modifications, therefore agree. These are local consequences of
the real quotient, with no additional published input.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem eventually_lifts_differ_by_integer
    {X : Type*} [TopologicalSpace X] {u v : X → ℝ} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle)) :
    ∃ m : ℤ, ∀ᶠ y in 𝓝 x, u y = v y + (m : ℝ) := by
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (u x) (v x)).mp hproj.self_of_nhds
  have hnear : ∀ᶠ y in 𝓝 x, u y - v y ∈ ball (u x - v x) 1 :=
    (hu.sub hv).eventually (ball_mem_nhds _ zero_lt_one)
  refine ⟨m, ?_⟩
  filter_upwards [hproj, hnear] with y hy hdist
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 (u y) (v y)).mp hy
  have hmx : u x - v x = (m : ℝ) := by linarith [hm]
  have hny : u y - v y = (n : ℝ) := by linarith [hn]
  have habs : |(n : ℝ) - (m : ℝ)| < 1 := by
    simpa only [mem_ball, Real.dist_eq, hmx, hny] using hdist
  have hlo : (-1 : ℤ) < n - m := by exact_mod_cast (abs_lt.mp habs).1
  have hhi : n - m < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  have hnm : n = m := by omega
  subst n
  simpa only [mul_one] using hn

theorem fderiv_lifts_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {x : E} (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle)) :
    fderiv ℝ u x = fderiv ℝ v x := by
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hu hv hproj
  have heq : u =ᶠ[𝓝 x] fun y => v y + (m : ℝ) := hm
  rw [heq.fderiv_eq (𝕜 := ℝ), fderiv_add_const]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleDifferential
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic differentials and cutoff modifications of circle coordinates

The differential is computed in a genuine real quotient chart. Local
integer transition functions make it independent of the chosen lift.
The cutoff staircase descends to the circle and is smooth in the same
charts; no global real lift or extra topological input is required.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def circleRepresentative (t : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 t

def circleBranch {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) : ℝ :=
  AddCircle.equivIco 1 a (f x)

@[simp] theorem coe_circleRepresentative (t : UnitAddCircle) :
    (circleRepresentative t : UnitAddCircle) = t := AddCircle.coe_equivIco

@[simp] theorem coe_circleBranch {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) :
    (circleBranch f a x : UnitAddCircle) = f x := AddCircle.coe_equivIco

def circleCut {X : Type*} (f : X → UnitAddCircle) (x : X) : ℝ :=
  circleRepresentative (f x) - 1 / 2

theorem circleCut_ne {X : Type*} (f : X → UnitAddCircle) (x : X) :
    f x ≠ (circleCut f x : UnitAddCircle) := by
  intro heq
  let r := circleRepresentative (f x)
  let a := circleCut f x
  have hr : r ∈ Ico a (a + 1) := by dsimp [r, a, circleCut]; constructor <;> linarith
  have ha : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
  have h : (r : UnitAddCircle) = (a : UnitAddCircle) :=
    (coe_circleRepresentative (f x)).trans heq
  have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hr ha).mp h
  dsimp [r, a, circleCut] at h'
  linarith

theorem smoothCircleAt_of_local_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    ∀ a : ℝ, f x ≠ (a : UnitAddCircle) → ContDiffAt ℝ ∞ (circleBranch f a) x := by
  intro a ha
  have ha' : (u x : UnitAddCircle) ≠ (a : UnitAddCircle) := by
    have hx : (u x : UnitAddCircle) = f x := heq.self_of_nhds
    exact fun h => ha (hx.symm.trans h)
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] :=
    AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha'
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hu.continuousAt
  have hloc : circleBranch f a =ᶠ[𝓝 x]
      (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [heq, hconst] with y hy hc
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hc
    dsimp only [circleBranch]
    rw [← hy]
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hc, zsmul_eq_mul, mul_one]
  exact (hu.sub contDiffAt_const).congr_of_eventuallyEq hloc

theorem smoothCircleOn_iff_local_lifts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} :
    SmoothCircleOn f U ↔ ∀ x ∈ U, ∃ u : E → ℝ,
      ContDiffAt ℝ ∞ u x ∧ (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f := by
  constructor
  · intro hf x hx
    exact ⟨circleBranch f (circleCut f x), hf x hx _ (circleCut_ne f x),
      Filter.Eventually.of_forall (coe_circleBranch f _)⟩
  · intro hf x hx
    obtain ⟨u, hu, heq⟩ := hf x hx
    exact smoothCircleAt_of_local_lift hu heq

theorem SmoothCircleOn.continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U) : ContinuousOn f U := by
  intro x hx
  obtain ⟨u, hu, heq⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  exact (((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hu.continuousAt).congr
    heq).continuousWithinAt

def circleFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → UnitAddCircle) (x : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (circleBranch f (circleCut f x)) x

/-- The intrinsic differential equals that of every continuous local
lift, including lifts defined only near the point of differentiation. -/
theorem circleFDeriv_eq_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {x : E}
    (hf : ContinuousAt f x) (hu : ContinuousAt u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    circleFDeriv f x = fderiv ℝ u x := by
  have hc : ContinuousAt (circleBranch f (circleCut f x)) x :=
    continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ (circleCut_ne f x)).comp hf)
  exact fderiv_lifts_eq hc hu (by
    filter_upwards [heq] with y hy
    exact (coe_circleBranch f _ y).trans hy.symm)

def circleGradient (f : (ℝ × ℝ) → UnitAddCircle) (x : ℝ × ℝ) : ℝ × ℝ :=
  (circleFDeriv f x (1, 0), circleFDeriv f x (0, 1))

/-- A unit-additive real modification descends pointwise to the circle. -/
def circleCutoff {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ) (P : ℝ → ℝ)
    (x : X) : UnitAddCircle :=
  (cutoffStaircase (fun y => circleRepresentative (f y)) χ P x : UnitAddCircle)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleCovectors
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleFDeriv_eventuallyEq_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hu : ContDiffOn ℝ ∞ u U)
    (hproj : ∀ y ∈ U, (u y : UnitAddCircle) = f y) {x : E} (hx : x ∈ U) :
    circleFDeriv f =ᶠ[𝓝 x] fderiv ℝ u := by
  filter_upwards [hU.mem_nhds hx] with y hy
  apply circleFDeriv_eq_lift (hf.continuousAt (hU.mem_nhds hy))
    (hu.continuousOn.continuousAt (hU.mem_nhds hy))
  filter_upwards [hU.mem_nhds hy] with z hz
  exact hproj z hz

/-- On a local real branch the intrinsic covector field equals the
ordinary gradient on a whole neighborhood, not only at its center. -/
theorem circleGradient_eventuallyEq_lift
    {f : (ℝ × ℝ) → UnitAddCircle} {u : (ℝ × ℝ) → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hu : ContDiffOn ℝ ∞ u U)
    (hproj : ∀ y ∈ U, (u y : UnitAddCircle) = f y) {x : ℝ × ℝ} (hx : x ∈ U) :
    circleGradient f =ᶠ[𝓝 x] planarGradient u := by
  filter_upwards [circleFDeriv_eventuallyEq_lift hU hf hu hproj hx] with y hy
  simp only [circleGradient, hy, planarGradient]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CovectorMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric selection for local covectors

Periodic coordinates need not have a global scalar potential. The Gram
argument applies to their smooth covector fields, retaining the spherical
metric near a closed core and near infinity, and realizing masked fields
by smooth extensions.
-/

open Set Filter MeasureTheory Finset Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def fieldEnergy (v : (ℝ × ℝ) → ℝ × ℝ) (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) : ℝ :=
  covectorEnergy ![(v z).1, (v z).2] (g z)

def fieldGram (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (z : ℝ × ℝ) : PlanarMetric :=
  gramTensor (fun i => (v i z).1) (fun i => (v i z).2) n

def fieldWedges (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  covectorWedges (fun i => (v i z).1) (fun i => (v i z).2) n

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleMetric
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One metric for masked periodic coordinates

The actual intrinsic differentials of the circle coordinates are used
throughout. Mask boundaries lie inside the retained core, so the masked
covectors extend smoothly across the portion on which the metric changes.
Their pairwise wedge budget controls the sum of energies on the masks.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def natCovectorFamily {n : ℕ} (v : Fin n → (ℝ × ℝ) → ℝ × ℝ) :
    ℕ → (ℝ × ℝ) → ℝ × ℝ := fun i => if hi : i < n then v ⟨i, hi⟩ else fun _ => 0

def maskedCircleWedges {n : ℕ} (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) : ℝ :=
  ∑ p : UpperPairs n, |planarWedge
    ((M (upperPair p).1).indicator (circleGradient (f (upperPair p).1)) z)
    ((M (upperPair p).2).indicator (circleGradient (f (upperPair p).2)) z)|

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CircleWedgeCost
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual random wedge cost for circle coordinates

The random covectors are exactly the intrinsic differentials of the
modified circle maps. Fixed-width integrability follows from the
original L² differentials and the cutoff, just as in the real case.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def circleCutoffFamily {n : ℕ} (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (δ : ℝ) (θ : Fin n → ℝ) :
    Fin n → (ℝ × ℝ) → UnitAddCircle :=
  fun i => circleCutoff (f i) χ (shiftedStaircase (reciprocalGridStep N) δ (θ i))

def circleWedges {n : ℕ} (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) : ℝ :=
  fieldWedges (natCovectorFamily (fun i => circleGradient (f i))) n z

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ComponentBarriers
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From analytic barriers to circle-domain component control

The complementary components are the components of the sphere's closed
complement. Components admitting vanishing absolutely continuous barriers
are points. If all remaining components are round disks, the domain is
a circle domain.
-/

open Set Topology
open scoped OnePoint

namespace CircleDomainRigidity

/-- The finite-coordinate part of a sphere set. -/
def planarPart (K : Set Sphere) : Set ℂ := (fun z : ℂ => (z : Sphere)) ⁻¹' K

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ConfigurationMeasures
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite atomic measures associated to weighted configurations, and
their probability barycenters. Integrals against the barycenter are exactly
the expected weighted configuration integrals. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {n : ℕ} {r : ℝ}

def configurationMeasure (p : HitConfiguration X n r) : Measure X :=
  ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) • Measure.dirac (p.val.1 i)

theorem measurable_configurationMeasure :
    Measurable (configurationMeasure (X := X) (n := n) (r := r)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [configurationMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · exact (by fun_prop : Continuous (fun p : HitConfiguration X n r => (p.val.2 i : ℝ))).measurable.ennreal_ofReal
  · exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (by fun_prop : Continuous (fun p : HitConfiguration X n r => p.val.1 i)).measurable)

omit [SecondCountableTopology X] [BorelSpace X] in
theorem lintegral_configurationMeasure (p : HitConfiguration X n r)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂configurationMeasure p =
      ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * f (p.val.1 i) := by
  rw [configurationMeasure, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

omit [SecondCountableTopology X] [BorelSpace X] in
theorem configurationMeasure_mass_le (p : HitConfiguration X n r) :
    configurationMeasure p univ ≤ n := by
  have h := lintegral_configurationMeasure p measurable_const
    (f := fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, mul_one] at h
  rw [h]
  calc
    ∑ i : Fin n, ENNReal.ofReal (p.val.2 i : ℝ) ≤ ∑ _i : Fin n, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun i _ => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (p.val.2 i).property.2
    _ = n := by simp

def meanConfigurationMeasure (P : ProbabilityMeasure (HitConfiguration X n r)) : Measure X :=
  (P : Measure (HitConfiguration X n r)).bind configurationMeasure

theorem lintegral_meanConfigurationMeasure (P : ProbabilityMeasure (HitConfiguration X n r))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂meanConfigurationMeasure P =
      ∫⁻ p : HitConfiguration X n r, ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * f (p.val.1 i)
        ∂(P : Measure (HitConfiguration X n r)) := by
  rw [meanConfigurationMeasure, Measure.lintegral_bind
    measurable_configurationMeasure.aemeasurable hf.aemeasurable]
  exact lintegral_congr fun p => lintegral_configurationMeasure p hf

instance instIsFiniteMeasureMeanConfigurationMeasure (P : ProbabilityMeasure (HitConfiguration X n r)) :
    IsFiniteMeasure (meanConfigurationMeasure P) := by
  constructor
  rw [meanConfigurationMeasure, Measure.bind_apply MeasurableSet.univ
    (measurable_configurationMeasure (X := X) (n := n) (r := r)).aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono fun p => configurationMeasure_mass_le p)
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FusionSmallSets
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CircleDomainRigidity

theorem exists_finite_atomless_dominating {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    [∀ n, NullSingletonClass (μ n)] :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ NullSingletonClass ν ∧ ∀ n, μ n ≪ ν := by
  obtain ⟨ν, hν, hsumν, hνsum⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (Measure.sum μ)
  refine ⟨ν, hν, ⟨fun x => hνsum ?_⟩, fun n =>
    (Measure.absolutelyContinuous_sum_right n (Measure.AbsolutelyContinuous.refl _)).trans hsumν⟩
  simp [Measure.sum_apply_of_countable]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AtomicHitTests
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace CircleDomainRigidity

variable {X : Type*}
  [MetricSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace X]
  [BorelSpace X]

def positiveAtoms (ν : Measure X) : Set X := {x | 0 < ν {x}}

def HasAtomicSquareBound (ν : Measure X) : Prop :=
  ∀ F : Finset X, ∑ x ∈ F, (ν {x}).toReal ^ 2 ≤ 1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConfigurationAtomicNorm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean measure of separated unit-square-norm configurations has atomic
square norm at most one. Separation makes the point assignment injective;
Cauchy--Schwarz then passes the finite-dimensional bound through averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_sq_fibers_le {I X : Type*} [Fintype I] [DecidableEq X]
    (p : I → X) (hp : Injective p) (w : I → ℝ) (F : Finset X) :
    ∑ x ∈ F, (∑ i, if p i = x then w i else 0) ^ 2 ≤ ∑ i, w i ^ 2 := by
  classical
  have he (x : X) : (∑ i, if p i = x then w i else 0) ^ 2 =
      ∑ i, if p i = x then w i ^ 2 else 0 := by
    by_cases hx : ∃ i, p i = x
    · obtain ⟨i, hi⟩ := hx
      have heq (j : I) : p j = x ↔ j = i := by
        constructor
        · intro h; exact hp (h.trans hi.symm)
        · rintro rfl; exact hi
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    · have hn (i : I) : p i ≠ x := fun hi => hx ⟨i, hi⟩
      simp [hn]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_ite_eq]
  split
  · exact le_rfl
  · exact sq_nonneg _

theorem sum_sq_integrals_le_one {I T : Type*} [Fintype I] [MeasurableSpace T]
    (P : ProbabilityMeasure T) (h : I → T → ℝ)
    (hi : ∀ i, Integrable (h i) (P : Measure T))
    (hbound : ∀ t, ∑ i, h i t ^ 2 ≤ 1) :
    ∑ i, (∫ t, h i t ∂(P : Measure T)) ^ 2 ≤ 1 := by
  let v : I → ℝ := fun i => ∫ t, h i t ∂(P : Measure T)
  let S := ∑ i, v i ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb (t : T) : ∑ i, v i * h i t ≤ Real.sqrt S := by
    have hh : Real.sqrt (∑ i, h i t ^ 2) ≤ 1 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hbound t⟩
    exact (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v (fun i => h i t)).trans
      (by simpa only [S, mul_one] using mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg S))
  have hsi : Integrable (fun t => ∑ i, v i * h i t) (P : Measure T) :=
    integrable_finsetSum _ fun i _ => (hi i).const_mul (v i)
  have he : ∫ t, ∑ i, v i * h i t ∂(P : Measure T) = S := by
    rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (v i))]
    simp only [integral_const_mul, S, v, sq]
  have hle : S ≤ Real.sqrt S := by
    calc
      S = ∫ t, ∑ i, v i * h i t ∂(P : Measure T) := he.symm
      _ ≤ Real.sqrt S := by
        simpa only [integral_const, probReal_univ, one_smul] using
          integral_mono_ae hsi (integrable_const (Real.sqrt S)) (Eventually.of_forall hb)
  have hsq := Real.sq_sqrt hS0
  change S ≤ 1
  nlinarith [Real.sqrt_nonneg S]

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {n : ℕ} {r : ℝ}

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem HitConfiguration.points_injective (hr : 0 < r) (p : HitConfiguration X n r) :
    Injective p.val.1 := by
  intro i j hij
  by_contra hne
  have h := p.property.2 i j hne
  rw [hij, dist_self] at h
  exact (not_le.mpr hr) h

theorem configurationMeasure_atom_real [DecidableEq X] (p : HitConfiguration X n r) (x : X) :
    (configurationMeasure p {x}).toReal =
      ∑ i, if p.val.1 i = x then (p.val.2 i : ℝ) else 0 := by
  classical
  simp only [configurationMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    mem_singleton_iff, Pi.one_apply]
  rw [ENNReal.toReal_sum (fun i _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [ENNReal.toReal_ofReal (p.val.2 i).property.1]

theorem configurationMeasure_hasAtomicSquareBound (hr : 0 < r)
    (p : HitConfiguration X n r) : HasAtomicSquareBound (configurationMeasure p) := by
  classical
  intro F
  simp_rw [configurationMeasure_atom_real]
  exact (sum_sq_fibers_le p.val.1 (HitConfiguration.points_injective hr p) (fun i => (p.val.2 i : ℝ)) F).trans
    p.property.1

instance instIsFiniteMeasureConfigurationMeasure (p : HitConfiguration X n r) : IsFiniteMeasure (configurationMeasure p) :=
  ⟨lt_of_le_of_lt (configurationMeasure_mass_le p) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)⟩

theorem meanConfigurationMeasure_atom_real
    (P : ProbabilityMeasure (HitConfiguration X n r)) (x : X) :
    (meanConfigurationMeasure P {x}).toReal =
      ∫ p, (configurationMeasure p {x}).toReal ∂(P : Measure (HitConfiguration X n r)) := by
  rw [meanConfigurationMeasure, Measure.bind_apply (measurableSet_singleton x)
    measurable_configurationMeasure.aemeasurable]
  exact (integral_toReal
    ((Measure.measurable_coe (measurableSet_singleton x)).comp
      measurable_configurationMeasure).aemeasurable
    (Eventually.of_forall fun p => measure_lt_top (configurationMeasure p) {x})).symm

theorem integrable_configuration_atom
    (P : ProbabilityMeasure (HitConfiguration X n r)) (x : X) :
    Integrable (fun p => (configurationMeasure p {x}).toReal)
      (P : Measure (HitConfiguration X n r)) := by
  apply Integrable.of_bound
    (((Measure.measurable_coe (measurableSet_singleton x)).comp
      measurable_configurationMeasure).ennreal_toReal.aestronglyMeasurable) n
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  change (configurationMeasure p {x}).toReal ≤ (n : ℝ)
  have hle : configurationMeasure p {x} ≤ n :=
    (measure_mono (subset_univ _)).trans (configurationMeasure_mass_le p)
  simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono (by simp) hle

theorem meanConfigurationMeasure_hasAtomicSquareBound (hr : 0 < r)
    (P : ProbabilityMeasure (HitConfiguration X n r)) :
    HasAtomicSquareBound (meanConfigurationMeasure P) := by
  classical
  intro F
  let a : F → HitConfiguration X n r → ℝ := fun x p => (configurationMeasure p {x.val}).toReal
  have hi (x : F) : Integrable (a x) (P : Measure (HitConfiguration X n r)) :=
    integrable_configuration_atom P x.val
  have hb (p : HitConfiguration X n r) : ∑ x : F, a x p ^ 2 ≤ 1 := by
    exact (Finset.sum_coe_sort F (fun x : X => (configurationMeasure p {x}).toReal ^ 2)).le.trans
      (configurationMeasure_hasAtomicSquareBound hr p F)
  have h := sum_sq_integrals_le_one P a hi hb
  simp_rw [meanConfigurationMeasure_atom_real]
  exact (Finset.sum_coe_sort F (fun x : X =>
    (∫ p, (configurationMeasure p {x}).toReal ∂(P : Measure (HitConfiguration X n r))) ^ 2)).symm.le.trans h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_IntervalTraceExtension
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Endpoint traces from finite variation on an open interval

A differentiable function on an open bounded interval whose derivative
is integrable has an absolutely continuous extension to the closed
interval. This supplies the endpoint traces at the round holes in the
parallel-line argument, without assuming boundary continuity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem exists_absolutelyContinuous_extension_of_integrable_derivative
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hi : IntervalIntegrable d volume a b) :
    ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ EqOn g f (Ioo a b) ∧
      Tendsto f (𝓝[Ioo a b] a) (𝓝 (g a)) ∧
      Tendsto f (𝓝[Ioo a b] b) (𝓝 (g b)) := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hcu : c ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hc
  let g : ℝ → ℝ := fun x => f c + ∫ t in c..x, d t
  have hg : AbsolutelyContinuousOnInterval g a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f c) a b :=
      (LipschitzWith.const (f c)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hconst.add (hi.absolutelyContinuousOnInterval_intervalIntegral hcu)
  have heq : EqOn g f (Ioo a b) := by
    intro x hx
    have hcx : uIcc c x ⊆ Ioo a b := by
      intro y hy
      rcases le_total c x with h | h
      · rw [uIcc_of_le h] at hy
        exact ⟨hc.1.trans_le hy.1, hy.2.trans_lt hx.2⟩
      · rw [uIcc_of_ge h] at hy
        exact ⟨hx.1.trans_le hy.1, hy.2.trans_lt hc.2⟩
    have hint : IntervalIntegrable d volume c x :=
      hi.mono_set (uIcc_subset_uIcc hcu (by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hx))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hd y (hcx hy)) hint
    dsimp only [g]
    rw [hFTC]
    ring
  have hgc : ContinuousOn g (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hg.continuousOn
  refine ⟨g, hg, heq, ?_, ?_⟩
  · apply ((hgc a ⟨le_rfl, hab.le⟩).mono
      Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx
  · apply ((hgc b ⟨hab.le, le_rfl⟩).mono
      Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLineGaps
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual gaps of finitely many disjoint line intervals

Sorting the closed holes supplies the open intervals on which variation
is paid. Every gap is nonempty, the gaps are disjoint, and no point of a
gap belongs to a hole. Point holes are allowed.
-/

open Set Function

namespace CircleDomainRigidity

noncomputable def gapsAfterHoles {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin (n + 1)) : ℝ × ℝ :=
  (Fin.cons (α := fun _ => ℝ) a (fun j => (H j).2) i, Fin.snoc (α := fun _ => ℝ) (fun j => (H j).1) b i)

@[simp] theorem gapsAfterHoles_zero_fst {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) :
    (gapsAfterHoles a b H 0).1 = a := by simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_last_snd {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) :
    (gapsAfterHoles a b H (Fin.last n)).2 = b := by simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_succ_fst {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin n) : (gapsAfterHoles a b H i.succ).1 = (H i).2 := by
  simp [gapsAfterHoles]

@[simp] theorem gapsAfterHoles_castSucc_snd {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (i : Fin n) : (gapsAfterHoles a b H i.castSucc).2 = (H i).1 := by
  simp [gapsAfterHoles]

theorem gapsAfterHoles_strict {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1) (i : Fin (n + 1)) :
    (gapsAfterHoles a b H i).1 < (gapsAfterHoles a b H i).2 := by
  cases n with
  | zero => fin_cases i; simpa [gapsAfterHoles, Fin.snoc] using hab
  | succ n =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change a < Fin.snoc (α := fun _ => ℝ) (fun j => (H j).1) b (0 : Fin (n + 2))
      simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using (hinside 0).1
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [gapsAfterHoles_succ_fst, Fin.succ_last, gapsAfterHoles_last_snd]
        exact (hinside (Fin.last n)).2.2
      · rw [gapsAfterHoles_succ_fst, ← Fin.castSucc_succ, gapsAfterHoles_castSucc_snd]
        exact hsep j.castSucc j.succ (by simp)

theorem gapsAfterHoles_avoid {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hfirst : Monotone (fun i => (H i).1)) (hlast : Monotone (fun i => (H i).2))
    (i : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) :
    ∀ j, x ∉ Icc (H j).1 (H j).2 := by
  intro j hj
  by_cases hji : j.val < i.val
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (show i ≠ 0 by intro he; simp [he] at hji)
    rw [gapsAfterHoles_succ_fst] at hx
    have hjk : j ≤ k := by
      simpa only [Fin.le_iff_val_le_val] using Nat.le_of_lt_succ hji
    exact (not_lt_of_ge (hj.2.trans (hlast hjk))) hx.1
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
      (show i ≠ Fin.last n by intro he; subst i; exact hji j.isLt)
    rw [gapsAfterHoles_castSucc_snd] at hx
    have hkj : k ≤ j := by
      exact Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hji)
    exact (not_lt_of_ge ((hfirst hkj).trans hj.1)) hx.2

theorem interval_right_lt_left_of_disjoint {z w : ℝ × ℝ}
    (hw : w.1 ≤ w.2)
    (hfirst : z.1 ≤ w.1) (hdisj : Disjoint (Icc z.1 z.2) (Icc w.1 w.2)) :
    z.2 < w.1 := by
  by_contra h
  exact (disjoint_left.mp hdisj ⟨hfirst, le_of_not_gt h⟩ ⟨le_rfl, hw⟩)

theorem sorted_holes_separated (F : Finset (ℝ × ℝ))
    (hvalid : ∀ z ∈ F, z.1 ≤ z.2)
    (hdisj : (↑F : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2)) :
    ∀ i j : Fin F.card, i < j →
      (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl i).2 <
        (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl j).1 := by
  intro i j hij
  let H := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hi := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have hj := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl j
  exact interval_right_lt_left_of_disjoint (hvalid _ hj)
    (Prod.Lex.le_iff'.mp (H.monotone hij.le)).1
    (hdisj hi hj (H.injective.ne hij.ne))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SourceArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The source-area inequality for circle domains

The source region and the interiors of its complementary disks are
disjoint subsets of one outer disk. Countable additivity gives the
source-area inequality used in Section 6 of the rigidity manuscript.
No regularity of the remaining point components is needed.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Planar ball area, expressed as an ordinary real number. -/
theorem real_volume_ball (center : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball center r)).toReal = Real.pi * r ^ 2 := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ParallelDiskTolls
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact costs of round holes on parallel lines

The horizontal lines meeting a closed round disk form an interval of
length twice its radius. Integrating finitely many hole tolls therefore
gives exactly the radius-weighted sum. Disjointness and a common containing
disk bound this sum by the square norm of the oscillation tolls.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem horizontal_line_meets_closedBall (c : ℂ) {r y : ℝ} :
    (∃ x : ℝ, (⟨x, y⟩ : ℂ) ∈ closedBall c r) ↔ y ∈ Icc (c.im - r) (c.im + r) := by
  constructor
  · rintro ⟨x, hx⟩
    have hb : |y - c.im| ≤ r := by
      have hx' : ‖(⟨x, y⟩ : ℂ) - c‖ ≤ r := by
        simpa only [mem_closedBall, dist_eq_norm] using hx
      exact (Complex.abs_im_le_norm ((⟨x, y⟩ : ℂ) - c)).trans hx'
    exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
  · intro hy
    refine ⟨c.re, ?_⟩
    have heq : dist (⟨c.re, y⟩ : ℂ) c = |y - c.im| := by
      rw [dist_eq_norm, ← Complex.abs_im_eq_norm.mpr (by simp)]
      rfl
    rw [mem_closedBall, heq]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem integral_parallel_disk_tolls
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (∫ y : ℝ, ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) =
      ∑ i, 2 * r i * A i := by
  have hi (i : I) : Integrable
      ((Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const _ measurableSet_Icc]
  simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [hr i])]
  ring

theorem real_volume_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (closedBall c r)).toReal = Real.pi * r ^ 2 := by
  simpa only [Complex.volume_closedBall, Complex.volume_ball] using real_volume_ball c hr

theorem sum_radii_sq_le_of_disjoint_closed_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L) :
    ∑ i, r i ^ 2 ≤ L ^ 2 := by
  have hm : (∑' i, volume (closedBall (c i) (r i))) ≤ volume (closedBall (0 : ℂ) L) := by
    rw [← measure_iUnion hdisj (fun _ => measurableSet_closedBall)]
    exact measure_mono (iUnion_subset hsub)
  have hreal := ENNReal.toReal_mono measure_closedBall_lt_top.ne hm
  rw [ENNReal.tsum_toReal_eq (fun _ => measure_closedBall_lt_top.ne), tsum_fintype] at hreal
  simp_rw [real_volume_closedBall _ (hr _)] at hreal
  rw [real_volume_closedBall 0 hL, ← Finset.mul_sum] at hreal
  exact (mul_le_mul_iff_right₀ Real.pi_pos).mp hreal

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskSlices
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Horizontal chords of round complementary disks

The exact real interval cut out by a round disk is used to enumerate the
holes of a chosen crossing segment. The formula includes tangent and
radius-zero disks.
-/

open Set Function Metric

namespace CircleDomainRigidity

noncomputable def horizontalChord (c : ℂ) (r y : ℝ) : ℝ × ℝ :=
  (c.re - Real.sqrt (r ^ 2 - (y - c.im) ^ 2),
   c.re + Real.sqrt (r ^ 2 - (y - c.im) ^ 2))

theorem horizontalChord_nonneg (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im - r) (c.im + r)) :
    0 ≤ r ^ 2 - (y - c.im) ^ 2 := by
  have h : |y - c.im| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hs := (sq_le_sq₀ (abs_nonneg (y - c.im)) hr).mpr h
  nlinarith [sq_abs (y - c.im)]

theorem horizontalChord_valid (c : ℂ) (r y : ℝ) :
    (horizontalChord c r y).1 ≤ (horizontalChord c r y).2 := by
  dsimp [horizontalChord]
  linarith [Real.sqrt_nonneg (r ^ 2 - (y - c.im) ^ 2)]

theorem mem_closedBall_iff_mem_horizontalChord (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im - r) (c.im + r)) :
    (⟨x, y⟩ : ℂ) ∈ closedBall c r ↔
      x ∈ Icc (horizontalChord c r y).1 (horizontalChord c r y).2 := by
  have hsq := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  have hsqrt := Real.sqrt_nonneg (r ^ 2 - (y - c.im) ^ 2)
  have hn := Complex.sq_norm ((⟨x, y⟩ : ℂ) - c)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hn
  dsimp only [horizontalChord, Prod.fst, Prod.snd]
  rw [mem_closedBall, dist_eq_norm]
  constructor
  · intro h
    have hnorm := norm_nonneg ((⟨x, y⟩ : ℂ) - c)
    have hbound : (x - c.re) ^ 2 ≤ r ^ 2 - (y - c.im) ^ 2 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (x - c.re - Real.sqrt (r ^ 2 - (y - c.im) ^ 2)),
      sq_nonneg (x - c.re + Real.sqrt (r ^ 2 - (y - c.im) ^ 2))]
  · rintro ⟨hx1, hx2⟩
    have hbound : (x - c.re) ^ 2 ≤ r ^ 2 - (y - c.im) ^ 2 := by nlinarith
    nlinarith [norm_nonneg ((⟨x, y⟩ : ℂ) - c)]

theorem horizontalChord_disjoint {c d : ℂ} {r s y : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hyc : y ∈ Icc (c.im - r) (c.im + r))
    (hyd : y ∈ Icc (d.im - s) (d.im + s))
    (hdisj : Disjoint (closedBall c r) (closedBall d s)) :
    Disjoint (Icc (horizontalChord c r y).1 (horizontalChord c r y).2)
      (Icc (horizontalChord d s y).1 (horizontalChord d s y).2) := by
  apply disjoint_left.mpr
  intro x hxc hxd
  exact disjoint_left.mp hdisj
    ((mem_closedBall_iff_mem_horizontalChord c hr hyc).mpr hxc)
    ((mem_closedBall_iff_mem_horizontalChord d hs hyd).mpr hxd)

theorem horizontalChord_inside_segment {c : ℂ} {r y a b : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im - r) (c.im + r))
    (ha : (⟨a, y⟩ : ℂ) ∉ closedBall c r)
    (hb : (⟨b, y⟩ : ℂ) ∉ closedBall c r)
    (hinter : (Icc a b ∩ Icc (horizontalChord c r y).1
      (horizontalChord c r y).2).Nonempty) :
    a < (horizontalChord c r y).1 ∧ (horizontalChord c r y).2 < b := by
  rw [mem_closedBall_iff_mem_horizontalChord c hr hy] at ha hb
  obtain ⟨x, hx, hx'⟩ := hinter
  constructor
  · by_contra h
    exact ha ⟨le_of_not_gt h, hx.1.trans hx'.2⟩
  · by_contra h
    exact hb ⟨hx'.1.trans hx.2, le_of_not_gt h⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CrossingChords
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The holes actually crossed by a segment

Only disks meeting the segment are retained. Their horizontal chords lie
strictly between its domain endpoints, are disjoint, and remove exactly
the same points of the segment as the full family of disks.
-/

open Set Function Metric

namespace CircleDomainRigidity

noncomputable def crossingDisks {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ Icc a b, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i))

noncomputable def crossingChords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (crossingDisks c r y a b).image (fun i => horizontalChord (c i) (r i) y)

@[simp] theorem mem_crossingDisks {I : Type*} [Fintype I]
    {c : I → ℂ} {r : I → ℝ} {y a b : ℝ} {i : I} :
    i ∈ crossingDisks c r y a b ↔
      ∃ x ∈ Icc a b, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) := by
  classical
  simp [crossingDisks]

theorem crossingDisk_line_hit {I : Type*} [Fintype I]
    {c : I → ℂ} {r : I → ℝ} {y a b : ℝ} {i : I}
    (hi : i ∈ crossingDisks c r y a b) :
    y ∈ Icc ((c i).im - r i) ((c i).im + r i) := by
  obtain ⟨x, _, hx⟩ := mem_crossingDisks.mp hi
  exact (horizontal_line_meets_closedBall (c i)).mp ⟨x, hx⟩

theorem crossingChords_inside {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b : ℝ} (hr : ∀ i, 0 ≤ r i)
    (ha : ∀ i, (⟨a, y⟩ : ℂ) ∉ closedBall (c i) (r i))
    (hb : ∀ i, (⟨b, y⟩ : ℂ) ∉ closedBall (c i) (r i)) :
    ∀ z ∈ crossingChords c r y a b, a < z.1 ∧ z.1 ≤ z.2 ∧ z.2 < b := by
  classical
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have hy := crossingDisk_line_hit hi
  obtain ⟨x, hx, hxi⟩ := mem_crossingDisks.mp hi
  have hends := horizontalChord_inside_segment (hr i) hy (ha i) (hb i)
    ⟨x, hx, (mem_closedBall_iff_mem_horizontalChord _ (hr i) hy).mp hxi⟩
  exact ⟨hends.1, horizontalChord_valid _ _ _, hends.2⟩

theorem crossingChords_disjoint {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b : ℝ} (hr : ∀ i, 0 ≤ r i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) :
    (↑(crossingChords c r y a b) : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2) := by
  classical
  intro z hz w hw hzw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hij : i ≠ j := by intro he; exact hzw (he ▸ rfl)
  exact horizontalChord_disjoint (hr i) (hr j)
    (crossingDisk_line_hit hi) (crossingDisk_line_hit hj) (hdisj hij)

theorem crossingChords_domain {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b x : ℝ} (hr : ∀ i, 0 ≤ r i) (hx : x ∈ Icc a b) :
    x ∈ (⋃ z ∈ crossingChords c r y a b, Icc z.1 z.2)ᶜ ↔
      (⟨x, y⟩ : ℂ) ∈ (⋃ i, closedBall (c i) (r i))ᶜ := by
  classical
  constructor
  · intro h hball
    obtain ⟨i, hi⟩ := mem_iUnion.mp hball
    have hit : i ∈ crossingDisks c r y a b := mem_crossingDisks.mpr ⟨x, hx, hi⟩
    apply h
    refine mem_iUnion₂.mpr ⟨horizontalChord (c i) (r i) y, Finset.mem_image.mpr ⟨i, hit, rfl⟩, ?_⟩
    exact (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hit)).mp hi
  · intro h hchord
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hchord
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    apply h
    exact mem_iUnion.mpr ⟨i,
      (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hi)).mpr hxz⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ChordTolls
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Accounting for chord tolls

The temporary chord enumeration carries the costs of its actual disks.
Summing over that enumeration charges exactly the disks meeting the
segment, and hence at most all disks meeting the whole parallel line.
-/

open Set Function

namespace CircleDomainRigidity

noncomputable def chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (z : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ i ∈ crossingDisks c r y a b,
    if horizontalChord (c i) (r i) y = z then A i else 0

theorem le_chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (hA : ∀ i, 0 ≤ A i)
    {i : I} (hi : i ∈ crossingDisks c r y a b) :
    A i ≤ chordToll c r A y a b (horizontalChord (c i) (r i) y) := by
  classical
  have h := Finset.single_le_sum
    (s := crossingDisks c r y a b)
    (f := fun j => if horizontalChord (c j) (r j) y = horizontalChord (c i) (r i) y
      then A j else 0) (fun j _ => by split <;> simp_all) hi
  simpa [chordToll] using h

theorem sum_chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) :
    (∑ z ∈ crossingChords c r y a b, chordToll c r A y a b z) =
      ∑ i ∈ crossingDisks c r y a b, A i := by
  classical
  unfold chordToll
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hmem : horizontalChord (c i) (r i) y ∈ crossingChords c r y a b :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  simp [eq_comm, hmem]

theorem sum_chordToll_le_line_hits {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (hA : ∀ i, 0 ≤ A i) :
    (∑ z ∈ crossingChords c r y a b, chordToll c r A y a b z) ≤
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  rw [sum_chordToll]
  calc
    _ = ∑ i, if i ∈ crossingDisks c r y a b then A i else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ crossingDisks c r y a b
      · simp only [hi, ↓reduceIte, indicator_of_mem (crossingDisk_line_hit hi), le_refl]
      · simp only [hi, ↓reduceIte]
        exact indicator_nonneg (fun _ _ => hA i) y

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DiskLinePayment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Variation across the round holes met by one line

This derives the linewise payment directly from smoothness on the
complement of the actual disks and their cluster oscillations. No
endpoint extension or pre-existing line-payment hypothesis is assumed.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

def diskLineDomain {I : Type*} (c : I → ℂ) (r : I → ℝ) (y : ℝ) : Set ℝ :=
  {x | (⟨x, y⟩ : ℂ) ∈ (⋃ i, closedBall (c i) (r i))ᶜ}

theorem isOpen_diskLineDomain {I : Type*} [Finite I] (c : I → ℂ) (r : I → ℝ) (y : ℝ) :
    IsOpen (diskLineDomain c r y) := by
  have hc : Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
  exact (isClosed_iUnion_of_finite (fun i => isClosed_closedBall)).isOpen_compl.preimage hc

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TerminalNormBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From terminal excess to the full oscillation norm

The finite transfer bounds the square-sum of the positive excess above
the original band widths. The elementary Euclidean triangle inequality
then gives the full oscillation norm needed in parallel-line payment.
-/

open Set

namespace CircleDomainRigidity

theorem sqrt_sum_sq_add_le {I : Type*} [Fintype I] (a b : I → ℝ) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤
      Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i)))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (b i)))
  have hab := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hsum : (∑ i, (a i + b i) ^ 2) =
      (∑ i, a i ^ 2) + 2 * (∑ i, a i * b i) + ∑ i, b i ^ 2 := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  nlinarith

theorem sqrt_sum_sq_le_band_add_excess {I : Type*} [Fintype I]
    (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt (∑ i, b i ^ 2) +
      Real.sqrt (∑ i, max (a i - b i) 0 ^ 2) := by
  calc
    _ ≤ Real.sqrt (∑ i, (b i + max (a i - b i) 0) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (ha i) (add_nonneg (hb i) (le_max_right _ _))).mpr
      linarith [le_max_left (a i - b i) 0]
    _ ≤ _ := sqrt_sum_sq_add_le b (fun i => max (a i - b i) 0)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteBandNorm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinct labels of physical terminals charge each original band
at most once in the finite oscillation estimate. -/

open Function

namespace CircleDomainRigidity

theorem finite_label_band_norm_le {I S : Type*} [Fintype I]
    (label : I → S) (hinj : Injective label) (b : S → ℝ)
    (hb : Summable (fun s => b s ^ 2)) :
    Real.sqrt (∑ i, b (label i) ^ 2) ≤ Real.sqrt (∑' s, b s ^ 2) := by
  classical
  apply Real.sqrt_le_sqrt
  have heq : (∑ s ∈ Finset.univ.image label, b s ^ 2) = ∑ i, b (label i) ^ 2 :=
    Finset.sum_image (fun i _ j _ hij => hinj hij)
  rw [← heq]
  exact hb.sum_le_tsum _ (fun s _ => sq_nonneg (b s))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FixedCapacityCutoffs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoffs for the scalar graph-capacity argument. Their
bounds are independent of the function, graph point, and chosen scale. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def scalarCapacityBump : ContDiffBump (0 : ℝ) := ⟨1,2,zero_lt_one,one_lt_two⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MobiusNormalization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def affineMobius (a b : ℂ) (ha : a ≠ 0) : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by simpa using ha)

def inversionMobius : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by norm_num)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LaurentNormalization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem analyticAt_dslope_zero {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (dslope u 0) 0 := by
  obtain ⟨p, hp⟩ := hu
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem reciprocal_germ_normalization {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 = 0) (hdu : deriv u 0 ≠ 0) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * (u z)⁻¹ + b = z⁻¹ + z * R z := by
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hv0 : v 0 ≠ 0 := by simpa only [v, dslope_same] using hdu
  let q : ℂ → ℂ := fun z => (v z)⁻¹
  have hq : AnalyticAt ℂ q 0 := hv.inv hv0
  let r := dslope q 0
  let t := dslope r 0
  have ht : AnalyticAt ℂ t 0 := analyticAt_dslope_zero (analyticAt_dslope_zero hq)
  have hu_eq (z : ℂ) : u z = z * v z := by
    simpa only [sub_zero, smul_eq_mul, hu0] using (sub_smul_dslope u 0 z).symm
  have hq_eq (z : ℂ) : q z = q 0 + z * r 0 + z ^ 2 * t z := by
    have h1 : z * r z = q z - q 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope q 0 z
    have h2 : z * t z = r z - r 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope r 0 z
    calc
      q z = q 0 + z * r z := by linear_combination -h1
      _ = q 0 + z * r 0 + z ^ 2 * t z := by linear_combination -z * h2
  refine ⟨v 0, -(v 0 * r 0), fun z => v 0 * t z, hv0, analyticAt_const.mul ht, ?_⟩
  intro z hz
  calc
    v 0 * (u z)⁻¹ + -(v 0 * r 0) = v 0 * z⁻¹ * q z - v 0 * r 0 := by
      rw [hu_eq, mul_inv_rev]
      dsimp only [q]
      ring
    _ = z⁻¹ + z * (v 0 * t z) := by
      rw [hq_eq]
      dsimp only [q]
      field_simp
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathLoopErasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a closed loop preserves every modulus of continuity and
cannot increase the diameter on any parameter interval. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
variable {a b : unitInterval}

def erasePathLoop (g : C(unitInterval, X)) (a b : unitInterval)
    (hab : a ≤ b) (heq : g a = g b) : C(unitInterval, X) where
  toFun := (Iic b).piecewise (fun t => g (min t a)) g
  continuous_toFun := by
    apply Continuous.piecewise _ (g.continuous.comp (continuous_id.min continuous_const))
      g.continuous
    intro t ht
    have ht' : t = b := by
      have h := frontier_Iic_subset b ht
      simpa only [mem_singleton_iff] using h
    subst t
    change g (min b a) = g b
    simpa only [min_eq_right hab] using heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathIntervalOscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The diameter of a path image on a fixed parameter set is continuous
in the uniform metric. Loop deletion decreases every interval diameter. -/
open Set Function Metric Bornology
open scoped Topology unitInterval NNReal
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def pathOscillation (S : Set unitInterval) (g : C(unitInterval, X)) : ℝ :=
  Metric.diam (g '' S)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLoopPathFamily
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact nonempty family of paths, stable under loop deletion.
It keeps the original image, endpoints and every uniform continuity bound. -/
open Set Function Filter Topology Metric
open scoped Topology UniformConvergence unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def loopPathFamily (f : C(unitInterval, X)) : Set C(unitInterval, X) :=
  {g | g 0 = f 0 ∧ g 1 = f 1 ∧ range g ⊆ range f ∧
    ∀ ε δ : ℝ, (∀ s t : unitInterval, dist s t ≤ δ → dist (f s) (f t) ≤ ε) →
      ∀ s t : unitInterval, dist s t ≤ δ → dist (g s) (g t) ≤ ε}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LoopOscillationMinimum
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimizing a uniformly convergent sum of interval oscillations.
Every nonconstant loop can strictly decrease one term without increasing
any other term. -/
open Set Function Filter Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def pathTestInterval (n : ℕ) : Set unitInterval :=
  Icc (denseSeq unitInterval n.unpair.1) (denseSeq unitInterval n.unpair.2)

def loopOscillationTerm (n : ℕ) (g : C(unitInterval, X)) : ℝ :=
  (1 / 2 : ℝ)^n * min 1 (pathOscillation (pathTestInterval n) g)

def loopOscillationCost (g : C(unitInterval, X)) : ℝ :=
  ∑' n, loopOscillationTerm n g

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricComposition
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric conformality after a holomorphic change of target

The actual chart differential is multiplied by the nonzero complex
derivative of the target map. Its Gram matrix is consequently multiplied
by the squared norm of that derivative, and its orientation stays positive.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem complex_column_norm_pos {a : ℂ} (ha : a ≠ 0) : 0 < a.re ^ 2 + a.im ^ 2 := by
  have hn : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro h
    have hr : a.re = 0 := by nlinarith [sq_nonneg a.im]
    have hi : a.im = 0 := by nlinarith [sq_nonneg a.re]
    exact ha (Complex.ext hr hi)
  exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) hn.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ExteriorCoefficientBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published coefficient area theorem and exterior bounds

Ahlfors, *Conformal Invariants* (1973), Theorem 5-1, p. 83, states
that the Laurent coefficients of a normalized exterior univalent map
satisfy the weighted square-sum bound. The proposition below includes
its Laurent expansion, in the zero-constant-term normalization needed
here. It is an explicit published input.

Only a coarse uniform exterior bound is needed for normal-family
compactness. It follows from the coefficient inequality and a geometric
series, with no additional analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def ExteriorCoefficientAreaTheorem : Prop :=
  ∀ F : ℂ → ℂ, DifferentiableOn ℂ F {z | 1 < ‖z‖} → InjOn F {z | 1 < ‖z‖} →
    (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) →
    ∃ c : ℕ → ℂ, Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖c n‖ ^ 2) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) * ‖c n‖ ^ 2) ≤ 1 ∧
      ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) (F z - z)

theorem norm_coefficient_le_one {c : ℕ → ℂ}
    (hc : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖c n‖ ^ 2))
    (hbound : (∑' n : ℕ, ((n : ℝ) + 1) * ‖c n‖ ^ 2) ≤ 1) (n : ℕ) : ‖c n‖ ≤ 1 := by
  have hterm : ((n : ℝ) + 1) * ‖c n‖ ^ 2 ≤ 1 :=
    (hc.le_tsum n (fun i _ => mul_nonneg (by positivity) (sq_nonneg _))).trans hbound
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcross : 0 ≤ (n : ℝ) * ‖c n‖ ^ 2 := mul_nonneg hn (sq_nonneg _)
  nlinarith [norm_nonneg (c n)]

theorem norm_exterior_series_le_one {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 1 := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  apply (div_le_one (by linarith : 0 < 1 - r)).mpr
  linarith

theorem ExteriorCoefficientAreaTheorem.exterior_bound
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 1 := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_one (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScaledExteriorBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exterior bounds at a prescribed physical radius

Scaling a principally normalized exterior map to the unit exterior
preserves its normalization. The coefficient-area input then bounds
its deviation from the identity outside twice the prescribed radius.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem principal_remainder_rescale {F : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    (fun z => F (a * z) / a - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  have hs := hF.comp_tendsto (tendsto_mul_left_cobounded ha)
  have hi : (fun z : ℂ => (a * z)⁻¹) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [smul_eq_mul, mul_inv_rev, mul_comm] using
      (IsBigO.const_smul_self (f' := fun z : ℂ => z⁻¹) (l := cobounded ℂ) a⁻¹)
  have hm := (hs.trans hi).const_smul_left a⁻¹
  apply hm.congr_left
  intro z
  change a⁻¹ * (F (a * z) - a * z) = F (a * z) / a - z
  field_simp

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_bound
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ R := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_bound hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR] at hb
  exact (div_le_one hR).mp hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalFamilyInputs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Classical normal-family inputs

The two propositions are classical consequences of Ahlfors,
*Complex Analysis*, third edition (1979):

* Chapter 5, Theorem 15, p. 224 (Montel compactness), in its diagonal
  exhaustion form, with the varying-domain convention of Chapter 5,
  Section 1.1, pp. 176–177. Holomorphy of the locally uniform limit
  follows from Mathlib.
* Chapter 5, Theorem 2, p. 178 (Hurwitz), applied to injective maps as in
  Chapter 6, Section 1.1, p. 231. Discarding finitely many initial terms
  gives the eventually holomorphic and injective formulation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def MontelExhaustion : Prop :=
  ∀ (D : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ),
    (∀ n, IsOpen (D n)) → Monotone D →
    (∀ n, DifferentiableOn ℂ (F n) (D n)) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M) →
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n)

def HurwitzUnivalentLimit : Prop :=
  ∀ (D : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsOpen D → IsConnected D →
    (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ InjOn (F n) D) →
    TendstoLocallyUniformlyOn F f atTop D →
    (¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) → InjOn f D

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityAlgebra
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and complex forms of the two-dimensional conductivity system.
These pointwise identities retain the signs and normalization used in the
Dirichlet-energy argument. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def planarDz (aX aY vX vY : ℝ) : ℂ :=
  ((aX + vY) / 2 : ℝ) + ((vX - aY) / 2 : ℝ) * Complex.I

 def planarDbar (aX aY vX vY : ℝ) : ℂ :=
  ((aX - vY) / 2 : ℝ) + ((vX + aY) / 2 : ℝ) * Complex.I

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityCoefficient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-valued conductivity coefficient. Its strict contraction
constant is (n-1)/(n+1), and the constructed density vanishes off F. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def conductivityRatio (n : ℕ) (hn : 1 ≤ n) : ℝ≥0 :=
  ⟨((n : ℝ) - 1) / ((n : ℝ) + 1), div_nonneg (by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) (by positivity)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityInterpolation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite priority interpolation of a horizontal coordinate. Overlaps
of the cutoff supports are allowed; the derivative estimate is uniform
in the number of cutoffs. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 def priorityBlend : List ((E → ℝ) × ℝ) → (E → ℝ) → E → ℝ
  | [], X => X
  | e :: L, X => fun p => e.1 p*e.2+(1-e.1 p)*priorityBlend L X p

 def priorityResidual : List ((E → ℝ) × ℝ) → E → ℝ
  | [] => fun _ => 1
  | e :: L => fun p => (1-e.1 p)*priorityResidual L p

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PriorityWeights
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable priority weights form a subprobability distribution. The
remaining mass belongs to the original horizontal coordinate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def priorityRemainder (χ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1-χ i)

 def priorityWeight (χ : ℕ → ℝ) (n : ℕ) : ℝ := χ n*priorityRemainder χ n

 def priorityInfiniteValue (χ c : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1-∑' n, priorityWeight χ n)*x + ∑' n, priorityWeight χ n*c n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ParallelLineIntegration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integration of the parallel-line payments

The linewise variation and hole costs are integrated without a measurable
choice of crossing segments. Cauchy–Schwarz is applied only to the density
in the chosen bounded region. This is the integration step of the
parallel-line lemma in Section 5 of the Koebe manuscript.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem integral_le_sqrt_measure_mul_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {g : X → ℝ} (hg : MemLp g 2 μ) (hpos : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun _ : X => (1 : ℝ)) (g := g)
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hpos
    (memLp_const 1) (by simpa using hg)
  simpa only [one_mul, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    Real.sqrt_eq_rpow] using h

theorem integral_le_disk_L2 {ρ : ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L) :
    Integrable ρ ∧ (∫ z, ρ z) ≤
      Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) L)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hi : IntegrableOn ρ (closedBall 0 L) :=
    (hρ.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have heq : (closedBall (0 : ℂ) L).indicator ρ = ρ := indicator_eq_self.mpr hsupport
  have heq2 : (closedBall (0 : ℂ) L).indicator (fun z => ρ z ^ 2) = (fun z => ρ z ^ 2) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hsupport (by simpa only [mem_support, ne_eq, pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hz)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupport).mp hi, ?_⟩
  have h := integral_le_sqrt_measure_mul_L2 (μ := volume.restrict (closedBall (0 : ℂ) L))
    (hρ.mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall hpos)
  rw [Measure.real, Measure.restrict_apply_univ, real_volume_closedBall 0 hL,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hL] at h
  rw [← integral_indicator measurableSet_closedBall, heq,
    ← integral_indicator measurableSet_closedBall, heq2] at h
  exact h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarGradientDensity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The planar gradient density used in line payment

The two Euclidean components are the real derivative on `1` and `I`.
The horizontal line derivative is the first component, and the square
of the density is the ordinary Euclidean Dirichlet energy integrand.
-/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def horizontalLine (y : ℝ) (x : ℝ) : ℂ := ⟨x, y⟩

theorem continuous_horizontalLine (y : ℝ) : Continuous (horizontalLine y) :=
  Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem contDiff_horizontalLine (y : ℝ) : ContDiff ℝ 1 (horizontalLine y) :=
  Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem hasDerivAt_horizontalLine (x y : ℝ) : HasDerivAt (horizontalLine y) 1 x := by
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

def euclideanGradientEnergy (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ v z 1) ^ 2 + (fderiv ℝ v z Complex.I) ^ 2

def euclideanGradientNorm (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (euclideanGradientEnergy v z)

theorem euclideanGradientEnergy_nonneg (v : ℂ → ℝ) (z : ℂ) :
    0 ≤ euclideanGradientEnergy v z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem euclideanGradientNorm_sq (v : ℂ → ℝ) (z : ℂ) :
    euclideanGradientNorm v z ^ 2 = euclideanGradientEnergy v z :=
  Real.sq_sqrt (euclideanGradientEnergy_nonneg v z)

theorem measurable_euclideanGradientNorm (v : ℂ → ℝ) : Measurable (euclideanGradientNorm v) :=
  (((measurable_fderiv_apply_const ℝ v 1).pow_const 2).add
    ((measurable_fderiv_apply_const ℝ v Complex.I).pow_const 2)).sqrt

theorem memLp_indicator_euclideanGradientNorm {v : ℂ → ℝ} {E : Set ℂ}
    (hE : MeasurableSet E) (henergy : IntegrableOn (euclideanGradientEnergy v) E) :
    MemLp (E.indicator (euclideanGradientNorm v)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_euclideanGradientNorm v).indicator hE).aestronglyMeasurable).mpr
  convert henergy.integrable_indicator hE using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  by_cases hz : z ∈ E
  · simp only [indicator_of_mem hz, euclideanGradientNorm_sq]
  · simp only [indicator_of_notMem hz, zero_pow (by norm_num : 2 ≠ 0)]

theorem horizontal_derivative_le_gradient {v : ℂ → ℝ} {x y : ℝ}
    (hv : DifferentiableAt ℝ v (horizontalLine y x)) :
    |deriv (v ∘ horizontalLine y) x| ≤ euclideanGradientNorm v (horizontalLine y x) := by
  rw [(hv.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontalLine x y)).deriv]
  apply Real.le_sqrt_of_sq_le
  simp only [sq_abs, euclideanGradientEnergy]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem horizontal_cluster_is_planar {U : Set ℂ} {v : ℂ → ℝ} {x y t : ℝ}
    (h : MapClusterPt t (𝓝[horizontalLine y ⁻¹' U] x) (v ∘ horizontalLine y)) :
    MapClusterPt t (𝓝[U] (horizontalLine y x)) v := by
  apply MapClusterPt.of_comp _ h
  exact tendsto_nhdsWithin_iff.mpr
    ⟨(continuous_horizontalLine y).continuousAt.mono_left nhdsWithin_le_nhds,
      self_mem_nhdsWithin⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy for periodic differentials

Agreement of circle maps near the retained core implies agreement of
their intrinsic differentials. Original L² energy controls the entire
unbounded core; smoothness on a compact tail controls the remainder.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleGradient_congr_of_eventuallyEq
    {f g : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    circleGradient f x = circleGradient g x := by
  have hx : f x = g x := hfg.self_of_nhds
  have hcut : circleCut f x = circleCut g x := congrArg (fun t => circleRepresentative t - 1 / 2) hx
  have heq : circleBranch f (circleCut f x) =ᶠ[𝓝 x] circleBranch g (circleCut g x) := by
    filter_upwards [hfg] with y hy
    change (AddCircle.equivIco 1 (circleCut f x) (f y) : ℝ) =
      (AddCircle.equivIco 1 (circleCut g x) (g y) : ℝ)
    rw [hy]
    exact congrArg (fun a => (AddCircle.equivIco 1 a (g y) : ℝ)) hcut
  simp only [circleGradient, circleFDeriv, heq.fderiv_eq (𝕜 := ℝ)]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_EnergyChangeCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The energy density under a change of coordinates

Pulling back a covector and its metric multiplies the planar Dirichlet
energy density by the absolute Jacobian determinant. Positive scalar
changes of metric have no effect in dimension two.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem covectorEnergy_pos_smul (v : Fin 2 → ℝ) {g : PlanarMetric}
    (hg : g.PosDef) {c : ℝ} (hc : 0 < c) :
    covectorEnergy v (c • g) = covectorEnergy v g := by
  simp only [covectorEnergy_eq_matrixEnergy, matrixEnergy_pos_smul _ hg hc]

theorem covectorEnergy_pullback (v : Fin 2 → ℝ) (g B : PlanarMetric)
    (hB : B.det ≠ 0) :
    covectorEnergy (Bᵀ *ᵥ v) (Bᵀ * g * B) = |B.det| * covectorEnergy v g := by
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hunitT : IsUnit Bᵀ.det := by simpa only [det_transpose] using hunit
  have hcancel : (Bᵀ * g * B)⁻¹ * Bᵀ = B⁻¹ * g⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hunitT, mul_one]
  have hquad : (Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * g * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) =
      v ⬝ᵥ (g⁻¹ *ᵥ v) := by
    rw [mulVec_mulVec, hcancel, ← mulVec_mulVec]
    rw [dotProduct_comm, dotProduct_transpose_mulVec,
      mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  have hdet : (Bᵀ * g * B).det = B.det ^ 2 * g.det := by
    rw [det_mul, det_mul, det_transpose]
    ring
  unfold covectorEnergy
  rw [hquad, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  ring

theorem pullback_metric_posDef {g B : PlanarMetric} (hg : g.PosDef) (hB : B.det ≠ 0) :
    (Bᵀ * g * B).PosDef := by
  have hunit : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hB)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa only [conjTranspose_eq_transpose_of_trivial] using hg.conjTranspose_mul_mul_same hi

theorem covectorEnergy_conformal_pullback (v : Fin 2 → ℝ) {g B : PlanarMetric}
    (hg : g.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c) :
    covectorEnergy (Bᵀ *ᵥ v) (c • (Bᵀ * g * B)) = |B.det| * covectorEnergy v g := by
  rw [covectorEnergy_pos_smul _ (pullback_metric_posDef hg hB) hc]
  exact covectorEnergy_pullback v g B hB

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarEnergyChange
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The integral energy formula in the real chart

Mathlib's change-of-variables theorem combines with the proved
covector pullback identity. This works on arbitrary measurable subsets,
including each mask and each localized tail of a finite completion.
-/

open Set Matrix MeasureTheory

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def planeDerivativeMatrix (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : PlanarMetric :=
  LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) A.toLinearMap

theorem det_planeDerivativeMatrix (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    (planeDerivativeMatrix A).det = A.det :=
  LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ) A.toLinearMap

/-- Dirichlet energy of a target covector field equals energy of its
actual pullback in any conformally rescaled pullback metric. -/
theorem integral_covectorEnergy_change_variables
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (A x) s x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0)
    (v : (ℝ × ℝ) → Fin 2 → ℝ) (g : (ℝ × ℝ) → PlanarMetric)
    (hPD : ∀ x ∈ s, (g (f x)).PosDef)
    (c : (ℝ × ℝ) → ℝ) (hc : ∀ x ∈ s, 0 < c x) :
    (∫ y in f '' s, covectorEnergy (v y) (g y)) =
      ∫ x in s, covectorEnergy ((planeDerivativeMatrix (A x))ᵀ *ᵥ v (f x))
        (c x • ((planeDerivativeMatrix (A x))ᵀ * g (f x) * planeDerivativeMatrix (A x))) := by
  refine (integral_image_eq_integral_abs_det_fderiv_smul volume hs hf hinj
    (fun y => covectorEnergy (v y) (g y))).trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [smul_eq_mul]
  have hB : (planeDerivativeMatrix (A x)).det ≠ 0 := by
    simpa only [det_planeDerivativeMatrix] using hdet x hx
  simpa only [det_planeDerivativeMatrix] using
    (covectorEnergy_conformal_pullback (v (f x)) (hPD x hx) hB (hc x hx)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleChainRule
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pullback of the intrinsic circle differential

The ordinary real chain rule applies to a local real lift. Independence
of that lift identifies the result with the intrinsic circle differential.
-/

open Set Filter Matrix
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleFDeriv_comp
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u : H → UnitAddCircle} {U : Set H} (hU : IsOpen U) (hu : SmoothCircleOn u U)
    {f : E → H} {x : E} (hf : DifferentiableAt ℝ f x) (hfx : f x ∈ U) :
    circleFDeriv (u ∘ f) x = (circleFDeriv u (f x)).comp (fderiv ℝ f x) := by
  let w := circleBranch u (circleCut u (f x))
  have hw : ContDiffAt ℝ ∞ w (f x) := hu (f x) hfx _ (circleCut_ne u (f x))
  have huc : ContinuousAt u (f x) := hu.continuousOn.continuousAt (hU.mem_nhds hfx)
  have hchain := (hw.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp x hf.hasFDerivAt
  rw [circleFDeriv_eq_lift (huc.comp hf.continuousAt) (hw.continuousAt.comp hf.continuousAt)
    (u := w ∘ f) (Filter.Eventually.of_forall fun y => coe_circleBranch u _ (f y))]
  exact hchain.fderiv

theorem planeDerivativeMatrix_eq_columns (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    planeDerivativeMatrix A = !![(A (1, 0)).1, (A (0, 1)).1;
      (A (1, 0)).2, (A (0, 1)).2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeDerivativeMatrix, LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
      Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]

theorem real_covector_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    L z = z.1 * L (1, 0) + z.2 * L (0, 1) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  calc
    L z = L (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg L hz
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem circleGradient_comp_vector
    {u : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hu : SmoothCircleOn u U)
    {f : (ℝ × ℝ) → (ℝ × ℝ)} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (hfx : f x ∈ U) :
    ![(circleGradient (u ∘ f) x).1, (circleGradient (u ∘ f) x).2] =
      (planeDerivativeMatrix (fderiv ℝ f x))ᵀ *ᵥ
        ![(circleGradient u (f x)).1, (circleGradient u (f x)).2] := by
  rw [planeDerivativeMatrix_eq_columns]
  simp only [circleGradient, circleFDeriv_comp hU hu hf hfx, ContinuousLinearMap.comp_apply]
  ext i
  fin_cases i
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      real_covector_apply (circleFDeriv u (f x)) (fderiv ℝ f x (1, 0))
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      real_covector_apply (circleFDeriv u (f x)) (fderiv ℝ f x (0, 1))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleEnergyChange
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformal invariance of the actual circle-coordinate energy

The chain rule identifies the pullback field with the intrinsic
circle differential. Thus the change-of-variables formula controls
the actual composed coordinate, without a chosen global real lift.
-/

open Set Filter Matrix MeasureTheory

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_circleEnergy_change_variables
    {s U : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hU : IsOpen U)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivAt f (A x) x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0) (hmap : MapsTo f s U)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u U)
    (g : (ℝ × ℝ) → PlanarMetric) (c : (ℝ × ℝ) → ℝ)
    (hc : ∀ x ∈ s, 0 < c x)
    (hg : ∀ x ∈ s, g x = c x • ((planeDerivativeMatrix (A x))ᵀ * planeDerivativeMatrix (A x))) :
    (∫ y in f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient (u ∘ f)) g x := by
  have heq := integral_covectorEnergy_change_variables hs f A
    (fun x hx => (hf x hx).hasFDerivWithinAt) hinj hdet
    (fun y => ![(circleGradient u y).1, (circleGradient u y).2]) (fun _ => 1)
    (fun _ _ => Matrix.PosDef.one) c hc
  refine heq.trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  have hvec := circleGradient_comp_vector hU hu (hf x hx).differentiableAt (hmap hx)
  rw [(hf x hx).fderiv] at hvec
  simp only [mul_one]
  rw [← hg x hx, ← hvec]
  rfl

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricChartEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy of the actual metric-conformal chart differential

The Gram equations defining metric conformality identify the source
metric with a scalar multiple of the pulled-back Euclidean metric.
Consequently the covector energy changes by the positive Jacobian.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def complexRealMatrix (A : ℂ →L[ℝ] ℂ) : PlanarMetric :=
  !![(A 1).re, (A Complex.I).re; (A 1).im, (A Complex.I).im]

theorem det_complexRealMatrix (A : ℂ →L[ℝ] ℂ) :
    (complexRealMatrix A).det =
      (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  simp [complexRealMatrix, Matrix.det_fin_two]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereRealDifferential
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def complexToRealDerivative (A : ℂ →L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toContinuousLinearMap.comp
    (A.comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)

theorem planeMatrix_complexToRealDerivative (A : ℂ →L[ℝ] ℂ) :
    planeDerivativeMatrix (complexToRealDerivative A) = complexRealMatrix A := by
  rw [planeDerivativeMatrix_eq_columns]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MarkedDiskLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous limits of marked round disks

Bounded centers and nonnegative bounded radii form a compact parameter
space. A countable family therefore admits one subsequence on which all
parameters converge. The limiting radius may be zero.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closedBall_eq_affine_image {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    closedBall c r = (fun u : ℂ => c + r • u) '' closedBall 0 1 := by
  rw [← affinity_unitClosedBall hr c]
  change (fun z : ℂ => c + z) '' ((fun u : ℂ => r • u) '' closedBall 0 1) = _
  rw [image_image]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Euclidean coordinates for bounded round disks

Completing the square for a fractional linear map identifies a round
spherical disk avoiding infinity with an ordinary Euclidean closed
disk. This provides the center/radius coordinates used for marked ends.
-/

open Set Function
open scoped ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

theorem fractional_norm_square_identity (a b c d z : ℂ) :
    ‖((Complex.normSq a - Complex.normSq c : ℝ) : ℂ) * z + (conj a * b - conj c * d)‖ ^ 2 -
      ‖a * d - b * c‖ ^ 2 =
      (Complex.normSq a - Complex.normSq c) * (‖a * z + b‖ ^ 2 - ‖c * z + d‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem fractional_norm_region_eq_closedBall
    (a b c d : ℂ) (hA : 0 < Complex.normSq a - Complex.normSq c) :
    {z : ℂ | ‖a * z + b‖ ≤ ‖c * z + d‖} =
      Metric.closedBall (-(conj a * b - conj c * d) / ((Complex.normSq a - Complex.normSq c : ℝ) : ℂ))
        (‖a * d - b * c‖ / (Complex.normSq a - Complex.normSq c)) := by
  let A : ℝ := Complex.normSq a - Complex.normSq c
  let B : ℂ := conj a * b - conj c * d
  have hA' : 0 < A := hA
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hnA : ‖(A : ℂ)‖ = A := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA']
  ext z
  change ‖a * z + b‖ ≤ ‖c * z + d‖ ↔ dist z (-B / (A : ℂ)) ≤ ‖a * d - b * c‖ / A
  have he : (A : ℂ) * z + B = (A : ℂ) * (z - -B / (A : ℂ)) := by field_simp <;> ring
  have hid := fractional_norm_square_identity a b c d z
  change ‖(A : ℂ) * z + B‖ ^ 2 - ‖a * d - b * c‖ ^ 2 =
    A * (‖a * z + b‖ ^ 2 - ‖c * z + d‖ ^ 2) at hid
  have hnorm : ‖(A : ℂ) * z + B‖ = A * dist z (-B / (A : ℂ)) := by
    rw [he, norm_mul, hnA, dist_eq_norm]
  rw [le_div_iff₀ hA, mul_comm (dist z (-B / (A : ℂ))) A, ← hnorm]
  constructor
  · intro h
    have hsq : ‖a * z + b‖ ^ 2 ≤ ‖c * z + d‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hp := mul_nonpos_of_nonneg_of_nonpos hA'.le (sub_nonpos.mpr hsq)
    linarith
  · intro h
    have hsq : ‖(A : ℂ) * z + B‖ ^ 2 ≤ ‖a * d - b * c‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    have hdif : ‖a * z + b‖ ^ 2 ≤ ‖c * z + d‖ ^ 2 := by nlinarith [hA']
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hdif

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskTopology
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Masks away from their retained boundaries

A connected filling cap disjoint from the mask boundary is wholly on
one side. Away from that boundary, extending a circle coordinate by zero
outside the mask is smooth and its intrinsic differential is exactly
the indicated covector.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def maskCircleMap {X : Type*} (M : Set X) (f : X → UnitAddCircle) (x : X) : UnitAddCircle := by
  classical
  exact if x ∈ M then f x else 0

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFillings
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous smooth fillings of circle coordinates

Connected collars and one active staircase per disk give actual real
rank-one extensions. Their projections patch into the retained circle
maps. The construction requires only the existing local branches and
does not assert any unproved period or winding statement.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def IsFilledCircleFamily {I L : Type*}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ))
    (v F : L → (ℝ × ℝ) → UnitAddCircle) : Prop :=
  (∀ l, SmoothCircleOn (F l) Ω) ∧
  (∀ l x, (∀ i, x ∉ D i) → F l x = v l x) ∧
  (∀ i, ∀ᶠ x in 𝓝ˢ (frontier (D i)), ∀ l, F l x = v l x) ∧
  ∀ i l m, l ≠ m → ∀ x ∈ D i,
    planarWedge (circleGradient (F l) x) (circleGradient (F m) x) = 0

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedWedgeCost
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Random wedge cost on different coordinate masks

Each pair is integrated on the intersection of its two masks. Thus
the original fields need square-integrable norm only on their own masks.
The same independent-shift estimate controls this actual masked cost.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def maskedStaircaseCost {X P : Type*} [MeasurableSpace X] [Fintype P]
    (μ : Measure X) {n : ℕ} (pairs : P → Fin n × Fin n) (M : Fin n → Set X)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  ∑ p, staircasePairCost (μ.restrict (M (pairs p).1 ∩ M (pairs p).2))
    u c x χ h δ (pairs p).1 (pairs p).2 θ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedCircleFillings
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle fillings with coordinate-specific masks

Real collar branches still give one simultaneous rank-one filling.
Smoothness is required only on each coordinate's own mask. The common
boundary agreement and zero-wedge identities hold on all filling disks.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def IsMaskedFilledCircleFamily {I : Type*} {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (Ω : Set (ℝ × ℝ)) (M : Fin n → Set (ℝ × ℝ))
    (v F : Fin n → (ℝ × ℝ) → UnitAddCircle) : Prop :=
  (∀ l, SmoothCircleOn (F l) (Ω ∩ interior (M l))) ∧
    IsFilledCircleFamily D ∅ v F

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CofiniteTransfer
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy transfer on a completed region containing infinity

The completed region is unbounded in a finite chart. Its tail outside the
retained core lies in one compact piece. Local agreement on the core and
the original finite energy give integrability on the entire completed
region, and hence the full localized estimate.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem gradientEnergy_eq_spherical_on_core
    {K : Set (ℝ × ℝ)} {f u : (ℝ × ℝ) → ℝ}
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {z : ℝ × ℝ} (hz : z ∈ K) :
    gradientEnergy f g z = gradientEnergy u (fun z => sphericalMetricFactor z • 1) z := by
  have heq := (hretain.filter_mono (nhds_le_nhdsSet hz)).fderiv_eq (𝕜 := ℝ)
  simp only [gradientEnergy, planarGradient, heq, hmetric.self_of_nhdsSet z hz]

theorem integrableOn_gradientEnergy_with_cofinite_core
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    {f u : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hu : IntegrableOn (gradientEnergy u (fun z => sphericalMetricFactor z • 1)) G)
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (gradientEnergy f g) Q := by
  obtain ⟨R, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  have ht : IntegrableOn (gradientEnergy f g) (Q \ K) := by
    rw [htail]
    exact (integrableOn_gradientEnergy hΩ hQc (fun z hz => hQΩ hz.1) hf hg hPD).mono_set sdiff_subset
  have hc : IntegrableOn (gradientEnergy f g) (Q ∩ K) := by
    apply (hu.mono_set (fun z hz => hKG hz.2)).congr
    filter_upwards [ae_restrict_mem (hQ.measurableSet.inter hK.measurableSet)] with z hz
    exact (gradientEnergy_eq_spherical_on_core hretain hmetric hz.2).symm
  simpa only [inter_union_sdiff] using hc.union ht

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanFillLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def dilatedJordan (H : ℂ ≃ₜ ℂ) (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans H

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitConformality
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def HurwitzZeroFreeLimit : Prop :=
  ∀ (D : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsOpen D → IsConnected D →
    (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, F n z ≠ 0) →
    TendstoLocallyUniformlyOn F f atTop D →
    (∀ z ∈ D, f z = 0) ∨ (∀ z ∈ D, f z ≠ 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def radialClamp (r : ℝ) (z : ℂ) : ℂ := (r / max r ‖z‖) • z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexRealEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the line-payment energy with the transferred real energy

The finite transfer uses real coordinate pairs, while round disks and
line payment use complex coordinates. The canonical linear equivalence
preserves volume and identifies the two ordinary gradient integrands.
-/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem euclideanGradientEnergy_eq_real_gradientEnergy
    {F : (ℝ × ℝ) → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (Complex.equivRealProdCLM z)) :
    euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) z =
      gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z) := by
  have hd := (hF.hasFDerivAt.comp z Complex.equivRealProdCLM.hasFDerivAt).fderiv
  unfold euclideanGradientEnergy gradientEnergy
  rw [hd, covectorEnergy_identity]
  rfl

theorem real_gradient_energy_in_complex_coordinates
    {O S : Set (ℝ × ℝ)} (hO : IsOpen O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    {F : (ℝ × ℝ) → ℝ} (hF : ContDiffOn ℝ 1 F O)
    (hi : IntegrableOn (gradientEnergy F (fun _ => 1)) S) :
    IntegrableOn (euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM))
      (Complex.equivRealProdCLM ⁻¹' S) ∧
      (∫ z in Complex.equivRealProdCLM ⁻¹' S,
        euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) z) =
        ∫ x in S, gradientEnergy F (fun _ => 1) x := by
  have hmp := Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding S
  have hcomp : IntegrableOn (fun z : ℂ => gradientEnergy F (fun _ => 1)
      (Complex.equivRealProdCLM z)) (Complex.equivRealProdCLM ⁻¹' S) :=
    (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have heq : euclideanGradientEnergy (F ∘ Complex.equivRealProdCLM) =ᵐ[
      volume.restrict (Complex.equivRealProdCLM ⁻¹' S)]
      (fun z => gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z)) := by
    filter_upwards [ae_restrict_mem (hS.preimage Complex.equivRealProdCLM.continuous.measurable)] with z hz
    exact euclideanGradientEnergy_eq_real_gradientEnergy
      ((hF.contDiffAt (hO.mem_nhds (hSO hz))).differentiableAt (by norm_num))
  refine ⟨hcomp.congr heq.symm, ?_⟩
  calc
    _ = ∫ z in Complex.equivRealProdCLM ⁻¹' S,
        gradientEnergy F (fun _ => 1) (Complex.equivRealProdCLM z) := integral_congr_ae heq
    _ = _ := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding _ S

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TransportedCircleCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual pushed-forward circle coordinates

A smooth coordinate on an open part of the source is composed with the
actual inverse of a normalized smooth sphere equivalence. Its target
domain is the actual image of that source region. It is smooth there,
its pullback is locally the original coordinate, and the full
Dirichlet change-of-variables formula follows.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem smoothCircleOn_comp
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u : H → UnitAddCircle} {U : Set H} (hu : SmoothCircleOn u U)
    {f : E → H} {V : Set E} (hf : ∀ x ∈ V, ContDiffAt ℝ ∞ f x)
    (hmap : MapsTo f V U) : SmoothCircleOn (u ∘ f) V := by
  intro x hx a hcut
  exact (hu (f x) (hmap hx) a hcut).comp x (hf x hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedRealCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real barrier coordinates on normalized circle models

Real coordinates are transported by the actual smooth inverse. The
ordinary real gradient has the same energy as its intrinsic circle
differential, so the proved change-of-variables formula applies without
discarding the real lift or its values.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem circleGradient_coe_eq_planarGradient
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) {F : (ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) {x : ℝ × ℝ} (hx : x ∈ O) :
    circleGradient (fun y => (F y : UnitAddCircle)) x = planarGradient F x := by
  exact (circleGradient_eventuallyEq_lift hO
    ((AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn hF.continuousOn) hF
    (fun _ _ => rfl) hx).self_of_nhds

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_EnergyTransportIntegrability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability in the metric energy change of variables

The Jacobian theorem gives integrability equivalence as well as equality
of integrals. This supplies the target finite-energy hypotheses required
by parallel-line payment from the actual source energy estimates.
-/

open Set Function Filter Matrix MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace FiniteTransfer

theorem integrable_covectorEnergy_change_variables_iff
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (A x) s x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0)
    (v : (ℝ × ℝ) → Fin 2 → ℝ) (g : (ℝ × ℝ) → PlanarMetric)
    (hPD : ∀ x ∈ s, (g (f x)).PosDef)
    (c : (ℝ × ℝ) → ℝ) (hc : ∀ x ∈ s, 0 < c x) :
    IntegrableOn (fun y => covectorEnergy (v y) (g y)) (f '' s) ↔
      IntegrableOn (fun x => covectorEnergy ((planeDerivativeMatrix (A x))ᵀ *ᵥ v (f x))
        (c x • ((planeDerivativeMatrix (A x))ᵀ * g (f x) * planeDerivativeMatrix (A x)))) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  simp only [smul_eq_mul]
  have hB : (planeDerivativeMatrix (A x)).det ≠ 0 := by
    simpa only [det_planeDerivativeMatrix] using hdet x hx
  simpa only [det_planeDerivativeMatrix] using
    (covectorEnergy_conformal_pullback (v (f x)) (hPD x hx) hB (hc x hx)).symm

theorem integrable_circleEnergy_change_variables_iff
    {s U : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hU : IsOpen U)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivAt f (A x) x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0) (hmap : MapsTo f s U)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u U)
    (g : (ℝ × ℝ) → PlanarMetric) (c : (ℝ × ℝ) → ℝ)
    (hc : ∀ x ∈ s, 0 < c x)
    (hg : ∀ x ∈ s, g x = c x • ((planeDerivativeMatrix (A x))ᵀ * planeDerivativeMatrix (A x))) :
    IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) (f '' s) ↔
      IntegrableOn (fieldEnergy (circleGradient (u ∘ f)) g) s := by
  have heq := integrable_covectorEnergy_change_variables_iff hs f A
    (fun x hx => (hf x hx).hasFDerivWithinAt) hinj hdet
    (fun y => ![(circleGradient u y).1, (circleGradient u y).2]) (fun _ => 1)
    (fun _ _ => Matrix.PosDef.one) c hc
  refine heq.trans (integrableOn_congr_fun ?_ hs)
  intro x hx
  have hvec := circleGradient_comp_vector hU hu (hf x hx).differentiableAt (hmap hx)
  rw [(hf x hx).fderiv] at hvec
  simp only [mul_one]
  rw [← hg x hx, ← hvec]
  rfl

end FiniteTransfer

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealSequencePayment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line-payment limit for a fixed test in the constructed countable sequence. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def prefixIndex (l n : ℕ) : Fin (n + 1) :=
  ⟨min l n, Nat.lt_succ_of_le (Nat.min_le_right l n)⟩

theorem prefixIndex_eq (l : ℕ) : ∀ᶠ n in atTop, (prefixIndex l n).val = l := by
  filter_upwards [eventually_ge_atTop l] with n hn
  exact Nat.min_eq_left hn

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCovectorEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex-chart differential norm is exactly the two-coordinate
Euclidean energy used by the finite transfer. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem complexCovector_norm_sq (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
  let a := (L 1) ^ 2 + (L Complex.I) ^ 2
  have ha : 0 ≤ a := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hu : ‖L‖ ≤ Real.sqrt a := by
    apply L.opNorm_le_bound (Real.sqrt_nonneg a)
    intro z
    rw [complexCovector_apply, Real.norm_eq_abs]
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hsq : (z.re * L 1 + z.im * L Complex.I) ^ 2 ≤ a * ‖z‖ ^ 2 := by
      dsimp only [a]
      rw [hz]
      nlinarith [sq_nonneg (z.re * L Complex.I - z.im * L 1)]
    have hs : (Real.sqrt a * ‖z‖) ^ 2 = a * ‖z‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha]
    nlinarith [sq_abs (z.re * L 1 + z.im * L Complex.I),
      abs_nonneg (z.re * L 1 + z.im * L Complex.I),
      mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg z)]
  have hd := complexCovector_dualVector_norm_le L
  have hdsq : ‖(L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I‖ ^ 2 = a := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    dsimp only [a]
    ring
  have hlo := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hhi := pow_le_pow_left₀ (norm_nonneg L) hu 2
  rw [hdsq] at hlo
  rw [Real.sq_sqrt ha] at hhi
  exact le_antisymm hhi hlo

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MollificationEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong mollification converges in Dirichlet energy on every measurable
source region. The limiting energy is that of the original weak field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_tendsto_of_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : ℕ → X → ℝ} {g : X → ℝ}
    (hv : ∀ n, MemLp (v n) 2 μ) (hg : MemLp g 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, v n x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv g hg).mpr hl
  have hn := ht.norm.pow 2
  have he (f : X → ℝ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq hf]
  simpa only [he] using hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PeriodicFilling
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer-translated fillings on the pulled-back circle cover

Section 2, Step 4, of the Koebe manuscript fills one sheet over each
filling disk and uses its integer translates on all other sheets. Here
the cover is the actual pullback of `ℝ → ℝ/ℤ` by the original circle
coordinate. The filled real function is the original height plus the
base correction `g - u` on each disk. Thus it has exactly the original
deck increments and projects to the circle map already constructed by
`CirclePatching`.

The differentials on every sheet are those of the selected real filling.
No additional lifting, period, or winding input is assumed.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The real difference of two continuous lifts is locally constant. -/
theorem isLocallyConstant_real_lift_difference
    {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hproj : ∀ x, (u x : UnitAddCircle) = (v x : UnitAddCircle)) :
    IsLocallyConstant (fun x => u x - v x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer (x := x) hu.continuousAt hv.continuousAt
    (Filter.Eventually.of_forall hproj)
  have hmx := hm.self_of_nhds
  exact hm.mono (fun y hy => by linarith)

/-- Endpoint differences of continuous real lifts of one path agree. -/
theorem real_lift_path_increment_eq (u v : C(unitInterval, ℝ))
    (hproj : ∀ t, (u t : UnitAddCircle) = (v t : UnitAddCircle)) :
    u 1 - u 0 = v 1 - v 0 := by
  have h := IsLocallyConstant.apply_eq_of_preconnectedSpace
    (isLocallyConstant_real_lift_difference u.continuous v.continuous hproj) (1 : unitInterval) 0
  linarith

/-- Canonical lift, used only to make the path increment independent of
the choice of real branch. -/
def realCirclePathLift (γ : C(unitInterval, UnitAddCircle)) : C(unitInterval, ℝ) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath γ (circleRepresentative (γ 0))
    (coe_circleRepresentative (γ 0)).symm

theorem realCirclePathLift_projects (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    (realCirclePathLift γ t : UnitAddCircle) = γ t :=
  congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_lifts γ
    (circleRepresentative (γ 0)) (coe_circleRepresentative (γ 0)).symm) t

/-- Winding measured in turns; on a loop it is an integer. -/
def circlePathIncrement (γ : C(unitInterval, UnitAddCircle)) : ℝ :=
  realCirclePathLift γ 1 - realCirclePathLift γ 0

theorem circlePathIncrement_eq_lift (γ : C(unitInterval, UnitAddCircle))
    (u : C(unitInterval, ℝ)) (hu : ∀ t, (u t : UnitAddCircle) = γ t) :
    circlePathIncrement γ = u 1 - u 0 := by
  apply real_lift_path_increment_eq
  intro t
  exact (realCirclePathLift_projects γ t).trans (hu t).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleIncrementContinuity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous families of circle paths have continuous real increments.
This follows from the actual homotopy lift, so no choice of a discontinuous
starting-angle representative enters the continuity or compact bounds. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_family_circle_increment
    {A : Type*} [TopologicalSpace A]
    (γ : A → C(unitInterval, UnitAddCircle)) (hγ : Continuous γ)
    (a : A → ℝ) (ha : Continuous a)
    (hproj : ∀ x, (a x : UnitAddCircle) = γ x 0) :
    Continuous (fun x => circlePathIncrement (γ x)) := by
  let H : C(unitInterval × A, UnitAddCircle) :=
    ⟨fun p => γ p.2 p.1, continuous_eval.comp ((hγ.comp continuous_snd).prodMk continuous_fst)⟩
  let L := (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy H ⟨a, ha⟩ (fun x => (hproj x).symm)
  have he (x : A) : circlePathIncrement (γ x) = L (1, x) - a x := by
    let u : C(unitInterval, ℝ) := L.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x))
    have hu (t : unitInterval) : (u t : UnitAddCircle) = γ x t :=
      congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_lifts H ⟨a, ha⟩
        (fun x => (hproj x).symm)) (t, x)
    rw [circlePathIncrement_eq_lift (γ x) u hu]
    change L (1, x) - L (0, x) = _
    rw [show L (0, x) = a x from
      (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_zero H ⟨a, ha⟩ (fun x => (hproj x).symm) x]
  exact ((L.continuous.comp (continuous_const.prodMk continuous_id)).sub ha).congr
    (fun x => (he x).symm)

theorem continuous_circlePathIncrement :
    Continuous (circlePathIncrement : C(unitInterval, UnitAddCircle) → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro γ
  let a := circleCut (fun δ : C(unitInterval, UnitAddCircle) => δ 0) γ
  let O : Set C(unitInterval, UnitAddCircle) := {δ | δ 0 ≠ (a : UnitAddCircle)}
  have hO : IsOpen O := isClosed_singleton.isOpen_compl.preimage (continuous_eval_const 0)
  have hγ : γ ∈ O := circleCut_ne (fun δ : C(unitInterval, UnitAddCircle) => δ 0) γ
  let u : O → ℝ := fun δ => (AddCircle.equivIco (1 : ℝ) a (δ.val 0)).val
  have hu : Continuous u := by
    apply continuous_iff_continuousAt.mpr
    intro δ
    have heval : ContinuousAt (fun ε : O => ε.val (0 : unitInterval)) δ :=
      ((continuous_eval_const (0 : unitInterval)).comp continuous_subtype_val).continuousAt
    have hchart : ContinuousAt
        (fun ε : O => AddCircle.equivIco (1 : ℝ) a (ε.val 0)) δ :=
      (AddCircle.continuousAt_equivIco (1 : ℝ) a δ.property).comp
        (f := fun ε : O => ε.val 0) heval
    exact continuous_subtype_val.continuousAt.comp hchart
  have hloc : ContinuousOn circlePathIncrement O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_family_circle_increment (fun δ : O => δ.val) continuous_subtype_val u hu
      (fun _ => AddCircle.coe_equivIco)
  exact hloc.continuousAt (hO.mem_nhds hγ)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePathPrefixes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for all initial lifts in a compact family of circle paths. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def circlePathPrefix (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    C(unitInterval, UnitAddCircle) :=
  γ.comp ⟨fun s => s * t, continuous_id.mul continuous_const⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleGreen
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- Real line integral of `P dx + Q dy`, with parameter interval `[0,1]`. -/
def planarFormIntegral (P Q : ℂ → ℝ) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im

def unitCircleParam (c : ℂ) (r : ℝ) (t : ℝ) : ℂ := circleMap c r (2 * Real.pi * t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCircleParametrization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positively sized round disk and its once-traversed regular
boundary, used to specialize the published Green identity to a disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def roundDiskChart (R : ℝ) (hR : 0 < R) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (R : ℂ) (by exact_mod_cast hR.ne')

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleStokes
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-region Stokes identity and area bound for the actual
intrinsic differential of a smooth circle coordinate. The only additional
published input is the precisely stated classical Green formula. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def circleFormIntegral (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) (γ : ℝ → ℂ) : ℝ :=
  planarFormIntegral (φ * fun z => circleFDeriv u z 1)
    (φ * fun z => circleFDeriv u z Complex.I) γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCircleOscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth circle variation controls a homeomorphic height on the enclosed
disk. This is the boundary step of the logarithmic modulus estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def smoothCircleVariation (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2*Real.pi), |deriv (f ∘ circleMap c r) θ|

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HilbertWeakSubsequence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Hilbert-space subsequence used for the scalar fillings
and their two L² differential components. It follows from the library's
sequential Banach–Alaoglu theorem and the Riesz representation isometry. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_hilbert_weak_subsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : E, ‖v‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ w : E, Tendsto (fun n => inner ℝ (u (σ n)) w) atTop (𝓝 (inner ℝ v w)) := by
  let a : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  have ha (n : ℕ) : a n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) C := by
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, a,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨l, hl, σ, hσ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := E) 0 C).subseq_of_frequently_in
      (Frequently.of_forall ha)
  let v : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual l)
  refine ⟨v, ?_, σ, hσ, ?_⟩
  · have hn : ‖WeakDual.toStrongDual l‖ ≤ C := by
      simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hl
    exact ((InnerProductSpace.toDual ℝ E).symm.norm_map _).trans_le hn
  · intro w
    have he := (WeakDual.eval_continuous w).continuousAt.tendsto.comp hlim
    have hv : inner ℝ v w = l w := InnerProductSpace.toDual_symm_apply
    simpa only [a, comp_def, StrongDual.toWeakDual_apply, InnerProductSpace.toDual_apply_apply,
      ← hv] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2WeakSubsequence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded L² sequences admit subsequences whose pairings converge.
The representative integrals below are obtained from the actual L² limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_weak_subsequence
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
    (u : ℕ → X → ℝ) (hu : ∀ n, MemLp (u n) 2 μ)
    (C : ℝ) (hbound : ∀ n, ‖(hu n).toLp (u n)‖ ≤ C) :
    ∃ V : Lp ℝ 2 μ, ‖V‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ w : Lp ℝ 2 μ,
        Tendsto (fun n => ∫ x, u (σ n) x * w x ∂μ) atTop
          (𝓝 (∫ x, V x * w x ∂μ)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  obtain ⟨V, hV, σ, hσ, hlim⟩ := exists_hilbert_weak_subsequence
    (fun n => (hu n).toLp (u n)) C hbound
  refine ⟨V, hV, σ, hσ, ?_⟩
  intro w
  have he (n : ℕ) : inner ℝ ((hu n).toLp (u n)) w = ∫ x, u n x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
  have hVeq : inner ℝ V w = ∫ x, V x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [Real.inner_apply]
  simpa only [he, hVeq] using hlim w

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakPairEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower semicontinuity of the combined energy of two weakly convergent
real L² fields. Only the two pairings with the limiting fields are needed. -/
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem paired_hilbert_energy_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u₁ u₂ : ℕ → E} {v₁ v₂ : E} {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ‖u₁ n‖ ^ 2 + ‖u₂ n‖ ^ 2 ≤ B + ε n)
    (h₁ : Tendsto (fun n => inner ℝ (u₁ n) v₁) atTop (𝓝 (‖v₁‖ ^ 2)))
    (h₂ : Tendsto (fun n => inner ℝ (u₂ n) v₂) atTop (𝓝 (‖v₂‖ ^ 2))) :
    ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 ≤ B := by
  have hlim := ((h₁.add h₂).const_mul 2).sub
    (tendsto_const_nhds (x := ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2))
  have hle : ∀ᶠ n in atTop,
      2 * (inner ℝ (u₁ n) v₁ + inner ℝ (u₂ n) v₂) -
        (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) ≤ B + ε n := by
    filter_upwards [hbound] with n hn
    have hpos₁ := sq_nonneg ‖u₁ n - v₁‖
    have hpos₂ := sq_nonneg ‖u₂ n - v₂‖
    rw [norm_sub_sq_real] at hpos₁ hpos₂
    linarith
  have h := le_of_tendsto_of_tendsto hlim (tendsto_const_nhds.add hε) hle
  linarith

theorem paired_L2_energy_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₁ u₂ : ℕ → X → ℝ} (hu₁ : ∀ n, MemLp (u₁ n) 2 μ)
    (hu₂ : ∀ n, MemLp (u₂ n) 2 μ)
    (G₁ G₂ : Lp ℝ 2 μ) {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (∫ x, (u₁ n x) ^ 2 + (u₂ n x) ^ 2 ∂μ) ≤ B + ε n)
    (h₁ : Tendsto (fun n => ∫ x, u₁ n x * G₁ x ∂μ) atTop
      (𝓝 (∫ x, G₁ x * G₁ x ∂μ)))
    (h₂ : Tendsto (fun n => ∫ x, u₂ n x * G₂ x ∂μ) atTop
      (𝓝 (∫ x, G₂ x * G₂ x ∂μ))) :
    (∫ x, G₁ x ^ 2 + G₂ x ^ 2 ∂μ) ≤ B := by
  have hnorm (G : Lp ℝ 2 μ) : (∫ x, G x ^ 2 ∂μ) = ‖G‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply, pow_two]
  have hpair (u : X → ℝ) (hu : MemLp u 2 μ) (G : Lp ℝ 2 μ) :
      inner ℝ (hu.toLp u) G = ∫ x, u x * G x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
  have hnormu (u : X → ℝ) (hu : MemLp u 2 μ) :
      ‖hu.toLp u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
    rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq hu]
  rw [integral_add (Lp.memLp G₁).integrable_sq (Lp.memLp G₂).integrable_sq,
    hnorm, hnorm]
  apply paired_hilbert_energy_le (u₁ := fun n => (hu₁ n).toLp (u₁ n))
    (u₂ := fun n => (hu₂ n).toLp (u₂ n)) hε
  · filter_upwards [hbound] with n hn
    simpa only [hnormu, integral_add (hu₁ n).integrable_sq (hu₂ n).integrable_sq] using hn
  · simpa only [hpair, ← hnorm, pow_two] using h₁
  · simpa only [hpair, ← hnorm, pow_two] using h₂

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def invertedPrincipalRemainder (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun w => F w⁻¹ - w⁻¹) 0 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothImageArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Jacobian boundary integral is the signed area of the
actual image curve, expressed using its real and imaginary coordinates. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def signedCurveArea (γ : ℝ → ℂ) : ℝ :=
    ∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalCircleArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed area of the first two principal Laurent terms is computed
exactly; the term linear in the first coefficient cancels. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalLeadingCurve (R : ℝ) (c : ℂ) (t : ℝ) : ℂ :=
    unitCircleParam 0 R t + c/unitCircleParam 0 R t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalCircleRemainder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives of the actual analytic remainder on large circles.
The bounds will make its contribution to signed area tend to zero. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalCircleRemainder (R : ℝ) (T : ℂ → ℂ) (t : ℝ) : ℂ :=
    (unitCircleParam 0 R t)⁻¹^2 * T (unitCircleParam 0 R t)⁻¹

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalCircleAreaEstimate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic remainder contributes vanishing signed area. All
bounds here come from its actual values and first derivatives. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalAreaErrorBudget (K B C : ℝ) : ℝ :=
    2*Real.pi*K*(3*B+C)+2*Real.pi*B*(2*B+C)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlattening
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar map flattening an open set of prescribed values.
It is one-Lipschitz, stays uniformly close to the identity, and is locally
constant on the open set, even when that open set is dense. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Interval
noncomputable section
namespace CircleDomainRigidity

 def flattenValues (O : Set ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Oᶜ.indicator (fun _ => (1 : ℝ)) s

 theorem flattenValues_integrable {O : Set ℝ} (hO : MeasurableSet O) (a b : ℝ) :
    IntervalIntegrable (Oᶜ.indicator (fun _ => (1 : ℝ))) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).mono_fun
    ((measurable_const.indicator hO.compl).aestronglyMeasurable)
  exact Eventually.of_forall fun s => by by_cases hs : s ∈ O <;> simp [hs]

 theorem flattenValues_sub {O : Set ℝ} (hO : MeasurableSet O) (a b : ℝ) :
    flattenValues O b - flattenValues O a =
      ∫ s in a..b, Oᶜ.indicator (fun _ => (1 : ℝ)) s := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (flattenValues_integrable hO 0 a) (flattenValues_integrable hO a b)
  dsimp only [flattenValues]
  linarith

 theorem flattenValues_lipschitz {O : Set ℝ} (hO : MeasurableSet O) :
    LipschitzWith 1 (flattenValues O) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [flattenValues_sub hO]
  simpa only [Real.norm_eq_abs, one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Oᶜ.indicator (fun _ => (1 : ℝ))) (a := b) (b := a) (C := 1) (fun s _ => by by_cases hs : s ∈ O <;> simp [hs]))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlatteningApproximation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth primitives approximating the flattening map, with bounded
derivatives converging at every scalar value to the complement indicator. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Interval
noncomputable section
namespace CircleDomainRigidity

 theorem exists_flattenValues_smooth_approximation {O : Set ℝ} (hO : IsOpen O) :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (F n) ∧ F n 0 = 0 ∧ LipschitzWith 1 (F n)) ∧
      (∀ t, Tendsto (fun n => F n t) atTop (𝓝 (flattenValues O t))) ∧
      (∀ n t, deriv (F n) t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t, Tendsto (fun n => deriv (F n) t) atTop
        (𝓝 (Oᶜ.indicator (fun _ => (1 : ℝ)) t))) := by
  obtain ⟨b, hbs, hbc, hb⟩ := hO.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  let a : ℕ → ℝ → ℝ := fun n t => 1 - Real.smoothTransition (((n : ℝ)+1)*b t-1)
  have haSmooth (n : ℕ) : ContDiff ℝ 1 (a n) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul hbc).sub contDiff_const)) |>.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have haUnit (n : ℕ) (t : ℝ) : a n t ∈ Icc (0 : ℝ) 1 := by
    dsimp only [a]
    constructor <;> linarith [Real.smoothTransition.nonneg (((n : ℝ)+1)*b t-1),
      Real.smoothTransition.le_one (((n : ℝ)+1)*b t-1)]
  have haLim (t : ℝ) : Tendsto (fun n => a n t) atTop
      (𝓝 (Oᶜ.indicator (fun _ => (1 : ℝ)) t)) := by
    by_cases ht : t ∈ O
    · have hbpos : 0 < b t := by
        have hn : b t ≠ 0 := by simpa only [← hbs, mem_support] using ht
        exact lt_of_le_of_ne (hb (mem_range_self t)).1 (Ne.symm hn)
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / b t)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlarge : 2 ≤ ((n : ℝ)+1)*b t := by
        have hN' : 2 < (N : ℝ)*b t := (div_lt_iff₀ hbpos).mp hN
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      simp only [a, Real.smoothTransition.one_of_one_le (by linarith :
        1 ≤ ((n : ℝ)+1)*b t-1), sub_self, indicator_of_notMem (show t ∉ Oᶜ by simpa only [mem_compl_iff, not_not] using ht)]
    · have hbzero : b t = 0 := by
        by_contra hn
        exact ht (hbs ▸ (show t ∈ support b from hn))
      have heq : ∀ n, a n t = Oᶜ.indicator (fun _ => (1 : ℝ)) t := by
        intro n
        simp [a, hbzero, ht, Real.smoothTransition.zero_of_nonpos]
      simpa only [heq] using (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => Oᶜ.indicator (fun _ => (1 : ℝ)) t) atTop _)
  let F : ℕ → ℝ → ℝ := fun n t => ∫ s in (0 : ℝ)..t, a n s
  have hderiv (n : ℕ) (t : ℝ) : HasDerivAt (F n) (a n t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((haSmooth n).continuous.intervalIntegrable 0 t)
      (haSmooth n).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      (haSmooth n).continuous.continuousAt
  have hFderiv (n : ℕ) : deriv (F n) = a n := funext fun t => (hderiv n t).deriv
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t => (hderiv n t).differentiableAt,
      by rw [hFderiv]; exact (haSmooth n).continuous⟩, by simp [F], ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hinc := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((haSmooth n).continuous.intervalIntegrable 0 y)
      ((haSmooth n).continuous.intervalIntegrable y x)
    have he : F n x - F n y = ∫ s in y..x, a n s := by dsimp only [F] <;> linarith
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, he]
    simpa only [Real.norm_eq_abs, one_mul] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := a n) (a := y) (b := x) (C := 1)
        (fun s _ => by rw [Real.norm_eq_abs, abs_of_nonneg (haUnit n s).1]; exact (haUnit n s).2)
  · intro t
    let : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.mpr (by simp [uIoc, Real.volume_Ioc])
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ι (0 : ℝ) t)) (bound := fun _ => (1 : ℝ))
      (fun n => (haSmooth n).continuous.aestronglyMeasurable)
      (integrable_const (1 : ℝ))
      (fun n => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (haUnit n s).1]; exact (haUnit n s).2)
      (Eventually.of_forall haLim)
    dsimp only [F, flattenValues]
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact hlim.const_smul _
  · intro n t
    rw [hFderiv]
    exact haUnit n t
  · intro t
    simp only [hFderiv]
    exact haLim t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlatteningEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattening construction retains a genuine Sobolev witness. Its
squared gradient error is exactly the energy above the removed values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem flattenValues_zero (O : Set ℝ) : flattenValues O 0 = 0 := by
  simp [flattenValues]

 theorem flattenValues_norm_le {O : Set ℝ} (hO : MeasurableSet O) (t : ℝ) :
    ‖flattenValues O t‖ ≤ ‖t‖ := by
  simpa only [flattenValues_zero, dist_zero_right, NNReal.coe_one, one_mul] using
    (flattenValues_lipschitz hO).dist_le_mul t 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScaledCutoffEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dirichlet energy of a smooth planar cutoff is unchanged by dilation.
This supplies the fixed energy budget for disjoint concentric transition
annuli used to make cutoffs of arbitrarily small energy. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def dilatedCutoff (f : ℂ → ℝ) (r : ℝ) : ℂ → ℝ := fun z => f (r⁻¹ • z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnnularCutoffs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentric smooth cutoffs whose transition annuli are disjoint.
Each dilation has the same Dirichlet energy in dimension two. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def unitAnnularCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnnularRadii
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete decreasing sequence of separated transition radii. -/
open Set Function MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def annularRadius (R : ℝ) (n : ℕ) : ℝ := R / 4^(n+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DisjointCutoffAverages
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging cutoffs with disjoint transition sets divides their common
Dirichlet energy by the number of cutoffs. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def cutoffAverage (f : ℕ → ℂ → ℝ) (N : ℕ) : ℂ → ℝ :=
    fun z => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f i z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallEnergyCutoff
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth planar cutoffs with arbitrarily small Dirichlet energy,
constructed by averaging disjoint concentric transition annuli. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def annularAverage (R : ℝ) (N : ℕ) : ℂ → ℝ :=
    cutoffAverage (fun i => dilatedCutoff unitAnnularCutoff (annularRadius R i)) N

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredSmallCutoffs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-energy smooth cutoffs centered at each actual omitted source
point, with their support inside a prescribed ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def translatedCutoff (f : ℂ → ℝ) (c : ℂ) : ℂ → ℝ := fun z => f (z-c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TargetArea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Target area from the exterior area theorem

Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem, supplies the
area bound for the set omitted by a normalized univalent exterior map.
The numerical bound yields the target-area estimate by change of variables
and disjointness of the image and omitted disks.
-/

open MeasureTheory Metric Set Function Bornology
open scoped ENNReal

namespace CircleDomainRigidity

/-- The specialization of the published exterior area bound needed here.
The map is evaluated only outside the closed source disk. Univalence and
principal normalization are the hypotheses needed to obtain this bound
from the exterior area theorem; this predicate is its numerical conclusion. -/
def ExteriorOmittedAreaBound (f : ℂ → ℂ) (R : ℝ) : Prop :=
  volume ((f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi * R ^ 2)

/-- Finite image area also gives actual integrability of the squared
holomorphic derivative, so the Bochner integral cannot vanish by being
undefined. -/
theorem integrable_norm_deriv_sq_of_image_area_finite {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hinj : InjOn f U) (hfinite : volume (f '' U) ≠ ∞) :
    Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict U) := by
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ
  have hL : ∀ z ∈ U, HasFDerivWithinAt f (L z) U z :=
    fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (L z).det = ‖deriv f z‖ ^ 2 := by
    simp [L, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  have h1 : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (f '' U) volume :=
    integrableOn_const hfinite
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hU hL hinj (fun _ : ℂ => (1 : ℝ))).mp h1
  simpa [hdet, IntegrableOn] using h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanDiskImages
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem planar_interior_image
    {f : ℂ → ℂ} {G K : Set ℂ} (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hG : IsOpen G)
    (hi : InjOn f G) (hKG : K ⊆ G) : interior (f '' K) = f '' interior K := by
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

theorem planar_frontier_image
    {f : ℂ → ℂ} {G K : Set ℂ} (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hG : IsOpen G)
    (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, planar_interior_image hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PriorityPointTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity at a point end: early cutoffs are retained exactly, while
all later active scalar values approach the original point trace. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def priorityTruncatedValues (c : ℕ → ℝ) (a : ℝ) (N : ℕ) (n : ℕ) : ℝ :=
  if n < N then c n else a

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HolomorphicScalarEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two real coordinate differentials of a holomorphic map have the
same pointwise squared norm as its complex derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_real_fderiv_norm_sq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖fderiv ℝ (fun w => (f w).re) z‖^2 = ‖deriv f z‖^2 := by
  have h := (Complex.reCLM.hasFDerivAt.comp z
    (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv
  change ‖fderiv ℝ (Complex.reCLM ∘ f) z‖^2 = _
  rw [h, complexCovector_norm_sq, Complex.sq_norm, Complex.normSq_apply]
  change (1 * deriv f z).re^2+(Complex.I * deriv f z).re^2 = _
  simp only [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, zero_sub, neg_sq]
  ring


 theorem holomorphic_imag_fderiv_norm_sq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖fderiv ℝ (fun w => (f w).im) z‖^2 = ‖deriv f z‖^2 := by
  have h := (Complex.imCLM.hasFDerivAt.comp z
    (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv
  change ‖fderiv ℝ (Complex.imCLM ∘ f) z‖^2 = _
  rw [h, complexCovector_norm_sq, Complex.sq_norm, Complex.normSq_apply]
  change (1 * deriv f z).im^2+(Complex.I * deriv f z).im^2 = _
  simp only [one_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, zero_add]
  ring


 theorem holomorphic_coordinate_memLp {D U : Set ℂ} (hD : IsOpen D)
    (hU : MeasurableSet U) (hUD : U ⊆ D) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hE : Integrable (fun z => ‖deriv f z‖^2) (volume.restrict U)) :
    MemLp (fderiv ℝ (fun z => (f z).re)) 2 (volume.restrict U) ∧
      MemLp (fderiv ℝ (fun z => (f z).im)) 2 (volume.restrict U) := by
  have hcf : ContDiffOn ℝ ∞ f D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hr : ContDiffOn ℝ ∞ (fun z => (f z).re) D :=
    Complex.reCLM.contDiff.comp_contDiffOn hcf
  have hi : ContDiffOn ℝ ∞ (fun z => (f z).im) D :=
    Complex.imCLM.contDiff.comp_contDiffOn hcf
  have hrm := (hr.continuousOn_fderiv_of_isOpen hD (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono hUD
  have him := (hi.continuousOn_fderiv_of_isOpen hD (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono hUD
  constructor
  · apply (memLp_norm_iff (hrm.aestronglyMeasurable hU)).mp
    apply (memLp_two_iff_integrable_sq (hrm.norm.aestronglyMeasurable hU)).mpr
    apply hE.congr
    filter_upwards [ae_restrict_mem hU] with z hz
    exact (holomorphic_real_fderiv_norm_sq ((hf z (hUD hz)).differentiableAt (hD.mem_nhds (hUD hz)))).symm
  · apply (memLp_norm_iff (him.aestronglyMeasurable hU)).mp
    apply (memLp_two_iff_integrable_sq (him.norm.aestronglyMeasurable hU)).mpr
    apply hE.congr
    filter_upwards [ae_restrict_mem hU] with z hz
    exact (holomorphic_imag_fderiv_norm_sq ((hf z (hUD hz)).differentiableAt (hD.mem_nhds (hUD hz)))).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityFinite
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite recursive interpolation with the
priority-weight formula, for passage from local finite sums to the
countable interpolation. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*}

 def priorityList (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) : List ((E → ℝ) × ℝ) :=
  (List.range n).map (fun i => (χ i, c i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CurveCoareaInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plane-to-line specialization of Esmayli–Hajłasz, *The Coarea
Inequality*, Ann. Fenn. Math. 46 (2021), 965–991, Theorem 1.1,
DOI 10.5186/aasfm.2021.4654. The authors' manuscript is
https://arxiv.org/pdf/2006.00419 (Theorem 1.1, p. 1; proof, §7).

Only s=t=1, X=ℂ and Y=ℝ is retained. The Hausdorff normalization
constant is one in these dimensions. The source's measurability clause
requires finite H¹ measure and a measurable set in a boundedly compact
space; all these hypotheses are retained. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

 def PlanarLipschitzFiberCoarea : Prop :=
  ∀ (A : Set ℂ), MeasurableSet A → (μH[1] : Measure ℂ) A < ∞ →
    ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f →
      AEMeasurable (fun y => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {y})) volume ∧
      (∫⁻ y, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {y})) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure ℂ) A

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RecursiveTestBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive tolerances give an explicit summable error budget.
Each later step respects every earlier saved tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def savedToleranceMinimum (ε : ℝ) : List ℝ → ℝ
  | [] => min 1 ε
  | t :: ts => min t (savedToleranceMinimum ε ts)

 theorem savedToleranceMinimum_pos {ε : ℝ} (hε : 0 < ε) {ts : List ℝ}
    (hts : ∀ t ∈ ts, 0 < t) : 0 < savedToleranceMinimum ε ts := by
  induction ts with
  | nil => exact lt_min zero_lt_one hε
  | cons t ts ih =>
    exact lt_min (hts t (List.mem_cons_self)) (ih (fun x hx => hts x (List.mem_cons_of_mem t hx)))

 def recursiveTestBudget (ε : ℝ) (n : ℕ) (ts : List ℝ) : ℝ :=
  (1/2 : ℝ)^(n+3)*savedToleranceMinimum ε ts

 theorem recursiveTestBudget_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) {ts : List ℝ}
    (hts : ∀ t ∈ ts, 0 < t) : 0 < recursiveTestBudget ε n ts := by
  exact mul_pos (pow_pos (by norm_num) _) (savedToleranceMinimum_pos hε hts)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarFormPullback
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual exterior derivative of a pulled-back smooth planar one-form.
This is a calculus identity used in the construction of Green's formula. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def pulledPlanarForm (P Q : ℂ → ℝ) (F : (ℝ × ℝ) → ℂ)
    (v : ℝ × ℝ) (x : ℝ × ℝ) : ℝ :=
  P (F x) * ((fderiv ℝ F x) v).re + Q (F x) * ((fderiv ℝ F x) v).im


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularCurveNormalStrip
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normal-strip map of a regular smooth planar curve has
positive Jacobian at its central curve. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def curveNormalStrip (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  γ p.1 + p.2 • (Complex.I * deriv γ p.1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_QuarterTurnEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quarter turn preserves the actual gradient energy used by line payment. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def quarterTurn : ℂ ≃ₗᵢ[ℝ] ℂ := rotation
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

@[simp] theorem quarterTurn_apply (z : ℂ) : quarterTurn z = Complex.I * z := rfl

@[simp] theorem quarterTurn_one : quarterTurn 1 = Complex.I := by simp

@[simp] theorem quarterTurn_I : quarterTurn Complex.I = -1 := by simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RotatedLocalizedPayment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized line payment in any fixed direction, with unchanged source energy and hole costs. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- A line in the direction chosen by a unit complex multiplier. -/
def rotatedLine (a : Circle) (y x : ℝ) : ℂ := rotation a (horizontalLine y x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExteriorMaskReplacement
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Values outside a closed mask can be replaced by a constant on a
closed set separated from that mask and the retained core. This supplies
honest real branches for absent coordinates without changing any masked
differential, any masked cutoff cost, or any retained value. -/

open Set Filter Function MeasureTheory Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def exteriorMaskReplacement (W : Set (ℝ × ℝ)) (c : UnitAddCircle)
    (f : (ℝ × ℝ) → UnitAddCircle) : (ℝ × ℝ) → UnitAddCircle :=
  W.piecewise (fun _ => c) f

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleQuantileArcs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four positively separated arcs from a fixed countable circle family. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

def unitCircleCut (θ : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 θ

theorem unitCircleCut_mem (θ : UnitAddCircle) : unitCircleCut θ ∈ Ico (0 : ℝ) 1 := by
  simpa only [unitCircleCut, zero_add] using (AddCircle.equivIco 1 0 θ).property

theorem unitCircleCut_injective : Injective unitCircleCut := by
  intro x y h
  exact (AddCircle.equivIco 1 0).injective (Subtype.ext h)

theorem continuousAt_unitCircleCut {θ : UnitAddCircle} (hθ : θ ≠ 0) :
    ContinuousAt unitCircleCut θ :=
  continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco 1 0 hθ)

theorem measurable_unitCircleCut : Measurable unitCircleCut := by
  apply measurable_of_continuousOn_compl_singleton (0 : UnitAddCircle)
  intro θ hθ
  exact (continuousAt_unitCircleCut hθ).continuousWithinAt

def rationalCircleArc (l u : ℚ) : Set UnitAddCircle :=
  unitCircleCut ⁻¹' Ioo (l : ℝ) (u : ℝ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableArcIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel version of the explicit index, including a value on the
coincidence set. Its deck identity holds everywhere, before averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology Classical

/-! d13f23b's Borel structure on `C(X, Y)` (missing in our Mathlib), with `measurable_iff_eval`
proved here for a compact metric domain. -/


noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_normalizedArgument : Measurable normalizedArgument := by
  have h : Measurable (fun z : ℂ =>
      ((Complex.arg z / (2 * Real.pi) : ℝ) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
      (Complex.measurable_arg.div_const _)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact normalizedArgument_eq z

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactArcLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

section Restriction
variable {Ω : Type*} [MeasurableSpace Ω]

def restrictProbability (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (μ : Measure Ω) K ≠ 0) : ProbabilityMeasure Ω :=
  ⟨cond (μ : Measure Ω) K, cond_isProbabilityMeasure hK⟩

end Restriction

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCrossingInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pascoletti and Zanolin, *A Crossing Lemma for Annular Regions and Invariant
Sets with an Application to Planar Dynamical Systems*, Journal of Mathematics
(2013), Article 267393, DOI 10.1155/2013/267393, Lemma 7 and Remark 6, p. 3.
In the closed unit disk, two compact connected sets containing four cyclically
alternating boundary points intersect. The rational cut coordinate records
that cyclic order.
-/

open Set Function Metric

noncomputable section
namespace CircleDomainRigidity

def standardCirclePoint (θ : UnitAddCircle) : ℂ :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero θ : Circle)

theorem standardCirclePoint_injective : Injective standardCirclePoint :=
  Subtype.val_injective.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective

def UnitDiskAlternatingContinua : Prop :=
  ∀ (A B : Set ℂ), IsCompact A → IsConnected A →
    IsCompact B → IsConnected B →
    A ⊆ closedBall 0 1 → B ⊆ closedBall 0 1 →
    ∀ θ : Fin 4 → UnitAddCircle, StrictMono (unitCircleCut ∘ θ) →
      standardCirclePoint (θ 0) ∈ A → standardCirclePoint (θ 2) ∈ A →
      standardCirclePoint (θ 1) ∈ B → standardCirclePoint (θ 3) ∈ B →
      (A ∩ B).Nonempty

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryIndexMean
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the proved boundary indices against an atomless starting
law gives a continuous boundary coordinate with positive period one. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

def boundaryIndexMean (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) : ℝ :=
  ∫ a, (⌊x - unitCircleCut a⌋ : ℝ) ∂(β : Measure UnitAddCircle)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive angular parametrization and inverse of a centered Jordan boundary. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem standardCirclePoint_normalizedArgument {z : ℂ} (hz : ‖z‖ = 1) :
    standardCirclePoint (normalizedArgument z) = z := by
  change (Circle.exp (Complex.arg z * ((2 * Real.pi)⁻¹ * 1) *
    ((1 : ℝ)⁻¹ * (2 * Real.pi))) : ℂ) = z
  have he : Complex.arg z * ((2 * Real.pi)⁻¹ * 1) *
      ((1 : ℝ)⁻¹ * (2 * Real.pi)) = Complex.arg z := by
    field_simp
  rw [he]
  exact congrArg ((↑) : Circle → ℂ)
    (Circle.exp_arg ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩)

@[simp] theorem normalizedArgument_standardCirclePoint (θ : UnitAddCircle) :
    normalizedArgument (standardCirclePoint θ) = θ := by
  apply standardCirclePoint_injective
  exact standardCirclePoint_normalizedArgument (Circle.norm_coe _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleLoopCircle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def circleOfClosedPath {a : ℂ} (p : Path a a) : C(UnitAddCircle, ℂ) :=
  ⟨AddCircle.liftIco 1 0 p.extend,
    AddCircle.liftIco_zero_continuous (by simp) p.continuous_extend.continuousOn⟩

theorem circleOfClosedPath_apply {a : ℂ} (p : Path a a) (θ : UnitAddCircle) :
    circleOfClosedPath p θ = p ⟨unitCircleCut θ,
      (unitCircleCut_mem θ).1, (unitCircleCut_mem θ).2.le⟩ := by
  exact p.extend_apply ⟨(unitCircleCut_mem θ).1, (unitCircleCut_mem θ).2.le⟩

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

@[simp] theorem standardCirclePoint_zero : standardCirclePoint 0 = 1 := by
  simp only [standardCirclePoint, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero, Circle.coe_one]

theorem boundary_angle_pos {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    0 < unitCircleCut (normalizedArgument a) := by
  apply lt_of_le_of_ne (unitCircleCut_mem _).1
  intro h
  apply ha1
  rw [← standardCirclePoint_normalizedArgument ha]
  have he : normalizedArgument a = 0 := by
    have hc : (unitCircleCut (normalizedArgument a) : UnitAddCircle) = normalizedArgument a :=
      AddCircle.coe_equivIco
    rw [← h] at hc
    exact hc.symm
  rw [he, standardCirclePoint_zero]

def boundaryClosingArc (a : ℂ) (ha : ‖a‖ = 1) : Path 1 a where
  toFun t := standardCirclePoint ((unitCircleCut (normalizedArgument a) * (t : ℝ) : ℝ) : UnitAddCircle)
  continuous_toFun :=
    (continuous_subtype_val.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous).comp
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_subtype_val))
  source' := by
    change standardCirclePoint ((unitCircleCut (normalizedArgument a) * 0 : ℝ) : UnitAddCircle) = 1
    simp only [mul_zero, AddCircle.coe_zero, standardCirclePoint_zero]
  target' := by
    change standardCirclePoint ((unitCircleCut (normalizedArgument a) * 1 : ℝ) : UnitAddCircle) = a
    simp only [mul_one]
    rw [show (unitCircleCut (normalizedArgument a) : UnitAddCircle) = normalizedArgument a from
      AddCircle.coe_equivIco]
    exact standardCirclePoint_normalizedArgument ha

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneDisk
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Cayley coordinate for compactifying the upper half-plane rays. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def halfPlaneDisk (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

theorem halfPlaneDisk_den_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

theorem halfPlaneDisk_normSq (z : ℂ) :
    Complex.normSq (z + Complex.I) - Complex.normSq (z - Complex.I) = 4 * z.im := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

theorem halfPlaneDisk_norm_le {z : ℂ} (hz : 0 ≤ z.im) : ‖halfPlaneDisk z‖ ≤ 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm] at hn
  have hb : ‖z - Complex.I‖ ≤ ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (halfPlaneDisk_den_ne_zero hz))).mpr hb

theorem halfPlaneDisk_norm_lt {z : ℂ} (hz : 0 < z.im) : ‖halfPlaneDisk z‖ < 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm] at hn
  have hb : ‖z - Complex.I‖ < ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (halfPlaneDisk_den_ne_zero hz.le))).mpr hb

theorem halfPlaneDisk_norm_eq {z : ℂ} (hz : z.im = 0) : ‖halfPlaneDisk z‖ = 1 := by
  have hn := halfPlaneDisk_normSq z
  simp only [← Complex.sq_norm, hz, mul_zero] at hn
  have hb : ‖z - Complex.I‖ = ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [halfPlaneDisk, norm_div, hb,
    div_self (norm_ne_zero_iff.mpr (halfPlaneDisk_den_ne_zero hz.ge))]

theorem continuousOn_halfPlaneDisk : ContinuousOn halfPlaneDisk {z : ℂ | 0 ≤ z.im} :=
  (continuous_id.sub continuous_const).continuousOn.div
    (continuous_id.add continuous_const).continuousOn (fun _ h => halfPlaneDisk_den_ne_zero h)

theorem halfPlaneDisk_injOn : InjOn halfPlaneDisk {z : ℂ | 0 ≤ z.im} := by
  intro z hz w hw he
  have hc := (div_eq_div_iff (halfPlaneDisk_den_ne_zero hz)
    (halfPlaneDisk_den_ne_zero hw)).mp he
  have h : (z - w) * (2 * Complex.I) = 0 := by
    calc
      _ = (z - Complex.I) * (w + Complex.I) - (w - Complex.I) * (z + Complex.I) := by ring
      _ = 0 := sub_eq_zero.mpr hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (by simp))

theorem halfPlaneDisk_sub_one {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z - 1 = (-2 * Complex.I) / (z + Complex.I) := by
  unfold halfPlaneDisk
  field_simp [halfPlaneDisk_den_ne_zero hz]
  ring

theorem halfPlaneDisk_ne_one {z : ℂ} (hz : 0 ≤ z.im) : halfPlaneDisk z ≠ 1 := by
  intro h
  have he := halfPlaneDisk_sub_one hz
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at he
  rcases he with he | he
  · simp at he
  · exact halfPlaneDisk_den_ne_zero hz he

theorem halfPlaneDisk_dist_one_le {z : ℂ} (hz : 0 ≤ z.im) :
    dist (halfPlaneDisk z) 1 ≤ 2 / (z.im + 1) := by
  rw [dist_eq_norm, halfPlaneDisk_sub_one hz, norm_div, norm_mul]
  have hd : z.im + 1 ≤ ‖z + Complex.I‖ := by
    simpa only [Complex.add_im, Complex.I_im] using Complex.im_le_norm (z + Complex.I)
  have hp : 0 < z.im + 1 := by linarith
  simpa using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hd

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CayleyBoundaryOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real boundary of the half-plane is sent monotonically to the
positively oriented circle cut at the point at infinity. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def cayleyBoundaryAngle (x : ℝ) : ℝ := unitCircleCut (normalizedArgument (halfPlaneDisk x))

theorem cayleyBoundary_norm (x : ℝ) : ‖halfPlaneDisk x‖ = 1 :=
  halfPlaneDisk_norm_eq (by simp)

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

def puncturedArgument : C({z : ℂ // z ≠ 0}, UnitAddCircle) :=
  ⟨fun z => normalizedArgument z.val, by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_normalizedArgument z.property).comp continuous_subtype_val.continuousAt⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RayProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic half-plane projection sends every integer translate
back to the original terminal arc. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def diskRayProjection (z : ℂ) : ℂ :=
  (Real.exp (-z.im) : ℂ) * standardCirclePoint (z.re : UnitAddCircle)

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

abbrev ClosedUpperHalfPlane := {z : ℂ // 0 ≤ z.im}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dust-band estimates for the same local representative used in the
Sobolev construction. The lift only needs nonnegative height on the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def upperHalfPlaneClamp (z : ℂ) : ClosedUpperHalfPlane :=
  ⟨⟨z.re, max z.im 0⟩, le_max_right _ _⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LogarithmicCutCharts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two explicit argument cuts give local logarithmic branches on any
topological source of a continuous punctured-disk map. No local
connectedness of the source is needed for this chart construction. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def logarithmicCutChart (a : ℝ) (w : ℂ) : ℂ :=
  ((AddCircle.equivIco (1 : ℝ) a (normalizedArgument w) : ℝ) : ℂ) +
    ((-Real.log ‖w‖ : ℝ) : ℂ) * Complex.I

def logarithmicCutDomain {X : Type*} (F : X → ℂ) (S : Set X) (a : ℝ) : Set X :=
  {x | x ∈ S ∧ normalizedArgument (F x) ≠ (a : UnitAddCircle)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneDiskInverse
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse Cayley coordinate on the punctured closed disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def diskHalfPlane (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexPeriod
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deck translation adds the corresponding integer to the actual ray
index and hence to its expectation. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def ClosedUpperHalfPlane.translate (z : ClosedUpperHalfPlane) (n : ℤ) : ClosedUpperHalfPlane :=
  ⟨z.val + (n : ℂ), by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using z.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedLocalBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local bounded lifts can be used in the compact-band construction by
setting them to zero outside their patch. Their bands, local continuity,
and physical derivatives within the open patch are unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def localBranchRepresentative {X : Type*} (V : Set X) (u : X → ℝ) : X → ℝ := V.indicator u

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarSliceIntegrals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangles with arbitrary compact transverse sets, and their exact
slice integrals. Coordinates are Euclidean physical coordinates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

 def planarSliceBox (I J : Set ℝ) : Set ℂ :=
  {z | z.re ∈ I ∧ z.im ∈ J}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarAxisSwap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interchanging physical coordinate axes preserves area and exchanges
horizontal and vertical fiber tests. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 def planarAxisSwap (z : ℂ) : ℂ := ⟨z.im, z.re⟩

 @[simp] theorem planarAxisSwap_involutive (z : ℂ) : planarAxisSwap (planarAxisSwap z) = z := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DustSmoothingTolerance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete smoothing tolerance is positive off the dust, uniformly
small, and tends to zero at every dust point. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def dustSmoothingTolerance {X Y : Type*} [MetricSpace Y]
    (q : X → Y) (B : Set Y) (ε : ℝ) (x : X) : ℝ :=
  min ε (infDist (q x) B) / 2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GraphGridCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered grid selection for a finite list containing both real and
masked period coordinates. It uses their actual closed level graphs. -/

open Set Function Filter MeasureTheory

namespace CircleDomainRigidity.FiniteTransfer

def reciprocalGraphLevel (R : Set (Sphere × UnitAddCircle))
    (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) : Set Sphere :=
  {x | (x, ((θ + (k.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈ R}

def OrderedGraphGridCompatibility {S : Type*} {n : ℕ}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (θ : Fin n → ℝ) (N : ℕ)
    (A : Set Sphere) (σ : S → Sphere) : Prop :=
  ∀ x ∈ A, x ∉ range σ → ∀ j : Fin n,
    x ∈ ⋃ k, reciprocalGraphLevel (R j) (θ j) N k →
    ∀ I : Finset (Fin n), (∀ i ∈ I, i.val < j.val) → ∀ k : Fin n → Fin (N + 1),
      ¬ (connectedComponentIn
        (⋃ i ∈ I, reciprocalGraphLevel (R i) (θ i) N (k i)) x).Nontrivial

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MeasurableCircleGradient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic circle differential is Borel measurable for a Borel
circle coordinate. Two fixed cuts suffice on the continuity set; at a
discontinuity every real branch is nondifferentiable and its derivative
is zero. This supplies the actual gradient used in grid averaging. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem circleFDeriv_eq_fixed_cut
    {f : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hf : ContinuousAt f x)
    {a : ℝ} (ha : f x ≠ (a : UnitAddCircle)) :
    circleFDeriv f x = fderiv ℝ (circleBranch f a) x := by
  apply fderiv_lifts_eq
    (continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ (circleCut_ne f x)).comp hf))
    (continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ ha).comp hf))
  exact Eventually.of_forall fun y => (coe_circleBranch f _ y).trans (coe_circleBranch f _ y).symm

 theorem circleFDeriv_eq_zero_of_not_continuousAt
    {f : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hf : ¬ContinuousAt f x) :
    circleFDeriv f x = 0 := by
  apply fderiv_zero_of_not_differentiableAt
  intro hd
  apply hf
  have hc := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hd.continuousAt
  exact hc.congr (Eventually.of_forall (coe_circleBranch f _))

 theorem measurable_circleFDeriv {f : (ℝ × ℝ) → UnitAddCircle} (hf : Measurable f) :
    Measurable (circleFDeriv f) := by
  let C : Set (ℝ × ℝ) := {x | ContinuousAt f x}
  let A : Set (ℝ × ℝ) := {x | f x ≠ (0 : UnitAddCircle)}
  have hC : MeasurableSet C := measurableSet_of_continuousAt f
  have hA : MeasurableSet A := hf (isClosed_singleton.measurableSet.compl)
  have hhalf : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro he
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hh).mp he
    norm_num at heq
  have heq : circleFDeriv f = C.piecewise
      (A.piecewise (fderiv ℝ (circleBranch f 0)) (fderiv ℝ (circleBranch f (1 / 2))))
      (fun _ => 0) := by
    funext x
    by_cases hc : x ∈ C
    · rw [piecewise_eq_of_mem C _ _ hc]
      by_cases ha : x ∈ A
      · rw [piecewise_eq_of_mem A _ _ ha]
        exact circleFDeriv_eq_fixed_cut hc ha
      · rw [piecewise_eq_of_notMem A _ _ ha]
        apply circleFDeriv_eq_fixed_cut hc
        simpa only [A, mem_ofPred_eq, not_not.mp ha] using hhalf
    · rw [piecewise_eq_of_notMem C _ _ hc]
      exact circleFDeriv_eq_zero_of_not_continuousAt hc
  rw [heq]
  exact ((measurable_fderiv ℝ _).piecewise hA (measurable_fderiv ℝ _)).piecewise hC measurable_const

 theorem measurable_circleGradient {f : (ℝ × ℝ) → UnitAddCircle} (hf : Measurable f) :
    Measurable (circleGradient f) :=
  (((ContinuousLinearMap.measurable_apply (1, 0)).comp (measurable_circleFDeriv hf)).prodMk
    ((ContinuousLinearMap.measurable_apply (0, 1)).comp (measurable_circleFDeriv hf)))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SubfamilyOverride
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain a prescribed real subfamily when choosing local branches. -/

open Function Classical
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def subfamilyOverride {A L Y : Type*} (ι : A → L) (r : A → Y) (u : L → Y) (l : L) : Y :=
  if h : ∃ j, ι j = l then r (Classical.choose h) else u l

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceAnchor
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def roundJordanAt (c : ℂ) (r : ℝ) (hr : 0 < r) : ℂ ≃ₜ ℂ :=
  dilatedJordan (Homeomorph.addRight c) r hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundBoundaryStability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative persistence of the fixed-source boundary integral under
uniform changes of the map and center-radius changes of the target disk. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def roundDiskBoundaryPairing (f : ℝ → ℂ) (c : ℂ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
   ∫ t in (0 : ℝ)..1, infDist (f t) (closedBall c r) * deriv v t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ShrinkingRealModels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing transfer errors and shrinking physical marked neighborhoods. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def modelError (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem modelError_tendsto : Tendsto modelError atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SmallMeanBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small occupation and punctured hit norms used by compact arc
reduction imply the quantitative strict Stokes budget needed for exclusion. -/

open Set MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 def meanBudgetConstant (B : ℝ≥0) (R : ℝ) : ℝ :=
  2 * Real.sqrt Real.pi * R * (1 + 2 * (B : ℝ)) + 2 * Real.pi * R

 def meanBudgetTolerance (B : ℝ≥0) (R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (δ / (meanBudgetConstant B R + 1))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AxisSwapEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swapping the two Cartesian axes preserves Dirichlet energy and round disks. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

def axisSwap : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans quarterTurn

@[simp] theorem axisSwap_apply (z : ℂ) : axisSwap z = Complex.I * conj z := rfl

@[simp] theorem axisSwap_one : axisSwap 1 = Complex.I := by simp

@[simp] theorem axisSwap_I : axisSwap Complex.I = 1 := by simp

@[simp] theorem axisSwap_re (z : ℂ) : (axisSwap z).re = z.im := by simp

@[simp] theorem axisSwap_im (z : ℂ) : (axisSwap z).im = z.re := by simp

@[simp] theorem axisSwap_axisSwap (z : ℂ) : axisSwap (axisSwap z) = z := by
  apply Complex.ext <;> simp

@[simp] theorem axisSwap_symm_apply (z : ℂ) : axisSwap.symm z = axisSwap z := by
  apply axisSwap.injective
  rw [axisSwap.apply_symm_apply, axisSwap_axisSwap]

theorem axisSwap_preimage_closedBall (z : ℂ) (r : ℝ) :
    axisSwap ⁻¹' closedBall z r = closedBall (axisSwap z) r := by
  have h := axisSwap.toIsometryEquiv.preimage_closedBall z r
  change axisSwap ⁻¹' closedBall z r = closedBall (axisSwap.symm z) r at h
  simpa only [axisSwap_symm_apply] using h

theorem euclideanGradientEnergy_axisSwap {v : ℂ → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (axisSwap z)) :
    euclideanGradientEnergy (v ∘ axisSwap) z = euclideanGradientEnergy v (axisSwap z) := by
  have hd := (hv.hasFDerivAt.comp z axisSwap.hasFDerivAt).fderiv
  unfold euclideanGradientEnergy
  rw [hd]
  change (fderiv ℝ v (axisSwap z) (axisSwap 1)) ^ 2 +
    (fderiv ℝ v (axisSwap z) (axisSwap Complex.I)) ^ 2 = _
  rw [axisSwap_one, axisSwap_I]
  exact add_comm _ _

theorem integral_energy_axisSwap
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    (hi : IntegrableOn (euclideanGradientEnergy v) U) :
    IntegrableOn (euclideanGradientEnergy (v ∘ axisSwap)) (axisSwap ⁻¹' U) ∧
      (∫ z in axisSwap ⁻¹' U, euclideanGradientEnergy (v ∘ axisSwap) z) =
        ∫ z in U, euclideanGradientEnergy v z := by
  have hm := axisSwap.measurePreserving.restrict_preimage_emb
    axisSwap.toMeasurableEquiv.measurableEmbedding U
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ axisSwap) (axisSwap ⁻¹' U) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ axisSwap) =ᵐ[volume.restrict (axisSwap ⁻¹' U)]
      euclideanGradientEnergy v ∘ axisSwap := by
    filter_upwards [ae_restrict_mem (hU.preimage axisSwap.continuous).measurableSet] with z hz
    exact euclideanGradientEnergy_axisSwap
      ((hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact axisSwap.measurePreserving.setIntegral_preimage_emb
    axisSwap.toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) U

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_VerticalCirclePayment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-circle payment estimate in the second Cartesian direction. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def verticalLine (x y : ℝ) : ℂ := ⟨x, y⟩

@[simp] theorem axisSwap_horizontalLine (x y : ℝ) :
    axisSwap (horizontalLine x y) = verticalLine x y := by
  apply Complex.ext <;> simp [horizontalLine, verticalLine]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCurveLength
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength identity as a measure identity and its weighted version. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

noncomputable def curveOnSet (S : Set ℝ) (γ : ℝ → ℂ) : ℝ → ℂ := by
  classical
  exact S.piecewise γ (fun _ => 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DelayedSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve the first coordinate slot for the zero test while preserving
all selected tests and their order. -/

open Set Function

namespace CircleDomainRigidity

def delayedSelection {C : Type*} (A : ℕ → Set C) : ℕ → Set C
  | 0 => ∅
  | n + 1 => A n

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GreedyOpenSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable selection of compatible open barriers

A basis enumeration selects one admissible candidate at each finite stage.
If removing previous candidates allows a candidate with the same or larger open set,
every candidate
admissible for the final family has its open set covered by that family.
This is the selection step only; countability of unavailable ends is separate.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

variable {X C : Type*}

def greedyStep (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) : Set C := by
  classical
  exact if h : ∃ c, Allowed A c ∧ B n ⊆ U c then insert h.choose A else A

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteTupleCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered compatibility null sets survive arbitrary finite selections
of a prior tuple, including tuples with repeated labels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def levelRelation (H : ℕ → Set (UnitAddCircle × X)) (i : ℕ) : Set (X × UnitAddCircle) :=
  Prod.swap ⁻¹' H i

def OrderedLevelNullCompatibility (H : ℕ → Set (UnitAddCircle × X)) (F : Set X) : Prop :=
  ∀ (j n : ℕ) (l : Fin n → ℕ), (∀ k, l k < j) →
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin n → UnitAddCircle)))
      (freeComponentFailure F (levelRelation H j) (levelRelation H) l) = 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelDensityBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel density budgets for measurable families of finite measures. The
finite mass cap lets us use the jointly measurable kernel Radon–Nikodym
 derivative in Mathlib. -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]

def BoundedDensityBudget (σ μ : Measure X) (mass energy : ℝ≥0∞) : Prop :=
  μ univ ≤ mass ∧ ∃ g : X → ℝ≥0∞,
    Measurable g ∧ μ = σ.withDensity g ∧ (∫⁻ x, g x ^ 2 ∂σ) ≤ energy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DensityMassBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite reference measure turns the square-density estimate into the
uniform mass cap needed for the Borel family of candidate laws. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

def densityMassBound (σ : Measure X) (energy : ℝ≥0∞) : ℝ≥0∞ :=
  energy ^ (1 / 2 : ℝ) * (σ univ) ^ (1 / 2 : ℝ)

theorem densityMassBound_lt_top (σ : Measure X) [IsFiniteMeasure σ]
    {energy : ℝ≥0∞} (henergy : energy < ∞) : densityMassBound σ energy < ∞ := by
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top σ univ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilityMixtureMap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable pushforwards commute with the actual Borel probability mixture. -/

open MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {Ω T Z : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace Z]

theorem measurable_probability_pushforward (f : Ω → T) (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure Ω => μ.map (f := f) hf.aemeasurable) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map f hf).comp measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableSquareLawBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably prescribed visit bounds define a Borel family of laws and are
preserved under probability mixtures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

def CountableSquareLawBounds (v : S → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (μ : ProbabilityMeasure Ω) : Prop :=
  ∀ F : Finset S, ∑ s ∈ F, (∫⁻ w, v s w ∂(μ : Measure Ω)) ^ 2 ≤ budget

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TwoTerminalHitBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two distinguished terminal hits and the remaining square tails control
the sum appearing in the independent dust-meeting bound. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

def awayFromTwo {A : Type*} (p q : A) (a : A → ℝ≥0∞) : A → ℝ≥0∞ :=
  fun x => if x = p ∨ x = q then 0 else a x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PuncturedHitProduct
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two terminal contributions are controlled by the opposite punctured
square norm. No separate small individual-hit hypothesis is needed. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

def puncturedHit {S : Type*} (m : S → ℝ≥0∞) (U : Set S) (p : S) : S → ℝ≥0∞ :=
  fun s => if s ∈ U ∧ s ≠ p then m s else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BallPairKernel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized proximity kernels for two local arclength occupations. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def ballPairKernel (A : Set X) (a : ℝ≥0) : X × X → ℝ≥0∞ :=
  {p | p.1 ∈ A ∧ p.2 ∈ A ∧ dist p.1 p.2 < 2 * a}.indicator
    (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FourSampleBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four independent samples in the alternating collar argument.  Outer
measure suffices, so no extra measurability premise is imposed on meeting events. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def pairSample (i : Fin 2) (p : X × X) : X := if i = 0 then p.1 else p.2

def crossSample (i j : Fin 2) (p : (X × X) × (Y × Y)) : X × Y :=
  (pairSample i p.1, pairSample j p.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

structure RecursiveLawBudgets where
  occupationMass : ℝ≥0∞
  tupleMass : ℝ≥0∞
  energy : ℝ≥0∞
  visitConstant : ℝ≥0∞
  occupationMass_finite : occupationMass < ∞
  energy_finite : energy < ∞
  visitConstant_finite : visitConstant < ∞

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_NullLevelTuples
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null sets of scalar levels induce null sets of finite tagged tuples.
This also supplies a Borel description when the null sets are envelopes. -/

open Set Function MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def tuplesWithBadLevel (N : ℕ → Set UnitAddCircle) : Set LevelTuple :=
  {q | ∃ j : Fin (q.1 + 1), q.2.2 j ∈ N (q.2.1 j)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ParametricNullTuples
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel scalar-level envelopes remain Borel after forming finite tuples
and active slots, also when they depend on an earlier sampled path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω : Type*} [MeasurableSpace Ω]

def badTupleGraph (N : Ω → ℕ → Set UnitAddCircle) : Set (Ω × LevelTuple) :=
  {q | q.2 ∈ tuplesWithBadLevel (N q.1)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TuplePairCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent tuples satisfy every ordered compatibility test and have
no equal levels carrying the same label across the two tuples. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def TuplePairCompatible (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (q r : LevelTuple) : Prop :=
  (∀ i j, q.2.1 i = r.2.1 j → q.2.2 i ≠ r.2.2 j) ∧
  (∀ j (A : Finset (Fin (q.1 + 1))), (∀ k ∈ A, q.2.1 k < r.2.1 j) →
    ∀ x ∈ F, (r.2.2 j, x) ∈ H (r.2.1 j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (q.2.2 k, y) ∈ H (q.2.1 k)}) x).Nontrivial) ∧
  (∀ i (A : Finset (Fin (r.1 + 1))), (∀ k ∈ A, r.2.1 k < q.2.1 i) →
    ∀ x ∈ F, (q.2.2 i, x) ∈ H (q.2.1 i) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (r.2.2 k, y) ∈ H (r.2.1 k)}) x).Nontrivial)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ContinuousLawMeasurable
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weakly continuous probability kernels are measurable for the evaluation
sigma algebra. This follows from the open-set Portmanteau inequality and the
pi-system of open sets. -/

open Set MeasureTheory TopologicalSpace

noncomputable section

namespace CircleDomainRigidity

theorem measurable_of_continuous_probability
    {Z Ω : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [HasOuterApproxClosed Ω]
    {law : Z → ProbabilityMeasure Ω} (hlaw : Continuous law) : Measurable law := by
  have hm : Measurable (fun z => (law z : Measure Ω)) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      BorelSpace.measurable_eq isPiSystem_isOpen
    intro U hU
    have h : LowerSemicontinuous (fun z => (law z : Measure Ω) U) := by
      apply lowerSemicontinuous_iff_le_liminf.mpr
      intro z
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlaw.continuousAt hU
    exact h.measurable
  exact hm.subtype_mk

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteChoiceLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The probability law of an explicitly weighted finite choice, viewed on the
natural numbers so that a single trajectory space works at all tree vertices. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

def finiteChoiceLaw (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) : ProbabilityMeasure ℕ :=
  ⟨∑ i, ENNReal.ofReal (w i) • Measure.dirac i.val, by
    constructor
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FusionTrajectory
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A probability measure on Baire addresses with a prescribed finite-history
transition law. The first coordinate is a dummy; later coordinates choose the
successive children. -/

open Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity
namespace FusionTrajectory

abbrev History (n : ℕ) := ↥(Finset.Iic n) → ℕ

def history (n : ℕ) (h : History n) : List ℕ :=
  PiNat.res (fun i => h ⟨min (i + 1) n, Finset.mem_Iic.mpr (Nat.min_le_right (i + 1) n)⟩) n

def branch (x : ℕ → ℕ) (i : ℕ) : ℕ := x (i + 1)

variable (step : List ℕ → ProbabilityMeasure ℕ)

def transition (n : ℕ) : Kernel (History n) ℕ where
  toFun h := (step (history n h) : Measure ℕ)
  measurable' := measurable_of_countable _

instance instIsMarkovKernelHistoryNatTransition (n : ℕ) : IsMarkovKernel (transition step n) :=
  ⟨fun h => (step (history n h)).prop⟩

def measure : Measure (ℕ → ℕ) :=
  Kernel.trajMeasure (Measure.dirac 0) (transition step)

instance instIsProbabilityMeasureForallNatMeasure : IsProbabilityMeasure (measure step) := by
  unfold measure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FusionTrajectory
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClosedFusionScheme
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested closed sets with uniformly shrinking children give a continuous
branch-limit map on Baire space. This is the topological part of law fusion. -/

open Set Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

structure ClosedFusionScheme (Z : Type*) [MetricSpace Z] where
  carrier : List ℕ → Set Z
  closed : ∀ l, IsClosed (carrier l)
  nonempty : ∀ l, (carrier l).Nonempty
  child_subset : ∀ l a, carrier (a :: l) ⊆ carrier l
  child_dist : ∀ l a, ∀ x ∈ carrier (a :: l), ∀ y ∈ carrier (a :: l),
    dist x y ≤ 1 / ((l.length : ℝ) + 1)

namespace ClosedFusionScheme

variable {Z : Type*} [MetricSpace Z] (S : ClosedFusionScheme Z)

theorem vanishingDiam : CantorScheme.VanishingDiam S.carrier := by
  intro x
  have hb (n : ℕ) : Metric.ediam (S.carrier (PiNat.res x (n + 1))) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [PiNat.res_succ]
    apply Metric.ediam_le_of_forall_dist_le
    intro z hz w hw
    simpa only [PiNat.res_length] using S.child_dist (PiNat.res x n) (x n) z hz w hw
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs : Tendsto (fun n : ℕ => Metric.ediam (S.carrier (PiNat.res x (n + 1))))
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) hb
  exact (tendsto_add_atTop_iff_nat 1).mp hs

variable [CompleteSpace Z]

theorem total : (CantorScheme.inducedMap S.carrier).1 = univ :=
  CantorScheme.ClosureAntitone.map_of_vanishingDiam S.vanishingDiam
    (CantorScheme.Antitone.closureAntitone S.child_subset S.closed) S.nonempty

def limit (x : ℕ → ℕ) : Z :=
  (CantorScheme.inducedMap S.carrier).2 ⟨x, S.total.symm ▸ mem_univ x⟩

theorem continuous_limit : Continuous S.limit :=
  S.vanishingDiam.map_continuous.comp (continuous_id.subtype_mk _)

end ClosedFusionScheme
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteConvexSplit
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite convex separation used in path-law fusion. A convex family of
vectors missing the strict upper orthant has a nonnegative normalized separator.
No closedness of the vector family is required. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem finite_nonnegative_separator {I : Type*} [Fintype I] [Nonempty I]
    {V : Set (I → ℝ)} (hV : Convex ℝ V) (hVne : V.Nonempty) (b : ℝ)
    (hmiss : ∀ v ∈ V, ∃ i, v i ≤ b) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ v ∈ V, ∑ i, w i * v i ≤ b := by
  classical
  let U : Set (I → ℝ) := {v | ∀ i, b < v i}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {v : I → ℝ | b < v i} by ext v; simp [U]]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hUconvex : Convex ℝ U := by
    rw [show U = Set.univ.pi (fun _ : I => Ioi b) by ext v; simp [U]]
    exact convex_pi fun _ _ => convex_Ioi b
  have hdis : Disjoint U V := by
    apply disjoint_left.mpr
    intro v hv hvV
    obtain ⟨i, hi⟩ := hmiss v hvV
    exact (hv i).not_ge hi
  obtain ⟨f, t, hUf, hVf⟩ := geometric_hahn_banach_open hUconvex hUopen hV hdis
  let base : I → ℝ := fun _ => b + 1
  have hbase : base ∈ U := fun _ => by dsimp [base] <;> linarith
  have hfne : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := hVne
    have h1 := hUf base hbase
    have h2 := hVf v hv
    simp only [hz, zero_apply] at h1 h2
    linarith
  have hexp (v : I → ℝ) : f v = ∑ i, v i * f (Pi.single i 1) := by
    have hv : (∑ i, Pi.single i (v i)) = v := by ext i; simp
    conv_lhs => rw [← hv]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i <;> simp [hji]
    rw [he, map_smul]
    rfl
  have hsign (i : I) : f (Pi.single i 1) ≤ 0 := by
    by_contra h
    have hpos : 0 < f (Pi.single i 1) := lt_of_not_ge h
    obtain ⟨n, hn'⟩ := exists_nat_gt ((t - f base) / f (Pi.single i 1))
    have hn : t - f base < (n : ℝ) * f (Pi.single i 1) :=
      (div_lt_iff₀ hpos).mp hn'
    have hmem : base + (n : ℝ) • Pi.single i 1 ∈ U := by
      intro j
      change b < b + 1 + (n : ℝ) * (Pi.single i (1 : ℝ) : I → ℝ) j
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      by_cases hji : j = i <;> simp [hji]
      linarith
    have hlt := hUf _ hmem
    rw [map_add, map_smul] at hlt
    change f base + (n : ℝ) * f (Pi.single i 1) < t at hlt
    linarith
  let a : I → ℝ := fun i => -f (Pi.single i 1)
  let S : ℝ := ∑ i, a i
  have ha (i : I) : 0 ≤ a i := neg_nonneg.mpr (hsign i)
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => ha i
    apply lt_of_le_of_ne hS0
    intro hzero
    have hai : ∀ i, a i = 0 := by
      have hz : ∑ i, a i = 0 := hzero.symm
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hz i
        (Finset.mem_univ i)
    apply hfne
    ext v
    rw [hexp]
    simp only [zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : f (Pi.single i 1) = 0 := neg_eq_zero.mp (hai i)
    simp [hi]
  have hbound (v : I → ℝ) (hv : v ∈ V) : ∑ i, a i * v i ≤ b * S := by
    by_contra h
    have hgap : 0 < (∑ i, a i * v i) - b * S := sub_pos.mpr (lt_of_not_ge h)
    let δ := ((∑ i, a i * v i) - b * S) / (2 * S)
    have hδ : 0 < δ := div_pos hgap (by positivity)
    have hu : (fun _ : I => b + δ) ∈ U := fun _ => by dsimp [U] <;> linarith
    have hlt := lt_of_lt_of_le (hUf _ hu) (hVf v hv)
    rw [hexp, hexp] at hlt
    have he1 : (∑ i, (b + δ) * f (Pi.single i 1)) = -(b + δ) * S := by
      dsimp only [S, a]
      rw [← Finset.mul_sum, Finset.sum_neg_distrib]
      ring
    have he2 : (∑ i, v i * f (Pi.single i 1)) = -(∑ i, a i * v i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [a]
      ring
    rw [he1, he2] at hlt
    have hδeq : δ * (2 * S) = (∑ i, a i * v i) - b * S :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨fun i => a i / S, fun i => div_nonneg (ha i) hS.le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hS.ne'
  · intro v hv
    have he : (∑ i, a i / S * v i) = (∑ i, a i * v i) / S := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact (div_le_iff₀ hS).mpr (hbound v hv)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedUpperIntegral
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak upper semicontinuity of integrals of bounded upper semicontinuous tests.
For a test between zero and one, its integral is the product measure of its
closed hypograph in the product with the unit interval. Thus the closed-set Portmanteau theorem suffices. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal unitInterval

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

def unitIntervalProbability : ProbabilityMeasure I := ⟨volume, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

omit [SecondCountableTopology X] in
theorem hypograph_probability_eq_lintegral
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (μ : ProbabilityMeasure X) :
    ((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I))
      {p | (p.2 : ℝ) ≤ f p.1} = ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) := by
  have hH : IsClosed {p : X × I | (p.2 : ℝ) ≤ f p.1} :=
    hf.IsClosed_hypograph.preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  change (μ : Measure X).prod (volume : Measure I) _ = _
  rw [Measure.prod_apply hH.measurableSet]
  apply lintegral_congr
  intro x
  have he : (Prod.mk x ⁻¹' {p : X × I | (p.2 : ℝ) ≤ f p.1}) =
      Iic (⟨f x, hf0 x, hf1 x⟩ : I) := rfl
  rw [he, unitInterval.volume_Iic]

theorem upperSemicontinuous_integral_unit_bounded
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) := by
  let H : Set (X × I) := {p | (p.2 : ℝ) ≤ f p.1}
  have hH : IsClosed H := hf.IsClosed_hypograph.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hprod : Continuous (fun μ : ProbabilityMeasure X => μ.prod unitIntervalProbability) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_const)
  have hupper : UpperSemicontinuous (fun μ : ProbabilityMeasure X =>
      ((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I)) H) := by
    apply upperSemicontinuous_iff_limsup_le.mpr
    intro μ
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprod.continuousAt hH
  have heq (μ : ProbabilityMeasure X) :
      ∫ x, f x ∂(μ : Measure X) =
        (((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I)) H).toReal := by
    rw [hypograph_probability_eq_lintegral hf hf0 hf1]
    have he := integral_toReal (hf.measurable.ennreal_ofReal.aemeasurable (μ := (μ : Measure X)))
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    simpa only [ENNReal.toReal_ofReal (hf0 _)] using he
  intro μ c hc
  change (∫ x, f x ∂(μ : Measure X)) < c at hc
  change ∀ᶠ ν : ProbabilityMeasure X in 𝓝 μ, (∫ x, f x ∂(ν : Measure X)) < c
  rw [heq] at hc
  have hfin : ((μ.prod unitIntervalProbability : Measure (X × I)) H) ≠ ∞ := measure_ne_top _ _
  filter_upwards [hupper μ (ENNReal.ofReal c)
    ((ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hc)] with ν hν
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hν

theorem upperSemicontinuous_integral_bounded
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 0 < M) (hfM : ∀ x, f x ≤ M) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) := by
  let g : X → ℝ := fun x => f x / M
  have hg : UpperSemicontinuous g :=
    (continuous_id.div_const M).comp_upperSemicontinuous hf
      (fun _ _ h => div_le_div_of_nonneg_right h hM.le)
  have hg0 (x : X) : 0 ≤ g x := div_nonneg (hf0 x) hM.le
  have hg1 (x : X) : g x ≤ 1 := (div_le_one hM).mpr (hfM x)
  have hu := upperSemicontinuous_integral_unit_bounded hg hg0 hg1
  have heq : (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) =
      fun μ : ProbabilityMeasure X => M * ∫ x, g x ∂(μ : Measure X) := by
    funext μ
    rw [← integral_const_mul]
    congr 1
    funext x
    dsimp only [g]
    field_simp
  rw [heq]
  exact (continuous_const.mul continuous_id).comp_upperSemicontinuous hu
    (fun _ _ h => mul_le_mul_of_nonneg_left h hM.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactLawSplit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite mixture uniformly controls all compact test configurations if every
probability distribution on configurations admits a good candidate. This is the
finite splitting step of the manuscript's fusion argument. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def probabilityConvexCombination {T : Type*} [MeasurableSpace T]
    (μ ν : ProbabilityMeasure T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ProbabilityMeasure T :=
  ⟨ENNReal.ofReal a • (μ : Measure T) + ENNReal.ofReal b • (ν : Measure T), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]⟩

theorem integral_probabilityConvexCombination {T : Type*} [MeasurableSpace T]
    (μ ν : ProbabilityMeasure T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {f : T → ℝ}
    (hμ : Integrable f (μ : Measure T)) (hν : Integrable f (ν : Measure T)) :
    ∫ t, f t ∂(probabilityConvexCombination μ ν a b ha hb hab : Measure T) =
      a * (∫ t, f t ∂(μ : Measure T)) + b * ∫ t, f t ∂(ν : Measure T) := by
  change ∫ t, f t ∂(ENNReal.ofReal a • (μ : Measure T) +
    ENNReal.ofReal b • (ν : Measure T)) = _
  rw [integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul]

theorem convex_integral_vectors {I T : Type*} [MeasurableSpace T]
    (f : I → T → ℝ) (hf : ∀ i (μ : ProbabilityMeasure T), Integrable (f i) (μ : Measure T)) :
    Convex ℝ (Set.range (fun μ : ProbabilityMeasure T => fun i => ∫ t, f i t ∂(μ : Measure T))) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  refine ⟨probabilityConvexCombination μ ν a b ha hb hab, ?_⟩
  funext i
  exact integral_probabilityConvexCombination μ ν a b ha hb hab (hf i μ) (hf i ν)

theorem exists_finite_compact_law_split
    {T Z : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (f : Z → T → ℝ) (A : Set Z)
    (hf : ∀ z ∈ A, UpperSemicontinuous (f z))
    (hf0 : ∀ z ∈ A, ∀ t, 0 ≤ f z t)
    {M : ℝ} (hM : 0 < M) (hfM : ∀ z ∈ A, ∀ t, f z t ≤ M)
    {b ε : ℝ} (hε : 0 < ε)
    (htest : ∀ μ : ProbabilityMeasure T, ∃ z ∈ A, ∫ t, f z t ∂(μ : Measure T) ≤ b) :
    ∃ (n : ℕ) (z : Fin n → Z) (w : Fin n → ℝ),
      (∀ i, z i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ t, ∑ i, w i * f (z i) t ≤ b + ε := by
  classical
  let U : A → Set (ProbabilityMeasure T) := fun z =>
    {μ | (∫ t, f z.val t ∂(μ : Measure T)) < b + ε}
  have hU (z : A) : IsOpen (U z) :=
    (upperSemicontinuous_integral_bounded (hf z.val z.property)
      (hf0 z.val z.property) hM (hfM z.val z.property)).isOpen_preimage _
  have hcover : (univ : Set (ProbabilityMeasure T)) ⊆ ⋃ z : A, U z := by
    intro μ _
    obtain ⟨z, hz, hzt⟩ := htest μ
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, lt_of_le_of_lt hzt (by linarith)⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hFne : F.Nonempty := by
    by_contra h
    have hm := hF (mem_univ (diracProba (Classical.arbitrary T)))
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hm
  let I := {z : A // z ∈ F}
  let : Fintype I := inferInstanceAs (Fintype F)
  let : Nonempty I := ⟨⟨hFne.choose, hFne.choose_spec⟩⟩
  let g : I → T → ℝ := fun i => f i.val.val
  have hg (i : I) (μ : ProbabilityMeasure T) : Integrable (g i) (μ : Measure T) := by
    apply Integrable.of_bound (hf i.val.val i.val.property).measurable.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _ i.val.property t)]
      exact hfM _ i.val.property t
  let V : Set (I → ℝ) := Set.range (fun μ : ProbabilityMeasure T =>
    fun i => ∫ t, g i t ∂(μ : Measure T))
  have hV : Convex ℝ V := convex_integral_vectors g hg
  have hVne : V.Nonempty := ⟨_, Set.mem_range_self (diracProba (Classical.arbitrary T))⟩
  have hmiss : ∀ v ∈ V, ∃ i, v i ≤ b + ε := by
    rintro v ⟨μ, rfl⟩
    obtain ⟨z, hz, hzμ⟩ := mem_iUnion₂.mp (hF (mem_univ μ))
    exact ⟨⟨z, hz⟩, le_of_lt hzμ⟩
  obtain ⟨w, hw, hw1, hwV⟩ := finite_nonnegative_separator hV hVne (b + ε) hmiss
  have hpoints (t : T) : ∑ i, w i * f i.val.val t ≤ b + ε := by
    have h := hwV _ (Set.mem_range_self (diracProba t))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (integral_dirac' (g i) t (hf i.val.val i.val.property).measurable.stronglyMeasurable).symm
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => (e i).val.val, fun i => w (e i),
    fun i => (e i).val.property, fun i => hw (e i), ?_, ?_⟩
  · exact (e.sum_comp w).trans hw1
  · intro t
    exact (e.sum_comp (fun i => w i * f i.val.val t)).le.trans (hpoints t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PublishedProbabilityTopology
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Probability-space topology for fusion.

A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
Theorems 17.23 and 17.24, pp. 112–113, give the Polish weak topology
on probability laws on a Polish space and identify its Borel sigma algebra
with the evaluation sigma algebra. The following paragraph gives the
standard Borel consequence.
-/

open MeasureTheory

namespace CircleDomainRigidity

def StandardBorelProbabilityLaws (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  StandardBorelSpace (ProbabilityMeasure Ω)

def PolishProbabilityLaws (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] : Prop :=
  PolishSpace (ProbabilityMeasure Ω) ∧ BorelSpace (ProbabilityMeasure Ω)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstUncountableRecursion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first uncountable well-order has countable strict initial segments.
This is the precise index set for retaining every earlier path law. -/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

noncomputable section
namespace CircleDomainRigidity

abbrev FirstUncountable := (ω₁ : Ordinal.{0}).ToType

instance instCountableElemFirstUncountableIio (i : FirstUncountable) : Countable (Iio i) := by
  let f : Iio i → Iio i.toOrd.val := fun j =>
    ⟨j.val.toOrd.val, (Ordinal.ToType.mk.symm.lt_iff_lt).mpr j.property⟩
  have hf : Injective f := by
    intro j k h
    apply Subtype.ext
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : Iio i.toOrd.val => z.val) h
  let := (show (Iio i.toOrd.val).Countable by
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
    exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp i.toOrd.property)).to_subtype
  exact Function.Injective.countable hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ExactBandMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Haar length of a projected interval. A band of width at most
one is measured without loss, so its actual coordinate weight controls
every bounded local real lift of that band. -/

open Set Function MeasureTheory Metric Filter
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem addCircle_image_Icc_eq_closedBall (a b : ℝ) :
    ((↑) : ℝ → UnitAddCircle) '' Icc a b =
      closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := by
  apply Subset.antisymm (addCircle_image_Icc_subset_closedBall a b)
  intro θ hθ
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hy : y ∈ ((↑) : ℝ → UnitAddCircle) ⁻¹'
      closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := hθ
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  rw [mem_closedBall, Real.dist_eq] at hz
  simp only [zsmul_eq_mul, mul_one] at hz
  refine ⟨y - (z : ℝ), ?_, ?_⟩
  · obtain ⟨hl, hu⟩ := abs_le.mp hz
    constructor <;> linarith
  · apply unitAddCircle_eq_iff_exists_int.mpr
    refine ⟨-z, ?_⟩
    push_cast
    ring

 theorem volume_addCircle_image_Icc (a b : ℝ) :
    volume (((↑) : ℝ → UnitAddCircle) '' Icc a b) =
      ENNReal.ofReal (min 1 (b - a)) := by
  rw [addCircle_image_Icc_eq_closedBall, AddCircle.volume_closedBall]
  congr 2
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagLevelSingleton
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At an independent compatible level, a free contact inside an active
tag belongs to a singleton component of that level. This is the first
topological step of the generic-intersection argument. -/

open Set Function
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

def singleLevelTuple (i : ℕ) (θ : UnitAddCircle) : LevelTuple :=
  ⟨0, (fun _ => i), fun _ => θ⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedTupleCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-tuple comparison uses the inherited coordinate order,
which need not be the order of its natural-number enumeration. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [TopologicalSpace X]

def RankedLevelNullCompatibility {L : Type*} [LT L] (rank : ℕ → L) (H : ℕ → Set (UnitAddCircle × X)) (F : Set X) : Prop :=
  ∀ (j n : ℕ) (l : Fin n → ℕ), (∀ k, rank (l k) < rank j) →
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin n → UnitAddCircle)))
      (freeComponentFailure F (levelRelation H j) (levelRelation H) l) = 0


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedTuplePairs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent tuple null sets with the inherited coordinate order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [TopologicalSpace X]

def RankedTuplePairCompatible {L : Type*} [LT L] (rank : ℕ → L) (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (q r : LevelTuple) : Prop :=
  (∀ i j, q.2.1 i = r.2.1 j → q.2.2 i ≠ r.2.2 j) ∧
  (∀ j (A : Finset (Fin (q.1 + 1))), (∀ k ∈ A, rank (q.2.1 k) < rank (r.2.1 j)) →
    ∀ x ∈ F, (r.2.2 j, x) ∈ H (r.2.1 j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (q.2.2 k, y) ∈ H (q.2.1 k)}) x).Nontrivial) ∧
  (∀ i (A : Finset (Fin (r.1 + 1))), (∀ k ∈ A, rank (r.2.1 k) < rank (q.2.1 i)) →
    ∀ x ∈ F, (q.2.2 i, x) ∈ H (q.2.1 i) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {y | (r.2.2 k, y) ∈ H (r.2.1 k)}) x).Nontrivial)


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_VerticalFrontierCrossings
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments from nested bounded regions

On any vertical line meeting the inner region, the bottommost points of
the inner and outer closures lie on their frontiers. Strict containment
puts the outer point strictly below. Thus prescribed zero/one
frontier values provide the crossing segments needed by line payment.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_verticalLine (x : ℝ) : Continuous (verticalLine x) :=
  Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nontrivial continuum has positive transverse overlap with any nearby anchor ball after
choosing a suitable direction. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

def unitOfNonzero (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hz))⟩

theorem one_add_im_ne_zero (t : ℝ) : (1 + (t : ℂ) * Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

def tiltedUnit (t : ℝ) : Circle :=
  unitOfNonzero (1 + (t : ℂ) * Complex.I) (one_add_im_ne_zero t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OrderedPhysicalCollar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual centered Jordan boundary admits a smooth physical circuit
whose disk angle is increasing from zero to one. Only the starting point
and direction of the original regular circuit are changed. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def orientedParameter (a : ℝ) (reverse : Bool) (t : ℝ) : ℝ :=
  if reverse then a + (1 - t) else a + t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SupportedProbability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A probability measure supported on a measurable set is the pushforward
of an actual probability measure on that set. -/

open Set Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

 def supportedProbability (μ : ProbabilityMeasure X) (A : Set X)
    (hA : MeasurableSet A) (hmem : ∀ᵐ x ∂(μ : Measure X), x ∈ A) : ProbabilityMeasure A :=
  ⟨(μ : Measure X).comap Subtype.val, ⟨by
    rw [(MeasurableEmbedding.subtype_coe hA).comap_apply, image_univ, Subtype.range_coe]
    exact (measure_congr (Filter.eventuallyEq_univ.mpr hmem)).trans (measure_univ)⟩⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PeriodicBoundaryPairing
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A boundary pairing defined for continuous lifts is stable under
uniform perturbations of the same period. For smooth lifts it is the
ordinary boundary integral, by integration by parts. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def liftedBoundaryPairing (φ dφ v : ℝ → ℝ) : ℝ :=
  φ 1 * v 1 - φ 0 * v 0 - ∫ x in (0 : ℝ)..1, dφ x * v x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedSelectedLevels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerating the selected labels does not change their inherited order.
This supplies exactly the ranked compatibility used by the tag-law proofs. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def selectedCoordinateEnumeration : ℕ ≃ ℕ ⊕ₗ ℕ :=
  Equiv.natSumNatEquivNat.symm.trans toLex

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RoundOuterCore
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def roundOuterJordan (R : ℝ) (hR : 0 < R) : ℂ ≃ₜ ℂ :=
  dilatedJordan (Homeomorph.refl ℂ) R hR

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

 theorem intervalFiberHull_value_of_continuousAt
    {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : ℝ} (ht : (x, t) ∈ intervalFiberHull (clusterGraph U f)) :
    t = f x := by
  obtain ⟨a, b, s, ha, hb, _, ht⟩ := mem_intervalFiberHull_iff.mp ht
  rw [clusterGraph_fiber_eq_of_continuousAt hf ha,
    clusterGraph_fiber_eq_of_continuousAt hf hb] at ht
  nlinarith [ht]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_BoundedScalarFillings
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable fillings on the whole plane, equal to the clipped
transferred scalar in the domain and constant on each actual round hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def clipScalar (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clipScalar_lipschitz : LipschitzWith 1 clipScalar :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem clipScalar_mem (t : ℝ) : clipScalar t ∈ Icc 0 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clipScalar_eq {t : ℝ} (ht : t ∈ Icc 0 1) : clipScalar t = t := by
  rw [clipScalar, min_eq_right ht.2, max_eq_right ht.1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClippedScalarEnergy
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping the transferred scalar preserves its source values and does
not increase its actual differential energy, including on the clipping levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem clipScalar_of_nonpos {t : ℝ} (ht : t ≤ 0) : clipScalar t = 0 := by
  rw [clipScalar, min_eq_right (ht.trans zero_le_one), max_eq_left ht]

theorem clipScalar_of_one_le {t : ℝ} (ht : 1 ≤ t) : clipScalar t = 1 := by
  rw [clipScalar, min_eq_left ht, max_eq_right zero_le_one]

theorem fderiv_clipScalar_comp {u : ℂ → ℝ} {z : ℂ} (hu : ContinuousAt u z) :
    fderiv ℝ (clipScalar ∘ u) z = 0 ∨
      fderiv ℝ (clipScalar ∘ u) z = fderiv ℝ u z := by
  by_cases h0 : u z ≤ 0
  · left
    apply IsLocalMin.fderiv_eq_zero
    exact Eventually.of_forall fun y => by
      change clipScalar (u z) ≤ clipScalar (u y)
      rw [clipScalar_of_nonpos h0]
      exact (clipScalar_mem _).1
  · by_cases h1 : 1 ≤ u z
    · left
      apply IsLocalMax.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u y) ≤ clipScalar (u z)
        rw [clipScalar_of_one_le h1]
        exact (clipScalar_mem _).2
    · right
      apply EventuallyEq.fderiv_eq
      have h := hu.tendsto (Ioo_mem_nhds (lt_of_not_ge h0) (lt_of_not_ge h1))
      filter_upwards [h] with y hy
      exact clipScalar_eq ⟨hy.1.le, hy.2.le⟩

theorem euclideanGradientEnergy_clipScalar_le {u : ℂ → ℝ} {z : ℂ}
    (hu : ContinuousAt u z) :
    euclideanGradientEnergy (clipScalar ∘ u) z ≤ euclideanGradientEnergy u z := by
  rcases fderiv_clipScalar_comp hu with h | h
  · simp only [euclideanGradientEnergy, h, zero_apply, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · simp only [euclideanGradientEnergy, h, le_refl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledScalarL2
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two ordinary differential components of the finite filled scalar
are in planar L², with the source energy as their combined bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem memLp_partials_of_integrable_euclidean_energy {f : ℂ → ℝ}
    (h : Integrable (euclideanGradientEnergy f)) :
    MemLp (fun z => fderiv ℝ f z 1) 2 volume ∧
      MemLp (fun z => fderiv ℝ f z Complex.I) 2 volume := by
  have hm₁ := measurable_fderiv_apply_const ℝ f (1 : ℂ)
  have hm₂ := measurable_fderiv_apply_const ℝ f Complex.I
  constructor
  · apply (memLp_two_iff_integrable_sq hm₁.aestronglyMeasurable).mpr
    apply h.mono' (hm₁.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_right (sq_nonneg _)
  · apply (memLp_two_iff_integrable_sq hm₂.aestronglyMeasurable).mpr
    apply h.mono' (hm₂.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (sq_nonneg _)

open FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ThreeL2WeakLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common weakly convergent subsequence for one scalar and its two
differential components, allowing the scalar measure to be spherical. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_three_L2_weak_limits
    {X : Type*} [MeasurableSpace X] (μ₀ μ₁ μ₂ : Measure X)
    [IsSeparable μ₀] [IsSeparable μ₁] [IsSeparable μ₂]
    (u₀ u₁ u₂ : ℕ → X → ℝ)
    (h₀ : ∀ n, MemLp (u₀ n) 2 μ₀) (h₁ : ∀ n, MemLp (u₁ n) 2 μ₁)
    (h₂ : ∀ n, MemLp (u₂ n) 2 μ₂) (C₀ C₁ C₂ : ℝ)
    (hb₀ : ∀ n, ‖(h₀ n).toLp (u₀ n)‖ ≤ C₀)
    (hb₁ : ∀ n, ‖(h₁ n).toLp (u₁ n)‖ ≤ C₁)
    (hb₂ : ∀ n, ‖(h₂ n).toLp (u₂ n)‖ ≤ C₂) :
    ∃ (V : Lp ℝ 2 μ₀) (G₁ : Lp ℝ 2 μ₁) (G₂ : Lp ℝ 2 μ₂)
      (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ w : Lp ℝ 2 μ₀, Tendsto (fun n => ∫ x, u₀ (σ n) x * w x ∂μ₀)
        atTop (𝓝 (∫ x, V x * w x ∂μ₀))) ∧
      (∀ w : Lp ℝ 2 μ₁, Tendsto (fun n => ∫ x, u₁ (σ n) x * w x ∂μ₁)
        atTop (𝓝 (∫ x, G₁ x * w x ∂μ₁))) ∧
      (∀ w : Lp ℝ 2 μ₂, Tendsto (fun n => ∫ x, u₂ (σ n) x * w x ∂μ₂)
        atTop (𝓝 (∫ x, G₂ x * w x ∂μ₂))) := by
  obtain ⟨V, _, s₀, hs₀, hv⟩ := exists_L2_weak_subsequence μ₀ u₀ h₀ C₀ hb₀
  obtain ⟨G₁, _, s₁, hs₁, hg₁⟩ := exists_L2_weak_subsequence μ₁ (u₁ ∘ s₀)
    (fun n => h₁ (s₀ n)) C₁ (fun n => hb₁ (s₀ n))
  obtain ⟨G₂, _, s₂, hs₂, hg₂⟩ := exists_L2_weak_subsequence μ₂ (u₂ ∘ s₀ ∘ s₁)
    (fun n => h₂ (s₀ (s₁ n))) C₂ (fun n => hb₂ (s₀ (s₁ n)))
  refine ⟨V, G₁, G₂, s₀ ∘ s₁ ∘ s₂, hs₀.comp (hs₁.comp hs₂), ?_, ?_, ?_⟩
  · intro w
    exact (hv w).comp (hs₁.tendsto_atTop.comp hs₂.tendsto_atTop)
  · intro w
    exact (hg₁ w).comp hs₂.tendsto_atTop
  · exact hg₂

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarWeakLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common subsequence of the actual finite scalar fillings and their
two differentials. The scalar is bounded in spherical L²; the differentials
are bounded in ordinary planar L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def planarSphericalArea : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z))

instance finitePlanarSphericalArea : IsFiniteMeasure planarSphericalArea :=
  isFiniteMeasure_withDensity integrable_sphericalAreaDensity.lintegral_lt_top.ne

instance separablePlanarSphericalArea : IsSeparable planarSphericalArea := by
  unfold planarSphericalArea
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedScalarTests
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact planar tests are legitimate dual tests for spherical L² after
dividing by the explicit positive stereographic area density. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def weightedScalarTest (ψ : ℂ → ℝ) (z : ℂ) : ℝ := ψ z / sphericalAreaDensity z

 theorem weightedScalarTest_continuous {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    Continuous (weightedScalarTest ψ) :=
  hψ.div continuous_sphericalAreaDensity (fun z => (sphericalAreaDensity_pos z).ne')

 theorem weightedScalarTest_compact {ψ : ℂ → ℝ} (hs : HasCompactSupport ψ) :
    HasCompactSupport (weightedScalarTest ψ) := by
  change HasCompactSupport (fun z => ψ z * (sphericalAreaDensity z)⁻¹)
  exact hs.mul_right

 theorem weightedScalarTest_memLp {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    MemLp (weightedScalarTest ψ) 2 planarSphericalArea :=
  (weightedScalarTest_continuous hψ).memLp_of_hasCompactSupport (weightedScalarTest_compact hs)

 theorem integral_weightedScalarTest (u ψ : ℂ → ℝ) :
    (∫ z, u z * weightedScalarTest ψ z ∂planarSphericalArea) = ∫ z, u z * ψ z := by
  rw [planarSphericalArea, integral_withDensity_eq_integral_toReal_smul
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change (ENNReal.ofReal (sphericalAreaDensity z)).toReal *
      (u z * weightedScalarTest ψ z) = u z * ψ z
    rw [ENNReal.toReal_ofReal (sphericalAreaDensity_pos z).le]
    unfold weightedScalarTest
    field_simp [(sphericalAreaDensity_pos z).ne']

 theorem tendsto_pairings_with_memLp_test
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℝ} {V : X → ℝ}
    (hlim : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ))) {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun n => ∫ x, u n x * ψ x ∂μ) atTop (𝓝 (∫ x, V x * ψ x ∂μ)) := by
  have he (f : X → ℝ) : (∫ x, f x * hψ.toLp ψ x ∂μ) = ∫ x, f x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
  simpa only [he] using hlim (hψ.toLp ψ)

 theorem tendsto_planar_pairings_of_spherical
    {u : ℕ → ℂ → ℝ} {V : ℂ → ℝ}
    (hlim : ∀ w : Lp ℝ 2 planarSphericalArea,
      Tendsto (fun n => ∫ z, u n z * w z ∂planarSphericalArea)
        atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea)))
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, u n z * ψ z) atTop (𝓝 (∫ z, V z * ψ z)) := by
  have h := tendsto_pairings_with_memLp_test hlim (weightedScalarTest_memLp hψ hs)
  simpa only [integral_weightedScalarTest] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnalyticWordBranch
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A branch through finite Baire words identifies an actual point of a
continuous image. This is the topological step for completed measurability. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def baireWordCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
    {b | PiNat.res b s.length = s}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelFiberCounts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite distinct-point witnesses make fiber counts universally
measurable. The image of each Borel configuration space is analytic. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

def pointCount {X : Type*} (S : Set X) : ℝ≥0∞ :=
  ∑' x, if x ∈ S then 1 else 0

def finitePointWitness {X : Type*} (S : Set X) (n : ℕ) : Prop :=
  ∃ g : Fin n → X, Injective g ∧ ∀ i, g i ∈ S

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureMajorants
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous test integrals on a compact family of finite measures and
the uniform positive mass needed for the compact duality construction. -/
open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The actual averaging operator used in compact-family separation. -/
def compactMeasureTestOperator (S : Set (FiniteMeasure Z)) :
    (Z →ᵇ ℝ) →ₗ[ℝ] C(S,ℝ) where
  toFun f := ⟨fun v => ∫ z, f z ∂(v.val : Measure Z),
    (FiniteMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_subtype_val⟩
  map_add' f g := by
    ext v
    exact integral_add (f.integrable (μ := (v.val : Measure Z)))
      (g.integrable (μ := (v.val : Measure Z)))
  map_smul' r f := by
    ext v
    exact integral_smul r f

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureBarycenter
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barycenter measure of a law on a compact family.
Both its finite mass and its nonnegative continuous test integrals follow
from the measurable measure-valued inclusion, not an assumed identity. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {S : Set (FiniteMeasure Z)}

def compactMeasureBarycenter (P : ProbabilityMeasure S) : Measure Z :=
  (P : Measure S).bind (fun v => (v.val : Measure Z))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureMajorantCost
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual least L² cost of a bounded continuous majorant on a compact
family of finite measures. Feasibility follows from its positive minimum
mass; sublinearity follows from the triangle inequality in L². -/
open Set MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  (σ : Measure Z) [IsFiniteMeasure σ] (S : Set (FiniteMeasure Z))

def majorantNorms (u : C_c(S,ℝ)) : Set ℝ :=
  {r | ∃ f : Z →ᵇ ℝ, (∀ v : S, u v ≤ compactMeasureTestOperator S f v) ∧
    ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ = r}

def compactMeasureMajorantCost (u : C_c(S,ℝ)) : ℝ := sInf (majorantNorms σ S u)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureSeparation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive modulus separates the actual compact-family majorant cost
from a constant functional. The separating functional is constructed. -/
open Set Filter MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_1 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactPlanTestDensity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact plan satisfying the continuous L² test bound has the actual
Borel barycenter density with the same norm bound. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_4 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteMeasureCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many measurable evaluations distinguish finite measures.
Finite intersections of a generating sequence form the required pi system. -/
open Set Function MeasureTheory MeasurableSpace
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity
variable (Z : Type*) [MeasurableSpace Z] [CountablyGenerated Z]

def measureCoordinateSet (s : Finset ℕ) : Set Z :=
  ⋂ n ∈ s, natGeneratingSequence Z n

def finiteMeasureCoordinates (μ : FiniteMeasure Z) (s : Finset ℕ) : ℝ≥0∞ :=
  (μ : Measure Z) (measureCoordinateSet Z s)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularMapPieces
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A planar map with invertible derivatives splits into countably many
measurable pieces with quantitative forward and inverse Lipschitz bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 def linearInverseApproxRadius (A : ℂ →L[ℝ] ℂ) : ℝ≥0 :=
  (2*(‖A.inverse‖₊+1))⁻¹

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurablePieceInverse
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable zero extensions of the inverse on a Borel image piece. -/
open Set Function MeasureTheory
open scoped Topology NNReal Classical
noncomputable section
namespace CircleDomainRigidity

 def inverseOnPiece (F : ℂ → ℂ) (S T : Set ℂ) : ℂ → ℂ :=
  T.piecewise (invFunOn F S) (fun _ => 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ScalarPairNull
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing prescribed real scalar trace pairs to their unit-circle levels
preserves planar outer-nullity. No measurability of the trace image is needed. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarPairModOne (p : ℝ × ℝ) : UnitAddCircle × UnitAddCircle :=
  (p.1, p.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HolomorphicInjOnDerivative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local inverse of a holomorphic injection on an open plane set.
The inverse is first continuous by open mapping; isolated possible
critical values are removable. Thus its actual derivative is nonzero. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma injOn_not_eventually_constant {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hi : InjOn F U) {z : ℂ} (hz : z ∈ U) :
    ¬ ∀ᶠ w in 𝓝 z, F w = F z := by
  intro hc
  have hUz : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  have hf : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [hUz.filter_mono nhdsWithin_le_nhds,
      hc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw he hne
    exact hne (hi hw hz he)
  obtain ⟨w, hw⟩ := Filter.Eventually.exists hf
  exact hw

lemma holomorphicInjOn_map_nhds {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : map F (𝓝 z) = 𝓝 (F z) := by
  apply le_antisymm
  · exact ((hF z hz).differentiableAt (hU.mem_nhds hz)).continuousAt
  · exact (hF.analyticAt (hU.mem_nhds hz)).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (injOn_not_eventually_constant hU hi hz)

lemma continuousAt_holomorphic_invFunOn {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ContinuousAt (invFunOn F U) (F z) := by
  have he : (invFunOn F U ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hi.leftInvOn_invFunOn hw
  change map (invFunOn F U) (𝓝 (F z)) ≤ 𝓝 (invFunOn F U (F z))
  rw [hi.leftInvOn_invFunOn hz, ← holomorphicInjOn_map_nhds hU hF hi hz,
    map_map, map_congr he, map_id]

lemma holomorphicInjOn_deriv_not_eventually_zero {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv F w = 0 := by
  intro hzero
  have hUz : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hUz.and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hb (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hF.mono hsub)
    (fun w hw => (hb (by simpa only [mem_ball] using hw)).2)
  apply injOn_not_eventually_constant hU hi hz
  filter_upwards [ball_mem_nhds z hr] with w hw
  exact (hc w hw).trans (hc z (mem_ball_self hr)).symm

lemma holomorphicInjOn_inverse_differentiableAt {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ (invFunOn F U) (F z) := by
  let g := invFunOn F U
  have hgc : ContinuousAt g (F z) := continuousAt_holomorphic_invFunOn hU hF hi hz
  have hgz : g (F z) = z := hi.leftInvOn_invFunOn hz
  have ha := hF.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv F w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicInjOn_deriv_not_eventually_zero hU hF hi hz)
  have hgc' : Tendsto g (𝓝 (F z)) (𝓝 z) := by
    change Tendsto g (𝓝 (F z)) (𝓝 (g (F z))) at hgc
    simpa only [hgz] using hgc
  have himage : ∀ᶠ y in 𝓝 (F z), y ∈ F '' U := by
    rw [← holomorphicInjOn_map_nhds hU hF hi hz]
    exact image_mem_map (hU.mem_nhds hz)
  have hgun : ∀ᶠ y in 𝓝 (F z), g y ∈ U := by
    filter_upwards [himage] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change invFunOn F U (F x) ∈ U
    rw [hi.leftInvOn_invFunOn hx]
    exact hx
  have ht : Tendsto g (𝓝[≠] (F z)) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hgc'.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [himage.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hne
    intro hgy
    have hright : F (g y) = y := invFunOn_eq hy
    rw [hgy] at hright
    exact hne hright.symm
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ hgc).differentiableAt
  filter_upwards [ht.eventually hn, hgun.filter_mono nhdsWithin_le_nhds,
    himage.filter_mono nhdsWithin_le_nhds] with y hy hyU hyimage
  have hcont : ContDiffAt ℂ 1 F (g y) := (hF.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hF _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hleft : (g ∘ F) =ᶠ[𝓝 (g y)] id := by
    filter_upwards [hU.mem_nhds hyU] with w hw
    exact hi.leftInvOn_invFunOn hw
  have hd := (hs.to_local_left_inverse hy hleft).hasDerivAt.differentiableAt
  rw [show F (g y) = y from invFunOn_eq hyimage] at hd
  exact hd

lemma holomorphicInjOn_deriv_ne_zero {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : deriv F z ≠ 0 := by
  have hf := ((hF z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hg := (holomorphicInjOn_inverse_differentiableAt hU hF hi hz).hasDerivAt
  have hleft : (invFunOn F U ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hi.leftInvOn_invFunOn hw
  have hd := (hg.comp z hf).congr_of_eventuallyEq hleft.symm
  have he := hd.deriv
  rw [deriv_id] at he
  intro hzero
  rw [hzero, mul_zero] at he
  exact one_ne_zero he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_HurwitzZeroFreeProof
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the zero-free Hurwitz input. A positive lower bound on a
circle bounds the reciprocals inside by maximum modulus. Isolated zeros
and the analytic identity principle then give the connected-domain form. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nonzero_limit_center_of_nonzero_circle
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (sphere c r))
    (hF : ∀ᶠ n in atTop, DiffContOnCl ℂ (F n) (ball c r) ∧
      ∀ z ∈ closedBall c r, F n z ≠ 0)
    (hlim : TendstoUniformlyOn F f atTop (sphere c r))
    (hcenter : Tendsto (fun n => F n c) atTop (𝓝 (f c)))
    (hboundary : ∀ z ∈ sphere c r, f z ≠ 0) : f c ≠ 0 := by
  intro hz
  obtain ⟨a,ha,hbound⟩ := (isCompact_sphere c r).exists_forall_le' hcont.norm
    (fun z hz => norm_pos_iff.mpr (hboundary z hz))
  have hu := Metric.tendstoUniformlyOn_iff.mp hlim (a/2) (half_pos ha)
  have hs : ∀ᶠ n in atTop, ‖F n c‖ < a/2 := by
    have ht := hcenter.norm
    rw [hz,norm_zero] at ht
    exact ht.eventually (gt_mem_nhds (half_pos ha))
  obtain ⟨n,hn,hu,hs⟩ := (hF.and (hu.and hs)).exists
  have hnz := hn.2 c (mem_closedBall_self hr.le)
  have hd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball c r) :=
    hn.1.inv (fun z hz => hn.2 z (closure_ball_subset_closedBall hz))
  have hmax : ‖(F n c)⁻¹‖ ≤ (a/2)⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (by
      intro z hz
      rw [frontier_ball c hr.ne'] at hz
      have he := hu z hz
      have hb := hbound z hz
      have hlo : a/2 ≤ ‖F n z‖ := by
        have hd := norm_le_norm_add_norm_sub (F n z) (f z)
        rw [← dist_eq_norm,dist_comm (F n z)] at hd
        linarith
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn.2 z (sphere_subset_closedBall hz)))
        (half_pos ha)).mpr hlo)
      (subset_closure (mem_ball_self hr))
  rw [norm_inv] at hmax
  have hlo := (inv_le_inv₀ (norm_pos_iff.mpr hnz) (half_pos ha)).mp hmax
  exact (not_lt_of_ge hlo) hs

 theorem hurwitzZeroFreeLimit : HurwitzZeroFreeLimit := by
  intro D F f hD hconn hF hlim
  have hd : DifferentiableOn ℂ f D := hlim.differentiableOn (hF.mono (fun _ h => h.1)) hD
  have ha := hd.analyticOnNhd hD
  by_cases hzall : ∀ z ∈ D, f z = 0
  · exact Or.inl hzall
  right
  intro c hc hz
  have hn : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 := by
    rcases (ha c hc).eventually_eq_zero_or_eventually_ne_zero with he | hn
    · exact (hzall (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected hc he)).elim
    · exact hn
  obtain ⟨ε,hε,hεn⟩ := Metric.mem_nhdsWithin_iff.mp hn
  obtain ⟨δ,hδ,hδD⟩ := Metric.isOpen_iff.mp hD c hc
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := by dsimp [r]; have := min_le_left ε δ; linarith
  have hrδ : r < δ := by dsimp [r]; have := min_le_right ε δ; linarith
  have hbD : closedBall c r ⊆ D := fun z hz => hδD (closedBall_subset_ball hrδ hz)
  have hnz : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    apply hεn
    refine ⟨closedBall_subset_ball hrε (sphere_subset_closedBall hz),?_⟩
    change z ≠ c
    intro he
    have hh := mem_sphere.mp hz
    rw [he,dist_self] at hh
    exact hr.ne' hh.symm
  have hfseq : ∀ᶠ n in atTop, DiffContOnCl ℂ (F n) (ball c r) ∧
      ∀ z ∈ closedBall c r, F n z ≠ 0 := hF.mono (fun n hn =>
    ⟨DiffContOnCl.mk_ball (hn.1.mono (ball_subset_closedBall.trans hbD))
      (hn.1.continuousOn.mono hbD),fun z hz => hn.2 z (hbD hz)⟩)
  have hU : TendstoUniformlyOn F f atTop (sphere c r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp
      (hlim.mono (sphere_subset_closedBall.trans hbD))
  exact nonzero_limit_center_of_nonzero_circle hr
    (hd.continuousOn.mono (sphere_subset_closedBall.trans hbD)) hfseq hU (hlim.tendsto_at hc) hnz hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_HurwitzUnivalentProof
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge injective-limit Hurwitz using the proved zero-free theorem
on a disk avoiding the other preimage and the analytic identity principle. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem hurwitzUnivalentLimit : HurwitzUnivalentLimit := by
  intro D F f hD hconn hF hlim hnonconstant
  have hd : DifferentiableOn ℂ f D := hlim.differentiableOn (hF.mono (fun _ h => h.1)) hD
  have ha := hd.analyticOnNhd hD
  intro x hx y hy heq
  by_contra hxy
  have hop : IsOpen (D ∩ {y}ᶜ) := hD.inter isClosed_singleton.isOpen_compl
  have hx' : x ∈ D ∩ {y}ᶜ := ⟨hx,hxy⟩
  obtain ⟨r,hr,hrD⟩ := Metric.isOpen_iff.mp hop x hx'
  have hbD : ball x r ⊆ D := fun z hz => (hrD hz).1
  have hseq : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => F n z-F n y) (ball x r) ∧
        ∀ z ∈ ball x r, F n z-F n y ≠ 0 := by
    filter_upwards [hF] with n hn
    refine ⟨(hn.1.mono hbD).sub_const (F n y),?_⟩
    intro z hz he
    have hh : z = y := hn.2 (hbD hz) hy (sub_eq_zero.mp he)
    exact (hrD hz).2 hh
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => F n y)
      (fun _ => f y) atTop (ball x r) :=
    ((hlim.tendsto_at hy).tendstoUniformlyOn_const (ball x r)).tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun n z => F n z-F n y)
      (fun z => f z-f y) atTop (ball x r) := (hlim.mono hbD).sub hconst
  rcases hurwitzZeroFreeLimit (ball x r) (fun n z => F n z-F n y)
    (fun z => f z-f y) isOpen_ball (Metric.isConnected_ball hr) hseq hsub with hz | hn
  · have hzero : (fun z => f z-f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [ball_mem_nhds x hr] with z hzr
      exact hz z hzr
    have hall := (ha.sub analyticOnNhd_const).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn.isPreconnected hx hzero
    exact hnonconstant ⟨f y,fun z hz => sub_eq_zero.mp (hall hz)⟩
  · exact hn x (mem_ball_self hr) (sub_eq_zero.mpr heq)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MontelCutoffExhaustion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported cutoffs for a varying open exhaustion. The
chosen subsequence is increasing and each fixed compact set eventually
lies in the region on which its cutoff is exactly one. -/
open Set Function Filter Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_montel_exhaustion_cutoffs (D : ℕ → Set ℂ)
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ φ : ℕ → C(ℂ, ℝ),
      (∀ n x, φ n x ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, tsupport (φ n) ⊆ D (s n)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
        ∀ᶠ n in atTop, ∀ x ∈ K, φ n x = 1) := by
  let U := ⋃ n, D n
  have hU : IsOpen U := isOpen_iUnion hD
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  have hK (n : ℕ) : IsCompact (((↑) : U → ℂ) '' K n) :=
    (K.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : ((↑) : U → ℂ) '' K n ⊆ ⋃ n, D n := by
    rintro z ⟨x,_,rfl⟩
    exact x.property
  choose m hm using (fun n => (hK n).elim_directed_cover D hD (hKU n) hmono.directed_le)
  let s : ℕ → ℕ := Nat.rec (m 0) (fun n k => max (k+1) (m (n+1)))
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun n => by
    change s n < max (s n+1) (m (n+1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
  have hms (n : ℕ) : m n ≤ s n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have hKn (n : ℕ) : ((↑) : U → ℂ) '' K n ⊆ D (s n) :=
    (hm n).trans (hmono (hms n))
  choose φ hone _ hsupp hrange using (fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) (hD (s n)) (hKn n))
  refine ⟨s,hs,φ,hrange,hsupp,?_⟩
  intro L hL hLU
  have hLc : IsCompact (((↑) : U → ℂ) ⁻¹' L) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hL
      (by simpa only [Subtype.range_coe] using hLU)
  obtain ⟨N,hN⟩ := K.exists_superset_of_isCompact hLc
  filter_upwards [eventually_ge_atTop N] with n hn
  intro x hx
  apply hone n
  exact ⟨⟨x,hLU hx⟩,K.subset hn (hN hx),rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MontelEquicontinuity
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local holomorphic bounds imply equicontinuity of the cutoff family.
Only finitely many initial cutoffs need individual continuity. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem equicontinuous_cutoffs_of_local_holomorphic_bounds
    {U : Set ℂ} (F : ℕ → ℂ → ℂ) (G : ℕ → C(ℂ, ℂ))
    (hlocal : ∀ x ∈ U, ∃ r > 0, ∃ M > 0, ∀ᶠ n in atTop,
      DifferentiableOn ℂ (F n) (ball x r) ∧
      (∀ z ∈ ball x r, ‖F n z‖ ≤ M) ∧ EqOn (G n) (F n) (ball x r)) :
    Equicontinuous (fun n (x : U) => G n x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨r,hr,M,hM,hlocal⟩ := hlocal x x.property
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlocal
  have hL : 0 < 2*M/r := div_pos (mul_pos (by norm_num) hM) hr
  have hinit : ∀ᶠ y : U in 𝓝 x, ∀ i : Fin N, dist (G i x) (G i y) < ε := by
    apply eventually_all.mpr
    intro i
    have hg : Tendsto (fun y : U => G i y) (𝓝 x) (𝓝 (G i x)) :=
      ((G i).continuous.comp continuous_subtype_val).tendsto x
    have hc : Tendsto (fun _ : U => G i x) (𝓝 x) (𝓝 (G i x)) := tendsto_const_nhds
    have ht := hc.dist hg
    have ht' : Tendsto (fun y : U => dist (G i x) (G i y)) (𝓝 x) (𝓝 0) := by
      simpa only [dist_self] using ht
    exact ht'.eventually (gt_mem_nhds hε)
  have hδ : 0 < min r (ε/(2*M/r)) := lt_min hr (div_pos hε hL)
  filter_upwards [hinit,ball_mem_nhds x hδ] with y hyinit hy
  intro n
  by_cases hn : n < N
  · exact hyinit ⟨n,hn⟩
  obtain ⟨hd,hb,he⟩ := hN n (Nat.le_of_not_gt hn)
  have hyc : dist (y : ℂ) (x : ℂ) < min r (ε/(2*M/r)) := hy
  have hyr : (y : ℂ) ∈ ball (x : ℂ) r := lt_of_lt_of_le hyc (min_le_left _ _)
  have hxr : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hm : MapsTo (F n) (ball (x : ℂ) r) (closedBall (F n x) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z hz,hb x hxr])
  rw [he hxr,he hyr,dist_comm]
  calc
    dist (F n y) (F n x) ≤ (2*M/r)*dist (y : ℂ) x :=
      Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm hyr
    _ < (2*M/r)*(ε/(2*M/r)) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hyc (min_le_right _ _)) hL
    _ = ε := mul_div_cancel₀ ε hL.ne'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MontelCutoffFamily
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn a locally bounded varying-domain holomorphic sequence into an
actual continuous family on the union, retaining every compact tail. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_montel_continuous_family (D : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ G : ℕ → C(ℂ, ℂ),
      (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
        ∀ᶠ n in atTop, EqOn (G n) (F (s n)) K) ∧
      Equicontinuous (fun n (x : ⋃ n, D n) => G n x) ∧
      (∀ x : ⋃ n, D n, ∃ B : ℝ, ∀ n, ‖G n x‖ ≤ B) := by
  obtain ⟨s,hs,φ,hφ,hφD,hφone⟩ := exists_montel_exhaustion_cutoffs D hD hmono
  have hcont (n : ℕ) : Continuous (fun z => φ n z • F (s n) z) := by
    apply ((φ n).continuous.continuousOn.smul (hF (s n)).continuousOn).continuous_of_tsupport_subset
      (hD (s n))
    exact (tsupport_smul_subset_left (f := (φ n : ℂ → ℝ)) (g := F (s n))).trans (hφD n)
  let G : ℕ → C(ℂ, ℂ) := fun n => ⟨fun z => φ n z • F (s n) z,hcont n⟩
  have heq (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ ⋃ n, D n) :
      ∀ᶠ n in atTop, EqOn (G n) (F (s n)) K := by
    filter_upwards [hφone K hK hKU] with n hn
    intro z hz
    change φ n z • F (s n) z = F (s n) z
    rw [hn z hz,one_smul]
  refine ⟨s,hs,G,heq,?_,?_⟩
  · apply equicontinuous_cutoffs_of_local_holomorphic_bounds (fun n => F (s n)) G
    intro x hx
    obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp (isOpen_iUnion hD) x hx
    let r := δ/2
    have hr : 0 < r := half_pos hδ
    have hrδ : r < δ := by dsimp [r] <;> linarith
    have hbU : closedBall x r ⊆ ⋃ n, D n :=
      (closedBall_subset_ball hrδ).trans hδU
    obtain ⟨M,hM⟩ := hbound (closedBall x r) (isCompact_closedBall x r) hbU
    refine ⟨r,hr,|M|+1,by positivity,?_⟩
    filter_upwards [hφone (closedBall x r) (isCompact_closedBall x r) hbU] with n hn
    have hbD : closedBall x r ⊆ D (s n) := by
      intro z hz
      apply hφD n
      apply subset_closure
      change φ n z ≠ 0
      rw [hn z hz]
      exact one_ne_zero
    refine ⟨(hF (s n)).mono (ball_subset_closedBall.trans hbD),?_,?_⟩
    · intro z hz
      have hm := hM (s n) z (ball_subset_closedBall hz) (hbD (ball_subset_closedBall hz))
      linarith [le_abs_self M]
    · intro z hz
      change φ n z • F (s n) z = F (s n) z
      rw [hn z (ball_subset_closedBall hz),one_smul]
  · intro x
    obtain ⟨M,hM⟩ := hbound {x.val} isCompact_singleton (singleton_subset_iff.mpr x.property)
    refine ⟨max 0 M,?_⟩
    intro n
    by_cases hx : x.val ∈ D (s n)
    · change ‖φ n x.val • F (s n) x.val‖ ≤ max 0 M
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφ n x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n x).2).trans
        ((hM (s n) x (mem_singleton _) hx).trans (le_max_right _ _))
    · have hz : φ n x.val = 0 := by
        by_contra hn
        exact hx (hφD n (subset_closure hn))
      change ‖φ n x.val • F (s n) x.val‖ ≤ max 0 M
      rw [hz,zero_smul,norm_zero]
      exact le_max_left _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MontelAscoli
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-open Ascoli extraction for the continuous cutoff family. -/
open Set Function Filter Topology
open scoped Topology UniformConvergence
noncomputable section
namespace CircleDomainRigidity

 theorem locally_uniform_complex_subsequence {U : Set ℂ} (hU : IsOpen U)
    (f : ℕ → C(U, ℂ)) (he : Equicontinuous (fun n z => f n z))
    (hb : ∀ z : U, ∃ B : ℝ, ∀ n, ‖f n z‖ ≤ B) :
    ∃ (v : C(U, ℂ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => f (s n) z) v atTop := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let S : Set C(U, ℂ) := range f
  let chooseIndex : S → ℕ := fun g => Classical.choose g.property
  have hchoose (g : S) : f (chooseIndex g) = g := Classical.choose_spec g.property
  have hse : Equicontinuous (fun g : S => ((g : C(U, ℂ)) : U → ℂ)) := by
    have hh := he.comp chooseIndex
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext g z
    exact congrArg (fun a : C(U, ℂ) => a z) (hchoose g).symm
  have hcover : ⋃₀ {K : Set U | IsCompact K} = univ := by
    apply eq_univ_of_forall
    intro z
    exact mem_sUnion.mpr ⟨{z},isCompact_singleton,mem_singleton z⟩
  let : T2Space (U →ᵤ[{K : Set U | IsCompact K}] ℂ) :=
    UniformOnFun.t2Space_of_covering hcover
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
        (fun g : C(U, ℂ) => (g : U → ℂ))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hclosed
      (fun K _ => hse.equicontinuousOn K) (fun _ _ z _ => by
        obtain ⟨B,hB⟩ := hb z
        refine ⟨Metric.closedBall 0 B,isCompact_closedBall _ _,?_⟩
        rintro g ⟨n,rfl⟩
        simpa only [Metric.mem_closedBall,dist_zero_right] using hB n)
  obtain ⟨v,_,s,hs,hv⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨v,s,hs,ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hv⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RiemannDiskSeed
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RiemannMappingCopy
/- Copied from Mathlib.Analysis.Complex.RiemannMapping (private in our Mathlib 0df444a,
public in d13f23b). -/
open Function Filter Metric Set
open scoped Pointwise Topology
open _root_.Complex

namespace RMCopy

/-- Proof of the Riemann Mapping Theorem, step 1.

If `U` is an open simply connected subset of `ℂ` that is not the whole `ℂ`,
then there exists a function `f : ℂ → ℂ` such that

- `f` is injective;
- the image `f '' U` isn't dense in `ℂ`;
- `f` is complex differentiable on `U` with nonzero derivative.

E.g., one can choose `a ∉ U`, then take `f z` to be the square root of `z - a`.
-/
theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  -- WLOG, `0 ∉ U`, otherwise we choose `a ∉ U` and replace `U` with `-a +ᵥ U`
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  -- Choose a continuous branch of `√z` on `U`.
  -- This is the function we're looking for.
  rcases exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  -- Then `0 ∉ f '' U`
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  -- Note that `f` is strictly differentiable at every point of `U`
  -- with derivative `1 / (2 * f z)`.
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  -- `f` has a left inverse, so it's injective. Let's show that `f '' U` isn't dense in `ℂ`.
  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  · -- Take a point `x ∈ U`.
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    -- Show that `-f x` has a neighborhood disjoint with `f '' U`.
    use -f x
    -- Since `f` is strictly differentiable at `x` with nonzero derivative,
    -- `f '' U` is a neighborhood of `f x`.
    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx
    -- Then `-f '' U` is a neighborhood of `-f x`.
    rw [nhds_neg, eventually_neg]
    -- This neighborhood has to be disjoint with `f '' U`,
    -- because `f a = - f b` implies `a = (f a) ^ 2 = (- f b) ^ 2 = b`, hence `f a = f b = 0`,
    -- which is impossible.
    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

/-- Proof of the Riemann Mapping Theorem, step 2.

If `U` is an open simply connected subset of `ℂ` which is not the whole field,
then there exists a map `f : ℂ → ℂ` such that

- `f` maps `U` to the unit disk;
- `f` is injective on `U`;
- `f` is differentiable on `U` with nonzero derivative.

Once the proof of the Riemann Mapping Theorem gets merged into Mathlib,
this lemma will be made private.
-/
lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  -- Take a continuous branch of the square root on `U`.
  -- It is injective, differentiable function on `U`, and `f '' U` isn't dense in `ℂ`.
  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩
  -- Choose a closed ball `Metric.closedBall x ε`, `ε > 0`, that is disjoint with `f '' U`.
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)
  -- Then `z ↦ ε / (f z - x)` satisfies all the assertions.
  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

end RMCopy

end RiemannMappingCopy

/-! A normalized nonconstant disk embedding from the existing square-root
construction. This is the initial competitor for extremal circularization. -/
section

open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

structure NormalizedDiskEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  injective : InjOn f U
  mapsTo : MapsTo f U (ball 0 1)
  at_base : f a=0

lemma exists_normalized_disk_embedding {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨f,hmap,hinj,hd⟩ := RMCopy.exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hc hproper
  let g : ℂ → ℂ := fun z => (f z-f a)/2
  have hdiff : DifferentiableOn ℂ f U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hd z hz)).differentiableWithinAt
  have hg : NormalizedDiskEmbedding U a g := by
    refine ⟨hdiff.sub_const (f a) |>.div_const 2,?_,?_,?_⟩
    · intro x hx y hy he
      apply hinj hx hy
      change (f x-f a)/2=(f y-f a)/2 at he
      have hh := (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp he
      linear_combination hh
    · intro z hz
      apply mem_ball_zero_iff.mpr
      change ‖(f z-f a)/2‖<1
      rw [norm_div]
      have hza : ‖f z‖<1 := mem_ball_zero_iff.mp (hmap hz)
      have haa : ‖f a‖<1 := mem_ball_zero_iff.mp (hmap ha)
      have hb := norm_sub_le (f z) (f a)
      norm_num
      linarith
    · dsimp [g]
      simp
  refine ⟨g,hg,?_⟩
  have hdg : HasDerivAt g (deriv f a/2) a :=
    ((differentiableAt_of_deriv_ne_zero (hd a ha)).hasDerivAt.sub_const (f a)).div_const 2
  rw [hdg.deriv]
  exact div_ne_zero (hd a ha) (by norm_num)

lemma normalized_disk_derivative_bound {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : NormalizedDiskEmbedding U a f) {r : ℝ} (hr : 0 < r) (hball : ball a r ⊆ U) :
    ‖deriv f a‖≤1/r := by
  apply Complex.norm_deriv_le_div_of_mapsTo_ball (hf.holomorphic.mono hball) _ hr
  intro z hz
  rw [hf.at_base]
  exact ball_subset_closedBall (hf.mapsTo (hball hz))

end CircleDomainRigidity

end
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskFractionalMap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary disk fractional transformations used to improve an
omitted-value extremal embedding. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

def diskFractionalMap (b z : ℂ) : ℂ := (z-b)/(1-star b*z)

lemma diskFractionalMap_denom_ne_zero {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    1-star b*z ≠ 0 := by
  intro h
  have he : star b*z=1 := (sub_eq_zero.mp h).symm
  have hn : ‖star b*z‖<1 := by
    rw [norm_mul,norm_star]
    nlinarith [norm_nonneg b,norm_nonneg z]
  rw [he,norm_one] at hn
  exact (lt_irrefl _ hn)

lemma diskFractionalMap_norm_identity (b z : ℂ) :
    ‖1-star b*z‖^2-‖z-b‖^2=(1-‖b‖^2)*(1-‖z‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.one_re,Complex.one_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma diskFractionalMap_mem_ball {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    ‖diskFractionalMap b z‖<1 := by
  have hd := diskFractionalMap_denom_ne_zero hb hz
  have hb' : 0<1-‖b‖^2 := by nlinarith [norm_nonneg b]
  have hz' : 0<1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have he := diskFractionalMap_norm_identity b z
  have hn : ‖z-b‖<‖1-star b*z‖ := by
    nlinarith [mul_pos hb' hz', norm_nonneg (z-b),norm_nonneg (1-star b*z)]
  simpa only [diskFractionalMap,norm_div,div_lt_one (norm_pos_iff.mpr hd)] using hn

lemma diskFractionalMap_hasDerivAt {b z : ℂ} (hb : ‖b‖<1) (hz : ‖z‖<1) :
    HasDerivAt (diskFractionalMap b)
      ((1-star b*b)/(1-star b*z)^2) z := by
  have hd := diskFractionalMap_denom_ne_zero hb hz
  have h := ((hasDerivAt_id z).sub_const b).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (star b))) hd
  refine h.congr_deriv (Eq.symm ?_)
  · dsimp
    ring

lemma diskFractionalMap_injective {b : ℂ} (hb : ‖b‖<1) :
    InjOn (diskFractionalMap b) (ball 0 1) := by
  intro x hx y hy he
  have hx' := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp hx)
  have hy' := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp hy)
  have hb' := diskFractionalMap_denom_ne_zero hb hb
  have he' := (div_eq_div_iff hx' hy').mp he
  have hf : (x-y)*(1-star b*b)=0 := by
    calc
      (x-y)*(1-star b*b) = (x-b)*(1-star b*y)-(y-b)*(1-star b*x) := by ring
      _ = 0 := sub_eq_zero.mpr he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hb')

@[simp] lemma diskFractionalMap_self {b : ℂ} : diskFractionalMap b b=0 := by
  simp [diskFractionalMap]

@[simp] lemma diskFractionalMap_zero {b : ℂ} : diskFractionalMap b 0 = -b := by
  simp [diskFractionalMap]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RiemannRootCompetitor
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A missing disk value gives a genuine holomorphic square-root
competitor; its derivative is computed before the final normalization. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_root_disk_competitor {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) {a : ℂ} {f : ℂ → ℂ}
    (hf : NormalizedDiskEmbedding U a f) {b : ℂ} (hb : ‖b‖<1)
    (hmiss : b ∉ f '' U) :
    ∃ r : ℂ → ℂ, ContinuousOn r U ∧ InjOn r U ∧ MapsTo r U (ball 0 1) ∧
      (∀ z, r z^2=diskFractionalMap b (f z)) ∧
      (∀ z ∈ U, r z ≠ 0) ∧
      (∀ z ∈ U, HasDerivAt r
        (((1-star b*b)/(1-star b*f z)^2*deriv f z)/(2*r z)) z) ∧
      r a^2 = -b := by
  let g := diskFractionalMap b ∘ f
  have hg (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      ((1-star b*b)/(1-star b*f z)^2*deriv f z) z :=
    (diskFractionalMap_hasDerivAt hb (mem_ball_zero_iff.mp (hf.mapsTo hz))).comp z
      ((hf.holomorphic z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hgcont : ContinuousOn g U := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hgnz (z : ℂ) (hz : z ∈ U) : g z ≠ 0 := by
    intro he
    have hden := diskFractionalMap_denom_ne_zero hb (mem_ball_zero_iff.mp (hf.mapsTo hz))
    have he' : f z-b=0 := (div_eq_zero_iff.mp he).resolve_right hden
    exact hmiss ⟨z,hz,sub_eq_zero.mp he'⟩
  obtain ⟨r,hr,hpow⟩ := Complex.exists_continuousOn_pow_eq hc hU hgcont (by
    rintro ⟨z,hz,he⟩
    exact hgnz z hz he) (by norm_num : (2:ℕ)≠0)
  have hrnz (z : ℂ) (hz : z ∈ U) : r z ≠ 0 := by
    intro he
    have hh := hpow z
    rw [he,zero_pow (by norm_num)] at hh
    exact hgnz z hz hh.symm
  refine ⟨r,hr,?_,?_,hpow,hrnz,?_,?_⟩
  · intro x hx y hy he
    apply hf.injective hx hy
    apply diskFractionalMap_injective hb (hf.mapsTo hx) (hf.mapsTo hy)
    change g x=g y
    rw [← hpow x,← hpow y,he]
  · intro z hz
    apply mem_ball_zero_iff.mpr
    have hh : ‖r z‖^2=‖g z‖ := by rw [← norm_pow,hpow]
    have hlt := diskFractionalMap_mem_ball hb (mem_ball_zero_iff.mp (hf.mapsTo hz))
    change ‖g z‖<1 at hlt
    nlinarith [norm_nonneg (r z)]
  · intro z hz
    have hp : HasDerivAt (fun w : ℂ => w^2) (2*r z) (r z) := by
      simpa using hasDerivAt_pow 2 (r z)
    exact hp.of_comp_left (hr.continuousAt (hU.mem_nhds hz)) (hg z hz)
      (mul_ne_zero (by norm_num) (hrnz z hz)) (Filter.Eventually.of_forall hpow)
  · simpa only [g,Function.comp_apply,hf.at_base,diskFractionalMap_zero] using hpow a

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RiemannDiskImprovement
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalizing the root competitor strictly increases the derivative
at the base point. This forces a derivative extremum to omit no disk value. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma disk_root_gain {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    1 < (1-t^4)/((1-t^2)*(2*t)) := by
  have hd : 0<1-t^2 := by nlinarith
  have he : (1-t^4)/((1-t^2)*(2*t)) = (1+t^2)/(2*t) := by
    field_simp [ne_of_gt hd,ne_of_gt ht0]
    ring
  rw [he,lt_div_iff₀ (by positivity : 0<2*t)]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ht1.ne)]

lemma norm_one_sub_star_mul {z : ℂ} (hz : ‖z‖<1) :
    ‖1-star z*z‖=1-‖z‖^2 := by
  have hp : 0<1-‖z‖^2 := by nlinarith [norm_nonneg z]
  rw [Complex.star_def,Complex.conj_mul']
  simp only [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]

lemma improve_disk_embedding_of_omitted_value {U : Set ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedDiskEmbedding U a f) (hdf : deriv f a ≠ 0)
    {b : ℂ} (hb : ‖b‖<1) (hmiss : b ∉ f '' U) :
    ∃ g : ℂ → ℂ, NormalizedDiskEmbedding U a g ∧ ‖deriv f a‖<‖deriv g a‖ := by
  obtain ⟨r,_hrcont,hrinj,hrmap,_hpow,hrnz,hrderiv,hbase⟩ :=
    exists_root_disk_competitor hU hc hf hb hmiss
  let v := r a
  have hv : ‖v‖<1 := mem_ball_zero_iff.mp (hrmap ha)
  have hv0 : 0<‖v‖ := norm_pos_iff.mpr (hrnz a ha)
  have hbnorm : ‖b‖=‖v‖^2 := by
    have hh := congrArg norm hbase
    simpa only [norm_pow,norm_neg,v] using hh.symm
  let g : ℂ → ℂ := diskFractionalMap v ∘ r
  have hdg (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      (((1-star v*v)/(1-star v*r z)^2)*
        (((1-star b*b)/(1-star b*f z)^2*deriv f z)/(2*r z))) z :=
    (diskFractionalMap_hasDerivAt hv (mem_ball_zero_iff.mp (hrmap hz))).comp z (hrderiv z hz)
  have hg : NormalizedDiskEmbedding U a g := by
    refine ⟨fun z hz => (hdg z hz).differentiableAt.differentiableWithinAt,?_,?_,?_⟩
    · exact (diskFractionalMap_injective hv).comp hrinj hrmap
    · intro z hz
      exact mem_ball_zero_iff.mpr
        (diskFractionalMap_mem_ball hv (mem_ball_zero_iff.mp (hrmap hz)))
    · exact diskFractionalMap_self
  refine ⟨g,hg,?_⟩
  have hnormv := norm_one_sub_star_mul hv
  have hnormb := norm_one_sub_star_mul hb
  have hformula : ‖deriv g a‖ =
      ((1-‖v‖^4)/((1-‖v‖^2)*(2*‖v‖)))*‖deriv f a‖ := by
    rw [(hdg a ha).deriv,hf.at_base]
    change ‖((1-star v*v)/(1-star v*v)^2)*
      (((1-star b*b)/(1-star b*0)^2*deriv f a)/(2*v))‖ = _
    simp only [mul_zero,sub_zero,one_pow,div_one,norm_mul,norm_div,norm_pow,
      hnormv,hnormb,Complex.norm_ofNat,hbnorm]
    have hvp : 0<1-‖v‖^2 := by nlinarith [norm_nonneg v]
    field_simp
  rw [hformula]
  have hgain := disk_root_gain hv0 hv
  nlinarith [norm_pos_iff.mpr hdf]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleIntervalTraversal
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual interval traversal used to compare circle embeddings with
interval-loop formulations of the Jordan--Schoenflies theorem. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def standardCircleTraversal (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

lemma continuous_standardCircleTraversal : Continuous standardCircleTraversal :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

lemma standardCircleTraversal_closes : standardCircleTraversal 0 = standardCircleTraversal 1 := by
  simp [standardCircleTraversal]

lemma standardCircleTraversal_injOn : InjOn standardCircleTraversal (Ico 0 1) := by
  intro s hs t ht he
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hs' : 2 * Real.pi * s ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hp.le hs.1, by nlinarith [ht.1, hs.2]⟩
  have ht' : 2 * Real.pi * t ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hp.le ht.1, by nlinarith [ht.2]⟩
  have heq := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hs' ht' he
  nlinarith

lemma standardCircleTraversal_image : standardCircleTraversal '' Icc 0 1 = univ := by
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hcover : Circle.exp '' Icc 0 (2 * Real.pi) = univ := by
    simpa only [zero_add, Circle.exp_surjective.range_eq] using
      Circle.periodic_exp.image_Icc hp 0
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ Circle.exp '' Icc 0 (2 * Real.pi) := by rw [hcover]; trivial
  obtain ⟨a, ha, he⟩ := hz
  refine ⟨a / (2 * Real.pi), ⟨div_nonneg ha.1 hp.le, (div_le_one hp).2 ha.2⟩, ?_⟩
  have heq : 2 * Real.pi * (a / (2 * Real.pi)) = a := by field_simp
  simpa only [standardCircleTraversal, heq] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.ModelCurve
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem segment_one_neg_one : segment ℝ (1 : ℝ) (-1) = Icc (-1) 1 := by
  rw [segment_symm]
  exact segment_eq_Icc (by norm_num)

theorem segment_neg_one_one : segment ℝ (-1 : ℝ) 1 = Icc (-1) 1 :=
  segment_eq_Icc (by norm_num)

/-! ### The model curve and its four sides -/

/-! ### The model curve is a Jordan curve -/

/-! ### The model curve is the boundary of the square

This is the blueprint's description `S = ∂Q` with `Q = [-1,1]²`, and the check that the sup-norm
definition above is the intended one. The only content is that a point of sup norm exactly `1`
is *not* interior to the square: scaling it out by a factor `1 + δ` leaves the square while
moving an arbitrarily small distance. -/

/-! ### A loop identifies exactly the ends of the parameter interval -/

/-! ### Lemma 3.1: parametrization by the model curve -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMover
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The tent of height `1` on `[-r, r]` with peak at `p`: it vanishes at the two endpoints,
takes the value `1` at `p`, and is linear on either side. Written as a minimum of two affine
functions rather than as a case split, which makes its continuity immediate. -/
noncomputable def tent (r p u : ℝ) : ℝ := min ((u + r) / (p + r)) ((r - u) / (r - p))

variable {r p q u : ℝ}

theorem continuous_tent (r p : ℝ) : Continuous (tent r p) := by
  unfold tent; fun_prop

theorem pos_of_lt_lt (h₁ : -r < p) (h₂ : p < r) : 0 < r := by linarith

theorem tent_le_one (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : tent r p u ≤ 1 := by
  rcases le_total u p with h | h
  · exact le_trans (min_le_left _ _) (by rw [div_le_one (by linarith)]; linarith)
  · exact le_trans (min_le_right _ _) (by rw [div_le_one (by linarith)]; linarith)

theorem tent_nonneg (h₁ : -r < p) (h₂ : p < r) (hu : -r ≤ u) (hu' : u ≤ r) :
    0 ≤ tent r p u :=
  le_min (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))

@[simp] theorem tent_self (h₁ : -r < p) (h₂ : p < r) : tent r p p = 1 := by
  rw [tent, div_self (by linarith), div_self (by linarith), min_self]

theorem tent_left (h₁ : -r < p) (h₂ : p < r) : tent r p (-r) = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show -r + r = 0 by ring, zero_div]
  exact min_eq_left (div_nonneg (by linarith) (by linarith))

theorem tent_right (h₁ : -r < p) (h₂ : p < r) : tent r p r = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show r - r = 0 by ring, zero_div]
  exact min_eq_right (div_nonneg (by linarith) (by linarith))

/-! ### Bending an interval -/

/-- The piecewise-linear self-map of `[-r, r]` that fixes both endpoints and carries `p` to
`q`, linearly on `[-r, p]` and on `[p, r]`. -/
noncomputable def bend (r p q u : ℝ) : ℝ :=
  if u ≤ p then -r + (u + r) * (q + r) / (p + r) else r - (r - u) * (r - q) / (r - p)

theorem bend_of_le (h : u ≤ p) : bend r p q u = -r + (u + r) * (q + r) / (p + r) := if_pos h

theorem bend_of_gt (h : p < u) : bend r p q u = r - (r - u) * (r - q) / (r - p) :=
  if_neg (not_le.2 h)

theorem bend_left (h : -r ≤ p) : bend r p q (-r) = -r := by
  rw [bend_of_le h]; simp

theorem bend_right (h : p < r) : bend r p q r = r := by
  rw [bend_of_gt h]; simp

theorem bend_self (h : -r < p) : bend r p q p = q := by
  have hp : p + r ≠ 0 := by linarith
  rw [bend_of_le le_rfl, mul_comm, mul_div_assoc, div_self hp, mul_one]; ring

theorem bend_refl (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : bend r p p u = u := by
  rcases le_or_gt u p with h | h
  · rw [bend_of_le h, mul_div_assoc, div_self (by linarith : p + r ≠ 0), mul_one]; ring
  · rw [bend_of_gt h, mul_div_assoc, div_self (by linarith : r - p ≠ 0), mul_one]; ring

/-- On the left half, the bend does not go past the image `q` of the peak. -/
theorem bend_le_of_le (h₁ : -r < p) (h₂ : -r < q) (h : u ≤ p) : bend r p q u ≤ q := by
  rw [bend_of_le h]
  have : (u + r) * (q + r) / (p + r) ≤ q + r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- On the right half, the bend stays past the image `q` of the peak. -/
theorem lt_bend_of_lt (h₁ : p < r) (h₂ : q < r) (h : p < u) : q < bend r p q u := by
  rw [bend_of_gt h]
  have : (r - u) * (r - q) / (r - p) < r - q := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The bend maps `[-r, r]` into itself. -/
theorem bend_mem (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (hu : -r ≤ u)
    (hu' : u ≤ r) : -r ≤ bend r p q u ∧ bend r p q u ≤ r := by
  rcases le_or_gt u p with h | h
  · refine ⟨?_, le_of_lt (lt_of_le_of_lt (bend_le_of_le h₁ h₃ h) h₄)⟩
    rw [bend_of_le h]
    have : 0 ≤ (u + r) * (q + r) / (p + r) := div_nonneg (by nlinarith) (by linarith)
    linarith
  · refine ⟨le_of_lt (lt_trans h₃ (lt_bend_of_lt h₂ h₄ h)), ?_⟩
    rw [bend_of_gt h]
    have : 0 ≤ (r - u) * (r - q) / (r - p) := div_nonneg (by nlinarith) (by linarith)
    linarith

/-- Bending from `p` to `q` and back from `q` to `p` is the identity. -/
theorem bend_bend (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (u : ℝ) :
    bend r q p (bend r p q u) = u := by
  rcases le_or_gt u p with h | h
  · have hp : p + r ≠ 0 := by linarith
    have hq : q + r ≠ 0 := by linarith
    rw [bend_of_le (bend_le_of_le h₁ h₃ h), bend_of_le h]
    field_simp
    ring
  · have hp : r - p ≠ 0 := by linarith
    have hq : r - q ≠ 0 := by linarith
    rw [bend_of_gt (lt_bend_of_lt h₂ h₄ h), bend_of_gt h]
    field_simp
    ring

/-- Past the peak the right-hand branch of the bend is valid, including at the peak itself,
where the two branches agree. -/
theorem bend_eq_right (h₁ : p + r ≠ 0) (h₂ : r - p ≠ 0) (h : p ≤ u) :
    bend r p q u = r - (r - u) * (r - q) / (r - p) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [bend_of_le le_rfl]
    field_simp
    ring
  · exact bend_of_gt h'

/-! ### Coordinates of the square -/

/-- In `Fin 2`, two indices distinct from a third are equal. -/
theorem fin2_eq_of_ne_of_ne {i j l : Fin 2} (h₁ : j ≠ i) (h₂ : l ≠ i) : l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-! ### Shearing the square along one coordinate -/

/-- The parameters of a shear are admissible when the peak of the level weight and the peak of
every bend it performs stay strictly inside the square. -/
structure IsShear (r a b k k' : ℝ) : Prop where
  /-- the level of maximal displacement is interior -/
  peak : b ∈ Ioo (-r) r
  /-- the point that is moved is interior -/
  base : a ∈ Ioo (-r) r
  /-- the breakpoints of the bends are interior -/
  mid : a + k ∈ Ioo (-r) r
  /-- the images of the breakpoints are interior -/
  top : a + (k + k') ∈ Ioo (-r) r

variable {a b k k' : ℝ}
  {i j l : Fin 2}

/-- The inverse shear has admissible parameters as well. -/
theorem IsShear.inv (h : IsShear r a b k k') : IsShear r a b (k + k') (-k') where
  peak := h.peak
  base := h.base
  mid := h.top
  top := by rw [show k + k' + -k' = k by ring]; exact h.mid

/-- A convex combination of two interior points of `(-r, r)` is interior. -/
theorem mem_Ioo_of_weight {w : ℝ} (ha : a ∈ Ioo (-r) r) (hak : a + k ∈ Ioo (-r) r)
    (hw : w ∈ Icc (0 : ℝ) 1) : a + k * w ∈ Ioo (-r) r := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hak
  obtain ⟨h5, h6⟩ := hw
  rcases eq_or_lt_of_le h5 with rfl | hw0
  · simpa using ⟨h1, h2⟩
  · constructor
    · nlinarith [mul_pos hw0 (show (0:ℝ) < a + k + r by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ a + r by linarith)]
    · nlinarith [mul_pos hw0 (show (0:ℝ) < r - a - k by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ r - a by linarith)]

/-! ### Movers of the square -/

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
-- module Solutions.Q146_CD.GeneratedStructure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- An edge of a subgraph has the same ends there as in the ambient graph. General; it is
here because nothing on `main` states it, and both elementary operations need it to know that
the outer cycle carries the subdivided edge with its own endpoints. -/
theorem isLink_of_le_of_mem_edgeSet (hHK : H ≤ K) (he : e ∈ E(H)) (h : K.IsLink e x y) :
    H.IsLink e x y := by
  obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
  rcases (hHK.isLink_mono hab).eq_and_eq_or_eq_and_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hab, hab.symm]

/-! ### The cells of an abstract structure -/

/-! ### Generated matched cell structures -/

/-! ### The geometric content of one 2-cell split

`thm:general-crosscut` is what the induction step of assertions (i) and (vii) applies at each
split. The two hypotheses it still carries on `main` — `thm:jordan` and `HasArcCollars` — are
threaded through verbatim; both are being discharged elsewhere. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.FiniteTransfer
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A finite family of fresh names can be chosen injectively outside any finite used set.  This
is the name-supply lemma used by the concrete ear relabelling: vertex, edge, and face requests
are put in one finite sum type so their chosen names are automatically pairwise distinct. -/
theorem exists_injective_avoiding [Infinite γ] (used : Set γ) (hused : used.Finite)
    (ι : Type*) [Finite ι] :
    ∃ fresh : ι → γ, Function.Injective fresh ∧ ∀ i, fresh i ∉ used := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let code : ι ↪ ℕ := (Fintype.equivFin ι).toEmbedding.trans Fin.valEmbedding
  let supply : ℕ ↪ {x // x ∈ (usedᶜ : Set γ)} :=
    hused.infinite_compl.natEmbedding (usedᶜ : Set γ)
  refine ⟨fun i => supply (code i), ?_, fun i => (supply (code i)).2⟩
  intro i j hij
  exact code.injective (supply.injective (Subtype.ext hij))

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
-- module Solutions.Q146_CD.Line
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A connected component of a bounded open subset of `ℝ` is an open interval `Ioo t₀ t₁` with
`t₀ < t₁`, and neither endpoint belongs to the set. -/
theorem exists_Ioo_eq_connectedComponentIn {T : Set ℝ} (hopen : IsOpen T) (hbdd : IsBounded T)
    {s : ℝ} (hs : s ∈ T) :
    ∃ t₀ t₁ : ℝ, t₀ < t₁ ∧ connectedComponentIn T s = Ioo t₀ t₁ ∧ t₀ ∉ T ∧ t₁ ∉ T := by
  set J := connectedComponentIn T s with hJdef
  have hJsub : J ⊆ T := connectedComponentIn_subset T s
  have hJs : s ∈ J := mem_connectedComponentIn hs
  have hJopen : IsOpen J := hopen.connectedComponentIn
  have hJord : J.OrdConnected :=
    (isPreconnected_connectedComponentIn (F := T) (x := s)).ordConnected
  have hbb : BddBelow J := (hbdd.subset hJsub).bddBelow
  have hba : BddAbove J := (hbdd.subset hJsub).bddAbove
  have hne : J.Nonempty := ⟨s, hJs⟩
  -- Openness keeps `J` clear of its own infimum and supremum.
  have hout : ∀ x ∈ J, sInf J < x ∧ x < sSup J := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJopen x hx
    have hlo : x - ε / 2 ∈ J := by
      refine hball ?_
      rw [mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hhi : x + ε / 2 ∈ J := by
      refine hball ?_
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact ⟨lt_of_le_of_lt (csInf_le hbb hlo) (by linarith),
      lt_of_lt_of_le (by linarith : x < x + ε / 2) (le_csSup hba hhi)⟩
  -- Order-connectedness fills the interval in.
  have hIoo : Ioo (sInf J) (sSup J) ⊆ J := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨v, hv, hxv⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hJord.out hu hv ⟨hux.le, hxv.le⟩
  have hlt : sInf J < sSup J := (hout s hJs).1.trans (hout s hJs).2
  refine ⟨sInf J, sSup J, hlt, subset_antisymm (fun x hx => hout x hx) hIoo, ?_, ?_⟩
  · -- Were the left endpoint in `T`, the half-open interval would be a larger connected subset.
    intro hmem
    have hsub : Ico (sInf J) (sSup J) ⊆ T := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h]; exact hmem
      · exact hJsub (hIoo ⟨h, hx.2⟩)
    have h2 := (isPreconnected_Ico (a := sInf J) (b := sSup J)).subset_connectedComponentIn
      (show s ∈ Ico (sInf J) (sSup J) from ⟨(hout s hJs).1.le, (hout s hJs).2⟩) hsub
    exact absurd (hout _ (h2 ⟨le_rfl, hlt⟩)).1 (lt_irrefl _)
  · intro hmem
    have hsub : Ioc (sInf J) (sSup J) ⊆ T := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]; exact hmem
      · exact hJsub (hIoo ⟨hx.1, h⟩)
    have h2 := (isPreconnected_Ioc (a := sInf J) (b := sSup J)).subset_connectedComponentIn
      (show s ∈ Ioc (sInf J) (sSup J) from ⟨(hout s hJs).1, (hout s hJs).2.le⟩) hsub
    exact absurd (hout _ (h2 ⟨hlt, le_rfl⟩)).2 (lt_irrefl _)

end Schoenflies
end

section
-- module Solutions.Q146_CD.InitialPair
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- A cell of the initial matched cell structure. -/
inductive InitialCell
  /-- One of the six boundary vertices, in cyclic order along `C`. -/
  | vert : Fin 6 → InitialCell
  /-- The outer edge from `vert i` to `vert (i + 1)`. -/
  | edge : Fin 6 → InitialCell
  /-- The crosscut edge, from `vert 1` to `vert 4`. -/
  | chord : InitialCell
  /-- One of the two 2-cells: `face false` is `R₁`, `face true` is `R₂`. -/
  | face : Bool → InitialCell
  /-- A spare name, belonging to no cell of the initial structure.

  The initial structure uses fifteen names; this constructor adds countably many more that it
  never uses. It is here for one reason: `thm:finite-transfer` needs `[Infinite γ]`, because an
  ear insertion consumes fresh cell names and on a finite name type the step is false. Without a
  spare supply the base case could not feed the recursion at all. Nothing below ever produces an
  `aux`, and no cell of `initialStructure` is one. -/
  | aux : ℕ → InitialCell
  deriving DecidableEq

namespace InitialCell

/-- The two ends of a cell, when it is an edge. Junk elsewhere; the graph below only ever
consults it on an edge name. -/
def ends : InitialCell → InitialCell × InitialCell
  | .edge i => (.vert i, .vert (i + 1))
  | .chord => (.vert 1, .vert 4)
  | c => (c, c)

/-- The six 0-cells. -/
def vertices : Set InitialCell := Set.range InitialCell.vert

/-- The seven 1-cells: six outer edges and the crosscut. -/
def edges : Set InitialCell := Set.range InitialCell.edge ∪ {InitialCell.chord}

/-- The six outer 1-cells. -/
def outerEdges : Set InitialCell := Set.range InitialCell.edge

/-- The two 2-cells. -/
def faces : Set InitialCell := Set.range InitialCell.face

theorem outerEdges_subset_edges : outerEdges ⊆ edges := Set.subset_union_left

theorem edge_mem_edges (i : Fin 6) : InitialCell.edge i ∈ edges := Or.inl ⟨i, rfl⟩

theorem chord_mem_edges : InitialCell.chord ∈ edges := Or.inr rfl

/-- Both ends of a 1-cell are 0-cells. -/
theorem ends_mem_vertices {e : InitialCell} (he : e ∈ edges) :
    e.ends.1 ∈ vertices ∧ e.ends.2 ∈ vertices := by
  rcases he with ⟨i, rfl⟩ | rfl
  · exact ⟨⟨i, rfl⟩, ⟨i + 1, rfl⟩⟩
  · exact ⟨⟨1, rfl⟩, ⟨4, rfl⟩⟩

theorem finite_vertices : vertices.Finite := Set.finite_range _

theorem finite_edges : edges.Finite := (Set.finite_range _).union (Set.finite_singleton _)

theorem finite_faces : faces.Finite := Set.finite_range _

theorem disjoint_vertices_edges : Disjoint vertices edges := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ (⟨j, hj⟩ | hj) <;> exact absurd hj (by simp)

theorem disjoint_faces_vertices : Disjoint faces vertices := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ ⟨j, hj⟩
  exact absurd hj (by simp)

theorem disjoint_faces_edges : Disjoint faces edges := by
  rw [Set.disjoint_left]
  rintro c ⟨i, rfl⟩ (⟨j, hj⟩ | hj) <;> exact absurd hj (by simp)

end InitialCell

/-- The abstract 1-skeleton of the initial structure: a hexagon with one long chord. -/
def initSkel : Graph InitialCell InitialCell where
  vertexSet := InitialCell.vertices
  edgeSet := InitialCell.edges
  IsLink e x y := e ∈ InitialCell.edges ∧
    ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by
    rintro e x y ⟨he, hxy | hxy⟩
    exacts [hxy.1 ▸ (InitialCell.ends_mem_vertices he).1,
      hxy.1 ▸ (InitialCell.ends_mem_vertices he).2]

/-- The distinguished outer cycle: the same hexagon without the chord. -/
def initOuter : Graph InitialCell InitialCell where
  vertexSet := InitialCell.vertices
  edgeSet := InitialCell.outerEdges
  IsLink e x y := e ∈ InitialCell.outerEdges ∧
    ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by
    rintro e x y ⟨he, hxy | hxy⟩
    exacts [hxy.1 ▸ (InitialCell.ends_mem_vertices (InitialCell.outerEdges_subset_edges he)).1,
      hxy.1 ▸ (InitialCell.ends_mem_vertices (InitialCell.outerEdges_subset_edges he)).2]

@[simp] theorem vertexSet_initSkel : V(initSkel) = InitialCell.vertices := rfl

@[simp] theorem edgeSet_initSkel : E(initSkel) = InitialCell.edges := rfl

@[simp] theorem vertexSet_initOuter : V(initOuter) = InitialCell.vertices := rfl

@[simp] theorem edgeSet_initOuter : E(initOuter) = InitialCell.outerEdges := rfl

theorem initSkel_isLink {e x y : InitialCell} :
    initSkel.IsLink e x y ↔ e ∈ InitialCell.edges ∧
      ((x = e.ends.1 ∧ y = e.ends.2) ∨ (x = e.ends.2 ∧ y = e.ends.1)) := Iff.rfl

theorem initSkel_isLink_ends {e : InitialCell} (he : e ∈ InitialCell.edges) :
    initSkel.IsLink e e.ends.1 e.ends.2 := ⟨he, Or.inl ⟨rfl, rfl⟩⟩

theorem initOuter_le_initSkel : initOuter ≤ initSkel :=
  ⟨subset_rfl, fun _ _ _ h => ⟨InitialCell.outerEdges_subset_edges h.1, h.2⟩⟩

/-- The cells lying on the closed boundary of a 2-cell: the vertices and edges of `Bᵢ`
together with the crosscut. `face false = R₁` is bounded by `B₁ ∪ P`, `face true = R₂` by
`B₂ ∪ P`. -/
def faceCells : Bool → Set InitialCell
  | false => {.vert 1, .vert 2, .vert 3, .vert 4, .edge 1, .edge 2, .edge 3, .chord}
  | true => {.vert 4, .vert 5, .vert 0, .vert 1, .edge 4, .edge 5, .edge 0, .chord}

/-- The cyclic boundary walk of each 2-cell, as a list of edge names. -/
def initBoundary : InitialCell → List InitialCell
  | .face false => [.edge 1, .edge 2, .edge 3, .chord]
  | .face true => [.edge 4, .edge 5, .edge 0, .chord]
  | _ => []

/-- The names that `initialStructure` declares to be cells: the six 0-cells, the seven 1-cells
and the two 2-cells. This is `initialStructure.cells` unfolded, written out here because
`initSub` is a field of `initialStructure` and cannot refer to it. -/
def cellNames : Set InitialCell :=
  InitialCell.vertices ∪ InitialCell.edges ∪ InitialCell.faces

theorem aux_notMem_cellNames (n : ℕ) : InitialCell.aux n ∉ cellNames := by
  rintro ((⟨i, hi⟩ | ⟨i, hi⟩ | hi) | ⟨k, hk⟩)
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hi
  · exact InitialCell.noConfusion hk

/-- **The base value of `≼_abs`** (tex 1590–1602): the reflexive pairs, the incidence of each
vertex with the edges it bounds, and, for `i = 1, 2`, the incidence of every vertex and edge of
`Bᵢ ∪ P` with `Rᵢ`. Nothing else.

The reflexive clause is restricted to `cellNames`. `≼_abs` must relate cells to cells —
`CellStructure.CombInvariants.sub_mem_left` and `.sub_mem_right` say so — and `InitialCell`
carries a spare supply of names beyond the fifteen cells, so unrestricted reflexivity would
relate a spare name to itself and make both false. -/
def initSub (c d : InitialCell) : Prop :=
  (c = d ∧ d ∈ cellNames) ∨ (d ∈ InitialCell.edges ∧ (c = d.ends.1 ∨ c = d.ends.2)) ∨
    (∃ k, d = .face k ∧ c ∈ faceCells k)

theorem initSub_refl {c : InitialCell} (hc : c ∈ cellNames) : initSub c c := Or.inl ⟨rfl, hc⟩

theorem initSub_ends {e : InitialCell} (he : e ∈ InitialCell.edges) :
    initSub e.ends.1 e ∧ initSub e.ends.2 e :=
  ⟨Or.inr (Or.inl ⟨he, Or.inl rfl⟩), Or.inr (Or.inl ⟨he, Or.inr rfl⟩)⟩

theorem initSub_face {k : Bool} {c : InitialCell} (h : c ∈ faceCells k) :
    initSub c (.face k) := Or.inr (Or.inr ⟨k, rfl, h⟩)

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

theorem fin6_add_sub : ∀ k j : Fin 6, j = k + (j - k) := by decide

theorem fin6_add_one : ∀ k m : Fin 6, k + m + 1 = k + (m + 1) := by decide

theorem fin6_add_eq_self : ∀ k n : Fin 6, k + n = k → n = 0 := by decide

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
-- module Solutions.Q146_CD.SquareMesh
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem segment_symm_Icc {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ (-r) r = Icc (-r) r := segment_eq_Icc (by linarith)

theorem segment_symm_Icc' {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ r (-r) = Icc (-r) r := by
  rw [segment_symm]; exact segment_symm_Icc hr

theorem inv_cast_lt_one {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN)

theorem inv_cast_pos {N : ℕ} (hN : 2 ≤ N) : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

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

/-- The radii of the `N` concentric rings, `1/N, 2/N, …, 1`. -/
noncomputable def meshRadii (N : ℕ) : List ℝ :=
  (List.range N).map fun j : ℕ => ((j : ℝ) + 1) / (N : ℝ)

theorem mem_meshRadii {N : ℕ} {r : ℝ} :
    r ∈ meshRadii N ↔ ∃ j < N, r = ((j : ℝ) + 1) / N := by
  rw [meshRadii]
  constructor
  · intro hr
    obtain ⟨j, hj, hval⟩ := List.mem_map.1 hr
    exact ⟨j, List.mem_range.1 hj, hval.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem meshRadii_pos {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : 0 < r := by
  obtain ⟨j, _, rfl⟩ := mem_meshRadii.1 hr
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

theorem meshRadii_le_one {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : r ≤ 1 := by
  obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [div_le_one hN0]
  have : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  linarith

theorem one_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : (1 : ℝ) ∈ meshRadii N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  refine mem_meshRadii.2 ⟨N - 1, Nat.sub_lt (by omega) one_pos, ?_⟩
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  field_simp
  ring

theorem inv_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) ∈ meshRadii N := by
  refine mem_meshRadii.2 ⟨0, by omega, ?_⟩
  norm_num

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

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

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

/-- The number of concentric rings used for mesh size `δ`. -/
noncomputable def meshCount (δ : ℝ) : ℕ := max 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)

theorem two_le_meshCount (δ : ℝ) : 2 ≤ meshCount δ := le_max_left _ _

theorem meshCount_spec {δ : ℝ} (hδ : 0 < δ) : 2 * Real.sqrt 2 < δ * meshCount δ := by
  have h1 : 2 * Real.sqrt 2 / δ < (meshCount δ : ℝ) := by
    calc 2 * Real.sqrt 2 / δ ≤ (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) + 1 := by linarith
      _ ≤ (meshCount δ : ℝ) := by exact_mod_cast le_max_right 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)
  rw [div_lt_iff₀ hδ] at h1
  linarith

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshConnected
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem chain_le_of_le {f : ℕ → ℝ} {m : ℕ} (h : ∀ i, i < m → f i ≤ f (i + 1)) :
    ∀ a b, a ≤ b → b ≤ m → f a ≤ f b := by
  intro a b
  induction b with
  | zero =>
    intro hab _
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    intro hab hb
    rcases Nat.lt_or_ge a (b + 1) with h₁ | h₁
    · exact (ih (by omega) (by omega)).trans (h b (by omega))
    · obtain rfl : a = b + 1 := by omega
      exact le_rfl

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

theorem coord_le_of_idx_le {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (h : a ≤ b) : f a ≤ f b := by
  rcases eq_or_lt_of_le h with rfl | h'
  · exact le_rfl
  · exact (hf ha hb h').le

end Schoenflies
end

section
-- module Solutions.Q146_CD.LocalGrid
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The `i`-th of the equally spaced coordinates starting at `a` with step `h`. -/
noncomputable def uniformCoord (a h : ℝ) (i : ℕ) : ℝ := a + i * h

@[simp] theorem uniformCoord_zero (a h : ℝ) : uniformCoord a h 0 = a := by
  simp [uniformCoord]

theorem uniformCoord_strictMono {h : ℝ} (hh : 0 < h) (a : ℝ) :
    StrictMono (uniformCoord a h) := by
  intro i j hij
  have hlt : (i : ℝ) < j := by exact_mod_cast hij
  have := mul_lt_mul_of_pos_right hlt hh
  simp only [uniformCoord]
  linarith

/-- **A preconnected set of reals inside `[a, a + k·h]` that avoids every coordinate
`a + i·h` has diameter less than `h`.** Two of its points more than `h` apart would straddle
one of the coordinates, and a preconnected subset of `ℝ` contains the interval between any two
of its points. -/
theorem abs_sub_lt_of_avoiding {a h : ℝ} (hh : 0 < h) {k : ℕ} {I : Set ℝ}
    (hI : IsPreconnected I) (hIsub : I ⊆ Set.Icc a (a + k * h))
    (havoid : ∀ i ≤ k, uniformCoord a h i ∉ I) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |x - y| < h := by
  -- one direction suffices, and the other is the same with `x` and `y` exchanged
  have key : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → v - u < h := by
    intro u hu v hv huv
    by_contra hcon
    push Not at hcon
    have hua : a ≤ u := (hIsub hu).1
    have hq0 : 0 ≤ (u - a) / h := div_nonneg (by linarith) hh.le
    set i : ℕ := ⌈(u - a) / h⌉₊ with hi
    have hile : (u - a) / h ≤ (i : ℝ) := Nat.le_ceil _
    have hilt : (i : ℝ) < (u - a) / h + 1 := Nat.ceil_lt_add_one hq0
    have hcu : u ≤ uniformCoord a h i := by
      have := (div_le_iff₀ hh).1 hile
      simp only [uniformCoord] <;> linarith
    have hcv : uniformCoord a h i ≤ v := by
      have : (i : ℝ) * h < (u - a) + h := by
        have := mul_lt_mul_of_pos_right hilt hh
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hh), one_mul] at this
        linarith
      simp only [uniformCoord] <;> linarith
    have hik : i ≤ k := by
      have hvk : v ≤ a + k * h := (hIsub hv).2
      have : (i : ℝ) * h ≤ (k : ℝ) * h := by
        simp only [uniformCoord] at hcv <;> linarith
      have : (i : ℝ) ≤ (k : ℝ) := le_of_mul_le_mul_right this hh
      exact_mod_cast this
    exact havoid i hik (hI.Icc_subset hu hv (Set.mem_Icc.2 ⟨hcu, hcv⟩))
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact key x hx y hy hxy
  · rw [abs_of_nonneg (by linarith)]
    exact key y hy x hx hxy

/-! ### The local grid

`prop:local-grid-attachment` clauses 2 and 3: a rectangular grid on the window `W`, all of
whose closed rectangles are smaller than `ε`. Everything combinatorial about it — that it is
2-connected, that it stays 2-connected after subdivision, that it is a plane graph and that its
boundary is a distinguished cycle — comes from `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean`; the content added here is the fineness. -/

variable {s ε : ℝ}
  {k : ℕ}

theorem localGrid_step_pos (hs : 0 < s) (hk : 1 ≤ k) : 0 < 2 * s / (k : ℝ) := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-! ### Fineness

The one quantitative clause: every closed grid rectangle is smaller than `ε`. Stated twice —
for the closed rectangle itself, which is the blueprint's wording, and for any connected subset
of `W` that avoids the grid, which is the form a face of the overlay arrives in. -/

/-! ### Choosing the mesh

`prop:local-grid-attachment` clause 3 asks for rectangles of diameter `< ε`. -/

/-- The number of intervals per side of `W` that makes every grid rectangle smaller than
`ε`. -/
noncomputable def localGridCount (s ε : ℝ) : ℕ := max 1 (⌈2 * Real.sqrt 2 * s / ε⌉₊ + 1)

theorem one_le_localGridCount (s ε : ℝ) : 1 ≤ localGridCount s ε := le_max_left _ _

theorem localGridCount_spec (hε : 0 < ε) :
    Real.sqrt 2 * (2 * s / (localGridCount s ε : ℕ)) < ε := by
  have hN : (1 : ℝ) ≤ (localGridCount s ε : ℕ) := by
    exact_mod_cast one_le_localGridCount s ε
  have hN0 : (0 : ℝ) < (localGridCount s ε : ℕ) := by linarith
  have h1 : 2 * Real.sqrt 2 * s / ε < ((localGridCount s ε : ℕ) : ℝ) := by
    calc 2 * Real.sqrt 2 * s / ε ≤ (⌈2 * Real.sqrt 2 * s / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈2 * Real.sqrt 2 * s / ε⌉₊ : ℝ) + 1 := by linarith
      _ ≤ ((localGridCount s ε : ℕ) : ℝ) := by
          exact_mod_cast le_max_right 1 (⌈2 * Real.sqrt 2 * s / ε⌉₊ + 1)
  rw [div_lt_iff₀ hε] at h1
  rw [mul_div_assoc', div_lt_iff₀ hN0]
  linarith

end Schoenflies
end

section
-- module Solutions.Q146_CD.SquareMeshClosed
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The anchored square mesh, closed

`Schoenflies/SquareMesh.lean` builds `Schoenflies.squareMesh δ fresh anchors` and proves the
geometric clauses of `prop:anchored-square-mesh`; `Schoenflies/SquareMeshConnected.lean`,
`Schoenflies/SquareMeshFixed.lean` and `Schoenflies/LocalGrid.lean` add the grid combinatorics,
the outer cycle from an explicit path-subdivision hypothesis, and the degenerate cases. This
module proves that path-subdivision hypothesis for the mesh.

## The hypothesis that is discharged here

`Schoenflies.SubdividesToPath pieces points` says: *the overlay edges lying inside a source
segment are exactly the edges of a path of the overlay from one end of that segment to the
other.* `SquareMeshFixed.lean` states it as an explicit hypothesis, and its docstring says the
theorem does not exist on `main`.

It does exist. `Schoenflies.exists_incWalk_insideEdges` in `Schoenflies/SquareCycle.lean` is
exactly that statement in the vocabulary of `Graph.IsIncWalk` — a walk along which
`dist P.1 ·` strictly increases — and `Graph.IsIncWalk.isPath` turns it into a path. The two
modules were simply never in one import chain: `SquareCycle.lean` was imported only by
`Schoenflies/JordanClosed.lean`. `Schoenflies.subdividesToPath_of_overlay` is the four-line
bridge, allowing the results of `SquareMeshFixed.lean` to be applied directly to the mesh.

## The outer cycle, as data

`Schoenflies.meshGraph_outer_cycle` is existential — its own docstring says *"once that
hypothesis is discharged by a theorem exporting the chain as a `def`, this should be restated
with the cycle as data"*. That is done here: `outerCycleEdge`, `outerCycleStart`,
`outerCycleEnd`, `outerCycleThird` and `outerCycleDetour` are `def`s, and the three clauses
are separate lemmas about them. A consumer needing the outer cycle of the mesh takes these
five names, not an `∃` it has to destructure at every use.

## Clause 5, and the hypothesis that is actually true

Clause 5 — *the skeleton of `T` is 2-connected* — was absent from every earlier module, and for
a good reason: it is **false** for `Schoenflies.squareMesh δ fresh anchors` when `fresh` has
fewer than two distinct points (`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`),
and `Schoenflies.FreshDense fresh δ` alone does not repair it
(`Schoenflies.freshDense_not_isTwoConnected`). What repairs it is `FreshDense fresh δ` together
with `δ < 4`, which forces two distinct fresh points
(`Schoenflies.exists_two_distinct_fresh_of_freshDense`). The blueprint's caller uses
`δ = ε_n = 2⁻ⁿ`, far below `4`, so the hypothesis is free at the only call site.

The assembly is the blueprint's, with one correction. The blueprint says *"adding these finitely
many cycles one at a time"*, but the **first** addition cannot be a cycle: distinct rings of the
mesh are disjoint, so no two of them share the two vertices `lem:union-two-connected` needs. The
first addition is an **ear** — down the spoke at `z`, round the inner ring, back up the spoke at
`w` — and that is precisely where the two distinct fresh points are spent. After it, every
further ring shares the crossing points `r • z ≠ r • w` with the spokes and goes in by
`lem:union-two-connected`, and every further spoke is an ear between the outer and inner rings.
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` then transfers 2-connectivity from the assembly
to the mesh, since every mesh vertex lies on a ring or on a spoke.

## The proposition, clause by clause

`prop:anchored-square-mesh` is exported as **data with its clauses as separate lemmas**: the
object is the `def` `Schoenflies.squareMesh δ fresh anchors`, and nothing is `∃`-packaged.

1. every 2-cell has diameter `< δ` — `Schoenflies.squareMesh_face_small`;
2. every anchor on `S` is a boundary vertex — `Schoenflies.squareMesh_anchor_mem_vertexSet`;
3. every new internal edge meeting `S` ends at a fresh point —
   `Schoenflies.squareMesh_inner_edge_at_fresh`;
4. exactly one such edge at each fresh point — `Schoenflies.squareMesh_unique_inner_edge`;
5. the skeleton is 2-connected — **`Schoenflies.squareMesh_isTwoConnected`** (this module);
6. `|T| ∖ S` is connected — `Schoenflies.squareMesh_isConnected_diff`.

and the outer cycle, which `def:admissible-graph` and every downstream consumer need as a
genuine cycle rather than a point set — `Schoenflies.squareMesh_isLongCycle_outerCycle`,
`Schoenflies.squareMesh_outerCycle_edgesCover` (this module).

## Blueprint

* `subdividesToPath_of_overlay`, `meshSubdividesToPath` — `lem:polygonal-overlay`: the
  subdivision of one source segment is a path of the overlay. This discharges
  `Schoenflies.SubdividesToPath`.
* `meshGraph_outer_cycle_of_mem_modelCurve`, `squareMesh_outer_cycle` —
  `prop:anchored-square-mesh` clause 3 as a **cycle**, with no hypothesis beyond `fresh ⊆ S`.
* `outerCycleEdge`, `outerCycleStart`, `outerCycleEnd`, `outerCycleThird`, `outerCycleDetour`,
  `squareMesh_isLongCycle_outerCycle`, `squareMesh_outerCycle_subset_modelCurve`,
  `squareMesh_outerCycle_edgesCover` — the same cycle as data with its clauses as lemmas.
* `rsideT`/`rsideL`/`rsideB`/`rsideR` and `meshGraph_ring_cycle` — the outer-cycle argument at
  every radius: each ring of the mesh is a long cycle occupying exactly that ring.
* `ringGraph`, `ringGraph_isTwoConnected`, `mem_vertexSet_ringGraph` — each ring as a named
  2-connected subgraph, via `Schoenflies.squareGraph` at centre `0`.
* `spokePiece_inter_ringSet`, `smul_mem_meshPoints`, `smul_mem_vertexSet_ringGraph` —
  the crossing points `r • z` as vertices, from the `MeetsAreCut` clause of `meshPoints`.
* `spokeWalk`, `spokeGraph` — each spoke as a path of the mesh.
* `meshEar`, `meshEar_isPath`, `meshCore_isTwoConnected` — `lem:subdivision-ear-preserve` (b):
  the ear that joins the outer ring to the inner one.
* `attachRings`, `attachSpokes` and their 2-connectivity — `lem:union-two-connected` and
  `lem:subdivision-ear-preserve` iterated, the blueprint's *"adding these finitely many cycles
  one at a time"*.
* `meshGraph_isTwoConnected`, `squareMesh_isTwoConnected` — `prop:anchored-square-mesh`
  clause 5.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### `SubdividesToPath` is a theorem

The membership clause of `Schoenflies.SubdividesToPath` and the membership clause of
`Schoenflies.insideEdges` are the same statement: `Q ∈ E(overlayGraph pieces points)` unfolds
to `Q ∈ overlayPieces pieces points` by `Iff.rfl`. So the only work is to turn the increasing
walk into a path, which `Graph.IsIncWalk.isPath` does. -/

/-! ### The outer cycle, with no hypothesis -/

/-! ### The outer cycle as data

Five `def`s and three lemmas, replacing the five-fold existential above. The `dite` is what
makes the definition total: the hypothesis `fresh ⊆ S` is not available inside a `def`, so the
data is junk when it fails and the lemmas carry the hypothesis. -/

/-! ### The four sides of a ring of arbitrary radius

`Schoenflies/SquareMeshFixed.lean` names the four sides of the *outer* ring — `sideT`, `sideL`,
`sideB`, `sideR` — and proves the handful of coordinate facts that the outer-cycle argument
runs on. Every inner ring needs the same facts, so they are restated here with the radius as a
parameter; `rsideT 1 = sideT` and so on, definitionally. -/

/-! ### Every ring of the mesh is a cycle

`Schoenflies.meshGraph_outer_cycle` proves this for the outer ring, `r = 1`, and every step of
its proof is about the four sides of that ring and nothing else. With the sides of a ring of
arbitrary radius now available, the same argument runs verbatim at every radius: the four sides
are four overlay paths, three concatenations glue them into one path once round the ring, and
the last edge of the fourth is peeled off to close the cycle.

This is the theorem the blueprint's *"adding these finitely many cycles one at a time"* needs
for the inner rings, and which `Schoenflies/SquareMeshFixed.lean` names as missing. -/


/-! ### Each ring of the mesh, as a named 2-connected subgraph

`Schoenflies/SquareCycle.lean` proves that the part of *any* polygonal overlay lying on the
boundary of a square whose four sides are among the overlay's source segments is a long cycle,
and is 2-connected — at any centre and any positive radius. The rings of the mesh are exactly
that, at centre `0`: `squarePieces 0 r` and `ringPieces r` are the same list. So each ring comes
with a name, `ringGraph`, a 2-connectivity proof, and the two membership lemmas the assembly of
clause 5 needs, at no cost. -/


/-! ### Where a spoke crosses a ring

`Schoenflies/SquareMeshFixed.lean` records the crossing points `r • z` as the thing its
assembly of clause 5 lacked: *"the crossing points `r • z` as vertices (which needs the
`MeetsAreCut` clause of `meshPoints`)"*. That is what this section supplies. The sup norm is a
faithful coordinate along a spoke (`Schoenflies.supNorm_smul_of_mem_modelCurve`), so a spoke
meets the ring of radius `r` in the single point `r • z`; a singleton meet forces both ends of
the `MeetsAreCut` segment to be that point; and `mem_vertexSet_ringGraph` then makes it a
vertex of the ring. -/

theorem inv_le_of_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) :
    ((N : ℝ)⁻¹) ≤ r := by
  obtain ⟨j, -, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hN0]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith


/-! ### The spokes, as paths of the mesh

`Schoenflies.SubdividesToPath` — now a theorem — turns each spoke into a path of the mesh from
its outer end `z` to its inner end `N⁻¹ • z`. The path is exported as data, `spokeWalk`, so
that the assembly can name it; and the crossing points are shown to be among the vertices it
visits, which is what makes each ring attachable at two of them. -/


/-! ### The core: outer ring, two spokes, inner ring

The blueprint assembles clause 5 by *"adding these finitely many cycles one at a time"*, but
the first addition cannot be a cycle: distinct rings of the mesh are disjoint, so no two of
them share the two vertices `lem:union-two-connected` asks for. What joins them is an **ear** —
a path with both ends on the outer ring — and the only such path runs down one spoke, round
part of the inner ring, and back up another spoke. That is why clause 5 needs **two distinct
fresh points**, and why it is false with fewer
(`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`).

Once that ear is in place the inner ring shares the two crossing points `N⁻¹ • z` and
`N⁻¹ • w` with it, and `Graph.IsTwoConnected.union` applies; from then on every further ring
shares `r • z` and `r • w`, and every further spoke is an ear between the outer and inner
rings. -/


/-! ### The assembly

`meshCore` is the outer ring, the ear, and the inner ring. `attachRings` then adds every ring
by `lem:union-two-connected` at the two crossing points `r • z ≠ r • w`, and `attachSpokes`
adds every remaining spoke by `lem:subdivision-ear-preserve` (b) — its two ends are `u` on the
outer ring and `N⁻¹ • u` on the inner one, both already present. Finally every vertex of the
mesh lies on a ring or on a spoke, so the assembled graph spans the mesh and
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` transfers 2-connectivity to the mesh itself. -/


/-! ### Adding every ring and every spoke -/


/-! ### Clause 5: the skeleton of the mesh is 2-connected -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.LimitMap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {γ : Type*}

/-! ### The realized skeleton and outer cycle, cell by cell

`Realization.skeletonSet` and `Realization.outerSet` are defined as point sets of drawn graphs.
The limit argument needs them as unions of *open cells*, because that is the form in which they
interact with `IsCellDecomposition`: "the carrier of any point of `C` is an outer cell" is the
first sentence of the blueprint's proof of `lem:outer-incidence`, and it is exactly this
rewriting. -/

/-! ### The tower of matched cellulations

Every field below is an obligation on whoever eventually constructs the sequence of
decompositions, and there is nothing here that the limit argument does not use. -/

namespace LimitTower

variable [Nonempty γ]
  {m n : ℕ}
  {σ : γ}

variable {L}

/-- A null real sequence is eventually below any positive bound. Used with `eps` and with the
pointwise source-star diameters. -/
theorem exists_lt_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (nhds 0)) {r : ℝ}
    (hr : 0 < r) : ∃ n, f n < r :=
  (h.eventually (Iio_mem_nhds hr)).exists

/-! #### Stars of the tower -/

/-! #### The limit map -/

/-! #### Agreement with the finite skeleton maps

The skeleton maps are nested, so `g_n = g_N` on `G_N` for every `n ≥ N`; at each such stage the
skeleton map carries the carrier of `x` onto the corresponding target cell, which sits inside
`T_n(x)`. The intersection of the `T_n(x)` is the single point `F x`. -/

/-! #### Continuity -/

/-! #### The image lies in the interior -/

/-! #### Injectivity -/

/-! #### Density of the target skeleton -/

/-! #### Surjectivity

The blueprint reaches `y` through the density of the target skeleton and a compactness argument
in `C ∪ D`. The route taken here is shorter and needs neither: the *source* stars of the
*target* carriers of `y` are themselves a nested sequence of nonempty compacts, and every point
of their intersection is already a preimage of `y`. -/

/-! #### Exact cell correspondence -/

/-! #### The inverse, and the interior homeomorphism -/

end LimitTower

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Windows
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {r ε δ : ℝ}

/-! ### One missing fact about `supDist`

`Schoenflies/Square.lean` has the ℓ^∞ norm, the ℓ^∞ distance, the triangle inequality and the
two comparisons with the Euclidean norm, but not that `supDist` separates points. It is needed
once below, to see that `r(p) > 0` off a compact set. **It belongs in `Square.lean`**; it is
here because this is its first use. -/

/-! ### The ℓ^∞ distance to a compact set -/

/-! ### 1-Lipschitz

*"The distance-to-`C` function is 1-Lipschitz in the ℓ^∞ metric."* Only the one-sided form is
used — `r(b) ≥ r(x) - ‖b - x‖_∞` — but both are recorded. -/

/-! ### The square of radius `r(p)` lies in the domain -/

/-! ### The windows

`windowRadius ε p` is the blueprint's `s_n(p)` with `ε_n` a parameter: the recursion chooses the
sequence, and nothing here needs to know that it is `2^{-n}`. -/

/-! ### The arithmetic of `prop:shrinking-stars` -/

/-! ### The two sequences the recursion fixes

*"Choose a sequence `b_1, b_2, …` in which every point of `B` occurs infinitely often, and put
`ε_n = 2^{-n}`."* Both are here, each with the one property `prop:shrinking-stars` uses: every
value of the enumeration recurs at arbitrarily large indices, and the mesh sequence is null. -/

/-- **An enumeration in which every value of `f` occurs infinitely often.** Cantor pairing, read
off the first component: the value `f k` reappears at `Nat.pair k m` for every `m`. -/
def recur {α : Type*} (f : ℕ → α) (n : ℕ) : α := f (Nat.unpair n).1

/-- **"The point `b` occurs at arbitrarily large indices."** This is the step of
`prop:shrinking-stars` that lets the mesh parameter be taken as small as the point requires: the
window centre is fixed first, and only then is a late enough stage chosen. -/
theorem exists_le_recur_eq {α : Type*} (f : ℕ → α) (k N : ℕ) :
    ∃ n, N ≤ n ∧ recur f n = f k :=
  ⟨Nat.pair k N, Nat.right_le_pair k N, by rw [recur, Nat.unpair_pair]⟩

/-- **`ε_n = 2^{-n}` is a null sequence.** -/
theorem tendsto_two_pow_neg :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))

end Schoenflies
end

section
-- module Solutions.Q146_CD.QuantitativeRecursion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

variable {γ : Type*}

/-- The dyadic window and source-mesh scale at successor `n`. -/
noncomputable def dyadicScale (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹ / 2

theorem dyadicScale_pos (n : ℕ) : 0 < dyadicScale n := by
  rw [dyadicScale]
  positivity

theorem tendsto_dyadicScale : Tendsto dyadicScale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ / 2) atTop (nhds 0)
  simpa only [zero_div] using tendsto_two_pow_neg.div_const (2 : ℝ)

/-- The target bound leaves an inessential factor four for the initial-stage estimate. -/
noncomputable def dyadicTargetBound (n : ℕ) : ℝ := 4 * dyadicScale n

theorem dyadicTargetBound_pos (n : ℕ) : 0 < dyadicTargetBound n :=
  mul_pos (by norm_num) (dyadicScale_pos n)

theorem tendsto_dyadicTargetBound :
    Tendsto dyadicTargetBound atTop (nhds 0) := by
  change Tendsto (fun n => 4 * dyadicScale n) atTop (nhds 0)
  simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_dyadicScale

/-- A target-star bound indexed by the actual stages.  The initial pair receives one coarse
bound; every successor uses the estimate established when it was constructed. -/
noncomputable def quantitativeTargetEps : ℕ → ℝ
  | 0 => 4
  | n + 1 => dyadicTargetBound n

theorem tendsto_quantitativeTargetEps :
    Tendsto quantitativeTargetEps atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat (f := quantitativeTargetEps) 1).mp
  simpa only [quantitativeTargetEps] using tendsto_dyadicTargetBound

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticJordanParametrization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic disk parametrizations retained by the iteration also
parametrize the entire actual Jordan boundary. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma holomorphic_injOn_isOpen_image {S : Set ℂ} {f : ℂ → ℂ}
    (hS : IsOpen S) (hf : DifferentiableOn ℂ f S) (hi : InjOn f S)
    {T : Set ℂ} (hT : IsOpen T) (hTS : T⊆S) : IsOpen (f '' T) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z,hz,rfl⟩
  rw [←holomorphicInjOn_map_nhds hS hf hi (hTS hz)]
  exact image_mem_map (hT.mem_nhds hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorDerivativeMean
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular mean of the derivative of a principal exterior
map. Inversion turns the derivative into a holomorphic disk function
with value one at its center. No area inequality is used. -/
open Set Filter Function Metric Asymptotics Bornology Real
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def invertedPrincipalDerivative (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  1 - w^2 * deriv (invertedPrincipalRemainder F) w

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_HolomorphicCircleCoefficients
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact circle coefficients of a holomorphic disk function. This is
Cauchy's formula in the Fourier normalization used for square integrals. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def diskTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionTiles
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint reflected copies of the exterior of finitely many disjoint caps.
Only the elementary side swapping and involution of each reflection are used. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [TopologicalSpace X]

def reflectionWord (R : I → X ≃ₜ X) : List I → X ≃ₜ X
  | [] => Homeomorph.refl X
  | i::w => (reflectionWord R w).trans (R i)

def reflectionTile (R : I → X ≃ₜ X) (K : I → Set X) (w : List I) : Set X :=
  reflectionWord R w '' (⋃i,K i)ᶜ

@[simp] lemma reflectionTile_nil (R : I → X ≃ₜ X) (K : I → Set X) :
    reflectionTile R K []=(⋃i,K i)ᶜ := by
  simp [reflectionTile,reflectionWord]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionTileAction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact action of a generating reflection on reduced words and their
geometric tiles, including cancellation of the leading generator. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X] [DecidableEq I]

def reflectionReduceStep (i : I) : List I → List I
  | [] => [i]
  | j::w => if i=j then w else i::j::w

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionCoefficientWords
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient transport through reduced reflection words. The pointwise
involution is proved before gluing the disjoint geometric copies. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X]

def reflectionCoefficientWord (R : I → X ≃ₜ X) (V : I → X → ℂ → ℂ) :
    List I → (X → ℂ) → X → ℂ
  | [],f => f
  | i::w,f => fun x => V i x (reflectionCoefficientWord R V w f (R i x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionWeightedL2
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The antiholomorphic Jacobian of circular reflection gives an exact
L2 isometry for its weighted pullback. The one pole is a null set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def roundReflectionWeight (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  -(r:ℂ)^2/(star (z-c))^2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealCoordinateLines
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product and complex coordinates of the physical line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def realCoordinateLine (i : Fin 2) (y x : ℝ) : ℝ × ℝ :=
  if i = 0 then (x,y) else (y,x)

 def complexCoordinateLine (i : Fin 2) (y x : ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm (realCoordinateLine i y x)

 def transverseCoordinate (i : Fin 2) (z : ℂ) : ℝ :=
  if i = 0 then z.im else z.re

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableAxialDiskTolls
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable axial disk tolls are integrable with their exact mixed-radius
budget. Point disks are missed outside a countable set of lines. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def axialDiskToll {ι : Type*} (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ) (y : ℝ) : ℝ :=
  ∑' j, (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
    (fun _ => 2*s j) y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialChordGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both source-axis geometries use the same exact real chord intervals.
Swapping real coordinates preserves every source disk and its distances. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialSwap (i : Fin 2) (z : ℂ) : ℂ := if i = 0 then z else Complex.I*star z

 def axialChord (i : Fin 2) (c : ℂ) (r y : ℝ) : ℝ × ℝ := horizontalChord (axialSwap i c) r y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialLineIntegral
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complex axial parametrizations preserve plane area.
Fubini provides the common integrable line densities. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def axialPlaneHomeomorph (i : Fin 2) : (ℝ × ℝ) ≃ₜ ℂ :=
    if i = 0 then (Homeomorph.prodComm ℝ ℝ).trans Complex.equivRealProdCLM.symm.toHomeomorph
    else Complex.equivRealProdCLM.symm.toHomeomorph

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedWeakIdentification
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a measurable region where uniformly bounded functions converge
pointwise, their L² weak limit has the same values almost everywhere. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_eq_on_of_bounded_weak_pointwise
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u : ℕ → X → ℝ} (hm : ∀ n, AEStronglyMeasurable (u n) μ)
    (hb : ∀ n x, ‖u n x‖ ≤ 1) (V : Lp ℝ 2 μ)
    (hw : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ)))
    {s : Set X} (hs : MeasurableSet s) {t : X → ℝ}
    (ht : ∀ x ∈ s, ‖t x‖ ≤ 1)
    (hp : ∀ x ∈ s, Tendsto (fun n => u n x) atTop (𝓝 (t x))) :
    ∀ᵐ x ∂μ, x ∈ s → V x = t x := by
  let T := s.indicator t
  have hpm : ∀ᵐ x ∂μ, Tendsto (fun n => s.indicator (u n) x) atTop (𝓝 (T x)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx, T] using hp x hx
    · simp only [indicator_of_notMem hx, T]
      exact tendsto_const_nhds
  have hTm : AEStronglyMeasurable T μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hm n).indicator hs) hpm
  have hT : MemLp T 2 μ := MemLp.of_bound hTm 1 (Eventually.of_forall fun x => by
    by_cases hx : x ∈ s
    · simpa only [T, indicator_of_mem hx] using ht x hx
    · simp only [T, indicator_of_notMem hx, norm_zero, zero_le_one])
  let D := s.indicator (fun x => V x - T x)
  have hD : MemLp D 2 μ := ((Lp.memLp V).sub hT).indicator hs
  have hprod := tendsto_integral_of_dominated_convergence
    (F := fun n x => u n x * D x) (f := fun x => T x * D x) (fun x => ‖D x‖)
    (fun n => (hm n).mul hD.aestronglyMeasurable)
    (hD.integrable (by norm_num)).norm
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)).trans_eq (one_mul _))
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ s
      · simpa only [T, indicator_of_mem hx] using (hp x hx).mul_const (D x)
      · simp only [D, T, indicator_of_notMem hx, mul_zero]
        exact tendsto_const_nhds)
  have he := tendsto_nhds_unique (tendsto_pairings_with_memLp_test hw hD) hprod
  have hI₁ : Integrable (fun x => V x * D x) μ := (Lp.memLp V).integrable_mul hD
  have hI₂ : Integrable (fun x => T x * D x) μ := hT.integrable_mul hD
  have hint : (∫ x, (V x - T x) * D x ∂μ) = 0 := by
    rw [show (fun x => (V x - T x) * D x) =
      (fun x => V x * D x - T x * D x) from funext (fun x => sub_mul _ _ _),
      integral_sub hI₁ hI₂]
    exact sub_eq_zero.mpr he
  have hDD : (fun x => (V x - T x) * D x) = fun x => D x ^ 2 := by
    funext x
    by_cases hx : x ∈ s <;> simp [D, hx, pow_two]
  rw [hDD] at hint
  have hzero := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (D x)) hD.integrable_sq).mp hint
  filter_upwards [hzero] with x hx hxs
  have hDx : D x = 0 := sq_eq_zero_iff.mp hx
  simpa only [D, T, indicator_of_mem hxs, sub_eq_zero] using hDx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalGradientMajorant
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-energy scalar has an integrable gradient majorant on each
fixed planar square. It is the actual gradient norm truncated to a disk. -/
open Set Function Filter Metric MeasureTheory
namespace CircleDomainRigidity

 theorem exists_integrable_gradient_majorant_on_square
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ}
    (he : IntegrableOn (euclideanGradientEnergy v) U) {L : ℝ} (hL : 0 ≤ L) :
    ∃ ρ : ℂ → ℝ, Integrable ρ ∧ ∀ z ∈ U,
      |z.re| ≤ L → |z.im| ≤ L → euclideanGradientNorm v z ≤ ρ z := by
  let E := U ∩ closedBall (0 : ℂ) (2 * L)
  let ρ := E.indicator (euclideanGradientNorm v)
  have hm : MeasurableSet E := hU.measurableSet.inter measurableSet_closedBall
  have he' : IntegrableOn (euclideanGradientEnergy v) E := he.mono_set inter_subset_left
  have hρ := memLp_indicator_euclideanGradientNorm hm he'
  have hp : ∀ z, 0 ≤ ρ z := fun z => indicator_nonneg
    (fun _ _ => Real.sqrt_nonneg _) z
  have hs : support ρ ⊆ closedBall 0 (2 * L) := by
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem (fun he : z ∈ E => h he.2) _)
  refine ⟨ρ, (integral_le_disk_L2 (mul_nonneg (by norm_num) hL) hρ hp hs).1, ?_⟩
  intro z hz hre him
  have hnorm : ‖z‖ ≤ 2 * L := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hE : z ∈ E := ⟨hz, by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩
  change euclideanGradientNorm v z ≤ E.indicator (euclideanGradientNorm v) z
  rw [indicator_of_mem hE]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ParallelJumpIntegral
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the two endpoint errors over the transverse disk projections
produces the exact factor four in the planar distributional estimate. -/
open Set Function MeasureTheory
namespace CircleDomainRigidity

 theorem integral_bound_of_parallel_disk_errors
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (C : ℝ) {f g : ℝ × ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hline : ∀ᵐ y : ℝ,
      |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| ≤
        2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    |(∫ p, f p) + (∫ p, g p)| ≤ 4 * C * ∑ i, r i * A i := by
  have hf' : Integrable f ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hf
  have hg' : Integrable g ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hg
  have hi := hf'.integral_prod_right.add hg'.integral_prod_right
  have hc (i : I) : Integrable
      ((Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ : ℝ => A i)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hcost := (integrable_finsetSum Finset.univ (fun i _ => hc i)).const_mul (2 * C)
  calc
    _ = |∫ y : ℝ, (∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| := by
      rw [integral_add hf'.integral_prod_right hg'.integral_prod_right,
        ← integral_prod_symm _ hf', ← integral_prod_symm _ hg', ← Measure.volume_eq_prod]
    _ ≤ ∫ y : ℝ, |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, 2 * C * ∑ i,
        (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y :=
      integral_mono_ae hi.abs hcost hline
    _ = 4 * C * ∑ i, r i * A i := by
      rw [integral_const_mul, integral_parallel_disk_tolls c r A hr]
      have he : (∑ i, 2 * r i * A i) = 2 * ∑ i, r i * A i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he]
      ring

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGapGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each actual gap of sorted disjoint holes lies in the residual interval. -/
open Set Function
namespace CircleDomainRigidity

 theorem gapsAfterHoles_subset_residual {n : ℕ} {a b : ℝ} (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1) (i : Fin (n + 1)) :
    Ioo (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ⊆
      Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ := by
  have hfirst : Monotone (fun i => (H i).1) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hinside i).2.1.trans (hsep i j hij).le
  have hlast : Monotone (fun i => (H i).2) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hsep i j hij).le.trans (hinside j).2.1
  have hleft : a ≤ (gapsAfterHoles a b H i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact (hinside j).1.le.trans (hinside j).2.1
  have hright : (gapsAfterHoles a b H i).2 ≤ b := by
    refine Fin.lastCases (motive := fun j : Fin (n + 1) =>
      (gapsAfterHoles a b H j).2 ≤ b) ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_last_snd, le_refl]
    · simpa only [gapsAfterHoles_castSucc_snd] using (hinside j).2.1.trans (hinside j).2.2.le
  intro x hx
  refine ⟨⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := mem_iUnion.mp h
  exact gapsAfterHoles_avoid a b H hfirst hlast i hx j hj

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGapIntegration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts on the open domain intervals between finitely many
holes. The two endpoint errors at each constant-filled hole are explicit. -/
open Set Function MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

theorem sum_gap_differences (n : ℕ) (left right : Fin (n + 1) → ℝ) :
    (∑ i, (right i - left i)) = right (Fin.last n) - left 0 +
      ∑ i : Fin n, (right i.castSucc - left i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i => left i.castSucc) (fun i => right i.castSucc)
    rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => right i - left i), h,
      Fin.sum_univ_castSucc (fun i : Fin (n + 1) => right i.castSucc - left i.succ)]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]
    ring

theorem filled_gap_boundary_identity
    (n : ℕ) (a b left right : Fin (n + 1) → ℝ) (value : Fin n → ℝ)
    (ha : a 0 = 0) (hb : b (Fin.last n) = 0) :
    (∑ i, (right i * b i - left i * a i)) +
      (∑ i : Fin n, value i * (a i.succ - b i.castSucc)) =
    ∑ i : Fin n, ((right i.castSucc - value i) * b i.castSucc +
      (value i - left i.succ) * a i.succ) := by
  rw [sum_gap_differences n (fun i => left i * a i) (fun i => right i * b i), ha, hb]
  simp only [mul_zero, sub_self, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem filled_gap_boundary_bound
    (n : ℕ) (a b left right : Fin (n + 1) → ℝ) (value A : Fin n → ℝ) (C : ℝ)
    (ha : a 0 = 0) (hb : b (Fin.last n) = 0) (_hC : 0 ≤ C)
    (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ i, |right i.castSucc - value i| ≤ A i)
    (hright : ∀ i, |value i - left i.succ| ≤ A i)
    (hφleft : ∀ i : Fin n, |b i.castSucc| ≤ C) (hφright : ∀ i : Fin n, |a i.succ| ≤ C) :
    |(∑ i, (right i * b i - left i * a i)) +
      (∑ i : Fin n, value i * (a i.succ - b i.castSucc))| ≤
        2 * C * ∑ i, A i := by
  rw [filled_gap_boundary_identity n a b left right value ha hb]
  calc
    _ ≤ ∑ i : Fin n, |(right i.castSucc - value i) * b i.castSucc +
        (value i - left i.succ) * a i.succ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, 2 * C * A i := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ := mul_le_mul (hleft i) (hφleft i) (abs_nonneg _) (hA i)
      have h₂ := mul_le_mul (hright i) (hφright i) (abs_nonneg _) (hA i)
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul]
      nlinarith
    _ = _ := by rw [Finset.mul_sum]

theorem integration_by_parts_with_filled_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (g : Fin (n + 1) → ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hg : ∀ i, AbsolutelyContinuousOnInterval (g i) (a i) (b i))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ i, |g i.castSucc (b i.castSucc) - value i| ≤ A i)
    (hright : ∀ i, |value i - g i.succ (a i.succ)| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∑ i, ((∫ x in a i..b i, g i x * deriv φ x) +
      (∫ x in a i..b i, deriv (g i) x * φ x))) +
      (∑ i : Fin n, value i * (φ (a i.succ) - φ (b i.castSucc)))| ≤
        2 * C * ∑ i, A i := by
  have he (i : Fin (n + 1)) :
      (∫ x in a i..b i, g i x * deriv φ x) + (∫ x in a i..b i, deriv (g i) x * φ x) =
        g i (b i) * φ (b i) - g i (a i) * φ (a i) := by
    have h := (hg i).integral_mul_deriv_eq_deriv_mul
      hφ.contDiffOn.absolutelyContinuousOnInterval
    linarith
  simp_rw [he]
  exact filled_gap_boundary_bound n (fun i => φ (a i)) (fun i => φ (b i))
    (fun i => g i (a i)) (fun i => g i (b i)) value A C hzero hone hC hA
    hleft hright hφleft hφright

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteIntervalSplitting
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting a line integral into its actual finite gaps and closed holes.
Only endpoint sets of zero length are ignored. -/
open Set Function MeasureTheory
namespace CircleDomainRigidity

 theorem sum_integral_gaps_and_holes (n : ℕ) (a b : Fin (n + 1) → ℝ) (h : ℝ → ℝ)
    (hia : ∀ i, IntervalIntegrable h volume (a 0) (a i))
    (hib : ∀ i, IntervalIntegrable h volume (a 0) (b i)) :
    (∑ i, ∫ x in a i..b i, h x) +
      (∑ i : Fin n, ∫ x in b i.castSucc..a i.succ, h x) =
      ∫ x in a 0..b (Fin.last n), h x := by
  let F := fun t => ∫ x in a 0..t, h x
  have heq {u v : ℝ} (hu : IntervalIntegrable h volume (a 0) u)
      (hv : IntervalIntegrable h volume (a 0) v) :
      (∫ x in u..v, h x) = F v - F u :=
    (intervalIntegral.integral_interval_sub_left hv hu).symm
  simp_rw [heq (hia _) (hib _), heq (hib _) (hia _)]
  rw [sum_gap_differences n (fun i => F (a i)) (fun i => F (b i)), add_assoc,
    ← Finset.sum_add_distrib]
  have hz : (∑ i : Fin n, ((F (b i.castSucc) - F (a i.succ)) +
      (F (a i.succ) - F (b i.castSucc)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    ring
  rw [hz, add_zero]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FilledGapIntegration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-gap estimate as an integral of the actual filled function,
with its ordinary derivative off the finitely many jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem intervalIntegral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : EqOn f g (Ioo a b)) : (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClippedDirectionalDerivative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped smooth functions have consistent ordinary directional
partials, including at the two clipping levels. -/
open Set Function Filter
open scoped Topology
namespace CircleDomainRigidity

 theorem fderiv_clipScalar_eq_ite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContinuousAt u z) :
    fderiv ℝ (clipScalar ∘ u) z = if u z ∈ Ioo 0 1 then fderiv ℝ u z else 0 := by
  by_cases hz : u z ∈ Ioo 0 1
  · simp only [hz, ↓reduceIte]
    apply EventuallyEq.fderiv_eq
    filter_upwards [hu.tendsto (isOpen_Ioo.mem_nhds hz)] with y hy
    exact clipScalar_eq ⟨hy.1.le, hy.2.le⟩
  · simp only [hz, ↓reduceIte]
    by_cases h0 : u z ≤ 0
    · apply IsLocalMin.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u z) ≤ clipScalar (u y)
        rw [clipScalar_of_nonpos h0]
        exact (clipScalar_mem _).1
    · have h1 : 1 ≤ u z := by
        have : ¬ u z < 1 := fun h => hz ⟨lt_of_not_ge h0, h⟩
        exact le_of_not_gt this
      apply IsLocalMax.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u y) ≤ clipScalar (u z)
        rw [clipScalar_of_one_le h1]
        exact (clipScalar_mem _).2

 theorem deriv_clipScalar_comp_curve {u : ℂ → ℝ} {γ : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hu : DifferentiableAt ℝ u (γ x)) (hγ : HasDerivAt γ v x) :
    deriv ((clipScalar ∘ u) ∘ γ) x = fderiv ℝ (clipScalar ∘ u) (γ x) v := by
  have hc : ContinuousAt (u ∘ γ) x := hu.continuousAt.comp hγ.continuousAt
  change fderiv ℝ (clipScalar ∘ (u ∘ γ)) x 1 = _
  rw [fderiv_clipScalar_eq_ite hc, fderiv_clipScalar_eq_ite hu.continuousAt]
  simp only [comp_apply]
  split_ifs with h
  · exact (hu.hasFDerivAt.comp_hasDerivAt x hγ).deriv
  · simp

 theorem deriv_eq_fderiv_of_eventuallyEq_clip
    {F u : ℂ → ℝ} {γ : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hF : F =ᶠ[𝓝 (γ x)] clipScalar ∘ u)
    (hu : DifferentiableAt ℝ u (γ x)) (hγ : HasDerivAt γ v x) :
    deriv (F ∘ γ) x = fderiv ℝ F (γ x) v := by
  rw [(hF.comp_tendsto hγ.continuousAt.tendsto).deriv_eq, hF.fderiv_eq]
  exact deriv_clipScalar_comp_curve hu hγ

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_VerticalFilledDerivative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second ordinary partial of the actual filled scalar is also its
line derivative almost everywhere, including the clipping levels. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem hasDerivAt_verticalLine (x y : ℝ) : HasDerivAt (verticalLine x) Complex.I y := by
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothLocalWeakDerivative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global distributional derivative agrees with the ordinary derivative
on any open set where its scalar has a smooth representative. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_mul_of_continuousOn_tsupport
    {U : Set ℂ} (hU : IsOpen U) {f φ : ℂ → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) : Integrable (fun z => f z * φ z) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_right.trans hsub)).integrable_of_hasCompactSupport hs.mul_left

 theorem integral_mul_fderiv_of_contDiffOn
    {U : Set ℂ} (hU : IsOpen U) {f φ : ℂ → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (hsub : tsupport φ ⊆ U) (v : ℂ) :
    (∫ z, f z * fderiv ℝ φ z v) = -(∫ z, fderiv ℝ f z v * φ z) := by
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_continuousOn_tsupport hU hdf hφ.continuous hs hsub)
    (integrable_mul_of_continuousOn_tsupport hU hf.continuousOn hdφ
      (hs.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset ℝ v).trans hsub))
    (integrable_mul_of_continuousOn_tsupport hU hf.continuousOn hφ.continuous hs hsub)
    (fun z hz => (hf.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num))
    (fun _ _ => hφ.differentiable (by norm_num) _)

 theorem weak_field_eq_smooth_derivative
    {U : Set ℂ} (hU : IsOpen U) {V f G : ℂ → ℝ} (v : ℂ)
    (hf : ContDiffOn ℝ 1 f U) (hG : MemLp G 2 volume)
    (heq : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → V z = f z)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, V z * fderiv ℝ φ z v) = -(∫ z, G z * φ z)) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → G z = fderiv ℝ f z v := by
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hzero : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → G z - fderiv ℝ f z v = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hG.locallyIntegrable (by norm_num)).locallyIntegrableOn U).sub
        (hdf.locallyIntegrableOn hU.measurableSet))
    intro φ hφ hs hsub
    have hV : (∫ z, V z * fderiv ℝ φ z v) = ∫ z, f z * fderiv ℝ φ z v := by
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      by_cases hzU : z ∈ U
      · rw [hz hzU]
      · have hnot : z ∉ tsupport (fun y => fderiv ℝ φ y v) :=
          fun h => hzU (hsub ((tsupport_fderiv_apply_subset ℝ v) h))
        have hd : fderiv ℝ φ z v = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v) hnot
        simp only [hd, mul_zero]
    have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hi := integral_mul_fderiv_of_contDiffOn hU hf hφ₁ hs hsub v
    have hw := hweak φ hφ₁ hs
    rw [hV] at hw
    have he : (∫ z, G z * φ z) = ∫ z, fderiv ℝ f z v * φ z := by linarith
    have hiG : Integrable (fun z => φ z * G z) := by
      change Integrable (φ * G)
      exact (hφ.continuous.memLp_of_hasCompactSupport hs : MemLp φ 2 volume).integrable_mul hG
    have hid : Integrable (fun z => φ z * fderiv ℝ f z v) := by
      simpa only [mul_comm] using integrable_mul_of_continuousOn_tsupport hU hdf hφ.continuous hs hsub
    simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
    rw [integral_sub hiG hid]
    simpa only [mul_comm, sub_eq_zero] using he
  filter_upwards [hzero] with z hz hzU
  exact sub_eq_zero.mp (hz hzU)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedWeakRange
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak L² limits of functions valued in the unit interval still lie in
that interval almost everywhere. The proof tests measurable sets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_mem_unitInterval_of_weak_limit
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u : ℕ → X → ℝ} (hm : ∀ n, AEStronglyMeasurable (u n) μ)
    (hb : ∀ n x, u n x ∈ Icc 0 1) (V : Lp ℝ 2 μ)
    (hw : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x * w x ∂μ)
      atTop (𝓝 (∫ x, V x * w x ∂μ))) :
    ∀ᵐ x ∂μ, V x ∈ Icc 0 1 := by
  have hi (n : ℕ) : Integrable (u n) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    apply MemLp.of_bound (hm n) 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb n x).1]
      exact (hb n x).2
  have hlim (s : Set X) (hs : MeasurableSet s) :
      Tendsto (fun n => ∫ x in s, u n x ∂μ) atTop (𝓝 (∫ x in s, V x ∂μ)) := by
    have he (f : X → ℝ) : (∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ) =
        ∫ x in s, f x ∂μ := by
      rw [← integral_indicator hs]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ s <;> simp [hx]
    simpa only [he] using tendsto_pairings_with_memLp_test hw
      (memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top μ s)))
  have hlo : ∀ᵐ x ∂μ, 0 ≤ V x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp V).integrable (by norm_num))
    intro s hs _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim s hs)
      (Eventually.of_forall fun n => integral_nonneg (fun x => (hb n x).1))
  have hhi : ∀ᵐ x ∂μ, V x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le ((Lp.memLp V).integrable (by norm_num)) (integrable_const 1)
    intro s hs _
    apply le_of_tendsto_of_tendsto (hlim s hs) tendsto_const_nhds
    exact Eventually.of_forall fun n => integral_mono (hi n).integrableOn
      (integrable_const 1) (fun x => (hb n x).2)
  filter_upwards [hlo, hhi] with x hx hy
  exact ⟨hx, hy⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarLocalLp
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar weak limit is locally planar L², including on arbitrary
compact regions that meet limiting complementary components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planarVolume_absolutelyContinuous_sphericalArea :
    (volume : Measure ℂ) ≪ planarSphericalArea :=
  withDensity_absolutelyContinuous'
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z)).ne')

open FiniteTransfer
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RangePreservingCutoff
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded region whose boundary lies in an open smooth locus admits
a cutoff whose transitions stay in that locus and preserve a strict range bound. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_range_preserving_cutoff
    {D O : Set ℂ} (hD : IsOpen D) (hO : IsOpen O)
    (hK : IsCompact (closure O)) (hfront : frontier O ⊆ D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {b : ℝ}
    (hbound : ∀ z ∈ closure O, z ∈ D → f z < b) :
    ∃ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ z, η z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ (closure O), η z = 1) ∧
      (∀ z, z ∉ D → fderiv ℝ η z = 0) ∧
      (∀ z ∈ D, η z ≠ 0 → f z ≤ b) := by
  let V := D ∩ f ⁻¹' Iio b
  have hV : IsOpen V := hf.isOpen_inter_preimage hD isOpen_Iio
  have hsub : closure O ⊆ O ∪ V := by
    intro z hz
    by_cases hi : z ∈ O
    · exact Or.inl hi
    · have hd : z ∈ D := hfront ⟨hz, by simpa only [hO.interior_eq] using hi⟩
      exact Or.inr ⟨hd, hbound z hz hd⟩
  obtain ⟨η, hη, hs, hsupp, hunit, hone⟩ :=
    exists_smooth_planar_cutoff hK (hO.union hV) hsub
  refine ⟨η, hη, hs, hunit, hone, ?_, ?_⟩
  · intro z hzD
    by_cases hz : z ∈ closure O
    · have hlocal : η =ᶠ[𝓝 z] fun _ => (1 : ℝ) := hone.filter_mono (nhds_le_nhdsSet hz)
      rw [hlocal.fderiv_eq]
      exact fderiv_const_apply 1
    · apply fderiv_of_notMem_tsupport ℝ
      intro h
      rcases hsupp h with ho | hv
      · exact hz (subset_closure ho)
      · exact hzD hv.1
  · intro z hzD hzη
    rcases hsupp (subset_tsupport η hzη) with ho | hv
    · exact (hbound z (subset_closure ho) hzD).le
    · exact hv.2.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteTraceMask
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite lower-envelope masks for the common-point trace argument.
The variation is paid only on intervals in which the corresponding cutoff
is active. These estimates precede the Sobolev and infinite-mask limits. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 def finiteTraceMask {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => min (finiteTraceMask cutoff I x t n) (if t ∈ I n then cutoff n x else 1)

 def infiniteTraceMask {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : ℝ := ⨅ n, finiteTraceMask cutoff I x t n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceCompression
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar tail compression used for common-point traces. The null-image
recovery works for arbitrary subsets of the line, by applying the monotone
area formula to a measurable envelope. No analyticity premise is needed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def traceCompression (E : Set ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, Eᶜ.indicator (fun _ => (1 : ℝ)) s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskPrimitive
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral primitives of the actual finite and infinite trace masks.
The finite spatial variation is bounded by interval lengths times cutoff
variation, while endpoint changes are always one-Lipschitz. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def finiteTracePrimitive {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (a : ℝ) (x : X) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in a..t, finiteTraceMask cutoff I x s n

 def infiniteTracePrimitive {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (a : ℝ) (x : X) (t : ℝ) : ℝ :=
  ∫ s in a..t, infiniteTraceMask cutoff I x s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableTraceEnumeration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate a countable family without repetitions. Missing natural
codes carry zero radii, so empty and finite families use the same bounds. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 def traceEnumeration {ι E : Type*} [Encodable ι] (v : ι → E) (fallback : E) : ℕ → E :=
  Function.extend Encodable.encode v (fun _ => fallback)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonPacking
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve each zero-radius balloon after removing all later balloons.
The reserved pieces are disjoint even when the balloons overlap. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def reservedBalloon (B : ℕ → Set ℂ) (j : ℕ) : Set ℂ :=
  B j \ ⋃ k : ℕ, B (k+j+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarMaximalInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published planar L² maximal input

T. Tao, *Lecture Notes 3 for Math 247A*, Fall 2006, Proposition 1.1,
p. 1, https://www.math.ucla.edu/~tao/247a.1.06f/notes3.pdf.
The dimension-two, p=2 strong maximal inequality is used. We retain a finite nonnegative
representative of the maximal function; modifying it on its null set
of infinite values leaves each fixed-radius average bound valid almost
everywhere. Squaring the norm bound gives the energy inequality below.
-/
open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def PlanarMaximalL2 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ g : ℂ → ℝ, MemLp g 2 volume →
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ z, 0 ≤ m z) ∧ MemLp m 2 volume ∧
      (∫ z, m z^2) ≤ A^2*(∫ z, g z^2) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
        (∫ y in ball x r, ‖g y‖) ≤ volume.real (ball x r)*m x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteBallSynthesis
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ball-synthesis estimate is derived from the published
planar maximal inequality, disjoint payment regions, and Cauchy--Schwarz. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def finiteBallDensity {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ F, (ball (c j) (d j)).indicator (fun _ => a j/d j) z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableBallSynthesis
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone convergence completes ball synthesis for the countable
balloon family. The density is the actual sum of weighted indicators. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def countableBallDensity (c : ℕ → ℂ) (d a : ℕ → ℝ) (z : ℂ) : ℝ :=
  ∑' j, (ball (c j) (d j)).indicator (fun _ => a j/d j) z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonRadii
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit shrinking balloon radii. The geometric extra radii reserve
at least half of every zero-radius balloon after all later deletions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 def traceExtraRadius (j : ℕ) : ℝ := (1/2:ℝ)^j

 def traceBalloonRadius (r : ℕ → ℝ) (m j : ℕ) : ℝ :=
  if 0 < r j then (1+1/((m:ℝ)+1))*r j else traceExtraRadius j/((m:ℝ)+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonSystem
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct each complete balloon system: shrinking radii, a smooth
cutoff around every closed component, and one square-integrable density
paying all finite sums of the cutoff derivatives. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def traceBalloonInnerRatio (m : ℕ) : ℝ := (2*(m:ℝ)+3)/(2*(m:ℝ)+4)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SmoothTraceTruncation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth scalar truncations vanish near the zero trace and converge to
positive inputs with a derivative bound independent of the scale. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def smoothTraceTruncation (δ : ℝ) (t : ℝ) : ℝ :=
  t * Real.smoothTransition (t / δ - 1)

 theorem smoothTraceTruncation_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothTraceTruncation δ) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const δ).sub contDiff_const))

 theorem smoothTraceTruncation_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    smoothTraceTruncation δ t = 0 := by
  unfold smoothTraceTruncation
  rw [Real.smoothTransition.zero_of_nonpos (by
    have h := (div_le_one hδ).mpr ht
    linarith), mul_zero]

 theorem smoothTraceTruncation_eq_self {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    smoothTraceTruncation δ t = t := by
  unfold smoothTraceTruncation
  rw [Real.smoothTransition.one_of_one_le (by
    have h : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr ht
    linarith), mul_one]

 theorem smoothTransition_deriv_zero_left {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Eventually.of_forall
  intro x
  rw [Real.smoothTransition.zero_of_nonpos ht]
  exact Real.smoothTransition.nonneg x

 theorem smoothTransition_deriv_zero_right {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Eventually.of_forall
  intro x
  rw [Real.smoothTransition.one_of_one_le ht]
  exact Real.smoothTransition.le_one x

 theorem smoothTraceTruncation_deriv (δ t : ℝ) :
    deriv (smoothTraceTruncation δ) t = Real.smoothTransition (t / δ - 1) +
      (t / δ) * deriv Real.smoothTransition (t / δ - 1) := by
  have hs := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have ht := (hasDerivAt_id t).div_const δ
  have he := (hasDerivAt_id t).mul ((hs _).hasDerivAt.comp t (ht.sub_const 1))
  change HasDerivAt (smoothTraceTruncation δ)
    (1 * Real.smoothTransition (t / δ - 1) + t * (deriv Real.smoothTransition (t / δ - 1) * (1 / δ))) t at he
  rw [he.deriv]
  ring

 theorem smoothTraceTruncation_deriv_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    deriv (smoothTraceTruncation δ) t = 0 := by
  have h : t / δ - 1 ≤ 0 := by have := (div_le_one hδ).mpr ht; linarith
  rw [smoothTraceTruncation_deriv, Real.smoothTransition.zero_of_nonpos h,
    smoothTransition_deriv_zero_left h]
  ring

 theorem smoothTraceTruncation_deriv_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    deriv (smoothTraceTruncation δ) t = 1 := by
  have h : 1 ≤ t / δ - 1 := by
    have : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr ht
    linarith
  rw [smoothTraceTruncation_deriv, Real.smoothTransition.one_of_one_le h,
    smoothTransition_deriv_zero_right h]
  ring

 theorem smoothTraceTruncation_mem {δ t : ℝ} (ht : 0 ≤ t) :
    smoothTraceTruncation δ t ∈ Icc 0 t := by
  exact ⟨mul_nonneg ht (Real.smoothTransition.nonneg _),
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) ht).trans_eq (mul_one t)⟩

 theorem smoothTraceTruncation_uniform_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ t : ℝ,
      ‖deriv (smoothTraceTruncation δ) t‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨1 + 2 * M, by positivity, ?_⟩
  intro δ hδ t
  by_cases hlo : t ≤ δ
  · rw [smoothTraceTruncation_deriv_zero hδ hlo, norm_zero]
    positivity
  by_cases hhi : 2 * δ ≤ t
  · rw [smoothTraceTruncation_deriv_one hδ hhi, norm_one]
    linarith
  have hr : t / δ - 1 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have : 1 < t / δ := (one_lt_div hδ).mpr (lt_of_not_ge hlo)
      linarith
    · have : t / δ < 2 := (div_lt_iff₀ hδ).mpr (lt_of_not_ge hhi)
      linarith
  have ht0 : 0 ≤ t / δ := by linarith [hr.1]
  have ht2 : t / δ ≤ 2 := by linarith [hr.2]
  rw [smoothTraceTruncation_deriv]
  calc
    _ ≤ ‖Real.smoothTransition (t / δ - 1)‖ +
      ‖(t / δ) * deriv Real.smoothTransition (t / δ - 1)‖ := norm_add_le _ _
    _ ≤ 1 + 2 * M := by
      rw [norm_mul, Real.norm_eq_abs (t / δ), abs_of_nonneg ht0]
      gcongr
      · rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      · exact hM _ hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceTruncationLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The truncations converge pointwise, and their derivatives converge
away from zero while remaining zero at zero. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smoothTraceTruncation_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => smoothTraceTruncation (δ n) t) atTop (𝓝 t) := by
  by_cases hz : t = 0
  · subst t
    have he : (fun n => smoothTraceTruncation (δ n) 0) = fun _ => (0 : ℝ) := by
      funext n
      exact smoothTraceTruncation_zero (hδ n) (hδ n).le
    rw [he]
    exact tendsto_const_nhds
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hl2 : Tendsto (fun n => 2 * δ n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hl.const_mul 2
    have hev : ∀ᶠ n in atTop, 2 * δ n < t := hl2.eventually (gt_mem_nhds hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (smoothTraceTruncation_eq_self (hδ n) hn.le).symm

 theorem smoothTraceTruncation_deriv_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => deriv (smoothTraceTruncation (δ n)) t) atTop
      (𝓝 (if t = 0 then 0 else 1)) := by
  split_ifs with hz
  · subst t
    have he : (fun n => deriv (smoothTraceTruncation (δ n)) 0) = fun _ => (0 : ℝ) := by
      funext n
      exact smoothTraceTruncation_deriv_zero (hδ n) (hδ n).le
    rw [he]
    exact tendsto_const_nhds
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hl2 : Tendsto (fun n => 2 * δ n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hl.const_mul 2
    have hev : ∀ᶠ n in atTop, 2 * δ n < t := hl2.eventually (gt_mem_nhds hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (smoothTraceTruncation_deriv_one (hδ n) hn.le).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SignedTraceTruncation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed smooth truncations for zero-trace differences of scalar tests. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def signedTraceTruncation (δ t : ℝ) : ℝ :=
  smoothTraceTruncation δ t - smoothTraceTruncation δ (-t)

 theorem signedTraceTruncation_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (signedTraceTruncation δ) :=
  (smoothTraceTruncation_contDiff δ).sub
    ((smoothTraceTruncation_contDiff δ).comp contDiff_id.neg)

 theorem signedTraceTruncation_deriv (δ t : ℝ) :
    deriv (signedTraceTruncation δ) t = deriv (smoothTraceTruncation δ) t +
      deriv (smoothTraceTruncation δ) (-t) := by
  have hd := (smoothTraceTruncation_contDiff δ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (hd t).hasDerivAt.sub ((hd (-t)).hasDerivAt.comp t (hasDerivAt_neg t))
  calc
    _ = deriv (smoothTraceTruncation δ) t - deriv (smoothTraceTruncation δ) (-t) * (-1) := he.deriv
    _ = _ := by ring

 theorem signedTraceTruncation_zero {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    signedTraceTruncation δ t = 0 := by
  rw [signedTraceTruncation, smoothTraceTruncation_zero hδ (abs_le.mp ht).2,
    smoothTraceTruncation_zero hδ (by linarith [(abs_le.mp ht).1])]
  exact sub_self _

 theorem signedTraceTruncation_deriv_zero {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    deriv (signedTraceTruncation δ) t = 0 := by
  rw [signedTraceTruncation_deriv, smoothTraceTruncation_deriv_zero hδ (abs_le.mp ht).2,
    smoothTraceTruncation_deriv_zero hδ (by linarith [(abs_le.mp ht).1])]
  exact add_zero _

 theorem signedTraceTruncation_norm_le {δ t : ℝ} (hδ : 0 < δ) :
    ‖signedTraceTruncation δ t‖ ≤ ‖t‖ := by
  by_cases ht : 0 ≤ t
  · rw [signedTraceTruncation, smoothTraceTruncation_zero (t := -t) hδ (by linarith), sub_zero,
      Real.norm_eq_abs, abs_of_nonneg (smoothTraceTruncation_mem ht).1,
      Real.norm_eq_abs, abs_of_nonneg ht]
    exact (smoothTraceTruncation_mem ht).2
  · have ht' : 0 ≤ -t := by linarith
    rw [signedTraceTruncation, smoothTraceTruncation_zero (t := t) hδ (by linarith), zero_sub,
      norm_neg, Real.norm_eq_abs, abs_of_nonneg (smoothTraceTruncation_mem ht').1,
      Real.norm_eq_abs, abs_of_nonpos (le_of_not_ge ht)]
    exact (smoothTraceTruncation_mem ht').2

 theorem signedTraceTruncation_uniform_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ t : ℝ,
      ‖deriv (signedTraceTruncation δ) t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := smoothTraceTruncation_uniform_deriv_bound
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro δ hδ t
  rw [signedTraceTruncation_deriv]
  exact (norm_add_le _ _).trans (by linarith [hbound δ hδ t, hbound δ hδ (-t)])

 theorem signedTraceTruncation_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => signedTraceTruncation (δ n) t) atTop (𝓝 t) := by
  by_cases ht : 0 ≤ t
  · have hz : ∀ n, smoothTraceTruncation (δ n) (-t) = 0 :=
      fun n => smoothTraceTruncation_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation, hz, sub_zero] using smoothTraceTruncation_tendsto hδ hl ht
  · have hz : ∀ n, smoothTraceTruncation (δ n) t = 0 :=
      fun n => smoothTraceTruncation_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation, hz, zero_sub, neg_neg] using
      (smoothTraceTruncation_tendsto hδ hl (show 0 ≤ -t by linarith)).neg

 theorem signedTraceTruncation_deriv_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (signedTraceTruncation (δ n)) t) atTop
      (𝓝 (if t = 0 then 0 else 1)) := by
  by_cases ht : 0 ≤ t
  · have hz : ∀ n, deriv (smoothTraceTruncation (δ n)) (-t) = 0 :=
      fun n => smoothTraceTruncation_deriv_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation_deriv, hz, add_zero] using
      smoothTraceTruncation_deriv_tendsto hδ hl ht
  · have hz : ∀ n, deriv (smoothTraceTruncation (δ n)) t = 0 :=
      fun n => smoothTraceTruncation_deriv_zero (hδ n) (by linarith [hδ n])
    simpa only [signedTraceTruncation_deriv, hz, zero_add, neg_eq_zero] using
      smoothTraceTruncation_deriv_tendsto hδ hl (show 0 ≤ -t by linarith)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentQuotientModel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The topological quotient by complementary components has a compatible
metric, an open domain chart, and a totally disconnected remainder.
Moore's decomposition theorem realizes this quotient as a sphere. -/
open Set Topology TopologicalSpace
noncomputable section
namespace CircleDomainRigidity

abbrev ComponentQuotient (G : Set Sphere) := Quotient (componentSetoid G)

def componentProjection (G : Set Sphere) : Sphere → ComponentQuotient G := @Quotient.mk' Sphere (componentSetoid G)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RadialDiskCompression
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit ambient disk compression. Its radial formula is the
identity outside the unit disk, has parameter reciprocal as inverse,
and compresses every fixed smaller disk as the parameter increases. -/
open Set Metric Topology
noncomputable section
namespace CircleDomainRigidity

def diskCompressionDenom (a t : ℝ) : ℝ := 1 + (a-1) * max (1-t) 0

def diskCompression (a : ℝ) (z : ℂ) : ℂ :=
  (diskCompressionDenom a ‖z‖)⁻¹ • z

lemma diskCompressionDenom_pos {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    0 < diskCompressionDenom a t := by
  unfold diskCompressionDenom
  by_cases h : t≤1
  · rw [max_eq_left (by linarith)]
    by_cases hzero : t=0
    · simpa [hzero] using ha
    · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm hzero)
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
  · rw [max_eq_right (by linarith)]
    simp

lemma diskCompression_norm {a : ℝ} (ha : 0<a) (z : ℂ) :
    ‖diskCompression a z‖ = ‖z‖ / diskCompressionDenom a ‖z‖ := by
  rw [diskCompression,norm_smul,Real.norm_eq_abs,abs_of_pos
    (inv_pos.mpr (diskCompressionDenom_pos ha (norm_nonneg z)))]
  rw [div_eq_mul_inv,mul_comm]

lemma diskCompressionDenom_inverse {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    diskCompressionDenom a⁻¹ (t / diskCompressionDenom a t) =
      (diskCompressionDenom a t)⁻¹ := by
  have hd := diskCompressionDenom_pos ha ht
  by_cases h : t≤1
  · have he : diskCompressionDenom a t=1+(a-1)*(1-t) := by
      simp [diskCompressionDenom,max_eq_left (show 0≤1-t by linarith)]
    have htd : t≤diskCompressionDenom a t := by
      rw [he]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
    have hh : 0≤1-t/diskCompressionDenom a t := by
      have := (div_le_one hd).mpr htd
      linarith
    have hd0 : 1+(a-1)*(1-t)≠0 := he ▸ hd.ne'
    rw [diskCompressionDenom,max_eq_left hh,he]
    field_simp [ha.ne',hd0]
    ring
  · have he : diskCompressionDenom a t=1 := by
      simp [diskCompressionDenom,max_eq_right (show 1-t≤0 by linarith)]
    rw [he,div_one]
    simp [diskCompressionDenom,max_eq_right (show 1-t≤0 by linarith)]

lemma diskCompression_inverse {a : ℝ} (ha : 0<a) (z : ℂ) :
    diskCompression a⁻¹ (diskCompression a z)=z := by
  rw [diskCompression,diskCompression_norm ha,
    diskCompressionDenom_inverse ha (norm_nonneg z),inv_inv]
  unfold diskCompression
  rw [smul_smul,mul_inv_cancel₀ (diskCompressionDenom_pos ha (norm_nonneg z)).ne',one_smul]

lemma diskCompression_continuous {a : ℝ} (ha : 0<a) : Continuous (diskCompression a) := by
  have hd : Continuous (fun z : ℂ => diskCompressionDenom a ‖z‖) := by
    unfold diskCompressionDenom
    fun_prop
  have hi : Continuous (fun z : ℂ => (diskCompressionDenom a ‖z‖)⁻¹) :=
    hd.inv₀ (fun z => (diskCompressionDenom_pos ha (norm_nonneg z)).ne')
  exact hi.smul (continuous_id : Continuous (fun z : ℂ => z))

def diskCompressionHomeomorph (a : ℝ) (ha : 0<a) : ℂ ≃ₜ ℂ where
  toFun := diskCompression a
  invFun := diskCompression a⁻¹
  left_inv := diskCompression_inverse ha
  right_inv := by
    intro z
    simpa only [inv_inv] using diskCompression_inverse (inv_pos.mpr ha) z
  continuous_toFun := diskCompression_continuous ha
  continuous_invFun := diskCompression_continuous (inv_pos.mpr ha)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NextComponentShrink
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial and successor stages for component shrinking. Every stage
is an actual plane homeomorphism; the successor controls both maps and
the quotient-valued inverse observations. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

def ComponentImageSmall {Y : Type*} [PseudoMetricSpace Y]
    (F : Set ℂ) (p : ℂ → Y) (H : ℂ ≃ₜ ℂ) (r : ℝ) : Prop :=
  ∀ x ∈ H '' F, ∀ y ∈ connectedComponentIn (H '' F) x, dist (p y) (p x) < r

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RecursiveComponentShrink
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual recursively chosen shrinking homeomorphisms, with
summable geometric forward and quotient-inverse displacement bounds. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

def componentShrinkRadius (n : ℕ) : ℝ := (1/2)^n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_QuadrantFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle flux expressed on four quarter arcs. This representation
uses the same boundary values as the axial slice integrals. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def quadrantSign (s : Bool) : ℝ := if s then 1 else -1
 def quadrantNormal (s t : Bool) (θ : ℝ) : ℂ :=
    ⟨quadrantSign s*Real.cos θ,quadrantSign t*Real.sin θ⟩
 def quadrantPoint (c : ℂ) (r : ℝ) (s t : Bool) (θ : ℝ) : ℂ := c+r*quadrantNormal s t θ
 def quadrantFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ θ in (0 : ℝ)..(Real.pi/2),
      r*∑ s : Bool, ∑ t : Bool, (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleProjectionEndpoints
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint maps in axial slicing are exactly the four quarter arcs. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def horizontalCirclePoint (right : Bool) (c : ℂ) (r y : ℝ) : ℂ :=
    ⟨c.re+quadrantSign right*Real.sqrt (r^2-(y-c.im)^2),y⟩
 def verticalCirclePoint (top : Bool) (c : ℂ) (r x : ℝ) : ℂ :=
    ⟨x,c.im+quadrantSign top*Real.sqrt (r^2-(x-c.re)^2)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CircleProjectionFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of the two axial endpoint integrals is exactly circle flux
for bounded measurable boundary values. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def horizontalCircleIncrement (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) : ℝ :=
    (F (horizontalCirclePoint true c r y)).re-(F (horizontalCirclePoint false c r y)).re
 def verticalCircleIncrement (F : ℂ → ℂ) (c : ℂ) (r x : ℝ) : ℝ :=
    (F (verticalCirclePoint true c r x)).im-(F (verticalCirclePoint false c r x)).im
 def horizontalCircleFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ y in (c.im-r)..(c.im+r), horizontalCircleIncrement F c r y
 def verticalCircleFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ x in (c.re-r)..(c.re+r), verticalCircleIncrement F c r x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalOuterFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal inverse germ gives the exact outer-circle flux
for every sufficiently large radius. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalInverseMean (F : ℂ → ℂ) (w : ℂ) : ℂ :=
    1+w*invertedPrincipalRemainder F w

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBeltramiCoefficientReduction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual conjugate Beltrami equation to a bounded standard
coefficient after constructing its L2 solution. No nonvanishing assumption
on the complex derivative is needed for this algebraic reduction. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 def realBeltramiStandardCoefficient (q : ℝ) (a : ℂ) : ℂ := (q : ℂ) * star a / a

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceLineTails
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tonelli's theorem selects lines with finite total interval cost.
The union of the remaining active intervals consequently has vanishing
outer length. Overlaps between the intervals require no disjointness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 def lineTailIntervals (I A : ℕ → Set ℝ) (t : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ k : ℕ, if t ∈ A (k+N) then I (k+N) else ∅

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ContinuousRunningMaximum
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous running maximum for nonnegative continuous functions.
Using the norm of a curried map avoids any selection of maximizers. -/
open Set
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def runningMaximum (k : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  let F : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => k (min p.1 p.2), k.continuous.comp (continuous_fst.min continuous_snd)⟩
  ⟨fun t => ‖F.curry t‖, continuous_norm.comp F.curry.continuous⟩

lemma runningMaximum_nonneg (k : C(unitInterval, ℝ)) (t : unitInterval) :
    0 ≤ runningMaximum k t := by
  dsimp only [runningMaximum, ContinuousMap.coe_mk]
  exact norm_nonneg _

lemma runningMaximum_le (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u)
    {t : unitInterval} {c : ℝ} (hc : 0 ≤ c) (h : ∀ u ≤ t, k u ≤ c) :
    runningMaximum k t ≤ c := by
  apply (ContinuousMap.norm_le _ hc).mpr
  intro u
  change ‖k (min t u)‖ ≤ c
  rw [Real.norm_eq_abs, abs_of_nonneg (hk _)]
  exact h _ (min_le_left _ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RescaledPlaneBump
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth plane cutoff with quantitative rescaling. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def planeUnitBump : ContDiffBump (0 : ℂ) := ⟨1,2,zero_lt_one,one_lt_two⟩
def planeScaledBump (r : ℝ) (z : ℂ) : ℝ := planeUnitBump (r⁻¹ • z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPerturbationHomeomorph
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small globally Lipschitz perturbations of the identity give actual
ambient homeomorphisms. These are the deformation maps for regular collars. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma approximatesLinearOn_id_add {V : ℂ → ℂ} {L : ℝ≥0}
    (hV : LipschitzWith L V) :
    ApproximatesLinearOn (fun z => z + V z) ((ContinuousLinearEquiv.refl ℝ ℂ) : ℂ →L[ℝ] ℂ)
      univ L := by
  apply LipschitzOnWith.approximatesLinearOn
  rw [lipschitzOnWith_univ]
  convert hV using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp

 def smallPerturbationHomeomorph (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) : ℂ ≃ₜ ℂ :=
  (approximatesLinearOn_id_add hV).toHomeomorph (fun z => z + V z)
    (Or.inr (by simpa using hL))

@[simp] lemma smallPerturbationHomeomorph_apply (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (z : ℂ) :
    smallPerturbationHomeomorph V hV hL z = z + V z := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalizedSmallPerturbation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local error with small differential gives an actual smooth ambient
perturbation, with exact values on the inner disk and compact support. -/
open Set Function Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

def localizedPlaneError (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ := planeScaledBump r z • f z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalInversionGerm
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inversion conjugate of a principal holomorphic exterior map has
an analytic germ at zero with derivative one. -/
open Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def principalInversionGerm (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun w => (F w⁻¹)⁻¹) 0 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceFlow
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete tangent trajectories on a compact relatively clopen piece of
an actual regular scalar level. This includes a prescribed Jordan boundary
without requiring the other components of its defining level to be bounded. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

structure CompactRegularPieceFlow (f : ℂ → ℝ) (a : ℝ) (K : Set ℂ) where
  field : ℂ → ℂ
  lipschitzConstant : ℝ≥0
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  lipschitz : LipschitzWith lipschitzConstant field
  tangent : ∀ z, (fderiv ℝ f z) (field z) = 0
  in_level : K ⊆ {z | f z = a}
  trajectory : K → ℝ → ℂ
  initial : ∀ z, trajectory z 0 = z.val
  equation : ∀ z t, HasDerivAt (trajectory z) (field (trajectory z t)) t
  scalar : ∀ z t, f (trajectory z t) = a
  member : ∀ z t, trajectory z t ∈ K
  trajectory_smooth : ∀ z, ContDiff ℝ ∞ (trajectory z)
  regular : ∀ z t, deriv (trajectory z) t ≠ 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceFlowOrbit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

lemma CompactRegularPieceFlow.trajectory_shift {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (s t : ℝ) :
    F.trajectory ⟨F.trajectory x s,F.member x s⟩ t = F.trajectory x (t+s) := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨F.equation ⟨F.trajectory x s,F.member x s⟩ u,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (by rw [F.initial,zero_add])
  exact congrFun h t

lemma CompactRegularPieceFlow.trajectory_shift_of_eq {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) {x y : {z // z ∈ K}} {s : ℝ}
    (hxy : F.trajectory x s = y.val) (t : ℝ) :
    F.trajectory y t = F.trajectory x (t+s) := by
  have hy : (⟨F.trajectory x s,F.member x s⟩ : {z // z ∈ K}) = y := Subtype.ext hxy
  simpa only [hy] using F.trajectory_shift x s t

lemma CompactRegularPieceFlow.periodic_of_return {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) {p : ℝ}
    (hp : F.trajectory x p = x.val) : Periodic (F.trajectory x) p := by
  intro t
  exact (F.trajectory_shift_of_eq hp t).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularPieceOpenOrbit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def CompactRegularPieceFlow.levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (t : ℝ) : {z // z ∈ K} :=
  ⟨F.trajectory x t,F.member x t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularPieceLeastPeriod
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

def CompactRegularPieceFlow.returnSubgroup {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) : AddSubgroup ℝ where
  carrier := {t | F.trajectory x t = x.val}
  zero_mem' := F.initial x
  add_mem' := by
    intro s t hs ht
    exact ((F.periodic_of_return x ht) s).trans hs
  neg_mem' := by
    intro t ht
    change F.trajectory x (-t) = x.val
    simpa only [zero_add] using ((F.periodic_of_return x ht).neg 0).trans (F.initial x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScaledGraphCover
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine dilation of a graph cover retains its diameter and cost
factors. The metric is the sup metric on the base and the vertical axis. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def graphAffine (c : ℝ × ℝ) (t s : ℝ) (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (c+s • p.1,t+s*p.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SortedCrossingChords
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sorting the actual crossed disks gives a finite ordered hole family
with an injective owner map and exact signed flux accounting. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 structure SortedCrossingChords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) where
  count : ℕ
  hole : Fin count → ℝ × ℝ
  owner : Fin count → I
  owner_mem : ∀ i, owner i ∈ crossingDisks c r y a b
  owner_injective : Injective owner
  owner_surjective : ∀ j ∈ crossingDisks c r y a b, ∃ i, owner i = j
  hole_eq : ∀ i, hole i = horizontalChord (c (owner i)) (r (owner i)) y
  inside : ∀ i, a < (hole i).1 ∧ (hole i).1 ≤ (hole i).2 ∧ (hole i).2 < b
  separated : ∀ i j, i < j → (hole i).2 < (hole j).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AdmissibleL2Convex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the actual L² classes with a nonnegative Borel,
pointwise-admissible representative for a specified family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def admissibleL2Classes {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : Set (Lp ℝ 2 σ) :=
  {v | ∃ f : Z → ℝ, ∃ hf : MemLp f 2 σ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
    (∀ a, 1 ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂(K a : Measure Z)) ∧ hf.toLp f = v}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ArgumentCircleIntegral
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized angular form has integral one on a positively
traversed round circle. Both the form and its tangent are actual derivatives. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def centeredArgument (c z : ℂ) : UnitAddCircle := normalizedArgument (z-c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexTangentFrame
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tangent and its quarter-turn form an invertible real planar frame. -/
open Function
noncomputable section
namespace CircleDomainRigidity

def complexTangentFrame (k : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight k +
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * k)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateSquares
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate squares, their exact areas, and the actual Sobolev Poincare estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def coordinateSquare (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) := closedBall c r

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorOmittedAreaInput
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantified numerical exterior-area bound: Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem,
Theorem 5-1, p.83. Only the omitted-area inequality for an injective
holomorphic exterior map with principal normalization is retained.
This is an explicit published-input parameter, not an axiom. -/
open Set Filter Function Metric Bornology Asymptotics
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def ExteriorOmittedAreaTheorem : Prop :=
    ∀ (F : ℂ → ℂ) (R : ℝ), 0 < R →
      DifferentiableOn ℂ F (closedBall (0 : ℂ) R)ᶜ →
      InjOn F (closedBall (0 : ℂ) R)ᶜ →
      (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) → ExteriorOmittedAreaBound F R

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_VerticalLevelCurve
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical parameter curves of a C1 inverse level chart. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def coareaVerticalLine (t s : ℝ) : ℂ := (t : ℂ) + s • Complex.I

@[simp] lemma coareaVerticalLine_re (t s : ℝ) : (coareaVerticalLine t s).re = t := by
  simp [coareaVerticalLine, Complex.real_smul]

@[simp] lemma coareaVerticalLine_im (t s : ℝ) : (coareaVerticalLine t s).im = s := by
  simp [coareaVerticalLine, Complex.real_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InverseChartCoarea
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted coarea inside a single regular level chart. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff Classical
noncomputable section
namespace CircleDomainRigidity

def inverseChartWeight (e : OpenPartialHomeomorph ℂ ℂ) (T : Set ℂ)
    (q : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  T.indicator (fun y => q (e.symm y) * ENNReal.ofReal ‖fderiv ℝ e.symm y Complex.I‖)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InversePieceJacobian
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact inverse Jacobian on a measurable scalar level-coordinate piece. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 def inversePieceWeight (F : ℂ → ℂ) (S T : Set ℂ) (q : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  T.indicator (fun y => q (invFunOn F S y) *
    ENNReal.ofReal ‖(fderiv ℝ F (invFunOn F S y)).inverse Complex.I‖)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.DiskMaximal_MaximalEstimates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace DiskMaximalTools

/-- A countable measurable envelope, sufficiently rich for every actual disk. -/
def rationalMaximal (ν : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q)

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MaximalTruncations
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded compactly supported increasing approximations to a nonnegative
L² function. Each fixed ball integral converges to the original integral. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def maximalInputTruncation (f : ℂ → ℝ) (n : ℕ) : ℂ → ℝ :=
  (closedBall 0 (n : ℝ)).indicator (fun x => min (f x) (n : ℝ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RescaledScalarBump
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed scalar cutoff translated to a level and rescaled to its
band width, with its exact derivative and support. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def rescaledScalarBump (t s : ℝ) (y : ℝ) : ℝ :=
  scalarCapacityBump ((y-t)/s)

lemma rescaledScalarBump_contDiff (t s : ℝ) :
    ContDiff ℝ 1 (rescaledScalarBump t s) :=
  scalarCapacityBump.contDiff.comp ((contDiff_id.sub contDiff_const).div_const s)

lemma rescaledScalarBump_deriv (t s y : ℝ) :
    deriv (rescaledScalarBump t s) y =
      deriv scalarCapacityBump ((y-t)/s) / s := by
  have hd := ((scalarCapacityBump.contDiff : ContDiff ℝ 1
    (scalarCapacityBump : ℝ → ℝ)).differentiable one_ne_zero ((y-t)/s)).hasDerivAt.comp y
      (((hasDerivAt_id y).sub_const t).div_const s)
  have he : (scalarCapacityBump : ℝ → ℝ) ∘ (fun x => (id x-t)/s) = rescaledScalarBump t s := rfl
  rw [he] at hd
  simpa only [one_div, div_eq_mul_inv, one_mul] using hd.deriv

lemma rescaledScalarBump_unit (t s y : ℝ) : rescaledScalarBump t s y ∈ Icc 0 1 :=
  ⟨scalarCapacityBump.nonneg,scalarCapacityBump.le_one⟩

lemma rescaledScalarBump_deriv_bound {C : ℝ}
    (hC : ∀ t, ‖deriv scalarCapacityBump t‖ ≤ C)
    (t : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    ‖deriv (rescaledScalarBump t s) y‖ ≤ C/s := by
  rw [rescaledScalarBump_deriv,norm_div,Real.norm_eq_abs s,abs_of_pos hs]
  exact div_le_div_of_nonneg_right (hC _) hs.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarRegularCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scalar coordinate maps with transverse real or imaginary coordinate.
Their Jacobians are the corresponding nonzero scalar partials. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

def scalarLevelCoordinate (f : ℂ → ℝ) (H : ℂ →L[ℝ] ℝ) : ℂ → ℂ :=
  fun z => (f z : ℂ) + H z • Complex.I

def scalarLevelDifferential (L H : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp L + (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).comp H

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRadialShrink
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth ambient radial contraction, fixed outside the larger disk.
It supplies the local shrinking step for analytic Jordan caps. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def radialShrinkFactor (t a b r : ℝ) : ℝ :=
  t+(1-t)*Real.smoothTransition ((r^2-a^2)/(b^2-a^2))

def radialShrink (t a b : ℝ) (z : ℂ) : ℂ :=
  radialShrinkFactor t a b ‖z‖ • z

lemma radialShrinkFactor_pos {t a b r : ℝ} (ht : 0<t) (ht1 : t≤1) :
    0 < radialShrinkFactor t a b r := by
  unfold radialShrinkFactor
  have := mul_nonneg (sub_nonneg.mpr ht1) (Real.smoothTransition.nonneg ((r^2-a^2)/(b^2-a^2)))
  linarith

lemma radialShrinkFactor_monotone {t a b : ℝ} (ht1 : t≤1) (ha : 0<a) (hab : a<b) :
    MonotoneOn (radialShrinkFactor t a b) (Ici 0) := by
  have hden : 0<b^2-a^2 := by nlinarith
  intro r hr s hs hrs
  unfold radialShrinkFactor
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _ hden.le
  have hr0 : 0 ≤ r := hr
  have hs0 : 0 ≤ s := hs
  nlinarith

lemma radialShrinkRadius_strictMono {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) :
    StrictMonoOn (fun r => radialShrinkFactor t a b r*r) (Ici 0) := by
  intro r hr s hs hrs
  calc
    radialShrinkFactor t a b r*r < radialShrinkFactor t a b r*s :=
      mul_lt_mul_of_pos_left hrs (radialShrinkFactor_pos ht ht1)
    _ ≤ radialShrinkFactor t a b s*s := mul_le_mul_of_nonneg_right
      (radialShrinkFactor_monotone ht1 ha hab hr hs hrs.le) hs

lemma radialShrink_norm {t a b : ℝ} (ht : 0<t) (ht1 : t≤1) (z : ℂ) :
    ‖radialShrink t a b z‖=radialShrinkFactor t a b ‖z‖*‖z‖ := by
  rw [radialShrink,norm_smul,Real.norm_eq_abs,abs_of_pos (radialShrinkFactor_pos ht ht1)]

lemma radialShrink_outer {t a b : ℝ} (ha : 0<a) (hab : a<b) {z : ℂ} (hz : b≤‖z‖) :
    radialShrink t a b z=z := by
  have hden : 0<b^2-a^2 := by nlinarith
  have harg : 1≤(‖z‖^2-a^2)/(b^2-a^2) := (le_div_iff₀ hden).mpr (by nlinarith)
  simp only [radialShrink,radialShrinkFactor,Real.smoothTransition.one_of_one_le harg,mul_one]
  have he : t+(1-t)=1 := by ring
  rw [he,one_smul]

lemma radialShrink_contDiff (t a b : ℝ) : ContDiff ℝ ∞ (radialShrink t a b) := by
  have hs : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖^2) := by
    simp only [Complex.sq_norm,Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (contDiff_const.add (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp ((hs.sub contDiff_const).div_const _)))).smul contDiff_id

lemma radialShrink_injective {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : Injective (radialShrink t a b) := by
  intro z w he
  have hn : ‖z‖=‖w‖ := (radialShrinkRadius_strictMono ht ht1 ha hab).injOn
    (norm_nonneg z) (norm_nonneg w) (by simpa only [radialShrink_norm ht ht1] using congrArg norm he)
  change radialShrinkFactor t a b ‖z‖ • z=radialShrinkFactor t a b ‖w‖ • w at he
  rw [hn] at he
  exact (smul_right_injective _ (radialShrinkFactor_pos ht ht1).ne') he

lemma radialShrink_surjective {t a b : ℝ} (_ht : 0<t) (_ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : Surjective (radialShrink t a b) := by
  intro y
  by_cases hy : y=0
  · subst y
    exact ⟨0,by simp [radialShrink]⟩
  have hypos : 0<‖y‖ := norm_pos_iff.mpr hy
  by_cases hyb : b≤‖y‖
  · exact ⟨y,radialShrink_outer ha hab hyb⟩
  have hb : 0<b := ha.trans hab
  have hc : Continuous (fun r => radialShrinkFactor t a b r*r) := by
    unfold radialShrinkFactor
    fun_prop
  have hbval : radialShrinkFactor t a b b*b=b := by
    have hd : b^2-a^2≠0 := by nlinarith
    simp [radialShrinkFactor,hd]
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc hb.le hc.continuousOn
    (show ‖y‖∈Icc (radialShrinkFactor t a b 0*0) (radialShrinkFactor t a b b*b) by
      rw [mul_zero,hbval];exact ⟨hypos.le,le_of_lt (lt_of_not_ge hyb)⟩)
  change radialShrinkFactor t a b r*r=‖y‖ at he
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r=0 := le_antisymm (le_of_not_gt hn) hr.1
    rw [hz,mul_zero] at he
    exact hypos.ne' he.symm
  refine ⟨(r/‖y‖) • y,?_⟩
  have hn : ‖(r/‖y‖) • y‖=r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hrpos hypos),div_mul_cancel₀ _ hypos.ne']
  unfold radialShrink
  rw [hn,smul_smul]
  have hfac : radialShrinkFactor t a b r*(r/‖y‖)=1 := by
    rw [←mul_div_assoc,he,div_self hypos.ne']
  rw [hfac,one_smul]

def smoothRadialShrinkHomeomorph {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : ℂ ≃ₜ ℂ := by
  let e := Equiv.ofBijective (radialShrink t a b)
    ⟨radialShrink_injective ht ht1 ha hab,radialShrink_surjective ht ht1 ha hab⟩
  have hc := (radialShrink_contDiff t a b).continuous
  have he : (fun z : ℂ => z)=ᶠ[cocompact ℂ] radialShrink t a b := by
    filter_upwards [(isCompact_closedBall (0:ℂ) b).compl_mem_cocompact] with z hz
    have hz' : b<‖z‖ := by
      simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hz
    exact (radialShrink_outer ha hab hz'.le).symm

  have hp : IsProperMap (radialShrink t a b) :=
    isProperMap_iff_tendsto_cocompact.mpr ⟨hc,tendsto_id.congr' he⟩
  exact e.toHomeomorphOfContinuousClosed hc hp.isClosedMap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactChartConjugation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a compactly supported deformation in an actual plane chart by
identity outside the chart. The support and smoothness are retained. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def chartConjugate (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ) (x : ℂ) : ℂ :=
  by
    classical
    exact if x∈e.target then e (T (e.symm x)) else x

lemma homeomorph_symm_eq_of_fixed {T : ℂ ≃ₜ ℂ} {x : ℂ} (hx : T x=x) : T.symm x=x := by
  apply T.injective
  rw [T.apply_symm_apply,hx]

lemma compactChart_maps_source (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) {x : ℂ} (hx : x∈e.source) :
    T x∈e.source := by
  by_contra hn
  have hfixed : T (T x)=T x := hfix _ (fun h => hn (hK h))
  have he : T x=x := T.injective hfixed
  rw [he] at hn
  exact hn hx

lemma chartConjugate_eq_off (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hfix : ∀x∉K,T x=x) {x : ℂ} (hx : x∉e '' K) :
    chartConjugate e T x=x := by
  unfold chartConjugate
  split_ifs with h
  · have hk : e.symm x∉K := fun hk => hx ⟨e.symm x,hk,e.right_inv h⟩
    rw [hfix _ hk,e.right_inv h]
  · rfl

lemma chartConjugate_left_inv (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) :
    LeftInverse (chartConjugate e T.symm) (chartConjugate e T) := by
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have ht := e.map_source hs
    change chartConjugate e T.symm (chartConjugate e T x)=x
    have hv : chartConjugate e T x=e (T (e.symm x)) := by
      rw [chartConjugate,ite_eq_left hx]
    rw [hv,chartConjugate,ite_eq_left ht,e.left_inv hs,T.symm_apply_apply,e.right_inv hx]
  · have hv : chartConjugate e T x=x := by rw [chartConjugate,ite_eq_right hx]
    rw [hv,chartConjugate,ite_eq_right hx]

lemma chartConjugate_continuous (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) :
    Continuous (chartConjugate e T) := by
  have himage : IsCompact (e '' K) := hKc.image_of_continuousOn (e.continuousOn.mono hK)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have he := e.continuousOn.continuousAt (e.open_source.mem_nhds hs)
    have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hx)
    have hT : ContinuousAt (T : ℂ → ℂ) (e.symm x) := T.continuous.continuousAt
    have hcomp : ContinuousAt (fun y => e (T (e.symm y))) x := ContinuousAt.comp (f := fun y => T (e.symm y)) (g := (e : ℂ → ℂ)) he
      (ContinuousAt.comp (f := (e.symm : ℂ → ℂ)) (g := (T : ℂ → ℂ)) hT hi)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    simp only [chartConjugate,ite_eq_left hy]
  · have ho : x∈(e '' K)ᶜ := by
      rintro ⟨z,hz,rfl⟩
      exact hx (e.map_source (hK hz))
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [himage.isClosed.isOpen_compl.mem_nhds ho] with y hy
    exact chartConjugate_eq_off e T hfix hy

def compactChartHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) : ℂ ≃ₜ ℂ :=
  { toFun := chartConjugate e T
    invFun := chartConjugate e T.symm
    left_inv := chartConjugate_left_inv e T hK hfix
    right_inv := chartConjugate_left_inv e T.symm hK
      (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx))
    continuous_toFun := chartConjugate_continuous e T hKc hK hfix
    continuous_invFun := chartConjugate_continuous e T.symm hKc hK
      (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx)) }

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicPathApproximation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic subdivision with quantitative oscillation and pointwise error
preservation when two replacement paths are concatenated. -/
open Set Function Filter Metric unitInterval
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def leftHalf (t : I) : I := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
def rightHalf (t : I) : I := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

def dyadicSmallOscillation {E : Type*} [PseudoMetricSpace E] : ℕ → (I → E) → ℝ → Prop
  | 0, f, ε => ∀ s t, dist (f s) (f t) < ε
  | n + 1, f, ε => dyadicSmallOscillation n (f ∘ leftHalf) ε ∧
      dyadicSmallOscillation n (f ∘ rightHalf) ε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicPathReplacement
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace a finely subdivided map by a path whose endpoints lie in a
fixed set, preserving a uniform error and a prescribed neighborhood. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def halfTime : I := ⟨1 / 2, by constructor <;> norm_num⟩
@[simp] lemma leftHalf_zero : leftHalf 0 = 0 := by apply Subtype.ext; norm_num [leftHalf]
@[simp] lemma leftHalf_one : leftHalf 1 = halfTime := by apply Subtype.ext; norm_num [leftHalf, halfTime]
@[simp] lemma rightHalf_zero : rightHalf 0 = halfTime := by apply Subtype.ext; norm_num [rightHalf, halfTime]
@[simp] lemma rightHalf_one : rightHalf 1 = 1 := by apply Subtype.ext; norm_num [rightHalf]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ExteriorCoefficientCircle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite coefficient lower bound on each exterior circle,
retaining the actual Laurent coefficients and the derivative energy. -/
open Set Filter Function Metric Real MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def principalLaurentCoefficient (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  diskTaylorCoefficient (invertedPrincipalRemainder F) (n+1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HolomorphicPlaneChart
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth plane chart and inverse supplied by a holomorphic
injection on an open set. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def holomorphicPlaneChart {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    OpenPartialHomeomorph ℂ ℂ where
  toPartialEquiv := hi.toPartialEquiv f U
  open_source := hU
  open_target := holomorphic_injOn_isOpen_image hU hf hi hU Subset.rfl
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := by
    rintro y ⟨x,hx,rfl⟩
    exact (continuousAt_holomorphic_invFunOn hU hf hi hx).continuousWithinAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LooplessTimeCoordinate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous monotone coordinates on a loopless path. Prefix distances
separate distinct fibers; running maxima are constant on every pause. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def prefixDistance (g : C(unitInterval, X)) (a : unitInterval) : C(unitInterval, ℝ) :=
  ⟨fun t => min 1 (infDist (g t) (g '' Iic a)),
    continuous_const.min ((continuous_infDist_pt (g '' Iic a)).comp g.continuous)⟩

lemma prefixDistance_nonneg (g : C(unitInterval, X)) (a t : unitInterval) :
    0 ≤ prefixDistance g a t := le_min zero_le_one infDist_nonneg

lemma prefixDistance_le_one (g : C(unitInterval, X)) (a t : unitInterval) :
    prefixDistance g a t ≤ 1 := min_le_left _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LooplessSeparatingCoordinate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single continuous monotone real coordinate with exactly the fibers
of a loopless metric path. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def looplessCoordinateTerm (g : C(unitInterval, X)) (n : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => (1 / 2 : ℝ)^n * runningMaximum (prefixDistance g (denseSeq unitInterval n)) t,
    continuous_const.mul (runningMaximum _).continuous⟩

lemma looplessCoordinateTerm_nonneg (g : C(unitInterval, X)) (n : ℕ) (t : unitInterval) :
    0 ≤ looplessCoordinateTerm g n t :=
  mul_nonneg (by positivity) (runningMaximum_nonneg _ _)

lemma looplessCoordinateTerm_le (g : C(unitInterval, X)) (n : ℕ) (t : unitInterval) :
    looplessCoordinateTerm g n t ≤ (1 / 2 : ℝ)^n := by
  apply (mul_le_mul_of_nonneg_left _ (by positivity)).trans_eq (mul_one _)
  exact runningMaximum_le _ (prefixDistance_nonneg _ _) zero_le_one
    (fun u _ => prefixDistance_le_one _ _ u)

def looplessCoordinate (g : C(unitInterval, X)) : C(unitInterval, ℝ) where
  toFun t := ∑' n, looplessCoordinateTerm g n t
  continuous_toFun := by
    apply continuous_tsum (fun n => (looplessCoordinateTerm g n).continuous) summable_geometric_two
    intro n t
    rw [Real.norm_eq_abs, abs_of_nonneg (looplessCoordinateTerm_nonneg g n t)]
    exact looplessCoordinateTerm_le g n t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarMapChangeVariables
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of variables from real product parameters to the physical complex
plane, with the actual two-column Jacobian. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def planarMapJacobian (A : (ℝ × ℝ) →L[ℝ] ℂ) : ℝ :=
  (A (1,0)).re * (A (0,1)).im - (A (1,0)).im * (A (0,1)).re

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPerturbationJordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small smooth ambient perturbations preserve regular Jordan curves. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

 def scaledPerturbationHomeomorph (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (ρ : Icc (0 : ℝ) 1) : ℂ ≃ₜ ℂ :=
  smallPerturbationHomeomorph (fun z => (ρ : ℝ) • V z) ((lipschitzWith_smul (ρ : ℝ)).comp hV) (by
    have hr : ‖(ρ : ℝ)‖₊ ≤ 1 := by
      change ‖(ρ : ℝ)‖ ≤ (1 : ℝ)
      simpa only [Real.norm_eq_abs, abs_of_nonneg ρ.property.1] using ρ.property.2
    exact (mul_le_of_le_one_left (by positivity) hr).trans_lt hL)

@[simp] lemma scaledPerturbationHomeomorph_apply (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (ρ : Icc (0 : ℝ) 1) (z : ℂ) :
    scaledPerturbationHomeomorph V hV hL ρ z = z + (ρ : ℝ) • V z := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GraphGridCells
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equal-scale three-dimensional cells, colored by sixteen residues
in each coordinate. Enlarged balls in one color are disjoint. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

abbrev GraphGridColor := (Fin 16 × Fin 16) × Fin 16
abbrev GraphGridIndex := (ℤ × ℤ) × ℤ
abbrev GraphSpace := (ℝ × ℝ) × ℝ

def graphGridInterval (r : Fin 16) (k : ℤ) (s : ℝ) : Set ℝ :=
  Icc ((16*(k:ℝ)+(r:ℕ))*s) ((16*(k:ℝ)+(r:ℕ)+1)*s)

def graphGridCell (r : GraphGridColor) (k : GraphGridIndex) (s : ℝ) : Set GraphSpace :=
  (graphGridInterval r.1.1 k.1.1 s ×ˢ graphGridInterval r.1.2 k.1.2 s) ×ˢ
    graphGridInterval r.2 k.2 s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RadialShrinkImages
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact disk images of the ambient radial shrinker. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

@[simp] lemma smoothRadialShrinkHomeomorph_apply {t a b : ℝ}
    (ht : 0<t) (ht1 : t≤1) (ha : 0<a) (hab : a<b) (z : ℂ) :
    smoothRadialShrinkHomeomorph ht ht1 ha hab z=radialShrink t a b z := rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ComplexRectangleLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Morera passage for smooth maps with vanishing antiholomorphic
error. Uniform convergence is needed only on the four compact edges. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def complexRectangleFlux (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫x : ℝ in z.re..w.re,f (x+z.im*I))-(∫x : ℝ in z.re..w.re,f (x+w.im*I))+
    I*(∫y : ℝ in z.im..w.im,f (w.re+y*I))-I*(∫y : ℝ in z.im..w.im,f (z.re+y*I))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCoefficientRadial
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact integration of a finite Laurent coefficient energy sum. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def finiteCoefficientRadialDensity (d : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  2*Real.pi*r*(1+∑ n ∈ Finset.range N,
    ((n : ℝ)+1)^2*d n*(r⁻¹)^(2*(n+2)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_CyclicCircularization
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fair finite schedule and simultaneous compactness of the actual
round disks selected during its cycles. No assertion of limiting
roundness for the later, deformed configurations is assumed here. -/
open Set Function Metric Filter
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration

def cyclicSchedule (m : ℕ) (n : ℕ) : Fin (m+1) := ⟨n%(m+1),Nat.mod_lt _ (by omega)⟩

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MetricBeltramiCoefficient
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.blendMetric_identity _root_.OAI.CircleDomainRigidity.FiniteTransfer.covectorEnergy_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded complex coefficient of a positive planar metric. This is
 the coefficient needed for the smooth metric-sphere uniformization input. -/
open Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def metricBeltramiDenominator (A : PlanarMetric) : ℝ :=
  A 0 0 + A 1 1 + 2 * Real.sqrt A.det

def metricBeltramiCoefficient (A : PlanarMetric) : ℂ :=
  (⟨A 0 0 - A 1 1, 2 * A 0 1⟩ : ℂ) / (metricBeltramiDenominator A : ℂ)

@[simp] lemma metricBeltramiCoefficient_scalar (r : ℝ) :
    metricBeltramiCoefficient (r • (1 : PlanarMetric)) = 0 := by
  unfold metricBeltramiCoefficient
  have hn : (⟨(r • (1 : PlanarMetric)) 0 0 - (r • (1 : PlanarMetric)) 1 1,
      2 * (r • (1 : PlanarMetric)) 0 1⟩ : ℂ) = 0 := by
    apply Complex.ext <;> simp [Matrix.smul_apply]
  rw [hn, zero_div]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalCoefficientConvergence
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform compact support turns bounded coefficient approximation into
strong L2 convergence. The bound retains the same coefficient radius. -/
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma compact_coefficient_memLp {μ : ℂ → ℂ} {K : Set ℂ} {k : ℝ}
    (hm : AEStronglyMeasurable μ volume) (hK : IsCompact K)
    (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (hs : ∀ z ∉ K, μ z = 0) :
    MemLp μ 2 volume := by
  have hB : MemLp (K.indicator (fun _ : ℂ => (k : ℂ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  apply hB.of_le hm
  filter_upwards [] with z
  by_cases hz : z ∈ K
  · simpa only [indicator_of_mem hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hk] using hb z
  · simp only [hs z hz, norm_zero, indicator_of_notMem hz, le_refl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SquareAverageLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking square averages recover the specified continuous representative. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def squareAverage (f : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (r : ℝ) : ℝ :=
  ⨍ p in coordinateSquare c r, f p

end CircleDomainRigidity

end

end OAI
end



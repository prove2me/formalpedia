-- Prove2me | Definitions.Def_OAIQ095D002
-- name    : OAIQ095D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:55:56.648912+00:00
-- url     : https://prove2.me/theorems/a8912c8c-cd41-4856-96dc-b631b8bb0fc9
-- title:
--   Definitions bundle OAIQ095D002 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 993 declarations of OpenAI's Lean: 782 definitions, 13 instances and 198 theorems. The definitions and types are `OAI.Ostmann.actionPermutation`, `OAI.Ostmann.additiveAutocorrelation`, `OAI.Ostmann.additiveCharacterSum`, `OAI.Ostmann.additiveConvolution`, `OAI.Ostmann.additiveDifferenceConvolution`, `OAI.Ostmann.additiveFiberEquiv`, `OAI.Ostmann.affineAction`, `OAI.Ostmann.affineAverage`, `OAI.Ostmann.affineAverageAdjoint`, `OAI.Ostmann.affineCoefficient`, `OAI.Ostmann.affineCoefficientSum`, `OAI.Ostmann.affineFourierMatrix`, `OAI.Ostmann.affineGenerator`, `OAI.Ostmann.affineGeneratorEquiv`, `OAI.Ostmann.affineGeneratorInv`, `OAI.Ostmann.affineParameters`, `OAI.Ostmann.allMultipleTuples`, `OAI.Ostmann.amplificationPrimeCount`, `OAI.Ostmann.approximationLift`, `OAI.Ostmann.archimedeanLeafFactor`, `OAI.Ostmann.arithmeticTestFlag`, `OAI.Ostmann.atomAncestorSet`, `OAI.Ostmann.atomFixedProduct`, `OAI.Ostmann.averagedCoordinates`, `OAI.Ostmann.backwardTargets`, `OAI.Ostmann.badDivisorMultipliers`, `OAI.Ostmann.badEndpoints`, `OAI.Ostmann.badPartitionCost`, `OAI.Ostmann.balancedTupleSet`, `OAI.Ostmann.binnedWordAverage`, `OAI.Ostmann.boolFinsetEquiv`, `OAI.Ostmann.booleanEnergy`, `OAI.Ostmann.booleanMoment`, `OAI.Ostmann.booleanPolynomial`, `OAI.Ostmann.bottomPairValue`, `OAI.Ostmann.boundedCellLists`, `OAI.Ostmann.boundedDyadicIndex`, `OAI.Ostmann.boundedSieveSubsets`, `OAI.Ostmann.bulkArrayEquiv`, `OAI.Ostmann.bulkCellMixture` and 742 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_ArithmeticCRTSeparation`, `Ostmann_Arithmetic_ArithmeticFrequencyTree`, `Ostmann_Arithmetic_ArithmeticGoodPatternRate`, `Ostmann_Arithmetic_ArithmeticIntegerComparison`, `Ostmann_Arithmetic_ArithmeticLifts`, `Ostmann_Arithmetic_ArithmeticLineComparison`, `Ostmann_Arithmetic_ArithmeticLineIntegration`, `Ostmann_Arithmetic_ArithmeticLines`, `Ostmann_Arithmetic_ArithmeticQuadraticCoefficient`, `Ostmann_Arithmetic_ArithmeticSpectatorHistory`, `Ostmann_Arithmetic_BulkCellMixtures`, `Ostmann_Arithmetic_BulkKernelPairComparison`, `Ostmann_Arithmetic_BulkLogWeightedKernelPairComparison`, `Ostmann_Arithmetic_BulkResidueCRT`, `Ostmann_Arithmetic_BulkSymmetrization`, `Ostmann_Arithmetic_CRTLineAverage`, `Ostmann_Arithmetic_CRTResidueAverage`, `Ostmann_Arithmetic_CommonHistoryPeriod`, `Ostmann_Arithmetic_FiniteRootFibres`, `Ostmann_Arithmetic_FiniteSeparatedHeight`, `Ostmann_Arithmetic_FrozenSupportedArithmetic`, `Ostmann_Arithmetic_IntegerIntervalVariation`, `Ostmann_Arithmetic_InternalLineProbability`, `Ostmann_Arithmetic_InternalPatternWeight`, `Ostmann_Arithmetic_LcmFrequencySum`, `Ostmann_Arithmetic_MovingAmplitudeTerms`, `Ostmann_Arithmetic_MovingBadHarmonicBudget`, `Ostmann_Arithmetic_MovingCompactLeaf`, `Ostmann_Arithmetic_MovingCompensationGapList`, `Ostmann_Arithmetic_MovingCompensationTargets`, `Ostmann_Arithmetic_MovingDiagonalOuterWeight`, `Ostmann_Arithmetic_MovingFourierVariation`, `Ostmann_Arithmetic_MovingFrequencyBudget`, `Ostmann_Arithmetic_MovingFullLiveTransformTransfer`, `Ostmann_Arithmetic_MovingFullTransformTransfer`, `Ostmann_Arithmetic_MovingGiantPhase`, `Ostmann_Arithmetic_MovingGuardedRow`, `Ostmann_Arithmetic_MovingInternalErrorRate`, `Ostmann_Arithmetic_MovingKernelRates`, `Ostmann_Arithmetic_MovingOneGiant`, `Ostmann_Arithmetic_MovingOriginalPatternSum`, `Ostmann_Arithmetic_MovingOuterJointComparison`, `Ostmann_Arithmetic_MovingPatternBulkFubini`, `Ostmann_Arithmetic_MovingPatternBulkLog`, `Ostmann_Arithmetic_MovingPatternModulusRange`, `Ostmann_Arithmetic_MovingPatternPrimeSupport`, `Ostmann_Arithmetic_MovingPatternRegularUnits`, `Ostmann_Arithmetic_MovingPrimeNodeFactor`, `Ostmann_Arithmetic_MovingProductFrequency`, `Ostmann_Arithmetic_MovingProductGapBudget`, `Ostmann_Arithmetic_MovingProtectedTarget`, `Ostmann_Arithmetic_MovingRealCells`, `Ostmann_Arithmetic_MovingRealResidues`, `Ostmann_Arithmetic_MovingRecursiveProductBounds`, `Ostmann_Arithmetic_MovingRecursiveTemplateCaps`, `Ostmann_Arithmetic_MovingRegularDiagonal`, `Ostmann_Arithmetic_MovingRegularLiveOffDiagonal`, `Ostmann_Arithmetic_MovingRegularOffDiagonal`, `Ostmann_Arithmetic_MovingRegularTransfer`, `Ostmann_Arithmetic_MovingSumFactors`, `Ostmann_Arithmetic_MovingTemplateLiveRaw`, `Ostmann_Arithmetic_MovingTemplateLiveTransfer`, `Ostmann_Arithmetic_MovingTemplateSupport`, `Ostmann_Arithmetic_MovingTopCells`, `Ostmann_Arithmetic_MovingTransferTransform`, `Ostmann_Arithmetic_NonbulkHarmonicBudget`, `Ostmann_Arithmetic_OneSidedGraphFactor`, `Ostmann_Arithmetic_PrimeTupleResidueRow`, `Ostmann_Arithmetic_RangedPairNumericBudget`, `Ostmann_Arithmetic_ReconstructedPhaseWeight`, `Ostmann_Arithmetic_RecursiveLeafExpansion`, `Ostmann_Arithmetic_RecursiveSupportExpansion`, `Ostmann_Arithmetic_ReducedFrequencyEnergy`, `Ostmann_Arithmetic_ResidueIntervals`, `Ostmann_Arithmetic_SampledTupleAmplitude`, `Ostmann_Arithmetic_ScaledPoisson`, `Ostmann_Arithmetic_SignedSplitSupport`, `Ostmann_Arithmetic_SingleFrequencyTree`, `Ostmann_Arithmetic_SplitPrefixProducts`, `Ostmann_Arithmetic_SplitSquareSupport`, `Ostmann_Arithmetic_SquareCongruence`, `Ostmann_Arithmetic_SymbolicLineComparison`, `Ostmann_Arithmetic_SymmetrizedPairBound`, `Ostmann_Arithmetic_WeightedIntegerIntervals`, `Ostmann_Arithmetic_WeightedIntervalMass`, `Ostmann_Arithmetic_WholeShellGeometry`, `Ostmann_Characters_AffineAction`, `Ostmann_Characters_AffineCoefficients`, `Ostmann_Characters_AffineFibers`, `Ostmann_Characters_AffineFourier`, `Ostmann_Characters_AffineMean`, `Ostmann_Characters_AffineOperator`, `Ostmann_Characters_BonamiCube`, `Ostmann_Characters_BonamiInput`, `Ostmann_Characters_BonamiMonomialFamily`, `Ostmann_Characters_BonamiTensor`, `Ostmann_Characters_BottomPairMellin`, `Ostmann_Characters_CharacterAtomIteration`, `Ostmann_Characters_CharacterBandGeometry`, `Ostmann_Characters_CharacterCellCovering`, `Ostmann_Characters_CharacterConstructedTargets`, `Ostmann_Characters_CharacterFourthBound`, `Ostmann_Characters_CharacterFourthMoment`, `Ostmann_Characters_CharacterIndexCutoff`, `Ostmann_Characters_CharacterInitialProduct`, `Ostmann_Characters_CharacterIntervalGeometry`, `Ostmann_Characters_CharacterMeanRotation`, `Ostmann_Characters_CharacterRoundedEndpoint`, `Ostmann_Characters_CharacterSelectedShellGeometry`, `Ostmann_Characters_CharacterSelectionBudget`, `Ostmann_Characters_CharacterSelectionScales`, `Ostmann_Characters_CharacterTargetCenters`, `Ostmann_Characters_CharacterTargetGaps`, `Ostmann_Characters_ConcreteQuartetFourier`, `Ostmann_Characters_ConjugatedPairMeans`, `Ostmann_Characters_CycleAction`, `Ostmann_Characters_CycleMellin`, `Ostmann_Characters_DifferenceMoment`, `Ostmann_Characters_FieldPairMoment`, `Ostmann_Characters_FiniteKernelBlocks`, `Ostmann_Characters_FiniteKernelCoordinates`, `Ostmann_Characters_FiniteKernelLinearMaps`, `Ostmann_Characters_FiniteKernelOperator`, `Ostmann_Characters_FiniteKernelPairing`, `Ostmann_Characters_GaussFourthMoment`, `Ostmann_Characters_HeldCycleAverage`, `Ostmann_Characters_HigherCharacterDecorrelation`, `Ostmann_Characters_Mellin`, `Ostmann_Characters_MellinDiagonal`, `Ostmann_Characters_MellinParseval`, `Ostmann_Characters_NormalizedCharacterPoisson`, `Ostmann_Characters_PermutedAdditiveCancellation`, `Ostmann_Characters_PivotLossBudget`, `Ostmann_Characters_PivotRowPhase`, `Ostmann_Characters_PivotSquareExpansion`, `Ostmann_Characters_PivotSquareSplit`, `Ostmann_Characters_PivotTargetScale`, `Ostmann_Characters_PolynomialCellSupports`, `Ostmann_Characters_PolynomialCircleEstimate`, `Ostmann_Characters_PolynomialKernelCoordinates`, `Ostmann_Characters_PolynomialLineFlags`, `Ostmann_Characters_PolynomialRootCells`, `Ostmann_Characters_PrimeCRTFourier`, `Ostmann_Characters_ProductMellinParseval`, `Ostmann_Characters_QuartetConjugation`, `Ostmann_Characters_QuartetCrossBound`, `Ostmann_Characters_QuartetCutAverages`, `Ostmann_Characters_QuartetExpansion`, `Ostmann_Characters_QuartetFourier`, `Ostmann_Characters_QuartetFriendlyCoordinates`, `Ostmann_Characters_QuartetHorizontalMean`, `Ostmann_Characters_QuartetLocalBounds`, `Ostmann_Characters_QuartetOrientations`, `Ostmann_Characters_QuartetOrientedValue`, `Ostmann_Characters_QuartetParseval`, `Ostmann_Characters_QuartetProductProjection`, `Ostmann_Characters_QuartetProjectedCut`, `Ostmann_Characters_QuartetSamePairBound`, `Ostmann_Characters_QuartetSpectrumBound`, `Ostmann_Characters_QuartetSymmetry`, `Ostmann_Characters_QuartetTestSymmetries`, `Ostmann_Characters_QuartetTotalMoment`, `Ostmann_Characters_QuartetTreeSmallParameters`, `Ostmann_Characters_RademacherMoments`, `Ostmann_Characters_RatioParseval`, `Ostmann_Characters_ReciprocalTwist`, `Ostmann_Characters_RepeatedCharacterCancellation`, `Ostmann_Characters_RepeatedPrimePeriod`, `Ostmann_Characters_RescaledWeightVariation`, `Ostmann_Characters_SchwartzWeightVariation`, `Ostmann_Characters_SparseConductorCutoff`, `Ostmann_Characters_SparseKernelEnergy`, `Ostmann_Characters_SparseKernelScalar`, `Ostmann_Characters_SparseKernelUnitFactor`, `Ostmann_Characters_SparseMellinCoefficients`, `Ostmann_Characters_SparsePrimitiveExpansion`, `Ostmann_Characters_SparseProductCharacter`, `Ostmann_Characters_SparseResidueMatrix`, `Ostmann_Characters_SparseTensorModes`, `Ostmann_Characters_SparseTransformSpectrum`, `Ostmann_Characters_SparseTruncatedWeight`, `Ostmann_Characters_SparseUnitPolydisc`, `Ostmann_Characters_SparseWeightMellinExpansion`, `Ostmann_Characters_SquareCharacterMass`, `Ostmann_Characters_SquarePullback`, `Ostmann_Characters_SquareRatioCoefficient`, `Ostmann_Characters_SquarefreeBonami`, `Ostmann_Characters_TensorKernelEnergy`, `Ostmann_Characters_TensorRamanujanExpansion`, `Ostmann_Characters_TreeCoordinates`, `Ostmann_Characters_TupleCRTFourier`, `Ostmann_Characters_TupleCharacterPoisson`, `Ostmann_Characters_TwistCauchy`, `Ostmann_Characters_UniformMellin`, `Ostmann_Characters_UnitRamanujanProduct`, `Ostmann_Characters_WeightedPhaseExtraction`, `Ostmann_Construction_AllMultipleTupleWeight`, `Ostmann_Construction_AtomAncestorSources`, `Ostmann_Construction_BackwardTargets`, `Ostmann_Construction_CellRoleBudget`, `Ostmann_Construction_CollisionTestTransfer`, `Ostmann_Construction_ConstituentFinalCostData`, `Ostmann_Construction_ConstituentInitialAmplitude`, `Ostmann_Construction_ConstituentPairFactors`, `Ostmann_Construction_CopiedDirectedPhase`, `Ostmann_Construction_DiagonalGapBudget`, `Ostmann_Construction_DiagonalRegularMultiplier`, `Ostmann_Construction_DiagonalTransfer`, `Ostmann_Construction_DirectedPrimePhase`, `Ostmann_Construction_DistinctTupleProducts`, `Ostmann_Construction_DoubledWordExpansion`, `Ostmann_Construction_DyadicHarmonicBias`, `Ostmann_Construction_DyadicPrimeSelection`, `Ostmann_Construction_DyadicSupportedHistory`, `Ostmann_Construction_EndpointBaseScale`, `Ostmann_Construction_EndpointTestScale`, `Ostmann_Construction_ExpandedWordPairBound`, `Ostmann_Construction_ExponentialSampling`, `Ostmann_Construction_ExternalResidueReduction`, `Ostmann_Construction_FillerTargetScale`, `Ostmann_Construction_FiniteBiasPopulation`, `Ostmann_Construction_FiniteCellPrior`, `Ostmann_Construction_FiniteEmbeddingPrior`, `Ostmann_Construction_FiniteFormulaRenaming`, `Ostmann_Construction_FiniteFrequencyExpansion`, `Ostmann_Construction_FiniteMatchedWindow`, `Ostmann_Construction_FiniteProductPrior`, `Ostmann_Construction_FixedPivotGraphEmbedding`, `Ostmann_Construction_FixedPivotPrimeChecks`, `Ostmann_Construction_FrozenInitialSmallAmplitude`, `Ostmann_Construction_FrozenInitialSpectatorData`, `Ostmann_Construction_FrozenPrimeDeletions`, `Ostmann_Construction_GiantCoprimeIntervals`, `Ostmann_Construction_GiantDiscreteTransport`, `Ostmann_Construction_GiantLogMeasures`, `Ostmann_Construction_GiantOuterFactors`, `Ostmann_Construction_GiantTransformProduct`, `Ostmann_Construction_GoodCellSelection`, `Ostmann_Construction_GoodCellTargets`, `Ostmann_Construction_GroupedPhaseFactorization`, `Ostmann_Construction_GroupedPivotPhase`, `Ostmann_Construction_GroupedResidueRow`, `Ostmann_Construction_HalfPrimeFactorization`, `Ostmann_Construction_HalfPrimeStatistic`, `Ostmann_Construction_HarmonicInitialAmplitude`, `Ostmann_Construction_HistoryGiantSources`, `Ostmann_Construction_HistorySmoothFactor`, `Ostmann_Construction_InfiniteSplitMass`, `Ostmann_Construction_InitialCellPriors`, `Ostmann_Construction_InitialCellSchedule`, `Ostmann_Construction_InitialGaussMultipliers`, `Ostmann_Construction_InitialLogSumBins`, `Ostmann_Construction_InitialMixedNormalizer`, `Ostmann_Construction_InitialMovingAverage`, `Ostmann_Construction_InitialMovingTests`, `Ostmann_Construction_InitialProtectedTarget`, `Ostmann_Construction_InitialSmallCellList`, `Ostmann_Construction_InitialSpectatorFourier`, `Ostmann_Construction_InitialSpectatorSplit`, `Ostmann_Construction_InitialWordAtomIntervals`, `Ostmann_Construction_InitialWordCoordinates`, `Ostmann_Construction_InjectiveCoefficientTransport`, `Ostmann_Construction_IntegerIntervalCoordinates`, `Ostmann_Construction_IntegerIntervalDistribution`, `Ostmann_Construction_LogCellFamilyWindow`, `Ostmann_Construction_MatchedGraphQuotient`, `Ostmann_Construction_MatchedRetainedPhase`, `Ostmann_Construction_OppositeBiasTransfer`, `Ostmann_Construction_OriginalKernelDecomposition`, `Ostmann_Construction_OriginalParameterChoice`, `Ostmann_Construction_OriginalPivotTransfer`, `Ostmann_Construction_OriginalTupleLifts`, `Ostmann_Construction_PhaseGiantTest`, `Ostmann_Construction_PhysicalAmplification`, `Ostmann_Construction_PositiveFourierCutoff`, `Ostmann_Construction_PositiveWordBins`, `Ostmann_Construction_PositiveWordStatistic`, `Ostmann_Construction_PrimeAlphabet`, `Ostmann_Construction_PrimeBulkInsertion`, `Ostmann_Construction_PrimeCellProductIntervals`, `Ostmann_Construction_PrimeDiagonalMatching`, `Ostmann_Construction_PrimeExternalAverage`, `Ostmann_Construction_PrimeFamilyEnumeration`, `Ostmann_Construction_PrimeLogCellMeasure`, `Ostmann_Construction_PrimeLogGrid`, `Ostmann_Construction_PrimeMaskExtension`, `Ostmann_Construction_PrimeMatchingSupport`, `Ostmann_Construction_PrimeTupleTranslation`, `Ostmann_Construction_PrimeWordEmbedding`, `Ostmann_Construction_RegularDiagonalCancellation`, `Ostmann_Construction_RegularGiantMultiplier`, `Ostmann_Construction_RepeatedPhysicalTests`, `Ostmann_Construction_RepeatedTuplePoisson`, `Ostmann_Construction_ScheduleWordUnary`, `Ostmann_Construction_ScheduledAnalyticParameters`, `Ostmann_Construction_ScheduledAnchorGraph`, `Ostmann_Construction_ScheduledComparisonCounts`, `Ostmann_Construction_ScheduledComparisonCutoffs`, `Ostmann_Construction_ScheduledDiagonalLengths`, `Ostmann_Construction_ScheduledIntegerRigidity`, `Ostmann_Construction_ScheduledPreorderNodes`, `Ostmann_Construction_ScheduledRegularUnary`, `Ostmann_Construction_SelectedBulkPermutation`, `Ostmann_Construction_SelectedCellGap`, `Ostmann_Construction_SelectedCellTiers`, `Ostmann_Construction_SelectedCompensationPrior`, `Ostmann_Construction_SelectedInitialProductWindow`, `Ostmann_Construction_SelectedPrimeFubini`, `Ostmann_Construction_SelectedScheduledTransfer`, `Ostmann_Construction_SeparatedPhasePacking`, `Ostmann_Construction_SignedAtomSchedule`, `Ostmann_Construction_SignedBulkGain`, `Ostmann_Construction_SmallPrimeSubset`, `Ostmann_Construction_SmoothGiantLiveSupport`, `Ostmann_Construction_SmoothGiantPrior`, `Ostmann_Construction_SmoothGiantSupport`, `Ostmann_Construction_SmoothLogCellProfile`, `Ostmann_Construction_SpectatorBulkScale`, `Ostmann_Construction_SupportedPivotTuples`, `Ostmann_Construction_SupportedRegularInitialAmplitude`, `Ostmann_Construction_TopWordBinScale`, `Ostmann_Construction_TransferAdditiveProduct`, `Ostmann_Construction_TransferCompletePhase`, `Ostmann_Construction_TransferDirectedPhase`, `Ostmann_Construction_TransferGapRanges`, `Ostmann_Construction_TransferGraphPhase`, `Ostmann_Construction_TransferGraphRows`, `Ostmann_Construction_TransferRoundedCutoffs`, `Ostmann_Construction_TransferTupleCoordinates`, `Ostmann_Construction_TupleFrequencyCutoff`, `Ostmann_Construction_TypicalCharacterEndpoints`, `Ostmann_Construction_TypicalEndpoints`, `Ostmann_Construction_WeightedRepeatRemoval`, `Ostmann_Construction_WeightedWordLeaves`, `Ostmann_Construction_WholePrimeGrid`, `Ostmann_Construction_WordCharacterRemoval`, `Ostmann_Construction_WordCharacterStatistic`, `Ostmann_Construction_WordCopyCoordinates`, `Ostmann_Construction_WordGraphAmplitude`, `Ostmann_Construction_WordPeriodBudget`, `Ostmann_Defs`, `Ostmann_FiniteCRT`, `Ostmann_Preliminaries_Autocorrelation`, `Ostmann_Preliminaries_BoundedSieveSubsets`, `Ostmann_Preliminaries_CircleSeparatedPoints`, `Ostmann_Preliminaries_CosecantDistanceBound`, `Ostmann_Preliminaries_CosecantHilbertBound`, `Ostmann_Preliminaries_CosecantKernel`, `Ostmann_Preliminaries_CosecantMatrix`, `Ostmann_Preliminaries_FiniteBlockMatrix`, `Ostmann_Preliminaries_FiniteCauchyEstimate`, `Ostmann_Preliminaries_FinitePolynomialTail`, `Ostmann_Preliminaries_FixedShiftMertensWeights`, `Ostmann_Preliminaries_FixedShiftResidues`, `Ostmann_Preliminaries_MertensFromFirst`, `Ostmann_Preliminaries_MertensHarmonicBands`, `Ostmann_Preliminaries_MertensPrimeBands`, `Ostmann_Preliminaries_PhaseDistance`, `Ostmann_Preliminaries_PrimeReciprocalLogBudget`, `Ostmann_Preliminaries_Residues`, `Ostmann_Preliminaries_SeparatedAdditiveSieve`, `Ostmann_Preliminaries_SieveDualEnergy`, `Ostmann_Preliminaries_SieveGeometricKernel`, `Ostmann_Preliminaries_SummandSizePrimeBand`, `Ostmann_Preliminaries_TwoBadFourier`, `Ostmann_Preliminaries_WeightedCollision`, `Ostmann_QuadraticCenter_ClosedQuadraticBand`, `Ostmann_QuadraticCenter_ConductorKernelCandidates`, `Ostmann_QuadraticCenter_DivisorWeightedCoefficient`, `Ostmann_QuadraticCenter_DyadicKernelShells`, `Ostmann_QuadraticCenter_FourthMomentFamily`, `Ostmann_QuadraticCenter_FullQuadraticCoefficient`, `Ostmann_QuadraticCenter_HalfKernel`, `Ostmann_QuadraticCenter_IntegerKernelScale`, `Ostmann_QuadraticCenter_IntegerPoissonTransform`, `Ostmann_QuadraticCenter_MaximalQuadraticBias`, `Ostmann_QuadraticCenter_PopulatedKernelSelection`, `Ostmann_QuadraticCenter_PositiveQuadraticInverse`, `Ostmann_QuadraticCenter_PrimeDivisorIndices`, `Ostmann_QuadraticCenter_PrimeQuadraticUniqueness`, `Ostmann_QuadraticCenter_PrimeSetQuadratic`, `Ostmann_QuadraticCenter_RationalApproximationLift`, `Ostmann_QuadraticCenter_RealQuadraticPhase`, `Ostmann_QuadraticCenter_RootNormalizedCoefficient`, `Ostmann_QuadraticCenter_SignedQuadraticFrequency`, `Ostmann_QuadraticCenter_SquareKernelIndex`, `Ostmann_QuadraticCenter_SquarefreeFrequencyRectangle`, `Ostmann_QuadraticCenter_TruncatedQuadraticCorrelation`, `Ostmann_QuadraticSieve_JacobiCharacter`, `Ostmann_QuadraticSieve_JacobiComplex`, `Ostmann_QuadraticSieve_JacobiPrimeSeries`, `Ostmann_QuadraticSieve_SignedQuadraticSieve`, `Ostmann_QuadraticSieve_SignedSquarefreeRange`, `Ostmann_QuadraticSieve_WeightedJacobiMoment`, `Ostmann_Quadratic_CommonCenter`, `Ostmann_Quadratic_CommonCenterAssembly`, `Ostmann_Quadratic_CommonCenterCharacter`, `Ostmann_Quadratic_CommonCenterConcreteMoments`, `Ostmann_Quadratic_CommonCenterCongruences`, `Ostmann_Quadratic_CommonCenterFromTuples`, `Ostmann_Quadratic_CommonCenterLiftBounds`, `Ostmann_Quadratic_CommonCenterTupleCounts`, `Ostmann_Quadratic_KernelPrimeCutoffs`, `Ostmann_Quadratic_QuadraticAmplificationBias`, `Ostmann_Quadratic_QuadraticAmplificationCoefficients`, `Ostmann_Quadratic_QuadraticArrayApproximation`, `Ostmann_Quadratic_QuadraticBalancedExponent`, `Ostmann_Quadratic_QuadraticBalancedKernel`, `Ostmann_Quadratic_QuadraticCompactCutoff`, `Ostmann_Quadratic_QuadraticCoprimeMain`, `Ostmann_Quadratic_QuadraticCorrectionCutoffGeometry`, `Ostmann_Quadratic_QuadraticCorrectionMoment`, `Ostmann_Quadratic_QuadraticCorrectionPolynomial`, `Ostmann_Quadratic_QuadraticDampedFresnel`, `Ostmann_Quadratic_QuadraticDensitySum`, `Ostmann_Quadratic_QuadraticDescentCutoff`, `Ostmann_Quadratic_QuadraticDivisorDyadicPartition`, `Ostmann_Quadratic_QuadraticEulerAtTwo`, `Ostmann_Quadratic_QuadraticEulerCancellation`, `Ostmann_Quadratic_QuadraticEulerCover`, `Ostmann_Quadratic_QuadraticFiniteDescent`, `Ostmann_Quadratic_QuadraticFirstSecondMain`, `Ostmann_Quadratic_QuadraticFourierSeparation`, `Ostmann_Quadratic_QuadraticFrequencyTerm`, `Ostmann_Quadratic_QuadraticFrequencyTwist`, `Ostmann_Quadratic_QuadraticFresnelCoefficient`, `Ostmann_Quadratic_QuadraticFresnelMain`, `Ostmann_Quadratic_QuadraticFresnelSigns`, `Ostmann_Quadratic_QuadraticGaussBilinear`, `Ostmann_Quadratic_QuadraticGaussMultiplier`, `Ostmann_Quadratic_QuadraticGcdRangeBridge`, `Ostmann_Quadratic_QuadraticGridApproximation`, `Ostmann_Quadratic_QuadraticGrowthBandBalance`, `Ostmann_Quadratic_QuadraticGrowthDivisorBudget`, `Ostmann_Quadratic_QuadraticHalfReflection`, `Ostmann_Quadratic_QuadraticHybridPoisson`, `Ostmann_Quadratic_QuadraticKernelCollision`, `Ostmann_Quadratic_QuadraticLogDecay`, `Ostmann_Quadratic_QuadraticLogDerivative`, `Ostmann_Quadratic_QuadraticLogFourierEnvelope`, `Ostmann_Quadratic_QuadraticLogKernel`, `Ostmann_Quadratic_QuadraticLogRootKernel`, `Ostmann_Quadratic_QuadraticMultiples`, `Ostmann_Quadratic_QuadraticPairKernel`, `Ostmann_Quadratic_QuadraticParameterGrid`, `Ostmann_Quadratic_QuadraticPrimeTwist`, `Ostmann_Quadratic_QuadraticReciprocityCharacter`, `Ostmann_Quadratic_QuadraticResidueDecomposition`, `Ostmann_Quadratic_QuadraticResidueTests`, `Ostmann_Quadratic_QuadraticRootCharacter`, `Ostmann_Quadratic_QuadraticSecondCutoffs`, `Ostmann_Quadratic_QuadraticSecondDyadic`, `Ostmann_Quadratic_QuadraticSecondError`, `Ostmann_Quadratic_QuadraticSecondPoisson`, `Ostmann_Quadratic_QuadraticSecondScale`, `Ostmann_Quadratic_QuadraticSecondSignedCore`, `Ostmann_Quadratic_QuadraticSieveDivisibility`, `Ostmann_Quadratic_QuadraticSieveProof`, `Ostmann_Quadratic_QuadraticSieveTranspose`, `Ostmann_Quadratic_QuadraticSmallEnvelope`, `Ostmann_Quadratic_QuadraticSmallGcdSum`, `Ostmann_Quadratic_QuadraticSmallKernelPoisson`, `Ostmann_Quadratic_QuadraticSmallKernelScale`, `Ostmann_Quadratic_QuadraticSmallKernelWindow`, `Ostmann_Quadratic_QuadraticSqrtCoefficients`, `Ostmann_Quadratic_QuadraticSquareCompose`, `Ostmann_Quadratic_QuadraticTotientKernel`, `Ostmann_Quadratic_QuadraticTransformedMain`, `Ostmann_Quadratic_QuadraticTruncatedPoisson`, `Ostmann_Quadratic_RootPopulationBudget`, `Ostmann_Quadratic_RootPopulations`, `Ostmann_Supply_AveragedKernelPairing`, `Ostmann_Supply_CenteredCoordinateSupport`, `Ostmann_Supply_CenteredResidueProjection`, `Ostmann_Supply_CenteredSupportProjection`, `Ostmann_Supply_ConcreteExtensionWeights`, `Ostmann_Supply_ElementaryPolynomial`, `Ostmann_Supply_FavorableMassAlternative`, `Ostmann_Supply_FiniteCoordinateEnergy`, `Ostmann_Supply_FiniteTensorKernel`, `Ostmann_Supply_GoodSieveMultipliers`, `Ostmann_Supply_MultiplierRatioProduct`, `Ostmann_Supply_MultiplierWeightedBudget`, `Ostmann_Supply_NaturalPrimeSupportSieve`, `Ostmann_Supply_NaturalResidueAverage`, `Ostmann_Supply_PrimeSubsetProducts`, `Ostmann_Supply_ResidueProjectionScalar`, `Ostmann_Supply_ResidueVectorNorm`, `Ostmann_Supply_SquarefreeMultiplierCount`, `Ostmann_Supply_SubsetReducedEnergy`, `Ostmann_Supply_TernaryProductPolynomial`, `Ostmann_Supply_TruncatedBilinearCube`, `Ostmann_Tree_ArrangementReindex`, `Ostmann_Tree_BadPartitionCounts`, `Ostmann_Tree_CellGroupPigeonhole`, `Ostmann_Tree_CellListPigeonhole`, `Ostmann_Tree_ComponentFibers`, `Ostmann_Tree_CrossPairMajorant`, `Ostmann_Tree_CrossQuartetFiber`, `Ostmann_Tree_FiberProjection`, `Ostmann_Tree_FiniteActionAverage`, `Ostmann_Tree_FriendlyQuartet`, `Ostmann_Tree_IncidenceCirculation`, `Ostmann_Tree_IncidenceCycle`, `Ostmann_Tree_PairCoefficientMeans`, `Ostmann_Tree_PairFourierMass`, `Ostmann_Tree_PairPopulationFibers`, `Ostmann_Tree_PairSquareMoment`, `Ostmann_Tree_PairedRationalReduction`, `Ostmann_Tree_ParallelCycle`, `Ostmann_Tree_PartitionMatching`, `Ostmann_Tree_PartitionProducts`, `Ostmann_Tree_QuartetPairMajorant`, `Ostmann_Tree_ReciprocalCoordinates`, `Ostmann_Tree_ReciprocalPair`, `Ostmann_Tree_SamePairFiber`, `Ostmann_Tree_SampleEqualityPatterns`, `Ostmann_Tree_TruncatedModePairing`, `Ostmann_ZeroDensity_BulkProgressionCutoff`, `Ostmann_ZeroDensity_CompletedCompensationPrior`, `Ostmann_ZeroDensity_ComplexPrimeWeights`, `Ostmann_ZeroDensity_ConductorDeletion`, `Ostmann_ZeroDensity_DensityAbscissaPolynomial`, `Ostmann_ZeroDensity_DensityBalanceParameters`, `Ostmann_ZeroDensity_DensityBlockWeights`, `Ostmann_ZeroDensity_DensityCRTProduct`, `Ostmann_ZeroDensity_DensityDetectorCoefficients`, `Ostmann_ZeroDensity_DensityDetectorPolynomial`, `Ostmann_ZeroDensity_DensityDetectorWeight`, `Ostmann_ZeroDensity_DensityDyadicShells`, `Ostmann_ZeroDensity_DensityFiniteContourShift`, `Ostmann_ZeroDensity_DensityGaussianCauchy`, `Ostmann_ZeroDensity_DensityGaussianEnvelope`, `Ostmann_ZeroDensity_DensityGaussianFubini`, `Ostmann_ZeroDensity_DensityHeightWeight`, `Ostmann_ZeroDensity_DensityKernelCost`, `Ostmann_ZeroDensity_DensityKernelPacking`, `Ostmann_ZeroDensity_DensityLocalizedPolynomial`, `Ostmann_ZeroDensity_DensityMollifierProduct`, `Ostmann_ZeroDensity_DensityPackedMoment`, `Ostmann_ZeroDensity_DensityPolynomialDerivative`, `Ostmann_ZeroDensity_DensityVerticalPolynomial`, `Ostmann_ZeroDensity_DensityWeightedMoment`, `Ostmann_ZeroDensity_DigammaTailEstimate`, `Ostmann_ZeroDensity_DirichletGraphFactor`, `Ostmann_ZeroDensity_FinitePriorDensity`, `Ostmann_ZeroDensity_GammaContourBounds`, `Ostmann_ZeroDensity_GammaGrowthStrip`, `Ostmann_ZeroDensity_GammaInverseBound`, `Ostmann_ZeroDensity_IntegerProgressionPartition`, `Ostmann_ZeroDensity_IntegratedThetaMain`, `Ostmann_ZeroDensity_IntervalDensityTree`, `Ostmann_ZeroDensity_PageFactors`, `Ostmann_ZeroDensity_PrimeLogDensity`, `Ostmann_ZeroDensity_PrimeLogDensityBounds`, `Ostmann_ZeroDensity_PrimeLogDerivative`, `Ostmann_ZeroDensity_PrimePartialSummation`, `Ostmann_ZeroDensity_PrimePowerRemainder`, `Ostmann_ZeroDensity_PrincipalFourthMoment`, `Ostmann_ZeroDensity_PrincipalRieszDecay`, `Ostmann_ZeroDensity_PrincipalRieszNearby`, `Ostmann_ZeroDensity_ProgressionCharacterCancellation`, `Ostmann_ZeroDensity_RationalNodeDensity`, `Ostmann_ZeroDensity_RealPrimeSeries`, `Ostmann_ZeroDensity_RestrictedGiantDensity`, `Ostmann_ZeroDensity_RieszSmoothRecovery`, `Ostmann_ZeroDensity_RieszUnsmoothing`, `Ostmann_ZeroDensity_SchwartzDensityCorrelation`, `Ostmann_ZeroDensity_SmoothLeftContourBound`, `Ostmann_ZeroDensity_SmoothLeftContourWeight`, `Ostmann_ZeroDensity_SmoothPrimePowerRemoval`, `Ostmann_ZeroDensity_SmoothVerticalKernel`, `Ostmann_ZeroDensity_TreeDensity`, `Ostmann_ZeroDensity_UnsignedPrimeMass`, `Ostmann_ZeroDensity_UnsignedPrimeTail`, `Ostmann_ZeroDensity_ZeroVariableHistory`, `Ostmann_ZeroDensity_ZetaLocalFactorBound`.
--
--   **Imports.** It imports the published bundle `Def_OstmannComplete`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D004` and `OAIQ095D005`; the statements `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction`, `OAI.Ostmann.common_center_biased_populations_impossible`, `OAI.Ostmann.density_packed_product_fourth`, `OAI.Ostmann.eventual_original_tail_commonCenter`, `OAI_Ostmann_quadratic_rough_iteration` and `OAI.Ostmann.quadratic_rough_power_growth`; the proof of `OAI.Ostmann.inverseGoldbach_of_published`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OstmannComplete

section
-- module Solutions.OAIQ095_OS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
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
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact line counts in the ideal giant residues -/

namespace Ostmann

open scoped BigOperators

/-- A feasible line on two unit coordinates has one point for each second coordinate. -/
def unitLineEquiv {G : Type*} [CommGroup G] (a b : G) :
    {xy : G × G // a * xy.1 = b * xy.2} ≃ G where
  toFun xy := xy.1.2
  invFun y := ⟨(a⁻¹ * b * y, y), by simp [mul_assoc]⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · change a⁻¹ * b * xy.1.2 = xy.1.1
      rw [mul_assoc, ← xy.property]
      simp
    · rfl
  right_inv _ := rfl

/-- An external integer coordinate is unrestricted; the second coordinate is still a unit. -/
noncomputable def externalLineEquiv {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} ≃ (ZMod p)ˣ where
  toFun xy := xy.1.2
  invFun y := ⟨(b / (a : ZMod p) * y, y), by field_simp⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · change b / (a : ZMod p) * xy.1.2 = xy.1.1
      apply (mul_left_cancel₀ (Units.ne_zero a))
      calc
        (a : ZMod p) * (b / (a : ZMod p) * xy.1.2) = b * xy.1.2 := by field_simp
        _ = _ := xy.property.symm
    · rfl
  right_inv _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTResidueAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent residue averages from the Chinese remainder theorem -/

namespace Ostmann

open scoped BigOperators

/-- CRT on the actual unit residue classes, including prime-square moduli. -/
noncomputable def crtUnitEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    (ZMod (∏ i, a i))ˣ ≃* (∀ i, (ZMod (a i))ˣ) :=
  (Units.mapEquiv (ZMod.prodEquivPi a hc).toMulEquiv).trans MulEquiv.piUnits

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTLineAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint CRT factorization in the two giant environments -/

namespace Ostmann

open scoped BigOperators

noncomputable def crtExternalPairEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    (ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) ≃
      (∀ i, ZMod (a i) × (ZMod (a i))ˣ) :=
  ((ZMod.prodEquivPi a hc).toEquiv.prodCongr (crtUnitEquiv a hc).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow I (fun i => ZMod (a i))
      (fun i => (ZMod (a i))ˣ)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance instDecidableEqMulCharZModComplex_solutions {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonidentity affine-map fibers

The finite-field representation count used immediately before equation
`tree-affine-coefficient-norm`: every nonidentity affine map arising from
`U_r^* U_s` has at most two representations.
-/

namespace Ostmann

/-- Slope and translation of the affine map underlying `U_r^* U_s`.
The translation is written in ratio coordinates. -/
def affineParameters {p : ℕ} (r s : (ZMod p)ˣ) : (ZMod p)ˣ × ZMod p :=
  ((s / r) ^ 2, (r : ZMod p) *
    (((s / r : (ZMod p)ˣ) : ZMod p) - ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The affine coefficient array

The identity fiber is diagonal, and all other fibers have size at most two.
These facts give the coefficient-square estimate in equation
`tree-affine-coefficient-norm` without a pointwise bound on the function.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The unnormalized coefficients obtained by collecting ordered unit pairs. -/
noncomputable def affineCoefficientSum {p : ℕ} [Fact p.Prime] (G : (ZMod p)ˣ → ℂ)
    (ab : (ZMod p)ˣ × ZMod p) : ℂ :=
  ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab), conj (G rs.1) * G rs.2

/-- The coefficient normalization for the operator `T* T`. -/
noncomputable def affineCoefficient {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (ab : (ZMod p)ˣ × ZMod p) : ℂ :=
  affineCoefficientSum G ab / (((p : ℝ) ^ 2 : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The affine action in the Fourier basis

On nonzero additive frequencies the affine action is a matrix whose entries
are additive character sums. Parseval bounds its squared matrix norm by
`p` times the coefficient energy. This is the finite matrix estimate in
the proof of the uniform Mellin bound in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def additiveCharacterSum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ξ : ZMod p) : ℂ :=
  ∑ b : ZMod p, f b * ZMod.stdAddChar (ξ * b)

/-- The input frequency is `ξ` and the output frequency is `η`. -/
noncomputable def affineFourierMatrix {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (η ξ : (ZMod p)ˣ) : ℂ :=
  additiveCharacterSum (fun b => c (η / ξ, b)) ξ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Autocorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive autocorrelation

The probability-normalized Fourier transform of an autocorrelation is
the squared modulus of the original transform. This is the positivity
identity used for the bottom-pair coefficients in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def additiveConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ y : ZMod p, f y * g (x - y)

noncomputable def additiveAutocorrelation {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (d : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ x : ZMod p, f x * conj (f (x - d))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def affineAction {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  ∑ a : (ZMod p)ˣ, ∑ b : ZMod p, c (a, b) * f ((a : ZMod p) * t + b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

noncomputable def productPrior {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (x : Fin n → A) : ℝ := ∏ i, μ i (x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the exceptional-character density in the arithmetic measures

The correction is retained, including when it correlates with the amplitude.
Once its conductor is supported on the frequency modulus, CRT places it in
that coordinate and the other residue averages factor exactly.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def pageMultiplier {A : Type*} (χ : A → ℝ) (β t : ℝ) (a : A) : ℝ :=
  1 - χ a * Real.exp ((β - 1) * t)

theorem pageMultiplier_bounds {A : Type*} (χ : A → ℝ) (β t : ℝ)
    (hχ : ∀ a, |χ a| ≤ 1) (hβ : β ≤ 1) (ht : 0 ≤ t) (a : A) :
    0 ≤ pageMultiplier χ β t a ∧ pageMultiplier χ β t a ≤ 2 := by
  have he0 := (Real.exp_pos ((β - 1) * t)).le
  have he1 : Real.exp ((β - 1) * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
  have hχa := abs_le.mp (hχ a)
  have hprod := mul_le_mul_of_nonneg_right hχa.2 he0
  have hprod' := mul_le_mul_of_nonneg_right hχa.1 he0
  dsimp [pageMultiplier]
  constructor <;> nlinarith

/-- The retained frequency block and all other unit residues in the actual
modulus. -/
noncomputable def crtSplitUnitEquiv (q r : ℕ) (h : q.Coprime r) :
    (ZMod (q * r))ˣ ≃ (ZMod q)ˣ × (ZMod r)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularDiagonalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the diagonal regular-prime unit loss

The external integer giant is restricted to units. At a regular prime
carrying a squared transform, its energy cancels that restriction exactly.
At an outer compensation prime the factor left over is `1 - 1/p`.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def externalRegularLocal {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (z : ZMod p × (ZMod p)ˣ) : ℝ :=
  if z.1 = 0 then 0 else
    if active then ‖g ((a : ZMod p) * (z.1 * (z.2 : ZMod p))⁻¹)‖ ^ 2 else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticCRTSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the regular-prime block from the signed arithmetic average -/

namespace Ostmann

open scoped BigOperators

/-- Simultaneously split the integer and unit giant residues. -/
noncomputable def crtSplitExternalEquiv (c r : ℕ) (hc : c.Coprime r) :
    (ZMod (c * r) × (ZMod (c * r))ˣ) ≃
      (ZMod c × (ZMod c)ˣ) × (ZMod r × (ZMod r)ˣ) :=
  ((ZMod.chineseRemainder hc).toEquiv.prodCongr (crtSplitUnitEquiv c r hc)).trans
    (Equiv.prodProdProdComm _ _ _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LcmFrequencySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal-lcm sum in the frequency budget

The gcd coordinates embed each frequency pair into three independent
positive harmonic sums. No asymptotic divisor estimate is used here.
-/

namespace Ostmann

open scoped BigOperators

def gcdFrequencyCoordinates (x : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1.gcd x.2, x.1 / x.1.gcd x.2, x.2 / x.1.gcd x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticFrequencyTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full arithmetic frequency-tree budget -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def pairedFrequencyLeaf (S : Finset ℤ) (V : ℕ) (x : S × S) : ℝ :=
  if (x.1 : ℤ).natAbs ≤ V ∧ (x.2 : ℤ).natAbs ≤ V then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square congruences in the frequency support -/

namespace Ostmann

open scoped BigOperators Classical

def squareFiberEquivOne {G : Type*} [CommGroup G] (r : G) :
    {x : G // x ^ 2 = r ^ 2} ≃ {x : G // x ^ 2 = 1} where
  toFun x := ⟨x / r, by rw [div_pow, x.property, div_self']⟩
  invFun x := ⟨x * r, by rw [mul_pow, x.property, one_mul]⟩
  left_inv x := by ext; exact div_mul_cancel x.val r
  right_inv x := by ext; exact mul_div_cancel_right x.val r

noncomputable def crtSquareFiberEquiv {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (a : (ZMod (∏ i, q i))ˣ) :
    {x : (ZMod (∏ i, q i))ˣ // x ^ 2 = a} ≃
      ∀ i, {x : (ZMod (q i))ˣ // x ^ 2 = crtUnitEquiv q hc a i} :=
  ((crtUnitEquiv q hc).toEquiv.subtypeEquiv (by
    intro x
    constructor
    · intro hx i
      simpa only [map_pow, Pi.pow_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using
        congrArg (fun y => crtUnitEquiv q hc y i) hx
    · intro hx
      apply (crtUnitEquiv q hc).injective
      funext i
      simpa only [map_pow, Pi.pow_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
        using hx i)).trans Equiv.subtypePiEquivPi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquareKernelIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-root counts from a cyclic subgroup of small index -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def cosetSquareInjection {G : Type*} [CommGroup G]
    (H : Subgroup G) (r : G) (hr : r ^ 2 = 1) :
    {x : G // x ^ 2 = 1 ∧ (x : G ⧸ H) = (r : G ⧸ H)} →
      {x : H // x ^ 2 = 1} := fun x =>
  ⟨⟨x / r, (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' H (x / r) = 1
    have hq : QuotientGroup.mk' H x.val = QuotientGroup.mk' H r := x.property.2
    rw [map_div, hq, div_self'])⟩, by
      apply Subtype.ext
      change (x.val / r) ^ 2 = 1
      rw [div_pow, x.property.1, hr, div_self']⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitSquareSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the actual split relation to its reduced square equation -/

namespace Ostmann

open scoped BigOperators Classical

theorem reduced_split_coefficients_coprime {s v w : ℕ} (hs : s ≠ 0)
    (hgcd : v.gcd s = w.gcd s) :
    (v / v.gcd s).Coprime (s / v.gcd s) ∧
      (w / v.gcd s).Coprime (s / v.gcd s) := by
  have hv := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right v (Nat.pos_of_ne_zero hs))
  have hw := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right w (Nat.pos_of_ne_zero hs))
  exact ⟨hv, hgcd ▸ hw⟩

noncomputable def splitSquareTarget {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (A B P : (ZMod s)ˣ) :
    (ZMod (s / v.gcd s))ˣ :=
  let f := ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s))
  let h := reduced_split_coefficients_coprime (NeZero.ne s) hgcd
  (ZMod.unitOfCoprime (v / v.gcd s) h.1 * f A) * f P /
    (ZMod.unitOfCoprime (w / v.gcd s) h.2 * f B)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SignedSplitSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed frequencies in the actual split-support equations -/

namespace Ostmann

open scoped BigOperators Classical

def frequencySignUnit (q : ℕ) (v : ℤ) : (ZMod q)ˣ := if 0 ≤ v then 1 else -1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency budget for one squared history

Unlike a pair of histories, this sum has exactly one frequency at each leaf.
This is needed before the level-zero square-weight cancellation.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def singleFrequencyLeaf (S : Finset ℤ) (V : ℕ) (x : S) : ℝ :=
  if (x : ℤ).natAbs ≤ V then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational coordinates at a tree split

These identities are equations `tree-difference-ratio`, `tree-held-square`,
and `tree-p-square` of the manuscript. Nonzero hypotheses state precisely
that the reconstructed node is valid.
-/

namespace Ostmann

def parentArgument {K : Type*} [Field K] (s D HL HR : K) : K := s / (D * HL * HR)

def childArgument {K : Type*} [Field K] (s D u H P : K) : K := s / (D * P * u * H)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_Mellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin coefficients of a square pullback

Character orthogonality identifies the coefficient after substituting
`K * z^2`. The factor-two estimate then follows from `SquarePullback`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance instDecidableEqMulCharZModComplex_solutions_1 {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

/-- Probability-normalized Mellin coefficient on the nonzero field elements. -/
noncomputable def mellinCoefficient {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (ρ : MulChar (ZMod p) ℂ) : ℂ :=
  (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z, f z * conj (ρ z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MellinParseval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin inversion and Parseval on the nonzero residues

The coefficients use the probability normalization from `Mellin.lean`.
The only character-theoretic input is the finite duality already in Mathlib.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BottomPairMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The bottom-pair Mellin coefficient is an autocorrelation

This is equation `tree-P-definition`. The difference parameter is a unit;
the exceptional ratio `t = 1` is assigned value zero. The function being
correlated is twisted by the conjugate multiplicative character.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The fractional-linear involution exchanges the two exceptional points
with themselves, making it a permutation of the entire finite field. -/
noncomputable def ratioInvolution {p : ℕ} [Fact p.Prime] (t : ZMod p) : ZMod p :=
  if t = 1 then 1 else t / (t - 1)

/-- Bottom-pair value with difference `d` and ratio `t`, zero at the singular ratio. -/
noncomputable def bottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : (ZMod p)ˣ) : ℂ :=
  if t = 1 then 0 else
    g ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
      conj (g ((d : ZMod p) / ((t : ZMod p) - 1)))

/-- The multiplicative twist appearing in the autocorrelation formula. -/
noncomputable def characterTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ℂ :=
  g x * conj (χ x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RationalNodeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The density bound for an actual reconstructed node

The fixed parent product makes its argument independent of the split.
The reconstructed entry vanishes exactly when the child ratio is one.
Thus the inverse-square density estimate applies to the actual formulas,
with the manuscript's invalid-node convention.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalNodeArgument {p : ℕ} [Fact p.Prime]
    (s D XL XR CL CR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  s / (D * XL * CL * XR * CR * P)

noncomputable def rationalNodeRatioConstant {p : ℕ} [Fact p.Prime]
    (sL sR XL XR CL CR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (sL / sR) * (XR * CR * P / (XL * CL))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_DifferenceMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Means of nonnegative difference convolutions

Removing the zero difference can only decrease the sum. This supplies
the mean bounds for the nonnegative quartet majorants in Section 6.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def differenceMoment {p : ℕ} [NeZero p]
    (f g : ZMod p → ℝ) (y : ZMod p) : ℝ := ∑ x : ZMod p, f x * g (x - y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TreeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterating the elementary tree density estimate

A split plan allows the remaining unit parameters to depend on every
previous split coordinate. The bound is uniform over those choices.
The separate rational-coordinate lemmas identify the manuscript's tree
with this inverse-square split law on valid ancestor data.
-/

namespace Ostmann

open scoped BigOperators

/-- Parameter-free density majorant, including the zero convention. -/
noncomputable def treeDensityMajorant {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) :
    ℕ → ZMod p → ℝ
  | 0, d => if d = 0 then 0 else w d
  | n + 1, d => if d = 0 then 0 else
      (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
        differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interval distribution for the external integer giant -/

namespace Ostmann

open scoped Classical
open MeasureTheory

noncomputable def integerLogDensity (q : ℕ) (G y : ℝ) : ℝ :=
  Real.exp (y - G) / q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pushforward to log-cell and residue coordinates

The finite partition of each actual prime sample induces independent cell
priors. This is an equality, before any progression approximation is used.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def cellPrior {A B : Type*} [Fintype A]
    (μ : A → ℝ) (cell : A → B) (b : B) : ℝ :=
  ∑ a, if cell a = b then μ a else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodCellTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifted cell indices and target sums -/

namespace Ostmann

/-- The nonnegative differences of a set of cell indices from its first index. -/
def cellDifferences (I : Finset ℕ) (a : ℕ) : Finset ℕ :=
  I.image (fun x => x - a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OppositeBiasTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Opposite empirical biases from complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def residueTestMean {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / S.card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodCellSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting many heavy cells with positive mean -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def positiveHeavyCells (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ : ℝ) : Finset ℕ :=
  I.filter (fun h => δ / 2 ≤ score h ∧ θ ≤ w h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive word means and a common product bin -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def binnedWordAverage {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B) : ℂ :=
  ∑ x, if bin x = b then (productPrior μ x : ℂ) * ∏ i, F i (x i) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePartialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation for the reciprocal-prime progression measure

This is the bridge from the published theta estimate (Montgomery--Vaughan,
Corollary 11.20, equations (11.32) and (11.34)) to the interval weights used
in Section 8. The conversion itself is proved here.
-/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

noncomputable def reciprocalPrimeInterval (q a : ℕ) (u v : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
    if n.Prime ∧ Nat.ModEq q n a then (n : ℝ)⁻¹ else 0

noncomputable def primeHarmonicWeight (x : ℝ) : ℝ := (x * Real.log x)⁻¹

noncomputable def primeHarmonicDerivative (x : ℝ) : ℝ :=
  -(Real.log x + 1) / (x * Real.log x) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page density in logarithmic coordinates -/

namespace Ostmann

open MeasureTheory

noncomputable def primeLogDensity (φ χ β t : ℝ) : ℝ :=
  (1 - χ * Real.exp ((β - 1) * t)) / (φ * t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds on the retained density and on discarded real zeros -/

namespace Ostmann

open MeasureTheory

theorem continuousOn_primeLogDensity (φ χ β : ℝ) {s t : ℝ} (hs : 0 < s) :
    ContinuousOn (primeLogDensity φ χ β) (Set.Icc s t) := by
  intro y hy
  have hy0 : y ≠ 0 := ne_of_gt (hs.trans_le hy.1)
  have hn : ContinuousAt (fun y : ℝ =>
      (1 - χ * Real.exp ((β - 1) * y)) / y) y :=
    (continuousAt_const.sub ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).const_mul χ)).div continuousAt_id hy0
  apply ((hn.div_const φ).congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [] with x
  dsimp [primeLogDensity]
  ring

theorem primeLogDensity_bounds (φ χ β : ℝ) (hφ : 0 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ primeLogDensity φ χ β t ∧ primeLogDensity φ χ β t ≤ 2 / (φ * t) := by
  have h := pageMultiplier_bounds (fun _ : Unit => χ) β t (fun _ => hχ) hβ ht ()
  dsimp [pageMultiplier] at h
  exact ⟨div_nonneg h.1 (mul_nonneg hφ ht),
    div_le_div_of_nonneg_right h.2 (mul_nonneg hφ ht)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

noncomputable def gridLower {N q : ℕ} (s h : ℝ) (c : Fin N × (ZMod q)ˣ) : ℝ :=
  s + (c.1 : ℝ) * h

noncomputable def gridUpper {N q : ℕ} (s h : ℝ) (c : Fin N × (ZMod q)ˣ) : ℝ :=
  s + ((c.1 : ℝ) + 1) * h

noncomputable def gridResidue {N q : ℕ} (c : Fin N × (ZMod q)ˣ) : ℕ :=
  (c.2 : ZMod q).val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySmoothFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth factors in the expanded arithmetic histories

Compensation-prime powers and spectator transforms are excluded here,
as in the definition of Xi in Section 8 of the manuscript.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def archimedeanLeafFactor (X M s cutoff : ℝ) (ψhat : ℝ → ℂ) : ℂ :=
  (Real.sqrt (X / M) * cutoff : ℝ) * ψhat (-s * X / M)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctTupleProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping distinct ordered products by their underlying subsets -/

namespace Ostmann

open scoped BigOperators Classical

def tupleImage {A : Type*} [DecidableEq A] {k : ℕ} (e : Fin k ↪ A) : Finset A :=
  Finset.univ.image e

noncomputable def tupleImageFiberEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (Q : Finset A) :
    {e : Fin k ↪ A // tupleImage e = Q} ≃ (Fin k ≃ Q) where
  toFun z := Equiv.ofBijective (fun i => ⟨z.1 i, by
    exact Eq.mp (congrArg (fun S : Finset A => z.1 i ∈ S) z.2)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)
    ⟨fun i j h => z.1.injective (congrArg Subtype.val h), by
      intro a
      have ha : a.val ∈ tupleImage z.1 := by rw [z.2]; exact a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans (Function.Embedding.subtype _), by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact (e i).property
    · intro ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩⟩
  left_inv z := by apply Subtype.ext; ext i; rfl
  right_inv e := by ext i; rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the transfer diagonal before expanding the square -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedCoefficient {A K : Type*} [Fintype A]
    (key : A → K) (z : A → ℂ) (k : K) : ℂ :=
  ∑ a, if key a = k then z a else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def pivotResidueKey (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ) : Fin M :=
  (ZMod.finEquiv M).symm ((v : ZMod M) * (L : ZMod M)⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact diagonal and signed-frequency decomposition of a transfer -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def pivotDiagonal {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) : ℂ :=
  ∑ a, ∑ b, if v a * L b - v b * L a = 0 then c a * conj (c b) else 0

noncomputable def pivotOffDiagonal {A : Type*} [Fintype A]
    (M : ℕ) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) : ℂ :=
  ∑ a, ∑ b, if v a * L b - v b * L a ≠ 0 ∧ (M : ℤ) ∣ v a * L b - v b * L a
    then c a * conj (c b) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitPrefixProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every current parent product from previously exposed splits -/

namespace Ostmann

/-- Pending subtrees are visited in preorder. Depth-zero branches require
no split coordinate, so they are never stored in the frontier. -/
def pendingSplitBranch {G : Type*} (n : ℕ) (P : G) (rest : List (ℕ × G)) : List (ℕ × G) :=
  match n with
  | 0 => rest
  | n + 1 => (n + 1, P) :: rest

def splitFrontierStep {G : Type*} [Div G] (frontier : List (ℕ × G)) (x : G) : List (ℕ × G) :=
  match frontier with
  | [] => []
  | (0, _) :: rest => rest
  | (n + 1, P) :: rest => pendingSplitBranch n x (pendingSplitBranch n (P / x) rest)

def currentSplitParent {G : Type*} [One G] (frontier : List (ℕ × G)) : G :=
  match frontier with
  | [] => 1
  | (_, P) :: _ => P

def splitPrefixParent {G : Type*} [Div G] [One G] (n : ℕ) (P : G) (past : List G) : G :=
  currentSplitParent (past.foldr (fun x frontier => splitFrontierStep frontier x)
    (pendingSplitBranch n P []))

def splitFrontierTrace {G : Type*} [Div G] [One G] (frontier : List (ℕ × G)) : List G → List (G × G)
  | [] => []
  | x :: xs => (currentSplitParent frontier, x) ::
      splitFrontierTrace (splitFrontierStep frontier x) xs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A weighted fourth moment of multiplicative character sums

The full character sum selects equality of two nonzero products. Together
with the split-quadratic collision count, this gives equation
`tree-fourth-moment` of the manuscript.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance characterFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def weightedCharacterSum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  ∑ b : ZMod p, (w b : ℂ) * χ (a - b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted character fourth-moment bound

Equation `tree-fourth-moment` follows from character orthogonality and
counting coincidences of two monic split quadratics.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance characterFourthBoundFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalFourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the principal character from the fourth moment

Its contribution cancels the leading fourth power of the total mass.
This leaves the second-moment term required by the two-bad quartet case.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance principalFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance principalFourthDecidableEq {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourth moments after a nonprincipal multiplicative twist

Gauss convolution transfers the weighted character fourth moment to
Fourier coefficients. The character inversion merely permutes the
nonprincipal characters.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance gaussFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance gaussFourthDecidableEq {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FourthMomentFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the nonprincipal fourth moment over bottom-pair characters

Only the common mass bound, the maximum squared mass, and the total
squared mass of the nonnegative Fourier weights enter this calculation.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance fourthFamilyFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance fourthFamilyDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TwistCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cauchy--Schwarz for the two-bad quartet twists

The two character changes are permutations. After excluding principal
twists, the two squared energies are exactly the fourth-moment sums.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance twistCauchyFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance twistCauchyDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MellinDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin Parseval on a multiplicative diagonal

This is the finite interchange of Mellin expansion and a weighted sum
used at the beginning of the proof of the uniform estimate `src42`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_1 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def mellinDiagonal {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (lam : (ZMod p)ˣ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, H d (lam * d) * v d

noncomputable def mellinDiagonalCoefficient {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (χ : MulChar (ZMod p) ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, mellinCoefficient (H d) χ * χ d * v d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted affine averaging operator

This is the operator in equation `tree-affine-coefficient`, together with
its adjoint. Its adjoint square is the affine action whose coefficient
energy is bounded in `AffineCoefficients`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def affineGenerator {p : ℕ} (r : (ZMod p)ˣ) (t : ZMod p) : ZMod p :=
  (r : ZMod p) - (r : ZMod p) ^ 2 * t

def affineGeneratorInv {p : ℕ} [Fact p.Prime] (r : (ZMod p)ˣ) (t : ZMod p) : ZMod p :=
  ((r : ZMod p) - t) / (r : ZMod p) ^ 2

noncomputable def affineGeneratorEquiv {p : ℕ} [Fact p.Prime]
    (r : (ZMod p)ˣ) : ZMod p ≃ ZMod p where
  toFun := affineGenerator r
  invFun := affineGeneratorInv r
  left_inv t := by
    dsimp [affineGenerator, affineGeneratorInv]
    field_simp
    ring
  right_inv t := by
    dsimp [affineGenerator, affineGeneratorInv]
    field_simp
    ring

/-- The paper uses this with weights `W r = conj (G r)`. -/
noncomputable def affineAverage {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, W r * F (affineGenerator r t)

noncomputable def affineAverageAdjoint {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, conj (W r) * F (affineGeneratorInv r t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Constant and mean-zero parts of the affine average

The self-correlation estimate here is the operator inequality used to
prove the uniform Mellin estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def unitMean {p : ℕ} [Fact p.Prime] (W : (ZMod p)ˣ → ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, W r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reciprocal twist used in the uniform Mellin estimate

Inversion preserves the finite-field squared norm. The mean of the
reciprocal twist is exactly an additive Fourier coefficient of the
original multiplicatively twisted test.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def reciprocalTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a x : ZMod p) : ℂ :=
  g x⁻¹ * η x⁻¹ * ZMod.stdAddChar (-(a * x⁻¹))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ReciprocalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal coordinates for the uniform Mellin estimate

The change of variables `r = lam - 1/d` is a permutation even with
the field's zero-inverse convention. Away from the singular bottom-pair
ratio, it turns reciprocal leaf arguments into a quadratic affine map.
-/

namespace Ostmann

variable {K : Type*} [Field K]

def reciprocalCoordinates (lam : K) : K ≃ K where
  toFun d := lam - d⁻¹
  invFun r := (lam - r)⁻¹
  left_inv d := by simp
  right_inv r := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ReciprocalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reciprocal pair identity

The character and additive phases in the reciprocal twist combine into
the diagonal bottom-pair weight. This is the pointwise calculation behind
the affine-operator parametrization of the uniform Mellin estimate.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def fieldBottomPair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) : ℂ :=
  g (d * t / (t - 1)) * conj (g (d / (t - 1)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_UniformMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The uniform Mellin estimate

The positive-difference form of equation `src42` follows by combining
Mellin Parseval on the diagonal with the reciprocal affine bound.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_2 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def pairAutocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℂ :=
  (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
    additiveAutocorrelation (characterTwist g χ) d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier estimates for quartet terms

The friendly term follows from the uniform Mellin estimate and Parseval
energy. A nonprincipal Gauss transform also has the uniform maximum used
when exactly one of the two quartet twists is principal.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetFourierFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetParseval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact Parseval reduction for quartet averages

Two independent unit parameters are separated by Mellin Parseval.
The remaining difference convolution is diagonalized by additive Parseval.
All normalizations are the probability normalizations of Section 6.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetParsevalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def additiveDifferenceConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (y : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p, f d * g (d - y)

noncomputable def quartetSynthesis {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (α β : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) : ℂ :=
  ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ,
    additiveDifferenceConvolution (fun d => f χ d * α χ ψ d)
      (fun e => g ψ e * β χ ψ e) y * χ z * ψ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact Mellin expansion of the two-bad quartet term

The pair function is zero at a zero difference or ratio. The extra
multiplicative character also kills zero differences, so the full-field
convolution and the valid-pair formula agree exactly.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetExpansionFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def fieldBottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) : ℂ :=
  if hd : d = 0 then 0 else if ht : t = 0 then 0 else
    bottomPairValue g (Units.mk0 d hd) (Units.mk0 t ht)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The four quartet orientation formulas

A friendly side uses its own difference, and a bad side uses the reciprocal
of the other difference. The twists below are exactly the four rows in
`tree-twisted-convolution`.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetOrientationsFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetLeftRatio {p : ℕ} [Fact p.Prime] (friendly : Bool) (z d e : ZMod p) : ZMod p :=
  if friendly then z * d else z / e

noncomputable def quartetRightRatio {p : ℕ} [Fact p.Prime] (friendly : Bool) (t d e : ZMod p) : ZMod p :=
  if friendly then t * e else t / d

noncomputable def quartetLeftTwist {p : ℕ} [Fact p.Prime] (left right : Bool)
    (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν * (if left then χ else 1) * (if right then 1 else ψ⁻¹)

noncomputable def quartetRightTwist {p : ℕ} [Fact p.Prime] (left right : Bool)
    (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν⁻¹ * (if left then 1 else χ⁻¹) * (if right then ψ else 1)

noncomputable def quartetParameterValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p,
    fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y)) *
        ν (d / (d - y))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FriendlyQuartet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The friendly quartet estimate

The exact held-parameter average is bounded by the uniform Mellin estimate
on one side and total Fourier energy on the other side.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance friendlyQuartetFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interchanging the two bottom pairs

Swapping the pairs inverts the quotient character and negates additive
frequency. This supplies the right-friendly estimate from the left one.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetSymmetryFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareCharacterMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the square-pullback majorants

Every character contributes to exactly one square fiber, and a single
fiber contains at most two characters. These are the two bounds needed
for the same-pair quartet majorant.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance squareMassFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance squareMassDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

noncomputable def squareCharacterMass {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ρ : MulChar (ZMod p) ℂ) : ℝ :=
  ∑ χ ∈ Finset.univ.filter (fun χ => χ ^ 2 = ρ), a χ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_QuartetPairMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean bounds for same-pair quartet majorants

The square-fiber factor costs two for one index and costs nothing when
summed over all indices. Difference convolution then multiplies masses.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance samePairFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def differenceMajorant {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * differenceMoment f g y

noncomputable def samePairMajorant {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  differenceMajorant (fun d => squareCharacterMass (fun χ => F χ d) ρ) R y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FieldPairMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second moment of the zero-extended bottom-pair value -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem fieldBottomPairValue_zero_difference {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (t : ZMod p) : fieldBottomPairValue g 0 t = 0 := by
  simp [fieldBottomPairValue]

@[simp] theorem fieldBottomPairValue_zero_ratio {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : fieldBottomPairValue g d 0 = 0 := by
  by_cases hd : d = 0 <;> simp [fieldBottomPairValue, hd]

noncomputable def fieldPairMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    ∑ t : (ZMod p)ˣ, ‖fieldBottomPairValue g d t‖ ^ 2

@[simp] theorem fieldPairMoment_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) : fieldPairMoment g 0 = 0 := by
  simp [fieldPairMoment]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RatioParseval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parseval in the ratio of two nonzero arguments with fixed difference -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance ratioParsevalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def ratioTest {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (t : (ZMod p)ˣ) : ℂ :=
  if t = 1 then 0 else F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))

noncomputable def ratioDifferenceTransform {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (ν : MulChar (ZMod p) ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p, F d * ν (d / (d - y))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTotalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total character mass of the cross-pair quartet coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetTotalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetParameterMoment {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossPairMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-pullback majorants for the two moving leaves in different pairs -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance crossPairFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def crossPairMajorant {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  squareCharacterMass (fun ν => quartetParameterMoment g h left right ν y) ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareRatioCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-coordinate coefficients of a fixed-difference quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance squareRatioFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetRatioValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (z t r : (ZMod p)ˣ) : ℂ :=
  ratioTest (fun d =>
    fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))) y r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFriendlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-friendly orientation of an actual rational quartet -/

namespace Ostmann

open scoped BigOperators

/-- Reciprocal coordinates on the two moving leaves preserve the quartet product. -/
theorem quartet_friendly_product {G : Type*} [CommGroup G] (P a b r : G) :
    (r⁻¹ * a) * (P * r / (a * b) * b) = P := by
  calc
    _ = P * (r⁻¹ * r) * (a * a⁻¹) * (b⁻¹ * b) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = P := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOrientedValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All free/held orientations in the local quartet value -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def orientedPairBase {p : ℕ} (g : ZMod p → ℂ) (friendly : Bool) : ZMod p → ℂ :=
  if friendly then g else fun x => conj (g (-x))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-coordinate estimates for one moving bottom pair -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance pairSquareFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def fieldPairCoefficientMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℝ :=
  ‖mellinCoefficient (fun t => fieldBottomPairValue g d t) χ‖ ^ 2

@[simp] theorem fieldPairCoefficientMoment_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    fieldPairCoefficientMoment g χ 0 = 0 := by
  simp [fieldPairCoefficientMoment, mellinCoefficient]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSamePairBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two moving leaves in the same bottom pair of an actual quartet -/

namespace Ostmann

open scoped BigOperators

theorem samePair_left_product {U : Type*} [CommGroup U] (P a r : U) :
    P / (a * r) * r = P / a := by
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

theorem samePair_total_product {U : Type*} [CommGroup U] (P a b r : U) :
    (P / (a * r) * r) * (a / b * b) = P := by
  rw [samePair_left_product, div_mul_cancel, div_mul_cancel]

theorem samePair_right_total_product {U : Type*} [CommGroup U] (P a b r : U) :
    (a⁻¹ / b * b) * (P * a / r * r) = P := by
  rw [div_mul_cancel, div_mul_cancel]
  simp [mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCrossBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient bound for every cross-pair orientation of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def crossLeftLeaves {U : Type*} [CommGroup U]
    (friendly : Bool) (a r : U) : U × U := if friendly then (r⁻¹, a) else (a, r⁻¹)

noncomputable def crossRightLeaves {U : Type*} [CommGroup U]
    (friendly : Bool) (P a b r : U) : U × U :=
  if friendly then (P * r / (a * b), b) else (b, P * r / (a * b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossQuartetFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-fiber coordinates for the cross-pair coefficient bounds -/

namespace Ostmann

open scoped BigOperators

def pairOrient {U : Type*} (friendly : Bool) (xy : U × U) : U × U :=
  if friendly then xy else (xy.2, xy.1)

def quartetOrient {U : Type*} (left right : Bool) (m : (U × U) × (U × U)) :
    (U × U) × (U × U) := (pairOrient left m.1, pairOrient right m.2)

theorem pairOrient_product {U : Type*} [CommGroup U] (friendly : Bool) (xy : U × U) :
    (pairOrient friendly xy).1 * (pairOrient friendly xy).2 = xy.1 * xy.2 := by
  cases friendly <;> simp [pairOrient, mul_comm]

theorem fourth_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P * a⁻¹ / (b * d) = c := by
  apply (div_eq_iff_eq_mul).2
  apply (mul_inv_eq_iff_eq_mul).2
  calc
    P = (a * b) * (c * d) := h.symm
    _ = (c * (b * d)) * a := by ac_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SamePairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-fiber laws for the two same-pair parametrizations -/

namespace Ostmann

open scoped BigOperators

theorem first_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P / ((c * d) * b) = a := by
  apply div_eq_iff_eq_mul.mpr
  exact h.symm.trans (by ac_rfl)

theorem third_of_product {U : Type*} [CommGroup U] (a b c d P : U)
    (h : (a * b) * (c * d) = P) : P * (a * b)⁻¹ / d = c := by
  apply div_eq_iff_eq_mul.mpr
  apply mul_inv_eq_iff_eq_mul.mpr
  exact h.symm.trans (by ac_rfl)

theorem undo_pair_product {U : Type*} [CommGroup U] (a b : U) :
    ((a * b)⁻¹)⁻¹ / b = a := by rw [inv_inv, mul_div_cancel_right]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryGiantSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two current giants refer only to previously reconstructed pivots -/

namespace Ostmann

open scoped Classical

/-- This is the actual forward update: the reconstructed pivot becomes
one giant, and the giant on the selected branch is retained. -/
def evolveGiantValues (p : ℕ → ℤ) : ℕ → ℤ × ℤ → List Bool → ℤ × ℤ
  | _, g, [] => g
  | d, g, b :: path => evolveGiantValues p (d + 1) (p d, if b then g.2 else g.1) path

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RealQuadraticPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def realAdditivePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem realAdditivePhase_zero : realAdditivePhase 0 = 1 := by
  simp [realAdditivePhase]

@[simp] theorem norm_realAdditivePhase (x : ℝ) : ‖realAdditivePhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem conj_realAdditivePhase (x : ℝ) :
    conj (realAdditivePhase x) = realAdditivePhase (-x) := by
  unfold realAdditivePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

noncomputable def realQuadraticPhase (α β : ℝ) (j : ℕ) : ℂ :=
  realAdditivePhase (α * (j : ℝ) ^ 2 + β * j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_WeightedPhaseExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

noncomputable def discreteVariation (w : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖w (N - 1)‖ + ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRootCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root cells used to split the long-variable weights

A cell records the side of each real root, retaining the roots themselves as
separate cells. Polynomial inequalities are constant on a cell; polynomial
arguments are monotone when the derivative roots are included among the cuts.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def rootCellCode (S : Finset ℝ) (x : ℝ) : S → Ordering :=
  fun r => compare x r.val

noncomputable def polynomialRootCuts {I : Type*} [Fintype I]
    (P : I → Polynomial ℝ) : Finset ℝ :=
  Finset.univ.biUnion (fun i => (P i).roots.toFinset)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiMonomialFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-cube inequality for a concrete family of distinct monomials -/

namespace Ostmann

open scoped BigOperators

noncomputable def monomialCoefficients {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (a : ι → ℝ) (Q : Finset P) : ℝ :=
  ∑ i, if σ i = Q then a i else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarefreeBonami
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bonami's inequality for the actual squarefree coefficient indices -/

namespace Ostmann

open scoped BigOperators

def primeFactorSubset (P : Finset ℕ) (s : ℕ) : Finset P :=
  Finset.univ.filter (fun p => p.val ∈ s.primeFactors)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PhaseDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance to the nearest integer controls a linear phase sum -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem realAdditivePhase_intCast (k : ℤ) : realAdditivePhase k = 1 := by
  unfold realAdditivePhase
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedPhasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite reciprocal-distance bound for separated centered phases -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def centeredPhaseBin (r : ℕ) (x : ℝ) : Bool × ℕ :=
  (decide (x < 0), ⌊2 * (r : ℝ) * |x|⌋₊)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_RootPopulations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete root populations attached to endpoint subsets -/

namespace Ostmann

open scoped Classical

def kernelRootPopulation (S : Finset ℤ) (root : ℤ → ℕ) : Finset ℕ := S.image root

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

theorem prime_list_prod_pos (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) : 0 < ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons]
    exact Nat.mul_pos (hp p (List.mem_cons_self)).pos (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeCRTFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the local correlation bounds over the prime factors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The actual function on the product modulus obtained from local prime functions. -/
noncomputable def primeCRTFunction (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) : ZMod ps.prod → ℂ := by
  cases ps with
  | nil => exact fun _ => 1
  | cons p ps =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let e := ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    exact fun x => F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete Dirichlet character with Jacobi numerator -/

namespace Ostmann

noncomputable def jacobiResidue (N : ℕ) (a : ZMod N) : ℤ := jacobiSym (a.val : ℤ) N

theorem jacobiResidue_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiResidue N (a : ZMod N) = jacobiSym a N := by
  unfold jacobiResidue
  rw [ZMod.val_intCast]
  exact (jacobiSym.mod_left a N).symm

/-- This definition includes the modulus-one character. The nonunit values
vanish by the gcd criterion for Jacobi symbols. -/
noncomputable def jacobiCharacterInt (N : ℕ) [NeZero N] : DirichletCharacter ℤ N where
  toFun := jacobiResidue N
  map_one' := by simpa using jacobiResidue_intCast N 1
  map_mul' := by
    intro a b
    have hm : (((a.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod N) = a * b := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    calc
      jacobiResidue N (a * b) = jacobiResidue N (((a.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod N) :=
        congrArg (jacobiResidue N) hm.symm
      _ = jacobiSym ((a.val : ℤ) * (b.val : ℤ)) N := jacobiResidue_intCast N _
      _ = jacobiResidue N a * jacobiResidue N b := jacobiSym.mul_left _ _ _
  map_nonunit' := by
    intro a ha
    unfold jacobiResidue
    apply jacobiSym.eq_zero_iff_not_coprime.mpr
    intro hc
    have hcop : a.val.Coprime N := by simpa only [Int.gcd_natCast_natCast] using hc
    have hu := (ZMod.isUnit_iff_coprime a.val N).mpr hcop
    rw [ZMod.natCast_zmod_val] at hu
    exact ha hu

@[simp] theorem jacobiCharacterInt_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiCharacterInt N (a : ZMod N) = jacobiSym a N := jacobiResidue_intCast N a

noncomputable def jacobiCharacter (N : ℕ) [NeZero N] : DirichletCharacter ℝ N :=
  (jacobiCharacterInt N).ringHomComp (Int.castRingHom ℝ)

@[simp] theorem jacobiCharacter_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiCharacter N (a : ZMod N) = (jacobiSym a N : ℝ) := by
  simp [jacobiCharacter, MulChar.ringHomComp_apply]

@[simp] theorem jacobiCharacter_natCast (N : ℕ) [NeZero N] (a : ℕ) :
    jacobiCharacter N (a : ZMod N) = (jacobiSym (a : ℤ) N : ℝ) := by
  simpa only [Int.cast_natCast] using jacobiCharacter_intCast N (a : ℤ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticReciprocityCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity formulas for the sign and two-part of a kernel -/

namespace Ostmann

noncomputable def realFourCharacter : DirichletCharacter ℝ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℝ)

noncomputable def realEightCharacter : DirichletCharacter ℝ 8 :=
  ZMod.χ₈.ringHomComp (Int.castRingHom ℝ)

@[simp] theorem realFourCharacter_apply (a : ℕ) : realFourCharacter (a : ZMod 4) = (ZMod.χ₄ a : ℝ) := by
  rfl

@[simp] theorem realEightCharacter_apply (a : ℕ) : realEightCharacter (a : ZMod 8) = (ZMod.χ₈ a : ℝ) := by
  rfl

/-- The odd-part character, with the parity twist prescribed by reciprocity. -/
noncomputable def signedOddKernelCharacter (N : ℕ) [NeZero N] (negative : Bool) :
    DirichletCharacter ℝ (Nat.lcm N 4) :=
  DirichletCharacter.mul (jacobiCharacter N)
    (realFourCharacter ^ (N / 2 + if negative then 1 else 0))

/-- The conductor-eight twist accounts for both the sign and the factor two. -/
noncomputable def evenKernelTwist (k : ℕ) : DirichletCharacter ℝ 8 :=
  (realFourCharacter ^ k).changeLevel (by decide : 4 ∣ 8) * realEightCharacter

noncomputable def signedEvenKernelCharacter (N : ℕ) [NeZero N] (negative : Bool) :
    DirichletCharacter ℝ (Nat.lcm N 8) :=
  DirichletCharacter.mul (jacobiCharacter N)
    (evenKernelTwist (N / 2 + if negative then 1 else 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePowerRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the prime-power remainder in the Euler identity -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def primePowerRemainder (n : ℕ) : ℂ :=
  if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime logarithmic series and the actual L-function derivative -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def primeLogCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then χ n * (Real.log n : ℂ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealPrimeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real prime series for a real Dirichlet character -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def realPrimeTerm {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then χ n * Real.log n / (n : ℝ) ^ s else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RademacherMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moments of the Boolean monomials -/

namespace Ostmann

open scoped BigOperators

def monomialOccurrence {ι : Type*} [Fintype ι] {P : Finset ℕ}
    (σ : ι → Finset P) (p : P) : ℕ :=
  (Finset.univ.filter (fun i => p ∈ σ i)).card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_WeightedJacobiMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring square-product moments to weighted Jacobi sums

The nonsquare error is an explicit numerical bound to be supplied by the
periodic-character calculation; it is not a published or global assumption.
-/

namespace Ostmann

open scoped BigOperators

def realJacobi (n m : ℕ) : ℝ := (jacobiSym (n : ℤ) m : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionCharacterCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of distinct short characters on a fixed progression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def characterPairValue {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (x : ZMod (q * r)) : ℂ :=
  χ ((ZMod.chineseRemainder hqr x).1) * conj (ψ ((ZMod.chineseRemainder hqr x).2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntegerProgressionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue-progressions in a padded integer interval -/

namespace Ostmann

/-- Row/column transposition lists each residue class in increasing order. -/
def integerProgressionPartition (Q K : ℕ) : Fin (K * Q) ≃ Σ _ : Fin Q, Fin K :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin K) (Fin Q)).trans
    (Equiv.sigmaEquivProd (Fin Q) (Fin K)).symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCellSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp polynomial support conditions are functions of the root cell -/

namespace Ostmann

open scoped Classical

noncomputable def polynomialSupportCode {I : Type*} (P : I → Polynomial ℝ) (x : ℝ) : I → Bool :=
  fun i => decide (0 ≤ (P i).eval x)

/-- This is the actual support flag, defined from the inequalities, rather
than an assumption that the supports are regular on the cells. -/
noncomputable def polynomialRootCellFlag {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (keep : (I → Bool) → Bool) (c : S → Ordering) : ℂ :=
  if ∃ x : ℝ, rootCellCode S x = c ∧ keep (polynomialSupportCode P x) = true then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lifts of a nonzero line modulo a prime square

The reduction map has exactly `p` lifts over every residue. A line with a
unit coefficient has exactly `p` zero lifts among the `p²` pairs over a
fixed solution modulo `p`. This is the relative `1/p` loss in §8.
-/

namespace Ostmann

open scoped BigOperators

/-- Translate an additive fiber to the zero fiber. -/
def additiveFiberEquiv {G H : Type*} [AddGroup G] [AddGroup H]
    (φ : G →+ H) (x : G) : {y : G // φ y = φ x} ≃ {y : G // φ y = 0} where
  toFun y := ⟨y - x, by simp [y.property]⟩
  invFun y := ⟨y + x, by simp [y.property]⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp

theorem unit_linear_solution {R : Type*} [CommRing R]
    (a : Rˣ) (b x y : R) (h : (a : R) * x + b * y = 0) :
    x = -(a⁻¹ : Rˣ) * b * y := by
  have he := congrArg (fun z : R => (a⁻¹ : Rˣ) * z) h
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at he
  linear_combination he

/-- A line with a unit first coefficient has one zero lift for each lift of
the second coordinate, over any fixed solution in the quotient. -/
def liftedLineEquiv {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (a : Rˣ) (b : R) (x₀ y₀ : K)
    (hbase : φ a * x₀ + φ b * y₀ = 0) :
    {xy : R × R // φ xy.1 = x₀ ∧ φ xy.2 = y₀ ∧ (a : R) * xy.1 + b * xy.2 = 0} ≃
      {y : R // φ y = y₀} where
  toFun xy := ⟨xy.1.2, xy.property.2.1⟩
  invFun y := ⟨(-(a⁻¹ : Rˣ) * b * y, y), by
    refine ⟨?_, y.property, ?_⟩
    · have he := unit_linear_solution (Units.map φ.toMonoidHom a) (φ b) x₀ y₀ hbase
      change x₀ = -φ (↑(a⁻¹)) * φ b * y₀ at he
      simpa only [map_mul, map_neg, y.property] using he.symm
    · simp [mul_assoc]⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · exact (unit_linear_solution a b xy.1.1 xy.1.2 xy.property.2.2).symm
    · rfl
  right_inv y := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SymbolicLineComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed replacement of accidental arithmetic flags

After denominators are cleared in §8, coefficient and minor tests are integer
polynomials. Under independent representative priors, replacing their congruence
flags by their rational polynomial-identity flags has the following quantitative
error. The polynomial root and prime-divisor estimates are proved inputs here.
-/

namespace Ostmann

open scoped BigOperators

/-- Use one fixed decision procedure in statements and proofs. -/
noncomputable def arithmeticTestFlag (P : Prop) : Bool := by
  classical
  exact decide P

@[simp] theorem arithmeticTestFlag_of_true {P : Prop} (h : P) : arithmeticTestFlag P = true := by
  simp [arithmeticTestFlag, h]

@[simp] theorem arithmeticTestFlag_of_false {P : Prop} (h : ¬P) : arithmeticTestFlag P = false := by
  simp [arithmeticTestFlag, h]

@[simp] theorem arithmeticTestFlag_eq_true_iff (P : Prop) :
    arithmeticTestFlag P = true ↔ P := by
  classical
  by_cases h : P <;> simp [h]

@[simp] theorem arithmeticTestFlag_eq_false_iff (P : Prop) :
    arithmeticTestFlag P = false ↔ ¬P := by
  classical
  by_cases h : P <;> simp [h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticIntegerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed arithmetic comparison for actual integer polynomial tests -/

namespace Ostmann

open scoped BigOperators

noncomputable def integerTestValue {A : Type*} {n : ℕ} (value : A → ℤ)
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → A) : ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun j => value (x j)) F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_InternalLineProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rank and feasibility tests for repeated internal-prime occurrences

Section 8, equation `arith-line-probabilities`: the simultaneous linear tests
have probability zero in rank two, and exactly `1/(p-1)` or `1/p` in the
respective feasible rank-one cases. A distinguished nonzero occurrence is
sufficient; no independence of the repeated tests is assumed.
-/

namespace Ostmann

open scoped BigOperators
open scoped Classical

def lineRankOne {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  ∀ j, a i * b j - b i * a j = 0

def externalLineFeasible {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  a i ≠ 0 ∧ lineRankOne a b i

def unitLineFeasible {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  a i ≠ 0 ∧ b i ≠ 0 ∧ lineRankOne a b i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialLineFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact cleared polynomial flags for an internal line system -/

namespace Ostmann

noncomputable section

open scoped Classical

def lineFeasibleFlags {J : Type*} (external : Bool) (f : Bool ⊕ J → Bool) : Prop :=
  f (.inl false) = false ∧ (external = true ∨ f (.inl true) = false) ∧
    ∀ j, f (.inr j) = true

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZeroVariableHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing reconstructed-pivot coprimalities to actual prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def zeroHistoryVariable {σ : Type*} (i : σ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  MvPolynomial.bind₁ (fun j => if j = i then 0 else MvPolynomial.X j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonHistoryPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero common modulus constructed from the actual small frequencies -/

namespace Ostmann

def historyFrequencyBase (frequencies : List ℤ) : ℕ := (frequencies.map Int.natAbs).prod

def historyFrequencyPeriod (frequencies : List ℤ) (degree : ℕ) : ℕ :=
  historyFrequencyBase frequencies ^ degree

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEmbeddingPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the original finite prior without changing its mean -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def embeddingExtend {A B C : Type*} [Zero C] (e : A ↪ B) (f : A → C) (b : B) : C :=
  if h : ∃ a, e a = b then f h.choose else 0

def intervalSampleEmbedding {A : Type*} (value : A → ℕ) (hinj : Function.Injective value)
    (a N : ℕ) (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + N) : A ↪ Fin N where
  toFun := fun x => ⟨value x - a, by have h₁ := hlow x; have h₂ := hhigh x; omega⟩
  inj' := by
    intro x y hxy
    apply hinj
    have he := congrArg Fin.val hxy
    have hx := hlow x
    have hy := hlow y
    dsimp at he
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveLeafExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact signed leaves and real support factor of a recursive history -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform Classical

noncomputable def signedLeafValue {State : Type*} (F : State → ℤ → ℂ)
    (z : (State × ℤ) × Bool) : ℂ :=
  if z.2 then F z.1.1 z.1.2 else conj (F z.1.1 z.1.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedWordLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal frequency and polynomial of every reconstructed Fourier leaf -/

namespace Ostmann

open scoped Classical

def flipEvaluatedLeaf (z : Bool × ℤ × ℚ) : Bool × ℤ × ℚ := (!z.1, z.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLineIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual line integrals as bounded functions of the cleared polynomial tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def internalLineScalar (external : Bool) (p : ℕ) : ℝ :=
  ((if external then p else p - 1 : ℕ) : ℝ)⁻¹

noncomputable def internalLineFlagWeight {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) : ℝ :=
  if lineFeasibleFlags external flags then internalLineScalar external p else 0

/-- The normalized count before the giant variables are integrated out. -/
noncomputable def internalLineProbability {J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (a b : J → ZMod p) : ℝ :=
  if external then
    (Fintype.card {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ)
  else
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLineComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed symbolic replacement for the actual integrated line factors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def integerLineReduction {A : Type*} {n : ℕ} (value : A → ℤ)
    (x : Fin n → A) (p : ℕ) : MvPolynomial (Fin n) ℤ →+* ZMod p :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun j => (value (x j) : ZMod p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_IntegerPoissonTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer-lattice form of finite periodic Poisson summation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

def integerResidueEquiv (N : ℕ) [NeZero N] : ℤ ≃ ZMod N × ℤ :=
  ((Int.divModEquiv N).trans (Equiv.prodComm ℤ (Fin N))).trans
    (Equiv.prodCongr (ZMod.finEquiv N).toEquiv (Equiv.refl ℤ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ScaledPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original scale in the quadratic-character Poisson formula -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory

noncomputable def positiveDilate (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => a * x) (by fun_prop)
    ⟨1, a⁻¹, fun x => by
      simp only [pow_one, norm_mul, Real.norm_eq_abs, abs_of_pos ha]
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      simpa only [mul_one] using le_add_of_nonneg_left (a := |x|) (inv_nonneg.mpr ha.le)⟩ f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TernaryProductPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The generating polynomial for a finite ternary population

The differential equation below yields an elementary repeat-removal bound.
It uses only `y^3 = y`, the identity satisfied by the oriented quadratic
characters, and does not invoke partition inversion as an additional input.
-/

namespace Ostmann

open scoped BigOperators Classical
open Polynomial

noncomputable def ternaryProduct {A : Type*} (S : Finset A) (y : A → ℝ) : ℝ[X] :=
  ∏ i ∈ S, (1 + C (y i) * X)

noncomputable def ternaryDistinct {A : Type*} (S : Finset A) (y : A → ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (ternaryProduct S y).coeff k

@[simp] theorem ternaryDistinct_zero {A : Type*} (S : Finset A) (y : A → ℝ) :
    ternaryDistinct S y 0 = 1 := by
  simp [ternaryDistinct, ternaryProduct, coeff_zero_prod]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedRepeatRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing repeated primes inside the positive amplified moment -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def ternaryMean {A : Type*} [Fintype A] (y : A → ℝ) : ℝ :=
  (∑ i, y i) / Fintype.card A

noncomputable def ternaryDistinctMean {A : Type*} [Fintype A] (y : A → ℝ) (k : ℕ) : ℝ :=
  (∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℝ) ^ k

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RescaledWeightVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the rescaled smooth weight -/

namespace Ostmann

open scoped BigOperators

noncomputable def rescaledPhaseWeight (Φ : ℝ → ℂ) (ξ Y : ℝ) (j : ℕ) : ℂ :=
  Φ (((j : ℝ) + ξ) / Y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SchwartzWeightVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete variation bounds for the quadratic Schwartz weight -/

namespace Ostmann

open scoped SchwartzMap

/-- Pullback along the squaring map is still a Schwartz function on the line.
This is the weight appearing after writing a frequency as `s*v*w^2`. -/
noncomputable def quadraticSchwartzWeight (Φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => x ^ 2) (by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]⟩ Φ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SchwartzDensityCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single expanded pair in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def correlationWeightBudget (Φ Ψ : 𝓢(ℝ, ℂ)) (C D : ℝ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 Φ *
    (SchwartzMap.seminorm ℝ 0 0 Ψ + SchwartzMap.seminorm ℝ 0 1 Ψ * D) +
  SchwartzMap.seminorm ℝ 0 0 Ψ *
    (SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_TruncatedQuadraticCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete finite correlation bound after quadratic normalization -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def densityWave {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (u : (ZMod q)ˣ)
    (Φ : 𝓢(ℝ, ℂ)) (α Y : ℝ) (n : ℕ) : ℂ :=
  Φ ((n : ℝ) / Y) * g ((u : ZMod q) * (n : ZMod q)) * realAdditivePhase α ^ n

noncomputable def normalizedDensityWaveSum {q : ℕ} [NeZero q] {ι : Type*}
    (g : ZMod q → ℂ) (W : Finset ι) (u : ι → (ZMod q)ˣ) (Φ : 𝓢(ℝ, ℂ))
    (α Y : ι → ℝ) (R v : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((n : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑ w ∈ W, densityWave g (u w) Φ (α w) (Y w) n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDensitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's finite quadratic sums and their zero nonunit terms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticDensityTerm {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s w : ℕ) : ℂ :=
  g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) *
    realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ s *
      Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q))

noncomputable def quadraticDensitySum {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (W : Finset ℕ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑ w ∈ W, quadraticDensityTerm g a θ Φ R v s w

noncomputable def unitQuadraticSupport {q : ℕ} (W : Finset ℕ) (a : ZMod q) : Finset ℕ :=
  by
    classical
    exact W.filter (fun w => IsUnit (a * (w : ZMod q) ^ 2))

noncomputable def quadraticUnitScalar {q : ℕ} (a : ZMod q) (w : ℕ) : (ZMod q)ˣ :=
  by
    classical
    exact if h : IsUnit (a * (w : ZMod q) ^ 2) then h.unit else 1

@[simp] theorem mem_unitQuadraticSupport {q : ℕ} (W : Finset ℕ) (a : ZMod q) (w : ℕ) :
    w ∈ unitQuadraticSupport W a ↔ w ∈ W ∧ IsUnit (a * (w : ZMod q) ^ 2) := by
  classical
  exact Finset.mem_filter

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeSet_list_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P.toList, p.Prime := fun p hp => hP p (Finset.mem_toList.mp hp)

theorem primeSet_list_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    P.toList.Pairwise Nat.Coprime := by
  apply List.Pairwise.imp_of_mem _ P.nodup_toList
  intro p q hp hq hpq
  exact (Nat.coprime_primes (hP p (Finset.mem_toList.mp hp))
    (hP q (Finset.mem_toList.mp hq))).mpr hpq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original physical-space amplified moment -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def orientedQuadraticValue (ε : ℕ → ℝ) (t : ℕ → ℤ) (n : ℤ) (p : ℕ) : ℝ :=
  ε p * (jacobiSym (n - t p) p : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCRTFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cofactor arguments for the Fourier transform of a prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def tupleCofactor {I : Type*} [Fintype I] (p : I → ℕ) (i : I) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p j

theorem tupleCofactor_mul {I : Type*} [Fintype I] (p : I → ℕ) (i : I) :
    p i * tupleCofactor p i = ∏ j, p j :=
  Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

theorem tupleCofactor_coprime {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (i : I) :
    (tupleCofactor p i).Coprime (p i) := by
  apply Nat.Coprime.symm
  exact Nat.coprime_prod_right_iff.mpr (fun j hj => hc (Finset.mem_erase.mp hj).1.symm)

noncomputable def tupleCRTFunction {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (x : ZMod (∏ i, p i)) : ℂ :=
  ∏ i, F i (ZMod.prodEquivPi p hc x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCharacterPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation and the initial graph phase of a character tuple -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap ComplexConjugate Classical

noncomputable def primitiveGaussPhase {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) : ℂ :=
  gaussSum χ ZMod.stdAddChar / (Real.sqrt (p : ℝ) : ℂ)

noncomputable def tupleGraphPhase {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
    primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i)) *
      ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotRowPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded pivot row after grouping by v/H -/

namespace Ostmann

open scoped BigOperators

noncomputable def pivotLocalRow {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (t D Y u : ZMod p) (ε : ℤ) : ℂ :=
  ZMod.stdAddChar (t * (u * (D * Y)⁻¹)) * κ * χ (D * Y * u⁻¹) ^ ε

noncomputable def pivotTupleRow {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i)) (κ : I → ℂ)
    (t D Y u : ∀ i, ZMod (p i)) (ε : I → ℤ) : ℂ :=
  ∏ i, pivotLocalRow (χ i) (κ i) (t i) (D i) (Y i) (u i) (ε i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraphRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The row products of the actual transferred directed graph -/

namespace Ostmann

open scoped BigOperators

def transferredLabels {H Y K : Type*} (L R : H → K) (U : Y → K) : (Bool × H) ⊕ Y → K
  | .inl (true, h) => L h
  | .inl (false, h) => R h
  | .inr y => U y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraphPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of every surviving local factor with the new graph phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The erased pivot is represented only by its total integer. Its outgoing
row has already been removed by Cauchy--Schwarz. -/
noncomputable def retainedGraphRow {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option I → Option I → ℤ)
    (i : I) (P : ZMod p) (q : I → ZMod p) : ℂ :=
  χ P ^ b (some i) none * ∏ j, χ (q j) ^ b (some i) (some j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DirectedPrimePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common directed-graph phase for the initial and transferred amplitudes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def directedPrimePhase {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (ν : I → ℂ) (b : I → I → ℤ) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
    ν i * ∏ j, χ i (p j : ZMod (p i)) ^ b i j

def initialDirectedGraph {I : Type*} [DecidableEq I] (i j : I) : ℤ :=
  if i = j then 0 else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_OneSidedGraphFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating a one-sided graph edge from the bounded unary factors -/

namespace Ostmann

open scoped BigOperators

def twoVertexLabels {J : Type*} (fixed : J → ℕ) (q p : ℕ) : Bool ⊕ J → ℕ
  | .inl true => q
  | .inl false => p
  | .inr j => fixed j

noncomputable def finiteEdgeWeight {I : Type*} [Fintype I]
    (E : I → I → ℕ → ℕ → ℂ) (ν : I → ℕ → ℂ) (v : I → ℕ) : ℂ :=
  ∏ i, ν i (v i) * ∏ j, E i j (v i) (v j)

noncomputable def fixedGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) : ℂ :=
  ∏ i, ν (.inr i) (fixed i) * ∏ j, E (.inr i) (.inr j) (fixed i) (fixed j)

noncomputable def longGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (p : ℕ) : ℂ :=
  ν (.inl false) p * (∏ j, E (.inl false) (.inr j) p (fixed j)) *
    ∏ i, E (.inr i) (.inl false) (fixed i) p

noncomputable def shortGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (q : ℕ) : ℂ :=
  ν (.inl true) q * (∏ j, E (.inl true) (.inr j) q (fixed j)) *
    (∏ i, E (.inr i) (.inl true) (fixed i) q) * fixedGraphFactor E ν fixed

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DirichletGraphFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine character attached to a surviving directed edge -/

namespace Ostmann

open scoped BigOperators

noncomputable def dirichletGraphEdge {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (b : I → I → ℤ)
    (i j : I) (x y : ℕ) : ℂ := χ i x (y : ZMod x) ^ b i j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPivotTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported transfer from actual prime tuples to positive integers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def positiveIntegerPivotKey (M : ℕ) (hM : 0 < M) (L : ℕ) (v : ℤ) : Fin M := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact pivotResidueKey M L v

theorem transferPrimeTupleProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (x : Fin n → P) : 0 < ∏ i, (x i : ℕ) :=
  Finset.prod_pos (fun i _ => (hP (x i) (x i).property).pos)

noncomputable def primeTuplePivotKey (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (x : Fin n → P) (L : ℕ) (v : ℤ) : Fin (∏ i, (x i : ℕ)) :=
  positiveIntegerPivotKey _ (transferPrimeTupleProduct_pos P hP x) L v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferTupleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product and cofactor coordinates for the copied prime list -/

namespace Ostmann

open scoped BigOperators

theorem tupleCofactor_sum_left {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) (h : H) (hL : L h ≠ 0) :
    tupleCofactor (Sum.elim L U) (.inl h) = tupleCofactor L h * ∏ y, U y := by
  apply mul_left_cancel₀ hL
  calc
    _ = ∏ i, Sum.elim L U i := tupleCofactor_mul (Sum.elim L U) (.inl h)
    _ = (∏ k, L k) * ∏ y, U y := Fintype.prod_sum_type _
    _ = (L h * tupleCofactor L h) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_sum_right {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) (y : Y) (hU : U y ≠ 0) :
    tupleCofactor (Sum.elim L U) (.inr y) = (∏ h, L h) * tupleCofactor U y := by
  apply mul_left_cancel₀ hU
  calc
    _ = ∏ i, Sum.elim L U i := tupleCofactor_mul (Sum.elim L U) (.inr y)
    _ = (∏ k, L k) * ∏ y, U y := Fintype.prod_sum_type _
    _ = (∏ k, L k) * (U y * tupleCofactor U y) := by rw [tupleCofactor_mul]
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferAdditiveProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete additive phase after a transfer, on the actual prime list -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def transferredAdditiveRow (t : ∀ p : ℕ, ZMod p) (s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) => ZMod.stdAddChar (t (L h) * ((s : ZMod (L h)) /
      (tupleCofactor (transferredLabels L R U) (.inl (true, h)) : ZMod (L h))))
  | .inl (false, h) => ZMod.stdAddChar (t (R h) * ((s : ZMod (R h)) /
      (tupleCofactor (transferredLabels L R U) (.inl (false, h)) : ZMod (R h))))
  | .inr y => ZMod.stdAddChar (t (U y) * ((s : ZMod (U y)) /
      (tupleCofactor (transferredLabels L R U) (.inr y) : ZMod (U y))))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferCompletePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full transfer phase identity on the actual copied tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def retainedAdditiveBranch (t : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) : ℂ :=
  (∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
      ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) *
  ∏ y, ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
      ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y))))

noncomputable def retainedCharacterBranch
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ) : ℂ :=
  (∏ h, νH h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
    (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) *
  ∏ y, νY y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
    (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))

noncomputable def retainedPrimePhase (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ) (v : ℤ) : ℂ :=
  retainedAdditiveBranch L U t M v * retainedCharacterBranch L U χH χY b νH νY M

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedPivotPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing every constituent of a grouped pivot from the directed phase -/

namespace Ostmann

open scoped BigOperators Classical

/-- The phase left after the outgoing pivot rows have been removed. -/
noncomputable def retainedGroupedPhase {I : Type*} [Fintype I] (Q : I → ℕ)
    [∀ i, NeZero (Q i)] (χ : ∀ i, DirichletCharacter ℂ (Q i))
    (t : ∀ i, ZMod (Q i)) (ν : I → ℂ)
    (b : Option I → Option I → ℤ) (M : ℕ) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * (((M * tupleCofactor Q i : ℕ) : ZMod (Q i))⁻¹ * (v : ZMod (Q i)))) * ν i *
      retainedGraphRow (χ i) b i (M : ZMod (Q i)) (fun j => (Q j : ZMod (Q i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedResidueRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire outgoing pivot phase factors through the composite residue key -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedResidueRow {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, NeZero (P k)] (χ : ∀ k, DirichletCharacter ℂ (P k))
    (κ : K → ℂ) (t : ∀ k, ZMod (P k)) (Y : ℕ) (ε : K → ℤ)
    (u : Fin (∏ k, P k)) : ℂ :=
  pivotTupleRow P χ κ t (fun k => (tupleCofactor P k : ZMod (P k)))
    (fun k => (Y : ZMod (P k))) (fun k => (u.val : ZMod (P k))) ε

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedPhaseFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact phase factorization for a supported grouped pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem groupedPivotProduct_pos {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, Fact (P k).Prime] : 0 < ∏ k, P k :=
  Finset.prod_pos fun k _ => (Fact.out : (P k).Prime).pos

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRegularUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-independent multipliers of the regular copied rows -/

namespace Ostmann

open scoped ComplexConjugate

/-- All frequency dependence of a regular unary is its current root power. -/
noncomputable def regularUnary {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (ε : ℤ) (v : ZMod p) : ℂ := κ * χ v ^ (-ε)

noncomputable def regularCopiedMultiplier {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (ε : ℤ) (b : Bool) : ℂ :=
  if b then κ else conj κ * χ (-1) ^ (-ε)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def primeTupleAdditivePhase {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) : ℂ := by
  let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
  exact ∏ i, ZMod.stdAddChar (t (p i) * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedGraphQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph quotient under an actual matching of the prime variables -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

def graphDifference {I : Type*} (b c : I → I → ℤ) (i j : I) : ℤ := b i j - c i j

def transportGraph {I J : Type*} (e : I ≃ J) (b : I → I → ℤ) (i j : J) : ℤ :=
  b (e.symm i) (e.symm j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes derived from the full copied-slot schedule -/

namespace Ostmann

open scoped Classical

/-- The level-zero graph has exponent one on every distinct ordered pair. -/
noncomputable def initialCompleteGraph {I : Type*} (i j : I) : ℤ :=
  if i = j then 0 else 1

@[simp] theorem initialCompleteGraph_self {I : Type*} (i : I) :
    initialCompleteGraph i i = 0 := by simp [initialCompleteGraph]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferDirectedPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied local factors form the next actual directed prime phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Characters keep their original slot identity when a slot is copied. -/
def copiedSlotCharacter {H Y : Type*}
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p) :
    (Bool × H) ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p
  | .inl (_, h) => χH h
  | .inr y => χY y

noncomputable def copiedSlotUnary {H Y : Type*}
    (q : (Bool × H) ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) => νL h * χH h (q (.inl (true, h)))
      ((v : ZMod (q (.inl (true, h)))) / (s : ZMod (q (.inl (true, h))))) ^
        b (some (.inl h)) none
  | .inl (false, h) => conj (νR h) * χH h (q (.inl (false, h)))
      ((-w : ZMod (q (.inl (false, h)))) / (s : ZMod (q (.inl (false, h))))) ^
        (-b (some (.inl h)) none)
  | .inr y => νYL y * conj (νYR y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleWordUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-independent multipliers for the actual schedule word slots -/

namespace Ostmann

open scoped ComplexConjugate Classical

noncomputable def initialRegularUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (i : I) (v : ℤ) (p : ℕ) : ℂ := regularUnary (χ i p) (κ i p) 1 (v : ZMod p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedDirectedPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next directed phase with support derived from the original ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem transferredPrimeFact {H Y : Type*} (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (i : (Bool × H) ⊕ Y) : Fact (transferredLabels L R U i).Prime := by
  rcases i with ⟨c, h⟩ | y
  · cases c
    · exact (inferInstance : Fact (R h).Prime)
    · exact (inferInstance : Fact (L h).Prime)
  · exact (inferInstance : Fact (U y).Prime)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomAncestorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing finite ancestor products from distinct atom sources -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def atomAncestorSet {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) : Finset (Fin d) :=
  (Finset.univ.image source).toRight

noncomputable def atomFixedProduct {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) (C : B → ℤ) : ℤ :=
  ∏ b ∈ (Finset.univ.image source).toLeft, C b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPreorderNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder pivots reproduce the literal scheduled atom assignments -/

namespace Ostmann
open scoped Classical

def reversePathOfList (path : List Bool) : Fin path.length → Bool :=
  fun j => !(path[j.val])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSpectatorHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From reconstructed integer histories to the spectator tree

The realization conditions record the two child products and the terminal
modulus. They allow composite inserted pivots: division by the compensation
unit gives the giant used by the rational tree. No prime law is assigned to
that composite integer.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def spectatorHistoryLeaf {State : Type*} {q : ℕ} [Fact q.Prime]
    (modulus : State → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (σ : State) (s : ℤ) : ℂ :=
  g ((s : ZMod q) / ((D : ZMod q) * (modulus σ : ZMod q)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveSupportExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original range factors and all arithmetic tests in a flat history -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def transferLeafCutoff {State : Type*}
    (cutoff : State → ℤ → ℝ) (leaf : (State × ℤ) × Bool) : ℝ :=
  cutoff leaf.1.1 leaf.1.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicSupportedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported one-sided estimate over the entire long-prime range -/

namespace Ostmann

open scoped BigOperators Classical

def boundedDyadicIndex (E p : ℕ) : Fin (Nat.log 2 E + 1) :=
  ⟨min (Nat.log 2 p) (Nat.log 2 E), by omega⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedWordPairBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed prime-word coefficient under the original product law -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def wordCoordinateUpdate {σ : Type*} (x : σ → ℤ) (v : σ) (z : ℤ) : σ → ℤ :=
  Function.update x v z

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed variation bounds for the actual moving Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingFourierVariationBudget (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) : ℝ :=
  (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
    (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) ^ (2 ^ n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTopCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual top-giant residue cells for the moving arithmetic support -/

namespace Ostmann
open scoped Classical

def topGiantInput (XL XR : ℕ) (b : Bool) : ℤ := if b then XR else XL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexPrimeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def complexPrimeInterval (q a : ℕ) (s t : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
    if p.Prime ∧ Nat.ModEq q p a then w (Real.log p) * ((p : ℝ)⁻¹ : ℂ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedIntegerIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutoff-weighted distribution of the external integer coordinate -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

noncomputable def integerResidueAtom (q a : ℕ) (G : ℝ) (n : ℕ) : ℝ :=
  if Nat.ModEq q n a then Real.exp (-G) else 0

noncomputable def integerLogCellMass (q a : ℕ) (s t G : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, integerResidueAtom q a G n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerIntervalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def complexIntegerInterval (q a : ℕ) (u v G : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
    w (Real.log n) * (integerResidueAtom q a G n : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

def topGiantReal (XL XR : ℝ) (b : Bool) : ℝ := if b then XR else XL

noncomputable def movingRealUpdate (a : Bool → ℝ) (coord : Bool) (z : ℝ) : Bool → ℝ :=
  @Function.update Bool (fun _ => ℝ) (fun x y => Classical.propDecidable (x = y)) a coord z

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue-independent cells for either real giant coordinate -/

namespace Ostmann
open scoped Classical BigOperators

def movingRealPair (coord : Bool) (fixed z : ℝ) : Bool → ℝ :=
  if coord then topGiantReal fixed z else topGiantReal z fixed

noncomputable def movingCoordinateLeft (coord : Bool) (fixed : ℝ) : Polynomial ℝ :=
  if coord then Polynomial.C fixed else Polynomial.X

noncomputable def movingCoordinateRight (coord : Bool) (fixed : ℝ) : Polynomial ℝ :=
  if coord then Polynomial.X else Polynomial.C fixed

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prime and integer comparisons for either real giant slice -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

def movingKernelRootBudget (n : ℕ) : ℕ :=
  (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 5 * 2 ^ n + 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantLogMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal giant measures, including the retained Page density -/

namespace Ostmann
open MeasureTheory
open scoped ENNReal

noncomputable def intervalDensityMeasure (u v : ℝ) (ρ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc u v)).withDensity (fun x => ENNReal.ofReal (ρ x))

theorem finite_intervalDensityMeasure (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    IsFiniteMeasure (intervalDensityMeasure u v ρ) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hρ.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc hpos)).mpr hρ

noncomputable def integerGiantMeasure (q : ℕ) (G u v : ℝ) : Measure ℝ :=
  intervalDensityMeasure u v (integerLogDensity q G)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact atomic measure of a harmonic prime cell -/

namespace Ostmann
open MeasureTheory Filter
open scoped BigOperators ENNReal BoundedContinuousFunction

instance finite_primeLogAtom (p : ℕ) :
    IsFiniteMeasure (ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)) :=
  (Measure.dirac (Real.log p)).smul_finite ENNReal.ofReal_ne_top

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkKernelPairComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the full original pair, with every sharp gate -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkKernelPairComparisonBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) : ℝ :=
  ((2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
      ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r))) + 1 : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

noncomputable def spectatorBulkCount (k : ℕ) (L : ℝ) : ℕ :=
  2 * ⌊(k : ℝ) ^ 4 * L / 2⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ComponentFibers
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform product fibers for a nonempty component

Fixing one distinguished leaf identifies every component-product fiber
with independent values on the remaining leaves. The fiber cardinality
therefore does not depend on its total.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def completeComponentProduct {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) (i : I) : G :=
  if h : i = i₀ then P / ∏ j, v j else v ⟨i, h⟩

theorem completeComponentProduct_pivot {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) :
    completeComponentProduct i₀ P v i₀ = P / ∏ j, v j := by
  simp [completeComponentProduct]

theorem completeComponentProduct_other {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G)
    (j : {i : I // i ≠ i₀}) : completeComponentProduct i₀ P v j = v j := by
  simp [completeComponentProduct, j.property]

theorem completeComponentProduct_total {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) (v : {i : I // i ≠ i₀} → G) :
    (∏ i : I, completeComponentProduct i₀ P v i) = P := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i₀]
  simp only [completeComponentProduct_pivot, completeComponentProduct_other, div_mul_cancel]

/-- All but one coordinate can be chosen freely in a fixed product fiber. -/
noncomputable def componentProductEquiv {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] (i₀ : I) (P : G) :
    {m : I → G // ∏ i, m i = P} ≃ ({i : I // i ≠ i₀} → G) where
  toFun m j := m.1 j
  invFun v := ⟨completeComponentProduct i₀ P v, completeComponentProduct_total i₀ P v⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    change completeComponentProduct i₀ P (fun j => m.1 j) i = m.1 i
    by_cases hi : i = i₀
    · subst i
      rw [completeComponentProduct_pivot]
      have h := m.property
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i₀] at h
      calc
        _ = (m.1 i₀ * ∏ j : {i : I // i ≠ i₀}, m.1 j) /
            (∏ j : {i : I // i ≠ i₀}, m.1 j) :=
          congrArg (fun x => x / (∏ j : {i : I // i ≠ i₀}, m.1 j)) h.symm
        _ = _ := by simp
    · exact completeComponentProduct_other i₀ P (fun j => m.1 j) ⟨i, hi⟩
  right_inv v := by
    funext j
    exact completeComponentProduct_other i₀ P v j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionProducts
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous product fibers for an arbitrary partition of the leaves -/

namespace Ostmann

open scoped BigOperators

noncomputable def partitionProduct {L C G : Type*} [Fintype L] [DecidableEq C]
    [CommGroup G] (component : L → C) (m : L → G) (c : C) : G :=
  ∏ i : {i : L // component i = c}, m i.1

noncomputable def partitionCoordinates {L C G : Type*}
    (component : L → C) : (L → G) ≃ (∀ c : C, {i : L // component i = c} → G) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

/-- Fixing all component totals is the product of the individual product fibers. -/
noncomputable def partitionProductFiberEquiv {L C G : Type*}
    [Fintype L] [DecidableEq C] [CommGroup G]
    (component : L → C) (P : C → G) :
    {m : L → G // partitionProduct component m = P} ≃
      (∀ c : C, {v : ({i : L // component i = c} → G) // ∏ i, v i = P c}) where
  toFun m c := ⟨fun i => m.1 i.1, congrFun m.property c⟩
  invFun v := ⟨(partitionCoordinates component).symm (fun c => (v c).1), by
    funext c
    change (∏ i : {i : L // component i = c},
      ((partitionCoordinates component).symm (fun d => (v d).1)) i.1) = P c
    have h := congrFun ((partitionCoordinates component).apply_symm_apply
      (fun d => (v d).1)) c
    change (fun i : {i : L // component i = c} =>
      ((partitionCoordinates component).symm (fun d => (v d).1)) i.1) = (v c).1 at h
    rw [h]
    exact (v c).property⟩
  left_inv m := by
    apply Subtype.ext
    exact (partitionCoordinates component).symm_apply_apply m.1
  right_inv v := by
    funext c
    apply Subtype.ext
    exact congrFun ((partitionCoordinates component).apply_symm_apply
      (fun d => (v d).1)) c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FinitePriorDensity
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing a dominated finite sampling law into a complex multiplier -/

namespace Ostmann

noncomputable def finitePriorDensity {X : Type*} (μ : X → ℝ) (F : X → ℂ) (x : X) : ℂ :=
  F x / (μ x : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_InternalPatternWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the line-probability scale in an internal-prime pattern -/

namespace Ostmann
open scoped BigOperators

/-- The coefficient before the simultaneous line probabilities includes one
factor of the prime for every original compensation occurrence. -/
noncomputable def internalPatternWeight {I C A : Type*} [Fintype I]
    (pattern : I → C) (μ : I → A → ℝ) (prime : A → ℕ) (x : C → A) : ℝ :=
  ∏ i, (prime (x (pattern i)) : ℝ) * μ i (x (pattern i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SampleEqualityPatterns
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of finite samples by equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

@[instance_reducible] noncomputable def sampleSetoidFintype (I : Type*) [Fintype I] : Fintype (Setoid I) :=
  Fintype.ofInjective (fun s : Setoid I => {p : I × I | s p.1 p.2}) (by
    intro s t h
    ext i j
    exact Set.ext_iff.mp h (i, j))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSymmetrization
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetrization under the identical original bulk priors -/

namespace Ostmann

open scoped BigOperators Classical

def permuteBulk {I A : Type*} (e : Equiv.Perm I) (x : I → A) : I → A :=
  x ∘ e.symm

def bulkArrayEquiv {I A : Type*} (e : Equiv.Perm I) : (I → A) ≃ (I → A) where
  toFun := permuteBulk e
  invFun := permuteBulk e.symm
  left_inv x := by funext i; simp [permuteBulk]
  right_inv x := by funext i; simp [permuteBulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionMatching
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

def slotFiberEquiv {L C : Type*} (f : L → C) (m : ℕ) (c : C) :
    {x : L × Fin m // f x.1 = c} ≃ ({l : L // f l = c} × Fin m) where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadPartitionCounts
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform counting bound for paired leaf partitions -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def badPartitionCost (r m : ℕ) : ℝ :=
  (m.factorial : ℝ) ^ r * Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SymmetrizedPairBound
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair-correlation control of the symmetrized amplitude -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteFamilyAverage {J X : Type*} [Fintype J]
    (A : J → X → ℂ) (x : X) : ℂ :=
  (Fintype.card J : ℂ)⁻¹ * ∑ j, A j x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BackwardTargets
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards pivot-target recurrence

For coefficients `c_j = 2^j J + a_j - Delta_j`, the pivot target is `c_j`
plus the sum of all later pivot targets. This constructs the recurrence,
rather than assuming that its simultaneous equations have a solution.
-/

namespace Ostmann

def backwardTargets : List ℝ → List ℝ
  | [] => []
  | c :: cs => let ts := backwardTargets cs; (c + ts.sum) :: ts

theorem backwardTargets_length (cs : List ℝ) : (backwardTargets cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [backwardTargets, List.length_cons, ih]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotTargetScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive pivot targets at the required logarithmic scale -/

namespace Ostmann

def pivotCoefficients (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) : List ℝ :=
  List.ofFn (fun i => (2 : ℝ) ^ i.val * J + a i - Δ i)

def pivotTargets (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) : List ℝ :=
  backwardTargets (pivotCoefficients k J a Δ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetGaps
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed gaps are small compared with the top-prime scale -/

namespace Ostmann

open Filter

noncomputable def characterBaseGap (B z m : ℝ) : ℝ := (B + 20 * Real.log z) * m

/-- The index is zero based here; this is the manuscript's `Delta_(i+1)`. -/
noncomputable def characterPivotGap (B z m : ℝ) (i : ℕ) : ℝ :=
  (2 : ℝ) ^ i * characterBaseGap B z m + (4 : ℝ) ^ (i + 1) * Real.sqrt m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticGoodPatternRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full equality-pattern and frequency sums in the good-matching estimate -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The signed gain can be chosen before the local quartet tolerance. This
amount absorbs every original pattern and paired-frequency count. -/
def goodPatternGain (n : ℕ) (Cprior Cfreq gain : ℝ) : ℝ :=
  2 * (((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * Cprior +
    (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq + gain

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Defs
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

@[simp] theorem mem_primes {n : ℕ} : n ∈ primes ↔ Nat.Prime n := Iff.rfl

@[simp] theorem mem_sumset {A B : Set ℕ} {n : ℕ} :
    n ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = n := Set.mem_add

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- Residues of the negative of the other summand, with the same deletion. -/
def negTailResidues (B : Set ℕ) (N p : ℕ) : Set (ZMod p) :=
  (fun b : ℕ => -(b : ZMod p)) '' {b | b ∈ B ∧ N + p < b}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

/-- Logarithmic weight of the primes at which two natural numbers collide. -/
noncomputable def primeCollisionWeight (P : Finset ℕ) (a b : ℕ) : ℝ :=
  ∑ p ∈ P.filter (fun p => a ≡ b [MOD p]), Real.log (p : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetProducts
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

def primeSubsetProducts (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (P.powersetCard k).image fun Q => ∏ p ∈ Q, p

theorem primeSubset_product_squarefree (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) : Squarefree (∏ p ∈ Q, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hpq)
  · intro p hp
    exact (hQ p hp).squarefree

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HalfKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small divisor carrying half the prime factors of a squarefree kernel -/

namespace Ostmann

open scoped BigOperators

theorem exists_half_subset_product (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∃ U ⊆ P, U.card = P.card / 2 ∧ (∏ p ∈ U, p) ^ 2 ≤ ∏ p ∈ P, p := by
  classical
  let k := P.card / 2
  have hk : k ≤ P.card := Nat.div_le_self _ _
  obtain ⟨U₀, hU₀, hk₀⟩ := Finset.exists_subset_card_eq hk
  have hex : ∃ r : ℕ, ∃ U ⊆ P, U.card = k ∧ ∏ p ∈ U, p = r :=
    ⟨∏ p ∈ U₀, p, U₀, hU₀, hk₀, rfl⟩
  obtain ⟨U, hUP, hUk, hUr⟩ := Nat.find_spec hex
  have hcomp : k ≤ (P \ U).card := by
    rw [Finset.card_sdiff_of_subset hUP, hUk]
    dsimp [k]
    omega
  obtain ⟨V, hVP, hVk⟩ := Finset.exists_subset_card_eq hcomp
  have hmin : (∏ p ∈ U, p) ≤ ∏ p ∈ V, p := by
    rw [hUr]
    exact Nat.find_min' hex ⟨V, hVP.trans Finset.sdiff_subset, hVk, rfl⟩
  have hVPprod : (∏ p ∈ V, p) ≤ ∏ p ∈ P \ U, p := by
    exact Finset.prod_le_prod_of_subset_of_one_le hVP (fun _ _ => Nat.zero_le _)
      (fun p hp _ => hP p (Finset.mem_sdiff.mp hp).1)
  have hprod : (∏ p ∈ U, p) * (∏ p ∈ P \ U, p) = ∏ p ∈ P, p := by
    rw [mul_comm, Finset.prod_sdiff hUP]
  refine ⟨U, hUP, hUk, ?_⟩
  calc
    _ = (∏ p ∈ U, p) * (∏ p ∈ U, p) := pow_two _
    _ ≤ (∏ p ∈ U, p) * (∏ p ∈ P \ U, p) := Nat.mul_le_mul_left _ (hmin.trans hVPprod)
    _ = _ := hprod

theorem squarefree_half_kernel (s : ℕ) (hs : Squarefree s) :
    ∃ r : ℕ, Squarefree r ∧ r ∣ s ∧ r ^ 2 ≤ s ∧
      r.primeFactors.card = s.primeFactors.card / 2 := by
  classical
  obtain ⟨U, hU, hcard, hprod⟩ := exists_half_subset_product s.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1.one_lt.le)
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hU hp)).1
  have htotal := Nat.prod_primeFactors_of_squarefree hs
  refine ⟨∏ p ∈ U, p, primeSubset_product_squarefree U hprime, ?_, ?_, ?_⟩
  · refine ⟨∏ p ∈ s.primeFactors \ U, p, ?_⟩
    calc
      s = ∏ p ∈ s.primeFactors, p := htotal.symm
      _ = (∏ p ∈ U, p) * ∏ p ∈ s.primeFactors \ U, p := by
        rw [mul_comm, Finset.prod_sdiff hU]
  · rwa [htotal] at hprod
  · rw [Nat.primeFactors_prod hprime, hcard]

noncomputable def smallHalfKernel (s : ℕ) : ℕ := by
  classical
  exact if h : Squarefree s then Classical.choose (squarefree_half_kernel s h) else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCompactCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite cutoffs for compactly supported quadratic transforms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticCompactCutoff (q : ℕ) (R v C : ℝ) (N : ℕ) : Finset ℕ :=
  Finset.Ioc 0 ⌊Real.sqrt (C * R * q / ((N : ℝ) * v))⌋₊

noncomputable def positiveQuadraticSum {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑' w : ℕ, if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DyadicKernelShells
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite dyadic decomposition of the large squarefree kernels -/

namespace Ostmann

open scoped BigOperators

def dyadicKernelShell (s : ℕ) : ℕ := Nat.log 2 (s - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_IntegerKernelScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the real analytic scale to the manuscript's integer K -/

namespace Ostmann

open Filter

noncomputable def integerKernelScale (K : ℝ) : ℝ := K ^ (10000000 / 9999999 : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorWeightedCoefficient
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the squarefree divisors v in the original coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable def divisorWeightedCoefficient (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ) (s : ℕ) : ℂ :=
  ∑ V ∈ Q.powerset, (ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) * F V s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFrequencyExpansion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite reindexing by squarefree kernel and square part -/

namespace Ostmann

open scoped BigOperators

noncomputable def frequencyTriples (L U : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 U).product (L.divisors.product (Finset.Icc 1 U))).filter
    (fun z => Squarefree (z.1 * z.2.1) ∧ z.1.Coprime L ∧ z.1 * z.2.1 * z.2.2 ^ 2 ≤ U)

theorem mem_frequencyTriples {L U : ℕ} {z : ℕ × ℕ × ℕ} :
    z ∈ frequencyTriples L U ↔
      1 ≤ z.1 ∧ z.1 ≤ U ∧ z.2.1 ∈ L.divisors ∧ 1 ≤ z.2.2 ∧ z.2.2 ≤ U ∧
      Squarefree (z.1 * z.2.1) ∧ z.1.Coprime L ∧ z.1 * z.2.1 * z.2.2 ^ 2 ≤ U := by
  rcases z with ⟨s, v, w⟩
  simp only [frequencyTriples, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootNormalizedCoefficient
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact coefficient energy of the normalized squarefree array -/

namespace Ostmann

open scoped BigOperators

noncomputable def rootNormalizedCoefficient (F : ℕ → ℂ) (s : ℕ) : ℂ :=
  ((Real.sqrt (s : ℝ))⁻¹ : ℂ) * F s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMultiples
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact outer-divisor quadratic subseries -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def positiveQuadraticMultiples {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑' w : ℕ, if 0 < w then quadraticDensityTerm g a θ Φ R v s (P * w) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullQuadraticCoefficient
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both divisor sums in the original quadratic coefficient -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

/-- The v divisor is part of the original modular quadratic argument. -/
noncomputable def divisorQuadraticScalar
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (V U : Finset ℕ) : ZMod U.toList.prod :=
  a U * (V.toList.prod : ZMod U.toList.prod)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticQuadraticCoefficient
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependence of the original coefficient on finite arithmetic residues -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticInverseResidue (M : ℕ) (U : Finset ℕ) : ZMod U.toList.prod :=
  -(M : ZMod U.toList.prod)⁻¹

noncomputable def quadraticSymbolCoefficient (M : ℕ) (U : Finset ℕ) : ℂ :=
  ((1 / 16 : ℝ) ^ U.card : ℂ) * (realJacobi U.toList.prod M : ℂ)

noncomputable def quadraticDivisorSymbol (M : ℕ) (V : Finset ℕ) : ℂ :=
  (realJacobi V.toList.prod M : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCellMixtures
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reassembling log cells with the original normalization -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def bulkCellMixture {C : Type*} [Fintype C]
    (Z : ℝ) (μ : C → Measure ℝ) : Measure ℝ := ENNReal.ofReal Z • ∑ c, μ c

instance finite_bulkCellMixture {C : Type*} [Fintype C]
    (Z : ℝ) (μ : C → Measure ℝ) [∀ c, IsFiniteMeasure (μ c)] :
    IsFiniteMeasure (bulkCellMixture Z μ) := by
  unfold bulkCellMixture
  exact (∑ c, μ c).smul_finite ENNReal.ofReal_ne_top

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordStatistic
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial nonnegative word statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def wordStatisticTerm {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (a : ℤ) : ℝ :=
  (ψ ((a : ℝ) / X)).re * ‖G a‖ ^ 2 * ∏ i, ‖R i a‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTransfer
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving regular Fourier transform in the giant-only transfer -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Product of the actual local transforms, with their CRT cofactors. -/
noncomputable def movingRegularTransform {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (g : ∀ i, ZMod (p i) → ℂ) (D : ℕ) (s : ℤ) : ℂ :=
  ∏ i, g i ((s : ZMod (p i)) * ((D * tupleCofactor p i : ℕ) : ZMod (p i))⁻¹)

local instance sumElim_neZero {H K : Type*} (L : H → ℕ) (R : K → ℕ)
    [∀ i, NeZero (L i)] [∀ i, NeZero (R i)] (i : H ⊕ K) :
    NeZero (Sum.elim L R i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- Splitting the actual prime list extracts exactly the pivot row and
retains the old regular transform at the composite pivot denominator. -/
theorem moving_regular_transform_split {H K : Type*} [Fintype H] [Fintype K]
    (L : H → ℕ) (R : K → ℕ) [∀ i, NeZero (L i)] [∀ i, NeZero (R i)]
    (gL : ∀ i, ZMod (L i) → ℂ) (gR : ∀ i, ZMod (R i) → ℂ)
    (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim L R)
      (fun i => match i with | .inl j => gL j | .inr j => gR j) D s =
    movingRegularTransform L gL (D * ∏ i, R i) s *
      movingRegularTransform R gR (D * ∏ i, L i) s := by
  unfold movingRegularTransform
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_left L R i (NeZero.ne (L i))]
    simp only [mul_assoc, mul_comm]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_right L R i (NeZero.ne (R i))]
    simp only [mul_assoc]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def complexUnitPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem complexUnitPhase_zero : complexUnitPhase 0 = 0 := by
  simp [complexUnitPhase]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RepeatedCharacterCancellation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A singleton prime makes a short-period repeated tuple vanish -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def groupedSlotValue {I : Type*} [Fintype I] (P : Finset ℕ)
    (p : I → P) (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q)
    (t : ∀ q : ℕ, ZMod q) (q : P) (x : ZMod (q : ℕ)) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => p i = q), χ i q (x - t q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RepeatedPrimePeriod
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal products and the smaller period of a repeated prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def sampledPrimeSet {I : Type*} [Fintype I] (p : I → ℕ) : Finset ℕ :=
  Finset.univ.image p

noncomputable def primeSlotCount {I : Type*} [Fintype I] (p : I → ℕ) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => p i = q)).card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedTuplePoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original product bounds imply the short-period cancellation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def characterTupleSum {I : Type*} [Fintype I] (p : I → ℕ)
    (χ : I → ∀ q : ℕ, DirichletCharacter ℂ q) (t : ∀ q : ℕ, ZMod q)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' a : ℤ, (∏ i, χ i (p i) ((a : ZMod (p i)) - t (p i))) * ψ ((a : ℝ) / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedPhysicalTests
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated local tests with normalized probability energy -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def groupedPhysicalTest {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (q : P) (x : ZMod (q : ℕ)) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => p i = q), F i q x

/-- Grouping at each distinct prime preserves the original physical product,
including when a prime occurs in several different roles. -/
noncomputable def physicalTupleSum {I : Type*} [Fintype I]
    (P : Finset ℕ) (p : I → P) (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑' a : ℤ, (∏ i, F i (p i) (a : ZMod (p i : ℕ))) * ψ ((a : ℝ) / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AllMultipleTupleWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic square-root weight of tuples with no singleton -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def allMultipleTuples (A : Type*) [Fintype A] (n : ℕ) : Finset (Fin n → A) :=
  Finset.univ.filter (fun x => ∀ a ∈ Finset.univ.image x,
    2 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DoubledWordExpansion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent copies in the original word statistic -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap Classical

noncomputable def jointWordPrior {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (z : (Fin k → A) × (Fin m → A)) : ℝ := productPrior μ z.1 * productPrior ν z.2

noncomputable def jointWordAmplitude {A B : Type*} {k m : ℕ}
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B)
    (z : (Fin k → A) × (Fin m → A)) : ℂ :=
  if bin z.1 = b then (∏ i, F i (z.1 i)) * ∏ i, R i (z.2 i) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCopyCoordinates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two copies of every word and cell role as one ordered tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def wordCopyEquiv (A : Type*) (k m : ℕ) :
    (((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) ≃
      (Fin ((k + m) + (k + m)) → A) :=
  ((Fin.appendEquiv k m).prodCongr (Fin.appendEquiv k m)).trans
    (Fin.appendEquiv (k + m) (k + m))

noncomputable def wordCopyCharacter (k m : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) :
    Fin ((k + m) + (k + m)) → ∀ p : ℕ, DirichletCharacter ℂ p :=
  Fin.append (fun _ p => χ p) (fun _ p => (χ p)⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeStatistic
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent half-lists in the positive physical statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

noncomputable def halfPrimeMean {n : ℕ}
    (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) : ℂ :=
  ∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * ∏ i, F i (x i) (a : ZMod (x i : ℕ))

noncomputable def doubledHalfWeight {n : ℕ} {A : Type*}
    (w : (Fin n → A) → ℂ) (x : Fin (n + n) → A) : ℂ :=
  w (fun i => x (i.castAdd n)) * w (fun i => x (i.natAdd n))

noncomputable def halfPrimeBound {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ) (w : (Fin n → P) → ℂ) : ℝ :=
  ∑ x : Fin n → P, |productPrior μ x| * ‖w x‖ * ∏ i, ∑ b, ‖F i (x i) b‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeFactorization
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the giant mean from the positive nongiant scalar -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def halfPrimeScalar {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ) : ℝ :=
  ∑ x : Fin n → P, productPrior μ x * w x * ∏ i, c i (x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FiniteActionAverage
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging over the finite cycle action

These are the finite-sum projection identities used in the tree cycle
reduction. The action will be reciprocal multiplication on cycle leaves.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def actionPermutation {G Ω : Type*} [Group G] [MulAction G Ω] (g : G) : Ω ≃ Ω where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x

noncomputable def finiteActionAverage {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (x : Ω) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleAction
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal multiplication on cycle leaves

An integer sign on each leaf specifies multiplication by `z` or its inverse.
A block whose signs sum to zero has its product preserved by this action.
Thus a balanced cycle preserves both component totals and quartet totals.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def cycleMultiply {I G : Type*} [CommGroup G] (sign : I → ℤ) (z : G) (m : I → G) : I → G :=
  fun i => z ^ sign i * m i

@[instance_reducible] def leafCycleAction {I G : Type*} [CommGroup G] (sign : I → ℤ) : MulAction G (I → G) where
  smul := cycleMultiply sign
  one_smul m := by
    change cycleMultiply sign 1 m = m
    funext i
    change (1 : G) ^ sign i * m i = m i
    simp
  mul_smul z w m := by
    change cycleMultiply sign (z * w) m = cycleMultiply sign z (cycleMultiply sign w m)
    funext i
    change (z * w) ^ sign i * m i = z ^ sign i * (w ^ sign i * m i)
    rw [mul_zpow, mul_assoc]

noncomputable def cycleAverage {I G : Type*} [CommGroup G] [Fintype G]
    (sign : I → ℤ) (f : (I → G) → ℂ) (m : I → G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ z : G, f (cycleMultiply sign z m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleMellin
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Mellin constraint retained by cycle averaging

Reciprocal multiplication retains exactly the character tuples whose
signed product is principal. This is the relation used in the final
cycle-coefficient estimate.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance cycleMellinFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance cycleMellinDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ProductMellinParseval
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parseval for the independent moving coordinates on a cycle

The tensor products of unit characters form an orthogonal basis. This
finite identity makes the cycle projection energy a sum of products of
squared Mellin coefficients, with its exact probability normalization.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance productMellinFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance productMellinDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

noncomputable def productCharacter {p : ℕ} [Fact p.Prime] {I : Type*} [Fintype I]
    (ρ : I → MulChar (ZMod p) ℂ) (m : I → (ZMod p)ˣ) : ℂ := ∏ i, ρ i (m i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HeldCycleAverage
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent held-leaf averaging in the cycle projection -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance heldCycleFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance heldCycleDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetHorizontalMean
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the surviving characters after horizontal density domination -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance horizontalCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IncidenceCycle
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A cycle in the component--quartet incidence diagram

There is one edge per leaf. Parallel edges already give the two-edge
cycle used in the manuscript; otherwise the incidence graph is simple,
and at least as many edges as vertices force a cycle.
-/

namespace Ostmann

def incidenceGraph {L C Q : Type*} (component : L → C) (quartet : L → Q) :
    SimpleGraph (C ⊕ Q) where
  Adj x y := match x, y with
    | .inl c, .inr q => ∃ i, component i = c ∧ quartet i = q
    | .inr q, .inl c => ∃ i, component i = c ∧ quartet i = q
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact not_false⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IncidenceCirculation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A balanced leaf action from an incidence-graph cycle -/

namespace Ostmann

open scoped BigOperators

theorem incidenceDart_exists {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) :
    ∃ i : L,
      (d.fst = Sum.inl (component i) ∧ d.snd = Sum.inr (quartet i)) ∨
      (d.fst = Sum.inr (quartet i) ∧ d.snd = Sum.inl (component i)) := by
  rcases d with ⟨⟨x, y⟩, h⟩
  cases x with
  | inl c =>
    cases y with
    | inl c' => exact False.elim h
    | inr q =>
      obtain ⟨i, hc, hq⟩ := h
      exact ⟨i, Or.inl ⟨congrArg Sum.inl hc.symm, congrArg Sum.inr hq.symm⟩⟩
  | inr q =>
    cases y with
    | inr q' => exact False.elim h
    | inl c =>
      obtain ⟨i, hc, hq⟩ := h
      exact ⟨i, Or.inr ⟨congrArg Sum.inr hq.symm, congrArg Sum.inl hc.symm⟩⟩

noncomputable def incidenceDartLabel {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) : L :=
  Classical.choose (incidenceDart_exists component quartet d)

def incidenceDartSign {L C Q : Type*} {component : L → C} {quartet : L → Q}
    (d : (incidenceGraph component quartet).Dart) : ℤ :=
  match d.fst with
  | Sum.inl _ => 1
  | Sum.inr _ => -1

noncomputable def incidenceWalkSign {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (i : L) : ℤ :=
  (w.darts.map fun d => if incidenceDartLabel component quartet d = i then incidenceDartSign d else 0).sum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ParallelCycle
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-edge cycle

Two leaves in the same component and the same quartet give a balanced
sign vector supported on precisely those two leaves. No additional
assumption is needed for this degenerate cycle.
-/

namespace Ostmann

open scoped BigOperators

def parallelCycleSign {I : Type*} [DecidableEq I] (i j k : I) : ℤ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetConjugation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent opposite conjugations on the two bottom sibling pairs -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def pairConjugate {p : ℕ} (g : ZMod p → ℂ) (c : Bool) : ZMod p → ℂ :=
  if c then fun x => conj (g x) else g

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairCoefficientMeans
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small individual and bounded total means of pair coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance pairCoefficientMeansFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ConjugatedPairMeans
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same-pair bounds uniformly in the manuscript's conjugation choices -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance conjugatedPairMeansFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TwoBadFourier
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joining the four cases of the two-bad quartet sum

The nonprincipal part uses the fourth moment. The two cases with exactly
one principal twist use its total energy and the other twist's maximum.
The last case uses the principal maximum and a single energy bound.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance twoBadFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance twoBadDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSpectrumBound
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-bad quartet estimate in terms of its spectra

The hypotheses are the nonnegative spectrum bounds `src40`. This combines
the previously proved Gauss fourth moment with all principal corrections.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetSpectrumFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairFourierMass
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete Fourier mass bounds needed in the cross-pair application -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance pairFourierMassFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ConcreteQuartetFourier
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet Fourier estimate with the actual autocorrelation spectra -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance concreteQuartetFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def twoBadQuartetError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := p / U
  (2 * (U / p) * (C ^ 2 * ε ^ 2) * (2 * C) + 3 * (U / (p : ℝ) ^ 2) * C ^ 4) +
    2 * ((p : ℝ)⁻¹ * C ^ 2) * (2 * C) +
      (C * ε ^ 2 + (p : ℝ)⁻¹ * C) ^ 2 * (C ^ 2 * ε ^ 2)

noncomputable def friendlyQuartetError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
    (ε ^ 4 + Real.sqrt (3 / (p : ℝ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTestSymmetries
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflection and conjugation preserve the hypotheses for every local row -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance quartetTestSymmetriesFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetLocalBounds
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six possible moving-leaf pairs and their uniform local estimates -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetLocalBoundsFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetLocalMeanError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 +
    16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 *
      (friendlyQuartetError p ε + twoBadQuartetError p ε)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductProjection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cycle projection of a product of actual quartet states -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetProjectionCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance quartetProjectionCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProjectedCut
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional projected norm bound on the actual tree cut -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance projectedCutCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance projectedCutCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCutAverages
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected cut bounds with invalid ancestors included -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance cutAverageCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance cutAverageCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FiberProjection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correlation over paired finite fibers

The component totals determine equal-cardinality fibers. Cauchy--Schwarz
on their sums, together with invariance under a cycle action, gives the
finite projection reduction before the local quartet bounds are applied.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def fiberSum {Ω T : Type*} [Fintype Ω] [DecidableEq T]
    (τ : Ω → T) (f : Ω → ℂ) (t : T) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x => τ x = t), f x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairedRationalReduction
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cycle projection for two actual rational diagrams -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def pairedPartitionCorrelation {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C) (f g : (L → G) → ℂ) : ℂ :=
  ((Fintype.card (L → G) : ℂ) *
      (Fintype.card G ^ (Fintype.card L - Fintype.card C) : ℕ))⁻¹ *
    ∑ x : L → G, ∑ y : L → G,
      if partitionProduct component₁ x = partitionProduct component₂ y
      then f x * conj (g y) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTreeSmallParameters
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform small parameters for the actual quartet tree error -/

namespace Ostmann

noncomputable def quartetTreeConstant (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 ^ (n + 2)) * (2 : ℝ) ^ (2 ^ n - 1) * 16384 *
    (128 : ℝ) ^ (2 ^ n - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalRegularMultiplier
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual squared regular transform in the diagonal CRT average -/

namespace Ostmann
open scoped BigOperators Classical

/-- `other i` is the fixed denominator consisting of the outside and all
small slots other than the regular prime `i`. The two giants are retained. -/
noncomputable def diagonalRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool)
    (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ) : ℝ :=
  if ∀ i, (z i).1 ≠ 0 then
    ∏ i, if active i then
      ‖g i ((s : ZMod (p i)) / (other i * (z i).1 * ((z i).2 : ZMod (p i))))‖ ^ 2 else 1
  else 0

noncomputable def diagonalRegularCoefficient {I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (s : ℤ) (other : ∀ i, ZMod (p i)) (hs : ∀ i, (s : ZMod (p i)) ≠ 0)
    (ho : ∀ i, other i ≠ 0) (i : I) : (ZMod (p i))ˣ :=
  Units.mk0 ((s : ZMod (p i)) / other i) (div_ne_zero (hs i) (ho i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularGiantMultiplier
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The displayed regular-prime multiplier on actual natural giants -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def naturalRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) : ℝ :=
  ∏ i, if active i then
    ‖g i ((s : ZMod (p i)) / (other i * (XL : ZMod (p i)) * (XR : ZMod (p i))))‖ ^ 2 else 1

noncomputable def guardedRegularMultiplier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) : ℝ :=
  if ∀ i, (XL : ZMod (p i)) ≠ 0 ∧ (XR : ZMod (p i)) ≠ 0 then
    naturalRegularMultiplier p active s other g XL XR else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def giantOuterScalar (diagonal : Bool) : ℝ := if diagonal then Real.exp 1 else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExternalResidueReduction
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing redundant prime powers from uniform giant residue averages -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def externalResidueReduction {m n : ℕ} (h : m ∣ n)
    (z : ZMod n × (ZMod n)ˣ) : ZMod m × (ZMod m)ˣ :=
  ((ZMod.castHom h (ZMod m)) z.1, ZMod.unitsMap h z.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantDiscreteTransport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport of the literal reciprocal-prime and integer sums -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

noncomputable def primeResidueAtom (q a p : ℕ) : ℝ :=
  if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ResidueIntervals
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue decompositions of the original giant sums -/

namespace Ostmann
open scoped BigOperators Classical

def reducedResidues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => a.Coprime q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NaturalResidueAverage
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural residue representatives and the Haar unit averages used by CRT -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def unitReducedResidueEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {a : ℕ // a ∈ reducedResidues q} where
  toFun u := ⟨(u : ZMod q).val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩⟩
  invFun a := ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2
  left_inv u := Units.ext (ZMod.natCast_zmod_val _)
  right_inv a := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RestrictedGiantDensity
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded densities on the common real giant rectangle -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def restrictedIntegerGiantDensity (q : ℕ) (J u v : ℝ) : ℝ → ℂ :=
  (Set.Ioc u v).indicator (fun x => (integerLogDensity q J x : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ConductorDeletion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor support after deleting one large prime

For each exceptional conductor choose one prime divisor above the threshold,
if there is one, and exclude that value from the nongiant priors. A conductor
that still divides the arithmetic modulus is then supported on its frequency
block, with full prime-power multiplicity.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def deletedConductorPrime (D T : ℕ) : Option ℕ :=
  if h : ∃ p, p.Prime ∧ p ∣ D ∧ T ≤ p then some h.choose else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResidueCRT
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bulk residue separation, with Page terms in the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

/-- The only moduli remaining after the internal line comparison. -/
def bulkResidueModuli {I : Type*} (r : ℕ) (p : I → ℕ) : Unit ⊕ I → ℕ
  | .inl _ => r
  | .inr i => p i

def bulkResidueAssemble {I : Type*} (r : ℕ) (p : I → ℕ)
    (f : (ZMod r)ˣ) (g : ∀ i, (ZMod (p i))ˣ) :
    ∀ i, (ZMod (bulkResidueModuli r p i))ˣ
  | .inl _ => f
  | .inr i => g i

/-- Simultaneous CRT on all bulk slots, transposed into one frequency block
and one block for each spectator. -/
noncomputable def bulkResidueEquiv {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j))) :
    (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) ≃
      (J → (ZMod r)ˣ) × (∀ i, J → (ZMod (p i))ˣ) where
  toFun x := (fun j => crtUnitEquiv (bulkResidueModuli r p) hc (x j) (.inl ()),
    fun i j => crtUnitEquiv (bulkResidueModuli r p) hc (x j) (.inr i))
  invFun z j := (crtUnitEquiv (bulkResidueModuli r p) hc).symm
    (bulkResidueAssemble r p (z.1 j) (fun i => z.2 i j))
  left_inv x := by
    funext j
    apply (crtUnitEquiv (bulkResidueModuli r p) hc).injective
    rw [MulEquiv.apply_symm_apply]
    funext i
    rcases i with u | i
    · cases u; rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext j
      exact congrFun ((crtUnitEquiv (bulkResidueModuli r p) hc).apply_symm_apply _) (.inl ())
    · funext i j
      exact congrFun ((crtUnitEquiv (bulkResidueModuli r p) hc).apply_symm_apply _) (.inr i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteProductPrior {K A : Type*} [Fintype K]
    (μ : K → A → ℝ) (x : K → A) : ℝ := ∏ i, μ i (x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantPrior
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact smooth harmonic giant prior from (7.3) -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantMass (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : ℝ :=
  ∑ p ∈ P, φ (Real.log p - G) / p

noncomputable def smoothGiantLogNormalizer (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : ℝ :=
  -Real.log (smoothGiantMass P φ G)

noncomputable def smoothGiantPrior (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) (p : P) : ℝ :=
  Real.exp (smoothGiantLogNormalizer P φ G) * φ (Real.log p - G) / p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantIntegerRange (G : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌈Real.exp (G + 1)⌉₊

noncomputable def smoothGiantPrimeRange (G : ℝ) : Finset ℕ :=
  (smoothGiantIntegerRange G).filter Nat.Prime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothLogCellProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth partition profile for the original logarithmic cells -/

namespace Ostmann
open Filter
open scoped Classical

noncomputable def logCellCentralLower : ℝ :=
  min (Real.smoothTransition (1 / 2)) (1 - Real.smoothTransition (1 / 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic cutoff weights in the initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def balancedTupleSet {A : Type*} [Fintype A] (n : ℕ)
    (good : Fin n → A → Prop) : Finset (Fin n → A) :=
  Finset.univ.filter (fun x => ∀ i, good i (x i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogWeightedKernelPairComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint prime comparison retaining the initial bulk logarithmic cutoffs -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkLogWeightedKernelPairBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e t rlog : ℕ) (B D Dlog : ℝ) : ℝ :=
  ((2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
      ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r))) + t * rlog + 1 : ℕ) : ℝ) *
    ((movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
      (2 + Dlog * (Real.exp 2 - 1)) ^ t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TupleFrequencyCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite frequency support of the initial tuple amplitude -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def tupleFrequencies {I : Type*} [Fintype I] (p : I → ℕ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun v => v ≠ 0 ∧ ∀ i, IsUnit (v : ZMod (p i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledTupleAmplitude
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph amplitude of an injective prime sample -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def sampledTupleAmplitude {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : I → P) : ℂ :=
  let : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  ∑ v ∈ tupleFrequencies (fun i => (x i : ℕ)) N,
    (Real.sqrt (X / (∏ i, (x i : ℕ))) : ℂ) *
      𝓕 ψ ((v : ℝ) * X / (∏ i, (x i : ℕ))) *
      tupleGraphPhase (fun i => (x i : ℕ)) (fun i => χ i (x i)) (fun i => t (x i)) v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeTupleResidueRow
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual harmonic-prior pivot row -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeTupleResidueRow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (t : ∀ p : ℕ, ZMod p) (Y : ℕ) (ε : Fin n → ℤ)
    (x : Fin n → P) (u : Fin (∏ i, (x i : ℕ))) : ℂ := by
  letI : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP (x i) (x i).property⟩
  exact groupedResidueRow (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => κ i (x i)) (fun i => t (x i)) Y ε u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructedPhaseWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The forced-pivot off-diagonal is the actual next directed amplitude -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def retainedWeightedCoefficient {A H Y : Type*} [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (M : ℕ) (a : A) : ℂ :=
  W M a * retainedPrimePhase (L a) U t χH χY b (ν a) (νY a) M (v a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInitialAmplitude
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual guarded amplitude at depth zero in original prime coordinates -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def sampledTuplePhase {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (center : ∀ p : ℕ, ZMod p) (v : ℤ) (x : I → P) : ℂ := by
  letI : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  exact tupleGraphPhase (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => center (x i)) v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGaussMultipliers
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bounded Gauss multipliers for every original prime role -/

namespace Ostmann
open scoped Classical

noncomputable def primeGaussMultiplier (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) : ℂ :=
  if hp : p.Prime ∧ χ p ≠ 1 then
    @primitiveGaussPhase p ⟨hp.1.ne_zero⟩ (χ p) else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueDecomposition
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue-class splitting before the inverse quadratic estimate -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticResidueAmplitude {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v : ℕ) (r : ZMod q) : ℂ :=
  g (a * r ^ 2 * (s : ZMod q)) * ZMod.stdAddChar (((h₀ * s * v : ℕ) : ZMod q) * r ^ 2)

noncomputable def quadraticResidueWave {q : ℕ} (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (s v w : ℕ) : ℂ :=
  realAdditivePhase (θ * s * v * (w : ℝ) ^ 2 / q) *
    Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyTerm
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency summand and its exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticFrequencyTerm {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (u : ℕ) : ℂ :=
  g (a * (u : ZMod q)) * realAdditivePhase (θ * u / q) * Φ ((u : ℝ) / (R * q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SignedQuadraticFrequency
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

noncomputable def integerQuadraticFrequency {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M : ℕ) (u : ℤ) : ℂ :=
  (jacobiSym u M : ℂ) * g (a * (u : ZMod q)) *
    realAdditivePhase (θ * (u : ℝ) / q) * Φ ((u : ℝ) / (R * q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveFourierCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

noncomputable def narrowBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 200, 1 / 100, by norm_num, by norm_num⟩

noncomputable def narrowSchwartz : 𝓢(ℝ, ℂ) :=
  (narrowBump.hasCompactSupport.toSchwartzMap narrowBump.contDiff).postcompCLM Complex.ofRealCLM

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteRootFibres
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the root frequency in the final counting measure -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def rootFibreSum {D R : Type*} [Fintype D]
    (root : D → R) (s : R) (F : D → ℂ) : ℂ :=
  ∑ d, if root d = s then F d else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteSeparatedHeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A unit interval contains a quantitatively separated height -/

namespace Ostmann

open Set MeasureTheory
open scoped BigOperators

/-- Avoid a finite set of ordinates while retaining a definite distance.
The proof pays only for the total lengths of the forbidden intervals. -/
theorem exists_height_separated (S : Finset ℝ) (T δ : ℝ) (_hδ : 0 < δ)
    (hsize : 2 * δ * (S.card : ℝ) < 1) :
    ∃ t ∈ Ioo T (T + 1), ∀ r ∈ S, δ ≤ |t - r| := by
  classical
  let U : Set ℝ := ⋃ r ∈ S, Ioo (r - δ) (r + δ)
  have hvol : volume U ≤ ENNReal.ofReal (2 * δ * (S.card : ℝ)) := by
    calc
      _ ≤ ∑ r ∈ S, volume (Ioo (r - δ) (r + δ)) := measure_biUnion_finset_le _ _
      _ = ∑ _r ∈ S, ENNReal.ofReal (2 * δ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Real.volume_Ioo]
        congr 1
        ring
      _ = ENNReal.ofReal (2 * δ * (S.card : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul, mul_comm]
  have hnot : ¬Ioo T (T + 1) ⊆ U := by
    intro h
    have hv := (measure_mono h).trans hvol
    rw [Real.volume_Ioo, add_sub_cancel_left] at hv
    norm_num at hv
    exact (not_lt_of_ge hv) hsize
  obtain ⟨t, ht, htu⟩ := Set.not_subset.mp hnot
  refine ⟨t, ht, ?_⟩
  intro r hr
  by_contra hd
  have hd' := abs_lt.mp (lt_of_not_ge hd)
  apply htu
  exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, by constructor <;> linarith⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSupportedArithmetic
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkIndexPredicate {σ J : Type*} (slot : J ↪ σ) (i : σ) : Bool :=
  decide (i ∈ Set.range slot)

@[simp] theorem bulkIndexPredicate_eq_true {σ J : Type*} (slot : J ↪ σ) (i : σ) :
    bulkIndexPredicate slot i = true ↔ i ∈ Set.range slot := by
  simp only [bulkIndexPredicate, decide_eq_true_eq]

@[simp] theorem bulkIndexPredicate_eq_false {σ J : Type*} (slot : J ↪ σ) (i : σ) :
    bulkIndexPredicate slot i = false ↔ i ∉ Set.range slot := by
  simp only [bulkIndexPredicate, decide_eq_false_iff_not]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalPatternSum
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original pattern weights and their exact zero extension -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternInjectionGuard {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) : ℂ :=
  if Function.Injective (fun c => x (e.symm (.inr c))) then G x else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGapRanges
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's gaps give both frequency cutoffs and history rigidity -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def transferErrorScale (Δ m : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * Δ + 2 * (4 : ℝ) ^ j * Real.sqrt m

/-- The gap for step j+1. -/
noncomputable def transferNextGap (Δ m : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * Δ + (4 : ℝ) ^ (j + 1) * Real.sqrt m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferRoundedCutoffs
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural cutoffs supplied by the transfer's exponential ranges -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def naturalTransferCutoff (Δ m : ℝ) (j : ℕ) : ℕ :=
  ⌊Real.exp (transferErrorScale Δ m j)⌋₊

noncomputable def naturalProductCap (T : ℝ) : ℕ := ⌊Real.exp T⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedPrimeFubini
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bulk and nonbulk decomposition of the original finite prime law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedIndexEquiv {σ J : Type*} (slot : J ↪ σ) :
    J ⊕ {i : σ // i ∉ Set.range slot} ≃ σ :=
  (Equiv.sumCongr (Equiv.ofInjective slot slot.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range slot))

@[simp] theorem selectedIndexEquiv_inl {σ J : Type*} (slot : J ↪ σ) (j : J) :
    selectedIndexEquiv slot (.inl j) = slot j := rfl

@[simp] theorem selectedIndexEquiv_inr {σ J : Type*} (slot : J ↪ σ)
    (i : {i : σ // i ∉ Set.range slot}) : selectedIndexEquiv slot (.inr i) = i := rfl

noncomputable def joinBulkNonbulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A) : σ → A :=
  Sum.elim bulk nonbulk ∘ (selectedIndexEquiv slot).symm

@[simp] theorem joinBulkNonbulk_bulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A) (j : J) :
    joinBulkNonbulk slot bulk nonbulk (slot j) = bulk j := by
  change Sum.elim bulk nonbulk ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inl j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem joinBulkNonbulk_nonbulk {σ J A : Type*} (slot : J ↪ σ)
    (bulk : J → A) (nonbulk : {i : σ // i ∉ Set.range slot} → A)
    (i : {i : σ // i ∉ Set.range slot}) : joinBulkNonbulk slot bulk nonbulk i = nonbulk i := by
  change Sum.elim bulk nonbulk ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFubini
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed bulk sum under the actual compensated pattern law -/

namespace Ostmann
open scoped Classical BigOperators

def movingPatternExternalLaw {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ) : Fin (N + 1) → A → ℝ :=
  fun i => Sum.elim ν (fun _ _ => 1) (e i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real bulk coordinates evaluate to the original pattern primes -/

namespace Ostmann
open scoped Classical

noncomputable def selectedBulkSet {σ J : Type*} [Fintype σ] (slot : J ↪ σ) : Finset σ :=
  Finset.univ.filter (fun i => i ∈ Set.range slot)

@[simp] theorem mem_selectedBulkSet {σ J : Type*} [Fintype σ] (slot : J ↪ σ) (i : σ) :
    i ∈ selectedBulkSet slot ↔ i ∈ Set.range slot := by
  simp only [selectedBulkSet, Finset.mem_filter, Finset.mem_univ, true_and]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeBulkInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

noncomputable def primeBulkValues {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) : σ → ℕ :=
  Function.extend slot (fun j => (x j : ℕ)) base

@[simp] theorem primeBulkValues_at {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (j : J) :
    primeBulkValues base slot x (slot j) = (x j : ℕ) := slot.injective.extend_apply _ _ j

theorem primeBulkValues_off {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (i : σ) (hi : i ∉ Set.range slot) :
    primeBulkValues base slot x i = base i := Function.extend_apply' _ _ i hi

theorem primeBulkValues_prime {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P)
    (hP : ∀ p ∈ P, p.Prime) (hbase : ∀ i ∉ Set.range slot, (base i).Prime) :
    ∀ i, (primeBulkValues base slot x i).Prime := by
  intro i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    rw [primeBulkValues_at]
    exact hP _ (x j).property
  · rw [primeBulkValues_off base slot x i hi]
    exact hbase i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def bulkProgressionCutoff (L : ℝ) : ℕ :=
  ⌊Real.exp (Real.exp ((12 / 10000 : ℝ) * L))⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeSupport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete prime support of a nonzero original pattern coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternInternalPrimes {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (x : Fin (N + 1) → A) : Finset ℕ :=
  Finset.univ.image (fun c : C => prime (x (e.symm (.inr c))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternRegularUnits
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual regular Fourier denominators are units on the original support -/

namespace Ostmann
open scoped Classical BigOperators

/-- The denominator left after removing one regular prime and both giants. -/
noncomputable def movingRegularOther {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (slots : List σ) (j : Fin slots.length) : ℤ :=
  (outside.prod * ∏ i ∈ Finset.univ.erase j, value (slots.get i) : ℕ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularDiagonal
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common Fourier multiplier on equal-product diagonal fibres -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The cofactor formula written in terms of the integer product, so that
the order of the current prime list is absent. -/
noncomputable def primeProductTransform (g : ∀ p : ℕ, ZMod p → ℂ)
    (D H : ℕ) (s : ℤ) : ℂ :=
  ∏ p ∈ H.primeFactors, g p ((s : ZMod p) * ((D * (H / p) : ℕ) : ZMod p)⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkPermutation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting only the selected bulk coordinates in the original law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedBulkPerm {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) : Equiv.Perm B :=
  (selectedIndexEquiv slot).symm.trans
    ((e.sumCongr (Equiv.refl _)).trans (selectedIndexEquiv slot))

@[simp] theorem selectedBulkPerm_bulk {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (j : J) : selectedBulkPerm slot e (slot j) = slot (e j) := by
  change selectedIndexEquiv slot ((e.sumCongr (Equiv.refl _))
    ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inl j)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem selectedBulkPerm_nonbulk {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (i : B) (hi : i ∉ Set.range slot) :
    selectedBulkPerm slot e i = i := by
  change selectedIndexEquiv slot ((e.sumCongr (Equiv.refl _))
    ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inr ⟨i, hi⟩)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem selectedBulkPerm_symm {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) : (selectedBulkPerm slot e).symm = selectedBulkPerm slot e.symm := by
  ext i
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j <;> simp [selectedBulkPerm]

@[simp] theorem selectedBulkPerm_one {B J : Type*} (slot : J ↪ B) :
    selectedBulkPerm slot 1 = 1 := by
  ext i
  simp [selectedBulkPerm]

@[simp] theorem selectedBulkPerm_mul {B J : Type*} (slot : J ↪ B)
    (e f : Equiv.Perm J) : selectedBulkPerm slot (e * f) =
      selectedBulkPerm slot e * selectedBulkPerm slot f := by
  ext i
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j <;> simp [selectedBulkPerm, Equiv.Perm.mul_apply]

noncomputable def selectedBulkSample {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) : B → A := y ∘ (selectedBulkPerm slot e).symm

@[simp] theorem selectedBulkSample_bulk {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) (j : J) :
    selectedBulkSample slot e y (slot j) = y (slot (e.symm j)) := by
  simp [selectedBulkSample]

@[simp] theorem selectedBulkSample_nonbulk {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) (i : B) (hi : i ∉ Set.range slot) :
    selectedBulkSample slot e y i = y i := by
  simp [selectedBulkSample, hi]

@[simp] theorem selectedBulkSample_one {B J A : Type*} (slot : J ↪ B) (y : B → A) :
    selectedBulkSample slot 1 y = y := by
  simp only [selectedBulkSample, selectedBulkPerm_one]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementReindex
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting actual overlap graphs along a leaf enumeration -/

namespace Ostmann

noncomputable def reindexArrangement {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) : Equiv.Perm (L' × Fin m) :=
  ((f.symm.prodCongr (Equiv.refl _)).trans e).trans (f.prodCongr (Equiv.refl _))

@[simp] theorem reindexArrangement_eq_iff {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (a b : L) (i j : Fin m) :
    reindexArrangement f e (f a, i) = (f b, j) ↔ e (a, i) = (b, j) := by
  change (f.prodCongr (Equiv.refl _)) (e (f.symm (f a), i)) =
    (f.prodCongr (Equiv.refl _)) (b, j) ↔ _
  rw [f.symm_apply_apply, Equiv.apply_eq_iff_eq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original giant Fourier phases on a fixed product fibre -/

namespace Ostmann
open scoped Classical BigOperators

/-- The two cofactor phases before inserting the logarithmic coordinates. -/
noncomputable def giantPairPhase (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D H XL XR : ℕ) (s : ℤ) : ℂ :=
  (if favorable XL then complexUnitPhase
    (g XL ((s : ZMod XL) * ((D * XR * H : ℕ) : ZMod XL)⁻¹)) else 0) *
  (if favorable XR then complexUnitPhase
    (g XR ((s : ZMod XR) * ((D * XL * H : ℕ) : ZMod XR)⁻¹)) else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantCoprimeIntervals
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top coprimality error on the literal giant interval laws -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def giantPrimes (u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊).filter Nat.Prime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExternalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the integer/prime comparison law to two prime giants -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def leftPrimeDensity (u x : ℝ) : ℝ :=
  if (⌊Real.exp x⌋₊).Prime ∧ Real.exp u ≤ (⌊Real.exp x⌋₊ : ℝ)
  then Real.exp u / (⌊Real.exp x⌋₊ : ℝ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeNodeFactor
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual top node factor before summing descendant histories -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original nine arithmetic tests at a node, in terms of its products. -/
def movingNodeArithmeticGuard (N B LH RH : ℕ) (s v w : ℤ) (P : ℕ) : Prop :=
  s ≠ 0 ∧ IsCoprime s (RH : ℤ) ∧ v * RH - w * LH = s * P ∧
    0 < P ∧ P ≤ B ∧ v.natAbs ≤ N ∧ w.natAbs ≤ N ∧
    2 * B * N < RH ∧ P.Coprime w.natAbs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantTransformProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the two giant phases with the common regular transform -/

namespace Ostmann
open scoped Classical BigOperators

local instance giantProductSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal regular template and its full Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

local instance templateSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full Fourier transform in the actual transfer slot order -/

namespace Ostmann
open scoped Classical BigOperators

/-- A common formula for regular factors and the two marked giant phases.
Using the modulus as an explicit argument makes reindexing independent of
presentation of the dependent residue types. -/
noncomputable def movingTaggedTransform {I : Type*} [Fintype I]
    (p : I → ℕ) (giant : I → Bool)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) : ℂ :=
  ∏ i, (if giant i then
      (fun t => if favorable (p i) then complexUnitPhase (ggiant (p i) t) else 0)
    else greg (p i))
      ((s : ZMod (p i)) * ((D * tupleCofactor p i : ℕ) : ZMod (p i))⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSumFactors
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A shared dependent Fourier family for disjoint prime lists -/

namespace Ostmann

/-- The dependent disjoint union of two families, with its motive explicit. -/
def movingSumFactors {J I : Type*} (Q : J → ℕ) (L : I → ℕ)
    (gQ : ∀ j, ZMod (Q j) → ℂ) (gL : ∀ i, ZMod (L i) → ℂ) :
    ∀ i, ZMod (Sum.elim Q L i) → ℂ :=
  Sum.rec (motive := fun i => ZMod (Sum.elim Q L i) → ℂ) gQ gL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOneGiant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One surviving giant and its actual regular Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance oneGiantSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

def movingOneGiantModuli {I : Type*} (X : ℕ) (p : I → ℕ) : Unit ⊕ I → ℕ :=
  Sum.elim (fun _ => X) p

instance movingOneGiantModuli_prime {I : Type*} (X : ℕ) (p : I → ℕ)
    [Fact X.Prime] [∀ i, Fact (p i).Prime] (i : Unit ⊕ I) :
    Fact (movingOneGiantModuli X p i).Prime := by
  cases i <;> dsimp only [movingOneGiantModuli, Sum.elim] <;> infer_instance

instance movingOneGiantModuli_neZero {I : Type*} (X : ℕ) (p : I → ℕ)
    [NeZero X] [∀ i, NeZero (p i)] (i : Unit ⊕ I) :
    NeZero (movingOneGiantModuli X p i) := by
  cases i <;> dsimp only [movingOneGiantModuli, Sum.elim] <;> infer_instance

noncomputable def movingOneGiantFactors {I : Type*} (X : ℕ) (p : I → ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    ∀ i, ZMod (movingOneGiantModuli X p i) → ℂ
  | .inl _ => fun t => if favorable X then complexUnitPhase (ggiant X t) else 0
  | .inr i => greg (p i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGuardedRow
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The extracted row with the original support indicators -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingGuardedRow {J : Type*} [Fintype J]
    (q : J → ℕ) (g : ∀ j, ZMod (q j) → ℂ) (D : ℕ) {M : ℕ} (t : Fin M) : ℂ :=
  if Pairwise (fun i j => (q i).Coprime (q j)) ∧ (∀ j, D.Coprime (q j)) then
    ∏ j, g j ((t.val : ZMod (q j)) * ((D * tupleCofactor q j : ℕ) : ZMod (q j))⁻¹)
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularOffDiagonal
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted off-diagonal with its actual surviving Fourier transform -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingRegularCoefficient {A H : Type*} [Fintype H]
    (L : A → H → ℕ) [∀ a i, NeZero (L a i)]
    (g : ∀ a i, ZMod (L a i) → ℂ) (D U : ℕ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (p : ℕ) (a : A) : ℂ :=
  W p a * movingRegularTransform (L a) (g a) (p * U * D) (v a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullTransformTransfer
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original full Fourier amplitude through one giant-only step -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance fullTransferSum_neZero {J H : Type*} (Q : J → ℕ) (L : H → ℕ)
    [∀ j, NeZero (Q j)] [∀ i, NeZero (L i)] (i : J ⊕ H) :
    NeZero (Sum.elim Q L i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual diagonal and integer off-diagonal of a prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance amplitudeSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBadHarmonicBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bad-arrangement saving in the complete diagonal normalization -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def movingNonbulkCost (n s : ℕ) : ℝ :=
  (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
    (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompactLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact leaf multipliers preserve the scheduled statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The zero frequency is removed and all live bottom frequencies are retained. -/
noncomputable def movingCompactLeaf (V : ℕ) (s : ℤ) : ℂ :=
  if s.natAbs ≤ V then if s = 0 then 0 else 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalGapBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal exponent and the parameter order in (7.1), (9.6)–(9.8) -/

namespace Ostmann

noncomputable def spectatorBaseGap (Bs z m : ℝ) : ℝ := (Bs + 8 * Real.log z) * m

noncomputable def spectatorStepGap (BD Bz z r m : ℝ) : ℝ :=
  r * (BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log r) * m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual accumulated gaps and rounded frequency cutoffs of Section 7 -/

namespace Ostmann
open scoped BigOperators

/-- The square-root reserve agrees with the proved bottom cutoff at `4m`. -/
noncomputable def movingCutoffExponent (Bs BD Bz z m : ℝ) (n : ℕ) : ℝ :=
  spectatorBaseGap Bs z m +
    ∑ j ∈ Finset.range n, spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m +
      (2 : ℝ) ^ n * Real.sqrt (4 * m)

noncomputable def movingNaturalCutoff (Bs BD Bz z m : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (movingCutoffExponent Bs BD Bz z m n)⌋₊

/-- One unit of reserve is left for the root-frequency count. -/
noncomputable def movingFrequencyRate (Bs BD Bz z : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (Bs + 8 * Real.log z + BD + Bz * Real.log z +
    (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ n) + 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationTargets
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards compensation-center construction of equation (7.4) -/

namespace Ostmann

/-- The entries are ordered from the first removed type to the last. -/
noncomputable def movingCompensationTargets (J : ℝ) : List ℝ → List ℝ
  | [] => []
  | d :: ds =>
    let rest := movingCompensationTargets J ds
    (J + rest.sum - d) :: rest

noncomputable def movingCompensationTargetError : List ℝ → ℝ
  | [] => 0
  | d :: ds => 2 * movingCompensationTargetError ds + d

@[simp] theorem movingCompensationTargets_length (J : ℝ) (ds : List ℝ) :
    (movingCompensationTargets J ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [movingCompensationTargets, List.length_cons, ih]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationGapList
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed normalized gaps in the backwards target recursion -/

namespace Ostmann
open Filter

noncomputable def movingCompensationGaps (k : ℕ) (BD Bz L : ℝ) : List ℝ :=
  List.ofFn (fun i : Fin k =>
    spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L) /
      (2 : ℝ) ^ (i : ℕ))

noncomputable def movingCompensationGapRate (k : ℕ) (BD Bz : ℝ) : ℝ :=
  (BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * k * Real.log 2) * (k : ℝ) ^ 4

@[simp] theorem movingCompensationGaps_length (k : ℕ) (BD Bz L : ℝ) :
    (movingCompensationGaps k BD Bz L).length = k := by simp [movingCompensationGaps]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalOuterWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def inactiveRegularDensity {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (x : σ → A) : ℝ :=
  ∏ j, if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹

noncomputable def diagonalOuterMajorant (B D : ℝ) (diagonal : Bool) : ℝ :=
  1 + giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
    (if diagonal then 1 + Real.exp 2 else 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularLiveOffDiagonal
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transfer only tests live retained primes -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveCopiedSum_neZero {H K : Type*} (L : H → ℕ) (R : K → ℕ)
    [∀ i, NeZero (L i)] [∀ i, NeZero (R i)] (i : H ⊕ K) :
    NeZero (Sum.elim L R i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullLiveTransformTransfer
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveFullTransferSum_neZero {J H : Type*} (Q : J → ℕ) (L : H → ℕ)
    [∀ j, NeZero (Q j)] [∀ i, NeZero (L i)] (i : J ⊕ H) :
    NeZero (Sum.elim Q L i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalErrorRate
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual internal arithmetic error at the source's prime scales -/

namespace Ostmann
open Filter

noncomputable def movingInternalArithmeticError (n c d : ℕ) (F U α β V : ℝ) : ℝ :=
  ((2 * (2 ^ n - 1 : ℕ)) * c * Real.exp (-V)) +
    2 * ((c * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
      ((2 * ((n + 1) * d) : ℕ) * α +
        (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterJointComparison
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport with the literal outer priors and diagonal reciprocal -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

noncomputable def movingOuterVariationBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ) (n : ℕ)
    (B D : ℝ) (diagonal : Bool) : ℝ :=
  (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
    ((2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternModulusRange
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full pattern modulus and the separate giant progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The giant comparison includes internal prime squares; the external bulk
comparison keeps `bulkProgressionCutoff L`. -/
noncomputable def giantProgressionCutoff (L : ℝ) : ℕ := bulkProgressionCutoff (10 * L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProtectedTarget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The protected target from the actual initial window -/

namespace Ostmann
open Filter

noncomputable def movingProtectedTarget (k : ℕ) (logX G td totalGap : ℝ) : ℝ :=
  (logX - 2 * G - 2 * td + totalGap) / (2 : ℝ) ^ k

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntervalDensityTree
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal subdivisions of actual intervals

Cumulative mass functions give exact averaging identities on the interval
partition, so the density-increment tree applies to concrete interval masses.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def intervalNode {M : ℕ} (a L : ℝ) (w : List (Fin M)) : ℝ × ℝ :=
  w.foldl (fun (s : ℝ × ℝ) (i : Fin M) => (s.1 + (i : ℝ) * (s.2 / M), s.2 / M)) (a, L)

noncomputable def intervalNodeDensity {M : ℕ} (φ : ℝ → ℝ) (a L : ℝ)
    (w : List (Fin M)) : ℝ :=
  let s := intervalNode a L w
  (φ (s.1 + s.2) - φ s.1) / s.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedIntervalMass
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cumulative and interval masses of a finite weighted set -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def weightedCDF (P : Finset ℕ) (x μ : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P.filter (fun p => x p ≤ t), μ p

noncomputable def weightedIntervalMass (P : Finset ℕ) (x μ : ℕ → ℝ) (a b : ℝ) : ℝ :=
  ∑ p ∈ P.filter (fun p => a < x p ∧ x p ≤ b), μ p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CollisionTestTransfer
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision stability controls every chosen bounded residue test -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def residueTestError (S : Finset ℕ) (μ f : ℕ → ℝ) : ℝ :=
  (∑ r ∈ S, μ r * f r) - residueTestMean S f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueTests
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic tests on complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticResidueTest (p : ℕ) (t : ℤ) (r : ℕ) : ℝ :=
  (jacobiSym ((r : ℤ) - t) p : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTransformSpectrum
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of a small-L1 normalized additive transform

This is the finite argument (5.7), before the contracting kernel in
Proposition 5.1. It requires no analytic input.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def largeTransformSpectrum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) : Finset (ZMod p) := Finset.univ.filter fun b => 1 < ‖g b‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredSupportProjection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centered support projections in the contracting local kernel -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finiteSupportMean {α : Type*} (S : Finset α) (f : α → ℂ) : ℂ :=
  (S.card : ℂ)⁻¹ * ∑ x ∈ S, f x

noncomputable def centeredSupportProjection {α : Type*}
    (S : Finset α) (f : α → ℂ) (x : α) : ℂ :=
  if x ∈ S then f x - finiteSupportMean S f else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy bounds for the sparse kernel and its pointwise square -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def rawAdditiveKernelAction {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (x : ZMod p) : ℂ := ∑ y, f y * k (x - y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueVectorNorm
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting L2 norms for the finite local kernel blocks -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueVectorNorm {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℝ :=
  ‖(toLp 2 f : EuclideanSpace ℂ (ZMod p))‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorKernelEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring finite kernel energy bounds without a dimension factor -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorKernel {α β γ δ : Type*}
    (M : α → β → ℂ) (N : γ → δ → ℂ) (x : α × γ) (y : β × δ) : ℂ :=
  M x.1 y.1 * N x.2 y.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteTensorKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the local residue matrices -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

universe u v

noncomputable def finiteTensorKernel {ι : Type*} [Fintype ι]
    {α : ι → Type u} {β : ι → Type v} (M : ∀ i, α i → β i → ℂ)
    (x : ∀ i, α i) (y : ∀ i, β i) : ℂ := ∏ i, M i (x i) (y i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelOperator
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting-energy matrix as a continuous operator -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators

noncomputable def finiteKernelOperator {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem finiteKernelOperator_apply {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (f : EuclideanSpace ℂ β) (x : α) :
    finiteKernelOperator M f x = ∑ y, M x y * f y := rfl

theorem finiteKernelOperator_add {α β : Type*} [Fintype α] [Fintype β]
    (M N : α → β → ℂ) :
    finiteKernelOperator (fun x y => M x y + N x y) = finiteKernelOperator M + finiteKernelOperator N := by
  ext f x
  change (∑ y, (M x y + N x y) * f y) =
    (finiteKernelOperator M f) x + (finiteKernelOperator N f) x
  simp only [finiteKernelOperator_apply, add_mul, Finset.sum_add_distrib]

theorem finiteKernelOperator_smul {α β : Type*} [Fintype α] [Fintype β]
    (a : ℂ) (M : α → β → ℂ) :
    finiteKernelOperator (fun x y => a * M x y) = a • finiteKernelOperator M := by
  ext f x
  change (∑ y, (a * M x y) * f y) = a * (finiteKernelOperator M f) x
  simp only [finiteKernelOperator_apply, Finset.mul_sum, mul_assoc]

noncomputable def finiteKernelOperatorLinearMap {α β : Type*} [Fintype α] [Fintype β] :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α) where
  toFun := finiteKernelOperator
  map_add' M N := finiteKernelOperator_add M N
  map_smul' a M := finiteKernelOperator_smul a M

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ResidueProjectionScalar
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative scalar block between complementary residue supports -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def uniformResidueVector {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  (((if x ∈ S then 1 else 0) / (S.card : ℝ) : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelScalar
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar decrease contributed by the sparse local kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueKernelScalar {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (k : ZMod p → ℂ) : ℂ :=
  ∑ x, conj (uniformResidueVector S x) *
    rawAdditiveKernelAction k (uniformResidueVector (Finset.univ \ S)) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredResidueProjection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered support projections annihilate the two values of the residue indicator -/

namespace Ostmann
open scoped Classical BigOperators

theorem centeredSupportProjection_const_mul {α : Type*}
    (S : Finset α) (a : ℂ) (f : α → ℂ) :
    centeredSupportProjection S (fun x => a * f x) =
      fun x => a * centeredSupportProjection S f x := by
  funext x
  unfold centeredSupportProjection finiteSupportMean
  rw [← Finset.mul_sum]
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelBlocks
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete side and lower blocks of the finite kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueKernelSide {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) : ZMod p → ℂ :=
  centeredSupportProjection S (rawAdditiveKernelAction k (uniformResidueVector T))

noncomputable def residueKernelLower {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) (f : ZMod p → ℂ) : ZMod p → ℂ :=
  centeredSupportProjection S (rawAdditiveKernelAction k (centeredSupportProjection T f))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelUnitFactor
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit-residue normalizing factor at the fixed kernel parameter -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseKernelUnitFactor (p e : ℝ) : ℝ :=
  1 + (((17 / 20 : ℝ) ^ 2) * (e - e ^ 2) - (17 / 10) * e) / (p - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelCoordinates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residue-point coordinates of the local kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residuePointVector {p : ℕ} (a x : ZMod p) : ℂ :=
  if x = a then 1 else 0

theorem rawAdditiveKernelAction_add_input {p : ℕ} [NeZero p]
    (k f g : ZMod p → ℂ) :
    rawAdditiveKernelAction k (fun x => f x + g x) =
      fun x => rawAdditiveKernelAction k f x + rawAdditiveKernelAction k g x := by
  funext x
  simp only [rawAdditiveKernelAction, add_mul, Finset.sum_add_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialKernelCoordinates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial kernel entries in centered residue coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def localPairing {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) : ℂ :=
  ∑ x, conj (f x) * g x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelLinearMaps
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps for the concrete finite kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def centeredSupportLinearMap {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun := centeredSupportProjection S
  map_add' f g := by
    funext x
    unfold centeredSupportProjection finiteSupportMean
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    change centeredSupportProjection S (fun x => c * f x) x = c * centeredSupportProjection S f x
    rw [centeredSupportProjection_const_mul]

noncomputable def rawKernelLinearMap {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun := rawAdditiveKernelAction k
  map_add' f g := rawAdditiveKernelAction_add_input k f g
  map_smul' c f := by
    funext x
    change (∑ y, (c * f y) * k (x - y)) = c * ∑ y, f y * k (x - y)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

noncomputable def residueLowerLinearMap {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  (centeredSupportLinearMap S).comp ((rawKernelLinearMap k).comp (centeredSupportLinearMap T))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteBlockMatrix
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite matrices for the scalar plus centered-residue blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def finiteBlockMatrix {p : ℕ} [NeZero p]
    (a : ℂ) (row col : ZMod p → ℂ) (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) :
    Option (ZMod p) → Option (ZMod p) → ℂ
  | none, none => a
  | none, some y => conj (row y)
  | some x, none => col x
  | some x, some y => L (residuePointVector y) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseResidueMatrix
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix form of the concrete local sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residuePointCoordinates {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a : ZMod p) : Option (ZMod p) → ℂ
  | none => 1
  | some x => centeredSupportProjection S (residuePointVector a) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseUnitPolydisc
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the scalar unit mean on the parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseUnitPolynomial (p e : ℝ) (c d : ℂ) : ℂ :=
  1 + c * ((-(17 / 20) * e / (p - 1) : ℝ) : ℂ) +
    d * (((17 / 20) ^ 2 * (e - e ^ 2) / (p - 1) : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteCauchyEstimate
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient bounds by finite Fourier inversion on a circle

For a finite polynomial, a sufficiently large root-of-unity grid recovers every
coefficient exactly. This supplies the Cauchy estimate used in Section 5.3,
including for finite-dimensional operator spaces, without a dimension factor.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def cyclicPolynomial {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c : ZMod N → E) (r : ℝ) (z : ZMod N) : E :=
  ∑ j, ZMod.stdAddChar (j * z) • ((r ^ j.val : ℝ) : ℂ) • c j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FinitePolynomialTail
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular polynomial truncation with a geometric error -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def rectangularPolynomialSum {E : Type*} [AddCommMonoid E]
    (c : ℕ → ℕ → E) (N K : ℕ) : E :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    if i ≤ K ∧ j ≤ K then c i j else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCircleEstimate
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy and truncation estimates for ordinary finite polynomials -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finitePolynomial {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (c : ℕ → E) (N : ℕ) (u : ℂ) : E := ∑ i ∈ Finset.range N, u ^ i • c i

noncomputable def finitePolynomial₂ {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (c : ℕ → ℕ → E) (N : ℕ) (u v : ℂ) : E :=
  finitePolynomial (fun i => finitePolynomial (c i) N v) N u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorModes
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only low centered modes survive the rectangular truncation -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def centeredCoordinateSupport {n : ℕ} {p : Fin n → ℕ}
    (x : ∀ i, Option (ZMod (p i))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ none)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ElementaryPolynomial
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subset polynomial used in the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def elementaryCoefficient {n : ℕ} (b : Fin n → ℂ) (j : ℕ) : ℂ :=
  ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j), ∏ i ∈ I, b i

noncomputable def elementaryTruncation {n : ℕ} (b : Fin n → ℂ) (K : ℕ) : ℂ :=
  ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card ≤ K), ∏ i ∈ I, b i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TruncatedModePairing
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairing the truncated kernel against only its active centered modes -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

noncomputable def countingVectorNorm {α : Type*} [Fintype α] (f : α → ℂ) : ℝ :=
  ‖(toLp 2 f : EuclideanSpace ℂ α)‖

noncomputable def lowModeVector {n : ℕ} {p : Fin n → ℕ}
    (K : ℕ) (f : (∀ i, Option (ZMod (p i))) → ℂ) (x : ∀ i, Option (ZMod (p i))) : ℂ :=
  if (centeredCoordinateSupport x).card ≤ K then f x else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelPairing
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear evaluation of the finite kernel against two fixed vectors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def kernelPairingLinearMap {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) : (α → β → ℂ) →ₗ[ℂ] ℂ where
  toFun M := ∑ x, conj (f x) * ∑ y, M x y * g y
  map_add' M N := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTruncatedWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The truncated tensor is the squared subset weight -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def tensorPointCoordinates {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (a : ∀ i, ZMod (p i))
    (x : ∀ i, Option (ZMod (p i))) : ℂ :=
  ∏ i, residuePointCoordinates (S i) (a i) (x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_AveragedKernelPairing
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the actual tensor coordinates over summand elements -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def averagedCoordinates {ι α : Type*}
    (A : Finset ι) (V : ι → α → ℂ) (x : α) : ℂ :=
  (A.card : ℂ)⁻¹ * ∑ a ∈ A, V a x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteCoordinateEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The energy of averaged finite tensor coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def centeredSubsetVector {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n))
    (a : ∀ i, ZMod (p i)) (x : ∀ i : T, ZMod (p i)) : ℂ :=
  ∏ i : T, centeredSupportProjection (S i) (residuePointVector (a i)) (x i)

noncomputable def centeredSubsetEnergy {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) : ℝ :=
  countingVectorNorm (averagedCoordinates A (fun x => centeredSubsetVector p S T (a x))) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredCoordinateSupport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decomposing the actual tensor coordinates by their centered support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def supportedCoordinates {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) (i : Fin n) : Option (ZMod (p i)) :=
  if hi : i ∈ T then some (z ⟨i, hi⟩) else none

@[simp] theorem supportedCoordinates_support {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) :
    centeredCoordinateSupport (supportedCoordinates p T z) = T := by
  ext i
  simp [centeredCoordinateSupport, supportedCoordinates]

theorem supportedCoordinates_injective {n : ℕ} (p : Fin n → ℕ) :
    Function.Injective (fun z : Σ T : Finset (Fin n), (∀ i : T, ZMod (p i)) =>
      supportedCoordinates p z.1 z.2) := by
  rintro ⟨T, z⟩ ⟨U, w⟩ h
  have hT := congrArg centeredCoordinateSupport h
  simp only [supportedCoordinates_support] at hT
  subst U
  congr 1
  funext i
  have hi := congrFun h i
  simpa [supportedCoordinates, i.property] using hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorRamanujanExpansion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expansion of the reduced-frequency kernel by centered subset modes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def centeredResidueGram {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (a b : ZMod p) : ℂ :=
  ∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
    centeredSupportProjection S (residuePointVector b) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_UnitRamanujanProduct
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced-frequency kernel factors over the actual CRT moduli -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def unitRamanujanKernel (q : ℕ) [NeZero q] (z : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencyEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced-frequency energy of a uniform set and its Ramanujan kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def unitFrequencyEnergy {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) : ℝ :=
  ∑ u : (ZMod q)ˣ, ‖(A.card : ℂ)⁻¹ * ∑ x ∈ A,
    ZMod.stdAddChar ((u : ZMod q) * a x)‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SubsetReducedEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive subset expansion of the classical reduced energy -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def subsetSieveCoefficient {n : ℕ} (p : Fin n → ℕ)
    (S : ∀ i, Finset (ZMod (p i))) (R T : Finset (Fin n)) : ℝ :=
  (∏ i ∈ T, (p i : ℝ)) * (∏ i ∈ R \ T, ((p i : ℝ) / (S i).card - 1))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SquarefreeMultiplierCount
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary positive-density supply of squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def nonSquarefreeMultipliers (U : ℕ) : Finset ℕ :=
  (Finset.range (U + 1)).filter (fun u => u ≠ 0 ∧ ¬ Squarefree u)

noncomputable def positiveMultiplesUpTo (U d : ℕ) : Finset ℕ :=
  (Finset.range (U + 1)).filter (fun u => u ≠ 0 ∧ d ∣ u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_MultiplierWeightedBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary divisor and logarithmic budgets for sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def positiveMultipliers (U : ℕ) : Finset ℕ := Finset.Icc 1 U

@[simp] theorem positiveMultipliers_card (U : ℕ) : (positiveMultipliers U).card = U := by
  simp [positiveMultipliers, Nat.card_Icc]

noncomputable def multiplierPrimeWeight (P : Finset ℕ) (w : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ u then w p else 0

noncomputable def badDivisorMultipliers (U : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => ∃ p ∈ P, p ∣ u)

noncomputable def largeWeightMultipliers (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => B < multiplierPrimeWeight P w u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_GoodSieveMultipliers
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously squarefree, coprime and low-weight sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def goodSieveMultipliers (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => Squarefree u ∧
    ¬ (∃ p ∈ T, p ∣ u) ∧ multiplierPrimeWeight P w u ≤ B)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_MultiplierRatioProduct
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both imbalance products on the retained squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def multiplierRatioProduct (P : Finset ℕ) (κ : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∏ p ∈ P, if p ∣ u then κ p else 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeDivisorIndices
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering squarefree integer multipliers as actual prime-index subsets -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeDivisorIndices {n : ℕ} (p : Fin n → ℕ) (u : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ∣ u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ConcreteExtensionWeights
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer multipliers supply the actual subset extension weights -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeProductSubsets {n : ℕ} (p : Fin n → ℕ) (Q : ℕ) :
    Finset (Finset (Fin n)) := Finset.univ.filter (fun R => (∏ i ∈ R, p i) ≤ Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product windows inherited through every actual integer extension -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The logarithmic product budget left after each common pivot is removed. -/
noncomputable def movingProductExponent (T : ℕ → ℝ) (W : ℝ) : ℕ → ℝ
  | 0 => W
  | n + 1 => 2 * (movingProductExponent T W n - T n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveTemplateCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived product caps for every restored moving template -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingCellPivotExponent (G c : ℕ → ℝ) (n : ℕ) : ℝ :=
  G (n + 1) - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c n - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer frequency cutoffs that retain the actual product-window center -/
namespace Ostmann

/-- Centering at the measured terminal product avoids charging its rounding
error again at each subsequent transfer. -/
noncomputable def movingProductFrequencyExponent (T : ℕ → ℝ)
    (W Y m : ℝ) (n : ℕ) : ℝ :=
  movingProductExponent T W n - Y + (2 : ℝ) ^ n * Real.sqrt (4 * m)

noncomputable def movingProductNaturalCutoff (T : ℕ → ℝ)
    (W Y m : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (movingProductFrequencyExponent T W Y m n)⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductGapBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive product budget is the prescribed compensation gap -/
namespace Ostmann

noncomputable def movingTargetPivotExponent (G : ℝ) (ws : List ℝ) (n : ℕ) : ℝ :=
  G + (2 : ℝ) ^ n * (ws.drop n).headD 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One giant-prior step with a product bound only on actual coefficient support -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveTemplateSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full giant-prior step with its actual supported product bound -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveFinalSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NonbulkHarmonicBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonbulk normalization costs only its actual surviving slots -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def nonbulkCombinatorialCost (n B : ℕ) : ℝ :=
  (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) * (2 ^ n * B).factorial

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPeriodBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential bound for the actual common frequency period -/

namespace Ostmann

def wordPeriodExponent (n : ℕ) (b : ℝ) : ℝ :=
  ((2 ^ n - 1 : ℕ) : ℝ) * (b ^ (n + 1) + 1) + ((2 ^ (n + 1) - 1 : ℕ) : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RangedPairNumericBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit numerical costs of the two actual ranged word histories -/

namespace Ostmann
open scoped BigOperators
open Filter

noncomputable def rangedPairExponent (n : ℕ) (b d C S H : ℝ) : ℝ :=
  H + 2 * C * wordPeriodExponent n b +
    4 * Real.log 3 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) *
      b ^ (n + 1) + 2 * ((4 * S + 2 * C) * (2 ^ n : ℕ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholePrimeGrid
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact short-cell partitions of the original whole prime shells -/

namespace Ostmann
open Filter
open scoped Classical

noncomputable def wholePrimeGridCount (b : ℝ) : ℕ := ⌈Real.exp (b + 1)⌉₊ + 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WholeShellGeometry
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact interval geometry for the full original bulk prime shell -/

namespace Ostmann
open scoped Classical

noncomputable def wholeShellLower (a b : ℝ) (c : Fin (wholePrimeGridCount b)) : ℝ :=
  Real.exp a + (c : ℝ) * ((Real.exp b - Real.exp a) / (wholePrimeGridCount b : ℝ))

noncomputable def wholeShellUpper (a b : ℝ) (c : Fin (wholePrimeGridCount b)) : ℝ :=
  Real.exp a + ((c : ℝ) + 1) * ((Real.exp b - Real.exp a) / (wholePrimeGridCount b : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiCube
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete finite Boolean polynomials for Bonami's inequality -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

noncomputable def booleanPolynomial {α : Type*} [Fintype α]
    (a : (α → Bool) → ℝ) (ε : α → Bool) : ℝ :=
  ∑ b : α → Bool, a b * ∏ i : α, if b i then (if ε i then 1 else -1) else 1

noncomputable def booleanEnergy {α : Type*} [Fintype α]
    (r : ℝ) (a : (α → Bool) → ℝ) : ℝ :=
  ∑ b : α → Bool, (∏ i : α, if b i then r else 1) * (a b) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiTensor
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensorizing the two-point Bonami estimate on a finite cube -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

universe u

noncomputable def booleanMoment {α : Type*} [Fintype α]
    (l : ℕ) (a : (α → Bool) → ℝ) : ℝ :=
  ∑ ε : α → Bool, |booleanPolynomial a ε| ^ (2 * l)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiInput
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharge of the published Bonami input

The finite even-moment specialization is proved here from the elementary
two-point inequality and finite convexity. No infinite-product theorem is
needed for the application.
-/

namespace Ostmann

open Finset
open scoped Classical BigOperators

noncomputable def boolFinsetEquiv (α : Type*) [Fintype α] :
    (α → Bool) ≃ Finset α where
  toFun b := univ.filter fun i => b i = true
  invFun Q i := decide (i ∈ Q)
  left_inv b := by
    funext i
    cases h : b i <;> simp [h]
  right_inv Q := by ext i; simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedPivotTuples
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting pivot tuples to the support of their original harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def supportedPivotTuples (P : Finset ℕ) {r : ℕ}
    (Q : Fin r → Finset ℕ) : Finset (Fin r → P) :=
  (Finset.univ.filter Function.Injective).filter (fun x => ∀ i, (x i : ℕ) ∈ Q i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CellRoleBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorption of the cell-role count

Section 4 fixes `ε = 1/10000`, bounds the number of selected cell roles by
`C (k+1) exp(2 ε k)`, and uses the scale `z = exp(3 ε k)`.  Their ratio tends
to zero, so every fixed positive proportion of `z` eventually absorbs the
role count. This is an elementary numerical step, with no published input.
-/

namespace Ostmann

open Filter
open scoped Topology

/-- The fixed small parameter used in the character selection. -/
noncomputable def cellRoleEpsilon : ℝ := 1 / 10000

/-- Upper bound for all selected cell roles, including the anchors. -/
noncomputable def cellRoleCountBound (C : ℝ) (k : ℕ) : ℝ :=
  C * ((k : ℝ) + 1) * Real.exp (2 * cellRoleEpsilon * k)

/-- The larger exponential scale which absorbs the cell-role count. -/
noncomputable def cellRoleScale (k : ℕ) : ℝ :=
  Real.exp (3 * cellRoleEpsilon * k)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeDiagonalMatching
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported arithmetic diagonal is a sum over actual prime permutations -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def primePermutationCorrelation {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) : ℂ :=
  ∑ e : Equiv.Perm H, ∑ l : H → P, ∑ d : D, ∑ d' : D,
    if v d = v d' then c (l, d) * conj (c (l ∘ e.symm, d')) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedRetainedPhase
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact diagonal phase quotients with a fixed external pivot -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def externalPivotUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option I → Option I → ℤ) (ν : I → ℕ → ℂ) (M : ℕ)
    (i : I) (p : ℕ) : ℂ :=
  ν i p * χ i p (M : ZMod p) ^ b (some i) none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SignedAtomSchedule
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive and conjugate atom copies retain their original characters -/

namespace Ostmann

noncomputable def signedAtomCharacter {I : Type*} (size : I → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) :
    (Σ i : Bool × I, Fin (size i.2)) → ∀ p : ℕ, DirichletCharacter ℂ p :=
  fun i p => if i.1.1 then χ p else (χ p)⁻¹

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordCoordinates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit original word and cell coordinates for the signed atom schedule -/

namespace Ostmann
open scoped Classical BigOperators

def initialWordSize {C : Type*} (k : ℕ) (s : C → ℕ) : Option C → ℕ
  | none => k
  | some c => s c

def positiveWordConstituentEquiv {C : Type*} (k : ℕ) (s : C → ℕ) :
    (Σ a : Option C, Fin (initialWordSize k s a)) ≃ (Fin k ⊕ (Σ c, Fin (s c))) where
  toFun := fun ⟨a, i⟩ => match a with
    | none => Sum.inl i
    | some c => Sum.inr ⟨c, i⟩
  invFun := fun z => match z with
    | Sum.inl i => ⟨none, i⟩
    | Sum.inr ⟨c, i⟩ => ⟨some c, i⟩
  left_inv := by rintro ⟨a, i⟩; cases a <;> rfl
  right_inv := by rintro (i | ⟨c, i⟩) <;> rfl

def signedConstituentEquiv {I : Type*} (size : I → ℕ) :
    (Σ a : Bool × I, Fin (size a.2)) ≃
      ((Σ i, Fin (size i)) ⊕ (Σ i, Fin (size i))) where
  toFun := fun ⟨⟨b, i⟩, j⟩ => if b then Sum.inl ⟨i, j⟩ else Sum.inr ⟨i, j⟩
  invFun := fun z => match z with
    | Sum.inl ⟨i, j⟩ => ⟨⟨true, i⟩, j⟩
    | Sum.inr ⟨i, j⟩ => ⟨⟨false, i⟩, j⟩
  left_inv := by rintro ⟨⟨b, i⟩, j⟩; cases b <;> rfl
  right_inv := by rintro (⟨i, j⟩ | ⟨i, j⟩) <;> rfl

def positiveWordTupleEquiv {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) :
    (Σ a : Option C, Fin (initialWordSize k s a)) ≃ Fin (k + m) :=
  (positiveWordConstituentEquiv k s).trans
    ((Equiv.sumCongr (Equiv.refl _) cell).trans finSumFinEquiv)

def initialWordTupleEquiv {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) :
    (Σ a : Bool × Option C, Fin (initialWordSize k s a.2)) ≃
      Fin ((k + m) + (k + m)) :=
  (signedConstituentEquiv (initialWordSize k s)).trans
    ((Equiv.sumCongr (positiveWordTupleEquiv k m s cell)
      (positiveWordTupleEquiv k m s cell)).trans finSumFinEquiv)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopWordBinScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top prime controls every nonempty bulk-word bin -/

namespace Ostmann

open Filter
open scoped BigOperators

noncomputable def wordLogBin {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ) :
    Fin (⌊4 * τ⌋₊ + 1) :=
  ⟨min ⌊∑ i, ℓ i⌋₊ ⌊4 * τ⌋₊, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCharacterStatistic
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive word statistic is the real part of the actual tuple mean -/

namespace Ostmann

open scoped BigOperators SchwartzMap ComplexConjugate Classical

noncomputable def wordCharacterMean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) : ℂ :=
  ∑ x, if bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b then
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCharacterRemoval
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeat removal for the actual two-copy word statistic -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordCharacterEvent {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (bin : (Fin k → A) → B) (b : B) :
    Finset (Fin ((k + m) + (k + m)) → A) :=
  Finset.univ.filter (fun x =>
    (bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b) ∧
    productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x ≠ 0)

noncomputable def injectiveWordCharacterMean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) : ℂ :=
  ∑ x ∈ (wordCharacterEvent μ ν bin b).filter Function.Injective,
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordGraphAmplitude
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial graph amplitude under the original word and cell laws -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordGraphAmplitude {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (bin : (Fin k → P) → B) (b : B) : ℂ :=
  ∑ x ∈ (wordCharacterEvent μ ν bin b).filter Function.Injective,
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      sampledTupleAmplitude P hP (wordCopyCharacter k m χ) t ψ X N x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotPrimeChecks
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructed prime checks with a fixed external integer coordinate -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotPrimeValues {V : Type*} (M : ℕ) (p : V → ℕ) : Option V → ℕ
  | none => M
  | some i => p i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPairFactors
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact prime guard and counterpart mask in the actual matched pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

noncomputable def constituentCounterpartMask {H Y : Type*}
    (Q : H → Finset ℕ) (e : Equiv.Perm H) : H ⊕ Y → ℕ → ℂ
  | .inl h, p => if p ∈ Q (e.symm h) then 1 else 0
  | .inr _, _ => 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCenters
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual backwards targets give the copied block's exact center -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterPivotTarget (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (j : Fin k) : ℝ :=
  (pivotTargets k J a Δ)[j.val]'(by simp only [pivotTargets, backwardTargets_length,
    pivotCoefficients, List.length_ofFn]; exact j.isLt)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterIntervalGeometry
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed character targets satisfy the two integer transfer inequalities -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

noncomputable def characterRangeError (k : ℕ) (c : ℝ) : ℝ :=
  ((2 : ℝ) ^ k + k + 2) * c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordAtomIntervals
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-atom intervals retain exactly the selected initial word bin -/
namespace Ostmann
open scoped BigOperators Classical

noncomputable def initialWordAtomLower {C : Type*} (j : ℕ) (lo : C → ℕ)
    (v : Bool × Option C) : ℕ :=
  v.2.elim ⌈Real.exp (j : ℝ)⌉₊ lo

noncomputable def initialWordAtomUpper {C : Type*} (j : ℕ) (hi : C → ℕ)
    (v : Bool × Option C) : ℕ :=
  v.2.elim (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1) hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotLossBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual factorial and harmonic-mass loss in the transfer iteration -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

noncomputable def pivotLogLoss (n : ℕ) (C L : ℝ) : ℝ :=
  Real.log (n.factorial : ℝ) + (n : ℝ) * C * L

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicInitialAmplitude
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive endpoints give an actual finite initial graph amplitude -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordRepeatFactor {k m : ℕ} (P : Finset ℕ)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) (ψ : 𝓢(ℝ, ℂ)) (D : ℝ) : ℝ :=
  ‖𝓕 ψ 0‖ * (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
    (((k + m) + (k + m) : ℕ) : ℝ) ^ ((k + m) + (k + m)) *
    Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAtomIteration
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iteration with the selected word bin and actual character cell products -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def characterPivotCap {k : ℕ} (T : Fin k → ℝ) (C : ℝ) (n : ℕ) : ℕ :=
  if h : n < k then naturalProductCap (T ⟨n, h⟩ + C) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def logPrimeBand (T : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊Real.exp (2 * T)⌋₊ \ Nat.primesLE ⌊Real.exp T⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandGeometry
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three selected prime bands give all character separation parameters -/
namespace Ostmann

noncomputable def characterBandPoint (α β : ℝ) (q i : ℕ) : ℝ :=
  α + i * ((β - α) / q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellProductIntervals
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer interval endpoints for actual selected prime-cell words -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeCellLower (h : ℕ) : ℕ := ⌈Real.exp (h : ℝ)⌉₊
noncomputable def primeCellUpper (h : ℕ) : ℕ := ⌊Real.exp ((h : ℝ) + 1)⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FillerTargetScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The filler target completing the prescribed total product -/

namespace Ostmann

open scoped BigOperators

noncomputable def fillerTarget (k : ℕ) (τ Δ₀ J A T : ℝ) : ℝ :=
  (1000 * (4 : ℝ) ^ k * τ + Δ₀) / 2 - J - (T + A)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterMeanRotation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One common rotation and the original, unrotated character priors -/
namespace Ostmann
open scoped Classical BigOperators

def quarterTurn (q : Bool × Bool) : ℂ :=
  if q.1 then (if q.2 then 1 else -1) else (if q.2 then Complex.I else -Complex.I)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CellListPigeonhole
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the ordered cell lists across endpoints -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def boundedCellLists (N B : ℕ) : Finset (List ℕ) :=
  (Finset.range (N + 1)).biUnion (fun n =>
    (Finset.univ : Finset (Fin n → Fin (B + 1))).image
      (fun f => List.ofFn (fun i => (f i : ℕ))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CellGroupPigeonhole
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing every cell group at the cost of the total number of labels -/

namespace Ostmann

def encodeCellGroups : List (List ℕ) → List ℕ
  | [] => []
  | w :: ws => w.length :: (w ++ encodeCellGroups ws)

def decodeCellGroups : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | _ + 1, [] => []
  | r + 1, n :: xs => xs.take n :: decodeCellGroups r (xs.drop n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single depth choice pays for all actual cell-selection codes -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterTargetLabelBound (c δ : ℝ) (k : ℕ) : ℕ :=
  ⌈cellRoleCountBound (256 / (δ * c)) k⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCellCovering
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed covering error for every selected character-cell list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterCellCoveringError (c δ : ℝ) (k : ℕ) : ℝ :=
  64 / (δ * c) + (characterTargetLabelBound c δ k : ℝ) + 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterInitialProduct
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete initial product has the prescribed logarithmic window -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterFillerTarget {k : ℕ} (logX Δ J : ℝ)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ) : ℝ :=
  (logX + Δ) / 2 - J - (∑ j, T j) - ∑ j, (a j false + a j true)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedTargets
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One target function containing precisely the backwards pivot and filler data -/
namespace Ostmann

noncomputable def characterConstructedTargets (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) : Option (Fin k) → ℝ :=
  let TP := characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
    (fun j => characterPivotGap B z m j.val)
  fun j => j.elim
    (characterFillerTarget logX (characterBaseGap B z m) J TP (fun j b => (a (j, b) : ℝ))) TP

@[simp] theorem characterConstructedTargets_some (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) (j : Fin k) :
    characterConstructedTargets k J logX B z m a (some j) =
      characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
        (fun j => characterPivotGap B z m j.val) j := rfl

@[simp] theorem characterConstructedTargets_none (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) :
    characterConstructedTargets k J logX B z m a none =
      characterFillerTarget logX (characterBaseGap B z m) J
        (characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
          (fun j => characterPivotGap B z m j.val)) (fun j b => (a (j, b) : ℝ)) := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRoundedEndpoint
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral endpoints with the original character product scale -/
namespace Ostmann
open scoped Classical

noncomputable def characterEndpointFactor (k : ℕ) : ℝ := 1000 * (4 : ℝ) ^ k
noncomputable def characterRoundedEndpoint (k : ℕ) (v : ℝ) : ℕ :=
  ⌊Real.exp (characterEndpointFactor k * Real.exp v)⌋₊
noncomputable def characterRoundedTau (k : ℕ) (v : ℝ) : ℝ :=
  Real.log (characterRoundedEndpoint k v : ℝ) / characterEndpointFactor k

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterIndexCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime log indices fit the fixed-cell selection budget -/
namespace Ostmann
open Filter

noncomputable def characterIndexCutoff (β L : ℝ) : ℕ := ⌈Real.exp (β * L)⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeMatchingSupport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the actual diagonal to cell-preserving matchings -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def cellPreservingMatchings {H K : Type*} [Fintype H]
    (label : H → K) : Finset (Equiv.Perm H) :=
  Finset.univ.filter (fun e => ∀ h, label (e h) = label h)

@[simp] theorem mem_cellPreservingMatchings {H K : Type*} [Fintype H]
    (label : H → K) (e : Equiv.Perm H) :
    e ∈ cellPreservingMatchings label ↔ ∀ h, label (e h) = label h := by
  simp [cellPreservingMatchings]

noncomputable def primeMatchingContribution {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ)
    (e : Equiv.Perm H) : ℂ :=
  ∑ d : D, ∑ d' : D, if v d = v d' then
    ∑ l : H → P, c (l, d) * conj (c (l ∘ e.symm, d')) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectedShellGeometry
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen small shell and upper rich shell satisfy the actual cutoffs -/
namespace Ostmann
open Filter

@[simp] theorem characterBandPoint_succ (α β : ℝ) (q i : ℕ) :
    characterBandPoint α β q (i + 1) = characterBandPoint α β q i + (β - α) / q := by
  unfold characterBandPoint
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionScales
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rates for the actual tail count and top-word bin count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The endpoint tests can be extended outside their selected finite set
without strengthening any premise about actual endpoints. -/
noncomputable def characterEndpointExtension (E : Finset ℕ) (x₀ : ℕ)
    (G : ℕ → ℕ → ℂ) (x p : ℕ) : ℂ := if x ∈ E then G x p else G x₀ p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotGraphEmbedding
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the retained graph while the pivot has only a constant coordinate -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotGraph {V : Type*} (g : V → V → ℤ) : Option V → Option V → ℤ
  | some i, some j => g i j
  | _, _ => 0

noncomputable def fixedPivotCharacters {V : Type*}
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) : Option V → ∀ p : ℕ, DirichletCharacter ℂ p
  | none, _ => 1
  | some i, p => χ i p

def fixedPivotUnary {V : Type*} (ν : V → ℕ → ℂ) : Option V → ℕ → ℂ
  | none, _ => 1
  | some i, p => ν i p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordEmbedding
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The existing supported comparison specialized to words of actual primes -/

namespace Ostmann
open scoped Classical SchwartzMap FourierTransform

def primeWordEmbedding {I K : Type*} (words : I → List K) : I → List (Option K) :=
  fun i => (words i).map some

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalCostData
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual final pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

/-- This single constant bounds both the prime-test count and the quadratic
pairwise-coprimality count of the literal final histories. -/
noncomputable def constituentFinalCountRate (N n : ℕ) (s : ℝ) : ℝ :=
  2 * (3 ^ n * N : ℕ) * s * (2 ^ n - 1 : ℕ) + 3 * ((3 ^ n * N : ℕ) * s) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedWindow
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counterpart normalization on the original H and Y product law -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def retainedHWord (H Y : Type*) [Fintype H] : List (H ⊕ Y) :=
  Finset.univ.toList.map Sum.inl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalEndpoints
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Few endpoints fail a positive prime test

The argument tests the uniform measure on the actual exceptional set. This
turns the collision estimate for every large subset into a cardinality bound.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def badEndpoints (A P : Finset ℕ) (w : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  A.filter (fun a => (∑ p ∈ P, w p * f a p) < (δ / 2) * ∑ p ∈ P, w p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointTestScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff used to test all large endpoint subsets -/

namespace Ostmann

open Filter

noncomputable def endpointTestCutoff (t : ℝ) : ℕ := ⌊Real.exp (t / 2) / t ^ 12⌋₊

noncomputable def endpointTestThreshold (t : ℝ) : ℕ := ⌈Real.exp (t / 2) / t ^ 10⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalCharacterEndpoints
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail collision estimate supplies typical character endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def realTranslatedCharacterTest
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (ζ : ℂ)
    (p r : ℕ) : ℝ := (ζ * χ p ((r : ZMod p) - t p)).re

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HigherCharacterDecorrelation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proposition 4.1: maximal translated higher-order bias has harmonic mass o(L) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

noncomputable def closedLogLogPrimeBand (α β L : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (Real.exp (β * L))⌋₊).filter
    (fun p => α * L ≤ Real.log (Real.log (p : ℝ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiComplex
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete complex Jacobi character used in the Fourier expansion -/

namespace Ostmann

noncomputable def jacobiComplex (M : ℕ) [NeZero M] : DirichletCharacter ℂ M :=
  (jacobiCharacterInt M).ringHomComp (Int.castRingHom ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedCharacterPoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square-root normalization in the quadratic Poisson formula -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform

noncomputable def jacobiGaussPhase (M : ℕ) [NeZero M] : ℂ :=
  gaussSum (jacobiComplex M) ZMod.stdAddChar / (Real.sqrt (M : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseConductorCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral conductor cutoff in (5.14) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseTruncationDegree (C L : ℝ) : ℕ := ⌈C * L⌉₊

noncomputable def sparseConductorCutoff (C L : ℝ) : ℕ :=
  ⌈Real.exp (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L))⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseMellinCoefficients
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative coefficients of the actual sparse additive kernel -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_3 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseProductCharacter
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product characters and their active conductor support -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseProductCharacter {I : Type*} [Fintype I]
    (p : I → ℕ) (χ : ∀ i, DirichletCharacter ℂ (p i)) :
    DirichletCharacter ℂ (∏ i, p i) :=
  ∏ i, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (χ i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TruncatedBilinearCube
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact truncation of the two subset choices -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def subsetPairFactor (b : ℂ) : Bool × Bool → ℂ
  | (false, false) => 1
  | (true, false) => b
  | (false, true) => b
  | (true, true) => b ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightMellinExpansion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative Fourier expansion of the original squared subset weight -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_4 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InjectiveCoefficientTransport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of coefficients along an injective character reduction -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def injectiveCoefficient {α β : Type*} (f : α → β) (w : α → ℂ)
    (b : β) : ℂ := if h : ∃ a, f a = b then w h.choose else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimitiveExpansion
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sparse weight as a bounded sum of primitive characters -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_5 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimeSelection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A prime block with retained logarithmic weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def dyadicPrimeBlock (P : Finset ℕ) (j : ℕ) : Finset ℕ :=
  P.filter fun p => Nat.log 2 p = j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmallPrimeSubset
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the original small-prime amplification modulus -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def amplificationPrimeCount (T : ℝ) (z : ℕ) : ℕ :=
  ⌊T / (50 * Real.log (2 * (z : ℝ)))⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalParameterChoice
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete integer choices for the original moment parameters -/

namespace Ostmann

noncomputable def originalMomentOrder (L V : ℝ) : ℕ := 2 * ⌈L / (2 * V)⌉₊ + 10
noncomputable def originalHolderOrder (V : ℝ) : ℕ := ⌊V ^ (1 / 1000000 : ℝ)⌋₊
noncomputable def originalFrequencyCutoff (V : ℝ) : ℕ := ⌈Real.exp (27 * V / 2)⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticParameterGrid
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite phase and scale grids for the quadratic coefficient arrays -/

namespace Ostmann

noncomputable def quadraticParameterGrid (Rmax δ : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (⌊1 / δ⌋₊ + 1)) ×ˢ (Finset.range (⌊Rmax / δ⌋₊ + 1))

noncomputable def quadraticGridPhase (δ : ℝ) (j : ℕ × ℕ) : ℝ := j.1 * δ

noncomputable def quadraticGridScale (δ : ℝ) (j : ℕ × ℕ) : ℝ := 1 + j.2 * δ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGridApproximation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Approximation of the original quadratic series by the fixed grid -/

namespace Ostmann

open scoped SchwartzMap

noncomputable def quadraticGridError (q s : ℕ) (B Rmax v H : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℝ :=
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H +
    Real.sqrt ((s : ℝ) * v / q) * W * B *
      (SchwartzMap.seminorm ℝ 0 0 Φ +
        SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticArrayApproximation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed array approximates the original Jacobi statistic -/

namespace Ostmann

open scoped BigOperators

noncomputable def quadraticArrayStatistic (S : Finset ℕ) (M : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ s : S, rootNormalizedCoefficient F s * (realJacobi s.val M : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquarefreeFrequencyRectangle
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rectangular expansion underlying the original coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable def squarefreeKernelSupport (L N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun s => Squarefree s ∧ s.Coprime L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalKernelDecomposition
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the principal small kernels in the original Fourier statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def smallSquarefreeKernels (L N : ℕ) : Finset ℕ :=
  (squarefreeKernelSupport L N).filter (fun s => s ≤ L ^ 4)

noncomputable def largeSquarefreeKernels (L N : ℕ) : Finset ℕ :=
  (squarefreeKernelSupport L N).filter (fun s => L ^ 4 < s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenter
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting one common center

The finite incidence argument in Section 3: large matching-prime sets
with small pairwise intersections have total size at most twice the
ambient set. A large moment therefore forces one large matching set.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def centerIncidence {I P : Type*} [Fintype I] [DecidableEq P]
    (S : I → Finset P) (p : P) : ℝ := ∑ i : I, if p ∈ S i then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCongruences
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intersections of the matching-prime sets attached to integer lifts -/

namespace Ostmann

open scoped BigOperators

def matchingPrimes (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) : Finset ℕ :=
  P.filter fun p => (p : ℤ) ∣ n - a * t p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterAssembly
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center extraction for the actual congruence matching sets -/

namespace Ostmann

open scoped BigOperators

def matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) : Finset P :=
  Finset.univ.filter fun p => (p.1 : ℤ) ∣ n - a * t p.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterTupleCounts
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered distinct tuples and common-center lift moments -/

namespace Ostmann

open scoped BigOperators

/-- An ordered tuple of distinct primes lies in a matching set exactly when
it is an embedding into that set. -/
def matchingTupleEquiv {P : Type*} (S : Finset P) (r : ℕ) :
    (Fin r ↪ S) ≃ {e : Fin r ↪ P // ∀ i, e i ∈ S} where
  toFun e := ⟨⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩,
    fun i => (e i).2⟩
  invFun e := ⟨fun i => ⟨e.1 i, e.2 i⟩, fun i j h => e.1.injective (congrArg Subtype.val h)⟩
  left_inv e := by ext i; rfl
  right_inv e := by apply Subtype.ext; ext i; rfl

def incidenceSwap {N E : Type*} (R : N → E → Prop) :
    (Σ n, {e // R n e}) ≃ (Σ e, {n // R n e}) where
  toFun z := ⟨z.2.1, z.1, z.2.2⟩
  invFun z := ⟨z.2.1, z.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterLiftBounds
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lift bounds for ordered distinct prime tuples -/

namespace Ostmann

open scoped BigOperators

def primeTupleProduct (P : Finset ℕ) {r : ℕ} (e : Fin r ↪ P) : ℕ := ∏ i, (e i).1

noncomputable def integerLiftSet (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) {r : ℕ}
    (e : Fin r ↪ P) (H : ℕ) : Finset ℤ :=
  (Finset.Ico (-(H : ℤ)) (H + 1)).filter fun n =>
    ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationCoefficients
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single finite coefficient array shared by all quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeSubsetCoefficient (P : Finset ℕ) (k : ℕ)
    (c : ℂ) (e : ℕ → ℂ) (s : ℕ) : ℂ :=
  if s ∈ primeSubsetProducts P k then c * ∏ p ∈ s.primeFactors, e p else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

def reciprocityTwist (b : ℕ → ℂ) (s : ℕ) : ℂ := if s % 4 = 3 then -b s else b s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleTranslation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the common translation for an actual tuple of primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeTupleSet (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) : Finset ℕ :=
  Finset.univ.image (fun i => (e i).val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalApproximationLift
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning the phase approximation into the common-center integer lift -/

namespace Ostmann

def approximationLift (a M : ℕ) (t b : ℤ) : ℤ := (a : ℤ) * t - b * M

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveQuadraticInverse
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational approximation forced by the actual quadratic witness

The only hypotheses below are the density energy, compact support, the
explicit large-sum event, and numerical scale bounds. The inverse quadratic
estimate and the progression reduction are proved in the imported modules.
-/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticVariationBudget (Φ : 𝓢(ℝ, ℂ)) (B : ℝ) : ℝ :=
  1 + SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
    SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * (B + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalTupleLifts
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original Fourier witnesses give a positive family of integer tuple lifts -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

noncomputable def tupleLiftFamily (P : Finset ℕ) (k A H : ℕ) (t : ℕ → ℤ) : Finset (Fin k ↪ P) :=
  Finset.univ.filter fun e => ∃ a ∈ Finset.Icc 1 A, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
    ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterConcreteMoments
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer-lift factorial moments used for common centers -/

namespace Ostmann

open scoped BigOperators

def intervalMatchingLiftEquiv (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ)
    {r : ℕ} (e : Fin r ↪ P) (H : ℕ) :
    {n : (Finset.Ico (-(H : ℤ)) (H + 1)) //
      ∀ i, e i ∈ matchingPrimeSubtype P a t n.1} ≃ integerLiftSet P a t e H where
  toFun n := ⟨n.1.1, Finset.mem_filter.mpr ⟨n.1.2,
    fun i => (Finset.mem_filter.mp (n.2 i)).2⟩⟩
  invFun n := ⟨⟨n.1, (Finset.mem_filter.mp n.2).1⟩,
    fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp n.2).2 i⟩⟩
  left_inv n := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv n := by apply Subtype.ext; rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterFromTuples
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational common center from witnessed prime tuples

This is the finite counting step in the paragraph “One common centre for many
primes” of Section 3 of the manuscript. The hypotheses are the actual family
of witnessed tuples and numerical inequalities; the factorial moments and
intersection estimates are proved from the congruences.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def liftMomentUpper (J r H Z : ℕ) : ℝ :=
  (J.descFactorial r : ℝ) * ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SignedSquarefreeRange
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete four-piece cover of the signed squarefree integers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def signedSquarefreeRange (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M : ℤ)) M).filter fun u => u ≠ 0 ∧ Squarefree u.natAbs

def quadraticSigns : Finset ℤ := {1, -1, 2, -2}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SignedQuadraticSieve
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed kernel form follows from Heath-Brown's published theorem -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticNumeratorTwist (d : ℤ) (b : ℕ → ℂ) (s : ℕ) : ℂ :=
  b s * (jacobiSym d s : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationBias
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed quadratic bias produces a large shared coefficient test -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticPrimeMean (P : Finset ℕ) (e : ℕ → ℂ) (u : ℤ) : ℂ :=
  (∑ p ∈ P, e p * (jacobiSym u p : ℂ)) / (P.card : ℂ)

noncomputable def quadraticAmplifiedCoefficients (P : Finset ℕ) (k : ℕ)
    (e : ℕ → ℂ) : ℕ → ℂ :=
  primeSubsetCoefficient P k (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCharacter
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translating the original local biases to the common affine form -/

namespace Ostmann

open scoped BigOperators

noncomputable def commonCenterOrientation (ε : ℕ → ℝ) (m : ℕ) (p : ℕ) : ℂ :=
  (ε p : ℂ) * (jacobiSym (m : ℤ) p : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteBiasPopulation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed signed mean yields a positive population with large character bias -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def orientedPrimeMean (P : Finset ℕ) (ε : ℕ → ℝ) (t : ℕ → ℤ) (x : ℤ) : ℝ :=
  (∑ p ∈ P, orientedQuadraticValue ε t x p) / P.card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairPopulationFibers
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair counting by the two population labels -/

namespace Ostmann

open scoped BigOperators Classical

def filteredPairFiberEquiv {A B C D : Type*} (f : A → C) (g : B → D)
    (R : C → D → Prop) :
    {z : A × B // R (f z.1) (g z.2)} ≃
      Σ q : {z : C × D // R z.1 z.2},
        {x : A // f x = q.1.1} × {y : B // g y = q.1.2} where
  toFun z := ⟨⟨(f z.1.1, g z.1.2), z.2⟩, ⟨z.1.1, rfl⟩, ⟨z.1.2, rfl⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), by rw [z.2.1.2, z.2.2.2]; exact z.1.2⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨⟨c, d⟩, h⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
    dsimp only at hx hy
    subst c d
    rfl

def finsetFiberEquiv {A B : Type*} [DecidableEq A] [DecidableEq B] (S : Finset A) (f : A → B) (b : B) :
    {x : S // f x = b} ≃ {x : A // x ∈ S.filter (fun x => f x = b)} where
  toFun x := ⟨x.1, Finset.mem_filter.mpr ⟨x.1.property, x.2⟩⟩
  invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PopulatedKernelSelection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining entire populated kernel fibers -/

namespace Ostmann

open scoped BigOperators Classical

/-- The retained set is a union of entire original fibers. -/
def populatedKernelPoints (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) : Finset ℤ :=
  S.filter fun x => A (f x) ∧ Q ≤ (S.filter fun y => f y = f x).card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ConductorKernelCandidates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many kernel candidates for one exceptional conductor -/

namespace Ostmann

open scoped Classical

/-- The eight possible quotients of a conductor by its odd kernel part,
with the four possible sign/two factors. -/
def conductorKernelCandidates (q : ℕ) : Finset ℤ :=
  ((Finset.Icc 1 8).product quadraticSigns).image
    (fun z : ℕ × ℤ => z.2 * (q / z.1 : ℕ))

def largeConductorKernelCandidates (q : ℕ) : Finset ℤ :=
  (conductorKernelCandidates q).filter fun d => q ≤ 4 * d.natAbs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UnsignedPrimeMass
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total logarithmic prime mass near one, from the proved zeta pole -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def unsignedPrimeTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / (n : ℝ) ^ s else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiPrimeSeries
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobi prime series differs only at the prime two -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def jacobiPrimeTerm (d : ℤ) (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (jacobiSym d n : ℝ) * Real.log n / (n : ℝ) ^ s else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UnsignedPrimeTail
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient tail estimate from the prime mass at a smaller exponent -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def unsignedPrimeTail (Q : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if Q < n then unsignedPrimeTerm s n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InfiniteSplitMass
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the prime-series bounds to a finite set of split primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def retainedSplitTerm (d : ℤ) (D Q : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ≤ Q ∧ ¬n ∣ D ∧ jacobiSym d n = 1 then unsignedPrimeTerm s n else 0

noncomputable def divisorPrimeTerm (D : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ∣ D then unsignedPrimeTerm s n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPrimeCutoffs
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual integer cutoffs for the quadratic split-prime argument -/

namespace Ostmann

noncomputable def kernelConductorCutoff (η L : ℝ) : ℕ := ⌈4 * Real.exp (2 * η * L)⌉₊
noncomputable def kernelSplitCutoff (η L : ℝ) : ℕ := ⌊Real.exp ((1 / 2 - 5 * η) * L)⌋₊
noncomputable def kernelDivisorCutoff (L : ℝ) : ℕ := ⌈Real.sqrt L⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelCollision
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision contradiction on the actual quadratic split primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticSplitPrimes (P : Finset ℕ) (m : ℕ) (u v : ℤ) : Finset ℕ :=
  P.filter fun p => ¬p ∣ 2 * m * u.natAbs * v.natAbs ∧ jacobiSym (u * v) p = 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_RootPopulationBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete diameter and collision budget for large root populations -/

namespace Ostmann

open scoped BigOperators

noncomputable def naturalRootDiameter (m : ℕ) (L : ℝ) : ℕ :=
  ⌈Real.sqrt ((m : ℝ) * Real.exp L)⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointBaseScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integer endpoint scale compatible with every selected dyadic block -/

namespace Ostmann

open Filter

noncomputable def endpointBaseScale (T : ℝ) : ℝ := 7 * T ^ (8 / 5 : ℝ) / 4
noncomputable def endpointSize (T : ℝ) : ℕ := ⌊Real.exp (endpointBaseScale T)⌋₊
noncomputable def endpointLogScale (T : ℝ) : ℝ := Real.log (endpointSize T : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_MaximalQuadraticBias
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

noncomputable def maximizingQuadraticTranslate (S : Finset ℕ) (p : ℕ) : ℕ :=
  Classical.choose (Finset.exists_max_image (Finset.range (p + 1))
    (fun t : ℕ => |residueTestMean S (quadraticResidueTest p t)|)
    (Finset.nonempty_range_iff.mpr (by omega)))

noncomputable def maximalQuadraticBias (S : Finset ℕ) (p : ℕ) : ℝ :=
  |residueTestMean S (quadraticResidueTest p (maximizingQuadraticTranslate S p))|

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ClosedQuadraticBand
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed prime band used in the manuscript's quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def closedLogPrimeBand (T : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (2 * T)⌋₊).filter (fun p => T ≤ Real.log (p : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicHarmonicBias
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring quadratic smallness to harmonic prime intervals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def iteratedLogPrimeBand (α β L : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (Real.exp (β * L))⌋₊).filter
    (fun p => Real.exp (α * L) ≤ Real.log (p : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothVerticalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent vertical kernel before contour shifting -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def primeMellinLine (t : ℝ) : ℂ := 2 + (t : ℂ) * Complex.I

@[simp] theorem primeMellinLine_re (t : ℝ) : (primeMellinLine t).re = 2 := by
  simp [primeMellinLine]

@[fun_prop] theorem primeMellinLine_continuous : Continuous primeMellinLine := by
  unfold primeMellinLine
  fun_prop

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaInverseBound
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A reciprocal Gamma bound from the reflection formula -/

namespace Ostmann

open Complex

theorem complex_sin_norm_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, norm_ofNat]
  have hp : ‖exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have hm : ‖exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  calc
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 :=
      div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

theorem gamma_inv_reflection (z : ℂ) (hz' : z.re < 1) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hne : Complex.Gamma (1 - z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  calc
    _ = Complex.Gamma (1 - z) * (Complex.Gamma z * Complex.Gamma (1 - z))⁻¹ := by
      simp [mul_inv_rev, hne]
    _ = _ := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
      simp only [inv_div]
      ring

theorem gamma_inv_norm_bound (C : ℝ) (hC : 0 ≤ C) (z : ℂ)
    (hz' : z.re < 1) (hΓ : ‖Complex.Gamma (1 - z)‖ ≤ C) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ (C / Real.pi) * Real.exp (Real.pi * |z.im|) := by
  rw [gamma_inv_reflection z hz', norm_div, norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hs : ‖sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    convert complex_sin_norm_le_exp ((Real.pi : ℂ) * z) using 1
    all_goals try with_reducible_and_instances rfl
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc
    _ ≤ C * Real.exp (Real.pi * |z.im|) / Real.pi := by
      gcongr
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaContourBounds
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma logarithmic derivatives on the four contour lines -/

namespace Ostmann

open Complex

theorem norm_inv_le_four_of_quarter_re (z : ℂ) (hz : |z.re| = 1 / 4) :
    ‖z⁻¹‖ ≤ 4 := by
  rw [norm_inv]
  have hn : (1 / 4 : ℝ) ≤ ‖z‖ := hz ▸ abs_re_le_norm z
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hn
  simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothLeftContourWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable majorant for the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

noncomputable def leftContourLine (t : ℝ) : ℂ := -(1 / 2) + (t : ℂ) * I

@[simp] theorem leftContourLine_re (t : ℝ) : (leftContourLine t).re = -(1 / 2 : ℝ) := by
  simp [leftContourLine]

@[simp] theorem leftContourLine_im (t : ℝ) : (leftContourLine t).im = t := by
  simp [leftContourLine]

@[fun_prop] theorem leftContourLine_continuous : Continuous leftContourLine := by
  unfold leftContourLine
  fun_prop

noncomputable def leftContourMajorant (t : ℝ) : ℝ := (1 + |t|) ^ (-(7 : ℝ))

theorem leftContourMajorant_integrable : Integrable leftContourMajorant := by
  have hp : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(7 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (E := ℝ)
      (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 7)
  change Integrable (fun t : ℝ => (1 + |t|) ^ (-(7 : ℝ)))
  simpa only [Real.norm_eq_abs] using hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothLeftContourBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform error from the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter

theorem one_add_log_le_log_twice (q : ℝ) (hq : 1 ≤ q) :
    1 + Real.log q ≤ (1 + 1 / Real.log 2) * Real.log (2 * q) := by
  have hq0 : 0 < q := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlog : Real.log (2 * q) = Real.log 2 + Real.log q := Real.log_mul (by norm_num) hq0.ne'
  have hfirst : 1 ≤ Real.log (2 * q) / Real.log 2 := by
    rw [le_div_iff₀ h2]
    rw [hlog]
    linarith
  have hsecond : Real.log q ≤ Real.log (2 * q) := by rw [hlog]; linarith
  calc
    _ ≤ Real.log (2 * q) / Real.log 2 + Real.log (2 * q) := add_le_add hfirst hsecond
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaGrowthStrip
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma-factor growth in the narrow strip around the contour

The upper bounds use only Euler's integral and reflection. They are needed
for the horizontal-edge logarithmic-derivative estimate.
-/

namespace Ostmann

open Complex

theorem gammaReal_inverse_eq (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  rw [Complex.Gammaℝ_def, mul_inv]
  congr 1
  rw [← Complex.cpow_neg]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialProtectedTarget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two cutoff centers fit the protected target -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def movingInitialGapTotal (k : ℕ) (Bs BD Bz L : ℝ) : ℝ :=
  spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L) +
    ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tailCellLinearRate (a C : ℝ) : ℝ :=
  20 + |4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a|

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSmallCellList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three top labels and two labels of each compensation type -/
namespace Ostmann

def initialSmallCellList (top : ℕ) (centers : List ℕ) : List ℕ :=
  List.replicate 3 top ++ centers.flatMap (fun j => [j, j])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellPriors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialRegularPrimeRange (L : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊Real.exp (Real.exp ((11 / 1000 : ℝ) * L))⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeQuadraticUniqueness
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The only nonprincipal quadratic character at a prime -/
namespace Ostmann

noncomputable def complexJacobiCharacter (p : ℕ) [NeZero p] : DirichletCharacter ℂ p :=
  (jacobiCharacterInt p).ringHomComp (Int.castRingHom ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensHarmonicBands
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens' second theorem on the iterated-logarithm band

F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
Math. 78 (1874), 46–62, second theorem. We only require its weaker bounded
error consequence `sum_{p≤Q} 1/p = log log Q + O(1)`. The pinned PNT library
states this specialization as `Mertens.sum_prime_div_eq_log_log`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def logLogPrimeBand (L : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ \
    Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FavorableMassAlternative
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Failure of favorable mass forces a large sparse balanced prime set -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def favorableTransformPrimes (P : Finset ℕ) (S : ℕ → Finset ℕ)
    (γ : ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter (fun p => (p : ℝ) / 3 ≤ (S p).card ∧
    ((S p).card : ℝ) ≤ 2 * p / 3 ∧ δ ≤ γ p)

noncomputable def sparseTransformPrimes (P : Finset ℕ) (S : ℕ → Finset ℕ)
    (γ : ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter (fun p => (p : ℝ) / 3 ≤ (S p).card ∧
    ((S p).card : ℝ) ≤ 2 * p / 3 ∧ γ p < δ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeReciprocalLogBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform reciprocal-log prime budget from the recorded Mertens input -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeReciprocalLogSum (Q : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Q, 1 / ((p : ℝ) * Real.log p)

noncomputable def primeReciprocalLogConstant (C : ℝ) : ℝ :=
  primeReciprocalLogSum ⌊Real.exp 1⌋₊ + 2 * (1 + Real.log 2 + 2 * max C 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMixedNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization cost of the two original mixed half-lists -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfNormalizer (b d r : ℕ) (a L g : ℝ) :
    Fin ((b + (d + r)) + 1) → ℝ :=
  Fin.cons (Real.exp (g * L))
    (Fin.append (fun _ : Fin b => (a * L)⁻¹)
      (Fin.append (fun _ : Fin d => (a * L)⁻¹) (fun _ : Fin r => Real.exp (2 * L))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original spectator coordinates without changing their law -/
namespace Ostmann
open scoped Classical BigOperators

/-- In one original half-list, separate the spectator block from the giant,
bulk and fixed cell blocks. -/
def initialSpectatorSlotEquiv (b d r : ℕ) :
    Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r)) ≃ Fin (b + (d + r) + 1) where
  toFun
    | .inl i => ((i.castAdd r).natAdd b).succ
    | .inr (.inl _) => 0
    | .inr (.inr (.inl i)) => (i.castAdd (d + r)).succ
    | .inr (.inr (.inr i)) => ((i.natAdd d).natAdd b).succ
  invFun := Fin.cases (.inr (.inl ())) (fun j =>
    Fin.addCases (fun i => .inr (.inr (.inl i)))
      (fun j => Fin.addCases (fun i => .inl i) (fun i => .inr (.inr (.inr i))) j) j)
  left_inv := by
    intro i
    rcases i with i | (i | (i | i)) <;> simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

noncomputable def initialHalfAssemble {P : Type*} (b d r : ℕ)
    (spectator : Fin d → P) (retained : Unit ⊕ (Fin b ⊕ Fin r) → P) :
    Fin (b + (d + r) + 1) → P :=
  Sum.elim spectator retained ∘ (initialSpectatorSlotEquiv b d r).symm

def initialTwoHalfTupleEquiv (P : Type*) (n : ℕ) :
    (Fin n → P) × (Fin n → P) ≃ (Fin (n + n) → P) where
  toFun x := Fin.append x.1 x.2
  invFun x := (fun i => x (i.castAdd n), fun i => x (Fin.natAdd n i))
  left_inv := by
    intro x
    apply Prod.ext <;> funext i
    · exact Fin.append_left x.1 x.2 i
    · exact Fin.append_right x.1 x.2 i
  right_inv := by intro x; exact Fin.append_castAdd_natAdd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LogCellFamilyWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete integer cell families around a real prime block -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def logBlockCenters (lo hi : ℝ) : Finset ℤ :=
  Finset.Icc (⌊lo⌋ - 1) (⌈hi⌉ + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrimePowerRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from the fixed smooth mean -/
namespace Ostmann
open scoped Classical BigOperators

 theorem nonprime_mangoldt_sum (X : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n) = Chebyshev.psi X - Chebyshev.theta X := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊)
    Nat.Prime (fun n => ArithmeticFunction.vonMangoldt n)
  have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n) = Chebyshev.theta X := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  rw [hp] at h
  change Chebyshev.theta X + _ = Chebyshev.psi X at h
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeFamilyEnumeration
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The indexed prime coordinates of a finite selected set -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeFamilyEnumeration (P : Finset ℕ) (i : Fin P.card) : ℕ :=
  ((P.equivFin).symm i).val

noncomputable def finitePrimeFamilyEmbedding {m : ℕ} (P : Finset ℕ)
    (p : Fin m → ℕ) (hinj : Function.Injective p) (hmem : ∀ i, p i ∈ P) :
    Fin m ↪ Fin P.card where
  toFun i := P.equivFin ⟨p i, hmem i⟩
  inj' := by
    intro i j hij
    apply hinj
    exact congrArg (fun x : P => x.val) ((P.equivFin).injective hij)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalCoordinates
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying actual integer sets with the interval coordinates of the sieve -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def integerIntervalIndices (A : Finset ℤ) (J : ℤ) (M : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => J + (i.val : ℤ) ∈ A)

def integerIntervalPoint (J : ℤ) {M : ℕ} (i : Fin M) : ℤ := J + (i.val : ℤ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialProductWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product center of the original selected mixed prior -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedInitialLogCenter (G Y cb cd : ℝ) (top : ℕ)
    (centers : List ℕ) : ℝ :=
  2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - Y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedRegularInitialAmplitude
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Poisson bounds on the actual support of the original prior -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def priorSupportedWeight {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (w : (Fin n → A) → ℂ) (x : Fin n → A) : ℂ :=
  if productPrior μ x = 0 then 0 else w x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preserving the original retained prior in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

def initialGiantAssignment (P : Type*) : P × P ≃ (Bool → P) where
  toFun x b := if b then x.1 else x.2
  invFun x := (x true, x false)
  left_inv := by intro x; rfl
  right_inv := by intro x; funext b; cases b <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact spectator cofactors in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The fixed spectator units are their true cofactors in the spectator list. -/
noncomputable def initialSpectatorCofactor {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : I) :
    (ZMod (q i))ˣ :=
  ZMod.unitOfCoprime (tupleCofactor q i) (tupleCofactor_coprime q hc i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant and regular tests under the moving-slot reindexing -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialGiantFlag (b d r : ℕ) :
    Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → Bool :=
  let a : Fin (b + (d + r) + 1) → Bool := Fin.cons true (fun _ => false)
  Fin.append a a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeAlphabet
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws are independent of the containing prime alphabet -/
namespace Ostmann
open scoped Classical

def primeAlphabetEmbedding {P Q : Finset ℕ} (h : Q ⊆ P) : Q ↪ P :=
  ⟨fun q => ⟨q.val, h q.property⟩,
    fun _ _ he => Subtype.ext (congrArg (fun p : P => p.val) he)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four-at-a-time compensation cell schedule -/
namespace Ostmann
open scoped Classical

def scheduledSmallLength : List ℕ → ℕ
  | [] => 6
  | _ :: cs => 4 + scheduledSmallLength cs

def scheduledSmallCell (top : ℕ) : (cs : List ℕ) → Fin (scheduledSmallLength cs) → ℕ
  | [] => fun _ => top
  | c :: cs => Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs)

def scheduledSmallCellList (top : ℕ) (cs : List ℕ) : List ℕ :=
  cs.flatMap (fun c => List.replicate 4 c) ++ List.replicate 6 top

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected compensation cells as one common prime-space prior -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedCompensationCenter (centers : List ℕ) (n : ℕ) : ℝ :=
  ((centers.drop n).headD 0 : ℕ) + 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedCompensationPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A total prior extending precisely the used compensation cells

Unused indices reuse the selected top cell. The pivot exponent retains its
original zero default beyond the finite list; no extra transfer is performed.
-/
namespace Ostmann
open scoped Classical BigOperators

def completedCompensationCell (top : ℕ) (cs : List ℕ) (n : ℕ) : ℕ :=
  (cs.drop n).headD top

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSmallAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed positive statistic on the actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

def restrictPrimeSamples {P Q : Finset ℕ} {d : ℕ} (s : Fin d → P)
    (hs : ∀ i, (s i : ℕ) ∈ Q) : Fin d → Q := fun i => ⟨s i, hs i⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledIntegerRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual product separation on the retained initial-coefficient support -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def scheduledPivotBound (G : ℝ) (cs : List ℕ) (n : ℕ) : ℕ :=
  ⌈Real.exp (G + 1 + (2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1))⌉₊

noncomputable def scheduledProductRounding (width : ℝ) (cs : List ℕ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (width + 14 + 4 * cs.length)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnalyticParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed gap constants and a common large depth for the constructed schedule -/
namespace Ostmann
open Filter

noncomputable def scheduledInitialRate : ℝ := 6 * Real.log 2 + 13

noncomputable def scheduledIterationRate : ℝ := scheduledInitialRate + 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SignedBulkGain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the quartet gain after the actual bulk-slot counting loss -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def signedBulkGainTarget (n : ℕ) (C D : ℝ) : ℝ :=
  Real.exp (-(C + D + (2 ^ n : ℕ) * Real.log 4))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenPrimeDeletions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite primes excluded after freezing the nonbulk coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def frozenPrimeDeletions {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : {i : σ // i ∉ Set.range slot} => base i) ∪ outside.toFinset

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeMaskExtension
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing the regular mask family without changing sampled primes -/
namespace Ostmann
open scoped Classical

noncomputable def primeMaskExtension (P : Finset ℕ)
    (sets : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) : Finset (ZMod p) :=
  if p ∈ P then sets p else {0}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantLiveSupport
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing zero-weight giant labels preserves the full original law -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantLivePrimes (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : Finset ℕ :=
  P.filter (fun p => φ (Real.log p - G) ≠ 0)

theorem smoothGiantLivePrimes_subset (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) :
    smoothGiantLivePrimes P φ G ⊆ P := Finset.filter_subset _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected cells satisfy the original finite transfer step -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def scheduledChildBound (V : ℕ → ℕ) (j : ℕ) : ℕ := V (j - 1)
noncomputable def scheduledPivotCaps (G : ℝ) (cs : List ℕ) (j : ℕ) : ℕ :=
  scheduledPivotBound G cs (j - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledComparisonCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cutoffs below the actual spectator band and above all finite frequencies -/
namespace Ostmann
open Filter

noncomputable def scheduledComparisonCutoff (L : ℝ) : ℕ :=
  ⌈Real.exp (Real.exp ((2 / 10000 : ℝ) * L))⌉₊

noncomputable def scheduledComparisonPrimeLo (L : ℝ) : ℕ :=
  ⌊Real.exp (Real.exp ((7 / 10000 : ℝ) * L))⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledComparisonCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexity of the actual bounded cell schedule and spectator list -/
namespace Ostmann
open Filter

noncomputable def scheduledComparisonCount (k m : ℕ) : ℕ :=
  2 + 2 ^ k * (10 + 4 * k + m) + 4 * k * 2 ^ k + m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledDiagonalLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The deterministic small-slot counts in the finite diagonal family -/
namespace Ostmann

noncomputable def scheduledTailLength (k n : ℕ) : ℕ := 6 + 4 * (k - (n + 1))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSpectatorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

def frozenInitialSpectatorPrimes {P : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (i : Fin (d + d)) : ℕ := ((Fin.append sl sr i : P) : ℕ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellTiers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tier labels for the actual disjoint compensation cells -/
namespace Ostmann
open scoped Classical

noncomputable def finitePrimeCellTier {k : ℕ} (Q : Fin k → Finset ℕ)
    (fallback : ℕ) (p : ℕ) : ℕ :=
  if h : ∃ i, p ∈ Q i then (Classical.choose h : Fin k) else fallback

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_FiniteCRT
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

noncomputable def separatingPrime (M a : ℕ) : ℕ := Nat.nth Nat.Prime (M + a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensFromFirst
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded second Mertens estimate from the first

Only bounded error is needed in the Ostmann application. Partial summation
therefore makes the second prime-sum input a consequence of the first.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable def logPrimeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszUnsmoothing
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering sharp positive counts from the integrated count -/

namespace Ostmann

open scoped BigOperators

theorem positivePart_step_lower (x y h : ℝ) (hh : 0 ≤ h) :
    (if y ≤ x then h else 0) ≤ max (x + h - y) 0 - max (x - y) 0 := by
  split_ifs with hy
  · rw [max_eq_left (by linarith : 0 ≤ x + h - y), max_eq_left (sub_nonneg.mpr hy)]
    linarith
  · have hm : max (x - y) 0 ≤ max (x + h - y) 0 := max_le_max_right 0 (by linarith)
    linarith

theorem positivePart_step_upper (x y h : ℝ) (hh : 0 ≤ h) :
    max (x + h - y) 0 - max (x - y) 0 ≤ (if y ≤ x + h then h else 0) := by
  split_ifs with hy
  · by_cases hxy : y ≤ x
    · rw [max_eq_left (by linarith : 0 ≤ x + h - y), max_eq_left (sub_nonneg.mpr hxy)]
      linarith
    · rw [max_eq_left (sub_nonneg.mpr hy), max_eq_right (by linarith : x - y ≤ 0)]
      linarith
  · rw [max_eq_right (by linarith : x + h - y ≤ 0), max_eq_right (by linarith : x - y ≤ 0)]
    norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszSmoothRecovery
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive unsmoothing with a twice differentiable main term -/

namespace Ostmann

open Set
open scoped BigOperators

theorem smooth_main_remainder_pair (F f f' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hF : ∀ t ∈ Icc (x - h) (x + h), HasDerivAt F (f t) t)
    (hf : ∀ t ∈ Icc (x - h) (x + h), HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (x - h) (x + h), |f' t| ≤ 2) :
    |F (x + h) - F x - h * f x| ≤ 2 * h ^ 2 ∧
      |F x - F (x - h) - h * f x| ≤ 2 * h ^ 2 := by
  let K := Icc (x - h) (x + h)
  have hx : x ∈ K := ⟨by linarith, by linarith⟩
  have hp : x + h ∈ K := ⟨by linarith, le_rfl⟩
  have hm : x - h ∈ K := ⟨le_rfl, by linarith⟩
  have hlocal (t : ℝ) (ht : t ∈ K) : ‖f t - f x‖ ≤ 2 * h := by
    have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hf y hy).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hb y hy)
      (convex_Icc (x - h) (x + h)) hx ht
    have ha : |t - x| ≤ h := abs_le.mpr ⟨by have := ht.1; linarith, by have := ht.2; linarith⟩
    simpa only [Real.norm_eq_abs] using hl.trans (mul_le_mul_of_nonneg_left ha (by norm_num))
  let G : ℝ → ℝ := fun t => F t - f x * t
  have hg (t : ℝ) (ht : t ∈ K) : HasDerivAt G (f t - f x) t := by
    have hh := (hF t ht).sub ((hasDerivAt_id t).const_mul (f x))
    change HasDerivAt (fun y => F y - f x * y) (f t - f x * 1) t at hh
    simpa only [mul_one] using hh
  have hplus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hlocal (convex_Icc (x - h) (x + h)) hx hp
  have hminus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hlocal (convex_Icc (x - h) (x + h)) hm hx
  have hep : G (x + h) - G x = F (x + h) - F x - h * f x := by dsimp [G]; ring
  have hem : G x - G (x - h) = F x - F (x - h) - h * f x := by dsimp [G]; ring
  rw [hep, Real.norm_eq_abs, show x + h - x = h by ring, Real.norm_eq_abs,
    abs_of_pos hh] at hplus
  rw [hem, Real.norm_eq_abs, show x - (x - h) = h by ring, Real.norm_eq_abs,
    abs_of_pos hh] at hminus
  exact ⟨by nlinarith, by nlinarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntegratedThetaMain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated principal and exceptional main term for positive unsmoothing -/

namespace Ostmann

noncomputable def integratedThetaMain (φ χ β x : ℝ) : ℝ :=
  (x ^ 2 / 2 - χ * x ^ (β + 1) / (β * (β + 1))) / φ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaLocalFactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the actual local zeta factors in the logarithmic-derivative bound -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zeta_local_log_budget : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    352 * (Real.log (96 * (|t| + 2) ^ 2) +
      (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) ≤
        C * Real.log (|t| + 2) := by
  let D := 1 + Real.log 6 / Real.log (7 / 6 : ℝ)
  let E := Real.log 96 / Real.log 2 + 2
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨352 * (D * E + 1 / Real.log 2), by positivity, ?_⟩
  intro t
  let L := Real.log (|t| + 2)
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ h2).mpr (by simpa using hL)
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * L := by
    have hh := mul_le_mul_of_nonneg_left hone h96.le
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hlog : Real.log (96 * (|t| + 2) ^ 2) = Real.log 96 + 2 * L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have he : Real.log (96 * (|t| + 2) ^ 2) ≤ E * L := by
    rw [hlog]
    dsimp [E]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he hD.le
  have hform : Real.log (96 * (|t| + 2) ^ 2) +
      (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 =
        D * Real.log (96 * (|t| + 2) ^ 2) := by dsimp [D]; ring
  rw [hform]
  change _ ≤ 352 * (D * E + 1 / Real.log 2) * L
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay of the principal Riesz error -/

namespace Ostmann

open Filter

theorem principal_riesz_height_log_bound (y : ℝ) (hy : 5 ≤ y) :
    0 < Real.log (Real.exp y + 4) + 1 ∧ Real.log (Real.exp y + 4) + 1 ≤ 3 * y := by
  have he : 4 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hlog : 0 ≤ Real.log (Real.exp y + 4) := Real.log_nonneg (by linarith)
  refine ⟨by linarith, ?_⟩
  have hh : Real.log (Real.exp y + 4) ≤ Real.log 2 + y := by
    calc
      _ ≤ Real.log (2 * Real.exp y) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszNearby
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integrated errors at the nearby points used for unsmoothing -/

namespace Ostmann

open Complex

theorem sqrt_log_nearby_lower (X Y : ℝ) (hX : 4 ≤ X) (hY : X / 2 ≤ Y) :
    Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log Y) := by
  have hXp : 0 < X := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hsq : X ≤ Y ^ 2 := by nlinarith
  have hl := Real.log_le_log hXp hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith [Real.sq_sqrt (Real.log_nonneg (show 1 ≤ X by linarith)),
    Real.sq_sqrt (Real.log_nonneg hY1), Real.sqrt_nonneg (Real.log X),
    Real.sqrt_nonneg (Real.log Y)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSizePrimeBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary dyadic prime counts used in the summand-size argument -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

noncomputable def sizePrimeBand (Q : ℕ) : Finset ℕ := Nat.primesLE (2 * Q) \ Nat.primesLE Q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_BoundedSieveSubsets
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Euler weights lie at the original integer sieve level -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def boundedSieveSubsets (P : Finset ℕ) (Q : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun U : Finset ℕ => (∏ p ∈ U, p) ≤ Q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftMertensWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens bounds for the actual fixed-shift Euler weights -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

noncomputable def fixedShiftPrimeSet (p₀ R : ℕ) : Finset ℕ :=
  Nat.primesLE R \ Nat.primesLE p₀

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftResidues
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact forbidden classes of finitely many distinct shifts -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def finiteShiftAllowed (B : Finset ℕ) (p : ℕ) : Finset (ZMod p) :=
  ((Finset.range p).image fun r : ℕ => (r : ZMod p)) \
    (B.image fun b : ℕ => -(b : ZMod p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

noncomputable def cosecantKernel (x y : ℝ) : ℝ := (Real.sin (Real.pi * (x - y)))⁻¹
noncomputable def cotangentKernel (x y : ℝ) : ℝ :=
  Real.cos (Real.pi * (x - y)) / Real.sin (Real.pi * (x - y))

@[simp] theorem cosecantKernel_self (x : ℝ) : cosecantKernel x x = 0 := by
  simp [cosecantKernel]

@[simp] theorem cotangentKernel_self (x : ℝ) : cotangentKernel x x = 0 := by
  simp [cotangentKernel]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantDistanceBound
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

noncomputable def cosecantRowWeight (t : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * t) ^ 2 +
    2 * |Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ^ 2|

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CircleSeparatedPoints
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredCircleRemainder (t : ℝ) : ℝ := t - (⌊t + 1 / 2⌋ : ℤ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantMatrix
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def imaginaryKernelMatrix (h : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of (fun s t => Complex.I * (h s t : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantHilbertBound
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cosecantMatrix (x : ι → ℝ) : Matrix ι ι ℂ :=
  imaginaryKernelMatrix (fun s t => cosecantKernel (x s) (x t))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveGeometricKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

noncomputable def sieveHalfPhase (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem sieveHalfPhase_zero : sieveHalfPhase 0 = 1 := by simp [sieveHalfPhase]

@[simp] theorem sieveHalfPhase_norm (t : ℝ) : ‖sieveHalfPhase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveDualEnergy
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def twistedCosecantSum (x : ι → ℝ) (b : ι → ℂ) (L : ℝ) : ℂ :=
  ∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
    (cosecantKernel (x s) (x t) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedAdditiveSieve
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

noncomputable def sievePhaseMatrix {ι : Type*} (x : ι → ℝ) (M : ℕ) (J : ℝ) :
    Matrix ι (Fin M) ℂ :=
  Matrix.of (fun s n => sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NaturalPrimeSupportSieve
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The support sieve for actual natural-number summand tails -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def naturalIntervalSet (S : Finset ℕ) (N : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun a => a.val ∈ S

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExponentialSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential cutoffs for the two-length summand comparison -/

namespace Ostmann

open Filter

noncomputable def exponentialSample (t : ℕ) : ℕ := ⌈Real.exp (t : ℝ)⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive kernel of a pair of odd squarefree denominators

Writing `d = gcd n₁ n₂`, the product character has squarefree kernel
`(n₁/d)(n₂/d)` and the remaining factor is precisely the coprimality mask
modulo `d`. This is the arithmetic decomposition in Heath-Brown (1995), §3.
-/

namespace Ostmann

def quadraticPairKernel (n₁ n₂ : ℕ) : ℕ :=
  (n₁ / n₁.gcd n₂) * (n₂ / n₁.gcd n₂)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDivisibility
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed divisor from the actual quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisibilityCoeff (s : ℕ) (b : ℕ → ℂ) (r : ℕ) : ℂ :=
  if s.Coprime r then b (s * r) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerCancellation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Euler cancellation of the two quadratic Poisson main terms

This is the finite arithmetic identity in Heath-Brown (1995), §7, Lemma 5.
The monomial index records the integer in each character, not a formal degree.
-/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

noncomputable def quadraticMonomial (k : ℕ) : ArithmeticFunction (MonoidAlgebra ℤ ℕ) :=
  ⟨fun n => if n = 0 then 0 else single (n ^ k) 1, by simp⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerCover
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite Euler product covering the original small squarefree indices -/

namespace Ostmann

open scoped Classical BigOperators

def quadraticEulerPrimes (D K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ¬p ∣ D)

def quadraticEulerCover (D K : ℕ) : ℕ :=
  ∏ p ∈ quadraticEulerPrimes D K, p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussMultiplier
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total quadratic Gauss multipliers and their elementary reciprocity sign -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticGaussMultiplier (n : ℕ) : ℂ :=
  if h : n = 0 then 0 else @jacobiGaussPhase n ⟨h⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussBilinear
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the Gauss factor in the actual divisor bilinear sum -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticGaussLeft (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * quadraticGaussMultiplier n

noncomputable def quadraticGaussRight (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  b n * conj (quadraticGaussMultiplier n)

noncomputable def quadraticThreeClass (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n % 4 = 3 then a n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFourierSeparation
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic Fourier separation of a smooth pair weight -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

noncomputable def quadraticLogModulate (u : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * realAdditivePhase (u * Real.log n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete smooth logarithmic cutoff for the quadratic Poisson kernel -/

namespace Ostmann

open scoped SchwartzMap

noncomputable def quadraticLogBump : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

noncomputable def quadraticLogWindow (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) : 𝓢(ℝ, ℂ) :=
  (show HasCompactSupport (fun u : ℝ =>
      (quadraticLogBump u : ℂ) * ρ (X * Real.exp (-u))) from
    (quadraticLogBump.hasCompactSupport.comp_left
      (show Complex.ofReal 0 = 0 by simp)).mul_right).toSchwartzMap (by
        apply ContDiff.mul
        · exact Complex.ofRealCLM.contDiff.comp quadraticLogBump.contDiff
        · exact (ρ.smooth ⊤).comp (by fun_prop))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogDerivative
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit derivatives of the compact logarithmic Poisson cutoff -/

namespace Ostmann

open LineDeriv
open scoped SchwartzMap

noncomputable def quadraticSmoothLogCutoff : 𝓢(ℝ, ℂ) :=
  (quadraticLogBump.hasCompactSupport.comp_left
    (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp quadraticLogBump.contDiff)

noncomputable def quadraticEulerDerivative (ρ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
    (SchwartzMap.derivCLM ℂ ℂ ρ)

noncomputable def quadraticLogFirst (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) : ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u * ρ (X * Real.exp (-u)) -
    quadraticSmoothLogCutoff u * quadraticEulerDerivative ρ (X * Real.exp (-u))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogDecay
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Schwartz decay on the compact logarithmic window -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap

noncomputable def quadraticLogDecayConstant (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) : ℝ :=
  Real.exp 3 ^ A * SchwartzMap.seminorm ℝ A 0 ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogFourierEnvelope
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Fourier majorant for varying Poisson parameters -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

noncomputable def quadraticFourierEnvelope (u : ℝ) : ℝ := (1 + ‖u‖) ^ (-(2 : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticHalfReflection
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed half-reflection needed for square-root Poisson weights -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def quadraticHalfReflection (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (-1 / 2 : ℝ) (by norm_num))) f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticLogRootKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root weight in the second Poisson transform -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def quadraticLogRootKernel (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) : 𝓢(ℝ, ℂ) :=
  (quadraticHalfReflection (quadraticLogWindow ρ (X * N))).compSubConstCLM ℂ (2 * Real.log N)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquareCompose
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-composed Schwartz test for the second Poisson step -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem quadratic_square_proper {a : ℝ} (ha : 1 ≤ |a|) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖a * x ^ 2‖) ^ k := by
  refine ⟨1, 1, ?_⟩
  intro x
  simp only [pow_one, one_mul, Real.norm_eq_abs, abs_mul, abs_pow]
  have hm : |x| ^ 2 ≤ |a| * |x| ^ 2 := le_mul_of_one_le_left (sq_nonneg _) ha
  nlinarith [sq_nonneg (|x| - 1), sq_nonneg |x|]

noncomputable def quadraticSquareCompose (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => a * x ^ 2) (by fun_prop)
    (quadratic_square_proper ha) ρ

noncomputable def quadraticFourierSquare (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) : 𝓢(ℝ, ℂ) :=
  quadraticSquareCompose (𝓕 ρ) a ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDampedFresnel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian regularization of the quadratic Fourier integral -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def quadraticGaussianDamping (ε x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi * ε : ℝ) : ℂ) * (x : ℂ) ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelCoefficient
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the regularized quadratic Gaussian coefficient -/

namespace Ostmann

open MeasureTheory Filter
open scoped Topology

noncomputable def quadraticFresnelCoefficient (ε a t : ℝ) : ℂ :=
  ((1 : ℂ) / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) ^ (1 / 2 : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelMain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact main term of the second quadratic Poisson transform -/

namespace Ostmann

open MeasureTheory Set
open scoped SchwartzMap FourierTransform

noncomputable def quadraticFresnelPhase (a : ℝ) : ℂ :=
  if 0 < a then 1 - Complex.I else 1 + Complex.I

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeMain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact main term in coprime Poisson summation -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticCoprimeRemainder (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
    ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticHybridPoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact passage between the physical and Fourier lattice tails -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticLatticeTail (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else ψ ((n : ℝ) * Y)

noncomputable def quadraticLatticeWindow (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)

noncomputable def quadraticLatticeOuter (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) (L : ℕ) : ℂ :=
  ∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTruncatedPoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full finite Poisson truncation, with every correction retained -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticPoissonError (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X U V : ℝ) (L : ℕ) : ℂ :=
  (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)) +
  (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
    (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)) +
  ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeOuter (𝓕 ψ) (X / d) L

noncomputable def quadraticPoissonCore (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X U V : ℝ) (L : ℕ) : ℂ :=
  ((X : ℂ) * q.totient / q) * 𝓕 ψ 0 -
  ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
  𝓕 ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
  ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeWindow (𝓕 ψ) (X / d) L

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondPoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson formula for the actual quadratic Fourier test -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondPoissonCore (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) : ℂ :=
  ((((X : ℂ) * q.totient / q) *
      ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2))) -
    𝓕 ρ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ)) -
    ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
    ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) / 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-root scale in the second Poisson transform -/

namespace Ostmann

noncomputable def quadraticSecondScale (M : ℝ) (e q b : ℕ) : ℝ :=
  Real.sqrt ((e : ℝ) * q / (M * b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondCutoffs
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One pair-independent Poisson cutoff on a dyadic block -/

namespace Ostmann

noncomputable def quadraticSecondLower (X₀ J : ℝ) : ℝ := X₀ / (2 * J)
noncomputable def quadraticSecondUpper (X₀ J : ℝ) : ℝ := 2 * X₀ * J
noncomputable def quadraticSecondWindow (J : ℝ) : ℕ := ⌈16 * J ^ 2⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelPoisson
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-squarefree-kernel Poisson formula -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallSquareTest (ρ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  quadraticSquareCompose ρ 1 (by norm_num)

noncomputable def quadraticSmallPoissonCore (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (X U V : ℝ) (L : ℕ) : ℂ :=
  (X : ℂ) * ((q.totient : ℂ) / q) * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) -
  (X : ℂ) * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) / d) +
  (X : ℂ) / 2 *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (X / d) L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelScale
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common cutoffs for the original small-squarefree-kernel block -/

namespace Ostmann

open scoped SchwartzMap BigOperators

noncomputable def quadraticSmallScale (M : ℝ) (b : ℕ) : ℝ := Real.sqrt (M / b)

noncomputable def quadraticSmallDyadicCore (ρ : 𝓢(ℝ, ℂ))
    (M B J : ℝ) (q b : ℕ) : ℂ :=
  quadraticSmallPoissonCore q ρ (quadraticSmallScale M b)
    (quadraticSecondLower (Real.sqrt (M / B)) J)
    (quadraticSecondUpper (Real.sqrt (M / B)) J) (quadraticSecondWindow J)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTotientKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact totient-weighted kernel after removal of the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticTotientCoeff (D s : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if D.Coprime n ∧ s.Coprime n then (Nat.totient n : ℂ) / n * b (D * n) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRootCharacter
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the original character weights in the main-term difference -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticRootCharacter (q w : ℕ) : ℂ :=
  (jacobiSym (w : ℤ) q : ℂ) / (Real.sqrt (w : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorDyadicPartition
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint divisor blocks, including the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorDyadicBlock (Q j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter (fun d => Nat.log 2 (d - 1) = j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionCutoffGeometry
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency-dependent cutoffs lie in fixed divisor bands -/

namespace Ostmann

noncomputable def quadraticCorrectionBase (M H : ℝ) (e b : ℕ) : ℝ :=
  Real.sqrt ((e : ℝ) * H ^ 2 / (M * b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthBandBalance
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common band budget has the required low/high recursive size -/

namespace Ostmann

noncomputable def quadraticGrowthBandBudget (F Y N D E : ℝ) : ℝ :=
  8 * F * Real.sqrt D * (Y + Real.sqrt (Y * N) + N / Real.sqrt D) * E

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthDivisorBudget
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual shorter sieve matrices supply every divisor-band budget -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticGrowthCutoff (C ε ξ : ℝ) (B N i : ℕ) : ℝ :=
  C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / (2 ^ i : ℕ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyTwist
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing signed square factors into the original coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticFrequencyTwist (a : ℤ) (c : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if c.Coprime n then (jacobiSym a n : ℂ) * v n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSqrtCoefficients
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-root denominator in the first Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticSqrtNormalize (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  v n / (Real.sqrt (n : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelWindow
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained small-kernel Fourier window with its actual reciprocal weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallFourierBound (ρ : 𝓢(ℝ, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (𝓕 (quadraticSmallSquareTest ρ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerAtTwo
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factor at two in the first quadratic Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticMoebiusRoot (q : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℂ) * quadraticRootCharacter q n, by simp⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelSigns
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four signed-square classes in the first Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFresnelSignSum (q : ℕ) : ℂ :=
  ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
    (jacobiSym a q : ℂ) * quadraticFresnelPhase a /
      (Real.sqrt |(a : ℝ)| : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondDyadic
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson estimate with the literal dyadic square argument -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondDyadicCore (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M B N J : ℝ) (e q b : ℕ) : ℂ :=
  let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
  quadraticSecondPoissonCore q ρ a ha (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) (quadraticSecondWindow J)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondError
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-transform error after the original Gauss normalization -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondDyadicError (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M B N J : ℝ) (e q b : ℕ) : ℂ :=
  (∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
    𝓕 ρ (a * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))) -
      quadraticSecondDyadicCore ρ a ha M B N J e q b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondSignedCore
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full signed second Poisson core, at the original first-transform weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

def quadraticPoissonSigns : Finset ℤ := {1, -1, 2, -2}

theorem quadraticPoissonSigns_abs {a : ℤ} (ha : a ∈ quadraticPoissonSigns) :
    1 ≤ |(a : ℝ)| := by
  simp only [quadraticPoissonSigns, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTransformedMain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transformed first main term is the original comparison term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticDualMainCoefficient (M : ℝ) (D q b : ℕ) : ℂ :=
  quadraticGaussMultiplier q *
    (∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
      (((M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) : ℝ) : ℂ) *
        ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
          (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
            (Real.sqrt |(a : ℝ)| : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSecondMain
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson core has exactly the original main term and corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondCorrection (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) : ℂ :=
  (-𝓕 ρ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ)) -
    ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
    ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) / 2

noncomputable def quadraticSecondDyadicCorrection (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (M H J : ℝ) (e q b : ℕ) : ℂ :=
  let X₀ := Real.sqrt ((e : ℝ) * H ^ 2 / (M * b))
  quadraticSecondCorrection q ρ a ha (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) (quadraticSecondWindow J)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdRangeBridge
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A genuine dyadic range after removing the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticRangeCoeff (L : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ≤ L then v n else 0

noncomputable def quadraticGcdBlockSize (R D : ℕ) : ℕ := ⌈(R : ℝ) / D⌉₊

noncomputable def quadraticGcdBlockCoeff (R D : ℕ) (v : ℕ → ℂ) : ℕ → ℂ :=
  quadraticRangeCoeff ((2 * R) / D) (quadraticDivisibilityCoeff D v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionMoment
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The correction envelope uses only the original coefficient energy -/

namespace Ostmann

noncomputable def quadraticCorrectionScalar (C ε ξ M J : ℝ) (N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * J * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
    ((Nat.log 2 Q + 2 : ℕ) : ℝ) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallEnvelope
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common bound for the two literal small-kernel corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticSmallCorrectionScalar (C ε ξ M J : ℝ) (E N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + 8 * E * J * N))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionPolynomial
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and logarithmic costs of the original correction parameters -/

namespace Ostmann

noncomputable def quadraticCorrectionLogFactor (ε : ℝ) (N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * (4 * (K : ℝ) * N) ^ ε

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdSum
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform summation of the bounded common divisors -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDescentScale (ξ : ℝ) (M N K : ℕ) : ℝ :=
  (M : ℝ) + N + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * N / Real.sqrt K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFiniteDescent
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite length of the actual coefficient descent -/

namespace Ostmann

open scoped Classical BigOperators

def quadraticDescentBudget (A B : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => A + B * quadraticDescentBudget A B r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDescentCutoff
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rounded cutoff that terminates the descent in a fixed number of steps -/

namespace Ostmann

noncomputable def quadraticDescentCutoff (N r : ℕ) : ℕ :=
  ⌈4 * (N : ℝ) ^ (1 / (r : ℝ))⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBalancedKernel
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rounded kernel cutoff in the long-row range -/

namespace Ostmann

noncomputable def quadraticBalancedKernel (η : ℝ) (M N : ℕ) : ℕ :=
  ⌈8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) / M⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPrimeTwist
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime dilation on the literal quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticPrimeTwist (p : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  v n * (jacobiSym (p : ℤ) n : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBalancedExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The balanced exponent and an explicit enlarged row cutoff -/

namespace Ostmann

noncomputable def quadraticImprovedExponent (ξ : ℝ) : ℝ := 2 - 1 / ξ

noncomputable def quadraticDilationCutoff (C δ p : ℝ) (M N : ℕ) : ℕ :=
  ⌈C * (2 * (M : ℝ) * N) ^ δ * max 1 ((N : ℝ) ^ p / M)⌉₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Heath-Brown's quadratic large sieve from the proved exponent descent -/

namespace Ostmann

noncomputable def quadraticSieveExponent (r : ℕ) : ℝ := 1 + 1 / ((r : ℝ) + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityLocalizedPolynomial
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier localization for finite Dirichlet polynomials -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

noncomputable def densityLocalizedPolynomial {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) : 𝓢(ℝ, ℂ) :=
  ∑ j, a j • (positiveDilate W h⁻¹ (inv_pos.mpr hh)).compSubConstCLM ℂ (freq j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DigammaTailEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded tail in the sharp positive-strip digamma comparison -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def densityDigammaTerm (z : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable envelope for the completed-square contour -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology

noncomputable def densityGaussianEnvelope (u : ℝ) : ℝ := (1 + u ^ 2) * Real.exp (-(u ^ 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteContourShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifting the actual finite Dirichlet polynomial to a short positive line -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable def densityFiniteMellin (S : Finset ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ n ∈ S, a n / (n : ℂ) ^ w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted square bounds for the Gaussian contour integral -/

namespace Ostmann

open MeasureTheory

noncomputable def densityHalfGaussian (u : ℝ) : ℝ := Real.exp (-(u ^ 2) / 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityGaussianFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gaussian and height integrals for actual character polynomials -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityCharacterPolynomial {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPolynomialDerivative
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit height derivative and its coefficient energy -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityDerivativeCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ)) * a n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorCoefficients
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual truncated Möbius coefficients in the zero detector -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityMobiusCutoff (X n : ℕ) : ℂ :=
  if n ≤ X then (ArithmeticFunction.moebius n : ℂ) else 0

noncomputable def densityDetectorCoefficient (X n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, densityMobiusCutoff X d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityMollifierProduct
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite mollifier times the character L-function -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityMollifierCoefficient {q : ℕ} (X : ℕ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * densityMobiusCutoff X n

noncomputable def densityMollifier {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityVerticalPolynomial
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vertical Dirichlet polynomials with the actual complex powers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityVerticalPoint (σ t : ℝ) : ℂ :=
  (σ : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * t

noncomputable def densityVerticalCoeff (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n / (n : ℂ) ^ (σ : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityAbscissaPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating the actual Dirichlet polynomial in its real part -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def densityAbscissaDerivativeCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  -(Real.log n : ℂ) * a n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common height and conductor cost for the smoothed square -/

namespace Ostmann

open Complex

noncomputable def densityKernelConstant : ℝ :=
  Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2)

noncomputable def densityKernelCost (Q : ℕ) (T c : ℝ) : ℝ :=
  densityKernelConstant * (10 * Q * T) ^ c / c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBalanceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-height parameters in the two zero-detector estimates -/

namespace Ostmann

noncomputable def densityTargetExponent (σ : ℝ) : ℝ := 3 * (1 - σ) / (2 - σ)
noncomputable def densityBalanceExponent (σ : ℝ) : ℝ := 3 / (2 * (2 - σ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityBlockWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable weights for the actual dyadic-square estimates -/

namespace Ostmann

open scoped BigOperators

noncomputable def densityBlockEnergyConstant : ℝ :=
  ∑' j : ℕ, (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorWeight
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact quadratic Riesz weight for detecting actual zeros -/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def densityDetectorWeight (x : ℝ) : ℂ :=
  (max (1 - x) 0 : ℝ) ^ 2 / 2

noncomputable def densityDetectorKernel (s : ℂ) : ℂ :=
  1 / (s * (s + 1) * (s + 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original polynomial alternative as one common coefficient sequence -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

noncomputable def densityPolynomialCoefficient (X : ℕ) (Y : ℝ) (n : ℕ) : ℂ :=
  if X < n then densityDetectorCoefficient X n * densityDetectorWeight (n / Y) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDyadicShells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A disjoint dyadic decomposition of the whole height line -/

namespace Ostmann

open Set Filter
open scoped Topology

noncomputable def densityHeightBall (T : ℝ) (j : ℕ) : Set ℝ :=
  Icc (-((2 : ℝ) ^ j * T)) ((2 : ℝ) ^ j * T)

noncomputable def densityHeightShell (T : ℝ) : ℕ → Set ℝ
  | 0 => densityHeightBall T 0
  | j + 1 => densityHeightBall T (j + 1) \ densityHeightBall T j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityKernelPacking
attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cubic detector kernel on separated ordinates -/

namespace Ostmann

open scoped BigOperators

noncomputable def densityCubicWeight (u : ℝ) : ℝ := 1 / (1 + |u|) ^ 3

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityHeightWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable cubic weights on the dyadic height shells -/

namespace Ostmann

open Set

noncomputable def densityHeightWeight (T x : ℝ) : ℝ := densityCubicWeight (x / T)

noncomputable def densityHeightEnergyConstant (k : ℕ) : ℝ :=
  1 + 2 * ∑' j : ℕ, (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPackedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing translated moments over characterwise separated ordinates -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

noncomputable def densityKernelPackingConstant : ℝ := 256 + 27 * (1 + 4 * Real.pi ^ 2 / 3)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityWeightedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A whole-line weighted moment from compact height moments -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

noncomputable def densityShellBudget (A : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => A
  | j + 1 => 2 * A * ((j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j)

end Ostmann

end OAI
end



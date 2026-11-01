-- Prove2me | Definitions.Def_OAIQ083J001
-- name    : OAIQ083J001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T20:17:49.525695+00:00
-- url     : https://prove2.me/theorems/898e1adf-2115-46c7-9ede-5dbd0d21a9d5
-- title:
--   Definitions bundle OAIQ083J001 of the split of OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1145 declarations of OpenAI's Lean: 870 definitions, 4 inductive types or structures, 3 instances and 268 theorems. The definitions and types are `Erdos970.sigma1Of`, `Erdos970.zetaPartialSum`, `HIntegral`, `HolomorphicOn`, `OAI.Erdos970.ErdosPrimeInputs.MertensStrong.primeProduct`, `OAI.Erdos970.ErdosPrimeInputs.PrimeAbel.errorKernel`, `OAI.Erdos970.ErdosPrimeInputs.PrimeAbel.invLogWeight`, `OAI.Erdos970.ErdosPrimeInputs.PrimeAbel.primeLogWeight`, `OAI.Erdos970.ErdosPrimeInputs.PrimeAbel.reciprocalPrimes`, `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.decay`, `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.tailKernel`, `OAI.Erdos970.ErdosPrimeInputs.PrimeProductOmissions.reducedPrimes`, `OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev.errorScale`, `OAI.Erdos970.ErdosPrimeInputs.SubsetPrimeSieve.euler`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.alternatingChoose`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.blockCorrection`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.blockLower`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.blockUpper`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.coefficientPolynomial`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.hitSet`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionMass`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionRemainder`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionValue`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.momentPolynomial`, `OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives`, `OAI.Erdos970.NumberTheoryLean.BonferroniDensity.densityPolynomial`, `OAI.Erdos970.NumberTheoryLean.BonferroniDensity.elementarySum`, `OAI.Erdos970.NumberTheoryLean.Dickman.identityDifference`, `OAI.Erdos970.NumberTheoryLean.Dickman.primitive`, `OAI.Erdos970.NumberTheoryLean.DickmanDecay.hazard`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.blockChoices`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.correctionCoefficient`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.globalCoefficient`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.intersectionChoices`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.layerCoefficient`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.lowerCoefficient`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.selectedUnion`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.truncatedCoefficient`, `OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.upperCoefficient`, `OAI.Erdos970.NumberTheoryLean.FundamentalBlockEstimate.actualLowerDensity` and 834 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_Fourier`, `Erdos970_PNT1_ComplexAnalysis`, `Erdos970_PNT2_LogDerivative`, `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Fourier`, `Jacobsthal_Analysis_BonferroniDensity`, `Jacobsthal_Estimates_BonferroniBlocks`, `Jacobsthal_Estimates_DisjointBlockExpansion`, `Jacobsthal_Estimates_FundamentalBlockEstimate`, `Jacobsthal_Estimates_SquarefreeHarmonic`, `Jacobsthal_Primes_HighPrimeRemoval`, `Jacobsthal_Primes_LargePrimeDeletion`, `Jacobsthal_Primes_PrimeDensityBlocks`, `Jacobsthal_Primes_PrimeProductOmissions`, `Jacobsthal_Renewal_DickmanFiniteDecay`, `Jacobsthal_Sieve_AlignedPrimeCongruence`, `Jacobsthal_Sieve_EulerProductRatio`, `Jacobsthal_Sieve_IntervalBoundingSieve`, `Jacobsthal_Sieve_ResidueCountDifference`, `JointDickman_Amplification_ActiveFirstForm`, `JointDickman_Amplification_ActiveVolumeMajorant`, `JointDickman_Amplification_ActualArithmeticFluctuation`, `JointDickman_Amplification_ActualArithmeticLimit`, `JointDickman_Amplification_AdditionCutoffScale`, `JointDickman_Amplification_AdditionProgressionInterval`, `JointDickman_Amplification_AffineLocalFactors`, `JointDickman_Amplification_AllLargeHighVanishing`, `JointDickman_Amplification_AmplificationArithmeticFeatures`, `JointDickman_Amplification_AmplificationBoxSupport`, `JointDickman_Amplification_AmplificationDyadicIdentity`, `JointDickman_Amplification_AmplificationEnvelope`, `JointDickman_Amplification_AmplificationFirstForm`, `JointDickman_Amplification_AmplificationMultiplier`, `JointDickman_Amplification_AmplificationRegularityIdentity`, `JointDickman_Amplification_AmplificationReindex`, `JointDickman_Amplification_AmplificationVolumeProducts`, `JointDickman_Amplification_AmplificationWeightBound`, `JointDickman_Amplification_ArithmeticAmplification`, `JointDickman_Amplification_ArithmeticAmplificationBounds`, `JointDickman_Amplification_ArithmeticCandidateSum`, `JointDickman_Amplification_ArithmeticCandidateWeight`, `JointDickman_Amplification_ArithmeticGraphCandidateCount`, `JointDickman_Amplification_ArithmeticGraphPair`, `JointDickman_Amplification_ArithmeticInputs`, `JointDickman_Amplification_ArithmeticOffDiagonalGraph`, `JointDickman_Amplification_ArithmeticPeriod`, `JointDickman_Amplification_ArithmeticProfilePreservation`, `JointDickman_Amplification_ArithmeticRootIdentification`, `JointDickman_Amplification_ArithmeticSquareHits`, `JointDickman_Amplification_AtomicProductMeasure`, `JointDickman_Amplification_AuxiliaryCostLimit`, `JointDickman_Amplification_AuxiliaryLogBins`, `JointDickman_Amplification_AuxiliaryScale`, `JointDickman_Amplification_AveragedRootFluctuation`, `JointDickman_Amplification_BinDecorrelation`, `JointDickman_Amplification_BinJointEvents`, `JointDickman_Amplification_BinLabels`, `JointDickman_Amplification_BinLowFrequency`, `JointDickman_Amplification_BinMarginalGenerating`, `JointDickman_Amplification_BinMarginalInput`, `JointDickman_Amplification_BinMarginalMean`, `JointDickman_Amplification_BinStateExtraction`, `JointDickman_Amplification_CandidateExpectedDegree`, `JointDickman_Amplification_CandidateFiniteCutoff`, `JointDickman_Amplification_CandidateForcedConditional`, `JointDickman_Amplification_CandidateForcedEvent`, `JointDickman_Amplification_CandidateForcedProbability`, `JointDickman_Amplification_CandidateGraphEncoding`, `JointDickman_Amplification_CandidateMatrix`, `JointDickman_Amplification_CandidateModularRoots`, `JointDickman_Amplification_CandidateMultiplicity`, `JointDickman_Amplification_CandidateRepeatEvent`, `JointDickman_Amplification_CandidateRepeatProbability`, `JointDickman_Amplification_CandidateRootGeometry`, `JointDickman_Amplification_CandidateScalarIdentity`, `JointDickman_Amplification_CandidateScalarSum`, `JointDickman_Amplification_CanonicalAffineCost`, `JointDickman_Amplification_CellAverageOscillation`, `JointDickman_Amplification_CoarseFeatureAverage`, `JointDickman_Amplification_CoarseGrid`, `JointDickman_Amplification_ConditionalAdditionProduct`, `JointDickman_Amplification_ConditionedRootErrorLimit`, `JointDickman_Amplification_ConditionedRootFluctuation`, `JointDickman_Amplification_CutBounds`, `JointDickman_Amplification_DiagonalRemoval`, `JointDickman_Amplification_EndpointConditionalMean`, `JointDickman_Amplification_EndpointFourierBounds`, `JointDickman_Amplification_EndpointRowEnvelope`, `JointDickman_Amplification_EndpointRowScale`, `JointDickman_Amplification_FiniteAdditiveOrthogonality`, `JointDickman_Amplification_FiniteConditionalProduct`, `JointDickman_Amplification_FiniteCutoffProfiles`, `JointDickman_Amplification_FiniteExponentialMaximum`, `JointDickman_Amplification_FiniteHoeffding`, `JointDickman_Amplification_FiniteRampApproximation`, `JointDickman_Amplification_FiniteRampMean`, `JointDickman_Amplification_FiniteStatistics`, `JointDickman_Amplification_FirstFormDiagonal`, `JointDickman_Amplification_FirstFormPairs`, `JointDickman_Amplification_FirstPairMass`, `JointDickman_Amplification_FourSubsetFailure`, `JointDickman_Amplification_FullSmallArcModel`, `JointDickman_Amplification_FullSpatialComparison`, `JointDickman_Amplification_GeneratingDegreeExpansion`, `JointDickman_Amplification_GeometricDiscardedArcs`, `JointDickman_Amplification_GeometricDyadicPartition`, `JointDickman_Amplification_GeometricFullModel`, `JointDickman_Amplification_GeometricSampledIntegral`, `JointDickman_Amplification_GraphCandidateDecoding`, `JointDickman_Amplification_GraphEdgeMajorant`, `JointDickman_Amplification_GraphEdgePeriod`, `JointDickman_Amplification_GraphEndpointDensity`, `JointDickman_Amplification_GraphSquareRemoval`, `JointDickman_Amplification_GraphTripleSupport`, `JointDickman_Amplification_HalfArithmetic`, `JointDickman_Amplification_HighExclusiveLocalLaw`, `JointDickman_Amplification_HighLowThinning`, `JointDickman_Amplification_IndependentForcedHits`, `JointDickman_Amplification_IndependentRootMean`, `JointDickman_Amplification_InteriorAmplificationMass`, `JointDickman_Amplification_InteriorRegularity`, `JointDickman_Amplification_LargeAdditionAvailability`, `JointDickman_Amplification_LargeAlternativePairs`, `JointDickman_Amplification_LargeCardinalityPartition`, `JointDickman_Amplification_LargeHighClass`, `JointDickman_Amplification_LargeHighVanishing`, `JointDickman_Amplification_LargeLowAdditionAvailability`, `JointDickman_Amplification_LargeLowClass`, `JointDickman_Amplification_LargeMultiplicityExponent`, `JointDickman_Amplification_LargeNumericAddition`, `JointDickman_Amplification_LiftedRationalEquiv`, `JointDickman_Amplification_LogIntervalApproximation`, `JointDickman_Amplification_LogMassBilinear`, `JointDickman_Amplification_LogOscillatoryTest`, `JointDickman_Amplification_LowAlternativePairs`, `JointDickman_Amplification_LowCardinalityPartition`, `JointDickman_Amplification_LowNumericAdditionClass`, `JointDickman_Amplification_MajorArcFiniteSum`, `JointDickman_Amplification_MajorArcPartition`, `JointDickman_Amplification_ManuscriptAdditionProduct`, `JointDickman_Amplification_MaskedArithmeticFluctuation`, `JointDickman_Amplification_MinorArcApproximation`, `JointDickman_Amplification_MinorArcMeasurable`, `JointDickman_Amplification_MixedThreeFormLocal`, `JointDickman_Amplification_MovingLimit`, `JointDickman_Amplification_MultiplicityRates`, `JointDickman_Amplification_NativeOrientedEvent`, `JointDickman_Amplification_NoChangeConditional`, `JointDickman_Amplification_NumericAdditionClass`, `JointDickman_Amplification_OccupiedRootComparison`, `JointDickman_Amplification_OmissionEnvelope`, `JointDickman_Amplification_OrderedBinTuples`, `JointDickman_Amplification_Ordering`, `JointDickman_Amplification_OrientedProbabilityBound`, `JointDickman_Amplification_OscillatoryTests`, `JointDickman_Amplification_OutsideCandidateMass`, `JointDickman_Amplification_ParameterEstimates`, `JointDickman_Amplification_PolynomialArithmeticFeatures`, `JointDickman_Amplification_PrefixViolationSum`, `JointDickman_Amplification_PrincipalBinRestriction`, `JointDickman_Amplification_ProductComparison`, `JointDickman_Amplification_ProductLogCells`, `JointDickman_Amplification_ProfilePreservation`, `JointDickman_Amplification_PublishedInputs`, `JointDickman_Amplification_PublishedRampProfile`, `JointDickman_Amplification_RamanujanMultiplicative`, `JointDickman_Amplification_RampCutoff`, `JointDickman_Amplification_RampDensity`, `JointDickman_Amplification_RampedCandidate`, `JointDickman_Amplification_RationalCandidateRoots`, `JointDickman_Amplification_RationalUnitRepresentatives`, `JointDickman_Amplification_ReducedArcLifts`, `JointDickman_Amplification_ReducedRationalEquiv`, `JointDickman_Amplification_RegularAlternatives`, `JointDickman_Amplification_RegularAmplificationMass`, `JointDickman_Amplification_RegularPrefixChoices`, `JointDickman_Amplification_RegularTiltAverage`, `JointDickman_Amplification_RegularityChernoffFactors`, `JointDickman_Amplification_RegularityUnionBound`, `JointDickman_Amplification_RegularizedProductWeight`, `JointDickman_Amplification_ReindexedCells`, `JointDickman_Amplification_RestrictedRootMass`, `JointDickman_Amplification_RetainedErrorSum`, `JointDickman_Amplification_ReverseEndpointTest`, `JointDickman_Amplification_ReverseRowEnvelope`, `JointDickman_Amplification_SignedRegularityLoss`, `JointDickman_Amplification_SingularFactor`, `JointDickman_Amplification_SingularSeries`, `JointDickman_Amplification_SmallAdditionCount`, `JointDickman_Amplification_SubsetPairTests`, `JointDickman_Amplification_SubsetThinning`, `JointDickman_Amplification_TailViolationSum`, `JointDickman_Amplification_ThinningRanges`, `JointDickman_Amplification_TiltedAdditionRate`, `JointDickman_Amplification_TrimmedCandidateRoots`, `JointDickman_Amplification_TruncatedMajorRegion`, `JointDickman_Amplification_WeightedAmplification`, `JointDickman_Amplification_WeightedCandidateMultiplicity`, `JointDickman_Amplification_WeightedCountTail`, `JointDickman_Amplification_WeightedPolynomialFeatures`, `JointDickman_Amplification_WeightedRemainderLaw`, `JointDickman_Analysis_BinCharacters`, `JointDickman_Analysis_CanonicalMellinBands`, `JointDickman_Analysis_CharacterContourSeries`, `JointDickman_Analysis_CharacterConvolution`, `JointDickman_Analysis_CharacterDistanceInput`, `JointDickman_Analysis_CharacterEulerRemainder`, `JointDickman_Analysis_CharacterFourierExpansion`, `JointDickman_Analysis_CharacterInputs`, `JointDickman_Analysis_CharacterPrimeCutoff`, `JointDickman_Analysis_CharacterRectangleLog`, `JointDickman_Analysis_CharacterResidues`, `JointDickman_Analysis_CharacterRieszKernel`, `JointDickman_Analysis_FairLaplaceFeature`, `JointDickman_Analysis_FractionalContourRectangles`, `JointDickman_Analysis_FractionalPowerBoundary`, `JointDickman_Analysis_LogRieszDerivatives`, `JointDickman_Analysis_MellinAngularEnergy`, `JointDickman_Analysis_MellinApplicationScales`, `JointDickman_Analysis_MellinBandSelection`, `JointDickman_Analysis_MellinLogWindows`, `JointDickman_Analysis_MellinPacketScale`, `JointDickman_Analysis_MellinPackets`, `JointDickman_Analysis_MellinPrimeSieve`, `JointDickman_Analysis_MellinSampleDuality`, `JointDickman_Analysis_MellinShortComparison`, `JointDickman_Analysis_MellinSieveBudget`, `JointDickman_Analysis_MellinSieveProfile`, `JointDickman_Analysis_MellinSieveQuadratic`, `JointDickman_Analysis_MellinSieveRegularity`, `JointDickman_Analysis_MellinSieveRemainder`, `JointDickman_Analysis_MellinWindowProfile`, `JointDickman_Analysis_MultiscaleMellinEnergy`, `JointDickman_Analysis_PrimeZetaPoleLog`, `JointDickman_Analysis_RieszLogPolynomial`, `JointDickman_Analysis_RieszUnsmoothCoefficients`, `JointDickman_Analysis_SquarefreeCharacterEuler`, `JointDickman_Analysis_SquarefreeCharacterFactorization`, `JointDickman_Analysis_SquarefreeRieszPerronLocal`, `JointDickman_Analysis_ZetaContourRegion`, `JointDickman_Analysis_ZetaPerronScale`, `JointDickman_Arithmetic_AdditionSieveDensity`, `JointDickman_Arithmetic_AdditionSieveGeometry`, `JointDickman_Arithmetic_AdditionSieveMajorant`, `JointDickman_Arithmetic_AffineRectangleSieve`, `JointDickman_Arithmetic_AmplificationPrimeRanges`, `JointDickman_Arithmetic_AmplificationSmoothCutoff`, `JointDickman_Arithmetic_BinGeneratingLimit`, `JointDickman_Arithmetic_BlockPrimeSites`, `JointDickman_Arithmetic_BrunBlocks`, `JointDickman_Arithmetic_BrunPrimeBlocks`, `JointDickman_Arithmetic_BrunTruncation`, `JointDickman_Arithmetic_BrunTruncationError`, `JointDickman_Arithmetic_BrunUpperSieve`, `JointDickman_Arithmetic_CandidateCoefficientPrimes`, `JointDickman_Arithmetic_CandidateDefectPrimes`, `JointDickman_Arithmetic_CandidateExceptionalPrimes`, `JointDickman_Arithmetic_ConditionalPrimeParameters`, `JointDickman_Arithmetic_ConditionedPrimeResidues`, `JointDickman_Arithmetic_ConsecutivePrimeHits`, `JointDickman_Arithmetic_DickmanDistribution`, `JointDickman_Arithmetic_DistinctBinDistribution`, `JointDickman_Arithmetic_DistinctBinGenerating`, `JointDickman_Arithmetic_DivisorEdgeReindex`, `JointDickman_Arithmetic_FinitePrimeWeight`, `JointDickman_Arithmetic_FormIntervalSieve`, `JointDickman_Arithmetic_FormRectangleSieve`, `JointDickman_Arithmetic_GoodPrimeDensity`, `JointDickman_Arithmetic_HarmonicSummation`, `JointDickman_Arithmetic_HigherPrimeDigits`, `JointDickman_Arithmetic_LogarithmicSimplexCutoff`, `JointDickman_Arithmetic_LogarithmicSimplexRecurrence`, `JointDickman_Arithmetic_LowAdditionSieve`, `JointDickman_Arithmetic_MixedThreeFormSieve`, `JointDickman_Arithmetic_MovingRoughExpansion`, `JointDickman_Arithmetic_NumericPrefixHarmonic`, `JointDickman_Arithmetic_OccupiedPrimeMass`, `JointDickman_Arithmetic_OrderedPrimeBoundary`, `JointDickman_Arithmetic_OrderedPrimeSubsets`, `JointDickman_Arithmetic_OrderedSimplex`, `JointDickman_Arithmetic_PartialPrimeChannel`, `JointDickman_Arithmetic_PeriodicConvolutionSmoothing`, `JointDickman_Arithmetic_PrimeBinPartition`, `JointDickman_Arithmetic_PrimeBoxBoundary`, `JointDickman_Arithmetic_PrimeCoarseFeatures`, `JointDickman_Arithmetic_PrimeDigitAverages`, `JointDickman_Arithmetic_PrimeDigitCRT`, `JointDickman_Arithmetic_PrimeDigitDecomposition`, `JointDickman_Arithmetic_PrimeFeatureShortError`, `JointDickman_Arithmetic_PrimeGeneratingMean`, `JointDickman_Arithmetic_PrimeIndicatorRegularity`, `JointDickman_Arithmetic_PrimeIntervalSums`, `JointDickman_Arithmetic_PrimeLogMeasure`, `JointDickman_Arithmetic_PrimeLogarithmicReduction`, `JointDickman_Arithmetic_PrimeNormalizer`, `JointDickman_Arithmetic_PrimePairLocalSieve`, `JointDickman_Arithmetic_PrimePairSieveCount`, `JointDickman_Arithmetic_PrimePresencePhase`, `JointDickman_Arithmetic_PrimeProductBoundary`, `JointDickman_Arithmetic_PrimeProductGcdError`, `JointDickman_Arithmetic_PrimeProductTail`, `JointDickman_Arithmetic_PrimeRampLocalLaw`, `JointDickman_Arithmetic_PrimeRangeOperators`, `JointDickman_Arithmetic_PrimeResidueChannel`, `JointDickman_Arithmetic_PrimeSetWeights`, `JointDickman_Arithmetic_PrimeSiteTranspose`, `JointDickman_Arithmetic_PrimeSubsetTail`, `JointDickman_Arithmetic_PrimeTupleBounds`, `JointDickman_Arithmetic_RamanujanDivisorFormula`, `JointDickman_Arithmetic_RegularPrimeSets`, `JointDickman_Arithmetic_RepeatedPrimeDensity`, `JointDickman_Arithmetic_RequiredPrimeProduct`, `JointDickman_Arithmetic_RoughAuxiliaryExpansion`, `JointDickman_Arithmetic_RoughCoefficients`, `JointDickman_Arithmetic_RoughConvolution`, `JointDickman_Arithmetic_RoughDensityLimit`, `JointDickman_Arithmetic_RoughLeadingCoefficient`, `JointDickman_Arithmetic_RoughMeanNormalization`, `JointDickman_Arithmetic_RoughResidueHarmonic`, `JointDickman_Arithmetic_RoughUniformExpansion`, `JointDickman_Arithmetic_RpowTaylor`, `JointDickman_Arithmetic_ScaledRoughCoefficients`, `JointDickman_Arithmetic_SieveAffineLines`, `JointDickman_Arithmetic_SieveInterval`, `JointDickman_Arithmetic_SieveRectangle`, `JointDickman_Arithmetic_SieveScale`, `JointDickman_Arithmetic_SieveSingleDensity`, `JointDickman_Arithmetic_SmoothArithmeticTensor`, `JointDickman_Arithmetic_SmoothCoefficientMinorArc`, `JointDickman_Arithmetic_SmoothDyadicPartition`, `JointDickman_Arithmetic_SquarefreeEulerFactorization`, `JointDickman_Arithmetic_SquarefreeEulerLog`, `JointDickman_Arithmetic_SquarefreeEulerProduct`, `JointDickman_Arithmetic_SubsetPrimeModel`, `JointDickman_Arithmetic_TiltedSieveDensity`, `JointDickman_Arithmetic_TotientProductTruncation`, `JointDickman_Arithmetic_UpperSieveInput`, `JointDickman_Arithmetic_WeightedSieve`, `JointDickman_Basic`, `JointDickman_Counting_AdditionRatioWindow`, `JointDickman_Counting_AmplificationWindows`, `JointDickman_Counting_ArithmeticBlockAverage`, `JointDickman_Counting_ArithmeticBlockMatrix`, `JointDickman_Counting_ArithmeticCoefficientHits`, `JointDickman_Counting_ArithmeticCoefficientProbability`, `JointDickman_Counting_ArithmeticLagCorrelations`, `JointDickman_Counting_AuxiliaryExceptionalEnergy`, `JointDickman_Counting_AuxiliaryPowerEnergy`, `JointDickman_Counting_BinLabelPositiveEnergy`, `JointDickman_Counting_BlockCandidates`, `JointDickman_Counting_BlockCounting`, `JointDickman_Counting_BlockEndpointLoss`, `JointDickman_Counting_BlockMatrixIndices`, `JointDickman_Counting_BlockPatternTranspose`, `JointDickman_Counting_BlockReindex`, `JointDickman_Counting_BlockSiteComparison`, `JointDickman_Counting_BlockSquareHits`, `JointDickman_Counting_BlockSquarePeriod`, `JointDickman_Counting_CandidateCoefficientFactor`, `JointDickman_Counting_CoefficientCountIndicators`, `JointDickman_Counting_CoefficientDigitEvents`, `JointDickman_Counting_CoefficientDyadicBoxes`, `JointDickman_Counting_CoefficientErrorScale`, `JointDickman_Counting_CoefficientPartialSum`, `JointDickman_Counting_CoefficientProbabilityLoss`, `JointDickman_Counting_CoefficientProfileFreeze`, `JointDickman_Counting_CoefficientRegularityLoss`, `JointDickman_Counting_CoefficientViolationBounds`, `JointDickman_Counting_CoefficientWeights`, `JointDickman_Counting_ComplexFiniteShortAverages`, `JointDickman_Counting_ComplexShortIntervalConsequences`, `JointDickman_Counting_ConvolutionTail`, `JointDickman_Counting_CountingApplicationScale`, `JointDickman_Counting_CountingArithmeticFeatures`, `JointDickman_Counting_CountingArithmeticMean`, `JointDickman_Counting_CountingCandidateModel`, `JointDickman_Counting_CountingCoefficientRegularity`, `JointDickman_Counting_CountingCutoffError`, `JointDickman_Counting_CountingDyadicIdentity`, `JointDickman_Counting_CountingErrorRate`, `JointDickman_Counting_CountingFeatureRows`, `JointDickman_Counting_CountingForwardRows`, `JointDickman_Counting_CountingOriginParameter`, `JointDickman_Counting_CountingPeriodicEnergy`, `JointDickman_Counting_CountingPeriodicModel`, `JointDickman_Counting_CountingRamp`, `JointDickman_Counting_CountingSiteModel`, `JointDickman_Counting_CountingSiteTest`, `JointDickman_Counting_CountingSlowMean`, `JointDickman_Counting_CountingTensorProfile`, `JointDickman_Counting_CyclicGeometricEnergy`, `JointDickman_Counting_DyadicScaleWindow`, `JointDickman_Counting_EndpointCoefficientMass`, `JointDickman_Counting_EndpointCoefficientTest`, `JointDickman_Counting_EndpointCountingCutoff`, `JointDickman_Counting_FiniteConvolutionShift`, `JointDickman_Counting_FiniteWeightedCoefficient`, `JointDickman_Counting_FirstCoefficientAverage`, `JointDickman_Counting_ForwardQuadraticEnergy`, `JointDickman_Counting_GeometricWindowKernel`, `JointDickman_Counting_GraphCoefficientMass`, `JointDickman_Counting_GraphCoefficientReindex`, `JointDickman_Counting_GraphCoefficientSupport`, `JointDickman_Counting_GraphLagMajorant`, `JointDickman_Counting_GraphLagSwap`, `JointDickman_Counting_HistogramCellCoefficients`, `JointDickman_Counting_HistogramWindows`, `JointDickman_Counting_InteriorAmplificationWindows`, `JointDickman_Counting_LagEnvelopeMoments`, `JointDickman_Counting_MaskedCoefficientErrors`, `JointDickman_Counting_OffDiagonalEnergy`, `JointDickman_Counting_OscillatoryCoefficientLaw`, `JointDickman_Counting_PeriodicAverages`, `JointDickman_Counting_PeriodicCandidateCutoff`, `JointDickman_Counting_PeriodicWindowIntegral`, `JointDickman_Counting_PolynomialTermLagVariation`, `JointDickman_Counting_ReverseCoefficientMass`, `JointDickman_Counting_SamplingConcentration`, `JointDickman_Counting_SamplingErrorEnvelope`, `JointDickman_Counting_SamplingMoments`, `JointDickman_Counting_SamplingSkeleton`, `JointDickman_Counting_SamplingTransfer`, `JointDickman_Counting_ShortLagRemoval`, `JointDickman_Counting_ShortLagSet`, `JointDickman_Counting_SignedCoefficientSums`, `JointDickman_Counting_SingularSeriesPeriodic`, `JointDickman_Counting_SmallMajorCoefficient`, `JointDickman_Counting_TiltedCoefficient`, `JointDickman_Counting_TruncatedCoefficientVariation`, `JointDickman_Counting_UniformHyperbolaBlock`, `JointDickman_MainStatements`, `JointDickman_Probability_AmplificationFairKernel`, `JointDickman_Probability_AmplificationHighCoins`, `JointDickman_Probability_AmplificationTensorProfile`, `JointDickman_Probability_ArithmeticCandidateKernel`, `JointDickman_Probability_ArithmeticGraphKernel`, `JointDickman_Probability_ArithmeticKernelPeriod`, `JointDickman_Probability_ArithmeticMomentComparison`, `JointDickman_Probability_BernoulliComparison`, `JointDickman_Probability_CandidateRetentionKernel`, `JointDickman_Probability_CandidateRootKernel`, `JointDickman_Probability_CandidateSiteKernel`, `JointDickman_Probability_CandidateSquareMoment`, `JointDickman_Probability_ChannelGrid`, `JointDickman_Probability_CoarseKernelComparison`, `JointDickman_Probability_ConditionalCoinAverage`, `JointDickman_Probability_ConditionalFairSplit`, `JointDickman_Probability_CorrectionMoments`, `JointDickman_Probability_EmpiricalResidueProfile`, `JointDickman_Probability_FairSplitChannel`, `JointDickman_Probability_FairSplitPairRegularity`, `JointDickman_Probability_FiniteChannels`, `JointDickman_Probability_FiniteGraphKernel`, `JointDickman_Probability_FiniteKernelBilinear`, `JointDickman_Probability_FixedResidueReduction`, `JointDickman_Probability_FlatExclusiveKernel`, `JointDickman_Probability_FrozenSiteLaw`, `JointDickman_Probability_GeometricCoarseKernel`, `JointDickman_Probability_GeometricHistogramErrors`, `JointDickman_Probability_GeometricSquareKernel`, `JointDickman_Probability_GroupedKernelFeatures`, `JointDickman_Probability_GrowingMomentParameters`, `JointDickman_Probability_HistogramProductError`, `JointDickman_Probability_IndependentKernelSplit`, `JointDickman_Probability_KernelDenominatorSum`, `JointDickman_Probability_LogSampledKernel`, `JointDickman_Probability_LowExclusiveKernel`, `JointDickman_Probability_ManuscriptHistogramFourier`, `JointDickman_Probability_MaskedResidueModel`, `JointDickman_Probability_MaskedSiteMoments`, `JointDickman_Probability_NoChangeCoinOperator`, `JointDickman_Probability_NoChangeSplitBound`, `JointDickman_Probability_OrientedSplitBound`, `JointDickman_Probability_PairHitSites`, `JointDickman_Probability_ProjectedHistogram`, `JointDickman_Probability_ProjectedHistogramError`, `JointDickman_Probability_PublishedCoarseChannel`, `JointDickman_Probability_PublishedResidueChannel`, `JointDickman_Probability_RemainderKernel`, `JointDickman_Probability_ResidueAverageMass`, `JointDickman_Probability_ResidueCentering`, `JointDickman_Probability_ResidueChannelDecay`, `JointDickman_Probability_ResidueFourierParseval`, `JointDickman_Probability_ResidueFourierProjection`, `JointDickman_Probability_ResidueHilbert`, `JointDickman_Probability_ResidueProfiles`, `JointDickman_Probability_ResidueSummatory`, `JointDickman_Probability_RootSiteLaw`, `JointDickman_Probability_SampledHistogram`, `JointDickman_Probability_SampledHistogramError`, `JointDickman_Probability_SampledMajorKernel`, `JointDickman_Probability_SignedChannelMass`, `JointDickman_Probability_SignedSplitProduct`, `JointDickman_Probability_SiteConditionedRootProduct`, `JointDickman_Probability_SiteGoodEvent`, `JointDickman_Probability_SitePartition`, `JointDickman_Probability_SiteTestRestriction`, `JointDickman_Probability_TensorCutoff`, `JointDickman_Probability_TwoSiteSplitModel`, `JointDickman_Probability_TwoSiteSplitProduct`, `JointDickman_Probability_TwoSplitLaw`, `JointDickman_Probability_UniformCoarseChannel`, `JointDickman_Probability_UniformResidueChannel`, `JointDickman_Probability_UniformResidueFibers`, `ResidueCalcOnRectangles`, `TwoPointCorrelations_MRTAmplificationPower`, `TwoPointCorrelations_MRTBandParameters`, `TwoPointCorrelations_MRTBinMomentSum`, `TwoPointCorrelations_MRTFrequencyExponents`, `TwoPointCorrelations_MRTLogPrimeBins`, `TwoPointCorrelations_MRTMeanSquare`, `TwoPointCorrelations_MRTPrimeBands`, `TwoPointCorrelations_MRTResolution`, `TwoPointCorrelations_MertensScale`.
--
--   **Imports.** It imports the published bundle `Def_JointDickman`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ083J003`; the statements `OAI_Erdos970_ErdosPrimeInputs_PrimeErrorDecay_uniform_prime_interval_error`, `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd`, `OAI_JointDickman_amplification_positive_mass_bound`, `OAI.JointDickman.amplification_positive_mass_bound_jd`, `OAI_JointDickman_amplification_regularity_loss`, `OAI.JointDickman.amplification_regularity_loss_jd`, `OAI_JointDickman_auxiliary_power_energy`, `OAI.JointDickman.auxiliary_power_energy_jd`, `OAI_JointDickman_bin_auxiliary_cofactor`, `OAI.JointDickman.bin_auxiliary_cofactor_jd`, `OAI_JointDickman_bounded_box_coarse_comparison`, `OAI.JointDickman.bounded_box_coarse_comparison_jd`, `OAI_JointDickman_canonical_full_energy`, `OAI.JointDickman.canonical_full_energy_jd`, `OAI_JointDickman_centered_bin_spectral`, `OAI.JointDickman.centered_bin_spectral_jd`, `OAI_JointDickman_characterDistanceDivergence`, `OAI.JointDickman.characterDistanceDivergence_jd`, `OAI_JointDickman_characterPerron_estimate`, `OAI.JointDickman.characterPerron_estimate_jd`, `OAI_JointDickman_character_agreement_distance_polynomial`, `OAI.JointDickman.character_agreement_distance_polynomial_jd`, `OAI_JointDickman_coarse_residue_smoothing_energy_proved`, `OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd`, `OAI_JointDickman_coefficient_frozen_fullArc_integral_law`, `OAI.JointDickman.coefficient_frozen_fullArc_integral_law_jd`, `OAI_JointDickman_counting_arithmetic_feature_comparison`, `OAI.JointDickman.counting_arithmetic_feature_comparison_jd`, `OAI_JointDickman_counting_model_energy_mean_proved`, `OAI.JointDickman.counting_model_energy_mean_proved_jd`, `OAI_JointDickman_counting_sampling`, `OAI_JointDickman_counting_sampling_actual_scale`, `OAI.JointDickman.counting_sampling_actual_scale_jd`, `OAI.JointDickman.counting_sampling_jd`, `OAI_JointDickman_finiteBinDistributionInput`, `OAI.JointDickman.finiteBinDistributionInput_jd`, `OAI_JointDickman_finite_graph_arithmetic_fluctuation`, `OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd`, `OAI_JointDickman_finite_graph_centered_mean_proved`, `OAI.JointDickman.finite_graph_centered_mean_proved_jd`, `OAI_JointDickman_finite_ramp_approximation`, `OAI.JointDickman.finite_ramp_approximation_jd`, `OAI_JointDickman_geometric_sampled_integral_error_sum`, `OAI.JointDickman.geometric_sampled_integral_error_sum_jd`, `OAI_JointDickman_groupedManuscriptChannel_square_bound`, `OAI.JointDickman.groupedManuscriptChannel_square_bound_jd`, `OAI_JointDickman_jointDickmanLaw_unconditional`, `OAI.JointDickman.jointDickmanLaw_unconditional_jd`, `OAI_JointDickman_largeMajorArc_box_bound`, `OAI.JointDickman.largeMajorArc_box_bound_jd`, `OAI_JointDickman_manuscript_geometric_residue_energy`, `OAI.JointDickman.manuscript_geometric_residue_energy_jd`, `OAI_JointDickman_masked_arithmetic_fluctuation_bound`, `OAI.JointDickman.masked_arithmetic_fluctuation_bound_jd`, `OAI_JointDickman_mellin_prime_sampling_arithmetic`, `OAI.JointDickman.mellin_prime_sampling_arithmetic_jd`, `OAI_JointDickman_nonzero_binLabel_correlation_along_forces_energy`, `OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd`, `OAI_JointDickman_positive_blocks_of_graph`, `OAI.JointDickman.positive_blocks_of_graph_jd`, `OAI_JointDickman_primeChannelMarginal_upper`, `OAI.JointDickman.primeChannelMarginal_upper_jd`, `OAI_JointDickman_primeCoarseFeature_laplace_approximation`, `OAI.JointDickman.primeCoarseFeature_laplace_approximation_jd`, `OAI_JointDickman_primeCommonLogCell_upper`, `OAI.JointDickman.primeCommonLogCell_upper_jd`, `OAI_JointDickman_primeProductMertensInput`, `OAI.JointDickman.primeProductMertensInput_jd`, `OAI_JointDickman_prime_agreement_distance_polynomial`, `OAI.JointDickman.prime_agreement_distance_polynomial_jd`, `OAI_JointDickman_ramare_product_sparse_integral`, `OAI.JointDickman.ramare_product_sparse_integral_jd`, `OAI_JointDickman_rationalFixedScaleLaw_of_distance_divergence_proved`, `OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd`, `OAI_JointDickman_squarefree_integer_rational_polylog_sum_bound`, `OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd`, `OAI_JointDickman_weightedAmplification_second_bound`, `OAI.JointDickman.weightedAmplification_second_bound_jd`, `OAI_TwoPointCorrelations_halasz_prime_mean_square_cauchy`, `OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy_jd`, `OAI_TwoPointCorrelations_halasz_prime_window_middle` and `OAI.TwoPointCorrelations.halasz_prime_window_middle_jd`; the proofs of `OAI_Erdos970_ErdosPrimeInputs_PrimeErrorDecay_uniform_prime_interval_error`, `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd`, `OAI.JointDickmanPaper.decreasing_order`, `OAI.JointDickmanPaper.increasing_order`, `OAI.JointDickmanPaper.joint_law`, `OAI_JointDickman_characterDistanceDivergence`, `OAI.JointDickman.characterDistanceDivergence_jd`, `OAI_JointDickman_character_agreement_distance_polynomial`, `OAI.JointDickman.character_agreement_distance_polynomial_jd`, `OAI_JointDickman_finiteBinDistributionInput`, `OAI.JointDickman.finiteBinDistributionInput_jd`, `OAI_JointDickman_mellin_prime_sampling_arithmetic`, `OAI.JointDickman.mellin_prime_sampling_arithmetic_jd`, `OAI_JointDickman_primeProductMertensInput`, `OAI.JointDickman.primeProductMertensInput_jd`, `OAI_JointDickman_prime_agreement_distance_polynomial`, `OAI.JointDickman.prime_agreement_distance_polynomial_jd`, `OAI_JointDickman_ramare_product_sparse_integral` and `OAI.JointDickman.ramare_product_sparse_integral_jd`.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_JointDickman

section
-- module Solutions.OAIQ083_JD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.Erdos970_Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

local instance instCoeForallRealForallComplex_solutions_r8e390f_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

end lemmas

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT1_ComplexAnalysis
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma lem_cos2t (θ : ℝ) : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  exact Real.cos_two_mul θ

lemma lem_cos2t2 (θ : ℝ) : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  rw [lem_cos2t]
  ring

lemma lem_cosSquare (θ : ℝ) : 2 * (1 + Real.cos θ)^2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ^2 := by
  ring

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [lem_cosSquare]
  rw [lem_cos2t2]
  ring

lemma lem_SquarePos (y : ℝ) : 0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : ℝ) : 0 ≤ 2 * y ^ 2 := by
  apply mul_nonneg
  · norm_num
  · exact lem_SquarePos y

lemma lem_SquarePoscos (θ : ℝ) : 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))

lemma lem_RrFpos (r R : ℝ) (F : ℂ) (_hr : 0 < r) (hrR : r < R) : (R - r) * norm F ≥ 0 := by
  have h_R_minus_r_nonneg : R - r ≥ 0 := by linarith [hrR]
  have h_abs_F_nonneg : 0 ≤ norm F := by apply norm_nonneg
  apply mul_nonneg h_R_minus_r_nonneg h_abs_F_nonneg

lemma lem_nonneg_product_with_real_abs (r M : ℝ) (hr : r > 0) (hM : M > 0) : 0 ≤ r * (2 * |M|) := by
                                 
  have h_abs_eq : |M| = M := abs_of_pos hM
                                         
  rw [h_abs_eq]

  have h_two_M_pos : (2 : ℝ) * M > 0 := by
    apply mul_pos
    norm_num
    exact hM
                              
  apply mul_nonneg
  linarith [hr]
  linarith [h_two_M_pos]

lemma deriv_ofReal_eq_one (t : ℝ) : deriv Complex.ofReal t = 1 := by

  have h : deriv Complex.ofReal t = Complex.ofReal 1 := by

    rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
    exact ContinuousLinearMap.deriv Complex.ofRealCLM
                                       
  rw [h]
  simp only [Complex.ofReal_one]

lemma differentiableAt_ofReal (t : ℝ) : DifferentiableAt ℝ Complex.ofReal t := by
                                                                                
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
                                                                                    
  apply ContinuousLinearMap.differentiableAt

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by
                            
  have h_pi_pos : Real.pi > 0 := Real.pi_pos
                        
  have h_2pi_pos : 2 * Real.pi > 0 := by
    apply mul_pos
    · norm_num
    · exact h_pi_pos
                              
  apply div_pos
  · norm_num
  · exact h_2pi_pos

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ} (_hab : a ≤ b) : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by

  exact MeasureTheory.norm_integral_le_integral_norm g

lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
                                          
  have h1 : norm (↑r * 1) = r * norm (1 : ℂ) := by simp; assumption
                                         
  simp only [mul_one] at h1
  have h2 : norm (1 : ℂ) = 1 := by simp
  rw [h2] at h1
  simp only [mul_one] at h1
  simp
  assumption

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
                                                                              
  have h_eq : (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]

  rw [h_eq]

  have h_nonneg : (1 / (2 * Real.pi) : ℝ) ≥ 0 := by
    apply div_nonneg
    · norm_num
    · apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos

  exact complex_abs_ofReal_nonneg (1 / (2 * Real.pi)) h_nonneg

lemma lem_modulus_wz (w z : ℂ) : norm ((w - z) ^ 2) = (norm (w - z)) ^ 2 := by
                                     
  exact Complex.norm_pow (w - z) 2

lemma lem_absdiv {a b : ℂ} (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
                                             
  exact norm_div a b

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ _t in a..b, C := by

  have h_const_integrable : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
                                                                             
  have h_pointwise : ∀ x ∈ Set.Icc a b, g x ≤ (fun _ => C) x := by
    intro x hx
    simp
    exact h_bound x hx
                                   
  exact intervalIntegral.integral_mono_on hab h_integrable h_const_integrable h_pointwise

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ _t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma lem_r_prime_lt_R {r R : ℝ}
    (_h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R := by
                                                                  
  rw [add_div_two_lt_right]
  exact h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  ·                         
    rw [left_lt_add_div_two]
    exact h_r_lt_R
  ·                         
    exact lem_r_prime_lt_R h_r_pos h_r_lt_R

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped Interval

open _root_.Filter Topology

open Classical

open scoped Topology

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT2_LogDerivative
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Filter Metric _root_.Set Bornology _root_.Function

open Classical

lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
                                   
  have hy : 0 < y := lt_of_lt_of_le hx hxy
                                                       
  exact one_div_le_one_div_of_le hx hxy

theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
                                                       
    simp [Finset.prod_insert ha, ih]

lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp

lemma lem_mod_div_ (w1 w2 : ℂ) (_hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp

lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
                                                              
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
                                                      
  rw [Complex.star_def]
                                                    
  exact Complex.mul_conj' z

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_three_gt_e : (3 : ℝ) > Real.exp 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h1 h2

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)

lemma norm_div_eq (a b : ℂ) (_hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
                                     
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
                                        
  rw [sub_pos]
                                                        
  rw [lt_div_iff₀ ha_pos]
                         
  rw [← pow_two]
                                                                         
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT3_RiemannZeta
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open scoped BigOperators Topology

lemma abs_of_tprod {P : Type*} (w : P → ℂ) (hw : Multipliable w) : norm (∏' p : P, w p) = ∏' p : P, norm (w p) := by exact Multipliable.norm_tprod hw

lemma abs_of_inv (z : ℂ) (_hz : z ≠ 0) : norm (z⁻¹) = (norm z)⁻¹ := norm_inv z

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

theorem tprod_commutes_with_inclusion_infinite {α : Type*} (f : α → ℂˣ) (h : Multipliable f) :
    ι (tprod f) = tprod (fun i ↦ ι (f i)) :=
by
  change ((tprod f : ℂˣ) : ℂ) = tprod (fun i ↦ ((f i : ℂˣ) : ℂ))
  have hcont : Continuous (Units.coeHom ℂ) := by
    simpa using! (Units.continuous_val : Continuous (fun u : ℂˣ => ((u : ℂˣ) : ℂ)))
  simpa [Units.coeHom] using
    (Multipliable.map_tprod (f := f) (γ := ℂ) h (g := Units.coeHom ℂ) hcont)

theorem inclusion_commutes_with_division (a b : ℂˣ) :
    ι (a / b) = ι a / ι b := by
  exact Units.val_div_eq_div_val a b

lemma lift_multipliable_of_nonzero {P : Type*} (a : P → ℂ) (ha : Multipliable a) (h_a_nonzero : ∀ p, a p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0):
  Multipliable (fun p ↦ Units.mk0 (a p) (h_a_nonzero p)) := by

  obtain ⟨A, hA⟩ := ha
  have hA_nonzero := hA_nonzero' A hA
  refine ⟨Units.mk0 A hA_nonzero, ?_⟩
  simp [HasProd, tendsto_nhds] at hA ⊢
  intro sU h_sU_open hA_mem
  have hA_im_mem : ι (Units.mk0 A hA_nonzero) ∈ ι '' sU := Set.mem_image_of_mem ι hA_mem
  have sU_im_open : IsOpen (ι '' sU) := by
    apply (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_).mp
    assumption
    exact Units.isOpenEmbedding_val
  have := hA (ι '' sU) sU_im_open hA_im_mem
  obtain ⟨a1, ha⟩ := this
  use a1
  intro b ha1
  obtain ⟨x', x'_spec_mem, x'_spec_eq⟩ := ha b ha1
  suffices x' = ∏ b ∈ b, Units.mk0 (a b) (by simp [*]) by
    rwa [← this]
  have : Units.mk0 (ι x') (Units.ne_zero x') = x' :=
    Units.mk0_val x' (Units.ne_zero x')
  have this2 : (Units.mk0 (∏ b ∈ b, a b)
    (Finset.prod_ne_zero_iff.mpr fun a a_1 => h_a_nonzero a)) = x' :=
      Units.ext (id (Eq.symm x'_spec_eq))
  rw [Units.mk0_prod] at this2
  rw [←this2]
  conv =>
    rhs
    rw [← Finset.prod_attach]

lemma prod_of_ratios_simplified {P : Type*} (a b : P → ℂ)
(ha : Multipliable a) (hb : Multipliable b)
    (h_a_nonzero : ∀ p, a p ≠ 0) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ A, HasProd b A → A ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                                      
  let a' : P → ℂˣ := fun p ↦ Units.mk0 (a p) (h_a_nonzero p)
  let b' : P → ℂˣ := fun p ↦ Units.mk0 (b p) (h_b_nonzero p)

  have h_multipliable_a' : Multipliable a' := lift_multipliable_of_nonzero a ha h_a_nonzero hA_nonzero'
  have h_multipliable_b' : Multipliable b' := lift_multipliable_of_nonzero b hb h_b_nonzero hB_nonzero'
  have h_multipliable_a'_div_b' : Multipliable (fun p ↦ a' p / b' p) := Multipliable.div h_multipliable_a' h_multipliable_b'

  calc
    (∏' p, a p) / (∏' p, b p)
                                                         
    _ = (∏' p, ι (a' p)) / (∏' p, ι (b' p)) := by simp [a', b']
                                                                             
    _ = ι (∏' p, a' p) / ι (∏' p, b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                              
    _ = ι ((∏' p, a' p) / (∏' p, b' p)) := by rw [← inclusion_commutes_with_division]
                                                                                                        
    _ = ι (∏' p, a' p / b' p) := by simp [Multipliable.tprod_div, *]
                                                                           
    _ = ∏' p, ι (a' p / b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                                                   
    _ = ∏' p, (ι (a' p) / ι (b' p)) := by simp
                                                                         
    _ = ∏' p, a p / b p := by simp [a', b']

lemma prod_of_ratios {P : Type*} (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ B, HasProd b B → B ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                         
  by_cases h_a_zero : ∃ p, a p = 0
  case pos =>

    have lhs_zero : ∏' p : P, a p = 0 := by
                                                                      
      exact tprod_of_exists_eq_zero h_a_zero
    have rhs_zero : ∏' p : P, (a p / b p) = 0 := by
                                                        
      obtain ⟨p₀, hp₀⟩ := h_a_zero
      have h_div_zero : ∃ p, (a p / b p) = 0 := by
        use p₀
        simp [hp₀]
      exact tprod_of_exists_eq_zero h_div_zero
    simp [lhs_zero, rhs_zero]
  case neg =>
                                  
    push Not at h_a_zero
                                                                          
    exact prod_of_ratios_simplified a b ha hb h_a_zero h_b_nonzero hA_nonzero' hB_nonzero'

lemma diff_of_squares (z : ℂ) : 1 - z^2 = (1 - z) * (1 + z) := by ring

lemma one_sub_ne_zero_of_abs_lt_one (z : ℂ) (hz : norm z < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : 1 = z := by
    have := congrArg (fun w : ℂ => w + z) h
    simpa [sub_add_cancel, zero_add] using this
  have habs1lt : norm (1 : ℂ) < 1 := by simpa [h1] using hz
  have hnorm1lt : ‖(1 : ℂ)‖ < 1 := by simp [norm] at habs1lt
  have : (1 : ℝ) < 1 := by simp [norm_one] at hnorm1lt
  exact (lt_irrefl _) this

lemma inv_mul_div_cancel_right_of_ne_zero (a b : ℂ) (ha : a ≠ 0) : ((a * b)⁻¹) / a⁻¹ = b⁻¹ := by
  simp [div_eq_mul_inv, inv_inv, mul_inv_rev, mul_comm, ha]

lemma ratio_invs (z : ℂ) (hz : norm z < 1) : (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_abs_lt_one z hz
  simpa [diff_of_squares z] using
    inv_mul_div_cancel_right_of_ne_zero (1 - z) (1 + z) hz1

lemma complex_cpow_neg_two_mul (z w : ℂ) (_hz : z ≠ 0) : z^(-(2*w)) = (z^(-w))^2 := by
  have h1 : -(2*w) = 2*(-w) := by ring
  rw [h1]
  have h2 : (2 : ℂ)*(-w) = ((2 : ℕ) : ℂ)*(-w) := by norm_cast
  rw [h2, Complex.cpow_nat_mul]

lemma two_mul_ofReal_div_two (r : ℝ) : (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = (r : ℂ) := by
  have hreal : (2 : ℝ) * (r / 2) = r := by
    calc
      (2 : ℝ) * (r / 2) = (2 : ℝ) * r / 2 := by
        have h : (2 : ℝ) * r / 2 = (2 : ℝ) * (r / 2) := by
          simpa using (mul_div_assoc (2 : ℝ) r (2 : ℝ))
        simpa using h.symm
      _ = r := by
        simp
  calc
    (2 : ℂ) * ((r : ℝ) / 2 : ℂ)
        = ((2 * (r / 2) : ℝ) : ℂ) := by
              simp
    _ = (r : ℂ) := by simp [hreal]

lemma triangle_inequality_specific (z : ℂ) : norm (1 - z) ≤ 1 + norm z := by
  simpa [sub_eq_add_neg, norm_one, norm_neg] using (norm_add_le (1 : ℂ) (-z))

lemma re_neg_eq_neg_re (s : ℂ) : (-s).re = - s.re := by
  simp

lemma abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : norm ((x : ℂ) ^ y) = x ^ y.re := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx y

lemma inv_inequality {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  simpa [one_div] using (one_div_le_one_div_of_le ha hab)

lemma eq_of_one_sub_eq_zero (z : ℂ) (h : 1 - z = 0) : z = 1 := by
  rw [sub_eq_zero] at h
  exact h.symm

open NNReal in
lemma prod_inequality {P : Type*} (a b : P → ℝ≥0) (ha : Multipliable a) (hb : Multipliable b)
  (hab : ∀ p : P, a p ≤ b p) :
  ∏' p : P, a p ≤ ∏' p : P, b p := by
  exact Multipliable.tprod_le_tprod hab ha hb

lemma multipliable_complex_abs_inv {i : Type*} (g : i → ℂ) (h_mult : Multipliable (fun i => (1 - g i)⁻¹)) (_h_nonzero : ∀ i, 1 - g i ≠ 0) : Multipliable (fun i => (norm (1 - g i))⁻¹) := by
                                                       
  have h_eq : (fun i => (norm (1 - g i))⁻¹) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    simp
  rw [h_eq]
                                       
  have h_norm_mult : Multipliable (fun i => ‖(1 - g i)⁻¹‖) := Multipliable.norm h_mult
  have h_norm_eq : (fun i => ‖(1 - g i)⁻¹‖) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    rw [norm_inv]
  rwa [← h_norm_eq]

lemma hasProd_nonneg_of_pos {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (a : ℝ) (ha : HasProd f a) : 0 ≤ a := by
                                     
  have h_pos : ∀ s : Finset i, 0 < ∏ i ∈ s, f i := fun s => Finset.prod_pos (fun i _ => hpos i)
                                                         
  have h_nonneg : ∀ s : Finset i, 0 ≤ ∏ i ∈ s, f i := fun s => le_of_lt (h_pos s)
                                                 
  exact ge_of_tendsto ha (Filter.Eventually.of_forall h_nonneg)

lemma nnreal_coe_tprod_eq_tprod_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) :
  ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) := by
                                                                  
  have h_prod : HasProd f (∏' i, f i) := Multipliable.hasProd hf
                                                                               
  have h_map : HasProd (NNReal.toRealHom ∘ f) (NNReal.toRealHom (∏' i, f i)) :=
    HasProd.map h_prod NNReal.toRealHom NNReal.continuous_coe
                                                                                                     
  have h_comp : NNReal.toRealHom ∘ f = fun i => (↑(f i) : ℝ) := by
    ext i
    rfl
  have h_val : NNReal.toRealHom (∏' i, f i) = ↑(∏' i, f i) := rfl
                              
  rw [h_comp, h_val] at h_map
                                             
  exact HasProd.tprod_eq h_map

lemma nnreal_tprod_le_coe {i : Type*} (f g : i → NNReal) (hf : Multipliable f) (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) : ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
                                                               
  rw [nnreal_coe_tprod_eq_tprod_coe f hf, nnreal_coe_tprod_eq_tprod_coe g hg]
                                                                                               
  exact NNReal.coe_le_coe.mpr h

lemma summable_one_div_nat_add_rpow' {x : ℝ} (hx : 1 < x) : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) x).2 hx
  have h' : Summable (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) := by
    simpa [one_div] using h
  have h2 : (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) = (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      exact add_nonneg this (show 0 ≤ (1 : ℝ) from zero_le_one)
    simp [abs_of_nonneg hn]
  have h'' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    simpa [h2] using h'
  have h''' : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ x)⁻¹) := by
    simpa [Nat.cast_add] using h''
  simpa [one_div] using h'''

lemma tsum_pos_of_pos_first_term {f : ℕ → ℝ} (hf : Summable f) (h0 : 0 < f 0) (hnonneg : ∀ n, 0 ≤ f n) : 0 < ∑' n, f n := by
  have hsum0 : ∑ n ∈ Finset.range 1, f n = f 0 := by
    simp
  have hpos_partial : 0 < ∑ n ∈ Finset.range 1, f n := by
    simpa [hsum0] using h0
  have hsumle : ∑ n ∈ Finset.range 1, f n ≤ ∑' n, f n := by
    have hnonneg' : ∀ n ∉ Finset.range 1, 0 ≤ f n := by
      intro n hn
      exact hnonneg n
    simpa using (hf.sum_le_tsum (s := Finset.range 1) hnonneg')
  exact lt_of_lt_of_le hpos_partial hsumle

lemma terms_nonneg (x : ℝ) : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ x) := by
  intro n
  have hposb' : 0 < ((n : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n)) zero_lt_one
  have hposb : 0 < ((n + 1 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hposb'
  have hdenpos : 0 < ((n + 1 : ℝ) ^ x) := by
    simpa using (Real.rpow_pos_of_pos hposb x)
  have hden_nonneg : 0 ≤ ((n + 1 : ℝ) ^ x) := le_of_lt hdenpos
  have hnum_nonneg : 0 ≤ (1 : ℝ) := le_of_lt (zero_lt_one : 0 < (1 : ℝ))
  exact div_nonneg hnum_nonneg hden_nonneg

lemma term_eq_ofRealC (x : ℝ) (n : ℕ) : (1 / ((n + 1 : ℂ) ^ (x : ℂ))) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
  have hbase_nonneg : 0 ≤ (n + 1 : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : 0 ≤ (n : ℝ) + 1 := add_nonneg hn (show 0 ≤ (1 : ℝ) from zero_le_one)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hpow' : ((n + 1 : ℂ) ^ (x : ℂ)) = (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (x := (n + 1 : ℝ)) (hx := hbase_nonneg) (y := x)).symm
  have hdiv : (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
    simp
  calc
    1 / ((n + 1 : ℂ) ^ (x : ℂ))
        = (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by simp [hpow']
    _ = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := hdiv

lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  have hz : (((∑' n : ℕ, g n) : ℝ) : ℂ).im = 0 := by
    simp
  exact Eq.trans him hz

lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  simpa [Complex.ofReal_re] using h

lemma zetapos (x : ℝ) (hx : 1 < x) : (riemannZeta x).im = 0 ∧ 0 < (riemannZeta x).re := by
  have hxC : 1 < (Complex.ofReal x).re := by simpa [Complex.ofReal_re] using hx
  have hz : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC
  have him : (riemannZeta x).im = 0 := by
    simpa [hz, term_eq_ofRealC x] using
      (im_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hre : (riemannZeta x).re = ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) := by
    simpa [hz, term_eq_ofRealC x] using
      (re_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) :=
    summable_one_div_nat_add_rpow' (x := x) hx
  have hpos0 : 0 < 1 / ((Nat.cast 0 + 1 : ℝ) ^ x) := by
    simp [zero_add]
  have hnonneg : ∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℝ) ^ x) := terms_nonneg x
  have hpos : 0 < ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) :=
    tsum_pos_of_pos_first_term hsum hpos0 hnonneg
  exact ⟨him, by simpa [hre] using hpos⟩

lemma zeta332pos : 0 < norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have h32 : (1 : ℝ) < (3 : ℝ) / 2 := by norm_num
  obtain ⟨h3im, h3repos⟩ := zetapos 3 h3
  obtain ⟨h32im, h32repos⟩ := zetapos ((3 : ℝ) / 2) h32
  have h3ne : riemannZeta (3 : ℝ) ≠ 0 := by
    intro hz
    exact (ne_of_gt h3repos) (by simpa using congrArg Complex.re hz)
  have h32ne : riemannZeta ((3 : ℝ) / 2) ≠ 0 := by
    intro hz
    exact (ne_of_gt h32repos) (by simpa using congrArg Complex.re hz)
  have hdivne : riemannZeta (3 : ℝ) / riemannZeta ((3 : ℝ) / 2) ≠ 0 :=
    div_ne_zero h3ne h32ne
  simpa using (norm_pos_iff.mpr hdivne)

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

lemma one_div_nat_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) : 1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · have hcalc : 1 / (n : ℂ) ^ s = (n : ℂ) ^ (-s) := by
      calc
        1 / (n : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by simp [one_div]
        _ = (n : ℂ) ^ (-s) := by simpa using (Complex.cpow_neg (n : ℂ) s).symm
    simpa [h] using hcalc

lemma lem_zetaLimit (s : ℂ) (hs : 1 < s.re) : riemannZeta s = ∑' n : ℕ, if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  classical
  have hsne : s ≠ 0 := by
    intro h
    have hpos : 0 < s.re := lt_trans (show (0 : ℝ) < 1 from zero_lt_one) hs
    have hne : s.re ≠ 0 := ne_of_gt hpos
    simp [h] at hne
  have hz : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hz

noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

lemma sum_Icc1_eq_sum_range_succ (N : ℕ) (g : ℕ → ℂ) :
  (∑ k ∈ Finset.Icc 1 N, g k) = ∑ n ∈ Finset.range N, g (n + 1) := by
  classical
                                                                  
  symm
  refine Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
    (f := fun n => g (n + 1)) (g := fun k => g k)
    (i := fun n (_hn : n ∈ Finset.range N) => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := Finset.mem_range.mp hn
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have h2 : n + 1 ≤ N := Nat.succ_le_of_lt hlt
    exact (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  · intro a ha b hb h
                             
    simpa using Nat.succ_injective h
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, ?_, ?_⟩
    ·                      
      have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      have hle : (k - 1) + 1 ≤ N := by simpa [hsucc] using hk2
      have hlt : k - 1 < N := lt_of_lt_of_le (Nat.lt_succ_self (k - 1)) hle
      exact Finset.mem_range.mpr hlt
    ·                  
      simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

lemma sum_Icc0_eq_sum_Icc1_of_zero (N : ℕ) (g : ℕ → ℂ) (h0 : g 0 = 0) :
  (∑ k ∈ Finset.Icc 0 N, g k) = ∑ k ∈ Finset.Icc 1 N, g k := by
  classical
  have hdecomp : insert (0 : ℕ) (Finset.Icc 1 N) = Finset.Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N))
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by
    intro h
    rcases Finset.mem_Icc.mp h with ⟨h1, _h2⟩
    have : ¬ (1 ≤ (0 : ℕ)) := by decide
    exact this h1
  calc
    (∑ k ∈ Finset.Icc 0 N, g k)
        = ∑ k ∈ insert 0 (Finset.Icc 1 N), g k := by
            simp [hdecomp]
    _ = g 0 + ∑ k ∈ Finset.Icc 1 N, g k := by
            simp
    _ = ∑ k ∈ Finset.Icc 1 N, g k := by simp [h0]

lemma sum_Icc0_shifted_eq_sum_range (a : ℕ → ℂ) (m : ℕ) :
  (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range m, a (n + 1) := by
  classical
  calc
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k))
        = ∑ k ∈ Finset.Icc 1 m, (if k = 0 then 0 else a k) := by
          simpa using
            (sum_Icc0_eq_sum_Icc1_of_zero (N := m)
              (g := fun k => (if k = 0 then 0 else a k)) (h0 := by simp))
    _ = ∑ n ∈ Finset.range m, (if n + 1 = 0 then 0 else a (n + 1)) := by
          simpa using
            (sum_Icc1_eq_sum_range_succ (N := m) (g := fun k => (if k = 0 then 0 else a k)))
    _ = ∑ n ∈ Finset.range m, a (n + 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp

lemma sum_Icc0_shifted_floor_eq (a : ℕ → ℂ) (t : ℝ) :
  (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range ⌊t⌋₊, a (n + 1) := by
  simpa using (sum_Icc0_shifted_eq_sum_range a ⌊t⌋₊)

lemma lem_fDeriv (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (let f := fun u : ℝ => (u : ℂ) ^ (-s)
     deriv f u = -s * (u : ℂ) ^ (-s - 1)) := by
                             
  show deriv (fun u : ℝ => (u : ℂ) ^ (-s)) u = -s * (u : ℂ) ^ (-s - 1)
  have hu_ne_zero : u ≠ 0 := ne_of_gt hu
  by_cases h : s = 0
  ·                                
    simp [h]
  ·                                
    have hneg_s_ne_zero : -s ≠ 0 := neg_ne_zero.mpr h
    exact Complex.deriv_ofReal_cpow_const hu_ne_zero hneg_s_ne_zero

lemma differentiable_integrable_cpow_on_Icc (s : ℂ) (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t)
  ∧ IntegrableOn (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc a b) :=
by
  classical
                                                       
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  set g : ℝ → ℂ := fun u => -s * (u : ℂ) ^ (-s - 1)
                            
  have hpos_of_mem : ∀ {t : ℝ}, t ∈ Set.Icc a b → 0 < t := by
    intro t ht; exact lt_of_lt_of_le h0 ht.1
                                    
  have hdiff_at : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hs : s = 0
    ·                   
      simp [f, hs]
    ·                                                        
      have hr : (-s) ≠ 0 := by simpa using (neg_ne_zero.mpr hs)
      have hhas : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * t ^ ((-s) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s) (hr := hr)
      exact hhas.differentiableAt
                             
  have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hzero : (-s - 1) = 0
    ·                       
      have : (fun u : ℝ => (u : ℂ) ^ (-s - 1)) = fun _ : ℝ => (1 : ℂ) := by
        funext u; simp [hzero]
      simpa [this] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
    ·                                             
      have hr : (-s - 1) ≠ 0 := hzero
      have hcpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * t ^ ((-s - 1) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s - 1) (hr := hr)
      have hcont_at : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-s - 1)) t :=
        hcpow.differentiableAt.continuousAt
      simpa using hcont_at.continuousWithinAt
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hconst : ContinuousOn (fun _ : ℝ => (-s : ℂ)) (Set.Icc a b) := continuousOn_const
    simpa only [g, Pi.mul_def, neg_mul] using! hconst.mul hcont_pow
                                                                                  
  have hEqOn : EqOn (deriv f) g (Set.Icc a b) := by
    intro u hu
    have hu_pos : 0 < u := hpos_of_mem hu
    simpa [f, g] using (lem_fDeriv s u hu_pos)
                                                                                                            
  have hcont_deriv : ContinuousOn (deriv f) (Set.Icc a b) := by
                                            
    have hg_restr : Continuous ((Set.Icc a b).domRestrict g) := hcont_g.domRestrict
    have hEqRestr : (Set.Icc a b).domRestrict (deriv f) = (Set.Icc a b).domRestrict g := by
      funext x; exact hEqOn x.property
    have hderiv_restr : Continuous ((Set.Icc a b).domRestrict (deriv f)) := by
      simpa [hEqRestr] using hg_restr
    simpa [continuousOn_iff_continuous_domRestrict] using hderiv_restr
                                                              
  have hInt : IntegrableOn (deriv f) (Set.Icc a b) :=
    hcont_deriv.integrableOn_compact isCompact_Icc
  exact And.intro hdiff_at hInt

lemma intervalIntegral_congr_of_Ioc_eq (a b : ℝ) (h : a ≤ b)
  (f g : ℝ → ℂ)
  (hpt : ∀ u ∈ Set.Ioc a b, f u = g u) :
  (∫ u in a..b, f u) = ∫ u in a..b, g u := by
                                                                                
  have h1 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc a b → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu; exact hpt u hu
  have hIocEmpty : Set.Ioc b a = (∅ : Set ℝ) := by
    simpa using! (Set.Ioc_eq_empty_of_le h)
  have h2 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc b a → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu
    have : u ∈ (∅ : Set ℝ) := by simp [hIocEmpty] at hu
    exact this.elim
  simpa using
    (intervalIntegral.integral_congr_ae' (a := a) (b := b) (μ := MeasureTheory.volume)
      (f := f) (g := g) h1 h2)

lemma lem_applyAbel (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  classical
                   
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
                                             
  have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff_int :=
    differentiable_integrable_cpow_on_Icc (s := s) (a := (1 : ℝ)) (b := (N : ℝ))
      (h0 := by exact zero_lt_one) (_hle := hle)
  rcases hdiff_int with ⟨hdiff, hint⟩
                                                         
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c])
      (hf_diff := by intro t ht; simpa [f] using (hdiff t ht))
      (hf_int := by simpa [f] using hint)
                                         
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
                                    
    have h0 :
        (∑ k ∈ Finset.Icc 0 N, f k * c k) = ∑ k ∈ Finset.Icc 1 N, f k * c k := by
      simpa [c] using
        (sum_Icc0_eq_sum_Icc1_of_zero (N := N)
          (g := fun k => f k * c k) (h0 := by simp [c]))
    have h1 : (∑ k ∈ Finset.Icc 1 N, f k * c k)
                = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by
      simpa using (sum_Icc1_eq_sum_range_succ (N := N) (g := fun k => f k * c k))
    have h2 : (∑ n ∈ Finset.range N, f (n + 1) * c (n + 1))
                = ∑ n ∈ Finset.range N, f (n + 1) := by
      apply Finset.sum_congr rfl; intro n hn; simp [c]
    calc
      (∑ k ∈ Finset.Icc 0 N, f k * c k)
          = ∑ k ∈ Finset.Icc 1 N, f k * c k := by simpa using h0
      _ = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by simpa using h1
      _ = ∑ n ∈ Finset.range N, f (n + 1) := by simpa using h2
      _ = zetaPartialSum s N := by simp [zetaPartialSum, f]
                                                     
  have hset_to_interval :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa using
      (intervalIntegral.integral_of_le
        (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        (μ := volume) hle).symm
  have hstep1 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa [hLHS, hset_to_interval] using habel
                                                
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
                                                                             
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hle)
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
      (g := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hderiv : deriv f u = -s * (u : ℂ) ^ (-s - 1) := by
      simpa [f] using (lem_fDeriv s u hu_pos)
                                          
    have hsumfloor : (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) = (Nat.floor u : ℂ) := by
      have hshift := sum_Icc0_shifted_floor_eq (a := fun _ => (1 : ℂ)) (t := u)
      have hsum : (∑ n ∈ Finset.range ⌊u⌋₊, (1 : ℂ)) = (Nat.floor u : ℂ) := by
        simp [Finset.sum_const, Finset.card_range]
      simpa [c, hsum] using hshift
    calc
      deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k
          = deriv f u * (Nat.floor u : ℂ) := by simp [hsumfloor]
      _ = (Nat.floor u : ℂ) * deriv f u := by simp [mul_comm]
      _ = (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by simp [hderiv]
                                     
  have hstep2 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    simpa [hInt_congr] using hstep1
                                                      
  have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
    have hs : (∑ k ∈ Finset.Icc 0 N, c k) = ∑ n ∈ Finset.range N, (1 : ℂ) := by
      simpa [c] using (sum_Icc0_shifted_eq_sum_range (a := fun _ => (1 : ℂ)) (m := N))
    have hsumN : (∑ n ∈ Finset.range N, (1 : ℂ)) = (N : ℂ) := by
      simp [Finset.sum_const, Finset.card_range]
    calc
      f N * (∑ k ∈ Finset.Icc 0 N, c k)
          = f N * (∑ n ∈ Finset.range N, (1 : ℂ)) := by simp [hs]
      _ = f N * (N : ℂ) := by simp [hsumN]
      _ = (N : ℂ) * f N := by simp [mul_comm]
                                     
  have hfinal :
      zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    calc
      zetaPartialSum s N
          = f N * (∑ k ∈ Finset.Icc 0 N, c k)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simpa using hstep2
      _ = (N : ℂ) * f N
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [hMain]
      _ = (N : ℂ) * (N : ℂ) ^ (-s)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [f]
  exact hfinal

lemma helper_cpow_mul_cpow_neg_eq_cpow_sub (x s : ℂ) (hx : x ≠ 0) : x * x ^ (-s) = x ^ (1 - s) := by
  calc
    x * x ^ (-s) = x ^ (1 : ℂ) * x ^ (-s) := by
      simp [Complex.cpow_one]
    _ = x ^ (1 + (-s)) := by
      simpa using (Complex.cpow_add (x := x) (y := (1 : ℂ)) (z := (-s)) hx).symm
    _ = x ^ (1 - s) := by
      simp [sub_eq_add_neg]

lemma lem_zetaNsimplified1 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) : zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have happly := lem_applyAbel s N hN
                                               
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    simp [mul_left_comm]
  calc
    zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          simpa using happly
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          - ((-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          simp [sub_eq_add_neg, neg_mul]
    _ = (N : ℂ) ^ (1 - s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          have hpos : 0 < N := (Nat.succ_le_iff).mp hN
          have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
          have hpow := helper_cpow_mul_cpow_neg_eq_cpow_sub (x := (N : ℂ)) (s := s) hNz
          simp [hpow]

lemma lem_floorUdecomp (u : ℝ) : (Int.floor u : ℝ) = u - Int.fract u := by exact (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)

lemma lem_fracPartBound (u : ℝ) : 0 ≤ Int.fract u ∧ Int.fract u < 1 ∧ |Int.fract u| ≤ (1 : ℝ) := by
  constructor
  · exact Int.fract_nonneg u
  · constructor
    · exact Int.fract_lt_one u
    · have hnonneg : 0 ≤ Int.fract u := Int.fract_nonneg u
      have hle : Int.fract u ≤ (1 : ℝ) := le_of_lt (Int.fract_lt_one u)
      simpa [abs_of_nonneg hnonneg] using hle

lemma helper_continuousOn_cpow (r : ℂ) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) := by
  classical
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
  by_cases hr : r = 0
  ·              
    have hconst : (fun u : ℝ => (u : ℂ) ^ r) = fun _ => (1 : ℂ) := by
      funext u; simp [hr]
    simpa [hconst] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
  ·                                        
    have hderiv : HasDerivAt (fun u : ℝ => (u : ℂ) ^ r) (r * t ^ (r - 1)) t :=
      hasDerivAt_ofReal_cpow_const (x := t) (hx := ne_of_gt ht_pos) (r := r) (hr := hr)
    exact hderiv.differentiableAt.continuousAt.continuousWithinAt

lemma helper_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                          
  have hcont1 : ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b) :=
    (Complex.continuous_ofReal).continuousOn
  have hcont2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont1.mul hcont2
                                                            
  have hint_on : IntegrableOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
    simpa using
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
        (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2 hint_on
  exact hint

lemma helper_aestronglyMeasurable_kernel_Icc (s : ℂ) {a b : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Icc a b)) := by
                                
  have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Icc a b)) :=
    (Complex.measurable_ofReal.comp hmeas_fract).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Icc a b)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by measurability
    exact hmeas.aestronglyMeasurable
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_intervalIntegrable_frac_kernel (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                                             
  let μ := volume.restrict (Icc a b)
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
                       
  have hmeas : AEStronglyMeasurable f μ := by simpa [μ, f] using helper_aestronglyMeasurable_kernel_Icc (s := s) (a := a) (b := b)
                                  
  have hbound_ae : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
                                                  
    refine ((ae_restrict_iff' (μ := volume) (s := Icc a b)
      (p := fun u : ℝ => ‖f u‖ ≤ g u) measurableSet_Icc)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro u hu
                    
    have hfract_le1 : ‖(Int.fract u : ℝ)‖ ≤ (1 : ℝ) := by
      simpa using (lem_fracPartBound u).2.2
                           
    have : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp
    have : ‖f u‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp [f]
    have : ‖f u‖ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ :=
      le_trans this (mul_le_mul_of_nonneg_right hfract_le1 (by exact norm_nonneg _))
    simpa [g] using (by simpa [one_mul] using this)
                                             
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hg_int_on : IntegrableOn g (Icc a b) := by
    have hcont_norm : ContinuousOn g (Icc a b) := by
      simpa [g] using (hcont.norm)
    exact hcont_norm.integrableOn_compact isCompact_Icc
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  have hg : Integrable g μ := by simpa [μ] using! hg_int_on
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas hf0 hg
      (by
                                    
        have : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
          simpa [sub_eq_add_neg, norm_neg, μ, f, g] using hbound_ae
        simpa using this)
                                         
  have hf_on : IntegrableOn f (Icc a b) := by simpa [μ, f] using! hf
  simpa using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
      (f := f) hab).2 hf_on

lemma lem_integralSplit (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
                                          
  have hcongr1 :
      (∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) (le_of_lt hu.1)
    have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
      simpa using (natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu0)
    have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hfloorR
    have hIFR : (Int.floor u : ℝ) = u - Int.fract u := lem_floorUdecomp u
    have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hIFR
    have : (Nat.floor u : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := hfloorC.trans hIFC
    simp [this, sub_eq_add_neg]
                               
  have hcongr2 :
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
        = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_mul_cpow_id (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have hI2 : IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_frac_kernel (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have :
        (∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
      intro u hu; simp [sub_mul]
    calc
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := this
      _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
            - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) :=
        (intervalIntegral.integral_sub (μ := volume) (a := (1 : ℝ)) (b := (N : ℝ)) hI1 hI2)
                                              
  have hpow :
      (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu_pos
    have hcx0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
    calc
      (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [Complex.cpow_one]
      _ = (u : ℂ) ^ (1 + (-s - 1)) := by
        simpa using
          (Complex.cpow_add (x := (u : ℂ)) (y := (1 : ℂ)) (z := (-s - 1)) hcx0).symm
      _ = (u : ℂ) ^ (-s) := by
        simp [add_left_comm, sub_eq_add_neg]
             
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := hcongr1
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := hcongr2
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
      simp [hpow]

lemma lem_zetaNsimplified2 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
  have hstep1: _ := lem_zetaNsimplified1 s N hN
  rw [lem_integralSplit] at hstep1
  rw [mul_sub] at hstep1
  rw [hstep1]
  exact (add_sub_assoc _ _ _).symm
  exact hN

lemma lem_evalMainIntegral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notIcc : (0 : ℝ) ∉ Set.Icc (1 : ℝ) (N : ℝ) := by
    intro hx
    exact (not_le.mpr (by norm_num : (0 : ℝ) < 1)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    simp [uIcc_of_le h01leN]
  have hrne : -s ≠ (-1 : ℂ) := by
    intro h
    apply hs
    simpa using congrArg Neg.neg h
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hcond : (-1 < (-s).re) ∨ (-s ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ)) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) hcond)
  have hmul : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
    simpa using congrArg (fun x => s * x) hint
  have hrewrite :
      s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
        = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
    have : s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
          = s * (((N : ℂ) ^ (1 - s) - (1 : ℂ) ^ (1 - s)) / (1 - s)) := by
      simp [add_comm, sub_eq_add_neg]
    have h1pow : (1 : ℂ) ^ (1 - s) = 1 := by simp
    simpa [h1pow] using this
  have hsplit : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
      = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
    have h1 : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
        = (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s) := by
      simpa using (mul_div_assoc s ((N : ℂ) ^ (1 - s) - 1) (1 - s)).symm
    have h2 : (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s)
        = (s / (1 - s)) * ((N : ℂ) ^ (1 - s) - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_mul_eq_mul_div (a := s) (b := (1 - s)) (c := ((N : ℂ) ^ (1 - s) - 1))).symm
    exact h1.trans h2
  calc
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
        = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := hmul
    _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := hrewrite
    _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := hsplit

lemma lem_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
                                                                         
  have hstep := lem_zetaNsimplified2 s N hN
                                                       
  rw [lem_evalMainIntegral s hs N hN] at hstep

  have hden : (1 - s) ≠ 0 := by
    intro h
    have h1 : 1 = s := by simpa [sub_eq_zero] using h
    have h2 : s = 1 := h1.symm
    exact hs h2
  let A := (N : ℂ) ^ (1 - s)
                                                                             
  have h1 : (1 - s) * (A + s / (1 - s) * (A - 1)) = A - s := by
    calc
      (1 - s) * (A + s / (1 - s) * (A - 1))
          = (1 - s) * A + (1 - s) * (s / (1 - s) * (A - 1)) := by ring
      _ = (1 - s) * A + s * (A - 1) := by field_simp [hden]
      _ = A - s := by ring
  have h2 : (1 - s) * (A / (1 - s) + 1 + 1 / (s - 1)) = A - s := by
    have hne : s - 1 ≠ 0 := by simpa [sub_eq_zero] using hs
    field_simp [hden, hne] <;> ring
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)

  rw [halg] at hstep
  exact hstep

lemma complex_tendsto_zero_iff_norm_tendsto_zero {α : Type*} {f : α → ℂ} {l : Filter α} :
    Tendsto f l (𝓝 0) ↔ Tendsto (fun x => ‖f x‖) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_zero_right]

lemma complex_norm_natCast_cpow (N : ℕ) (w : ℂ) (hN : 0 < N) :
    ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
  have hNnz : (N : ℂ) ≠ 0 := by
    simp [Ne, Nat.cast_eq_zero]
    exact ne_of_gt hN
  rw [Complex.norm_cpow_of_ne_zero hNnz]
  rw [Complex.norm_natCast]
  rw [Complex.natCast_arg]
  simp [Real.exp_zero]

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [complex_tendsto_zero_iff_norm_tendsto_zero]
                                
  have h1 : ∀ᶠ (N : ℕ) in atTop, ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact complex_norm_natCast_cpow N w hN
  rw [tendsto_congr' h1]

  have hw_pos : 0 < -w.re := neg_pos.mpr hw
                                 
  have h_eq : w.re = -(-w.re) := by ring
  rw [h_eq]
                                                                                               
  have h_comp : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h_rpow : Tendsto (fun x : ℝ => x ^ (-(-w.re))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hw_pos
  exact Tendsto.comp h_rpow h_comp

lemma lem_limitTerm1 (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_natCast_cpow_zero_of_neg_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma lem_integrandBound (u : ℝ) (hu : 1 ≤ u) (s : ℂ) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                  
  set a : ℂ := ((Int.fract u : ℝ) : ℂ)
  set b : ℂ := (u : ℂ) ^ (-s - 1)
                  
  have hfract_le1 : ‖a‖ ≤ (1 : ℝ) := by
    simpa [a, Complex.norm_real] using (lem_fracPartBound u).2.2
                          
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
                                                     
  have h₁ : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by simp
  have h₂ : ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ :=
    mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
  have h₃ : ‖a * b‖ ≤ 1 * ‖b‖ := le_trans h₁ h₂
  have hle : ‖a * b‖ ≤ ‖b‖ := by simpa [one_mul] using h₃
                                                                   
  have hb : ‖b‖ = u ^ ((-s - 1).re) := by
    simpa [b] using
      Complex.norm_cpow_eq_rpow_re_of_pos (x := u) (hx := hu0) (y := -s - 1)
                                           
  have hexp : (-s - 1).re = -s.re - 1 := by
    simp [sub_eq_add_neg]
                                                       
  calc
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
        = ‖a * b‖ := rfl
    _ ≤ ‖b‖ := hle
    _ = u ^ ((-s - 1).re) := hb
    _ = u ^ (-s.re - 1) := by simp [hexp]

lemma lem_integrandBoundeps (ε : ℝ) (_hε : 0 < ε) (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : ε ≤ s.re) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
  have h1 : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := lem_integrandBound u hu s
  have h2 : -s.re - 1 ≤ -1 - ε := by linarith [hs]
  have h3 : u ^ (-s.re - 1) ≤ u ^ (-1 - ε) := Real.rpow_le_rpow_of_exponent_le hu h2
  exact le_trans h1 h3

lemma lem_triangleInequality_add (z₁ z₂ : ℂ) :
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  exact norm_add_le z₁ z₂

lemma helper_integral_interval_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b) (hac : IntervalIntegrable f volume a c) :
    ((∫ x in a..b, f x) - ∫ x in a..c, f x) = ∫ x in c..b, f x := by
  simpa using
    (intervalIntegral.integral_interval_sub_left (μ := volume) (f := f) (a := a) (b := b) (c := c)
      hab hac)

lemma helper_integral_rpow_eval {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
                                         
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    have : ¬ m ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one hm)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by
    simpa [uIcc_of_le hmn] using h0notIcc
                              
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    have hplus := congrArg (fun t => t + 1) h
    have hminus : -ε = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hplus
    have hε0 : ε = 0 := by simpa using congrArg Neg.neg hminus
    exact (ne_of_gt hε) hε0
                                               
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    have hcond : (-1 < (-1 - ε)) ∨ ((-1 - ε) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc m n) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_rpow (a := m) (b := n) (r := -1 - ε) hcond)
                                                      
  have h1 : ((-1 - ε) + 1) = -ε := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
    simpa [h1]
      using hint
  have hnegnum : -(n ^ (-ε) - m ^ (-ε)) = m ^ (-ε) - n ^ (-ε) := by
    simp
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ (-ε) - m ^ (-ε)) / (-ε) := this
    _ = (n ^ (-ε) - m ^ (-ε)) * ((-ε)⁻¹) := by simp [div_eq_mul_inv]
    _ = (n ^ (-ε) - m ^ (-ε)) * (-(ε⁻¹)) := by simp [inv_neg]
    _ = -((n ^ (-ε) - m ^ (-ε)) * ε⁻¹) := by simp [mul_neg]
    _ = (-(n ^ (-ε) - m ^ (-ε))) * ε⁻¹ := by
      simpa using (neg_mul (n ^ (-ε) - m ^ (-ε)) (ε⁻¹)).symm
    _ = (m ^ (-ε) - n ^ (-ε)) * ε⁻¹ := by
      simp
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by simp [div_eq_mul_inv]

lemma helper_integral_rpow_le {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  have heval := helper_integral_rpow_eval (ε := ε) hε hm hmn
  have hn0 : 0 ≤ n := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans h01 (le_trans hm hmn)
  have hsub_le : m ^ (-ε) - n ^ (-ε) ≤ m ^ (-ε) := by
    exact sub_le_self _ (Real.rpow_nonneg hn0 (-ε))
  have hinv_nonneg : 0 ≤ ε⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hε)
  have hdiv_le : ((m ^ (-ε) - n ^ (-ε)) / ε) ≤ (m ^ (-ε) / ε) := by
    have := mul_le_mul_of_nonneg_right hsub_le hinv_nonneg
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (m ^ (-ε) - n ^ (-ε)) / ε := heval
    _ ≤ m ^ (-ε) / ε := hdiv_le
    _ = (1 / ε) * m ^ (-ε) := by simp [div_eq_mul_inv, mul_comm]

lemma helper_tendsto_nat_rpow_neg (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε)) atTop (𝓝 0) := by
                                                                              
  have hcont : Tendsto (fun x : ℝ => x ^ (-ε)) atTop (𝓝 0) := by
                                                                              
    simpa using (tendsto_rpow_neg_atTop (y := ε) hε)

  have hcoe : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop

  have : Tendsto ((fun x : ℝ => x ^ (-ε)) ∘ fun n : ℕ => (n : ℝ)) atTop (𝓝 0) :=
    hcont.comp hcoe
                                       
  simpa using! this

lemma helper_exists_limit_of_tail_bound (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb_nonneg : ∀ m, 0 ≤ b m)
    (hb_tendsto : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m) :
    ∃ l : ℂ, Tendsto a atTop (𝓝 l) := by
  classical
                                              
  have hCauchy : CauchySeq a := by
                                      
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
                                                               
    have h_ball : ∀ᶠ m in atTop, dist (b m) 0 < ε / 2 := by
      exact hb_tendsto (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    have h_b_lt : ∀ᶠ m in atTop, b m < ε / 2 := by
      refine h_ball.mono ?_
      intro m hm
      have : |b m| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hm
      simpa [abs_of_nonneg (hb_nonneg m)] using this
                                  
    rcases eventually_atTop.1 hbound with ⟨M1, hM1⟩
    rcases eventually_atTop.1 h_b_lt with ⟨M2, hM2⟩
    let M := max M1 M2
    have hPM : ∀ᶠ n in atTop, M ≤ n → ‖a n - a M‖ ≤ b M := by
      have h' := hM1 M (le_max_left _ _)
      exact h'
    have hMb : b M < ε / 2 := hM2 M (le_max_right _ _)
    rcases eventually_atTop.1 hPM with ⟨N0, hN0⟩
    refine ⟨max N0 M, ?_⟩
    intro n hn k hk
    have hMn : M ≤ n := le_trans (le_max_right _ _) hn
    have hMk : M ≤ k := le_trans (le_max_right _ _) hk
    have hN0n : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hN0k : N0 ≤ k := le_trans (le_max_left _ _) hk
    have h1 : ‖a n - a M‖ ≤ b M := (hN0 n hN0n) hMn
    have h2 : ‖a k - a M‖ ≤ b M := (hN0 k hN0k) hMk
                                           
    have htri : ‖a n - a k‖ ≤ ‖a n - a M‖ + ‖a M - a k‖ := by
      have h := norm_add_le (a n - a M) (a M - a k)
      simpa [sub_add_sub_cancel (a n) (a M) (a k)] using h
    have h2' : ‖a M - a k‖ ≤ b M := by simpa [norm_sub_rev] using h2
    have hsumle : ‖a n - a k‖ ≤ b M + b M :=
      le_trans htri (add_le_add h1 h2')
    have hsumlt : b M + b M < ε := by
      have := add_lt_add hMb hMb
      simpa [add_halves] using this
    have : ‖a n - a k‖ < ε := lt_of_le_of_lt hsumle hsumlt
    simpa [dist_eq_norm] using this
                                                 
  rcases cauchySeq_tendsto_of_complete (u := a) hCauchy with ⟨l, hl⟩
  exact ⟨l, hl⟩

lemma helper_intervalIntegrable_rpow_neg {ε : ℝ} {a b : ℝ} (_hε : 0 < ε)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume a b := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc a b := by
    intro hx
    have : ¬ a ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ha)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc a b := by
    simpa [uIcc_of_le hab] using h0notIcc
  simpa using
    (intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b) (r := -1 - ε)
      (Or.inr h0not))

lemma helper_one_le_of_mem_Ioc {m n u : ℝ} (hm : 1 ≤ m) (hu : u ∈ Ioc m n) : 1 ≤ u := by
  exact le_trans hm (le_of_lt hu.1)

lemma helper_integrableOn_of_bound_Ioc {m n : ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
  (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc m n)))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioc m n)), ‖f u‖ ≤ g u)
  (hg : IntegrableOn g (Ioc m n) volume) :
  IntegrableOn f (Ioc m n) volume := by
                                                                    
  let μ := volume.restrict (Ioc m n)
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by
    simp
                             
  have hg' : Integrable g μ := by
    simpa [μ] using! hg
                                           
  have hmeas' : AEStronglyMeasurable f μ := by
    simpa [μ] using hmeas
                                               
  have hineq : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
    simpa [μ, sub_eq_add_neg, norm_neg] using hbound
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas' hf0 hg' hineq
                                     
  simpa [μ] using! hf

lemma helper_aestronglyMeasurable_kernel_Ioc (s : ℂ) {m n : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Ioc m n)) := by
                                                           
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Ioc m n)) := by
    have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    have hmeas_coe : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hmeas_fract)
    exact hmeas_coe.aestronglyMeasurable
                                                        
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioc m n)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
      measurability
    exact hmeas.aestronglyMeasurable
                                             
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_aebound_kernel_Ioc {ε : ℝ} (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (_hmn : m ≤ n) :
    ∀ᵐ u ∂(volume.restrict (Ioc m n)),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
                                                                                             
  refine
    ((ae_restrict_iff' (μ := volume) (s := Ioc m n)
        (p := fun u : ℝ => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε))
        measurableSet_Ioc)).2 ?_
                                                  
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu1 : 1 ≤ u := helper_one_le_of_mem_Ioc hm hu
  simpa using (lem_integrandBoundeps ε hε u hu1 s hs)

lemma helper_integrableOn_rpow_neg_Ioc {ε : ℝ} (hε : 0 < ε)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntegrableOn (fun u : ℝ => u ^ (-1 - ε)) (Ioc m n) volume := by
  have hInt : IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume m n :=
    helper_intervalIntegrable_rpow_neg (ε := ε) hε hm hmn
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (f := fun u : ℝ => u ^ (-1 - ε)) hmn).1 hInt

lemma helper_tendsto_const_mul_zero (c : ℝ) {f : ℕ → ℝ}
  (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c * f n) atTop (𝓝 0) := by
  simpa using (Filter.Tendsto.const_mul (b := c) h)

lemma helper_limit_norm_le_of_eventual_bound {a : ℕ → ℂ} {l : ℂ} {B : ℝ}
  (h : Tendsto a atTop (𝓝 l)) (hbound : ∀ᶠ n in atTop, ‖a n‖ ≤ B) : ‖l‖ ≤ B := by
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖l‖) := (Filter.Tendsto.norm h)
  exact le_of_tendsto hnorm hbound

lemma lem_integralConvergence (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re) :
    ∃ I : ℂ,
      Tendsto
        (fun N : ℕ =>
          ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
        atTop (𝓝 I)
      ∧ ‖I‖ ≤ (1 / ε) := by
  classical
                
  let fC : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  let gR : ℝ → ℝ := fun u => u ^ (-1 - ε)
  let a : ℕ → ℂ := fun N => ∫ u in (1 : ℝ)..(N : ℝ), fC u
  let b : ℕ → ℝ := fun m => (1 / ε) * (m : ℝ) ^ (-ε)
          
  have hb_nonneg : ∀ m, 0 ≤ b m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hpow : 0 ≤ (m : ℝ) ^ (-ε) := Real.rpow_nonneg hm0 _
    have hpos : 0 ≤ 1 / ε := by exact le_of_lt (one_div_pos.mpr hε)
    have := mul_le_mul_of_nonneg_left hpow hpos
    simpa [b] using this
          
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have hpow := helper_tendsto_nat_rpow_neg (ε := ε) hε
    have hmul := helper_tendsto_const_mul_zero (c := (1 / ε)) hpow
    simpa [b] using hmul
                                    
  have h_tail_pointwise : ∀ m n : ℕ, 1 ≤ m → m ≤ n → ‖a n - a m‖ ≤ b m := by
    intro m n hm1 hmn
                        
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
                                                                                     
    have hInt_f_1n : IntervalIntegrable fC volume (1 : ℝ) (n : ℝ) := by
                              
      have h1nNat : 1 ≤ n := le_trans hm1 hmn
      have h1nR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1nNat
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (n : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (n : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (hmn := h1nR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (_hmn := h1nR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (n : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (n : ℝ)) (f := fC) h1nR).2 hintOn
    have hInt_f_1m : IntervalIntegrable fC volume (1 : ℝ) (m : ℝ) := by
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (m : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (m : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (hmn := hmR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (_hmn := hmR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (m : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (m : ℝ)) (f := fC) hmR).2 hintOn
    have hdiff := helper_integral_interval_sub_left
      (E := ℂ) (f := fC) (a := (1 : ℝ)) (b := (n : ℝ)) (c := (m : ℝ))
      (hab := hInt_f_1n) (hac := hInt_f_1m)
    have hsub : a n - a m = ∫ u in (m : ℝ)..(n : ℝ), fC u := by
      simpa [a] using hdiff
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs
      (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (_hmn := hmnR)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (m : ℝ) (n : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (m : ℝ) (n : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_mn : IntervalIntegrable gR volume (m : ℝ) (n : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (m : ℝ)) (b := (n : ℝ)) (f := gR) hmnR).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR))
                                      
    have h1 : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ ∫ u in (m : ℝ)..(n : ℝ), gR u := by
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (m : ℝ)) (b := (n : ℝ)) (f := fC) (g := gR)
          (hab := hmnR) (h := hbound_Ioc_imp) (hbound := hgInt_mn))
                                            
    have h3 : ∫ u in (m : ℝ)..(n : ℝ), gR u ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      helper_integral_rpow_le (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR)
              
    have : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      le_trans h1 h3
    simpa [hsub, b] using this
                        
  have hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m := by
    have h_m_ge1 : ∀ᶠ m in atTop, 1 ≤ m := eventually_ge_atTop 1
    refine h_m_ge1.mono ?_
    intro m hm1
    have h_n_ge_m : ∀ᶠ n in atTop, m ≤ n := eventually_ge_atTop m
    exact h_n_ge_m.mono (fun n hmn => by intro hle; exact h_tail_pointwise m n hm1 hle)
                           
  rcases helper_exists_limit_of_tail_bound a b hb_nonneg hb_tendsto hbound with ⟨I, hT⟩
                                    
  have h_eventual_bound : ∀ᶠ N in atTop, ‖a N‖ ≤ (1 / ε) := by
    have hN1 : ∀ᶠ N in atTop, 1 ≤ N := eventually_ge_atTop 1
    refine hN1.mono ?_
    intro N hNge1
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge1
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (_hmn := h1N)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (1 : ℝ) (N : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (1 : ℝ) (N : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_1N : IntervalIntegrable gR volume (1 : ℝ) (N : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (N : ℝ)) (f := gR) h1N).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N))
                                      
    have h1 : ‖∫ u in (1 : ℝ)..(N : ℝ), fC u‖ ≤ ∫ u in (1 : ℝ)..(N : ℝ), gR u := by
      simpa [a] using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (1 : ℝ)) (b := (N : ℝ)) (f := fC) (g := gR)
          (hab := h1N) (h := hbound_Ioc_imp) (hbound := hgInt_1N))
                                    
    have h3 : ∫ u in (1 : ℝ)..(N : ℝ), gR u ≤ (1 / ε) := by
      have := helper_integral_rpow_le (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N)
      simpa [one_div, Real.one_rpow, one_mul] using this
    have : ‖a N‖ ≤ (1 / ε) := by exact le_trans h1 h3
    exact this
                                              
  have hIle : ‖I‖ ≤ (1 / ε) :=
    helper_limit_norm_le_of_eventual_bound (a := a) (l := I) (B := 1 / ε) hT h_eventual_bound
                                                   
  refine ⟨I, ?_, hIle⟩
  simpa [a, fC] using hT

lemma helper_tendsto_zetaPartialSum_to_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  classical
                                                                                    
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
                          
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using (ne_of_gt this)
                                                          
  have hsum_div : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hgSumm : Summable g := by
    simpa [g, one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hsum_div
                                                   
  have h_eq_tail : (fun n => g (n + 1)) = h := by
    funext n; simp [g, h]
  have hhSumm : Summable h := by
    have : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [h_eq_tail] using this
                                                                         
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n : ℕ, h n) = ∑' n : ℕ, g n := by
    have hzero_add := (Summable.tsum_eq_zero_add (f := g) hgSumm)
                                                         
    have : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n + 1) := by
      simpa [hg0, add_comm] using hzero_add
    simpa [h_eq_tail] using this.symm
                                             
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    simpa [g] using lem_zetaLimit s hs
                                                                         
  have h_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h n) atTop (𝓝 (∑' n, h n)) :=
    (Summable.tendsto_sum_tsum_nat hhSumm)
                                                               
  have htsumeq : (∑' n, h n) = riemannZeta s := h_tsum_eq.trans hzeta.symm
  simpa [zetaPartialSum, htsumeq, h] using h_tendsto

lemma integrableOn_of_ae_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {g : ℝ → ℝ} {s : Set ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict s))
    (hgint : IntegrableOn g s)
    (hbound : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ g x) :
    IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hgint
  have hf' : Integrable f (volume.restrict s) :=
    MeasureTheory.Integrable.mono' (μ := volume.restrict s) hg' hfm hbound
  simpa [IntegrableOn] using hf'

lemma kernel_aestronglyMeasurable_on_Ioi (s : ℂ) (a : ℝ) :
  AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioi a)) := by
                                                                                                           
  have hmeas_fract : Measurable (fun u : ℝ => (Int.fract u : ℝ)) := by
    simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have hmeas_fractC : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
    hmeas_fract.complex_ofReal
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
    have hmeas_ofReal : Measurable (fun u : ℝ => (u : ℂ)) := Complex.measurable_ofReal
    simpa using hmeas_ofReal.pow_const (-s - 1)
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) :=
    hmeas_fractC.mul hmeas_cpow
                                                                                                  
  simpa using hmeas.aestronglyMeasurable

lemma kernel_ae_bound_on_Ioi (s : ℂ) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                          
  let p : ℝ → Prop := fun u => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1)
                             
  have hAll : ∀ u ∈ Ioi (1 : ℝ), p u := by
    intro u hu
    have hu' : (1 : ℝ) ≤ u := le_of_lt hu
    dsimp [p]
    simpa using (lem_integrandBound u hu' s)
                                                          
  have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    MeasureTheory.ae_of_all _ hAll
                                                              
  have hiff :
      (∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)), p u) ↔ ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ)) (p := p)) measurableSet_Ioi
  exact hiff.mpr hAE

lemma helper_intervalIntegral_tendstoIoi_kernel (s : ℂ) (hs : 1 < s.re) :
  Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
    (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
                                                                    
  have hfm : AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) := by
    simpa using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
  have hbound' : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                                      
    simpa using kernel_ae_bound_on_Ioi (s := s)
  have hlt : (-s.re - 1) < (-1 : ℝ) := by linarith
  have hpos : 0 < (1 : ℝ) := by norm_num
  have hgint : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (a := (-s.re - 1)) (c := (1 : ℝ)) hlt hpos
  have hint : IntegrableOn (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
                              
    exact integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) hfm hgint hbound'
                                                   
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (a := (1 : ℝ))
      (b := fun N : ℕ => (N : ℝ)) hint hb)

lemma helper_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  simpa using (lem_zetaNfinal s hs N hN)

lemma helper_eventually_eq_from_zetaNfinal (s : ℂ) (hs : s ≠ 1) :
  ∀ᶠ N in atTop,
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hEv : ∀ᶠ N : ℕ in atTop, 1 ≤ N := Filter.eventually_ge_atTop (1 : ℕ)
  refine hEv.mono ?_
  intro N hN
  simpa using (helper_zetaNfinal s hs N hN)

lemma helper_limit_scaled_cpow (s : ℂ) (hs : 1 < s.re) (_hsne : s ≠ 1) :
  Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
  have h := lem_limitTerm1 s hs
  have h' := (Filter.Tendsto.const_mul (b := (1 / (1 - s))) h)
  simpa [div_eq_mul_inv, mul_comm] using h'

lemma helper_tendsto_const_mul {f : ℕ → ℂ} {l : ℂ} (c : ℂ)
  (h : Tendsto f atTop (𝓝 l)) : Tendsto (fun n => c * f n) atTop (𝓝 (c * l)) := by
  exact h.const_mul c

lemma helper_tendsto_add {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n + g n) atTop (𝓝 (a + b)) := by
                                                   
  have hpair : Tendsto (fun n => (f n, g n)) atTop (𝓝 (a, b)) := by
    simpa using (hf.prodMk_nhds hg)
  have hadd : Continuous (fun p : ℂ × ℂ => p.1 + p.2) := by
    simpa using! (continuous_fst.add continuous_snd)
  simpa using! ((hadd.tendsto (a, b)).comp hpair)

lemma helper_tendsto_neg {f : ℕ → ℂ} {a : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun n => - f n) atTop (𝓝 (-a)) := by
  simpa only [Function.comp_def] using! ((continuous_neg.tendsto a).comp hf)

lemma helper_tendsto_sub {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n - g n) atTop (𝓝 (a - b)) := by
  have hneg : Tendsto (fun n => - g n) atTop (𝓝 (-b)) :=
    helper_tendsto_neg (f := g) (a := b) hg
  simpa [sub_eq_add_neg] using
    helper_tendsto_add (f := f) (g := fun n => - g n) hf hneg

lemma lem_zetaFormula (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s
      = 1 + 1 / (s - 1)
        - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  classical
                          
  have hsne : s ≠ 1 := by
    intro h
    have hlt : 1 < (1 : ℝ) := by simp [h, Complex.one_re] at hs
    exact (lt_irrefl _ ) hlt
                                                           
  let G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
                                          
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N := by
    simpa [G] using helper_eventually_eq_from_zetaNfinal s hsne
                                  
  have h_ps : Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) :=
    helper_tendsto_zetaPartialSum_to_zeta s hs
                                      
  have hG_to_zeta : Tendsto G atTop (𝓝 (riemannZeta s)) := by
    have hcongr := (Filter.tendsto_congr' (hl := hEv) :
      Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) ↔
      Tendsto G atTop (𝓝 (riemannZeta s)))
    exact hcongr.mp h_ps

  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) :=
    helper_limit_scaled_cpow s hs hsne
                                  
  have hK : Tendsto (fun _ : ℕ => (1 : ℂ) + 1 / (s - 1)) atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) :=
    tendsto_const_nhds
                                             
  have hInt : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_intervalIntegral_tendstoIoi_kernel s hs
                           
  have hIntMul : Tendsto (fun N : ℕ => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_tendsto_const_mul (c := s) hInt
                                             
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 : ℂ) + 1 / (s - 1)
  have hA2 : Tendsto Aseq atTop (𝓝 0) := by simpa [Aseq] using hA
  have hK2 : Tendsto Kseq atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) := by simp [Kseq]
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (0 + ((1 : ℂ) + 1 / (s - 1)))) :=
    helper_tendsto_add (hf := hA2) (hg := hK2)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hIseq : Tendsto Iseq atTop (𝓝 (s * ∫ u in Ioi (1 : ℝ),
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
    simpa [Iseq] using hIntMul
  have hG_limit : Tendsto G atTop
      (𝓝 ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)))) := by
    have hSub := helper_tendsto_sub (hf := hSum) (hg := hIseq)
                                            
    have hGdef : (fun N => (Aseq N + Kseq N) - Iseq N) = G := by
      funext N; simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef]
      using hSub
                                                    
  have huniq :=
    tendsto_nhds_unique (f := G) (l := atTop)
      (a := riemannZeta s)
      (b := ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))))
      (ha := hG_to_zeta) (hb := hG_limit)
                                     
  simpa [zero_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using huniq

lemma lem_zetaanalOnnot1 : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
                                                                             
  have hset : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext z; simp
  have hopen : IsOpen ({s : ℂ | s ≠ 1}) := by
    simp [hset]
                                               
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
    intro z hz

    simpa using (differentiableAt_riemannZeta (by simpa [Set.mem_ofPred_eq] using hz)).differentiableWithinAt
  simpa [Complex.analyticOn_iff_differentiableOn hopen] using hdiff

lemma lem_zetaanalS : (let S := {s : ℂ | s ≠ 1}; AnalyticOn ℂ riemannZeta S) := by exact lem_zetaanalOnnot1

lemma lem_S_isOpen : (let S := {s : ℂ | s ≠ 1}; IsOpen S) := by
                                                            
  have h : {s : ℂ | s ≠ 1} = {(1 : ℂ)}ᶜ := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h]
  exact isOpen_compl_singleton

lemma lem_T_isOpen : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsOpen T) := by
                                      
  show IsOpen {s : ℂ | s ≠ 1 ∧ 1/10 < s.re}

  apply IsOpen.and
  ·                           
    exact lem_S_isOpen
  ·                                 
                                                             
    have h_eq : {s : ℂ | 1/10 < s.re} = Complex.re ⁻¹' (Set.Ioi (1/10)) := by
      ext s
      simp [Set.mem_preimage, Set.mem_Ioi]
    rw [h_eq]
    exact Complex.continuous_re.isOpen_preimage (Set.Ioi (1/10)) isOpen_Ioi

lemma inter_compl_singleton_eq_diff {α : Type*} [DecidableEq α] (A : Set α) (x : α) :
  A ∩ ({x} : Set α)ᶜ = A \ ({x} : Set α) := by
  ext z; simp [Set.mem_inter_iff, Set.mem_singleton_iff]

lemma isPathConnected_punctured_halfplane_re_gt (a : ℝ) (p : ℂ) (hp : a < p.re) :
  IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
                                                                 
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
                            
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
                    
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
                           
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
                          
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
                               
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    ·         
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    ·         
      simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    ·         
      simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    ·         
      simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
                      
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    ·               
      refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    ·               
      refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
                                      
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
                                                 
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
                            
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      ·                        
        exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      ·                                             
        rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        ·                    
          exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        ·                                                
          have hz_eq : z = p := by
                                              
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by
              simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by
              simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
                                            
              simp [heq, himeq]
                                
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        ·                    
          exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      ·                         
        exact Or.inr (Or.inr hgt)
    · intro hz
                        
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          ·             
            intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          ·             
            intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
             
  simpa [hcover] using hUnionPC

lemma aestronglyMeasurable_kernel_param_deriv (z : ℂ) :
  AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
                                                                  
  let μ := volume.restrict (Ioi (1 : ℝ))
                                                                                                 
  have hmeas_logR : Measurable (fun u : ℝ => Real.log u) := Real.measurable_log
  have hmeas_logC : Measurable (fun u : ℝ => ((Real.log u) : ℂ)) := hmeas_logR.complex_ofReal
  have hmeas_neg : Measurable (fun u : ℝ => -((Real.log u) : ℂ)) := hmeas_logC.neg
  have h1 : AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ)) μ := by
    simpa [μ] using hmeas_neg.aestronglyMeasurable
                                                                                 
  have h2 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) μ := by
    simpa [μ] using kernel_aestronglyMeasurable_on_Ioi (s := z) (a := (1 : ℝ))
                                      
  have hmul : AEStronglyMeasurable
      (fun u : ℝ => (-((Real.log u) : ℂ)) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)))
      μ := (MeasureTheory.AEStronglyMeasurable.mul h1 h2)
  simpa [μ] using hmul

lemma kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
  ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖ ≤ Real.log u * u ^ (-1 - ε) := by
                                       
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
                                                                  
  have hinner1 : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-x.re - 1) := by
    simpa using (lem_integrandBound u hu1 x)
  have hexp_le : -x.re - 1 ≤ -1 - ε := by linarith
  have hmono : u ^ (-x.re - 1) ≤ u ^ (-1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hu1 hexp_le
  have hinner : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-1 - ε) :=
    le_trans hinner1 hmono
                      
  have hmul : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
      = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := by
    simp
  have hnorm_nonneg : 0 ≤ ‖-((Real.log u) : ℂ)‖ := by simp
  have hmul_le : ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖
      ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := by
    exact mul_le_mul_of_nonneg_left hinner hnorm_nonneg
                                                                  
  have hlognorm_neg : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
             
  calc
    ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
        = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := hmul
    _ ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := hmul_le
    _ = (Real.log u) * u ^ (-1 - ε) := by simp [hlognorm_neg, mul_comm]

lemma exists_radius_ball_two_step_subset_halfspace (s : ℂ) {ε : ℝ} (hε : ε < s.re) :
  ∃ δ > 0, ∀ x, dist x s < δ → ∀ y, dist y x < δ → ε ≤ y.re := by
                                  
  set δ : ℝ := (s.re - ε) / 2 with hδdef
  have hpos : 0 < s.re - ε := sub_pos.mpr hε
  have hδpos : 0 < δ := by simpa [hδdef] using (half_pos hpos)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy
                                                                           
  have htri : dist y s ≤ dist y x + dist x s := by
    simpa using (dist_triangle y x s)
  have hsumlt : dist y x + dist x s < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - s‖ < δ + δ := by
    have := lt_of_le_of_lt htri hsumlt
    simpa [dist_eq_norm] using this
  have hdeltaSum : δ + δ = s.re - ε := by
    simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - s‖ < s.re - ε := by simpa [hdeltaSum] using hnorm_lt
                                  
  have h_eps_lt : ε < s.re - ‖y - s‖ := by
    have hsum' : ε + ‖y - s‖ < s.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_right hnorm_lt_re ε)
    simpa [lt_sub_iff_add_lt] using hsum'
                                       
  have hre_abs : |(y - s).re| ≤ ‖y - s‖ := by
    simpa using (Complex.abs_re_le_norm (y - s))
  have hre_lower : -‖y - s‖ ≤ (y - s).re := by
                                                  
    have hpair := (abs_le.mp hre_abs)
    exact hpair.left
  have hyge : s.re - ‖y - s‖ ≤ y.re := by
    have h' : s.re + (-‖y - s‖) ≤ s.re + (y - s).re := add_le_add_right hre_lower s.re
    have h'' : s.re + (y - s).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
                                            
  have hygt : ε < y.re := lt_of_lt_of_le h_eps_lt hyge
  exact le_of_lt hygt

lemma integrable_kernel_at_param (s : ℂ) (hs : 0 < s.re) :
  Integrable ((fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
  classical
                                                
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set ε : ℝ := s.re / 2
  set g1 : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
                                           
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [f] using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
                       
  have hε : 0 < ε := by
    have : 0 < s.re := hs
    simpa [ε] using (half_pos this)
  have hεle : ε ≤ s.re := by
    have hnonneg : 0 ≤ s.re := le_of_lt hs
    simpa [ε] using (half_le_self hnonneg)
                                            
  have hbound1 : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g1 u := by
    simpa [f, g1] using (kernel_ae_bound_on_Ioi (s := s))
                                             
  have hpow_ae : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), g1 u ≤ g u := by
                                      
    have hAll : ∀ u ∈ Ioi (1 : ℝ), g1 u ≤ g u := by
      intro u hu
      have hx : (1 : ℝ) ≤ u := le_of_lt hu
      have hlexp : (-s.re - 1) ≤ (-1 - ε) := by linarith
      have := Real.rpow_le_rpow_of_exponent_le hx hlexp
      simpa [g1, g] using this
                                           
    have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → g1 u ≤ g u :=
      MeasureTheory.ae_of_all _ hAll
    have hiff :=
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ))
        (p := fun u => g1 u ≤ g u) measurableSet_Ioi)
    exact hiff.mpr hAE
                   
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g u := by
    filter_upwards [hbound1, hpow_ae] with u hu1 hu2
    exact le_trans hu1 hu2
                                               
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    have ha_lt : (-1 - ε) < (-1 : ℝ) := by linarith
    have hc : 0 < (1 : ℝ) := by norm_num
    simpa [g] using (integrableOn_Ioi_rpow_of_lt (a := (-1 - ε)) (ha := ha_lt) (c := (1 : ℝ)) (hc := hc))
                                        
  have hint : IntegrableOn f (Ioi (1 : ℝ)) :=
    integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) (f := f) (g := g)
      (hfm := hfm) (hgint := hgint) (hbound := hbound)
  simpa [IntegrableOn, f] using hint

lemma eventually_aestronglyMeasurable_kernel_param (s : ℂ) :
  ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) (volume.restrict (Ioi (1 : ℝ))) := by
  refine Filter.Eventually.of_forall ?_
  intro z
                                
  have hmeas_fract : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) := by
    have hmeas_fr : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    exact (Complex.measurable_ofReal.comp hmeas_fr)
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-z - 1)) := by
                                                                                
    measurability
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) :=
    hmeas_fract.mul hmeas_cpow
  simpa using hmeas.aestronglyMeasurable

lemma hasDerivAt_kernel_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
  HasDerivAt (fun w : ℂ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))
    ( -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) ) z := by
                       
  set c0 : ℂ := ((Int.fract u : ℝ) : ℂ)
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu0
  have hcz : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
                                      
  have hfneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfneg.sub_const (1 : ℂ)
                                         
  have hbase : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) (hf := hf) (h0 := Or.inl hcz)
  have hbase' : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
                        
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
                            
  have hmul : HasDerivAt (fun w : ℂ => c0 * ((u : ℂ) ^ (-w - 1)))
      (c0 * (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1))) z :=
    HasDerivAt.const_mul c0 hbase'
                                             
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (Complex.ofReal_log (x := u) (hx := le_of_lt hu0))
                        
  simpa [c0, hlog, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ)
  (hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, HasDerivAt (fun w => F w u) (F' z u) z)
  :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
                                                                                                 
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (hs := Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint)
      (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int)
      (h_diff := hderiv)
  rcases h with ⟨_hint, hDeriv⟩
                                                                                 
  simpa using hDeriv

lemma analyticAt_of_eventually_differentiableAt {f : ℂ → ℂ} {s : ℂ}
  (h : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ f z) : AnalyticAt ℂ f s := by
  simpa using
    (Complex.analyticAt_iff_eventually_differentiableAt (f := f) (c := s)).2 h

lemma lem_integralAnalytic (s : ℂ) (hs : 1/10 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
  classical
                                                            
  have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1/10) hs
  set ε : ℝ := s.re / 2 with hεdef
  have hεpos : 0 < ε := by simpa [ε] using (half_pos hspos)
  have hεlt : ε < s.re := by
    have : s.re / 2 < s.re := by simpa [ε] using (half_lt_self hspos)
    simpa [ε] using this
                                                                        
  rcases exists_radius_ball_two_step_subset_halfspace (s := s) (ε := ε) hεlt with ⟨δ, hδpos, hδprop⟩
                                                            
  let F : ℂ → ℝ → ℂ := fun z u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
                                                 
  let bound : ℝ → ℝ := fun u => (2/ε) * u ^ (-1 - (ε/2))
                                                     
  have hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have hlt : (-1 - (ε/2)) < (-1 : ℝ) := by
      have : 0 < ε/2 := by simpa using (half_pos hεpos)
      linarith
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    have hpow_int : IntegrableOn (fun u : ℝ => u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) := by
      simpa using (integrableOn_Ioi_rpow_of_lt (a := (-1 - (ε/2))) hlt (c := (1 : ℝ)) hpos1)
    have hconst : IntegrableOn (fun u : ℝ => (2/ε) * u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) :=
      hpow_int.const_mul (2/ε)
    simpa [IntegrableOn, bound] using hconst
                                                                                  
  have hDiff_eventually : ∀ᶠ z in 𝓝 s,
      DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
                                              
    have hball : Metric.ball s (δ/2) ∈ 𝓝 s := Metric.ball_mem_nhds _ (by simpa using (half_pos hδpos))
    refine Filter.eventually_of_mem hball ?_
    intro z hz
                                                                                            
    have hz_lt_δ : dist z s < δ := lt_trans (by simpa [Metric.mem_ball] using hz) (by simpa using (half_lt_self hδpos))
    have hRe_inner : ∀ y, y ∈ Metric.ball z (δ/2) → ε ≤ y.re := by
      intro y hy
      have hy_lt_δ : dist y z < δ := lt_trans (by simpa [Metric.mem_ball] using hy) (by simpa using (half_lt_self hδpos))
      exact hδprop z hz_lt_δ y hy_lt_δ
                                              
    have hmeas_z : ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      eventually_aestronglyMeasurable_kernel_param (s := z)
                                                                     
    have hzRe_ge : ε ≤ z.re := by
                                                      
      have hss : dist s s < δ := by simpa [dist_self] using hδpos
      have hz_lt_δ' : dist z s < δ := hz_lt_δ
      exact hδprop s hss z hz_lt_δ'
    have hzpos : 0 < z.re := lt_of_lt_of_le hεpos hzRe_ge
    have hFint_z : Integrable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F] using integrable_kernel_at_param (s := z) hzpos
                                      
    have hF'meas_z : AEStronglyMeasurable (F' z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F, F'] using aestronglyMeasurable_kernel_param_deriv (z := z)
                                                       
    have hbound_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
                                                                                           
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
        intro u hu w hw
        have hu1 : 1 < u := hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu1
                                                             
        have hwRe : ε ≤ w.re := hRe_inner w hw
        have hker : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))‖
              ≤ Real.log u * u ^ (-1 - ε) :=
          kernel_deriv_norm_bound_on_ball (ε := ε) (u := u) (hu := hu1) (x := w) (hx := hwRe)
        have hF'le : ‖F' w u‖ ≤ Real.log u * u ^ (-1 - ε) := by
          simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hker
                                                    
        have hx' := Real.add_one_le_exp ((ε/2) * Real.log u)
        have hx : 1 + (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          simpa [add_comm] using hx'
        have hsub : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) - 1 := by
          have := sub_le_sub_right hx 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hle_exp : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          have hnonneg : 0 ≤ (1 : ℝ) := by norm_num
          have : Real.exp ((ε/2) * Real.log u) - 1 ≤ Real.exp ((ε/2) * Real.log u) :=
            sub_le_self _ hnonneg
          exact le_trans hsub this
        have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
        have hpos_inv : 0 < ε⁻¹ := inv_pos.mpr hεpos
        have hpos_coeff : 0 < (2/ε) := by
          have : 0 < (2 : ℝ) := by norm_num
          simpa [one_div, div_eq_mul_inv] using (mul_pos this hpos_inv)
        have hlog_bound : Real.log u ≤ (2/ε) * Real.exp ((ε/2) * Real.log u) := by
          have hmul := mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
                                            
          have hleft : (2/ε) * ((ε/2) * Real.log u) = Real.log u := by
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            calc
              (2/ε) * ((ε/2) * Real.log u)
                  = ((2/ε) * (ε/2)) * Real.log u := by ring
              _ = ((2 * ε⁻¹) * (ε * (2)⁻¹)) * Real.log u := by simp [div_eq_mul_inv]
              _ = ((2 * (2)⁻¹) * (ε⁻¹ * ε)) * Real.log u := by ring
              _ = (1 * 1) * Real.log u := by simp [hεne, h2ne]
              _ = Real.log u := by simp
          simpa [hleft]
            using hmul
                                                
        have hexp_rpow : Real.exp ((ε/2) * Real.log u) = u ^ (ε/2) := by
          have : 0 < u := hu0
          simp [Real.rpow_def_of_pos this, mul_comm]
                                                 
        have hmul : Real.log u * u ^ (-1 - ε)
              ≤ ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) := by
          have hqpos : 0 < u ^ (-1 - ε) := Real.rpow_pos_of_pos hu0 _
          have hq : 0 ≤ u ^ (-1 - ε) := le_of_lt hqpos
          exact mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound) hq
                                                                    
        have hpow_mul : u ^ (ε/2) * u ^ (-1 - ε) = u ^ (-1 - (ε/2)) := by
          have hu0' : 0 < u := hu0
          have h1 : Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u)
              = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
            simpa using (Real.exp_add ((ε/2) * Real.log u) ((-1 - ε) * Real.log u)).symm
          calc
            u ^ (ε/2) * u ^ (-1 - ε)
                = Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u) := by
                    simp [Real.rpow_def_of_pos hu0', mul_comm]
            _ = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
                    simpa using h1
            _ = Real.exp (((ε/2) + (-1 - ε)) * Real.log u) := by
                    ring_nf
            _ = u ^ (-1 - (ε/2)) := by
                    have : (ε/2) + (-1 - ε) = -1 - (ε/2) := by ring
                    simp [this, Real.rpow_def_of_pos hu0', mul_comm]
        have hmul' : ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) = (2/ε) * u ^ (-1 - (ε/2)) := by
          simp [mul_assoc, hpow_mul]
                      
        have : ‖F' w u‖ ≤ bound u := by
          refine le_trans hF'le ?_
          simpa [bound, hmul'] using hmul
        simpa [F, F', bound]
          using this
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                           
    have hderiv_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
                                                  
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2),
          HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
        intro u hu w hw
        simpa [F, F', mul_comm, mul_left_comm, mul_assoc]
          using hasDerivAt_kernel_in_param (u := u) (hu := hu) (z := w)
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2),
            HasDerivAt (fun w0 => F w0 u) (F' w u) w) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                         
    have hD := hasDerivAt_integral_param_dominated_Ioi
      (F := F) (F' := F') (s := z) (δ := δ/2) (hδ := by simpa using (half_pos hδpos))
      (hmeas := hmeas_z) (hFint := hFint_z) (hF'meas := hF'meas_z)
      (bound := bound) (hbound_int := hbound_int) (hbound := hbound_z) (hderiv := hderiv_z)
                                      
    simpa using hD.differentiableAt
                                                               
  exact analyticAt_of_eventually_differentiableAt hDiff_eventually

lemma lem_zetaFormulaAC :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     let F := fun z : ℂ =>
       z / (z - 1)
       - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)
     AnalyticOn ℂ F T) := by
                                    
  simp only [AnalyticOn]
  intro s hs
  simp at hs
  obtain ⟨hs_ne_1, hs_re⟩ := hs

  apply AnalyticAt.analyticWithinAt

  have h1 : AnalyticAt ℂ (fun z => z / (z - 1)) s := by
    apply AnalyticAt.div
    · exact analyticAt_id
    · exact analyticAt_id.sub analyticAt_const
    ·                             
      rw [sub_ne_zero]
      exact hs_ne_1

  have hs_re_eq : (10 : ℝ)⁻¹ = (1 : ℝ) / 10 := by norm_num
  have hs_re_correct : (1 : ℝ) / 10 < s.re := by rwa [← hs_re_eq]

  have hconv := lem_integralConvergence (1/10) (by norm_num) s (le_of_lt hs_re_correct)

  obtain ⟨I, hI_tendsto, hI_bound⟩ := hconv

  have hI_bound_10 : ‖I‖ ≤ 10 := by
    convert (preTransparency := .instances) hI_bound
    norm_num

  have h_integral : AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    apply lem_integralAnalytic s hs_re_correct

  have h2 : AnalyticAt ℂ (fun z => z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    exact analyticAt_id.mul h_integral

  exact h1.sub h2

lemma lem_div_eq_one_plus_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + 1 / (z - 1) := by
  have h : z - 1 ≠ 0 := by
    intro h0
    have : z = 1 := by
      rw [sub_eq_zero] at h0
      exact h0
    exact hz this
  calc z / (z - 1)
    = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + 1 / (z - 1) := by simp [div_self h]

lemma lem_integralBoundValue (s : ℂ) (hs : 0 < s.re) : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := by exact zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp

lemma lem_sOverSminus1Bound (s : ℂ) (_hs : s ≠ 1) : ‖(1 / (s - 1))‖ = 1 / ‖s - 1‖ := by simp [one_div]

lemma helper_normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq, pow_two] using (Complex.normSq_eq_norm_sq z).symm

lemma helper_three_abs_sq (t : ℝ) : (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  have hnonneg : 0 ≤ (6 : ℝ) * |t| := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact mul_nonneg h6 (abs_nonneg t)
  have hmul : |t| * |t| = t * t := by
    simp
  calc
    (3 : ℝ) ^ 2 + t ^ 2 = (3 : ℝ) ^ 2 + t * t := by simp [pow_two]
    _ = (3 : ℝ) ^ 2 + |t| * |t| := by simp [hmul]
    _ ≤ (3 : ℝ) ^ 2 + |t| * |t| + (6 : ℝ) * |t| := by exact le_add_of_nonneg_right hnonneg
    _ = (3 + |t|) ^ 2 := by ring

lemma lem_sBound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) : ‖s‖ < (3 : ℝ) + |s.im| := by
  have hnegthree_lt_re : (- (3 : ℝ)) < s.re := by
    have hlt : (- (3 : ℝ)) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hlt hs.1
  have hlt3 : s.re < (3 : ℝ) := hs.2
  have h_re_sq_lt : s.re ^ 2 < (3 : ℝ) ^ 2 := by
    simpa using (sq_lt_sq' hnegthree_lt_re hlt3)
  have hsumlt : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := by
    exact add_lt_add_left h_re_sq_lt _
  have hsq : ‖s‖ ^ 2 < (3 + |s.im|) ^ 2 := by
    have h := lt_of_lt_of_le hsumlt (helper_three_abs_sq s.im)
    simpa [helper_normsq s] using h
  have hnormnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hpos : 0 ≤ (3 : ℝ) + |s.im| := add_nonneg (by norm_num) (abs_nonneg _)
  exact (sq_lt_sq₀ hnormnn hpos).1 hsq

lemma lem_invReSbound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have h_pos : (0 : ℝ) < s.re := by
    linarith [hs.1]
  have h_half_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have h_recip : 1 / s.re ≤ 1 / (1/2 : ℝ) := one_div_le_one_div_of_le h_half_pos hs.1
  have h_simplify : 1 / (1/2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h_simplify] at h_recip
  exact h_recip

lemma lem_invSminus1bound (s : ℂ) (_hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : (1 : ℝ) ≤ ‖s - 1‖ := by
  have h2 : |s.im| ≤ ‖s - 1‖ := by
    have : (s - (1 : ℂ)).im = s.im := by
      simp [Complex.sub_im, Complex.one_im]
    simpa [this] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im h2

lemma reciprocal_le_one_of_one_le {x : ℝ} (hx_pos : 0 < x) (hx_ge : 1 ≤ x) : 1 / x ≤ 1 := by
                                                            
  have h_div_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
                                     
  have h1 : (1 / x) * 1 ≤ (1 / x) * x := by
    exact mul_le_mul_of_nonneg_left hx_ge (le_of_lt h_div_pos)
                                                
  rw [mul_one] at h1
  rw [one_div_mul_cancel (ne_of_gt hx_pos)] at h1
  exact h1

lemma div_le_mul_of_one_div_le {a c d : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (h : 1 / c ≤ d) : a / c ≤ a * d := by
                                 
  rw [div_eq_mul_one_div]
                                                                  
  exact mul_le_mul_of_nonneg_left h ha

lemma lem_finalAlgebra (t : ℝ) : 1 + 1 + ((3 : ℝ) + |t|) * 2 = (8 : ℝ) + 2 * |t| := by ring

lemma lem_abs_im_bound (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) : |s.im + t| ≤ 1 + |t| := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ 1 := le_trans h1 hs
  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
  linarith

open Metric _root_.Set _root_.Filter Asymptotics BigOperators

lemma zetadiffAtnot1 : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s :=
  fun _ => differentiableAt_riemannZeta

lemma sigmageq1 (s : ℂ) (hs : s.re > 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

lemma frac_cancel_const {x y c : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) : (x / c) / (y / c) = x / y := by
  field_simp [hc, hy]

lemma analyticOrderAt_mul_const_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => f z * a) z0 = analyticOrderAt f z0 := by
  classical
                                                             
  have hcomm : (fun z => f z * a) = (fun z => a * f z) := by
    funext z; simp [mul_comm]
  have hrew : analyticOrderAt (fun z => f z * a) z0 =
      analyticOrderAt (fun z => a * f z) z0 := by
    simp [hcomm]
  by_cases hf : AnalyticAt ℂ f z0
  ·                                                                        
    have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
    have hadd : analyticOrderAt (fun z => a * f z) z0
        = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := by
      simpa using! (analyticOrderAt_mul hconst hf)
                                          
    have hconst_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      have hiff := (AnalyticAt.analyticOrderAt_eq_zero hconst)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
      exact hiff.mpr hval
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := hadd
      _ = 0 + analyticOrderAt f z0 := by simp [hconst_zero]
      _ = analyticOrderAt f z0 := by simp
  ·                                                               
    have hnot : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro hmul
      have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
        simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
                                                                
      have hiff := (analyticAt_iff_analytic_fun_smul (h₁f := hconst) (h₂f := hval)
                        (g := f) (z := z0))
      have hsmul : AnalyticAt ℂ (fun z => (fun _ : ℂ => a) z • f z) z0 := by
                                       
        simpa [smul_eq_mul] using hmul
      have : AnalyticAt ℂ f z0 := hiff.mpr hsmul
      exact hf this
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = 0 := by simp [analyticOrderAt, hnot]
      _ = analyticOrderAt f z0 := by simp [analyticOrderAt, hf]

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT4_ZeroFreeRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma complex_abs_real_cast (r : ℝ) : ‖(r : ℂ)‖ = abs r := Complex.norm_real r

lemma log_abs_le_log_abs_add_two {t : ℝ} (ht : 2 < |t|) :
  Real.log (abs t) ≤ Real.log (abs t + 2) := by
  have hpos : 0 < |t| := lt_trans (by norm_num) ht
  have hle : |t| ≤ |t| + 2 := by nlinarith
  simpa using Real.log_le_log hpos hle

lemma norm_sub_comm' (x y : ℂ) : ‖x - y‖ = ‖y - x‖ := by
  calc
    ‖x - y‖ = ‖-(x - y)‖ := by simpa using (norm_neg (x - y)).symm
    _ = ‖y - x‖ := by simp [neg_sub]

lemma s_in_closedBall_12 (δ t : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
  ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.closedBall ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
                                         
  have hdiff :
      ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)
        = ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) := by
    simp
  have hreal :
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) = ((δ - (1 / 2 : ℝ)) : ℂ) := by
    have h' : ((1 + δ : ℝ) - (3 / 2 : ℝ)) = δ - (1 / 2 : ℝ) := by
      calc
        (1 + δ) - (3 / 2 : ℝ) = δ + 1 - (3 / 2 : ℝ) := by ac_rfl
        _ = δ + (1 - (3 / 2 : ℝ)) := by simp [add_sub_assoc]
        _ = δ + (- (1 / 2 : ℝ)) := by norm_num
        _ = δ - (1 / 2 : ℝ) := by simp [sub_eq_add_neg]
    calc
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)
          = ((1 + δ : ℝ) : ℂ) - (3 / 2 : ℂ) := by
              simp [add_comm]
      _ = (↑((1 + δ : ℝ) - (3 / 2 : ℝ)) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = ((δ - (1 / 2 : ℝ)) : ℂ) := by simp [h']
  have hnormle :
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (1 / 2 : ℝ) := by
    calc
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
          = ‖((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)‖ := by simp [hdiff]
      _ = ‖((δ - (1 / 2 : ℝ)) : ℂ)‖ := by simp [hreal]
      _ = |δ - (1 / 2 : ℝ)| := by simpa using complex_abs_real_cast (δ - (1 / 2 : ℝ))
      _ ≤ 1 / 2 := by
        have hleft : - (1 / 2 : ℝ) ≤ δ - 1 / 2 := by linarith [hδ_pos]
        have hright : δ - 1 / 2 ≤ 1 / 2 := by linarith [hδ_lt]
        simpa using (abs_le.mpr ⟨hleft, hright⟩)
                                           
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnormle

lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
                                             
  have hc_le : c ≤ L * c := by
    have h := mul_le_mul_of_nonneg_right hL hc
    simpa [one_mul] using h
                                        
  have h0 : A * L + c ≤ A * L + L * c := by
    exact add_le_add_right hc_le (A * L)
  calc
    A * L + c ≤ A * L + L * c := h0
    _ = A * L + c * L := by simp [mul_comm]
    _ = (A + c) * L := by simp [right_distrib]

lemma lem_realnx (n : ℕ) (x : ℝ) (_hn : n ≥ 1) (_hx : x ≥ 1) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  apply mul_nonneg
  ·                                             
    exact ArithmeticFunction.vonMangoldt_nonneg
  ·                           
    apply Real.rpow_nonneg
                       
    exact Nat.cast_nonneg n

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) (hdelta : delta > 0) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  ·                                                                        
    apply lem_realnx n (1 + delta) hn
                         
    linarith [hdelta]
  ·                                                                                          
    exact lem_postriglogn n hn t

lemma lem_seriespos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  ·                                                            
    simp [h]
  ·                                             
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn hdelta

lemma log_abs_add_two_pos (t : ℝ) : 0 < Real.log (abs t + 2) := by
                                                    
  have h0 : 0 ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    linarith
  have hge : (2 : ℝ) ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    have := add_le_add_left h' (2 : ℝ)
    simp
  have hgt : 1 < abs t + 2 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hge
                                                                
  exact (Real.log_pos_iff h0).2 hgt

lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have hCL : 0 < C * L := mul_pos hC hL
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hpos : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos h2 hCL
    simpa [mul_assoc] using this
  exact one_div_pos.mpr hpos

lemma log_abs_two_pos (t : ℝ) : 0 < Real.log (|t| + 2) := by
  simpa using log_abs_add_two_pos t

lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := log_abs_two_pos t
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  calc
    3 / δ + C * L
        = 3 * (1 / δ) + C * L := by simp [div_eq_mul_inv]
    _   = 3 * (2 * C * L) + C * L := by simp [h]
    _   = 6 * C * L + C * L := by ring
    _   = 7 * C * L := by ring

lemma div_le_to_le_mul (x y z : ℝ) (hy : 0 < y) (h : x / y ≤ z) : x ≤ z * y := by
  rwa [div_le_iff₀ hy] at h

lemma le_mul_to_le_div (x y z : ℝ) (hy : 0 < y) (h : x ≤ z * y) : x / y ≤ z := by
  rw [div_le_iff₀ hy]
  exact h

lemma reciprocal_div_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 4 / a ≤ b) : a ≥ 4 / b := by
                                                                
  have h1 : 4 ≤ b * a := div_le_to_le_mul 4 a b ha h
                                       
  have h2 : 4 ≤ a * b := by
    rwa [mul_comm] at h1
                                                              
  have h3 : 4 / b ≤ a := le_mul_to_le_div 4 b a hb h2
                                                                           
  exact h3

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
                                             
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
                                                     
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT5_Strong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

@[inline] noncomputable def sigma1Of (A T : ℝ) : ℝ := 1 - A / Real.log T

open _root_.Filter Topology

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Fourier
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

local instance instCoeForallRealForallComplex_solutions_r8e390f_2 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Sieve_AlignedPrimeCongruence
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]

noncomputable def survivors (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) : Finset α := by
  classical
  exact C.filter fun x => ∀ p ∈ P, ¬ bad p x

omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]

def residueBad (a : ℕ → ℕ) (p n : ℕ) : Prop := n % p = a p % p

instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))

end NumberTheoryLean.SievePartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Primes_LargePrimeDeletion
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped BigOperators

def cutoffPrimes (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

@[simp] theorem mem_cutoffPrimes {p z : ℕ} :
    p ∈ cutoffPrimes z ↔ p.Prime ∧ p ≤ z := by
  simp only [cutoffPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

noncomputable def deletionCell (C : Finset ℕ) (a : ℤ) (q : ℕ) : Finset ℕ := by
  classical
  exact C.filter fun i => (q : ℤ) ∣ a + i

@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]

def divisibilityResidue (a : ℤ) (q : ℕ) : ℕ := ((-a) % q).toNat

noncomputable def cutoffSurvivors (Y z : ℕ) (residue : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.range Y) (cutoffPrimes z)
    (SievePartition.residueBad residue)

@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto

noncomputable def coprimeOffsets (Y n : ℕ) (a : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range Y).filter fun i => (a + i).natAbs.Coprime n

@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]

end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Sieve_IntervalBoundingSieve
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped BigOperators

noncomputable def reciprocalDensity : ArithmeticFunction ℝ where
  toFun := fun d => (d : ℝ)⁻¹
  map_zero' := by simp

@[simp] theorem reciprocalDensity_apply (d : ℕ) :
    reciprocalDensity d = (d : ℝ)⁻¹ := rfl

theorem reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [reciprocalDensity_apply, Nat.cast_mul, mul_inv_rev, mul_comm]

noncomputable def intervalSieve (A J P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.range J).image fun i => A + i
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := J
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

noncomputable def residueAvoidingOffsets (J P : ℕ) (residue : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range J).filter fun i => ∀ p ∈ P.primeFactors,
    i % p ≠ residue p % p

theorem squarefree_primeSet_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpprime : p.Prime := hs p (Finset.mem_insert_self p s)
      have hsprime : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp]
      apply Nat.squarefree_mul_iff.mpr
      refine ⟨?_, hpprime.squarefree, ih hsprime⟩
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpprime (hsprime q hq)).mpr (by
        intro heq
        exact hp (heq ▸ hq))

def cutoffProduct (z : ℕ) : ℕ := ∏ p ∈ LargePrimeDeletion.cutoffPrimes z, p

theorem cutoffProduct_squarefree (z : ℕ) : Squarefree (cutoffProduct z) := by
  apply squarefree_primeSet_product
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1

@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1

end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Estimates_BonferroniBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniBlocks

open scoped BigOperators

noncomputable def alternatingChoose (m n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * n.choose r

noncomputable def hitSet (P : Finset ℕ) (hit : ℕ → Prop) : Finset ℕ := by
  classical
  exact P.filter hit

noncomputable def intersectionValue (T : Finset ℕ) (hit : ℕ → Prop) : ℝ := by
  classical
  exact if ∀ p ∈ T, hit p then 1 else 0

noncomputable def coefficientPolynomial (m : ℕ) (P : Finset ℕ) (hit : ℕ → Prop) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r *
    ∑ T ∈ P.powersetCard r, intersectionValue T hit

noncomputable def survives (P : Finset ℕ) (hit : ℕ → Prop) : ℝ := by
  classical
  exact if ∀ p ∈ P, ¬ hit p then 1 else 0

noncomputable def blockUpper (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  ∏ j ∈ B, coefficientPolynomial (2 * orders j) (blocks j) hit

noncomputable def blockCorrection (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  ∑ j ∈ B,
    (coefficientPolynomial (2 * orders j) (blocks j) hit -
      coefficientPolynomial (2 * orders j + 1) (blocks j) hit) *
      ∏ i ∈ B.erase j, coefficientPolynomial (2 * orders i) (blocks i) hit

noncomputable def blockLower (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (hit : ℕ → Prop) : ℝ :=
  blockUpper B blocks orders hit - blockCorrection B blocks orders hit

noncomputable def intersectionMass {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (T : Finset ℕ) : ℝ :=
  ∑ x ∈ C, weight x * intersectionValue T (fun p => hit p x)

noncomputable def momentPolynomial (m : ℕ) (P : Finset ℕ) (M : Finset ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * ∑ T ∈ P.powersetCard r, M T

noncomputable def intersectionRemainder {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  intersectionMass C weight hit T - X * ∏ p ∈ T, g p

end NumberTheoryLean.BonferroniBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Analysis_BonferroniDensity
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped BigOperators

noncomputable def elementarySum (P : Finset ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ P.powersetCard k, ∏ p ∈ T, g p

@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]

noncomputable def densityPolynomial (m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), (-1 : ℝ) ^ r * elementarySum P g r

@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]

end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Estimates_DisjointBlockExpansion
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped BigOperators

noncomputable def blockChoices (B : Finset ℕ) (blocks : ℕ → Finset ℕ) :
    Finset (∀ j ∈ B, Finset ℕ) := by
  classical
  exact B.pi fun j => (blocks j).powerset

@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]

noncomputable def selectedUnion (B : Finset ℕ) (choice : ∀ j ∈ B, Finset ℕ) : Finset ℕ := by
  classical
  exact B.attach.biUnion fun j => choice j.1 j.2

def intersectionChoices (B : Finset ℕ) (blocks : ℕ → Finset ℕ) (T : Finset ℕ) :
    ∀ j ∈ B, Finset ℕ := fun j _ => T ∩ blocks j

def truncatedCoefficient (m : ℕ) (T : Finset ℕ) : ℝ :=
  if T.card ≤ m then (-1 : ℝ) ^ T.card else 0

def layerCoefficient (m : ℕ) (T : Finset ℕ) : ℝ :=
  if T.card = m then 1 else 0

noncomputable def globalCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (localCoeff : ℕ → Finset ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ j ∈ B, localCoeff j (T ∩ blocks j)

noncomputable def upperCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : ℝ :=
  globalCoefficient B blocks (fun j => truncatedCoefficient (2 * orders j)) T

noncomputable def correctionCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (j : ℕ) (T : Finset ℕ) : ℝ :=
  globalCoefficient B blocks
    (fun i => if i = j then layerCoefficient (2 * orders i + 1)
      else truncatedCoefficient (2 * orders i)) T

noncomputable def lowerCoefficient (B : Finset ℕ) (blocks : ℕ → Finset ℕ)
    (orders : ℕ → ℕ) (T : Finset ℕ) : ℝ :=
  upperCoefficient B blocks orders T - ∑ j ∈ B, correctionCoefficient B blocks orders j T

@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all

end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Estimates_SquarefreeHarmonic
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable def lowerMobius (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ m.divisorsAntidiagonal, (μ t.1 : ℝ) * F t.2

noncomputable def inverseMultiples (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  lowerMobius (fun t => y (P / t)) (P / d)

noncomputable def normalization (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, if l ≤ R then s.selbergTerms l else 0

noncomputable def diagonalTarget (s : BoundingSieve) (R l : ℕ) : ℝ :=
  if l ≤ R then (μ l : ℝ) * s.selbergTerms l / normalization s R else 0

noncomputable def optimizedWeight (s : BoundingSieve) (R d : ℕ) : ℝ :=
  inverseMultiples s.prodPrimes (diagonalTarget s R) d / s.nu d

noncomputable def cutoffNormalization (z R : ℕ) : ℝ :=
  normalization (IntervalBoundingSieve.intervalSieve 0 0
    (IntervalBoundingSieve.cutoffProduct z) (IntervalBoundingSieve.cutoffProduct_squarefree z)) R

end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped BigOperators

noncomputable def squarefreeUpTo (R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 R).filter Squarefree

@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def squarefreeHarmonic (R : ℕ) : ℝ :=
  ∑ d ∈ squarefreeUpTo R, (d : ℝ)⁻¹

end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Primes_PrimeDensityBlocks
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped BigOperators

def dyadicPrimes (n : ℕ) : Finset ℕ := (Finset.Ico n (2 * n)).filter Nat.Prime

@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto

def geometricPrimes (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ (2 ^ j)) (2 ^ (2 ^ (j + 1)))).filter Nat.Prime

@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto

def lastBlock (V : ℕ) : ℕ := Nat.log 2 (Nat.log 2 V)

def blockIndices (V : ℕ) : Finset ℕ := Finset.range (lastBlock V + 1)

def primeBlock (P : Finset ℕ) (j : ℕ) : Finset ℕ := P ∩ geometricPrimes j

def reverseOrder (m J j : ℕ) : ℕ := m + (J - j)

def supportCost (m J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (J + 1), 2 ^ (j + 1) * (2 * reverseOrder m J j + 1)

noncomputable def actualLowerCoefficient (V m : ℕ) (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.lowerCoefficient (blockIndices V) (primeBlock P)
    (reverseOrder m (lastBlock V)) T

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Estimates_FundamentalBlockEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FundamentalBlockEstimate

open scoped BigOperators

noncomputable def baseError (m : ℕ) : ℝ := Real.exp (5 * 1532) / (2 : ℝ) ^ (2 * m + 1)

noncomputable def blockEuler (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - g p)

noncomputable def blockUpperDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  BonferroniDensity.densityPolynomial (2 * PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j)
    (PrimeDensityBlocks.primeBlock P j) g

noncomputable def blockOverflowDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  BonferroniDensity.elementarySum (PrimeDensityBlocks.primeBlock P j) g
    (2 * PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V) j + 1)

noncomputable def actualUpperDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    DisjointBlockExpansion.upperCoefficient (PrimeDensityBlocks.blockIndices V) (PrimeDensityBlocks.primeBlock P)
      (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V)) T * ∏ p ∈ T, g p

noncomputable def actualLowerDensity (V m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset, PrimeDensityBlocks.actualLowerCoefficient V m P T * ∏ p ∈ T, g p

noncomputable def actualUpperCoefficient (V m : ℕ) (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.upperCoefficient (PrimeDensityBlocks.blockIndices V) (PrimeDensityBlocks.primeBlock P)
    (PrimeDensityBlocks.reverseOrder m (PrimeDensityBlocks.lastBlock V)) T

def levelSubsets (P : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun T => (∏ p ∈ T, p) ≤ L

def levelDivisors (P : Finset ℕ) (L : ℕ) : Finset ℕ :=
  (∏ p ∈ P, p).divisors.filter fun d => d ≤ L

noncomputable def integerRemainder {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hit : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  BonferroniBlocks.intersectionRemainder C weight hit X g d.primeFactors

end NumberTheoryLean.FundamentalBlockEstimate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Primes_HighPrimeRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter Asymptotics
open scoped Topology

noncomputable def errorScale (c x : ℝ) : ℝ :=
  x * Real.exp (-c * Real.sqrt (Real.log x))

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeAbel

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped Topology

noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
noncomputable def reciprocalPrimes (a b : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n : ℝ)⁻¹
noncomputable def invLogWeight (t : ℝ) : ℝ := 1 / (t * Real.log t)
noncomputable def errorKernel (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

end ErdosPrimeInputs.PrimeAbel



namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel

noncomputable def decay (c t : ℝ) : ℝ := Real.exp (-c * Real.sqrt (Real.log t))
noncomputable def tailKernel (c t : ℝ) : ℝ := decay c t / (t * Real.sqrt (Real.log t))

end ErdosPrimeInputs.PrimeErrorDecay



namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter Asymptotics _root_.Finset
open scoped Topology
open PrimeAbel PrimeErrorDecay

noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)

end ErdosPrimeInputs.MertensStrong



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Sieve_EulerProductRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RealFundamentalSieve

open scoped BigOperators

noncomputable def levelDivisors (P : Finset ℕ) (v s : ℝ) : Finset ℕ := by
  classical
  exact (∏ p ∈ P, p).divisors.filter fun d => (d : ℝ) ≤ v ^ s

end NumberTheoryLean.RealFundamentalSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Sieve_ResidueCountDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosPrimeInputs.SubsetPrimeSieve

open Finset
open NumberTheoryLean
open IntervalBoundingSieve

noncomputable def euler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

end ErdosPrimeInputs.SubsetPrimeSieve



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Primes_PrimeProductOmissions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeProductOmissions

open _root_.Finset
open NumberTheoryLean.LargePrimeDeletion SubsetPrimeSieve MertensStrong

noncomputable def reducedPrimes (z q : ℕ) : Finset ℕ := cutoffPrimes z \ q.primeFactors

end ErdosPrimeInputs.PrimeProductOmissions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Renewal_DickmanFiniteDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

noncomputable def primitive (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, rho t

noncomputable def identityDifference (u : ℝ) : ℝ := u * rho u - (primitive u - primitive (u - 1))

end NumberTheoryLean.Dickman

end

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter
open scoped Topology
open Dickman

noncomputable def hazard (u : ℝ) : ℝ := rho (u - 1) / (u * rho u)

end NumberTheoryLean.DickmanDecay

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Basic
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

@[simp] theorem Nat.maxPrimeFac_zero : Nat.maxPrimeFac 0 = 0 := by simp [Nat.maxPrimeFac]

@[simp] theorem Nat.maxPrimeFac_one : Nat.maxPrimeFac 1 = 1 := by simp [Nat.maxPrimeFac]

namespace OAI

/-!
# Arithmetic and counting conventions for the joint Dickman law

`Nat.maxPrimeFac` has exactly the paper's convention `P⁺(1) = 1`.
The counting endpoint below is an integer; the paper's real endpoint is
obtained by flooring it.
-/

namespace JointDickman

/-- The logarithmic size of the largest prime factor of `n`, measured at `base`. -/
noncomputable def normalizedPrimeFactor (base n : ℕ) : ℝ :=
  Real.log (n.maxPrimeFac : ℝ) / Real.log (base : ℝ)

/-- The fixed-scale smoothness event in the proof of the joint law. -/
def fixedScaleEvent (a b : ℝ) (N n : ℕ) : Prop :=
  (n.maxPrimeFac : ℝ) ≤ (N : ℝ) ^ a ∧
    ((n + 1).maxPrimeFac : ℝ) ≤ (N : ℝ) ^ b

/-- The moving-threshold event in the main theorem. -/
def movingEvent (a b : ℝ) (n : ℕ) : Prop :=
  (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧
    ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b

/-- Ordinary, unweighted density normalized by the counting endpoint. -/
noncomputable def empiricalDensity (P : ℕ → Prop) (N : ℕ) : ℝ :=
  (empiricalCount P N : ℝ) / N

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

/-- The independent-selection mass of a subset of `P`. All sums of these
masses below are restricted to `P.powerset`. -/
noncomputable def bernoulliSubsetMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : Finset α) : ℝ :=
  (∏ p ∈ S, q p) * ∏ p ∈ P \ S, (1 - q p)

/-- The prime-product pushforward of independent Bernoulli `z/p` selection;
this is the manuscript's `ν_z` on the finite allowed prime set. -/
noncomputable def primeProductMass (P : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if (∏ p ∈ S, p) = n then
    bernoulliSubsetMass P (fun p => z / p) S else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_BernoulliComparison
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mutually exclusive site hits versus independent Bernoulli hits

At one prime the actual site hits are mutually exclusive. Their categorical
law differs from independent Bernoulli hits by at most twice the square of
the sum of the site probabilities in `L¹`. Everything here is a finite-sum
proof; no coupling estimate is assumed.
-/

namespace JointDickman

open scoped BigOperators

/-- Empty hit set with mass `1-sum q`, singleton `{i}` with mass `q i`,
and zero on every other subset. The delta-sum form avoids any choices. -/
noncomputable def categoricalSubsetMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : Finset α) : ℝ :=
  (if S = ∅ then 1 - ∑ i ∈ P, q i else 0) +
    ∑ i ∈ P, if S = {i} then q i else 0

@[simp] theorem categoricalSubsetMass_empty {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    categoricalSubsetMass P q ∅ = 1 - ∑ i ∈ P, q i := by
  simp [categoricalSubsetMass]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

/-- Product mass on a finite family of coordinate spaces. -/
noncomputable def finiteProductMass {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (a : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) : ℝ := ∏ i, a i (x i)

/-- Mutually exclusive site hits, independent between coordinates. -/
noncomputable def categoricalProductMass {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ) (x : ι → P.powerset) : ℝ :=
  finiteProductMass (fun i S => categoricalSubsetMass P (q i) S.val) x

/-- Independent site hits, independent also between coordinates. -/
noncomputable def bernoulliProductMass {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ) (x : ι → P.powerset) : ℝ :=
  finiteProductMass (fun i S => bernoulliSubsetMass P (q i) S.val) x

/-- One Bernoulli coordinate, written as a mass on `Bool`. -/
noncomputable def bernoulliBitMass (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- The membership indicators of a subset give its finite Boolean coordinates. -/
noncomputable def subsetHitEquiv {α : Type*} [DecidableEq α] (P : Finset α) :
    P.powerset ≃ (P → Bool) where
  toFun S i := decide (i.val ∈ S.val)
  invFun f := ⟨P.filter (fun i => ∃ hi : i ∈ P, f ⟨i, hi⟩ = true),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, _, hi⟩
      exact hi
    · intro hi
      have hiP := Finset.mem_powerset.mp S.property hi
      exact ⟨hiP, hiP, hi⟩
  right_inv f := by
    funext i
    change decide (i.val ∈ P.filter (fun j => ∃ hj : j ∈ P, f ⟨j, hj⟩ = true)) = f i
    cases hf : f i <;> simp [Finset.mem_filter, i.property, hf]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smoothing channels

Nonnegative transition probabilities and a uniform output mass bound
imply the weighted square-norm estimate for finite smoothing channels.
-/

namespace JointDickman

open Finset

section Channel

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

noncomputable def finiteChannel (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (f : Ω → ℝ) (a : A) : ℝ := (∑ s, w s * p s a * f s) / μ a

noncomputable def finiteChannelAdjoint (p : Ω → A → ℝ) (g : A → ℝ) (s : Ω) : ℝ :=
  ∑ a, p s a * g a

/-- The two-split kernel, expressed without an assumed adjoint theorem. -/
noncomputable def finiteTwoSplitKernel (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (a b : A) : ℝ :=
  (∑ s, w s * p s a * p s b) / (μ a * μ b)

/-- Integral action of a kernel on a finite space with atom masses `μ`. -/
noncomputable def finiteKernelAction (μ : A → ℝ) (K : A → A → ℝ)
    (g : A → ℝ) (a : A) : ℝ := ∑ b, μ b * K a b * g b

end Channel


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSplitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two fair splits of the same prime site

The local law is constructed by first selecting a Bernoulli site and then,
conditional on that hit, taking two independent fair splits. Its common and
exclusive categories have mass `q/4` each. Finite product comparison gives
the independent common/exclusive model without assuming a coupling.
-/

namespace JointDickman

open scoped BigOperators

/-- Finite pushforward of a real mass function. -/
noncomputable def finitePushMass {A B : Type*} [Fintype A]
    (a : A → ℝ) (f : A → B) (y : B) : ℝ := by
  classical
  exact ∑ x, if f x = y then a x else 0

/-- Conditional on a site hit, the two choices are independent fair bits;
an absent site gives two absent splits. -/
noncomputable def conditionalFairSplitMass (hit : Bool) (b : Bool × Bool) : ℝ :=
  if hit then bernoulliBitMass (1 / 2) b.1 * bernoulliBitMass (1 / 2) b.2
  else if b = (false, false) then 1 else 0

/-- The three labels are common, first-exclusive, second-exclusive. -/
abbrev SplitCategories := ((Finset.univ : Finset (Fin 3)).powerset : Type)

/-- Prime product corresponding to one of the common/exclusive categories. -/
noncomputable def categoryPrimeProduct (Q : Finset ℕ) (k : Fin 3)
    (y : Q → SplitCategories) : ℕ :=
  ∏ p, if k ∈ (y p).val then p.val else 1

/-- The independent model is `(C E₁, C E₂)`. If two categories contain the
same prime, its square is retained in the corresponding product. -/
noncomputable def independentSplitProducts (Q : Finset ℕ) (y : Q → SplitCategories) : ℕ × ℕ :=
  (categoryPrimeProduct Q 0 y * categoryPrimeProduct Q 1 y,
    categoryPrimeProduct Q 0 y * categoryPrimeProduct Q 2 y)

/-- Prime products of the actual pair of splits. -/
noncomputable def actualSplitProducts (Q : Finset ℕ) (x : Q → Bool × Bool) : ℕ × ℕ :=
  (∏ p, if (x p).1 then p.val else 1, ∏ p, if (x p).2 then p.val else 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

/-- One conditional retention bit. -/
noncomputable def fairRetentionBitMass (hit retained : Bool) : ℝ :=
  if hit then bernoulliBitMass (1 / 2) retained else if retained then 0 else 1

/-- Independent Bernoulli mass of the original site. -/
noncomputable def bernoulliSiteMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (x : ι → Bool) : ℝ := finiteProductMass (fun i => bernoulliBitMass (q i)) x

/-- Conditional probability of a particular retained subset of a site. -/
noncomputable def fairRetentionMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : ℝ := finiteProductMass (fun i => fairRetentionBitMass (x i)) y

/-- Conditional expectation of a test of the retained subset. -/
noncomputable def fairSplitAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (f : (ι → Bool) → ℝ) : ℝ := ∑ y, fairRetentionMass x y * f y

/-- Actual transition probability to an output cell of the retained subset. -/
noncomputable def fairSplitTransition {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (cell : (ι → Bool) → A) (x : ι → Bool) (a : A) : ℝ := by
  classical
  exact ∑ y, if cell y = a then fairRetentionMass x y else 0

/-- Prime product of one retained bit vector. -/
noncomputable def retainedPrimeProduct (Q : Finset ℕ) (y : Q → Bool) : ℕ :=
  ∏ p, if y p then p.val else 1

/-- The conditional probability `p_A(S)` that a fair split of the site
has its retained prime product in the specified cell. -/
noncomputable def fairSplitPrimeCell (Q : Finset ℕ) (A : Set ℕ) (x : Q → Bool) : ℝ := by
  classical
  exact fairSplitAverage x (fun y => if retainedPrimeProduct Q y ∈ A then 1 else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair thinning of an independently selected prime set -/

namespace JointDickman

open Finset

open Classical in
noncomputable def subsetRetentionMass {α : Type*} [DecidableEq α]
    (S T : Finset α) : ℝ := if T ⊆ S then (1 / 2 : ℝ)^S.card else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThinningRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the remaining-set and second-coin law by prime range -/

namespace JointDickman

open Finset

noncomputable def jointRetentionMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S T : Finset α) : ℝ :=
  bernoulliSubsetMass P q S * subsetRetentionMass S T

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighLowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging high second coins after the low addition product -/

namespace JointDickman

open Finset

open Classical in
noncomputable def highNoAdditionMass {α : Type*} [DecidableEq α]
    (Q : Finset α) (q : α → ℝ) (k : ℝ) : ℝ :=
  ∑ R ∈ Q.powerset, if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeRangeOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The high-prime restrictions as finite averaging operators -/

namespace JointDickman

open Finset

open Classical in
noncomputable def keptHighAverage (P Q : Finset ℕ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) (fun _ => (1 / 2 : ℝ)) S *
    (if S ∩ Q = Q then F (S ∩ P) else 0)

open Classical in
noncomputable def noHighAdditionAverage (P Q : Finset ℕ) (q : ℕ → ℝ)
    (k : ℝ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
    jointRetentionMass (P ∪ Q) q S T *
      (if k ≤ ((S ∩ Q).card : ℝ) ∧ T ∩ Q = ∅ then F (T ∩ P) else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

/-- The squarefree coefficient `μ(n)^2 z^ω(n)`. On squarefree integers,
the number of prime factors with multiplicity equals the number of distinct
prime factors. -/
noncomputable def squarefreeWeight (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then z ^ cardFactors n else 0, by simp⟩

@[simp] theorem squarefreeWeight_one (z : ℝ) : squarefreeWeight z 1 = 1 := by
  simp [squarefreeWeight]

/-- The finite Euler-factor inverse supported on integers whose prime
factors all belong to the excluded set. -/
noncomputable def smoothCorrection (E : Finset ℕ) (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    if n.primeFactors ⊆ E then (-z) ^ cardFactors n else 0, by simp⟩

@[simp] theorem smoothCorrection_one (E : Finset ℕ) (z : ℝ) :
    smoothCorrection E z 1 = 1 := by simp [smoothCorrection]

/-- Restriction to integers with no prime factor from `E`. -/
noncomputable def roughSquarefreeWeight (E : Finset ℕ) (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Disjoint n.primeFactors E then squarefreeWeight z n else 0, by simp⟩

@[simp] theorem roughSquarefreeWeight_one (E : Finset ℕ) (z : ℝ) :
    roughSquarefreeWeight E z 1 = 1 := by simp [roughSquarefreeWeight]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published arithmetic inputs at the strength needed here

The fixed-order Selberg–Delange expansion is Granville–Koukoulopoulos,
*Beyond the LSD method* (2019), Theorem 1, specialized to
`μ²(n) z^ω(n)`, or Koukoulopoulos, *The Distribution of Prime Numbers*,
Theorem 13.2. The expansion concerns squarefree weights and contains no
character estimates.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def squarefreeSummatory (z Y : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, squarefreeWeight z n

/-- The convergent Euler-product normalization of the first LSD coefficient. -/
noncomputable def squarefreeLeadingConstant (z : ℝ) : ℝ :=
  (∏' p : {p : ℕ // p.Prime},
    (1 + z / (p.val : ℝ)) * (1 - 1 / (p.val : ℝ)) ^ z) / Real.Gamma z

namespace PublishedInputs

/-- Only the two positive exponents used by the paper, with all fixed
expansion orders and the actual leading coefficient. -/
def SquarefreeSelbergDelangeInput : Prop :=
  ∀ z : ℝ, z = 1 / 4 ∨ z = 1 / 2 →
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 3 ≤ Y →
        |squarefreeSummatory z Y -
          Y * ∑ j ∈ range (H + 1), c j * (Real.log Y) ^ (z - 1 - j)| ≤
            C * Y * (Real.log Y) ^ (z - 2 - H)

/-- The classical reciprocal-prime Mertens estimate, at its usual
`O(1/log x)` strength: Montgomery–Vaughan, Multiplicative Number Theory I,
Theorem 2.7(d). -/
def PrimeReciprocalMertensInput : Prop :=
  ∃ M C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
      Real.log (Real.log x) - M| ≤ C / Real.log x

/-- Mertens' product theorem, with its normalized limiting constant:
Montgomery–Vaughan, Multiplicative Number Theory I, Theorem 2.7(e). -/
def PrimeProductMertensInput : Prop :=
  Tendsto (fun x : ℝ => Real.log x *
    ∏ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)))
    atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

noncomputable def weightBaseExponent : ℝ := (1 - Real.log 2) / 2

noncomputable def amplificationExponent : ℝ := (8 / 5) * Real.log 2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeTupleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime tuples in the marginal floor error

Fix the first `h` entries of an ordered prime tuple and count the last
entry by a Chebyshev bound. Summing its reciprocal-product weight gives
the `h`th power of the reciprocal-prime sum. Repeated primes are allowed,
so this bounds the distinct tuples used in inclusion-exclusion as well.
The Chebyshev and reciprocal-sum hypotheses are explicit arithmetic inputs.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

/-- Only the range `t ≥ y` of the usual Chebyshev upper estimate is needed. -/
def PrimeCountingUpperBound (C y : ℝ) : Prop :=
  ∀ t : ℝ, y ≤ t → (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

/-- Allowed large primes up to the real endpoint `N`. -/
noncomputable def largePrimeSet (N y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊N⌋₊).filter (fun p => y < (p : ℝ))

/-- Ordered tuples of `h` primes from `P` with product at most `N`. -/
noncomputable def primeTupleCount (P : Finset ℕ) (h : ℕ) (N : ℝ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin h => P).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)).card

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)

namespace PublishedInputs

/-- The large-argument Chebyshev upper bound; Montgomery–Vaughan,
Multiplicative Number Theory I, Corollary 2.6. -/
def ChebyshevPrimeCountingInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def primeNormalizer (P : Finset ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - z / (p : ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RpowTaylor
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform power expansion for removing roughness

Taylor expansion is made on the fixed compact interval `[0, 1/2]`.
Its coefficients are independent of the expansion order and of the
moving logarithmic scale.
-/

namespace JointDickman

open Finset Set

noncomputable def rpowShiftCoeff (a : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ)⁻¹ *
    iteratedDerivWithin k (fun t : ℝ => (1 - t) ^ a) (Icc 0 (1 / 2)) 0

@[simp] theorem rpowShiftCoeff_zero (a : ℝ) : rpowShiftCoeff a 0 = 1 := by
  simp [rpowShiftCoeff]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

def auxiliaryCutoff (B : ℕ) : ℕ := B ^ 1000

noncomputable def auxiliaryUpper (B : ℕ) : ℝ := Real.exp (4 * (B : ℝ))

noncomputable def auxiliaryRatio (B : ℕ) : ℝ :=
  (B : ℝ) / (1000 * Real.log B)

noncomputable def auxiliaryPrimes (B : ℕ) : Finset ℕ :=
  largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ConvolutionTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite truncation estimates for roughness removal

The large-divisor part of the convolution is bounded before invoking any
Selberg–Delange input. The bound needs only the elementary `|g_z| ≤ 1`.
-/

namespace JointDickman

open Finset

/-- The part indexed by divisors greater than the chosen truncation. -/
noncomputable def roughConvolutionTail (E : Finset ℕ) (z : ℝ) (N V : ℕ) : ℝ :=
  ∑ v ∈ Ioc V N, smoothCorrection E z v *
    ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CorrectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficients' actual logarithmic moments

These are absolutely convergent series of the smooth correction.
The bounds are uniform in the moving cutoff and every fixed moment order.
-/

namespace JointDickman

open Finset

noncomputable def correctionLogTerm (E : Finset ℕ) (z : ℝ) (k n : ℕ) : ℝ :=
  smoothCorrection E z n / (n : ℝ) * (Real.log n) ^ k

noncomputable def correctionLogMoment (E : Finset ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  ∑' n, correctionLogTerm E z k n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients after removal of the small prime factors

Each coefficient is a finite combination of the published fixed-order
Selberg–Delange coefficients and the actual correction moments. The
definition has no dependence on a subsequently chosen truncation order.
-/

namespace JointDickman

open Finset

noncomputable def roughCoefficient (c : ℕ → ℝ) (E : Finset ℕ) (z : ℝ) (ν : ℕ) : ℝ :=
  ∑ j ∈ range (ν + 1), c j * rpowShiftCoeff (z - 1 - j) (ν - j) *
    correctionLogMoment E z (ν - j)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def squarefreeEulerFactor (z : ℝ) (p : ℕ) : ℝ :=
  (1 + z / (p : ℝ)) * (1 - 1 / (p : ℝ)) ^ z

noncomputable def primeEulerFactor (z : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then squarefreeEulerFactor z n else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughLeadingCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The leading coefficient after the roughness cutoff

Mertens' product theorem and the convergent squarefree Euler factor give
the precise constant `exp(-γ z) / Gamma(z)`.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughLeadingCoefficient (z : ℝ) (P : ℕ) : ℝ :=
  squarefreeLeadingConstant z * ∏ p ∈ Nat.primesLE P, (1 + z / (p : ℝ))⁻¹

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ScaledRoughCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients in the limiting prime-product density

The zeroth normalized coefficient has the stated limit, and every fixed
higher coefficient vanishes. No residue-distribution assertion is assumed.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def scaledRoughCoefficient (c : ℕ → ℝ) (z : ℝ) (j B : ℕ) : ℝ :=
  primeNormalizer (auxiliaryPrimes B) z *
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j * (B : ℝ) ^ (z - j)

theorem auxiliaryPrimes_prime (B : ℕ) : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
  intro p hp
  exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence of the prime-product density

Finite combinations of the actual rough coefficients converge uniformly
away from zero. This is the smooth density used for the coarse channel.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughDensityPolynomial (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ range (H + 1), roughCoefficient c E z j *
    (L ^ (z - 1 - j) + (z - 1 - j) * L ^ (z - 2 - j))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published character estimate

The input is the Siegel–Walfisz specialization of Singha Roy,
*The Landau–Selberg–Delange method for products of Dirichlet L-functions,
and applications, I*, arXiv:2511.15928v1, Theorem 1.1 and Corollary 1.2,
with Siegel's bound (Koukoulopoulos, Theorem 12.10). Take ν = 1, the
exponent z at one nonprincipal character, and zero at every other
character. The Euler correction is absolutely convergent for Re(s)>1/2;
the principal exponent is zero, so all the main coefficients vanish.
This is an explicit conditional input, not a proof of that analytic result.
-/

namespace JointDickman

open Finset

/-- Twist the squarefree coefficients, before removing any small primes. -/
noncomputable def squarefreeCharacterSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z Y : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, (squarefreeWeight z n : ℂ) * χ (n : ZMod q)

namespace PublishedInputs

/-- Only the two exponents and the arbitrary fixed logarithmic saving
needed for the moving-cutoff argument are retained. -/
def SquarefreeCharacterEstimateInput : Prop :=
  ∀ z : ℝ, z = 1 / 4 ∨ z = 1 / 2 →
    ∀ C D : ℝ, 0 < C → 0 ≤ D → ∃ K : ℝ, 0 ≤ K ∧
      ∀ Y : ℝ, 3 ≤ Y → ∀ q : ℕ, ∀ [NeZero q],
        (q : ℝ) ≤ (Real.log Y) ^ C →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖squarefreeCharacterSum χ z Y‖ ≤ K * Y * (Real.log Y) ^ (-D)

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterConvolution
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact character-twisted roughness convolution -/

namespace JointDickman

open Finset ArithmeticFunction

noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * χ (n : ZMod q), by simp⟩

@[simp] theorem characterTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    characterTwist χ f n = (f n : ℂ) * χ (n : ZMod q) := rfl

noncomputable def roughCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, (roughSquarefreeWeight E z n : ℂ) * χ (n : ZMod q)

noncomputable def characterConvolutionTail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z : ℝ) (N V : ℕ) : ℂ :=
  ∑ v ∈ Ioc V N, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
    squarefreeCharacterSum χ z ((N / v : ℕ) : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingRoughExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion with explicit errors

The classical expansion, Taylor approximation, and correction-moment
tails are now combined for the actual rough squarefree summatory function.
No moving-cutoff asymptotic is used as an input.
-/

namespace JointDickman

open Finset

noncomputable def powerExpansionError (A C a : ℝ) (H P V : ℕ) (L : ℝ) : ℝ :=
  C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
    A * (Real.log P) ^ (Real.exp 1) *
      ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
        ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
          (V : ℝ) ^ ((1 / Real.log P) / 2))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughUniformExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform remainder for removal of small primes

The four explicit errors are bounded by one algebraic remainder and one
Rankin remainder. All constants are independent of the cutoff and endpoint.
-/

namespace JointDickman

open Finset

noncomputable def powerTailConstant (a : ℝ) (H : ℕ) : ℝ :=
  ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughAuxiliaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion on the manuscript's auxiliary scale

The remainder is uniform once `log Y ≥ B^0.89`. Its decay is derived
from the explicit expansion, rather than assumed as an analytic input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughErrorEnvelope (z : ℝ) (H : ℕ) (B : ℝ) : ℝ :=
  (B ^ (89 / 100 : ℝ)) ^ (z - 2 - H) *
      (1000 * Real.log B) ^ (Real.exp 1 + (H + 1 : ℕ)) +
    (1000 * Real.log B) ^ (Real.exp 1 + H) *
      Real.exp (-(B ^ (89 / 100 : ℝ) / (8000 * Real.log B)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character orthogonality for the actual rough coefficients -/

namespace JointDickman

open Finset

noncomputable def progressionSum {q : ℕ} (S : Finset ℕ) (w : ℕ → ℝ)
    (r : ZMod q) : ℝ := ∑ n ∈ S, if (n : ZMod q) = r then w n else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueSummatory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform progression estimate for rough squarefree integers -/

namespace JointDickman

open Finset Filter
open scoped Topology

noncomputable def roughResidueSummatory {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z Y : ℝ) : ℝ :=
  progressionSum (Ioc 0 ⌊Y⌋₊) (roughSquarefreeWeight E z) r

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def coefficientScale (B : ℕ) : ℝ :=
  Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 2 : ℝ)

noncomputable def coefficientWeight (B n : ℕ) : ℝ :=
  coefficientScale B * roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n

noncomputable def coefficientModel (c : ℕ → ℝ) (H B : ℕ) (Y : ℝ) : ℝ :=
  coefficientScale B * (Y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) j *
      (Real.log Y) ^ ((1 / 2 : ℝ) - 1 - j))

noncomputable def coefficientDensity (c : ℕ → ℝ) (H B : ℕ) (s : ℝ) : ℝ :=
  coefficientScale B * roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (B * s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveSingleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form Euler product at the roughness cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

def sievePrimes (Z : ℕ) : Finset ℕ := (Nat.primesLE Z).filter (fun p => 6 ≤ p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the coefficient scale in the sieve density -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def sieveCutoff (c : ℝ) (B : ℕ) : ℕ := ⌊Real.exp (c * B)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionCutoffScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed sieve cutoff used for the addition-product small-ball bound -/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def additionSieveCutoff (Y : ℝ) : ℕ := ⌊Real.exp (Y / 100)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

noncomputable def periodicAverage {q : ℕ} (f : ZMod q → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, f (n : ZMod q)) / N

noncomputable def residueMean {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ℂ :=
  (∑ a : ZMod q, f a) / q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reducing local weights by random forbidding

The upper sieve is applied to deterministic forbidden congruences. Randomly
forbidding each form converts that bound to the product of its local weights,
without changing the remainder. The transfer below is exact on finite sets;
the deterministic upper-sieve estimate is a separate published input.
-/

namespace JointDickman

open Finset

/-- A point survives if none of its vanishing forms is selected. -/
noncomputable def avoidsSelected {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : ℝ := if Disjoint S E then 1 else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_UpperSieveInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published finite-event upper sieve

Theorem 2.4 of Kevin Ford, *Sieve Methods Lecture Notes, Spring 2023*,
page 18, https://ford126.web.illinois.edu/sieve2023.pdf, in its general
probability-space formulation (Section 1.2). The sum of absolute remainders
is only over squarefree products at most the sifting bound. No arithmetic
progression estimate or application-specific weight bound is assumed here.
-/

namespace JointDickman

open Finset

/-- Mass of the intersection of the events indexed by `D`. -/
noncomputable def sieveIntersection {X : Type*} [Fintype X]
    (E : X → Finset ℕ) (w : X → ℝ) (D : Finset ℕ) : ℝ :=
  ∑ x, if D ⊆ E x then w x else 0

/-- Ford's remainder `r_d`, with `D` the prime factors of `d`. -/
noncomputable def sieveRemainder {X : Type*} [Fintype X]
    (E : X → Finset ℕ) (w : X → ℝ) (M : ℝ) (g : ℕ → ℝ)
    (D : Finset ℕ) : ℝ := sieveIntersection E w D - M * ∏ p ∈ D, g p

/-- Ford's interval condition `(Ω)`. Primes outside `P` have local density zero. -/
def SieveDimension (P : Finset ℕ) (g : ℕ → ℝ) (κ A z : ℝ) : Prop :=
  ∀ y v : ℝ, 2 ≤ y → y ≤ v → v ≤ z →
    (∏ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v), (1 - g p)⁻¹) ≤
      (Real.log v / Real.log y) ^ κ * Real.exp (A / Real.log y)

namespace PublishedInputs

/-- Ford 2023, Theorem 2.4, specialized to a finite nonnegative population.
The constant is independent of the population, events, densities and bound.
The parameter `M` is the main-term mass `X` in the source; its difference
from the actual population mass is retained in the `D = ∅` remainder. -/
def FordUpperSieveInput : Prop :=
  ∀ κ A : ℝ, 0 < κ → 0 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [Fintype X] (P : Finset ℕ) (E : X → Finset ℕ)
      (w : X → ℝ) (M z : ℝ) (g : ℕ → ℝ),
      2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
      SieveDimension P g κ A z →
      (∑ x, w x * avoidsSelected P (E x)) ≤
        C * M * (∏ p ∈ P, (1 - g p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D|

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interval sieve with its actual arithmetic remainder -/

namespace JointDickman

open Finset

/-- Forbidden primes of an actual integer point. -/
noncomputable def rootEvents (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (n : ℕ) : Finset ℕ := P.filter (fun p => (n : ZMod p) ∈ A p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle sieve with an explicit arithmetic remainder -/

namespace JointDickman

open Finset

noncomputable def pairRootEvents (P : Finset ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (r s : ℕ) : Finset ℕ :=
  P.filter (fun p => ((r : ZMod p), (s : ZMod p)) ∈ A p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveAffineLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality of a proper affine line over a prime residue field -/

namespace JointDickman

open Finset

noncomputable def affineResidueLine {p : ℕ} [NeZero p] (a b c : ZMod p) :
    Finset (ZMod p × ZMod p) := univ.filter (fun x => a * x.1 + b * x.2 = c)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FormRectangleSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently weighted forms in a rectangle -/

namespace JointDickman

open Finset

noncomputable def formSetWeight {k : ℕ} {α : Type*} [DecidableEq α]
    (F : Fin k → Finset α) (θ : Fin k → ℝ) (x : α) : ℝ :=
  ∏ i ∈ univ.filter (fun i => x ∈ F i), θ i

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AffineRectangleSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted affine-line rectangle sieve -/

namespace JointDickman

open Finset

noncomputable def affineFormWeight {k p : ℕ} (a b c : Fin k → ZMod p)
    (θ : Fin k → ℝ) (r s : ZMod p) : ℝ :=
  ∏ i, if a i * r + b i * s = c i then θ i else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AffineLocalFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact local means for the three forms b, c, b+jc -/

namespace JointDickman

open Finset

open Classical in
noncomputable def residueWeight {α : Type*} (t : ℝ) (a x : α) : ℝ :=
  if x = a then t else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MixedThreeFormLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three-form local means with independently tilted weights -/

namespace JointDickman

open Finset

noncomputable def mixedThreeFormMean {p : ℕ} [NeZero p]
    (j : ZMod p) (t u v : ℝ) : ℝ :=
  (∑ b : ZMod p, ∑ c : ZMod p,
    residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) / (p : ℝ) ^ 2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded moments of the singular factor Σ(j) -/

namespace JointDickman

open Finset

noncomputable def singularFactor (C : ℝ) (j : ℕ) : ℝ :=
  ∏ p ∈ j.primeFactors, (1 + C / p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MixedThreeFormSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rectangle sieve for three separately tilted coefficient weights -/

namespace JointDickman

open Finset

noncomputable def mixedThreeFormLocalFactor (p j : ℕ) (t u v : ℝ) : ℝ :=
  (∑ b ∈ range p, ∑ c ∈ range p,
    residueWeight t 0 (b : ZMod p) * residueWeight u 0 (c : ZMod p) *
      residueWeight v 0 ((b : ZMod p) + j * c)) / (p : ℝ) ^ 2

noncomputable def mixedThreeFormSieveWeight (P : Finset ℕ) (t u v : ℕ → ℝ) (j b c : ℕ) : ℝ :=
  ∏ p ∈ P, residueWeight (t p) 0 (b : ZMod p) * residueWeight (u p) 0 (c : ZMod p) *
    residueWeight (v p) 0 ((b : ZMod p) + j * c)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularPrimeSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's regular prime sets and truncated weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def auxiliaryLogLength (B : ℕ) : ℝ := Real.log (auxiliaryRatio B)

noncomputable def primePrefix (B : ℕ) (g : ℝ) (S : Finset ℕ) : Finset ℕ :=
  if g < 1 then S.filter (fun p : ℕ => Real.log p ≤ (B : ℝ) ^ g) else S

noncomputable def primeTailEndpoint (B i : ℕ) : ℝ :=
  (2 : ℝ) ^ i * Real.log (auxiliaryCutoff B)

/-- The last dyadic endpoint and all later endpoints impose an automatic
condition when C is nonnegative, so the tail condition is stated for all i. -/
def RegularPrimeSet (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) : Prop :=
  (∀ i ∈ Icc 1 L, (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B ≤
      (primePrefix B ((i : ℝ) / L) S).card ∧
    ((primePrefix B ((i : ℝ) / L) S).card : ℝ) ≤
      (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B) ∧
  (∀ i : ℕ, (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
    ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ))

noncomputable def coefficientPrimeSet (B n : ℕ) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => p ∣ n)

noncomputable def residueBaseWeight (B : ℕ) (S : Finset ℕ) : ℝ :=
  auxiliaryRatio B ^ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ S.card

open Classical in
noncomputable def regularResidueWeight (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) : ℝ :=
  if RegularPrimeSet B L τ C S then residueBaseWeight B S else 0

open Classical in
noncomputable def regularCoefficientWeight (B L : ℕ) (τ C : ℝ) (n : ℕ) : ℝ :=
  if RegularPrimeSet B L τ C (coefficientPrimeSet B n) then coefficientWeight B n else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficient
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

noncomputable def primeDivisorCount (Q : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactors ∩ Q).card

@[simp] theorem coefficientWeight_zero (B : ℕ) : coefficientWeight B 0 = 0 := by
  simp [coefficientWeight, roughSquarefreeWeight, squarefreeWeight]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TiltedSieveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler-product cost of an exponential prime-count tilt -/

namespace JointDickman

open Finset

noncomputable def tiltPrimeReciprocalMass (P Z : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ p ∈ (sievePrimes Z).filter (fun p => P < p ∧ p ∈ Q), 1 / (p : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The combined normalizer and sieve density for an addition product -/

namespace JointDickman

open Finset

noncomputable def quarterOdds (p : ℕ) : ℝ := (1 / 4) / (1 - (1 / 4 : ℝ) / p)

noncomputable def additionSieveTheta (P p : ℕ) : ℝ := if p ≤ P then 0 else quarterOdds p

noncomputable def additionSieveDensity (P Z : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Z, (1 - (1 - additionSieveTheta P p) / p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sieve majorants for the actual quarter-density product law -/

namespace JointDickman

open Finset

noncomputable def additionSieveWeight (P Z n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Z, residueWeight (additionSieveTheta P p) 0 (n : ZMod p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ManuscriptAdditionProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's actual addition-prime process -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def additionPrimes (B : ℕ) (Y : ℝ) : Finset ℕ :=
  largePrimeSet (Real.exp (min Y (4 * B))) (auxiliaryCutoff B)

open Classical in
noncomputable def additionLogIntervalMass (B : ℕ) (Y v H : ℝ) : ℝ :=
  ∑ S ∈ (additionPrimes B Y).powerset,
    if v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
        Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ) then
      bernoulliSubsetMass (additionPrimes B Y) (fun p => (1 / 4 : ℝ) / p) S else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityChernoffFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chernoff factors with the actual truncated sieve prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def prefixUpperFactor (B : ℕ) (c g τ s : ℝ) : ℝ :=
  Real.exp (-s * (g / 2 + τ) * auxiliaryLogLength B + ((Real.exp s - 1) / 2) *
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B)))

noncomputable def prefixLowerFactor (B : ℕ) (c g τ s : ℝ) : ℝ :=
  Real.exp (s * (g / 2 - τ) * auxiliaryLogLength B + ((Real.exp (-s) - 1) / 2) *
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityUnionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite union bound for every failure of the regularity cutoff -/

namespace JointDickman

open Finset

open Classical in
noncomputable def prefixViolationMass (B L : ℕ) (τ : ℝ) (S : Finset ℕ) (w : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 L,
    ((if ((primePrefix B ((i : ℝ) / L) S).card : ℝ) <
        (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then w else 0) +
    (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B ((i : ℝ) / L) S).card : ℝ) then w else 0))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCountTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Markov bounds for prime counts in the actual coefficient sums -/

namespace JointDickman

open Finset

noncomputable def tripleCoefficientWeight (B j b c : ℕ) : ℝ :=
  coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)

open Filter
open scoped Topology

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientCountIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing regularity violations with the signed count events -/

namespace JointDickman

open Finset

def coefficientForm (k : Fin 3) (j b c : ℕ) : ℕ := ![b, c, b + j * c] k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientViolationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted bounds for individual prefix and tail violations -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def coefficientRectangleRemainder (B Z l₁ r₁ l₂ r₂ : ℕ) : ℝ :=
  coefficientScale B ^ 3 *
    (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrefixViolationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual prefix failures on a fixed grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def prefixGridError (B L : ℕ) (c τ s : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 L,
    (prefixLowerFactor B c ((i : ℝ) / L) τ s +
      prefixUpperFactor B c ((i : ℝ) / L) τ s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TailViolationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic summation of the actual tail failures -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def activeTailIndices (B : ℕ) : Finset ℕ :=
  (range B).filter (fun i => primeTailEndpoint B i < B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIndicatorRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform regularity loss for independent prime indicators -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def primeRegularityFailureProbability (B L : ℕ) (τ C : ℝ) (q : ℕ → ℝ) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C S then 0 else bernoulliSubsetMass (auxiliaryPrimes B) q S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConditionalPrimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual remaining-prime parameters after a coefficient is selected -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def remainingPrimeParameter (S : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ S then 0 else 1 / (2 * (p : ℝ) - 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionalAdditionProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Addition products after fixing the first coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def conditionalAdditionParameter (A : Finset ℕ) (p : ℕ) : ℝ :=
  remainingPrimeParameter A p / 2

open Classical in
noncomputable def conditionalAdditionLogIntervalMass (B : ℕ) (A : Finset ℕ) (Y v H : ℝ) : ℝ :=
  ∑ S ∈ (additionPrimes B Y).powerset,
    if v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
        Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ) then
      bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter A) S else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AdditionRatioWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Solving the second ratio condition for either addition product -/

namespace JointDickman

open Finset Filter
open scoped Topology

open Classical in
noncomputable def firstAdditionRatioMass (B : ℕ) (A D : Finset ℕ) (Y T a c : ℝ) : ℝ :=
  ∑ V ∈ (additionPrimes B Y).powerset,
    bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter D) V *
      ∑ U ∈ (additionPrimes B Y).powerset,
        if T * (c * (∏ p ∈ V, p : ℕ)) ≤ a * (∏ p ∈ U, p : ℕ) ∧
            a * (∏ p ∈ U, p : ℕ) ≤ 2 * (T * (c * (∏ p ∈ V, p : ℕ))) ∧
            Y / 2 ≤ Real.log (∏ p ∈ U, p : ℕ) then
          bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter A) U else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationHighCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact high-prime no-change probability -/

namespace JointDickman

open Finset

noncomputable def highPrimePart (Y : ℝ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun p => Y < Real.log p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationPrimeRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual low and high prime ranges used by the second split -/

namespace JointDickman

open Finset

noncomputable def upperAdditionPrimes (B : ℕ) (Y : ℝ) : Finset ℕ :=
  auxiliaryPrimes B \ additionPrimes B Y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_OrientedSplitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One oriented change interval in the actual conditional split law -/

namespace JointDickman

open Finset Filter
open scoped Topology

open Classical in
noncomputable def additionRatioTest (Y T a c : ℝ) (U V : Finset ℕ) : ℝ :=
  if T * (c * (∏ p ∈ V, p : ℕ)) ≤ a * (∏ p ∈ U, p : ℕ) ∧
      a * (∏ p ∈ U, p : ℕ) ≤ 2 * (T * (c * (∏ p ∈ V, p : ℕ))) ∧
      Y / 2 ≤ Real.log (∏ p ∈ U, p : ℕ) then 1 else 0

noncomputable def orientedSplitMass (B : ℕ) (A D : Finset ℕ) (Y C T : ℝ) : ℝ :=
  let P := additionPrimes B Y
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  keptHighAverage (A ∩ P) (A ∩ Q) (fun I =>
    keptHighAverage (D ∩ P) (D ∩ Q) (fun J =>
      noHighAdditionAverage P Q (remainingPrimeParameter D) k (fun V =>
        noHighAdditionAverage P Q (remainingPrimeParameter A) k (fun U =>
          additionRatioTest Y T (∏ p ∈ I ∪ (A ∩ Q), p : ℕ)
            (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) U V))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientRegularityLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing mass discarded by the coefficient regularity cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def regularityRemainder (B L : ℕ) : ℝ :=
  (2 * (L : ℝ) * B + (B : ℝ)^2) / (B : ℝ)^10

open Classical in
noncomputable def discardedCoefficientWeight (B L j b d : ℕ) (τ C : ℝ) : ℝ :=
  if ∀ k : Fin 3, RegularPrimeSet B L τ C (coefficientPrimeSet B (coefficientForm k j b d))
  then 0 else tripleCoefficientWeight B j b d

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProbabilityLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic probability bounds for nonregular coefficient pairs -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def coefficientPairFailureMass (B L : ℕ) (τ C : ℝ) (a c : ℕ) : ℝ :=
  if RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c) then 0
  else primeProductMass (auxiliaryPrimes B) (1 / 2) a *
    primeProductMass (auxiliaryPrimes B) (1 / 2) c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDyadicBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic boxes covering the amplification coefficients -/

namespace JointDickman

open Filter Finset
open scoped Topology

def coefficientDyadicBox (T k : ℕ) : Finset (ℕ × ℕ) :=
  (Ico (T * 2^k) (4 * T * 2^k)) ×ˢ (Ico (2^k) (2 * 2^k))

def coefficientDyadicCover (B T : ℕ) : Finset (ℕ × ℕ) :=
  (Ico B (4 * B)).biUnion (coefficientDyadicBox T)

open Classical in
noncomputable def amplificationCoefficientPairs (B T : ℕ) : Finset (ℕ × ℕ) :=
  (coefficientDyadicCover B T).filter fun ac =>
    Real.exp (B : ℝ) ≤ ac.2 ∧ (ac.2 : ℝ) ≤ Real.exp (2 * B) ∧
      T * ac.2 ≤ ac.1 ∧ ac.1 < 2 * T * ac.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalFairSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conditional law of the remaining half of a prime site -/

namespace JointDickman

open Finset

open Classical in
/-- A site is sampled at density 1/p and split by fair coins; A and R are
its selected and remaining prime sets. -/
noncomputable def fairSelectedRemainingMass (P A R : Finset ℕ) : ℝ :=
  if Disjoint A R then
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) (A ∪ R) * (1 / 2 : ℝ)^(A ∪ R).card
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitPairRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two remaining subsets in the amplification model -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def fairRemainingPairFailure (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q then 0 else
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FourSubsetFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite decomposition of the four regularity failures -/

namespace JointDickman

open Finset

open Classical in
noncomputable def fairFourSubsetFailureAt (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D) ∧
        (RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q) then 0 else
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q

open Classical in
noncomputable def fairFourSubsetFailure (B L T : ℕ) (τ C : ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
      fairFourSubsetFailureAt B L τ C A D else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HarmonicSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partial summation for the local prime-product law

Harmonic weighting of a counting estimate costs only the logarithmic
length of the interval. The finite counting function is kept explicit.
-/

namespace JointDickman

open Finset MeasureTheory
open scoped Interval

noncomputable def finiteCountingFunction (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊t⌋₊, w n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AmplificationWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive rectangle inside the coefficient size-and-ratio support -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def amplificationLowerC (B : ℕ) : Finset ℕ :=
  Ioc ⌊Real.exp (B : ℝ)⌋₊ ⌊Real.exp ((3 / 2 : ℝ) * B)⌋₊

noncomputable def amplificationLowerA (T c : ℕ) : Finset ℕ :=
  Ioc (T * c) ⌊(3 / 2 : ℝ) * T * c⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularAmplificationMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive first moment after all four regularity cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def fairRegularAmplificationAt (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D) ∧
        (RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q) then
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteSplitModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent sites with two fair splits at each site -/

namespace JointDickman

open Finset

structure TwoSiteSplit (P : Finset ℕ) where
  site₁ : P.powerset
  site₂ : P.powerset
  first₁ : P.powerset
  first₂ : P.powerset
  second₁ : P.powerset
  second₂ : P.powerset
  deriving Fintype, DecidableEq

def TwoSiteSplit.swap {P : Finset ℕ} (x : TwoSiteSplit P) : TwoSiteSplit P :=
  ⟨x.site₁, x.site₂, x.second₁, x.second₂, x.first₁, x.first₂⟩

theorem TwoSiteSplit.swap_swap {P : Finset ℕ} (x : TwoSiteSplit P) : x.swap.swap = x := by
  cases x
  rfl

def amplificationSplitGood (B L T : ℕ) (τ C : ℝ) (S₁ S₂ A D : Finset ℕ) : Prop :=
  (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T ∧
    RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
    RegularPrimeSet B L τ C (S₁ \ A) ∧ RegularPrimeSet B L τ C (S₂ \ D)

def bothAmplificationSplitsGood (B L T : ℕ) (τ C : ℝ)
    (x : TwoSiteSplit (auxiliaryPrimes B)) : Prop :=
  amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.first₁.val x.first₂.val ∧
  amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.second₁.val x.second₂.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalCoinAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common finite expectation for the conditional second split -/

namespace JointDickman
open Finset

noncomputable def conditionalCoinAverage (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ I ∈ A.powerset, ∑ J ∈ D.powerset,
    ∑ Q ∈ P.powerset, ∑ V ∈ P.powerset, ∑ R ∈ P.powerset, ∑ U ∈ P.powerset,
      bernoulliSubsetMass A (fun _ => (1 / 2 : ℝ)) I *
      bernoulliSubsetMass D (fun _ => (1 / 2 : ℝ)) J *
      jointRetentionMass P (remainingPrimeParameter D) Q V *
      jointRetentionMass P (remainingPrimeParameter A) R U * F R Q I J U V

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NativeOrientedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of the actual oriented event by the conditional operator -/

namespace JointDickman
open Finset

def nativeOrientedEvent (B L T : ℕ) (τ C Y : ℝ)
    (A D R Q I J U V : Finset ℕ) : Prop :=
  Disjoint A R ∧ Disjoint D Q ∧ U ⊆ R ∧ V ⊆ Q ∧
  RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
  (∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) ∧
  (∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y) ∧
  (∏ p ∈ I ∪ U, p, ∏ p ∈ J ∪ V, p) ∈ amplificationCoefficientPairs B T ∧
  ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p

open Classical in
noncomputable def nativeOrientedMass (B L T : ℕ) (τ C Y : ℝ) (A D : Finset ℕ) : ℝ :=
  conditionalCoinAverage (auxiliaryPrimes B) A D
    (fun R Q I J U V => if nativeOrientedEvent B L T τ C Y A D R Q I J U V then 1 else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OrientedProbabilityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the oriented conditional bound to the actual two-site event -/

namespace JointDickman
open Finset

def firstCoefficientGood (B L T : ℕ) (τ C : ℝ) (A D : Finset ℕ) : Prop :=
  (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T ∧
  RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D

def orientedTwoSplitTest (B L T : ℕ) (τ C Y : ℝ)
    (A R E D Q F : Finset ℕ) : Prop :=
  firstCoefficientGood B L T τ C A D ∧
  RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
  (∀ p ∈ symmDiff A E, Real.log p ≤ Y) ∧
  (∀ p ∈ symmDiff D F, Real.log p ≤ Y) ∧
  (∏ p ∈ E, p, ∏ p ∈ F, p) ∈ amplificationCoefficientPairs B T ∧
  ∃ p ∈ E \ A, Y / 2 < Real.log p

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NoChangeSplitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The no-change part of the amplification second moment -/

namespace JointDickman

open Finset Filter
open scoped Topology

/-- All second assignments agree with the first assignments, retaining the
necessary lower tail restrictions on the two remaining sets. -/
noncomputable def noChangeSplitMass (B : ℕ) (A D : Finset ℕ) (C : ℝ) : ℝ :=
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
  (1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^D.card *
    (highNoAdditionMass (auxiliaryPrimes B) (remainingPrimeParameter D) k *
      highNoAdditionMass (auxiliaryPrimes B) (remainingPrimeParameter A) k)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NoChangeCoinOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact no-change operator on conditional second coins -/

namespace JointDickman
open Finset

noncomputable def noChangeCoinOperator (P A D : Finset ℕ) (k : ℝ) : ℝ :=
  keptHighAverage ∅ A (fun _ => keptHighAverage ∅ D (fun _ =>
    noHighAdditionAverage ∅ P (remainingPrimeParameter D) k (fun _ =>
      noHighAdditionAverage ∅ P (remainingPrimeParameter A) k (fun _ => 1))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NoChangeConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The no-change event in the exact conditional law -/

namespace JointDickman
open Finset

def noChangeTwoSplitTest (B L T : ℕ) (τ C : ℝ) (A R E D Q F : Finset ℕ) : Prop :=
  firstCoefficientGood B L T τ C A D ∧ RegularPrimeSet B L τ C R ∧
    RegularPrimeSet B L τ C Q ∧ E = A ∧ F = D

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FirstCoefficientAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging conditional estimates over the first coefficient event -/

namespace JointDickman
open Finset

open Classical in
noncomputable def firstCoefficientAverage (B L T : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
  ∑ D ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
    (if firstCoefficientGood B L T τ C A D then F A D else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteSplitProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional products of the two independent fair splits -/

namespace JointDickman
open Finset

noncomputable def sitePairSplitAverage (P S T : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ C ∈ P.powerset,
    subsetRetentionMass S A * subsetRetentionMass T C * F A C

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent-model amplification envelope and its second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def independentAmplificationEnvelope (B L T : ℕ) (τ C : ℝ)
    (S R : Finset ℕ) : ℝ :=
  B * sitePairSplitAverage (auxiliaryPrimes B) S R
    (fun A D => if amplificationSplitGood B L T τ C S R A D then 1 else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded coefficient cutoffs in the independent amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def independentWeightedAmplification (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (S R : Finset ℕ) : ℝ :=
  B * sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D =>
    if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
    then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor weight equals the fair-split model away from square hits -/

namespace JointDickman
open Finset

open Classical in
noncomputable def arithmeticSubsetAmplification (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (B : ℝ)) * ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1 then
      (regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p)))) *
      (regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B ((n + 1) / (∏ p ∈ D, p)))) *
      w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the actual arithmetic amplification into a divisor form -/

namespace JointDickman
open Finset

noncomputable def arithmeticResidueWeight (B L : ℕ) (τ C : ℝ) (n : ℕ) : ℝ :=
  regularResidueWeight B L τ C (coefficientPrimeSet B n)

open Classical in
noncomputable def amplificationDivisorForm (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (H : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    ∑ m ∈ range N, if a*m < N ∧ c ∣ a*m+1 then
      H (a*m) * (((regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m) *
        (regularCoefficientWeight B L τ C c * arithmeticResidueWeight B L τ C ((a*m+1)/c)) *
        w a c : ℝ) : ℂ) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_InteriorAmplificationWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive coefficient windows strictly inside the smooth cutoff support -/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def amplificationInteriorC (B : ℕ) : Finset ℕ :=
  Ioc ⌊Real.exp ((5 / 4 : ℝ) * B)⌋₊ ⌊Real.exp ((3 / 2 : ℝ) * B)⌋₊

noncomputable def amplificationInteriorA (T c : ℕ) : Finset ℕ :=
  Ioc ⌊(5 / 4 : ℝ) * T * c⌋₊ ⌊(3 / 2 : ℝ) * T * c⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_InteriorAmplificationMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive first moment strictly inside both coefficient cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def amplificationInteriorPairs (B T : ℕ) : Finset (ℕ × ℕ) :=
  (amplificationInteriorC B).biUnion fun c => (amplificationInteriorA T c).image fun a => (a, c)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationSmoothCutoff
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth cutoff equal to one on the positive interior rectangle -/

namespace JointDickman
open Finset

noncomputable def amplificationBump : ContDiffBump (11/8 : ℝ) where
  rIn := 1/8
  rOut := 1/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def amplificationSmoothWeight (B T a c : ℕ) : ℝ :=
  amplificationBump (Real.log c / B) * amplificationBump ((a : ℝ) / ((T : ℝ)*c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticAmplificationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the actual arithmetic amplification -/

namespace JointDickman
open Finset

open Classical in
noncomputable def arithmeticSiteWeight (B L : ℕ) (τ C : ℝ) (n : ℕ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p) ∣ n then
      regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p)))
    else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite period of the divisor amplification -/

namespace JointDickman
open Finset

noncomputable def auxiliarySquarePeriod (B : ℕ) : ℕ :=
  (∏ p ∈ auxiliaryPrimes B, p)^2

theorem auxiliarySquarePeriod_pos (B : ℕ) : 0 < auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  exact pow_pos (prod_pos (fun p hp => (auxiliaryPrimes_prime B p hp).pos)) _

instance instNeZeroNatAuxiliarySquarePeriod (B : ℕ) : NeZero (auxiliarySquarePeriod B) :=
  ⟨(auxiliarySquarePeriod_pos B).ne'⟩

open Classical in
noncomputable def residueAmplification (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ)
    (a : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  arithmeticSubsetAmplification B L τ C w a.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticSquareHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact rare-square error for the arithmetic amplification -/

namespace JointDickman
open Finset

open Classical in
def AuxiliarySquareHit (B n : ℕ) : Prop :=
  ∃ p ∈ auxiliaryPrimes B, p^2 ∣ n ∨ p^2 ∣ n+1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConsecutivePrimeHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two-hit law at one prime for consecutive integers -/

namespace JointDickman
open Finset

noncomputable def consecutivePrimeHit {p : ℕ} (r : ZMod p) : Bool × Bool :=
  (decide (r = 0), decide (r = -1))

noncomputable def consecutiveHitMass (q : ℝ) (v : Bool × Bool) : ℝ :=
  if v.1 then (if v.2 then 0 else q) else (if v.2 then q else 1 - 2*q)

noncomputable def independentHitMass (q : ℝ) (v : Bool × Bool) : ℝ :=
  bernoulliBitMass q v.1 * bernoulliBitMass q v.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PairHitSites
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing two prime-hit vectors as two prime subsets -/

namespace JointDickman
open Finset

noncomputable def pairHitEquiv (P : Finset ℕ) :
    (P.powerset × P.powerset) ≃ (P → Bool × Bool) where
  toFun S p := (subsetHitEquiv P S.1 p, subsetHitEquiv P S.2 p)
  invFun x := ((subsetHitEquiv P).symm (fun p => (x p).1),
    (subsetHitEquiv P).symm (fun p => (x p).2))
  left_inv S := by simp
  right_inv x := by
    funext p
    exact Prod.ext
      (congrFun ((subsetHitEquiv P).apply_symm_apply (fun p => (x p).1)) p)
      (congrFun ((subsetHitEquiv P).apply_symm_apply (fun p => (x p).2)) p)

noncomputable def hitSites (P : Finset ℕ) (x : P → Bool × Bool) : P.powerset × P.powerset :=
  (pairHitEquiv P).symm x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticMomentComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic amplification moments and the independent model -/

namespace JointDickman
open Finset

noncomputable def arithmeticAmplificationMoment (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ a : ZMod (auxiliarySquarePeriod B),
    (arithmeticSubsetAmplification B L τ C w a.val)^k) / (auxiliarySquarePeriod B : ℝ)

noncomputable def independentAmplificationMoment (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
    ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
      (independentWeightedAmplification B L τ C w S R)^k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_InteriorRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interior positive mass survives all four regularity cutoffs -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def fairRegularInteriorMass (B L T : ℕ) (τ C : ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T then
      fairRegularAmplificationAt B L τ C A D else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Hilbert estimates for residue profiles

Only uniform finite residue means are needed for the profile-preservation
argument. Their compatible refinements replace an explicit construction of
Haar measure on the profinite integers.
-/

namespace JointDickman
open Finset

noncomputable def residueEnergy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ℝ :=
  (∑ a, ‖f a‖ ^ 2) / (q : ℝ)

noncomputable def residueLift {d q : ℕ} (f : ZMod d → ℂ) (a : ZMod q) : ℂ :=
  f (a.val : ZMod d)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationFirstForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first divisor form and its quadratic energy -/

namespace JointDickman
open Finset

noncomputable def firstFormWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (D : Finset ℕ) (m : ℕ) : ℝ :=
  u (∏ p ∈ D, p) * regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
    arithmeticResidueWeight B L τ C m

open Classical in
noncomputable def firstFormInner (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) (D : Finset ℕ) (m : ℕ) : ℂ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    if a*m < N ∧ c ∣ a*m+1 then
      ((regularCoefficientWeight B L τ C a *
        arithmeticResidueWeight B L τ C ((a*m+1)/c) * v a c : ℝ) : ℂ) * J (a*m)
    else 0

noncomputable def firstDivisorForm (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (g J : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    (firstFormWeight B L τ C u i.1 i.2 : ℂ) * star (g i.2) *
      firstFormInner B L τ C v J N i.1 i.2) / (N : ℂ)

noncomputable def firstFormEnergy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 * ‖firstFormInner B L τ C v J N i.1 i.2‖^2) / (N : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveFirstForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the Cauchy volume to the actual multiplier range -/

namespace JointDickman
open Finset

noncomputable def activeFirstFormWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (T N : ℕ) (D : Finset ℕ) (m : ℕ) : ℝ :=
  if T*(∏ p ∈ D, p)*m < N then firstFormWeight B L τ C u D m else 0

noncomputable def activeFirstFormVolume (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (T N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    activeFirstFormWeight B L τ C u T N i.1 i.2) / (N : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationVolumeProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient harmonic mass cancels the residue-weight mean -/

namespace JointDickman
open Finset

noncomputable def baseArithmeticResidueWeight (B n : ℕ) : ℝ :=
  residueBaseWeight B (coefficientPrimeSet B n)

noncomputable def baseArithmeticResidueMean (B : ℕ) : ℝ :=
  auxiliaryRatio B ^ (1/2 : ℝ) * primeNormalizer (auxiliaryPrimes B) (1/2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveVolumeMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic majorant for the active Cauchy volume -/

namespace JointDickman
open Finset

noncomputable def activeVolumeMajorant (B T N : ℕ) : ℝ :=
  ∑ D ∈ (auxiliaryPrimes B).powerset,
    coefficientWeight B (∏ p ∈ D, p) *
      ((∑ m ∈ range (N/(T*(∏ p ∈ D, p))+1), baseArithmeticResidueWeight B m)/(N : ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible finite residue profiles

A profile records the conditional averages on every finite residue space.
Compatibility is tested against all functions on a coarser residue space.
The energy identity below is the finite conditional-expectation identity.
-/

namespace JointDickman
open Finset

structure ResidueProfile where
  value : (q : ℕ+) → ZMod (q : ℕ) → ℂ
  compatible : ∀ (d q : ℕ+) (_ : (d : ℕ) ∣ (q : ℕ)) (g : ZMod (d : ℕ) → ℂ),
    residueMean (fun a => value q a * residueLift g a) =
      residueMean (fun a => value d a * g a)
  energy_bounded : BddAbove (Set.range fun q => residueEnergy (value q))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProfilePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preservation of every bounded residue profile by moving-prime weights -/

namespace JointDickman
open Finset Filter
open scoped Topology

namespace ResidueProfile

noncomputable def mean (W : ResidueProfile) : ℂ := residueMean (W.value 1)

noncomputable def correlation (W : ResidueProfile) (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) : ℂ :=
  residueMean (fun a => W.value q a * f a)

end ResidueProfile
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticProfilePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Profile preservation for the manuscript's actual smooth divisor weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationPeriod (B : ℕ) : ℕ+ :=
  ⟨auxiliarySquarePeriod B, auxiliarySquarePeriod_pos B⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EmpiricalResidueProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite residue coefficients of a bounded arithmetic correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def empiricalResidueCoefficient (H : ℕ → ℕ → ℂ) (N : ℕ)
    (q : ℕ+) (a : ZMod (q : ℕ)) : ℂ :=
  (q : ℕ) * ((∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0) / (N : ℂ))

noncomputable def empiricalResidueTest (H : ℕ → ℕ → ℂ) (N : ℕ)
    {q : ℕ} (f : ZMod q → ℂ) : ℂ :=
  (∑ n ∈ range N, H N n * f (n : ZMod q)) / (N : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published short-interval inputs for the joint Dickman problem

These definitions are *propositions to be supplied as hypotheses*. They are not
axioms or proofs of the cited analytic theorems. In particular they do not
assume joint independence at the shift one, the manuscript's new mixed
decorrelation proposition, or any of its graph estimates.

The natural-number floor is harmless here: all intervals to which the inputs
apply have positive left endpoint. `Finset.Ioc` implements the convention
`z < n ≤ z + H`; changing the inclusion of the endpoints has the elementary
`O(1 / H)` cost recorded in the manuscript.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

/-- A complex short average with the same endpoint convention. -/
noncomputable def complexShortAverage (f : ArithmeticFunction ℂ) (H z : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, f n) / (H : ℂ)

/-- The squared pretentious distance from `n ↦ n^(it)` up to `X`. -/
noncomputable def primeDistanceSquared (f : ArithmeticFunction ℂ) (X t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)).re) /
      (p : ℝ)

end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

/-- The prime bin `(x^(k/J), x^((k+1)/J)]`. -/
noncomputable def primeBin (x : ℝ) (J k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc ⌊x ^ ((k : ℝ) / J)⌋₊ ⌊x ^ (((k : ℝ) + 1) / J)⌋₊).filter Nat.Prime

/-- The number of factors in a finite bin, with multiplicity. -/
def binCount (E : Finset ℕ) (n : ℕ) : ℕ := ∑ p ∈ E, n.factorization p

@[simp] theorem binCount_one (E : Finset ℕ) : binCount E 1 = 0 := by
  simp [binCount]

@[simp] theorem binCount_zero (E : Finset ℕ) : binCount E 0 = 0 := by
  simp [binCount]

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

/-- A bin label, viewed as an arithmetic function (so its value at zero is zero). -/
noncomputable def binLabel (E : ι → Finset ℕ) (z : ι → R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else ∏ i, z i ^ binCount (E i) n, by simp⟩

@[simp] theorem binLabel_apply_zero (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z 0 = 0 := by simp [binLabel]

@[simp] theorem binLabel_apply_one (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z 1 = 1 := by simp [binLabel]

end Labels


section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct real interpolation nodes strictly between zero and one. -/
noncomputable def interpolationNode {m : ℕ} (j : Fin m) : ℝ := ((j : ℝ) + 1) / ((m : ℝ) + 1)

end Interpolation

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's multiplier scale and negligible diagonal cap -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def amplificationMultiplier (B : ℕ) : ℕ := ⌊(B : ℝ) ^ (8/25 : ℝ)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstFormDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal is bounded by one weight cap times the linear mass -/

namespace JointDickman
open Finset

open Classical in
noncomputable def firstFormAtom (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) (D : Finset ℕ) (m : ℕ) (A : Finset ℕ) : ℂ :=
  let a := ∏ p ∈ A, p
  let c := ∏ p ∈ D, p
  if a*m < N ∧ c ∣ a*m+1 then
    ((regularCoefficientWeight B L τ C a *
      arithmeticResidueWeight B L τ C ((a*m+1)/c) * v a c : ℝ) : ℂ) * J (a*m)
  else 0

noncomputable def firstFormDiagonal (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ‖firstFormAtom B L τ C v J N i.1 i.2 A‖^2) / (N : ℝ)

noncomputable def firstFormMass (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (firstDivisorForm B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N).re

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DiagonalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth amplification has a negligible diagonal -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationOuterWeight (B c : ℕ) : ℝ :=
  amplificationBump (Real.log c / B)

noncomputable def amplificationInnerWeight (T a c : ℕ) : ℝ :=
  amplificationBump ((a : ℝ) / ((T : ℝ)*c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BinLabelPositiveEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive energy forced by a nonzero mixed bin-label correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def movingBinLabel {ι : Type*} [Fintype ι]
    (J : ℕ) (k : ι → ℕ) (z : ι → ℂ) (N n : ℕ) : ℂ :=
  binLabel (fun i => primeBin (N : ℝ) J (k i)) z n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_OffDiagonalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unequal-coefficient terms of the actual quadratic energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def firstFormOffDiagonal (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if A = D then 0 else
          (star (firstFormAtom B L τ C v J N i.1 i.2 A) *
            firstFormAtom B L τ C v J N i.1 i.2 D).re) / (N : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorEdgeReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite transport from multiplier sums to additive graph endpoints -/

namespace JointDickman
open Finset

noncomputable def divisorEdgeInverse (a b c n : ℕ) : ℕ := (c*(n/b)-1)/a

noncomputable def divisorEdgeOld (a b c N : ℕ) : Finset ℕ :=
  (range N).filter (fun m => a*m < N ∧ b*m < N ∧ c ∣ a*m+1 ∧ c ∣ b*m+1)

noncomputable def divisorEdgeNew (a b c N : ℕ) (j : ℤ) : Finset ℕ :=
  (Icc 1 (b*N)).filter (fun n => b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j ∧
    a*divisorEdgeInverse a b c n < N ∧ b*divisorEdgeInverse a b c n < N)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstFormPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic weight of each unequal-coefficient pair -/

namespace JointDickman
open Finset

noncomputable def firstFormPairWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (D A E : Finset ℕ) (m : ℕ) : ℝ :=
  firstFormWeight B L τ C u D m *
    (regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      arithmeticResidueWeight B L τ C (((∏ p ∈ A, p)*m+1)/(∏ p ∈ D, p)) *
        v (∏ p ∈ A, p) (∏ p ∈ D, p)) *
    (regularCoefficientWeight B L τ C (∏ p ∈ E, p) *
      arithmeticResidueWeight B L τ C (((∏ p ∈ E, p)*m+1)/(∏ p ∈ D, p)) *
        v (∏ p ∈ E, p) (∏ p ∈ D, p))

noncomputable def firstFormPairEnergy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (D A E : Finset ℕ) : ℝ :=
  ∑ m ∈ range N, firstFormWeight B L τ C u D m *
    (star (firstFormAtom B L τ C v J N D m A) * firstFormAtom B L τ C v J N D m E).re

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic graph weight obtained from the actual quadratic form -/

namespace JointDickman
open Finset

noncomputable def arithmeticGraphPairWeight (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  (u c * regularCoefficientWeight B L τ C c *
    arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n)) *
  (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b) * v a c) *
  (regularCoefficientWeight B L τ C b *
    arithmeticResidueWeight B L τ C (((n : ℤ)+j).toNat/a) * v b c)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical lags and the finite coefficient support of the graph -/

namespace JointDickman
open Finset

noncomputable def coefficientPairLag (D A E : Finset ℕ) : ℤ :=
  (((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ))/(∏ p ∈ D, p : ℕ)

def GraphCoefficientAdmissible (T : ℕ) (D A E : Finset ℕ) : Prop :=
  A ≠ E ∧ coefficientPairLag D A E ≠ 0 ∧ (coefficientPairLag D A E).natAbs < T ∧
    ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = coefficientPairLag D A E*(∏ p ∈ D, p : ℕ) ∧
    (∏ p ∈ A, p).Coprime (coefficientPairLag D A E).natAbs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticOffDiagonalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact graph representation of the full off-diagonal energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def arithmeticOffDiagonalGraph (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) : ℝ :=
  (∑ D ∈ (auxiliaryPrimes B).powerset, ∑ A ∈ (auxiliaryPrimes B).powerset,
    ∑ E ∈ (auxiliaryPrimes B).powerset, if GraphCoefficientAdmissible T D A E then
      ∑ n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N (coefficientPairLag D A E),
        arithmeticGraphPairWeight B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
          (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) (coefficientPairLag D A E) n *
          (star (F n) * F ((n : ℤ)+coefficientPairLag D A E).toNat).re
      else 0) / (N : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticGraphKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual arithmetic graph by lag and endpoint -/

namespace JointDickman
open Finset

abbrev GraphCoefficientTriple := Finset ℕ × (Finset ℕ × Finset ℕ)

open Classical in
noncomputable def arithmeticGraphTriples (B T : ℕ) : Finset GraphCoefficientTriple :=
  ((auxiliaryPrimes B).powerset ×ˢ
    ((auxiliaryPrimes B).powerset ×ˢ (auxiliaryPrimes B).powerset)).filter
      (fun i => GraphCoefficientAdmissible T i.1 i.2.1 i.2.2)

noncomputable def arithmeticGraphVertexCap (B N : ℕ) : ℕ :=
  (∏ p ∈ auxiliaryPrimes B, p)*N

noncomputable def graphTripleLag (i : GraphCoefficientTriple) : ℤ :=
  coefficientPairLag i.1 i.2.1 i.2.2

noncomputable def graphTripleEdges (N : ℕ) (i : GraphCoefficientTriple) : Finset ℕ :=
  divisorEdgeNew (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) N (graphTripleLag i)

noncomputable def graphTripleWeight (B L : ℕ) (τ C : ℝ) (T : ℕ)
    (i : GraphCoefficientTriple) (n : ℕ) : ℝ :=
  arithmeticGraphPairWeight B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) (graphTripleLag i) n

open Classical in
noncomputable def rawArithmeticGraphKernel (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ arithmeticGraphTriples B T,
    if graphTripleLag i = j ∧ n ∈ graphTripleEdges N i then graphTripleWeight B L τ C T i n else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite candidate representations determined by endpoint types -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointSplits (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter (fun A => RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A))

abbrev BlockCandidateIndex (M : ℕ) := (Fin M × Fin M) × (Finset ℕ × Finset ℕ)

/-- Lower and upper endpoint subsets; the coefficient c is determined by
these two subset products and the positive lag. -/
noncomputable def candidateLow {M : ℕ} (e : BlockCandidateIndex M) : ℕ := ∏ p ∈ e.2.1, p
noncomputable def candidateHigh {M : ℕ} (e : BlockCandidateIndex M) : ℕ := ∏ p ∈ e.2.2, p
def candidateLag {M : ℕ} (e : BlockCandidateIndex M) : ℕ := e.1.2.val-e.1.1.val
noncomputable def candidateQuotient {M : ℕ} (e : BlockCandidateIndex M) : ℕ :=
  (candidateHigh e-candidateLow e)/candidateLag e

open Classical in
noncomputable def blockCandidatePool (B L M : ℕ) (τ C : ℝ) (S : Fin M → Finset ℕ) :
    Finset (BlockCandidateIndex M) :=
  (univ : Finset (Fin M × Fin M)).biUnion (fun ik =>
    ((endpointSplits B L τ C (S ik.1)).product (endpointSplits B L τ C (S ik.2))).image
      (fun ab => (ik,ab)))

def BlockCandidateAdmissible {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) : Prop :=
  e.1.1 < e.1.2 ∧ H < candidateLag e ∧ candidateLag e < T ∧
  0 < candidateQuotient e ∧
  candidateHigh e = candidateLow e+candidateLag e*candidateQuotient e ∧
  (candidateLow e).Coprime (candidateHigh e) ∧
  (candidateLow e).Coprime (candidateQuotient e) ∧
  (candidateHigh e).Coprime (candidateQuotient e) ∧
  candidateQuotient e = ∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B (candidateQuotient e)) ∧
  (B : ℝ) ≤ Real.log (candidateQuotient e) ∧
  Real.log (candidateQuotient e) ≤ 2*B ∧
  T*candidateQuotient e ≤ candidateLow e ∧ candidateLow e ≤ 2*T*candidateQuotient e ∧
  T*candidateQuotient e ≤ candidateHigh e ∧ candidateHigh e ≤ 2*T*candidateQuotient e

open Classical in
noncomputable def blockCandidates (B L T H M : ℕ) (τ C : ℝ) (S : Fin M → Finset ℕ) :
    Finset (BlockCandidateIndex M) :=
  (blockCandidatePool B L M τ C S).filter (BlockCandidateAdmissible B L T H τ C)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalCandidateRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational roots of candidate representations -/

namespace JointDickman

noncomputable def shiftedCandidateRoot (b c : ℕ) (i : ℤ) : ℚ := (b : ℚ)/c-i

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRootGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of a representation at a fixed pair of endpoints -/

namespace JointDickman
open Finset

noncomputable def blockCandidateRoot {M : ℕ} (e : BlockCandidateIndex M) : ℚ :=
  shiftedCandidateRoot (candidateLow e) (candidateQuotient e) (e.1.1.val+1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateExceptionalPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large-prime obstructions attached to actual candidate roots -/

namespace JointDickman
open Finset

noncomputable def candidateRootNumerator {M : ℕ} (e : BlockCandidateIndex M) : ℤ :=
  (candidateLow e : ℤ)-(e.1.1.val+1)*candidateQuotient e

noncomputable def candidateSiteValue {M : ℕ} (e : BlockCandidateIndex M) (s : Fin M) : ℤ :=
  (candidateLow e : ℤ)+((s.val : ℤ)-e.1.1.val)*candidateQuotient e

noncomputable def candidateRootDifference {M : ℕ} (e f : BlockCandidateIndex M) : ℤ :=
  candidateRootNumerator e*candidateQuotient f-candidateRootNumerator f*candidateQuotient e

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RequiredPrimeProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Availability of a prescribed coefficient at an independent endpoint -/

namespace JointDickman
open Finset

def PrimeProductAvailable (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A ⊆ S, (∏ p ∈ A, p) = n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CutBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real cut tests control complex label energies

This is the deterministic estimate (graph-cut-labels) in the manuscript.
It makes no independence assumption about the labels and the kernel.
-/

open scoped BigOperators ComplexConjugate

namespace JointDickman

/-- Signs used in the finite cut maximum. -/
def cutSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def realBilinear {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (f g : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, K i j * f i * g j

noncomputable def complexEnergy {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (K i j : ℂ) * conj (z i) * z j

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingSkeleton
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A small-column sampling skeleton

This is the deterministic part of `sampling-skeleton` in the manuscript.
Sampling with replacement allows repeated columns; their multiplicities are
retained in the row response.  The number of distinct columns is at most the
sample size.  No probabilistic or cut-approximation hypothesis is assumed.
-/

open scoped BigOperators
open Finset

namespace JointDickman

attribute [local instance] Classical.propDecidable

/-- The best-response sign, with the manuscript's convention at zero. -/
noncomputable def responseSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

@[simp] theorem abs_responseSign (x : ℝ) : |responseSign x| = 1 := by
  unfold responseSign
  split_ifs <;> norm_num

/-- The residual column optimum after deleting the sampled endpoints. -/
noncomputable def residualColumnBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (T : Finset ι) (g : ι → ℝ) : ℝ :=
  ∑ j ∈ univ \ T, |∑ i ∈ univ \ T, K i j * g i|

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concentration after restriction to a common good event

The extension used in the manuscript's sampling argument is constructed
explicitly from a finite good set. The only concentration hypothesis below
is the uniform-constant finite-product specialization of McDiarmid's
published bounded-differences inequality.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section Extension

variable {ι A : Type*} [Fintype ι] [DecidableEq A]

/-- The finite McShane extension, clamped at the chosen upper bound. -/
noncomputable def goodSetExtension (G : Finset (ι → A)) (hG : G.Nonempty)
    (f : (ι → A) → ℝ) (c L : ℝ) (x : ι → A) : ℝ :=
  min L (G.inf' hG (fun y => f y + c * hammingDist x y))

end Extension

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Expectation with respect to an explicitly supplied finite mass function. -/
noncomputable def finiteExpectation (w : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, w x * f x

/-- Event mass for the same finite law. -/
noncomputable def finiteProbability (w : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  by classical exact ∑ x, if E x then w x else 0

end FiniteProbability

namespace PublishedInputs

/-- Independent site mass, retaining the actual coordinate laws. -/
noncomputable def siteProductMass {ι A : Type*} [Fintype ι]
    (p : ι → A → ℝ) (x : ι → A) : ℝ := ∏ i, p i (x i)

/-- McDiarmid, *On the method of bounded differences*, Surveys in
Combinatorics 1989, Theorem (6.7), pp. 166–167 (proof p. 168),
DOI `10.1017/CBO9781107359949.008`. The one-sided estimate follows by
applying that martingale theorem to the coordinate Doob martingale.
Only independent finite sites and one common coordinate bound are needed.
The global Hamming bound is a stronger sufficient hypothesis on `f`. -/
def FiniteMcDiarmidInput (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] : Prop :=
  ∀ (p : ι → A → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
    ∀ (f : (ι → A) → ℝ) (c : ℝ), 0 ≤ c →
      (∀ x y, |f x - f y| ≤ c * hammingDist x y) →
      ∀ a : ℝ, 0 < a →
        finiteProbability (siteProductMass p)
          (fun x => a < f x - finiteExpectation (siteProductMass p) f) ≤
          Real.exp (-2 * a ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2))

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingMoments
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-product moments for the sampling argument

All expectations here are finite sums with the actual independent site
masses. The variance identities, conditional moments, and absolute-error
estimates are proved directly; no moment or independence input is assumed.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section ConditionalSite

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Reinsert one fixed site into a configuration on the other sites. -/
def insertSite (k : ι) (a : A) (x : {i : ι // i ≠ k} → A) (i : ι) : A :=
  if h : i = k then a else x ⟨i, h⟩

omit [Fintype ι] [Fintype A] in
@[simp] theorem insertSite_self (k : ι) (a : A) (x : {i : ι // i ≠ k} → A) :
    insertSite k a x k = a := by simp [insertSite]

omit [Fintype ι] [Fintype A] in
@[simp] theorem insertSite_other (k : ι) (a : A) (x : {i : ι // i ≠ k} → A)
    (i : {i : ι // i ≠ k}) : insertSite k a x i = x i := by simp [insertSite, i.property]

/-- A row evaluated on the independent site configuration. -/
noncomputable def siteRowSum (K : ι → ι → A → A → ℝ) (k : ι) (x : ι → A) : ℝ :=
  ∑ j, K k j (x k) (x j)

end ConditionalSite

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite sampling transfer

The finite family consists of sampled column sequences and one sign per
sampled occurrence. Its cardinal is `(2 * N)^m`, including repeated columns.
The common bad event is paid once. Moment and tail obligations are explicit
mathematical hypotheses, not additional published inputs.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized finite real sign-cut maximum. -/
noncomputable def kernelCutMaximum (K : ι → ι → ℝ) : ℝ :=
  (univ : Finset ((ι → Bool) × (ι → Bool))).sup' univ_nonempty
    (fun st => |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)

/-- A sampled column sequence with a sign attached to each occurrence. -/
abbrev ColumnSample (m : ℕ) := (Fin m → ι) × (Fin m → Bool)

noncomputable def columnSampleResponse {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) (i : ι) : ℝ :=
  responseSign (∑ a, K i (s.1 a) * cutSign (s.2 a))

noncomputable def columnSampleResidual {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) : ℝ :=
  residualColumnBound K (univ.image s.1) (columnSampleResponse K s)

/-- The manuscript's normalization divides the sign maximum by `N`. -/
noncomputable def kernelCutNorm (K : ι → ι → ℝ) : ℝ :=
  kernelCutMaximum K / Fintype.card ι

noncomputable def kernelAbsoluteMass (K : ι → ι → ℝ) : ℝ :=
  (∑ i, ∑ j, |K i j|) / Fintype.card ι

noncomputable def columnSampleNorm {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) : ℝ := columnSampleResidual K s / Fintype.card ι

end CutFamily

section SiteKernel

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A]

/-- Realizing a finite site kernel on one independent configuration. -/
def realizedSiteKernel (E : ι → ι → A → A → ℝ) (x : ι → A) (i j : ι) : ℝ :=
  E i j (x i) (x j)

end SiteKernel

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteExponentialMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite exponential moments control the expectation of a maximum -/

namespace JointDickman
open Finset
open PublishedInputs

noncomputable def finiteFamilyMaximum {J Ω : Type*} [Fintype J] [Nonempty J]
    (X : J → Ω → ℝ) (x : Ω) : ℝ :=
  univ.sup' univ_nonempty (fun j => X j x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetric matrices assembled from unordered candidate edges -/

namespace JointDickman
open Finset

noncomputable def candidateMatrix {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (i k : κ) : ℝ :=
  ∑ e, ((if i = row e then if k = col e then v e else 0 else 0)+
    (if i = col e then if k = row e then v e else 0 else 0))

abbrev EdgeCutTest (κ : Type*) := ((κ → Bool) × (κ → Bool)) × Bool

noncomputable def edgeCutCoefficient {ι κ : Type*} (row col : ι → κ)
    (s : EdgeCutTest κ) (e : ι) : ℝ :=
  cutSign s.2*(cutSign (s.1.1 (row e))*cutSign (s.1.2 (col e))+
    cutSign (s.1.1 (col e))*cutSign (s.1.2 (row e)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRootKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent auxiliary-root weights for the actual candidate list -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

/-- The five endpoint/coefficient factors and the sixth, auxiliary-root
factor in the manuscript's kernel, including its normalization. -/
noncomputable def candidateRootWeight {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) (R : Finset ℕ) : ℝ :=
  (regularCoefficientWeight B L τ C (candidateLow e) *
    regularResidueWeight B L τ C (S e.1.1 \ e.2.1) *
    (regularCoefficientWeight B L τ C (candidateHigh e) *
      regularResidueWeight B L τ C (S e.1.2 \ e.2.2)) *
    (regularCoefficientWeight B L τ C (candidateQuotient e) *
      regularResidueWeight B L τ C R))/(B : ℝ) * χ e

noncomputable def independentPrimeSetMass (B : ℕ) (R : (auxiliaryPrimes B).powerset) : ℝ :=
  bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R.val

noncomputable def candidateMeanWeight {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  finiteExpectation (independentPrimeSetMass B)
    (fun R => candidateRootWeight B L τ C S χ e R.val)

noncomputable def latentCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) : Fin M → Fin M → ℝ :=
  candidateMatrix (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
    (fun e => e.val.1.2) (fun e => candidateMeanWeight B L τ C S χ e.val)

noncomputable def independentCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (R : blockCandidates B L T H M τ C S → (auxiliaryPrimes B).powerset) :
    Fin M → Fin M → ℝ :=
  candidateMatrix (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
    (fun e => e.val.1.2) (fun e => candidateRootWeight B L τ C S χ e.val (R e).val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forced hits at an independently sampled third endpoint -/

namespace JointDickman
open Finset

open Classical in
noncomputable def candidateForcedPrimes {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (s : Fin M) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => p ∣ (candidateSiteValue e s).natAbs)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disintegration of independent site laws over a chosen set -/

namespace JointDickman
open Finset PublishedInputs

section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

noncomputable def mergeSitePartition (I : Finset ι) (a : I → Ω)
    (b : {i : ι // i ∉ I} → Ω) (i : ι) : Ω :=
  if h : i ∈ I then a ⟨i,h⟩ else b ⟨i,h⟩

end
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRepeatEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local third-site event covering coincident rational roots -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
noncomputable def pairSplitChoices (B L : ℕ) (τ C : ℝ) (S R : Finset ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (endpointSplits B L τ C S).product (endpointSplits B L τ C R)

def CandidateRepeatWitness {M : ℕ} (T : ℕ) (e : BlockCandidateIndex M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ s : Fin M, s ≠ e.1.1 ∧ s ≠ e.1.2 ∧
    T*candidateQuotient e ≤ (candidateSiteValue e s).natAbs ∧
    PrimeProductAvailable (candidateSiteValue e s).natAbs (S s)

def PairRepeatEvent (B L T H M : ℕ) (τ C : ℝ) (i k : Fin M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ ab ∈ pairSplitChoices B L τ C (S i) (S k),
    BlockCandidateAdmissible B L T H τ C ((i,k),ab) ∧
    CandidateRepeatWitness T ((i,k),ab) S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRepeatProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated rational roots in the actual random candidate list -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

def RepeatedCandidateRoot (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ e ∈ blockCandidates B L T H M τ C S,
    ∃ f ∈ blockCandidates B L T H M τ C S,
      e ≠ f ∧ blockCandidateRoot e = blockCandidateRoot f

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RootSiteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact categorical law of distinct residue roots at one prime -/

namespace JointDickman
open Finset

noncomputable def rootHitSet {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (r : ZMod p) : Finset ι :=
  I.filter (fun i => root i = r)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BlockPrimeSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite-residue law at every site of a block -/

namespace JointDickman
open Finset

noncomputable def rootHitType {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (r : ZMod p) : I.powerset :=
  ⟨rootHitSet I root r, mem_powerset.mpr (filter_subset _ _)⟩

noncomputable def blockSiteRoot (M p : ℕ) (i : Fin M) : ZMod p :=
  -((i.val+1 : ℕ) : ZMod p)

noncomputable def blockPrimeHit (M p : ℕ) (r : ZMod p) : (univ : Finset (Fin M)).powerset :=
  rootHitType univ (blockSiteRoot M p) r

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RestrictedRootMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual root-hit law on a restricted residue set -/

namespace JointDickman
open Finset PublishedInputs

noncomputable def restrictedRootMass {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p))
    (S : I.powerset) : ℝ :=
  finitePushMass (fun _ : U => 1/(U.card : ℝ)) (fun r => rootHitType I root r.val) S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateModularRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Modular collisions force the explicit integer obstructions -/

namespace JointDickman

noncomputable def candidateModRoot {M : ℕ} (p : ℕ) [Fact p.Prime]
    (e : BlockCandidateIndex M) : ZMod p :=
  (candidateRootNumerator e : ZMod p)/(candidateQuotient e : ZMod p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateDefectPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite set of primes defective for candidate root comparison -/

namespace JointDickman
open Finset

noncomputable def auxiliaryDivisors (B : ℕ) (z : ℤ) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => p ∣ z.natAbs)

open Classical in
noncomputable def candidateDefectPrimes {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) : Finset ℕ :=
  I.biUnion (fun e => auxiliaryDivisors B (candidateQuotient e : ℤ) ∪
    (univ.biUnion (fun s : Fin M => auxiliaryDivisors B (candidateSiteValue e s))) ∪
    (I.biUnion (fun f => if e = f then ∅ else auxiliaryDivisors B (candidateRootDifference e f))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OutsideCandidateMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional candidate-root distribution at an unoccupied prime -/

namespace JointDickman
open Finset

noncomputable def outsideCandidatePrimeMass {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) [Fact p.Prime] (S : I.powerset) : ℝ :=
  restrictedRootMass I (candidateModRoot p) (univ \ univ.image (blockSiteRoot M p)) S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HigherPrimeDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next digit at a coefficient prime remains uniform -/

namespace JointDickman
open Finset Classical

noncomputable def higherDigitRoot (p : ℕ) [Fact p.Prime] (z c : ℤ) : ZMod p :=
  -(z/p : ℤ)/(c : ZMod p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitDecomposition
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prime-square residues split into two uniform digits -/

namespace JointDickman
open Finset

noncomputable def primeDigits (p : ℕ) (x : ZMod (p^2)) : ZMod p × ZMod p :=
  ((x.val : ZMod p), (x.val/p : ZMod p))

noncomputable def joinPrimeDigits (p : ℕ) (x : ZMod p × ZMod p) : ZMod (p^2) :=
  (x.1.val+p*x.2.val : ℕ)

theorem primeDigits_join {p : ℕ} [NeZero p] (x : ZMod p × ZMod p) :
    primeDigits p (joinPrimeDigits p x) = x := by
  have hp : 0 < p := NeZero.pos p
  have hb : x.1.val+p*x.2.val < p^2 := by
    have h1 := x.1.val_lt
    have h2 := x.2.val_lt
    nlinarith
  unfold primeDigits joinPrimeDigits
  rw [ZMod.val_natCast_of_lt hb]
  apply Prod.ext
  · simp
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt x.1.val_lt, zero_add]
    exact ZMod.natCast_zmod_val _

theorem join_primeDigits {p : ℕ} [NeZero p] (x : ZMod (p^2)) :
    joinPrimeDigits p (primeDigits p x) = x := by
  have hp : 0 < p := NeZero.pos p
  have hq : x.val/p < p := (Nat.div_lt_iff_lt_mul hp).mpr (by
    simpa only [pow_two] using x.val_lt)
  unfold joinPrimeDigits primeDigits
  rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hq, Nat.mod_add_div]
  exact ZMod.natCast_zmod_val _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitCRT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square CRT with the first and higher digits kept separate -/

namespace JointDickman
open Finset

noncomputable def primeDigitFamilyEquiv (P : Finset ℕ)
    [∀ p : P, NeZero p.val] :
    (∀ p : P, ZMod (p.val^2)) ≃ ((∀ p : P, ZMod p.val) × (∀ p : P, ZMod p.val)) where
  toFun x := (fun p => (primeDigits p.val (x p)).1, fun p => (primeDigits p.val (x p)).2)
  invFun x := fun p => joinPrimeDigits p.val (x.1 p,x.2 p)
  left_inv x := by funext p; exact join_primeDigits (x p)
  right_inv x := by
    apply Prod.ext <;> funext p
    · exact congrArg Prod.fst (primeDigits_join (x.1 p,x.2 p))
    · exact congrArg Prod.snd (primeDigits_join (x.1 p,x.2 p))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Occupied third-site primes that force an auxiliary root hit -/

namespace JointDickman
open Finset PublishedInputs

def CandidateForcedWitness {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ s : Fin M, s ≠ e.1.1 ∧ s ≠ e.1.2 ∧
    ∃ p ∈ candidateForcedPrimes B e s, p ∈ S s

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteConditionalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite disintegration for coordinate observations -/

namespace JointDickman
open Finset Classical

noncomputable def uniformFiber {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) : Finset Ω := univ.filter (fun x => f x = y)

noncomputable def uniformConditionalMass {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (x : Ω) : ℝ :=
  if f x = y then 1/((uniformFiber f y).card : ℝ) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformResidueFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform conditional residues, including null observation fibers -/

namespace JointDickman
open Finset Classical

/-- Null fibers are assigned a point mass. Their observation mass is zero,
so this makes a probability kernel without changing any joint law. -/
noncomputable def totalUniformConditionalMass {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) : ℝ :=
  if (uniformFiber f y).card = 0 then (if x = default then 1 else 0)
  else uniformConditionalMass f y x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConditionedPrimeResidues
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying conditional residue fibers with the candidate root model -/

namespace JointDickman
open Finset Classical

noncomputable def emptyBlockPrimeHit (M : ℕ) : (univ : Finset (Fin M)).powerset :=
  ⟨∅,by simp⟩

noncomputable def maskedCandidatePrimeHit {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (p : ℕ) [Fact p.Prime]
    (H : (univ : Finset (Fin M)).powerset) (r : ZMod p) : I.powerset :=
  if H = emptyBlockPrimeHit M then rootHitType I (candidateModRoot p) r else
    ⟨∅,by simp⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSiteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic comparison of all arithmetic sites of a finite block -/

namespace JointDickman
open Finset

noncomputable def blockSiteResidues (M : ℕ) (P : Finset ℕ) (n : ℕ) :
    P → (univ : Finset (Fin M)).powerset :=
  fun p => blockPrimeHit M p.val (n : ZMod p.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteTranspose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing independent prime hits as independent endpoint sets -/

namespace JointDickman
open Finset

noncomputable def primeSiteTranspose {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) : (P → I.powerset) ≃ (I → P.powerset) :=
  (Equiv.piCongrRight (fun _ : P => subsetHitEquiv I)).trans
    ((Equiv.piComm (fun (_ : P) (_ : I) => Bool)).trans
      (Equiv.piCongrRight (fun _ : I => (subsetHitEquiv P).symm)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OccupiedPrimeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal mass of occupied primes in independent endpoint sites -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
noncomputable def occupiedPrimeReciprocalMass {M : ℕ} (B : ℕ) (S : Fin M → Finset ℕ) : ℝ :=
  ∑ p ∈ auxiliaryPrimes B, if ∃ i, p ∈ S i then 1/(p : ℝ) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OccupiedRootComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost of setting auxiliary root tests to zero at occupied primes -/

namespace JointDickman
open Finset

open Classical in
noncomputable def siteConditionedRootPrimeMass {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (p : ℕ) [Fact p.Prime] (R : I.powerset) : ℝ :=
  if ∃ i, p ∈ S i then (if R.val = ∅ then 1 else 0) else outsideCandidatePrimeMass I p R

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteConditionedRootProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent prime product after conditioning the endpoint sites -/

namespace JointDickman
open Finset

noncomputable def siteConditionedRootProductMass {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (R : auxiliaryPrimes B → I.powerset) : ℝ :=
  finiteProductMass (fun p : auxiliaryPrimes B => @siteConditionedRootPrimeMass M I S p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩) R

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_MaskedResidueModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conditional law of the masked arithmetic residue model -/

namespace JointDickman
open Finset Classical

abbrev BlockPrimePatterns (B M : ℕ) := auxiliaryPrimes B → (univ : Finset (Fin M)).powerset

noncomputable def primePatternsSites {B M : ℕ} (H : BlockPrimePatterns B M)
    (i : Fin M) : Finset ℕ :=
  (primeSiteTranspose univ (auxiliaryPrimes B) H ⟨i,mem_univ _⟩).val

noncomputable def maskedPrimeRootFamily {B M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (H : BlockPrimePatterns B M)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : auxiliaryPrimes B → I.powerset :=
  fun p => @maskedCandidatePrimeHit M I p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩ (H p) (r p)

noncomputable def arithmeticPrimePatterns (B M u : ℕ) : BlockPrimePatterns B M :=
  fun p => blockPrimeHit M p.val (u : ZMod p.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateCoefficientPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal mass of the exceptional coefficient primes -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCoefficientPrimes {M : ℕ} (B : ℕ)
    (e : BlockCandidateIndex M) : Finset ℕ :=
  auxiliaryDivisors B (candidateLow e : ℤ) ∪
    auxiliaryDivisors B (candidateHigh e : ℤ) ∪
    auxiliaryDivisors B (candidateQuotient e : ℤ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDigitEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional coefficient tests after the endpoint digits are exposed -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def primeDigitMass (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (t : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  finiteProductMass (fun (p : auxiliaryPrimes B) (_ : ZMod p.val) => 1/(p.val : ℝ)) t

noncomputable def coefficientDigitTest {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (r t : ∀ p : auxiliaryPrimes B, ZMod p.val) (p : ℕ) : Prop :=
  if hp : p ∈ auxiliaryPrimes B then
    p ∣ candidateLow e*candidateHigh e ∧
    (p : ℤ)^2 ∣ (candidateQuotient e : ℤ)*
      ((r ⟨p,hp⟩).val+(p : ℤ)*(t ⟨p,hp⟩).val+(e.1.1.val+1))-candidateLow e
  else False

def CoefficientDigitEvent {M : ℕ} (B : ℕ) (I : Finset (BlockCandidateIndex M))
    (r t : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, coefficientDigitTest B e r t p

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticCoefficientHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every arithmetic coefficient-prime hit is a controlled digit event -/

namespace JointDickman
open Finset Classical

def ArithmeticCoefficientHit {M : ℕ} (B : ℕ) (I : Finset (BlockCandidateIndex M))
    (m : BlockCandidateIndex M → ℕ) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, p ∣ m e

noncomputable def arithmeticFirstDigits (B u : ℕ) : ∀ p : auxiliaryPrimes B, ZMod p.val :=
  fun p => (primeDigits p.val (u : ZMod (p.val^2))).1

noncomputable def arithmeticSecondDigits (B u : ℕ) : ∀ p : auxiliaryPrimes B, ZMod p.val :=
  fun p => (primeDigits p.val (u : ZMod (p.val^2))).2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TrimmedCandidateRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic identification after removing coefficient tests -/

namespace JointDickman
open Finset Classical

noncomputable def arithmeticCandidateHit {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) (m : BlockCandidateIndex M → ℕ) : I.powerset :=
  ⟨I.filter (fun e => p ∣ m e),mem_powerset.mpr (filter_subset _ _)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_MaskedCoefficientErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring coefficient-prime tests in the masked comparison model -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def conditionalResidueMass {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val] (H : BlockPrimePatterns B M)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  finiteProductMass (fun p : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M p.val) (H p)) r

noncomputable def maskedCoefficientTest {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (H : BlockPrimePatterns B M) (e : BlockCandidateIndex M) (p : ℕ)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  if hp : p ∈ auxiliaryPrimes B then
    e ∈ (@maskedCandidatePrimeHit M I p ⟨auxiliaryPrimes_prime B p hp⟩ (H ⟨p,hp⟩) (r ⟨p,hp⟩)).val
  else False

def MaskedCoefficientEvent {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (H : BlockPrimePatterns B M) (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, maskedCoefficientTest I H e p r

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticRootIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic root families agree outside the explicit exceptional events -/

namespace JointDickman
open Finset Classical

noncomputable def arithmeticCandidatePrimeFamily {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ) :
    auxiliaryPrimes B → I.powerset := fun p => arithmeticCandidateHit I p.val m

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSquareHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing all site squares in a block, after taking digit averages -/

namespace JointDickman
open Finset PublishedInputs Classical

def BlockSquareHit (B M u : ℕ) : Prop :=
  ∃ i : Fin M, ∃ p ∈ auxiliaryPrimes B, p^2 ∣ u+(i.val+1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticCandidateWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six arithmetic graph factors are the candidate root weight -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCutoff {M : ℕ} (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  w (candidateQuotient e)*v (candidateHigh e) (candidateQuotient e)*
    v (candidateLow e) (candidateQuotient e)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgeMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-root majorant for the actual arithmetic edge weights -/

namespace JointDickman
open Finset

noncomputable def graphGoodPrimes (B a b c : ℕ) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => ¬p ∣ a ∧ ¬p ∣ b ∧ ¬p ∣ c)

noncomputable def graphResidueEnvelope (B a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  (auxiliaryRatio B^(1/2 : ℝ))^3 * ∏ p ∈ graphGoodPrimes B a b c,
    residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
    residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
    residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEndpointDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact density of the endpoint congruences and retained roots -/

namespace JointDickman
open Finset

noncomputable def graphEndpointResidue (a b : ℕ) (j : ℤ) (hab : a.Coprime b) :
    ZMod (a*b) :=
  (ZMod.chineseRemainder hab).symm (-(j : ZMod a), 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgePeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The periodic majorant of a fixed arithmetic graph representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def graphEdgeEnvelope (B a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  if b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j then graphResidueEnvelope B a b c j n else 0

noncomputable def graphEdgePeriod (B a b c : ℕ) : ℕ :=
  a*b*∏ p ∈ graphGoodPrimes B a b c, p

noncomputable def graphEdgeMean (B a b c : ℕ) : ℝ :=
  (auxiliaryRatio B^(1/2 : ℝ))^3 *
    ((1/((a : ℝ)*b)) * ∏ p ∈ graphGoodPrimes B a b c, (1-3/(2*(p : ℝ))))

theorem graphEdgePeriod_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (B c : ℕ) :
    0 < graphEdgePeriod B a b c := by
  unfold graphEdgePeriod
  exact Nat.mul_pos (Nat.mul_pos ha hb)
    (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_filter.mp hp).1).pos))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the harmonic coefficient mass for a fixed positive lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def graphCoefficientHarmonicTerm (B j : ℕ) (bc : ℕ × ℕ) : ℝ :=
  (coefficientWeight B bc.1 * coefficientWeight B bc.2 *
    coefficientWeight B (bc.1+j*bc.2)) / ((bc.1 : ℝ)*(bc.1+j*bc.2))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph coefficient triples have no multiplicity at a fixed lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def graphTriplePair (i : GraphCoefficientTriple) : ℕ × ℕ :=
  (∏ p ∈ i.2.2, p, ∏ p ∈ i.1, p)

open Classical in
noncomputable def supportedGraphTriples (B T : ℕ) (j : ℤ) : Finset GraphCoefficientTriple :=
  (arithmeticGraphTriples B T).filter (fun i => graphTripleLag i = j ∧
    (∏ p ∈ i.2.1, p, ∏ p ∈ i.1, p) ∈ amplificationCoefficientPairs B T ∧
    graphTriplePair i ∈ amplificationCoefficientPairs B T)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphTripleSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only supported coprime coefficient triples contribute to a lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def coprimeGraphTriples (B T : ℕ) (j : ℤ) : Finset GraphCoefficientTriple :=
  (supportedGraphTriples B T j).filter fun i =>
    (∏ p ∈ i.2.1, p).Coprime (∏ p ∈ i.1, p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateGraphEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding endpoint candidates as the original graph's coefficient triples -/

namespace JointDickman
open Finset Classical

noncomputable def candidateGraphTriple {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M) :
    GraphCoefficientTriple := (coefficientPrimeSet B (candidateQuotient e),e.2.2,e.2.1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphCandidateDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering endpoint candidates from nonzero arithmetic graph terms -/

namespace JointDickman
open Finset Classical

noncomputable def graphBlockCandidate {M : ℕ} (i k : Fin M)
    (g : GraphCoefficientTriple) : BlockCandidateIndex M := ((i,k),(g.2.2,g.2.1))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticCandidateSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reindexing of the arithmetic graph by its endpoint candidates -/

namespace JointDickman
open Finset Classical

noncomputable def arithmeticCandidateWeight (B L T : ℕ) (τ C : ℝ)
    {M : ℕ} (u : ℕ) (e : BlockCandidateIndex M) : ℝ :=
  candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
    (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) e
    (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
      (candidateQuotient e) (u+(e.1.1.val+1))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticCandidateKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original candidate weights and the masked residue kernel -/

namespace JointDickman
open Finset Classical

noncomputable def candidateArithmeticQuotient {M : ℕ} (u : ℕ)
    (e : BlockCandidateIndex M) : ℕ :=
  divisorEdgeInverse (candidateHigh e) (candidateLow e) (candidateQuotient e)
    (u+(e.1.1.val+1))

noncomputable def actualCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) : Fin M → Fin M → ℝ :=
  let I := blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
  independentCandidateKernel B L T H M τ C
    (fun i => coefficientPrimeSet B (u+(i.val+1))) χ
    (primeSiteTranspose I (auxiliaryPrimes B)
      (arithmeticCandidatePrimeFamily B I (candidateArithmeticQuotient u)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the adaptive coefficient exceptions over prime digits -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def residuePrimePatterns {B M : ℕ}
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : BlockPrimePatterns B M :=
  fun p => blockPrimeHit M p.val (r p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticCoefficientProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient exceptions for the actual arithmetic candidate family -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def arithmeticSquareMean (B : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ u ∈ range (∏ p ∈ auxiliaryPrimes B, p^2), f u)/
    (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2)

noncomputable def residueCandidates (B L T H M : ℕ) (τ C : ℝ)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Finset (BlockCandidateIndex M) :=
  blockCandidates B L T H M τ C (primePatternsSites (residuePrimePatterns r))

def ActualCoefficientException (B L T H M : ℕ) (τ C : ℝ) (u : ℕ) : Prop :=
  ArithmeticCoefficientHit B
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (candidateArithmeticQuotient u)

def MaskedCoefficientException (B L T H M : ℕ) (τ C : ℝ) (u : ℕ) : Prop :=
  MaskedCoefficientEvent
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockPatternTranspose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transposing all block-prime patterns to their endpoint types -/

namespace JointDickman
open Finset Classical PublishedInputs

noncomputable def univPiEquiv (α β : Type*) [Fintype α] :
    (↥(univ : Finset α) → β) ≃ (α → β) where
  toFun f a := f ⟨a,mem_univ a⟩
  invFun f a := f a.val
  left_inv f := by funext a; rfl
  right_inv f := rfl

noncomputable def blockPatternEquiv (B M : ℕ) :
    BlockPrimePatterns B M ≃ (Fin M → (auxiliaryPrimes B).powerset) :=
  (primeSiteTranspose (univ : Finset (Fin M)) (auxiliaryPrimes B)).trans
    (univPiEquiv (Fin M) ((auxiliaryPrimes B).powerset))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional forced-hit bound over an exposed endpoint pair -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

def PairForcedEvent (B L T H M : ℕ) (τ C : ℝ) (i k : Fin M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ ab ∈ pairSplitChoices B L τ C (S i) (S k),
    BlockCandidateAdmissible B L T H τ C ((i,k),ab) ∧
    CandidateForcedWitness B ((i,k),ab) S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forced occupied-prime hits in the actual random candidate list -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

def ForcedCandidateHit (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ e ∈ blockCandidates B L T H M τ C S, CandidateForcedWitness B e S

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRootMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded scalar root mean in the latent kernel -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

noncomputable def independentRootMean (B L : ℕ) (τ C : ℝ) : ℝ :=
  finiteExpectation (independentPrimeSetMass B)
    (fun R => regularResidueWeight B L τ C R.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FormIntervalSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval sieve for individually weighted forms

Roots may coincide. The Euler factor is the exact residue average of all
local form weights, rather than a product that assumes distinct roots.
-/

namespace JointDickman

open Finset

/-- The product of the weights of all forms vanishing at a residue. -/
noncomputable def formRootWeight {k p : ℕ}
    (root : Fin k → ZMod p) (θ : Fin k → ℝ) (r : ZMod p) : ℝ :=
  ∏ i ∈ univ.filter (fun i => root i = r), θ i

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_GoodPrimeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler product after removing primes dividing j and b -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def goodSievePrimes (Z j b : ℕ) : Finset ℕ :=
  (sievePrimes Z).filter (fun p => ¬p ∣ j ∧ ¬p ∣ b)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointCoefficientMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The half-prime coefficient mass at a fixed first endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointCoefficientMass (B b j q : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
    primeProductMass (auxiliaryPrimes B) (1/2) (b+j*c)*coefficientWeight B c else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointCoefficientTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pushing the second endpoint's fair split onto its coefficient -/

namespace JointDickman
open Finset

open Classical in
noncomputable def endpointCoefficientTest (B b j q a : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if a = b+j*c ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
    then coefficientWeight B c else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointRowScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coefficient box chosen from the fixed endpoint alone -/

namespace JointDickman
open Finset

noncomputable def endpointRowScale (T b : ℕ) : ℕ := ⌈(b : ℝ)/(2*T)⌉₊

def EndpointCoefficientWindow (B T b : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B ∧
    T*c ≤ b ∧ b ≤ 2*T*c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointConditionalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mean at one independently averaged endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def supportedEndpointTest (B T b j a : ℕ) : ℝ :=
  if EndpointCoefficientWindow B T b then
    endpointCoefficientTest B b j (endpointRowScale T b) a else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointRowEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform row means for the coefficient majorant -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def endpointSplitWeight (B L : ℕ) (τ C : ℝ) (S A : Finset ℕ) : ℝ :=
  regularCoefficientWeight B L τ C (∏ p ∈ A, p)*regularResidueWeight B L τ C (S \ A)

noncomputable def endpointRowEnvelope (B L T j : ℕ) (τ C : ℝ) (S R : Finset ℕ) : ℝ :=
  independentRootMean B L τ C/(B : ℝ)*
    ∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A*
      ∑ D ∈ endpointSplits B L τ C R, endpointSplitWeight B L τ C R D*
        supportedEndpointTest B T (∏ p ∈ A, p) j (∏ p ∈ D, p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AveragedRootFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent-root fluctuation vanishes after averaging endpoint types -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

noncomputable def averagedIndependentRootError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) : ℝ :=
  finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) (fun S =>
    finiteExpectation (siteProductMass
      (fun _ : blockCandidates B L T H M τ C (fun i => (S i).val) => independentPrimeSetMass B))
      (fun R => kernelCutNorm (fun i k =>
        independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ R i k-
          latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionedRootErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditioned root-model error survives the polynomial weight bound -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def conditionedRootError (B : ℕ) : ℝ :=
  214*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+2*(B : ℝ)^8/Real.exp B

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionedRootFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The site-conditioned auxiliary roots have vanishing fluctuations -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

noncomputable def averagedConditionedRootError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) : ℝ :=
  finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) (fun S =>
    finiteExpectation
      (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (fun i => (S i).val))
        (fun i => (S i).val))
      (fun R => kernelCutNorm (fun i k =>
        independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ
          (primeSiteTranspose (blockCandidates B L T H M τ C (fun i => (S i).val)) (auxiliaryPrimes B) R) i k-
        latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MaskedArithmeticFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The masked arithmetic CRT kernel inherits the root fluctuation bound -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

noncomputable def patternRootCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : BlockPrimePatterns B M)
    (R : auxiliaryPrimes B → (blockCandidates B L T H M τ C (primePatternsSites S)).powerset) : ℝ :=
  kernelCutNorm (fun i k => independentCandidateKernel B L T H M τ C (primePatternsSites S) χ
      (primeSiteTranspose _ (auxiliaryPrimes B) R) i k-
    latentCandidateKernel B L T H M τ C (primePatternsSites S) χ i k)

noncomputable def patternRootMean (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : BlockPrimePatterns B M) : ℝ :=
  finiteExpectation
    (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (primePatternsSites S))
      (primePatternsSites S)) (patternRootCutError B L T H M τ C χ S)

noncomputable def maskedDigitCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  patternRootCutError B L T H M τ C χ (residuePrimePatterns r)
    (maskedPrimeRootFamily (blockCandidates B L T H M τ C (primePatternsSites (residuePrimePatterns r)))
      (residuePrimePatterns r) r)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualArithmeticFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the root-identification exceptions from the arithmetic kernel -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

noncomputable def actualCandidateCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) : ℝ :=
  kernelCutNorm (fun i k => actualCandidateKernel B L T H M τ C χ u i k-
    latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ i k)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient-prime exclusions survive the graph's polynomial weight cap -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def coefficientRootError (B : ℕ) : ℝ :=
  72*(B : ℝ)^17/(auxiliaryCutoff B : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualArithmeticLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the arithmetic candidate root fluctuations -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def arithmeticFluctuationError (K : ℝ) (B : ℕ) : ℝ :=
  K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+
    coefficientRootError B+10*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+4/(B : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_NumericPrefixHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic sieve at the actual large-addition prefix cutoff -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def numericAdditionSieveCutoff (B : ℕ) (g : ℝ) : ℕ :=
  ⌊Real.exp ((B : ℝ)^g)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual coefficient primes in the addition sieve -/

namespace JointDickman
open Finset Classical

noncomputable def additionExcludedPrimes (B e b : ℕ) : Finset ℕ :=
  (e*b).primeFactors ∩ auxiliaryPrimes B

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionProgressionInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common interval for additions in a factor-four size window -/

namespace JointDickman
open Finset Classical

noncomputable def additionIntervalLower (W : ℝ) (j : ℕ) : ℕ := ⌊W/j⌋₊
noncomputable def additionIntervalUpper (W : ℝ) (j : ℕ) : ℕ := ⌊4*W/j⌋₊+1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicityRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entropy and Poisson exponents in representation multiplicity -/

namespace JointDickman

noncomputable def halfPoissonRate (u : ℝ) : ℝ := 1/2-u+u*Real.log (2*u)
noncomputable def halfRankinExponent (r : ℝ) : ℝ := r*(1+Real.log ((1/2)/r))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NumericAdditionClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing a class of actual numeric additions

A class fixes the retained coefficient, the opposite coefficient, the lag,
the number of added primes, and a factor-four product window.  The alternative
quotient remains regular.  Its weighted sum is reduced to one progression.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def numericAdditionClass (B L : ℕ) (τ C : ℝ)
    (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (auxiliaryPrimes B).powerset.filter (fun Z => Z.card = d ∧
    W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
    ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p) = b+j*c ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c))

noncomputable def additionProgressionWeight (B : ℕ) (g : ℝ)
    (e j b z₀ : ℕ) (c₀ : ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
    residueWeight q 0 ((z₀ : ZMod p)+j*n)*residueWeight (1/2) 0 ((c₀ : ZMod p)+e*n))/
      ((z₀ : ℝ)+(j : ℝ)*n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeNumericAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's large numeric-addition harmonic estimate -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def largeAdditionExponent (g Δ δ τ ε ℓ : ℝ) (d : ℕ) : ℝ :=
  g*(halfRankinExponent (min ((d : ℝ)/(g*ℓ)) (1/2))-1-weightBaseExponent)+
    3*Δ+δ+τ*Real.log 2+ε

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedRemainderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact measure obtained by weighting the first representation

After requiring a coefficient and weighting the remaining primes by one
half, the unforced indicators have probability 1/(2p-1). Regularity tests
remain inside the expectation and do not alter its normalization.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def remainderTiltNormalizer (B : ℕ) (A : Finset ℕ) : ℝ :=
  auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B \ A) (1/2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TiltedAdditionRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-addition availability estimate from Mertens -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def clippedAdditionDensity (B : ℕ) (g : ℝ) (Z : Finset ℕ) : ℝ :=
  min ((Z.card : ℝ)/(g*auxiliaryLogLength B)) (1/2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAdditionAvailability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expected large additions with first-remainder regularity retained -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def availableNumericAdditionClass (B L k : ℕ) (τ C : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (numericAdditionClass B L τ C e j b d W).filter (fun Z =>
    Z ⊆ auxiliaryPrimes B \ A ∧
    (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
    Z ⊆ primePrefix B ((k : ℝ)/L) Z)

noncomputable def largeAvailabilityExponent (g Δ δ τ ε ℓ : ℝ) (d : ℕ) : ℝ :=
  g*((1/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))-1-weightBaseExponent)+
    3*Δ+(1+g)*δ+(Real.log 2-Real.log (2*δ))*τ+2*ε

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeHighClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active high-addition classes at the actual coefficient ratio -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def highAdditionWindow (e b : ℕ) : ℝ := (b : ℝ)/(2*(e : ℝ))

noncomputable def activeHighAdditionClass (B L k : ℕ) (τ C Δ : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) : Finset (Finset ℕ) :=
  if (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b then
    availableNumericAdditionClass B L k τ C A e j b d (highAdditionWindow e b)
  else ∅

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding regular alternatives with small additions -/

namespace JointDickman
open Finset Classical

noncomputable def regularSmallAlternatives (B L k : ℕ) (τ C : ℝ)
    (A R : Finset ℕ) : Finset (Finset ℕ) :=
  (A ∪ R).powerset.filter (fun X => RegularPrimeSet B L τ C X ∧
    X \ A ⊆ primePrefix B ((k : ℝ)/L) (X \ A))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SmallAdditionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-addition contribution to representation multiplicity -/

namespace JointDickman
open Finset Classical Filter
open scoped Topology

noncomputable def highOmissionExponent (τ : ℝ) : ℝ :=
  (1/2+τ)*Real.binEntropy (4*τ/(1/2+τ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OmissionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An omission envelope independent of the random remainder -/

namespace JointDickman
open Finset Classical

/-- The old-prime choices can be enumerated before drawing the other
remainder.  This is essential when applying the inclusion bound to a fixed
numeric addition. -/
noncomputable def omissionEnvelope (B L k : ℕ) (τ : ℝ) (A : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  A.powerset.filter (fun O =>
    |((O ∩ Q).card : ℝ)/auxiliaryLogLength B-((k : ℝ)/L)*r| ≤ 3*τ ∧
      ((O \ Q).card : ℝ) ≤ 4*τ*auxiliaryLogLength B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularPrefixChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting prescribed-size additions inside a regular remainder -/

namespace JointDickman
open Finset Classical

noncomputable def regularPrefixChoices (B L k : ℕ) (R : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  (primePrefix B ((k : ℝ)/L) R).powerset.filter (fun Y => Y.card = d)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAlternativePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual alternative coefficient pairs in a large-addition class -/

namespace JointDickman
open Finset Classical

noncomputable def largeHighAlternativePairs (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      (XY.1 \ A).card = d ∧ (XY.2 \ D).card = f ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.1, p : ℕ) ≤ 2*(∏ p ∈ XY.2, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p) = (∏ p ∈ XY.2, p)+j*c ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeCardinalityPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning all large high-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

noncomputable def allLargeHighAlternativePairs (B L k j : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.1, p : ℕ) ≤ 2*(∏ p ∈ XY.2, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p) = (∏ p ∈ XY.2, p)+j*c ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeMultiplicityExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The combined entropy exponent in large representation classes -/

namespace JointDickman

noncomputable def largeMultiplicityBase : ℝ := 2*Real.log 2-1-weightBaseExponent

noncomputable def largeMultiplicityLoss (Δ δ τ ε : ℝ) : ℝ :=
  3*Δ+2*δ+(Real.log 2-Real.log (2*δ))*τ+5*ε+2*highOmissionExponent τ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ReverseCoefficientMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic coefficient mass with the upper endpoint fixed -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def reverseCoefficientMass (B T b j q : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if T*q ≤ b-j*c ∧ (b-j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
    primeProductMass (auxiliaryPrimes B) (1/2) (b-j*c)*coefficientWeight B c else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReverseEndpointTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the lower endpoint while the upper coefficient is fixed -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def reverseCoefficientTest (B T b j q a : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if a = b-j*c ∧ T*q ≤ a ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
    then coefficientWeight B c else 0

noncomputable def reverseSupportedTest (B T b j a : ℕ) : ℝ :=
  if EndpointCoefficientWindow B T b then
    reverseCoefficientTest B T b j (endpointRowScale T b) a else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReverseRowEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional envelope for the lower endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def reverseEndpointRowEnvelope (B L T j : ℕ) (τ C : ℝ) (S R : Finset ℕ) : ℝ :=
  independentRootMean B L τ C/(B : ℝ)*
    ∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A*
      ∑ D ∈ endpointSplits B L τ C R, endpointSplitWeight B L τ C R D*
        reverseSupportedTest B T (∏ p ∈ A, p) j (∏ p ∈ D, p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSiteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The latent graph as a kernel of its two endpoint types -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidateSiteKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ) : ℝ :=
  latentCandidateKernel B L T H M τ C (Function.update (fun _ => a) k b) χ i k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping representation multiplicity in the latent second moment -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidatePairRepresentations (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i k : Fin M) (S R : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((endpointSplits B L τ C S).product (endpointSplits B L τ C R)).filter
    (fun ab => BlockCandidateAdmissible B L T H τ C ((i,k),ab))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeHighVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing contribution of each large high-endpoint class -/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def largeClassError (K η ν : ℝ) (B : ℕ) : ℝ :=
  (K/η)*(Real.log B+1)^3/(B : ℝ)^((32/100 : ℝ)-ν)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AllLargeHighVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing every cardinality class of a large high-endpoint addition -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def allLargeClassError (K η ν : ℝ) (B : ℕ) : ℝ :=
  (K/η)*(Real.log B+1)^5/(B : ℝ)^((32/100 : ℝ)-ν)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

noncomputable def additivePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def oscillatoryTest (w : ℝ → ℝ) (ξ : ℝ) (t : ℝ) : ℂ :=
  (w t : ℂ) * additivePhase (ξ * t)

noncomputable def oscillatoryTestDeriv (w w' : ℝ → ℝ) (ξ : ℝ) (t : ℝ) : ℂ :=
  (w' t : ℂ) * additivePhase (ξ * t) +
    (w t : ℂ) * (additivePhase (ξ * t) * ((2 * Real.pi : ℝ) * Complex.I) * ξ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

noncomputable def finiteAdditiveSum (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, c n*additivePhase ((n : ℝ)*θ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughMeanNormalization (B : ℕ) (z : ℝ) : ℝ :=
  Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 - z)

noncomputable def roughMeanProfile (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ range (H + 1), scaledRoughCoefficient c z j B * s ^ (z - 1 - j)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedSplitProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def splitProductMass (P S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ A ∈ P.powerset, subsetRetentionMass S A*(if (∏ p ∈ A, p) = n then 1 else 0)

noncomputable def signedSplitProductMass (P : Finset ℕ) (g : Finset ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S *
    splitProductMass P S n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second Fourier bounds for signed endpoint masses -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def endpointFourierSum (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) (θ : ℝ) : ℂ :=
  finiteAdditiveSum (Ioc ⌊a*X⌋₊ ⌊b*X⌋₊)
    (fun n => (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X) : ℝ)) θ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueFourierParseval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact unit-residue Parseval identity for the fine histograms -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

noncomputable def unitResidueFourier {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) (h : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (h*(r : ZMod q))*v r

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RamanujanDivisorFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exact divisor formula for all Ramanujan frequencies -/

namespace JointDickman
open Finset
open scoped ArithmeticFunction.Moebius

noncomputable def ramanujanSum (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (h*(r : ZMod q))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanMultiplicative
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicativity of the Ramanujan factor in its modulus -/

namespace JointDickman
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def divisorIndicatorWeight (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∣ k then (n : ℂ) else 0, by simp⟩

noncomputable def ramanujanArithmetic (k : ℕ) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ)*divisorIndicatorWeight k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReducedArcLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact enumeration of the lifts of reduced coefficient arcs -/

namespace JointDickman
open Finset

noncomputable def arcLiftEquiv (j q : ℕ) [NeZero (j*q)] :
    Fin j × Fin q ≃ ZMod (j*q) :=
  finProdFinEquiv.trans (ZMod.finEquiv (j*q)).toEquiv

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalUnitRepresentatives
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced rational representatives modulo the integer period -/

namespace JointDickman

theorem isUnit_intCast_of_natAbs_coprime {q : ℕ} (n : ℤ) (hn : n.natAbs.Coprime q) :
    IsUnit (n : ZMod q) := by
  have hunit := (ZMod.unitOfCoprime n.natAbs hn).isUnit
  rw [ZMod.coe_unitOfCoprime] at hunit
  by_cases hsign : 0 ≤ n
  · have he : (n.natAbs : ZMod q) = (n : ZMod q) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hsign]
    rwa [he] at hunit
  · have he : (n.natAbs : ZMod q) = -(n : ZMod q) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hsign),Int.cast_neg]
    rw [he] at hunit
    simpa only [neg_neg] using hunit.neg

theorem rational_eq_unit_fraction_add_int (r : ℚ) :
    let : NeZero r.den := ⟨r.pos.ne'⟩
    ∃ (u : (ZMod r.den)ˣ) (k : ℤ),
      (r : ℝ) = ((u : ZMod r.den).val : ℝ)/r.den+k := by
  let : NeZero r.den := ⟨r.pos.ne'⟩
  obtain ⟨u,hu⟩ := isUnit_intCast_of_natAbs_coprime r.num r.reduced
  have he : (((u : ZMod r.den).val : ℕ) : ZMod r.den) = (r.num : ZMod r.den) := by
    rw [ZMod.natCast_zmod_val,hu]
  have hd : (r.den : ℤ) ∣ r.num-((u : ZMod r.den).val : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
    simpa only [Int.cast_natCast] using he
  obtain ⟨k,hk⟩ := hd
  refine ⟨u,k,?_⟩
  have hr : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hk' : (r.num : ℝ)-((u : ZMod r.den).val : ℝ) = (r.den : ℝ)*k := by
    exact_mod_cast hk
  rw [Rat.cast_def]
  apply (div_eq_iff hr).mpr
  field_simp
  nlinarith

theorem unit_fraction_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    (((u : ZMod q).val : ℚ)/q).den = q := by
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hc : (((u : ZMod q).val : ℤ).natAbs).Coprime ((q : ℤ).natAbs) := by
    simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime u
  have h := Rat.den_div_eq_of_coprime hq hc
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast] using h

theorem unit_fraction_add_int_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (k : ℤ) :
    ((((u : ZMod q).val : ℚ)/q)+(k : ℚ)).den = q := by
  rw [Rat.add_intCast_den,unit_fraction_den]

theorem unit_fraction_add_int_injective {q : ℕ} [NeZero q]
    (u v : (ZMod q)ˣ) (k l : ℤ)
    (he : ((u : ZMod q).val : ℝ)/q+k = ((v : ZMod q).val : ℝ)/q+l) :
    u = v ∧ k = l := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hu : 0 ≤ ((u : ZMod q).val : ℝ)/q := by positivity
  have hv : 0 ≤ ((v : ZMod q).val : ℝ)/q := by positivity
  have hu1 : ((u : ZMod q).val : ℝ)/q < 1 :=
    (div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt (u : ZMod q))
  have hv1 : ((v : ZMod q).val : ℝ)/q < 1 :=
    (div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt (v : ZMod q))
  have hkl : k < l+1 := by
    exact_mod_cast (show (k : ℝ) < (l : ℝ)+1 by linarith)
  have hlk : l < k+1 := by
    exact_mod_cast (show (l : ℝ) < (k : ℝ)+1 by linarith)
  have hkeq : k = l := by omega
  refine ⟨?_,hkeq⟩
  apply Units.val_injective
  apply ZMod.val_injective
  have he' : ((u : ZMod q).val : ℝ)/q = ((v : ZMod q).val : ℝ)/q := by
    rw [hkeq] at he
    linarith
  have hv' := (div_left_inj' hq.ne').mp he'
  exact_mod_cast hv'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReducedRationalEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing rational arcs by denominator, unit residue and integer translate -/

namespace JointDickman

abbrev ReducedRationalData := Σ q : ℕ+, (ZMod (q : ℕ))ˣ × ℤ

noncomputable def reducedRationalValue (d : ReducedRationalData) : ℚ :=
  (((d.2.1 : ZMod (d.1 : ℕ)).val : ℚ)/(d.1 : ℕ))+(d.2.2 : ℚ)

theorem reducedRationalValue_den (d : ReducedRationalData) :
    (reducedRationalValue d).den = (d.1 : ℕ) :=
  unit_fraction_add_int_den d.2.1 d.2.2

theorem reducedRationalValue_injective : Function.Injective reducedRationalValue := by
  rintro ⟨q,⟨u,k⟩⟩ ⟨q',⟨v,l⟩⟩ he
  have hq : q = q' := by
    apply Subtype.ext
    have h := congrArg Rat.den he
    rw [reducedRationalValue_den,reducedRationalValue_den] at h
    exact h
  subst q'
  have he' : ((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+k =
      ((v : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+l := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) he
    simpa only [reducedRationalValue,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] using h
  obtain ⟨hu,hk⟩ := unit_fraction_add_int_injective u v k l he'
  subst v
  subst l
  rfl

theorem reducedRationalValue_surjective : Function.Surjective reducedRationalValue := by
  intro r
  obtain ⟨u,k,he⟩ := rational_eq_unit_fraction_add_int r
  refine ⟨⟨⟨r.den,r.pos⟩,⟨u,k⟩⟩,?_⟩
  change (((u : ZMod r.den).val : ℚ)/r.den)+(k : ℚ) = r
  apply (Rat.cast_injective (α := ℝ))
  simpa only [reducedRationalValue,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast]
    using he.symm

noncomputable def reducedRationalEquiv : ReducedRationalData ≃ ℚ :=
  Equiv.ofBijective reducedRationalValue
    ⟨reducedRationalValue_injective,reducedRationalValue_surjective⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LiftedRationalEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational arcs indexed by their finite lifts and period translates -/

namespace JointDickman

abbrev LiftedRationalData (j : ℕ) :=
  Σ q : ℕ+, (ZMod (q : ℕ))ˣ × (Fin j × ℤ)

noncomputable def liftedRationalEquiv (j : ℕ) [NeZero j] :
    LiftedRationalData j ≃ ℚ :=
  (Equiv.sigmaCongrRight (fun q : ℕ+ =>
    Equiv.prodCongr (Equiv.refl (ZMod (q : ℕ))ˣ)
      ((Equiv.prodComm (Fin j) ℤ).trans
        ((Equiv.prodCongr (Equiv.neg ℤ) (Equiv.refl (Fin j))).trans
          (Int.divModEquiv j).symm)))).trans
    (reducedRationalEquiv.trans (Equiv.neg ℚ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_OscillatoryCoefficientLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (1): the oscillatory coefficient law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

noncomputable def coefficientExponentialSum (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ, (coefficientWeight B n : ℂ) * (w (n / X) : ℂ) *
    additivePhase (((u : ZMod q).val : ℝ) * n / q + ξ * n / X)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientPartialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive partial sums of the actual rough coefficient -/

namespace JointDickman
open Finset

noncomputable def coefficientAdditivePartialSum (B Y : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 Y, (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MinorArcApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced rational approximation outside the major arcs -/

namespace JointDickman

/-- Real representatives of the rational arcs; translating a numerator by
an integer retains the corresponding arc on the unit circle. -/
def InRationalArc (θ Q δ : ℝ) : Prop :=
  ∃ r : ℚ, (r.den : ℝ) ≤ Q ∧ |θ-(r : ℝ)| ≤ δ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCoefficientMinorArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth minor-arc bound for the actual coefficient, equation (36) -/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def smoothCoefficientAdditiveSum (B : ℕ) (X θ : ℝ) (w : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ, (coefficientWeight B n : ℂ)*(w (n/X) : ℂ)*additivePhase ((n : ℝ)*θ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MinorArcMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable discarded minor-arc region -/

namespace JointDickman

noncomputable def minorArcRegion (B j : ℕ) (X : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioc 0 1 ∧ ¬ InRationalArc (-(j : ℝ)*θ) ((B : ℝ)^12) ((B : ℝ)^13/X)}

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MajorArcPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable major-arc partition of the exact Fourier integral -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

noncomputable def majorArcRegion (B j : ℕ) (X : ℝ) : Set ℝ :=
  {θ | θ ∈ Ioc 0 1 ∧ InRationalArc (-(j : ℝ)*θ) ((B : ℝ)^12) ((B : ℝ)^13/X)}

noncomputable def rationalArcPiece (B j : ℕ) (X : ℝ) (r : ℚ) : Set ℝ :=
  {θ | θ ∈ Ioc 0 1 ∧ (r.den : ℝ) ≤ (B : ℝ)^12 ∧
    |-(j : ℝ)*θ-(r : ℝ)| ≤ (B : ℝ)^13/X}

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicWindowIntegral
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unfolding a compact window across the integer period -/

namespace JointDickman
open MeasureTheory Set

noncomputable def integerLatticeEquiv : ℤ ≃ AddSubgroup.zmultiples (1 : ℝ) :=
  Equiv.ofBijective (fun k => ⟨(k : ℝ),by
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k,by simp⟩⟩) (by
      constructor
      · intro k l h
        have he := congrArg Subtype.val h
        change (k : ℝ) = (l : ℝ) at he
        exact_mod_cast he
      · intro x
        obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
        refine ⟨k,Subtype.ext ?_⟩
        simpa only [zsmul_eq_mul,mul_one] using hk)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MajorArcFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite major-arc identity for the actual Fourier integrand -/

namespace JointDickman
open Filter MeasureTheory Set Function Finset
open scoped Topology

def positiveDenominators (N : ℕ) : Finset ℕ+ :=
  (range (N+1)).subtype (fun n => 0 < n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SmallMajorCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published coefficient expansion on the actual lifted arcs -/

namespace JointDickman
open Filter MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

noncomputable def coefficientFourierTransform (c : ℕ → ℝ) (H B : ℕ)
    (X : ℝ) (w : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*
    additivePhase (-ξ*s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProfileFreeze
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing the slowly varying coefficient density inside one box -/

namespace JointDickman
open MeasureTheory Filter

noncomputable def testFourierTransform (w : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (w s : ℂ)*additivePhase (-ξ*s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TruncatedMajorRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting the major arcs at a finite denominator -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

noncomputable def smallMajorArcRegion (B j : ℕ) (X : ℝ) (Q : ℕ) : Set ℝ :=
  ⋃ r : ℚ, if r.den ≤ Q then rationalArcPiece B j X r else ∅

noncomputable def largeMajorArcRegion (B j : ℕ) (X : ℝ) (Q : ℕ) : Set ℝ :=
  majorArcRegion B j X \ smallMajorArcRegion B j X Q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FullSmallArcModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained arc model with its full Fourier integral -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

noncomputable def fullSmallMajorArcModel (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ)
    (F W : ℝ → ℂ) (a : ℕ+ → ℂ) : ℂ :=
  (1/(j : ℂ))*∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
    ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*
      ∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ
    else 0 else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughResidueHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation in the unit residue classes -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughResidueWeight {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  if (n : ZMod q) = r then roughSquarefreeWeight E z n else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueCentering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centering finite channels in the residue coordinate

All residues above the same base cell carry the same atom weight. Thus
subtracting the residue average of the transition subtracts exactly the
residue average of the channel. The corresponding two-split kernel is
centered in both coordinates. A residue-independent approximation cancels,
at a loss of at most four in its uniform error.
-/

namespace JointDickman

open scoped BigOperators

noncomputable def finiteResidueAverage {R : Type*} [Fintype R] (f : R → ℝ) : ℝ :=
  (∑ r, f r) / Fintype.card R

/-- Subtract the uniform residue average within each base cell. -/
noncomputable def residueCenteredTransition {Ω D R : Type*} [Fintype R]
    (p : Ω → D × R → ℝ) (s : Ω) (a : D × R) : ℝ :=
  p s a - finiteResidueAverage (fun t => p s (a.1, t))

/-- Center a kernel in both of its residue coordinates. -/
noncomputable def residueCenteredKernel {D R : Type*} [Fintype R]
    (K : D × R → D × R → ℝ) (a b : D × R) : ℝ :=
  K a b - finiteResidueAverage (fun t => K (a.1, t) b) -
    finiteResidueAverage (fun u => K a (b.1, u)) +
      finiteResidueAverage (fun t => finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FlatExclusiveKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Flattening the retained exclusive-product kernel

Conditioned on the common variable, the two retained exclusive outputs
are independent. An additive local-law error for each cell therefore
gives an explicit error for their product and for the integrated kernel.
The approximating profile may be signed: its required bound follows from
the local law and the fact that the actual cell probabilities lie in `[0,1]`.
-/

namespace JointDickman

open scoped BigOperators

/-- Kernel of two conditionally independent exclusive outputs sharing the
common variable. The denominators are the output-cell masses. -/
noncomputable def exclusiveProductKernel {C D R : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (a b : D × R) : ℝ :=
  (∑ c, w c * p c a * p c b) / (μ a.1 * μ b.1)

/-- The local-law profile is independent of the residue coordinate. -/
noncomputable def flatExclusiveKernel {C D : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (v : C → D → ℝ) (d e : D) : ℝ :=
  (∑ c, w c * v c d * v c e) / (μ d * μ e)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_LowExclusiveKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite low-exclusive kernel

The common variable and the two exclusive variables have independent
finite masses. Cells are specified by an `Option`-valued map, allowing
discarded outputs. Restricting the second exclusive variable to `low`
has separate row and column estimates, proved from these actual masses.
-/

namespace JointDickman

open scoped BigOperators

section

variable {C E A : Type*} [Fintype C] [Fintype E] [Fintype A] [DecidableEq A]

noncomputable def optionCellMass (v : E → ℝ) (cell : E → Option A) (a : A) : ℝ :=
  ∑ e, if cell e = some a then v e else 0

noncomputable def lowExclusiveProbability (v : E → ℝ) (low : E → Prop)
    [DecidablePred low] : ℝ := ∑ e, if low e then v e else 0

noncomputable def independentCellMarginal (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a

/-- The common mass is integrated after multiplying the two independent
exclusive cell probabilities; only the second exclusive is restricted. -/
noncomputable def lowExclusiveMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a *
    optionCellMass (fun e => if low e then v e else 0) (cell c) b

end

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_IndependentKernelSplit
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The independent common/exclusive model and its cutoff

The three independent category bits are reindexed as three independent
Boolean prime subsets. Their products are the common product and the two
exclusive products. The low-exclusive union is separated exactly; the
complement is the product of the two high-exclusive cell probabilities.
-/

namespace JointDickman

open scoped BigOperators

def categoryToTriple (S : SplitCategories) : Bool × Bool × Bool :=
  (decide ((0 : Fin 3) ∈ S.val), decide ((1 : Fin 3) ∈ S.val),
    decide ((2 : Fin 3) ∈ S.val))

def tripleToCategory (b : Bool × Bool × Bool) : SplitCategories :=
  ⟨Finset.univ.filter (fun j : Fin 3 =>
    (if j = 0 then b.1 else if j = 1 then b.2.1 else b.2.2) = true),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

theorem tripleToCategory_categoryToTriple (S : SplitCategories) :
    tripleToCategory (categoryToTriple S) = S := by
  apply Subtype.ext
  apply Finset.ext
  intro j
  fin_cases j <;> simp [tripleToCategory, categoryToTriple]

theorem categoryToTriple_tripleToCategory (b : Bool × Bool × Bool) :
    categoryToTriple (tripleToCategory b) = b := by
  rcases b with ⟨b₀, b₁, b₂⟩
  cases b₀ <;> cases b₁ <;> cases b₂ <;> rfl

/-- Three category bits at each site are exactly three Boolean vectors. -/
def categoryTripleEquiv (ι : Type*) :
    (ι → SplitCategories) ≃ (ι → Bool) × (ι → Bool) × (ι → Bool) where
  toFun y := (fun i => (categoryToTriple (y i)).1,
    fun i => (categoryToTriple (y i)).2.1, fun i => (categoryToTriple (y i)).2.2)
  invFun x i := tripleToCategory (x.1 i, x.2.1 i, x.2.2 i)
  left_inv y := by
    funext i
    exact tripleToCategory_categoryToTriple (y i)
  right_inv x := by
    rcases x with ⟨c, e₁, e₂⟩
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))
    · apply Prod.ext <;> funext i
      · exact congrArg (fun b => b.2.1) (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))
      · exact congrArg (fun b => b.2.2) (categoryToTriple_tripleToCategory (c i, e₁ i, e₂ i))

section Cutoff

variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

noncomputable def independentPairMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a b : A) : ℝ :=
  ∑ c, w c * optionCellMass v (cell c) a * optionCellMass v (cell c) b

/-- The discarded mass is the genuine union event, so overlap is counted once. -/
noncomputable def lowUnionExclusiveMass (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) : ℝ :=
  ∑ c, ∑ e₁, ∑ e₂,
    if (low e₁ ∨ low e₂) ∧ cell c e₁ = some a ∧ cell c e₂ = some b
      then w c * v e₁ * v e₂ else 0

/-- Conditional cell probability retaining only high exclusive products. -/
noncomputable def highExclusiveCell (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (c : C) (a : A) : ℝ :=
  optionCellMass (fun e => if low e then 0 else v e) (cell c) a

noncomputable def lowUnionExclusiveKernel (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (μ : A → ℝ) (a b : A) : ℝ := lowUnionExclusiveMass w v cell low a b / (μ a * μ b)

end Cutoff

noncomputable def primeProductCell {A : Type*} (Q : Finset ℕ) (cell : ℕ → Option A)
    (c e : Q → Bool) : Option A := cell (retainedPrimeProduct Q c * retainedPrimeProduct Q e)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeResidueChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite residue estimate for the actual fair-prime channel

This combines the actual two-split comparison, the independent low/high
decomposition, and the exclusive local law. The conclusion concerns the
original fair-split channel and every real input simultaneously.
-/

namespace JointDickman

open scoped BigOperators

noncomputable def fullPrimeMass (Q : Finset ℕ) : (Q → Bool) → ℝ :=
  bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ))

noncomputable def quarterPrimeMass (Q : Finset ℕ) : (Q → Bool) → ℝ :=
  bernoulliSiteMass (fun p : Q => 1 / (4 * (p.val : ℝ)))

noncomputable def fairPrimeTransition {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → A) : (Q → Bool) → A → ℝ :=
  fairSplitTransition (fun x => cell (retainedPrimeProduct Q x))

noncomputable def primeOutputCell {A : Type*} (Q : Finset ℕ) (cell : ℕ → A) :
    (Q → Bool) → (Q → Bool) → Option A :=
  primeProductCell Q (fun n => some (cell n))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductLogCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic and residue cells, with partial output -/

namespace JointDickman

open Finset

open Classical in
noncomputable def logResidueCell {D : Type*} (B q : ℕ) (lower upper : D → ℝ)
    (n : ℕ) : Option (D × (ZMod q)ˣ) :=
  if hn : n.Coprime q then
    if hi : ∃ d, Real.log n / B ∈ Set.Ioc (lower d) (upper d) then
      some (hi.choose, ZMod.unitOfCoprime n hn)
    else none
  else none

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighExclusiveLocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local laws for the high-exclusive part of the actual prime channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

def lowPrimeLog (Q : Finset ℕ) (B : ℕ) (θ : ℝ) (x : Q → Bool) : Prop :=
  Real.log (retainedPrimeProduct Q x) / B ≤ θ

open Classical in
noncomputable def clippedIntervalIntegral (f : ℝ → ℝ) (θ a b t : ℝ) : ℝ :=
  if max θ (a - t) ≤ b - t then ∫ s in max θ (a - t)..b - t, f s else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PartialPrimeChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair-prime channels restricted to a collection of output cells -/

namespace JointDickman

open scoped BigOperators

noncomputable def partialFairPrimeTransition {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) (a : A) : ℝ :=
  optionCellMass (fairRetentionMass x) (fun y => cell (retainedPrimeProduct Q y)) a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PublishedResidueChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual residue-channel estimate from published analytic inputs

No marginal, conditional-cell, or high-exclusive approximation is assumed
here: all three are derived from the cited input estimates.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def residueChannelError (M C T : ℝ) (B : ℕ) (m mass : ℝ) : ℝ :=
  8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) *
      (M + (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) / m) +
    4 * ((2 * (C * (B : ℝ) ^ (-(80 : ℝ))) + (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 +
      9 / (8 * (auxiliaryCutoff B : ℝ))) / (m * m)) * mass

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueChannelDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of the residue-channel error at polynomial cell scales -/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def residueDecayEnvelope (M C T : ℝ) (B : ℕ) : ℝ :=
  8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) *
    (M + C * (B : ℝ) ^ (-(77 : ℝ)) + (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ))) +
  12 * (2 * C * (B : ℝ) ^ (-(74 : ℝ)) + C ^ 2 * (B : ℝ) ^ (-(154 : ℝ)) +
    (9 / 8 : ℝ) * (B : ℝ) ^ (-(994 : ℝ)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ChannelGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's refining logarithmic grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def channelFineCount (m₁ B : ℕ) : ℕ :=
  m₁ * ⌈((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m₁⌉₊

noncomputable def channelMesh (n : ℕ) : ℝ := (5 / 2 : ℝ) / n

noncomputable def channelLower (n : ℕ) (i : Fin n) : ℝ :=
  1 / 2 + (i.val : ℝ) * channelMesh n

noncomputable def channelUpper (n : ℕ) (i : Fin n) : ℝ :=
  1 / 2 + ((i.val : ℝ) + 1) * channelMesh n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformResidueChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform residue attenuation on the actual refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def manuscriptChannel (m₁ B q : ℕ)
    (f : (auxiliaryPrimes B → Bool) → ℝ) :
    Fin (channelFineCount m₁ B) × (ZMod q)ˣ → ℝ :=
  finiteChannel (fullPrimeMass (auxiliaryPrimes B))
    (fun _ => channelMesh (channelFineCount m₁ B) / (q.totient : ℝ))
    (partialFairPrimeTransition (auxiliaryPrimes B)
      (logResidueCell B q (channelLower (channelFineCount m₁ B))
        (channelUpper (channelFineCount m₁ B)))) f

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedChannelMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of signed split masses and the actual channel -/

namespace JointDickman
open Finset

noncomputable def primeSplitProductSupport (P : Finset ℕ) : Finset ℕ :=
  P.powerset.image (fun A => ∏ p ∈ A, p)

noncomputable def subsetSiteTest (P : Finset ℕ) (g : (P → Bool) → ℝ)
    (S : Finset ℕ) : ℝ := g (fun p => decide (p.val ∈ S))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CellAverageOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex cell averages and oscillation bounds -/

namespace JointDickman
open MeasureTheory

noncomputable def complexCellAverage (a b : ℝ) (F : ℝ → ℂ) : ℂ :=
  (∫ x in a..b, F x)/(b-a : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogOscillatoryTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oscillation of the actual major-arc tests in logarithmic coordinates -/

namespace JointDickman
open MeasureTheory

noncomputable def logOscillatoryTest (w : ℝ → ℝ) (B N ω : ℝ) (x : ℝ) : ℂ :=
  oscillatoryTest w ω (Real.exp (B*x)/N)

noncomputable def logOscillatoryTestDeriv (w w' : ℝ → ℝ) (B N ω : ℝ) (x : ℝ) : ℂ :=
  oscillatoryTestDeriv w w' ω (Real.exp (B*x)/N) * (B*(Real.exp (B*x)/N) : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ManuscriptHistogramFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local Fourier error of the actual signed split-product histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptCellSum (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) : ℂ :=
  ∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B),
    if logResidueCell B q (channelLower (channelFineCount m B))
      (channelUpper (channelFineCount m B)) k = some (i,r) then
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k : ℂ)*
        F (Real.log k/B) else 0

noncomputable def manuscriptCellApprox (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) : ℂ :=
  ((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ)*
    complexCellAverage (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the manuscript grid into equal coarse cells -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def channelBlockCount (m B : ℕ) : ℕ :=
  ⌈((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m⌉₊

noncomputable def groupedLower (m k : ℕ) (a : Fin m × Fin k) : ℝ :=
  channelLower (m * k) (finProdFinEquiv a)

noncomputable def groupedUpper (m k : ℕ) (a : Fin m × Fin k) : ℝ :=
  channelUpper (m * k) (finProdFinEquiv a)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_KernelDenominatorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient subpower bound for the kernel denominator sum

Mertens' product theorem and the harmonic sum bound suffice here. A
polylogarithmic bound is enough to absorb either of the manuscript's
positive power savings, so no additional mean-value theorem is assumed.
-/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def kernelDenominatorSum (j Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (1/(q.totient : ℝ))*((j*q : ℕ)/(Nat.totient (j*q) : ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local collections of fine cells for an endpoint box -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def histogramWindowCells (n : ℕ) (l u : ℝ) : Finset (Fin n) :=
  univ.filter (fun i => channelLower n i ≤ u ∧ l ≤ channelUpper n i)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramProductError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product error for the actual two endpoint histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h

noncomputable def manuscriptApproxFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h

noncomputable def manuscriptAmplitudeEnergy (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) : ℝ :=
  ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*
    (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q (fun _ => 1) (i,r)^2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueFourierProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite residue-average projection is an L2 contraction -/

namespace JointDickman
open Finset

noncomputable def complexResidueMean {q : ℕ} [NeZero q] (v : (ZMod q)ˣ → ℂ) : ℂ :=
  (∑ r, v r)/(q.totient : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ProjectedHistogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the residue projection of the actual histogram -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptProjectedValue (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ i ∈ J, (channelMesh (channelFineCount m B) : ℂ)*
    (finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) : ℂ)*
      complexCellAverage (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i) F

noncomputable def manuscriptProjectedFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun _ => complexResidueMean
    (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r)) h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ProjectedHistogramError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local residue-projection errors of the actual endpoint histograms -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptResidueEnergy (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*
    (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      (manuscriptChannel m B q g (i,r)-finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s)))^2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramCellCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing histogram cell averages by a chosen cell value -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def cellCoefficientFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J,
    (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i) h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SampledHistogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue projection of the sampled endpoint histogram -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def sampledProjectedFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun _ => complexResidueMean (fun r => ∑ i ∈ J,
    (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i)) h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SampledHistogramError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete local error from actual endpoints to the sampled projected kernel -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def oppositeProductSum {q : ℕ} [NeZero q] (P : ZMod q → Prop) [DecidablePred P]
    (A B : ZMod q → ℂ) : ℂ := ∑ h : ZMod q, if P h then A h*B (-h) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An averaged sharp cutoff for the coarse channel -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

noncomputable def averagingRamp (a b x : ℝ) : ℝ :=
  (min b (max a x) - a) / (b - a)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeRampLocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime-product local law with a ramp weight -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology

open Classical in
noncomputable def rampIntervalIntegral (f : ℝ → ℝ) (lo hi a b t : ℝ) : ℝ :=
  (∫ θ in lo..hi, clippedIntervalIntegral f θ a b t) / (hi - lo)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Lipschitz densities after the lower ramp cutoff -/

namespace JointDickman

open scoped NNReal

noncomputable def rampDensity (f : ℝ → ℝ) (lo hi x : ℝ) : ℝ :=
  averagingRamp lo hi x * f (max lo x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PublishedRampProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smoothed prime channel profile from published inputs -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology NNReal

open Classical in
noncomputable def primeRampCell {D : Type*} [DecidableEq D]
    (B q : ℕ) (lower upper : D → ℝ) (lo hi : ℝ)
    (c : auxiliaryPrimes B → Bool) (a : D × (ZMod q)ˣ) : ℝ :=
  optionCellMass
    (fun e => quarterPrimeMass (auxiliaryPrimes B) e *
      averagingRamp lo hi (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B))
    (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c) a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReindexedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing partial output cells -/

namespace JointDickman

open scoped BigOperators

def trivialResidueEquiv (A : Type*) : A × (ZMod 1)ˣ ≃ A where
  toFun := Prod.fst
  invFun a := (a, 1)
  left_inv a := by cases a with | mk a r => exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

noncomputable def logarithmicCell {A : Type*} [DecidableEq A]
    (B : ℕ) (lower upper : A → ℝ) (n : ℕ) : Option A :=
  (logResidueCell B 1 lower upper n).map (trivialResidueEquiv A)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PublishedCoarseChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic coarse channel bound from published inputs -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

noncomputable def coarseChannelError (A C T M L θ : ℝ) (B : ℕ) (δ mesh mass : ℝ) : ℝ :=
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let η := E / δ + L * δ
  8 * (T * (2 * θ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) * (A + (E + κ) / δ) +
    4 * (2 * M * η + η ^ 2 + κ / (δ * δ) + 2 * M * L * mesh) * mass

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformCoarseChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's coarse channel on its refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

noncomputable def groupedManuscriptChannel (m B : ℕ)
    (f : (auxiliaryPrimes B → Bool) → ℝ) :
    Fin m × Fin (channelBlockCount m B) → ℝ :=
  finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => channelMesh (channelFineCount m B))
    (partialFairPrimeTransition (auxiliaryPrimes B)
      (logarithmicCell B (groupedLower m (channelBlockCount m B))
        (groupedUpper m (channelBlockCount m B)))) f

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueAverageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue averaging recovers the same logarithmic marginal for every modulus -/

namespace JointDickman
open Finset

noncomputable def logCellSignedMass (m B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) : ℝ :=
  ∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
    if Real.log n/B ∈ Set.Ioc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) then
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteKernelBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear stability of a finite kernel under square-norm approximation -/

namespace JointDickman
open Finset

noncomputable def finiteKernelBilinear {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (u v : A → ℝ) : ℝ :=
  ∑ a, μ a*u a*finiteKernelAction μ K v a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CoarseKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse replacement of both bounded endpoint tests -/

namespace JointDickman
open Finset Filter

noncomputable def coarseGroupAverage {D R : Type*} [Fintype R]
    (u : D × R → ℝ) (a : D × R) : ℝ := finiteResidueAverage (fun r => u (a.1,r))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricHistogramErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summed fine-histogram and residue losses in geometric boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def geometricHistogramWindow (m B : ℕ) (t L U : ℝ) (k : ℤ) :
    Finset (Fin (channelFineCount m B)) :=
  histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricSampledIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summed replacement of the actual logarithmic endpoint integrals -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

noncomputable def manuscriptSampledIntegralError (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (F G : ℝ → ℝ → ℂ)
    (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∫ ξ : ℝ, testFourierTransform w ξ*
    (oppositeProductSum P (manuscriptFourier m B q J g (F ξ))
        (manuscriptFourier m B q J h (G ξ))-
      oppositeProductSum P
        (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)))
        (sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular series produced by the Ramanujan residue factor -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

noncomputable def singularSeriesCoefficient (j q : ℕ) : ℝ :=
  if q.Coprime j then (μ q : ℝ)/(q.totient : ℝ)^2 else 0

noncomputable def singularSeries (j : ℕ) : ℝ :=
  (j : ℝ)/j.totient * ∑' q, singularSeriesCoefficient j q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SampledMajorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained sampled kernel and its singular-series limit -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def sampledMajorKernel (m B j Q : ℕ) [NeZero j]
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
    (∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
      ∫ ξ : ℝ, testFourierTransform w ξ*
        sampledProjectedFourier m B (j*(q : ℕ)) J g (fun i => a i*additivePhase (ξ*x i)) r*
        sampledProjectedFourier m B (j*(q : ℕ)) K h (fun i => b i*additivePhase (-ξ*y i)) (-r)
      else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_LogSampledKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampled major-arc kernel in its actual logarithmic coordinates -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def sampledEndpointKernel (m B j Q : ℕ) [NeZero j]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  sampledMajorKernel m B j Q J J g h
    (fun i => (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)) w

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RetainedErrorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual retained-denominator error weights -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

noncomputable def retainedErrorSum (B j Q : ℕ) (E : ℕ+ → ℂ) : ℂ :=
  ((B : ℂ)/j)*∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/(q : ℕ).totient)*E q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricFullModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact box-summed replacement in the full retained-arc model -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def geometricFullModelDifference (m B j Q : ℕ) [NeZero j]
    (a b T t : ℝ) (S : Finset ℤ) (d : ℤ → ℂ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  (B : ℂ)*(∑ k ∈ S,
      (fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
        (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
          endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
        (fun ξ => d k*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))-
      (d k/j)*sampledEndpointKernel m B j Q
        (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
        g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogMassBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse approximation for the actual logarithmic mass kernel -/

namespace JointDickman
open Finset Filter

noncomputable def channelIndexEquiv (m B : ℕ) :
    Fin m × Fin (channelBlockCount m B) ≃ Fin (channelFineCount m B) := finProdFinEquiv

noncomputable def cellMassBilinear (m B : ℕ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) : ℝ :=
  ∑ i, ∑ k, u i*v k*K i k

noncomputable def coarseLogMass (m B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) : ℝ :=
  channelMesh (channelFineCount m B)*
    coarseGroupAverage (groupedManuscriptChannel m B g) ((channelIndexEquiv m B).symm i)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GeometricWindowKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summed geometric windows form a uniformly bounded narrow kernel -/

namespace JointDickman
open Finset Filter

noncomputable def geometricWindowKernel (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (i j : Fin (channelFineCount m B)) : ℝ :=
  (B : ℝ)*∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k ∧
    j ∈ geometricHistogramWindow m B t L U k then V k i j else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricCoarseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse comparison for the actual box-summed spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

noncomputable def endpointSpatialWeight (m B : ℕ) (t β : ℝ) (d : ℤ → ℝ)
    (w₁ w₂ w : ℝ → ℝ) (k : ℤ) (i j : Fin (channelFineCount m B)) : ℝ :=
  let zi := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let zj := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  d k*w₁ zi*w₂ zj*w (β*zi-β*zj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FullSpatialComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the full retained-arc sum to the actual spatial log kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

noncomputable def geometricFullArcSum (B j Q : ℕ) [NeZero j]
    (a b T t : ℝ) (S : Finset ℤ) (d : ℤ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  (B : ℂ)*∑ k ∈ S,
    fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
      (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
        endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
      (fun ξ => (d k : ℂ)*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogarithmicReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime bilinear reduction for squarefree-supported coefficients -/
namespace JointDickman
open Finset

noncomputable def primeSquareLogError (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0

noncomputable def primeLogBilinear (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
    ((f p*f m*Real.log p:ℝ):ℂ)*additivePhase ((p*m:ℕ)*θ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Even inclusion-exclusion truncations for the finite sieve -/
namespace JointDickman
open Finset

noncomputable def brunTruncation (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ D ∈ S.powerset.filter (fun D => D.card ≤ m), (-1 : ℝ)^D.card

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncationError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exponential error bound for even truncation -/
namespace JointDickman
open Finset

noncomputable def brunMean (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ E ∈ P.powerset, bernoulliSubsetMass P g E * brunTruncation E (2*r)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of even truncations over disjoint prime blocks -/
namespace JointDickman
open Finset

noncomputable def brunBlockChoices {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (r : ι → ℕ) : Finset (ι → Finset ℕ) := by
  classical
  exact Fintype.piFinset (fun i => (P i).powerset.filter (fun D => D.card ≤ 2*r i))

noncomputable def brunBlockUnion {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : Finset ℕ :=
  univ.biUnion D

noncomputable def brunBlockSign {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : ℝ :=
  ∏ i, (-1 : ℝ)^(D i).card

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunPrimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic logarithmic prime blocks -/
namespace JointDickman
open Finset

noncomputable def brunPrimeBlock (P : Finset ℕ) (L : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => L/(2:ℝ)^(j+1) < Real.log p ∧ Real.log p ≤ L/(2:ℝ)^j)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunUpperSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional proof of the required upper sieve

Even inclusion-exclusion truncations on disjoint logarithmic prime blocks have
coefficients of absolute value one. Their orders grow with the block index,
so their errors are summable while every supported prime product stays below
`z`. This proves the finite-event consequence of Ford's Theorem 2.4 used here.
-/
namespace JointDickman
open Finset

noncomputable def brunSieveConstant (κ A : ℝ) : ℝ :=
  Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2)) + (κ*Real.log 8+A/Real.log 2))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairLocalSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local factors for the prime-pair upper sieve -/
namespace JointDickman
open Finset

noncomputable def primePairRoots (p h : ℕ) : Finset (ZMod p) := {0,-(h:ZMod p)}

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairSieveCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the proved finite-event sieve to prime pairs -/
namespace JointDickman
open Finset

noncomputable def primePairCount (Q h : ℕ) : ℕ := by
  classical
  exact ((Ico 0 (Q+1)).filter (fun n => n.Prime ∧ (n+h).Prime)).card

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricSquareKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squared geometric kernel in the smoothed bilinear estimate -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

noncomputable def geometricSquareKernel (N : ℕ) (t : ℝ) : ℝ :=
  ‖∑ n ∈ range N, additivePhase (t*n)‖^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CyclicGeometricEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete-residue energy of the geometric kernel -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

noncomputable def cyclicGeometricKernel {q : ℕ} [NeZero q] (N : ℕ) (x : ZMod q) : ℝ :=
  ‖∑ n ∈ range N, ZMod.stdAddChar (x*(n:ZMod q))‖^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_UniformHyperbolaBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalization of the prime hyperbola block estimate -/
namespace JointDickman
open Finset

noncomputable def rationalHyperbolaBudget (N Z L : ℝ) (q : ℕ) : ℝ :=
  2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricDiscardedArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original geometric sum loses only o(1/T) outside the retained arcs -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

/-- The lag is displayed separately from the geometric endpoint scale. -/
noncomputable def geometricBoxIntegrand (B j : ℕ) (a b T t : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w₃ : ℝ → ℝ)
    (k : ℤ) (θ : ℝ) : ℂ :=
  endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
    endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)*
    smoothCoefficientAdditiveSum B (Real.exp ((k : ℝ)*t)/T) (-(j : ℝ)*θ) w₃

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCoarseFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded coarse features of the actual prime-site distribution -/

namespace JointDickman
open Finset

noncomputable def primeGroupedTransition (m B : ℕ) (x : auxiliaryPrimes B → Bool)
    (a : Fin m × Fin (channelBlockCount m B)) : ℝ :=
  partialFairPrimeTransition (auxiliaryPrimes B)
    (logarithmicCell B (groupedLower m (channelBlockCount m B))
      (groupedUpper m (channelBlockCount m B))) x a

noncomputable def primeCoarseFeature (m B : ℕ) (d : Fin m)
    (x : auxiliaryPrimes B → Bool) : ℝ :=
  (∑ r : Fin (channelBlockCount m B), primeGroupedTransition m B x (d,r))/channelMesh m

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GroupedKernelFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-feature form of a coarse kernel -/

namespace JointDickman
open Finset

noncomputable def groupedKernelCoefficient {D R : Type*} [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) (d e : D) : ℝ :=
  δ^2*∑ r, ∑ s, K (d,r) (e,s)

noncomputable def primeCoarseCoefficient (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    Fin m → Fin m → ℝ :=
  groupedKernelCoefficient (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))

noncomputable def primeCoarseKernel (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (x y : auxiliaryPrimes B → Bool) : ℝ :=
  ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
    primeCoarseFeature m B d x*primeCoarseFeature m B e y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorCutoff
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth separated factors for compact polynomial approximation -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def tensorBoxBump : ContDiffBump (9/4 : ℝ) where
  rIn := 7/4
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def tensorPowerFactor (n : ℕ) : 𝓢(ℝ,ℝ) :=
  (tensorBoxBump.hasCompactSupport.mul_left (f := fun x : ℝ => x^n)).toSchwartzMap
    ((contDiff_id.pow n).mul tensorBoxBump.contDiff)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothArithmeticTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tensor expansion of the full smooth arithmetic weight -/

namespace JointDickman
open Finset

noncomputable def geometricSmoothArithmeticSum (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (W : ℤ → ℝ → ℝ → ℝ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ k ∈ S,
    ∑ c ∈ Ioc ⌊l*(Real.exp ((k : ℝ)*t)/T)⌋₊ ⌊u*(Real.exp ((k : ℝ)*t)/T)⌋₊,
    ∑ n₂ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
    ∑ n₁ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
      if n₁ = n₂+j*c then
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n₁*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) n₂*
        coefficientWeight B c*
        W k (n₁/Real.exp ((k : ℝ)*t)) (n₂/Real.exp ((k : ℝ)*t))
          (c/(Real.exp ((k : ℝ)*t)/T))
      else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolynomialArithmeticFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite polynomial smooth weight has a finite prime-site kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

noncomputable def polynomialTermKernel (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  primeCoarseKernel m B
    (geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
      (endpointSpatialWeight m B t (T/j)
        (fun k => (P.coeff d*(s k)^(d 3))*
          coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))))

noncomputable def polynomialPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ)
    (x y : auxiliaryPrimes B → Bool) : ℝ :=
  ∑ d ∈ P.support, polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothDyadicPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete smooth geometric partition of unity -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def dyadicPartitionWeight (x : ℝ) : ℝ :=
  Real.smoothTransition (2-x)-Real.smoothTransition (2-2*x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationTensorProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual amplification weight in normalized geometric-box coordinates -/

namespace JointDickman
open scoped Topology

noncomputable def amplificationSpatialProfile (x y z : ℝ) : ℝ :=
  amplificationBump (x/z)*amplificationBump (y/z)*dyadicPartitionWeight z

noncomputable def amplificationTensorProfile (v : Fin 4 → ℝ) : ℝ :=
  amplificationBump (v 3)*amplificationSpatialProfile (v 0) (v 1) (v 2)

noncomputable def amplificationBoxWeight (B : ℕ) (s x y z : ℝ) : ℝ :=
  amplificationBump (s+Real.log z/B)*amplificationSpatialProfile x y z

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricDyadicPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic recombination of the original amplification weight -/

namespace JointDickman
open Finset

noncomputable def dyadicBoxIndices (L U : ℕ) : Finset ℤ :=
  (Ico L U).image (fun k => ((k+1 : ℕ) : ℤ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationBoxSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact support of the amplification integrand in each geometric box -/

namespace JointDickman
open Finset

noncomputable def amplificationArithmeticTerm (B j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
    coefficientWeight B c*
    (amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*amplificationBump (b/(T*c)))
  else 0

noncomputable def amplificationBoxTerm (B j : ℕ) (T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
    coefficientWeight B c*
    amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T))
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DyadicScaleWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic indices in the manuscript's scale window -/

namespace JointDickman
open Finset

noncomputable def dyadicBoxLower (B : ℕ) (T : ℝ) : ℕ :=
  ⌊((B : ℝ)+Real.log T)/Real.log 2⌋₊-1

noncomputable def dyadicBoxUpper (B : ℕ) (T : ℝ) : ℕ :=
  ⌈(2*(B : ℝ)+Real.log T)/Real.log 2⌉₊+1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationDyadicIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reconstruction of the unpartitioned amplification triple sum -/

namespace JointDickman
open Finset

noncomputable def amplificationArithmeticSum (B j : ℕ) (T : ℝ) (U V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    amplificationArithmeticTerm B j T g h c b a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationArithmeticFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original amplification arithmetic sum has a bounded finite-feature kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T : ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  polynomialPrimeKernel P m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun k => Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SignedCoefficientSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact sign reversal for the coefficient relation a - b = jc -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def coefficientRelationWeight (B : ℕ) (j : ℤ) (a b c : ℕ) : ℝ :=
  if (a : ℤ) = b + j * c then
    coefficientWeight B a * coefficientWeight B b * coefficientWeight B c else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedRegularityLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss on the signed coefficient support -/

namespace JointDickman

open Filter Finset
open scoped Topology

def coefficientTripleRegular (B L : ℕ) (τ C : ℝ) (a b c : ℕ) : Prop :=
  RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B b) ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B c)

open Classical in
noncomputable def discardedRelationWeight (B L : ℕ) (τ C : ℝ) (j : ℤ) (a b c : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else coefficientRelationWeight B j a b c

noncomputable def signedDiscardedCoefficientMass (B L : ℕ) (τ C : ℝ)
    (j : ℤ) (I J : Finset ℕ) : ℝ :=
  ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ J, discardedRelationWeight B L τ C j a b c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationRegularityIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic recombination of the discarded regularity mass -/

namespace JointDickman
open Finset

open Classical in
noncomputable def discardedAmplificationTerm (B L j : ℕ) (τ C T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else
    |(B : ℝ)*amplificationArithmeticTerm B j T g h c b a|

open Classical in
noncomputable def discardedAmplificationBoxTerm (B L j : ℕ) (τ C T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else
    |(B : ℝ)*amplificationBoxTerm B j T N g h c b a|

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationFairKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth amplification sum as the actual fair-split kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def amplificationScalarWeight (B j : ℕ) (T : ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then coefficientWeight B c*
    (amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
      amplificationBump (b/(T*c))) else 0

open Classical in
noncomputable def amplificationFairKernel (B j : ℕ) (T : ℝ) (V : ℕ)
    (x z : auxiliaryPrimes B → Bool) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
    fairRetentionMass x y*fairRetentionMass z w*
      amplificationScalarWeight B j T c
        (retainedPrimeProduct (auxiliaryPrimes B) w)
        (retainedPrimeProduct (auxiliaryPrimes B) y)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique-quotient bound used when removing coprimality -/

namespace JointDickman
open Finset

open Classical in
noncomputable def amplificationProductWeight (B j : ℕ) (T : ℝ) (V a b : ℕ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, amplificationScalarWeight B j T c b a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphCandidateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial graph multiplicity without excluding site squares -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def activeGraphTriples (B L T N : ℕ) (τ C : ℝ) (j : ℤ) (n : ℕ) :
    Finset GraphCoefficientTriple :=
  (arithmeticGraphTriples B T).filter (fun g => graphTripleLag g = j ∧
    n ∈ graphTripleEdges N g ∧ graphTripleWeight B L τ C T g n ≠ 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeLogMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite measure of logarithmic large-prime locations -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def finiteDirac (t : ℝ) : FiniteMeasure ℝ :=
  ⟨Measure.dirac t, inferInstance⟩

noncomputable def primeLogMeasure (c x : ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ largePrimeSet x (x^c),
    (Real.toNNReal (1/(p : ℝ))) • finiteDirac (Real.log p/Real.log x)

noncomputable def logIntervalVolume (c : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Ioc (Real.log c) 0), inferInstance⟩

noncomputable def logarithmicPrimeMeasure (c : ℝ) : FiniteMeasure ℝ :=
  (logIntervalVolume c).map Real.exp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AtomicProductMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite atomic expansions of product measures -/
namespace JointDickman
open Finset MeasureTheory
open scoped NNReal ENNReal

noncomputable def finitePointMeasure {Ω : Type*} [MeasurableSpace Ω] (t : Ω) : FiniteMeasure Ω :=
  ⟨Measure.dirac t, inferInstance⟩

noncomputable def finiteAtomicMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ P, w p • finitePointMeasure (f p)

noncomputable def atomicTupleMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure (Fin h → ℝ) :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
    (∏ i, w (v i)) • finitePointMeasure (fun i => f (v i))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothed logarithmic windows and their Dirichlet energy

A finite sum of translates of a Schwartz window is itself Schwartz. Its
Fourier transform factors into the window transform and the actual finite
Dirichlet polynomial. Plancherel therefore identifies the two energies
without a truncation or an arithmetic hypothesis.
-/
namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap FourierTransform

/-- The reciprocal-weighted Dirichlet polynomial in Fourier normalization. -/
noncomputable def mellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ S, (a n / (n : ℂ)) * additivePhase (-ξ * Real.log (n : ℝ))

/-- A smoothed logarithmic window, retaining the literal coefficients. -/
noncomputable def mellinPacket (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) :
    𝓢(ℝ, ℂ) :=
  ∑ n ∈ S, (a n / (n : ℂ)) • w.compSubConstCLM ℂ (Real.log (n : ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPacketScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithmic windows at a prescribed scale -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap FourierTransform

/-- The normalized dilation `w(v/δ)/δ`, for a positive window scale. -/
noncomputable def normalizedSchwartzScale (w : 𝓢(ℝ, ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    𝓢(ℝ, ℂ) :=
  ((δ : ℂ)⁻¹) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 δ hδ.ne')).symm w

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinAngularEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Angular-frequency normalization for the published Dirichlet estimates -/
namespace JointDickman
open Finset MeasureTheory

/-- The convention used in the Dirichlet-polynomial mean-square estimates. -/
noncomputable def angularMellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n / (n : ℂ)) * Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Set
open scoped BigOperators ComplexConjugate

noncomputable def mrtExponentialPolynomial {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i * Complex.exp ((freq i * t : ℝ) * Complex.I)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MertensScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The bounded-error estimate controls the reciprocal-prime mass
at the rough-sieve scale. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def sievePrimesUpTo (y : ℝ) : Finset ℕ := (Iic ⌊y⌋₊).filter Nat.Prime

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The only classical input here is the already discharged Mertens theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtPrimeBand (P Q : ℝ) : Finset ℕ :=
  sievePrimesUpTo Q \ sievePrimesUpTo P

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTAmplificationPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit amplification order used between two successive MRT
prime scales. The integer ceiling satisfies the exact support inequalities
needed by the mixed cofactor moment. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtAmplificationOrder (Y u : ℝ) : ℕ :=
  ⌈Real.log u / Real.log Y⌉₊

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MultiscaleMellinEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual multiscale prime partition in the Mellin convention

The costs below are the proved Ramaré extraction and amplified cofactor
costs. The integral over the class with no small prime polynomial remains
explicit; no estimate for that exceptional class is assumed here.
-/
namespace JointDickman
open Finset MeasureTheory
open TwoPointCorrelations

structure MellinPrimeBands where
  primes : ℕ → Finset ℕ
  bins : ℕ → Finset ℕ
  bin : ℕ → ℕ → ℕ
  lower : ℕ → ℕ → ℝ
  resolution : ℕ → ℝ
  threshold : ℕ → ℕ → ℝ

namespace MellinPrimeBands

noncomputable def polynomial (D : MellinPrimeBands) (f : ℕ → ℂ)
    (j k : ℕ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial ((D.primes j).filter (fun p => D.bin j p = k))
    (fun p => f p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t

structure Valid (D : MellinPrimeBands) (J N : ℕ) : Prop where
  prime : ∀ j ∈ range J, ∀ p ∈ D.primes j, p.Prime
  disjoint : Set.PairwiseDisjoint (range J : Set ℕ) D.primes
  bin_mem : ∀ j ∈ range J, ∀ p ∈ D.primes j, D.bin j p ∈ D.bins j
  resolution_one : ∀ j ∈ range J, 1 ≤ D.resolution j
  resolution_two : ∀ j ∈ range J, D.resolution j ≤ 2
  prime_bounds : ∀ j ∈ range J, ∀ p ∈ D.primes j,
    D.lower j (D.bin j p) ≤ p ∧ (p : ℝ) ≤ D.resolution j * D.lower j (D.bin j p)
  lower_two : ∀ j ∈ range J, ∀ k ∈ D.bins j, 2 ≤ D.lower j k
  upper : ∀ j ∈ range J, ∀ k ∈ D.bins j, 2 ≤ (N : ℝ) / D.lower j k
  threshold_pos : ∀ j ∈ range J, ∀ k ∈ D.bins j, 0 < D.threshold j k

noncomputable def extractionCost (D : MellinPrimeBands) (j N : ℕ) (T : ℝ) : ℝ :=
  2816 * Real.exp 1 * (T / N + 1) *
    ((∑ p ∈ D.primes j, 1 / (p : ℝ)^2) +
      (∑ p ∈ D.primes j, 1 / (p : ℝ)^2)^2 + (D.resolution j - 1))

noncomputable def initialCost (D : MellinPrimeBands) (N : ℕ) (T : ℝ) : ℝ :=
  64 * Real.exp 1 * ((D.bins 0).card : ℝ) *
    ∑ k ∈ D.bins 0, (D.threshold 0 k)^2 * (T * D.lower 0 k / N + 1)

noncomputable def laterCost (D : MellinPrimeBands) (j N : ℕ) (T : ℝ) : ℝ :=
  2 * ∑ b ∈ D.bins (j-1), ((D.bins j).card : ℝ) *
    ∑ k ∈ D.bins j, (D.threshold j k)^2 *
      ((16 * Real.exp 10 *
        (T / N + (2 : ℝ)^(mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)+1) *
          ⌈D.lower (j-1) b⌉₊) *
        ((mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)).factorial : ℝ)^2) /
        (D.threshold (j-1) b)^(2*mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)))

end MellinPrimeBands
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandParameters
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def mrtBandLower (P Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j) * (Real.log Q) ^ (j - 1) * Real.log P)

noncomputable def mrtBandUpper (Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j + 2) * (Real.log Q) ^ j)

lemma mrt_band_index_le_log_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hlogQ : 1 ≤ Real.log Q) : (j : ℝ) ≤ Real.log (mrtBandUpper Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  simp only [mrtBandUpper, Real.log_exp]
  calc
    (j : ℝ) ≤ (j : ℝ) ^ (4 * j + 2) := by
      simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 4 * j + 2 by omega)
    _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by
      have hh := one_le_pow₀ (n := j) hlogQ
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ j) (4 * j + 2)]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations

noncomputable def mrtFrequencyExponent (η : ℝ) (j : ℕ) : ℝ :=
  1 / 4 - η * (1 + 1 / (2 * ((j : ℝ) + 1)))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLogPrimeBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtPrimeLogBin (H : ℝ) (p : ℕ) : ℕ :=
  ⌊H * Real.log (p : ℝ)⌋₊

noncomputable def mrtPrimeLogLower (H : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / H)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBinMomentSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite witness-bin sum. Both bin cardinalities and the
remaining exponential sum are bounded using their actual endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtLogBins (H P Q : ℝ) : Finset ℕ :=
  Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic bin resolution used in the multiscale partition.
Its balance with the first prime threshold is exact. -/

namespace TwoPointCorrelations

open Finset

noncomputable def mrtBaseResolution (P Q η : ℝ) : ℝ :=
  Real.exp ((1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q))

noncomputable def mrtResolution (P Q η : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ 2 * mrtBaseResolution P Q η

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalMellinBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published logarithmic prime bands in the actual energy partition -/
namespace JointDickman
open Finset TwoPointCorrelations

noncomputable def canonicalMellinBands (P Q η : ℝ) : MellinPrimeBands where
  primes j := mrtPrimeBand (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  bins j := mrtLogBins (mrtResolution P Q η (j+1))
    (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  bin j := mrtPrimeLogBin (mrtResolution P Q η (j+1))
  lower j := mrtPrimeLogLower (mrtResolution P Q η (j+1))
  resolution j := Real.exp (1 / mrtResolution P Q η (j+1))
  threshold j k := Real.exp (-mrtFrequencyExponent η j *
    Real.log (mrtPrimeLogLower (mrtResolution P Q η (j+1)) k))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexShortIntervalConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The nonprincipal-character consequence of the published complex input

The arithmetic proof that the pretentious distance tends to infinity is a
separate obligation. Given exactly that fact, the Matomäki--Radziwiłł--Tao
input proves the short-average conclusion in the order of limits used in
`labels-short`: the main scale tends to infinity before the short length.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

/-- The pretentious-distance error in the published complex estimate. -/
noncomputable def distanceError (M : ℝ) : ℝ := (1 + M) * Real.exp (-M)

end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexFiniteShortAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite complex combinations of nonprincipal short averages -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory
open scoped Topology

noncomputable def complexFiniteShort {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (H z : ℝ) : ℂ :=
  ∑ i ∈ S, c i*complexShortAverage (f i) H z

end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinShortComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal weights in a short interval

Replacing the counting weight by `x/n` costs at most `(H+1)/x` in a
one-bounded short average. This is the elementary bridge to logarithmic
windows; the bound is uniform in the coefficients.
-/
namespace JointDickman
open Finset PublishedInputs

noncomputable def reciprocalShortAverage (f : ArithmeticFunction ℂ) (H x : ℝ) : ℂ :=
  (x : ℂ) * (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n / (n : ℂ)) / (H : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinLogWindows
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic reparametrization of a short interval -/
namespace JointDickman
open Finset PublishedInputs

noncomputable def logarithmicWindowAverage (f : ArithmeticFunction ℂ) (δ v : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + δ)⌋₊,
    f n / (n : ℂ)) / (δ : ℂ)

theorem logarithmic_window_width {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    0 < Real.log ((x + H) / x) ∧
      H / (x + H) ≤ Real.log ((x + H) / x) ∧
      Real.log ((x + H) / x) ≤ H / x := by
  have hsum : 0 < x + H := by positivity
  have hr : 0 < (x + H) / x := div_pos hsum hx
  have hr1 : 1 < (x + H) / x := (lt_div_iff₀ hx).mpr (by linarith)
  refine ⟨Real.log_pos hr1, ?_, ?_⟩
  · calc
      H / (x + H) = 1 - ((x + H) / x)⁻¹ := by field_simp [hx.ne', hsum.ne'] <;> ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos hr
  · calc
      _ ≤ (x + H) / x - 1 := Real.log_le_sub_one_of_pos hr
      _ = H / x := by field_simp [hx.ne'] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWindowProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth inner approximations to a logarithmic interval -/
namespace JointDickman
open scoped SchwartzMap

noncomputable def logarithmicWindowBump (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ContDiffBump (1/2 : ℝ) where
  rIn := 1/2 - η
  rOut := 1/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

noncomputable def logarithmicWindowProfile (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    𝓢(ℝ, ℂ) :=
  ((logarithmicWindowBump η hη hηhalf).hasCompactSupport.toSchwartzMap
    (logarithmicWindowBump η hη hηhalf).contDiff).postcompCLM Complex.ofRealCLM

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinBandSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximal band selection below the square-root logarithmic cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma exists_mellin_band_above (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) :
    ∃ j : ℕ, Y < Real.log (mrtBandUpper Q (j+1)) := by
  obtain ⟨j, hj⟩ := exists_nat_gt Y
  refine ⟨j, hj.trans_le ?_⟩
  have hjs : (j : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (show j ≤ j+1 by omega)
  exact hjs.trans (mrt_band_index_le_log_upper Q (j+1) (by omega) hQ)

noncomputable def mellinBandCount (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) : ℕ :=
  Nat.find (exists_mellin_band_above Q Y hQ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GrowingMomentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary parameters for the growing prime moment -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

noncomputable def growingPrimeMoment (X M : ℝ) : ℕ := ⌊Real.log X/Real.log M⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DickmanDistribution
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The continuous Dickman distribution function

Continuity and endpoint behavior of the Dickman function determine its
continuous distribution function and the limiting order probabilities.
-/

namespace JointDickman

open Filter Erdos970.NumberTheoryLean
open scoped Topology

noncomputable def dickmanCDF (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else Dickman.rho (1 / t)

@[simp] theorem dickmanCDF_zero : dickmanCDF 0 = 0 := by simp [dickmanCDF]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published one-variable distribution input

G. Tenenbaum, *A rate estimate in Billingsley's theorem for the size
distribution of large prime factors*, Quart. J. Math. 51 (2000), 385–403:
the unnumbered main Theorem, parts (i), (iii) at H = 0, equations (1.1),
(1.3), and the multiplicity remark following (1.7), printed pp. 386–388.
Author's corrected version: https://tenenb.perso.math.cnrs.fr/PPP/Billingsley.pdf

The input below is only its finite-bin consequence. Thresholds are the
fixed positive numbers k/J; hence finitely many ranks suffice. Continuity
of the limiting distribution permits replacing the counting endpoint by
A*x and the rank thresholds by powers of x. Its first-rank marginal is
the classical Dickman law. No statement about two different integers,
residue restrictions, weights, or short intervals is included.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

abbrev BinCountState (J : ℕ) := Fin (J-1) → Fin (J+1)

noncomputable def canonicalBinVector (J : ℕ) (x : ℝ) (n : ℕ) : BinCountState J :=
  fun i => ⟨min (binCount (primeBin x J (i.val+1)) n) J,
    (min_le_right _ _).trans_lt (Nat.lt_succ_self J)⟩

noncomputable def binStateDensity (J : ℕ) (A x : ℝ) (r : BinCountState J) : ℝ :=
  (((Ioc 0 ⌊A*x⌋₊).filter (fun n => canonicalBinVector J x n = r)).card : ℝ)/(A*x)

namespace PublishedInputs

/-- Finite-bin specialization of Tenenbaum (2000), main Theorem (i),(iii),
including the stated multiplicity version. -/
def FiniteBinDistributionInput : Prop :=
  ∀ J : ℕ, 2 ≤ J → ∃ ν : BinCountState J → ℝ,
    (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
    (∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r))) ∧
    (∀ k : ℕ, 0 < k → k < J →
      (∑ r with ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0, ν r) =
        dickmanCDF ((k : ℝ)/J))

end PublishedInputs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered prefix means supplied by the one-variable distribution -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def binDistributionMean {J : ℕ} (ν : BinCountState J → ℝ)
    (ζ : Fin (J-1) → ℂ) : ℂ := ∑ r, (ν r : ℂ)*∏ i, ζ i^(r i).val

noncomputable def centeredBinPrefix (J : ℕ) (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (A x : ℝ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ))/(A*x : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FinitePrimeWeight
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact divisor expansion for weights supported on finitely many primes -/
namespace JointDickman
open Finset Classical

noncomputable def finitePrimeWeight (P : Finset ℕ) (t : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ P, if p ∣ n then t p else 1, by simp⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeGeneratingMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generating functions for distinct prime factors -/
namespace JointDickman
open Finset

noncomputable def primeGeneratingAverage (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ := by
  classical
  exact (∑ n ∈ Ioc 0 N, ∏ p ∈ P, if p ∣ n then z p else 1)/(N : ℝ)

noncomputable def boundedPrimeSubsets (P : Finset ℕ) (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)

noncomputable def primeGeneratingModel (P : Finset ℕ) (z : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ D ∈ boundedPrimeSubsets P N, (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedPrimeSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered tuple parametrization of prime subsets -/
namespace JointDickman
open Finset

noncomputable def orderedPrimeTuples (P : Finset ℕ) (h : ℕ) : Finset (Fin h → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin h => P)).filter StrictMono

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeneratingDegreeExpansion
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the generating model into ordered prime degrees -/
namespace JointDickman
open Finset

noncomputable def primeGeneratingDegree (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) : ℝ := by
  classical
  exact ∑ D ∈ P.powersetCard h,
    if (∏ p ∈ D, p) ≤ N then (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ) else 0

@[simp] theorem primeGeneratingDegree_zero (P : Finset ℕ) (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    primeGeneratingDegree P z N 0 = 1 := by
  classical
  simp [primeGeneratingDegree, hN.ne']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Null boundaries for the prime-product cutoffs -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

instance logarithmicPrimeMeasure_nullSingletons (c : ℝ) :
    NullSingletonClass (logarithmicPrimeMeasure c : Measure ℝ) := by
  constructor
  intro t
  change (Measure.map Real.exp (volume.restrict (Set.Ioc (Real.log c) 0))) {t} = 0
  rw [Measure.map_apply Real.measurable_exp (measurableSet_singleton t),
    Measure.restrict_apply (Real.measurable_exp (measurableSet_singleton t))]
  apply measure_mono_null (t := {Real.log t}) _ (measure_singleton _)
  rintro y ⟨hy,_⟩
  have he : Real.exp y = t := hy
  simpa only [Real.log_exp, Set.mem_singleton_iff] using (congrArg Real.log he)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBoxBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity sets for prescribed prime bins and product bounds -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def primeBoxCutoff (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) ∩ {t | ∑ i, t i ≤ u}

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedPrimeBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered prime tuples are continuity sets -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def orderedPrimeBox (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  {t | StrictMono t} ∩ primeBoxCutoff h a b u

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBinPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact partition of the large primes into logarithmic bins -/
namespace JointDickman
open Finset

noncomputable def primeBinWeight (J : ℕ) (z : Fin (J-1) → ℝ) (x : ℝ) (p : ℕ) : ℝ := by
  classical
  exact ∏ i, if p ∈ primeBin x J (i.val+1) then z i else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OrderedBinTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Limits of ordered prime tuples with prescribed bin indices -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def orderedBinTupleMass (J h : ℕ) (A x : ℝ)
    (r : Fin h → Fin (J-1)) : ℝ := by
  classical
  exact ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^((1 : ℝ)/J))) h,
    if (∀ i, v i ∈ primeBin x J ((r i).val+1)) ∧ (∏ i, v i) ≤ ⌊A*x⌋₊
      then ∏ i, 1/(v i : ℝ) else 0

noncomputable def orderedBinTupleLimit (J h : ℕ) (r : Fin h → Fin (J-1)) : ℝ :=
  (FiniteMeasure.pi (fun _ : Fin h => logarithmicPrimeMeasure ((1 : ℝ)/J)))
    (orderedPrimeBox h (fun i => ((r i).val+1 : ℝ)/J)
      (fun i => ((r i).val+2 : ℝ)/J) 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RepeatedPrimeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated large prime factors have vanishing density

This removes prime multiplicities when proving the finite-bin distribution
input from finite prime-divisor expansions.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def repeatedPrimeExceptions (Q : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun n => ∃ p ∈ Q, p^2 ∣ n)

noncomputable def distinctBinCount (E : Finset ℕ) (n : ℕ) : ℕ := by
  classical
  exact (E.filter (fun p => p ∣ n)).card

noncomputable def allLargeBinPrimes (J : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊x^((1 : ℝ)/J)⌋₊ ⌊x⌋₊).filter Nat.Prime

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BinGeneratingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional limits of the finite-bin generating polynomials -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def binDegreeLimit (J : ℕ) (z : Fin (J-1) → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ r : Fin (n+1) → Fin (J-1),
      (∏ i, (z (r i)-1))*orderedBinTupleLimit J (n+1) r

noncomputable def binGeneratingLimit (J : ℕ) (z : Fin (J-1) → ℝ) : ℝ :=
  ∑ h ∈ range (J+1), binDegreeLimit J z h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinStateExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting finite-state probabilities from generating values -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def binStateGeneratingAverage (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(canonicalBinVector J x n i).val)/(A*x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DistinctBinDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing prime multiplicities in the finite-bin marginal law -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def distinctBinVector (J : ℕ) (x : ℝ) (n : ℕ) : BinCountState J :=
  fun i => ⟨min (distinctBinCount (primeBin x J (i.val+1)) n) J,
    (min_le_right _ _).trans_lt (Nat.lt_succ_self J)⟩

noncomputable def distinctBinStateDensity (J : ℕ) (A x : ℝ) (r : BinCountState J) : ℝ :=
  (((Ioc 0 ⌊A*x⌋₊).filter (fun n => distinctBinVector J x n = r)).card : ℝ)/(A*x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DistinctBinGenerating
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generating functions are unchanged by discarding repeated large primes -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def distinctBinGeneratingAverage (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(distinctBinVector J x n i).val)/(A*x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalGenerating
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-bin marginal as an explicit generating value -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def highBinZeroWeight (J k : ℕ) (i : Fin (J-1)) : ℝ :=
  if k ≤ i.val+1 then 0 else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_OrderedSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the least coordinate from an ordered simplex -/
namespace JointDickman
open Finset MeasureTheory
open scoped ENNReal

noncomputable def orderedTupleRegion (n : ℕ) (u : ℝ) : Set (Fin n → ℝ) :=
  {t | StrictMono t} ∩ {t | ∑ i, t i ≤ u}

noncomputable def orderedSimplexMass (μ : Measure ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => μ)).real (orderedTupleRegion n u)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicSimplexRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The least-coordinate recurrence for ordered logarithmic simplices -/
namespace JointDickman
open MeasureTheory Set

noncomputable def logarithmicSimplex (n : ℕ) (c : ℝ) : ℝ :=
  orderedSimplexMass (logarithmicPrimeMeasure c) n 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicSimplexCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordered integral vanishes above the product-degree cutoff -/
namespace JointDickman
open Finset Filter MeasureTheory

noncomputable def logarithmicAvoidance (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex n c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLowFrequency
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional low-frequency control of the actual weighted bin labels -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def centeredWeightedBinCoefficient (J : ℕ) (ζ : Fin (J-1) → ℂ)
    (μ : ℂ) (P : Finset ℕ) (t : ℕ → ℝ) (x : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n - μ) *
    (finitePrimeWeight P t n : ℂ), by simp⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrimeSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The proved sieve applied to nonnegative Mellin square weights -/
namespace JointDickman
open Finset
open scoped Classical

noncomputable def primeDivisorEvents (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun p => p ∣ n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSampleDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite duality for sampled Mellin polynomials

Finite duality reduces sparse-prime sampling to a row bound for the
weighted Mellin kernel.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped ComplexConjugate

noncomputable def mellinSampleKernel (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ P, (w n : ℂ)*Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive smooth weight for sparse prime sampling

The weight is at least 1/8 on `[N,2N]` and its Mellin transform has
quadratic decay. This provides the majorant used by the finite sieve.
-/
namespace JointDickman
open MeasureTheory TwoPointCorrelations

noncomputable def mellinSieveWeight (N x : ℝ) : ℝ :=
  (N/x)*Real.exp (-2*|Real.log x-Real.log N|)

noncomputable def mellinSieveAtom (N t x : ℝ) : ℂ :=
  (mellinSieveWeight N x : ℂ)*
    Complex.exp (((-t*(Real.log x-Real.log N) : ℝ) : ℂ)*Complex.I)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive continuous main term for the sparse-prime sieve -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped ComplexConjugate

noncomputable def mellinSieveMainKernel (N t : ℝ) : ℂ :=
  Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I) * ((4*N/(4+t^2) : ℝ) : ℂ)

noncomputable def mellinSieveMain (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) : ℝ :=
  N * ∫ v : ℝ, Real.exp (-|v|/(1/2)) *
    ‖mrtExponentialPolynomial S (fun t => b t *
      Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I)) (fun t => -t) v‖^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal divisor-sum remainders for the Mellin sieve -/
namespace JointDickman
open Finset
open scoped Classical ComplexConjugate

noncomputable def mellinSieveDiscreteKernel (K d : ℕ) (N t : ℝ) : ℂ :=
  mellinSampleKernel ((Icc 1 K).filter (fun n => d ∣ n)) (fun n => mellinSieveWeight N n) t

noncomputable def mellinSieveSquareWeight (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) : ℝ :=
  mellinSieveWeight N n * ‖∑ t ∈ S, b t *
    Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterFourierExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Fourier expansion of character-twisted logarithmic sums -/
namespace JointDickman
open Finset Complex

noncomputable def characterFourierCoefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ZMod q) : ℂ :=
  (q:ℂ)⁻¹ * ZMod.dft (fun n => χ n) k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the positive Mellin sieve profile -/
namespace JointDickman
open Complex

noncomputable def mellinSieveFunction (N t x : ℝ) : ℂ :=
  (mellinSieveWeight N x : ℂ)*Complex.exp (((-Real.log x*t : ℝ) : ℂ)*I)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary budgets for sparse prime sampling -/
namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def mellinSparseBudget (A δ κ q : ℝ) : ℝ :=
  132*q^(2*κ-1)*Real.log q + 176*A*q^(2*κ-10*δ)*(Real.log q)^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AuxiliaryExceptionalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bound for the full exceptional energy -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

noncomputable def auxiliarySampleCost (C H₀ X : ℝ) (N : ℕ) (T a b : ℝ) : ℝ :=
  (((Real.log a)^10)⁻¹)^2*
    (48000*(2*(1+Real.log (2*T+1))+
      ((H₀*(Real.log X)^2+1)*X^(5/12:ℝ))*Real.sqrt (2*T)*a/N))+
    b^2*(C/(Real.log a)^2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryCostLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The auxiliary sampling error vanishes after the bin-count loss -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def auxiliaryVanishingCost (H L c β X : ℝ) : ℝ :=
  48000*(8*L^2/c^4/Real.log X+
    2*L^2*(H+1)*(Real.log X)^4*X^(β-1/12))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual logarithmic bins in a fixed power auxiliary band -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

noncomputable def auxiliaryLogBins (H α β X : ℝ) : Finset ℕ :=
  Icc ⌊H*Real.log (X^α)⌋₊ ⌊H*Real.log (X^β)⌋₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphLagMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual lag mass is dominated by a finite sum of periodic means -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def arithmeticLagMass (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) : ℝ :=
  (∑ i ∈ arithmeticGraphTriples B T, if graphTripleLag i = j then
    ∑ n ∈ graphTripleEdges N i, graphTripleWeight B L τ C T i n else 0)/(N : ℝ)

noncomputable def graphLagMajorant (B T N : ℕ) (j : ℤ) : ℝ :=
  (∑ i ∈ coprimeGraphTriples B T j,
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) *
    ∑ n ∈ range (2*T*N), graphEdgeEnvelope B (∏ p ∈ i.2.1, p)
      (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) j n)/(N : ℝ)

noncomputable def graphLagMean (B T : ℕ) (j : ℤ) : ℝ :=
  ∑ i ∈ coprimeGraphTriples B T j,
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) * (2*(T : ℝ)) *
    graphEdgeMean B (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphLagSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing a coefficient representation reverses its lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

def graphTripleSwap (i : GraphCoefficientTriple) : GraphCoefficientTriple :=
  (i.1,i.2.2,i.2.1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticLagCorrelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite sets of actual lag correlations are controlled by their mass -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def arithmeticKernelMass (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) : ℝ :=
  (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
    rawArithmeticGraphKernel B L τ C T N j n)/((B : ℝ)*T*N)

noncomputable def kernelLagCorrelation (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (F : ℕ → ℂ) : ℝ :=
  (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
    rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re) /
      ((B : ℝ)*T*N)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLagSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular factor has bounded mean on both signs of the short lags -/

namespace JointDickman
open Finset

noncomputable def nonzeroShortLags (H : ℕ) : Finset ℤ := (Icc (-(H : ℤ)) H).erase 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLagRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short additive lags have a uniformly small total contribution -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def graphEnergyWithoutShortLags (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (F : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Icc (-(T : ℤ)) T\nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockEndpointLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint cost of averaging the actual graph over finite blocks -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The coefficient is precisely the fraction of origins retaining both endpoints. -/
noncomputable def blockWeightedGraphEnergy (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) : ℝ :=
  ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
    (1-(j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact counting of translated pairs inside integer blocks -/

namespace JointDickman
open Finset

noncomputable def blockOverlap (M : ℕ) (j : ℤ) : Finset ℤ :=
  (Icc 1 (M : ℤ)).filter (fun i => i+j ∈ Icc 1 (M : ℤ))

noncomputable def blockOrigins (M V : ℕ) : Finset ℤ := Icc (1-(M : ℤ)) V

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact block averaging and reindexing into square matrices -/

namespace JointDickman
open Finset

noncomputable def finiteBlockAverage (M V : ℕ) (J : Finset ℤ)
    (K : ℤ → ℤ → ℝ) : ℝ :=
  (∑ s ∈ blockOrigins M V, ∑ j ∈ J, ∑ i ∈ blockOverlap M j,
    if s+i ∈ Icc 1 (V : ℤ) then K j (s+i) else 0)/(M : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite block expression for the arithmetic graph energy -/

namespace JointDickman
open Finset

noncomputable def arithmeticVertexCorrelation (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) (j n : ℤ) : ℝ :=
  (rawArithmeticGraphKernel B L τ C T N j n.toNat *
    (star (F n.toNat)*F ((n.toNat : ℤ)+j).toNat).re)/((B : ℝ)*T*N)

noncomputable def arithmeticBlockAverage (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) : ℝ :=
  finiteBlockAverage M (arithmeticGraphVertexCap B N)
    (nonzeroShortLags T \ nonzeroShortLags H)
    (arithmeticVertexCorrelation B L τ C T N F)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockMatrixIndices
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block positions as a finite matrix index type -/

namespace JointDickman
open Finset

def blockIndexEquiv (M : ℕ) : Fin M ≃ (Icc (1 : ℤ) M) where
  toFun i := ⟨(i.val : ℤ)+1, mem_Icc.mpr ⟨by omega,by have h := i.isLt; omega⟩⟩
  invFun i := ⟨(i.val-1).toNat,by have h := mem_Icc.mp i.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; have h := mem_Icc.mp i.property; dsimp; omega

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual block energy as a quadratic form of a finite matrix -/

namespace JointDickman
open Finset

noncomputable def arithmeticBlockMatrix (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (s : ℤ) (i k : Fin M) : ℝ :=
  let j := ((k.val : ℤ)+1)-((i.val : ℤ)+1)
  let n := s+((i.val : ℤ)+1)
  if j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
      n ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
    rawArithmeticGraphKernel B L τ C T N j n.toNat/((B : ℝ)*T*N)
  else 0

noncomputable def blockLabels (M : ℕ) (s : ℤ) (F : ℕ → ℂ) (i : Fin M) : ℂ :=
  F (s+((i.val : ℤ)+1)).toNat

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticKernelPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary long means of the actual candidate fluctuation kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def residueCandidateCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (a : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  actualCandidateCutError B L T H M τ C χ a.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateFiniteCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting-scale edge condition is a single monotone cutoff -/

namespace JointDickman
open Finset Classical

noncomputable def finiteCandidateCutoff {M : ℕ} (B T N u : ℕ)
    (e : BlockCandidateIndex M) : ℝ :=
  if candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1) then
    candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteCutoffProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite interval profiles for the original graph cutoffs -/

namespace JointDickman
open Finset Classical

noncomputable def primeCandidatePool (B M : ℕ) : Finset (BlockCandidateIndex M) :=
  univ ×ˢ ((auxiliaryPrimes B).powerset ×ˢ (auxiliaryPrimes B).powerset)

noncomputable def finiteCutProfile (B M N u : ℕ) : primeCandidatePool B M → Bool :=
  fun e => decide (candidateQuotient e.val*(u+(e.val.1.1.val+1)) < candidateLow e.val*(N+1))

noncomputable def profileCandidateCutoff (B T M : ℕ) (s : primeCandidatePool B M → Bool)
    (e : BlockCandidateIndex M) : ℝ :=
  if he : e ∈ primeCandidatePool B M then
    if s ⟨e,he⟩ then candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e else 0
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteGraphKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both orientations of the original finite graph kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteGraphKernel (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) : ℝ :=
  if H < ((k.val : ℤ)-i.val).natAbs then
    rawArithmeticGraphKernel B L τ C T N ((k.val : ℤ)-i.val) (u+(i.val+1))/(B : ℝ)
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphSquareRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing square-hit blocks from the original finite graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteGraphCandidateError (B L T H M N u : ℕ) (τ C : ℝ) : ℝ :=
  kernelCutNorm (fun i k => finiteGraphKernel B L T H M N u τ C i k-
    actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k)

noncomputable def finiteGraphLatentError (B L T H M N u : ℕ) (τ C : ℝ) : ℝ :=
  kernelCutNorm (fun i k => finiteGraphKernel B L T H M N u τ C i k-
    latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u) i k)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSquarePeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary long means of square-hit blocks -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def blockSquareWeight (B M u : ℕ) : ℝ :=
  (B : ℝ)^10*(if BlockSquareHit B M u then 1 else 0)

noncomputable def residueBlockSquareWeight (B M : ℕ) (r : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  blockSquareWeight B M r.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPolynomialFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite polynomial smooth weight has a finite prime-site kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

noncomputable def weightedPolynomialTermKernel (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  primeCoarseKernel m B
    (geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
      (endpointSpatialWeight m B t (T/j)
        (fun k => (r k*(P.coeff d*(s k)^(d 3)))*
          coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))))

noncomputable def weightedPolynomialPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ)
    (x y : auxiliaryPrimes B → Bool) : ℝ :=
  ∑ d ∈ P.support, weightedPolynomialTermKernel P d (m d) B j (c d) (H d) T t S s r x y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PolynomialTermLagVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lag variation of the polynomial model's finite coefficients -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def weightedTermCoefficient (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) (a b : Fin m) : ℝ :=
  primeCoarseCoefficient m B
    (geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
      (endpointSpatialWeight m B t (T/j)
        (fun k => (r k*(P.coeff d*(s k)^(d 3)))*
          coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2)))) a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingRamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A continuous approximation of the actual counting-scale cutoff -/

namespace JointDickman
open Finset

noncomputable def countingRamp (δ s x : ℝ) : ℝ := averagingRamp s (s+δ) x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingTensorProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The continuous profile for the counting-scale restriction -/

namespace JointDickman
open scoped Topology

noncomputable def countingTensorProfile (δ : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  amplificationSpatialProfile (v 0) (v 1) (v 2)*countingRamp δ (v 3) (v 1/v 2)

noncomputable def countingBoxWeight (B : ℕ) (δ s σ x y z : ℝ) : ℝ :=
  amplificationBoxWeight B s x y z*countingRamp δ σ (y/z)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingDyadicIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recover the unpartitioned arithmetic sum with its counting ramp -/

namespace JointDickman
open Finset

noncomputable def rampedAmplificationArithmeticSum (B j : ℕ) (T : ℝ) (U V : ℕ)
    (δ σ : ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    amplificationArithmeticTerm B j T g h c b a*countingRamp δ σ (b/(T*c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingArithmeticFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original amplification arithmetic sum has a bounded finite-feature kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def countingPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  weightedPolynomialPrimeKernel P m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun _ => σ)
    (fun k => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCoefficientRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coefficients of the actual counting model and their regularity -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def countingTermCoefficient (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T σ : ℝ) (a b : Fin m) : ℝ :=
  weightedTermCoefficient P d m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun _ => σ) (fun k => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)) a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FairLaplaceFeature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair-split Laplace features are finite-prime multiplicative weights -/
namespace JointDickman
open Finset Classical

noncomputable def primeLaplaceFeature (Q : Finset ℕ) (B v : ℝ) (x : Q → Bool) : ℝ :=
  ∏ p : Q, if x p then (1+(p.val : ℝ)^(-v/B))/2 else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDistanceInput
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published Dirichlet-character distance estimate

Only the fixed-modulus consequence of Klurman--Mangerel--Teräväinen,
*Multiplicative functions in short arithmetic progressions*, Proc. London
Math. Soc. 127 (2023), 366--446, Lemma 7.8, is assumed here. That lemma
bounds the infimum over `|t| ≤ 10X` by
`(1/4) log (log X / log (2 conductor χ)) + O(1)`.
For a fixed character the conductor term is absorbed in the constant.
The primes dividing the modulus only add nonnegative terms to our distance.
No modified character, bin label, or short average occurs in this input.
Source: https://doi.org/10.1112/plms.12546, arXiv:1909.12280, Lemma 7.8.
-/
namespace JointDickman
open Classical

noncomputable def characterArithmetic {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else χ (n : ZMod q),by simp⟩

open Filter PublishedInputs
open scoped Topology

def CharacterDistanceDivergence : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ R : ℝ, ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, |t| ≤ X →
      R ≤ primeDistanceSquared (characterArithmetic χ) X t


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrincipalBinRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Principal characters are exact finite-prime restrictions -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def coprimePrimeWeight (P : Finset ℕ) (t : ℕ → ℝ) (q : ℕ) : ArithmeticFunction ℝ :=
  finitePrimeWeight (P ∪ q.primeFactors) (fun p => if p ∈ q.primeFactors then 0 else t p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeFeatureShortError
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing prime features inside centered bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

noncomputable def primeSiteWeight (Q : Finset ℕ) (F : (Q → Bool) → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else F (fun p => decide (p.val ∣ n)),by simp⟩

@[simp] theorem primeSiteWeight_apply (Q : Finset ℕ) (F : (Q → Bool) → ℝ)
    {n : ℕ} (hn : n ≠ 0) : primeSiteWeight Q F n = F (fun p => decide (p.val ∣ n)) := by
  simp [primeSiteWeight,hn]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FixedResidueReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dividing a residue class and its averaging interval by a fixed divisor -/
namespace JointDickman
open Finset Classical

noncomputable def residueBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) (H z : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0)/(H : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseFeatureAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse features are conditional averages of fixed logarithmic intervals -/
namespace JointDickman
open Finset Classical

noncomputable def coarseLogTest {m : ℕ} (d : Fin m) (s : ℝ) : ℝ :=
  if s ∈ Set.Ioc (channelLower m d) (channelUpper m d) then 1/channelMesh m else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogIntervalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial approximation of fixed logarithmic interval tests -/
namespace JointDickman
open Finset Classical
open scoped Topology

noncomputable def logIntervalRamp (a b δ t : ℝ) : ℝ :=
  averagingRamp (Real.exp (-(b+δ))) (Real.exp (-b)) t -
    averagingRamp (Real.exp (-a)) (Real.exp (-(a-δ))) t

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteConvolutionShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short translations of a finite convolution with small coefficient variation -/
namespace JointDickman
open Finset Classical

noncomputable def finiteConvolution (K : ℕ → ℝ) (g : ℕ → ℂ) (N v : ℕ) : ℂ :=
  ∑ j ∈ range N, (K j : ℂ)*g (v+j)

noncomputable def finiteCoefficientVariation (K : ℕ → ℝ) (N : ℕ) : ℝ :=
  |K 0|+|K N|+∑ j ∈ range N, |K j-K (j+1)|

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PeriodicConvolutionSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothing a periodic lag factor along its residue class -/
namespace JointDickman
open Finset Classical

noncomputable def residueSmoothed (g : ℕ → ℂ) (q R n : ℕ) : ℂ :=
  (∑ h ∈ range R, g (n+q*(h+1)))/(R : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TruncatedCoefficientVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total variation of the cut-off lag coefficients -/
namespace JointDickman
open Finset Classical

noncomputable def cutLagWeight (H T : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  if H < j ∧ j < T then w j else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientProductTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A mean approximation of the totient ratio by finitely many prime factors -/
namespace JointDickman
open Finset Classical

noncomputable def totientLocalProduct (Y n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Y, if p ∣ n then 1+1/((p : ℝ)-1) else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SingularSeriesPeriodic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic finite-factor approximation to the lag singular series -/
namespace JointDickman
open Finset Classical

noncomputable def periodicSingularSeries (Y Q n : ℕ) : ℝ :=
  totientLocalProduct Y n * ∑ q ∈ range Q, singularSeriesCoefficient n q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductGcdError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing GCD restrictions on two independent selected prime products

The probability of a common selected prime is bounded by the sum of the
products of the two marginal hit probabilities. For the independent
`1/(2p)` selection laws this is at most `1/(4N)` when all allowed primes
exceed `N`. The same bound controls any bounded test of the selected pair.
-/

namespace JointDickman

open Finset PublishedInputs

noncomputable def primeSubsetPairMass (P : Finset ℕ) (q r : ℕ → ℝ)
    (x : P.powerset × P.powerset) : ℝ :=
  bernoulliSubsetMass P q x.1.val * bernoulliSubsetMass P r x.2.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LowAdditionSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic sieve for the decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def lowAdditionProgressionWeight (B : ℕ) (g : ℝ)
    (e j b z₀ : ℕ) (c₀ : ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
    residueWeight q 0 ((z₀ : ZMod p)+j*n)*residueWeight (1/2) 0 ((c₀ : ZMod p)-e*n))/
      ((z₀ : ℝ)+(j : ℝ)*n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowNumericAdditionClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Squarefree low-endpoint additions on a decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def lowNumericAdditionClass (B L : ℕ) (τ C : ℝ)
    (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (auxiliaryPrimes B).powerset.filter (fun Z => Z.card = d ∧
    W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
    ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p)+j*c = b ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowAdditionAvailability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-remainder availability for the large low-endpoint addition -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def availableLowNumericAdditionClass (B L k : ℕ) (τ C : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (lowNumericAdditionClass B L τ C e j b d W).filter (fun Z =>
    Z ⊆ auxiliaryPrimes B \ A ∧
    (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
    Z ⊆ primePrefix B ((k : ℝ)/L) Z)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active low-addition classes at the actual coefficient ratio -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def activeLowAdditionClass (B L k : ℕ) (τ C Δ : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) : Finset (Finset ℕ) :=
  if (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b then
    availableLowNumericAdditionClass B L k τ C A e j b d (highAdditionWindow e b)
  else ∅

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAlternativePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual pairs with a large addition at the low endpoint -/

namespace JointDickman
open Finset Classical

noncomputable def largeLowAlternativePairs (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      (XY.1 \ A).card = d ∧ (XY.2 \ D).card = f ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.2, p : ℕ) ≤ 2*(∏ p ∈ XY.1, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p)+j*c = (∏ p ∈ XY.2, p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowCardinalityPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning all large low-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

noncomputable def allLargeLowAlternativePairs (B L k j : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.2, p : ℕ) ≤ 2*(∏ p ∈ XY.1, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p)+j*c = (∏ p ∈ XY.2, p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularTiltAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tilted remainder averages with the regularity event retained -/

namespace JointDickman
open Finset Classical

noncomputable def regularTiltAverage (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (F : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
      if RegularPrimeSet B L τ C U then F U else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CandidateCoefficientFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the deterministic and remainder factors of a candidate -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCoefficientFactor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) : ℝ :=
  (regularCoefficientWeight B L τ C (candidateLow e)*
    regularCoefficientWeight B L τ C (candidateHigh e)*
    regularCoefficientWeight B L τ C (candidateQuotient e))/(B : ℝ)*χ e*
      independentRootMean B L τ C

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateScalarIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the arithmetic scalar with an admissible candidate -/

namespace JointDickman
open Finset


open Classical in
noncomputable def regularCandidateScalar {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  if BlockCandidateAdmissible B L T H τ C e then
    regularCoefficientWeight B L τ C (candidateQuotient e)*
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateScalarSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the unique additive coefficient in the candidate kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def regularArithmeticScalar (B L j : ℕ) (τ C : ℝ) (T : ℕ)
    (c b a : ℕ) : ℝ :=
  if b.Coprime a ∧ RegularPrimeSet B L τ C (coefficientPrimeSet B c) then
    amplificationScalarWeight B j T c b a else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RemainderKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing remainder regularity in the actual finite retention kernel -/

namespace JointDickman
open Finset

noncomputable def retainedSubsetKernel (P : Finset ℕ) (F : Finset ℕ → Finset ℕ → ℝ)
    (S R : Finset ℕ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, subsetRetentionMass S A*subsetRetentionMass R D*F A D

open Classical in
noncomputable def regularRemainderKernel (B L : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) (S R : Finset ℕ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D) then
      subsetRetentionMass S A*subsetRetentionMass R D*F A D else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRetentionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The candidate coefficient weight for the remainder-regularity estimate -/

namespace JointDickman
open Finset

open Classical in
noncomputable def candidateRetainedWeight (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (A D : Finset ℕ) : ℝ :=
  if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then
    B*∑ c ∈ Ioc 0 V, regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p)
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularizedProductWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient-regularized product weight in the candidate mean -/

namespace JointDickman
open Finset

open Classical in
noncomputable def regularizedProductWeight (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (a b : ℕ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, if coefficientTripleRegular B L τ C a b c then
    amplificationScalarWeight B j T c b a else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampedCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual candidate cutoff and its ramped arithmetic counterpart -/
namespace JointDickman
open Finset

noncomputable def rampedCandidateCutoff {M : ℕ} (B T : ℕ) (δ σ : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
    countingRamp δ σ ((candidateLow e : ℝ)/(T*candidateQuotient e))

noncomputable def rampedProductCutoff (T j : ℕ) (δ σ : ℝ) (a b : ℕ) : ℝ :=
  countingRamp δ σ ((b : ℝ)/(T*((a-b)/j : ℕ)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SubsetPrimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a finite prime-feature model to endpoint subsets -/
namespace JointDickman
open Finset Classical

noncomputable def subsetPrimeModel (B : ℕ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ)
    (S R : Finset ℕ) : ℝ :=
  K (fun p => decide (p.val ∈ S)) (fun p => decide (p.val ∈ R))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCandidateModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite prime-feature model for each ramped candidate entry -/
namespace JointDickman
open Finset

noncomputable def countingCandidateModel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ)
    (S R : Finset ℕ) : ℝ :=
  (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*
    subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c H T σ y x) S R

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The symmetric finite-feature block model and its lag envelope -/
namespace JointDickman
open Finset Classical

noncomputable def countingSiteModel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  if i < k then
    if H < k.val-i.val ∧ k.val-i.val < T then
      countingCandidateModel P m B L (k.val-i.val) τ C c D T σ a.val b.val else 0
  else if k < i then
    if H < i.val-k.val ∧ i.val-k.val < T then
      countingCandidateModel P m B L (i.val-k.val) τ C c D T σ b.val a.val else 0
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagEnvelopeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row moments of the deterministic singular-factor envelope -/
namespace JointDickman
open Finset Classical PublishedInputs

noncomputable def lagEnvelope {M : ℕ} (T : ℕ) (D : ℝ) (i k : Fin M) : ℝ :=
  if i ≠ k ∧ Nat.dist i.val k.val < T then D/(T : ℝ)*singularFactor 24 (Nat.dist i.val k.val) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingPeriodicModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the singular series in the actual finite-feature graph -/
namespace JointDickman
open Finset Classical

noncomputable def countingCandidateWithSeries (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) (S R : Finset ℕ) : ℝ :=
  (independentRootMean B L τ C*(F j/(j : ℝ)))*
    subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c D T σ y x) S R

noncomputable def countingSiteWithSeries (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  if i < k then
    if H < k.val-i.val ∧ k.val-i.val < T then
      countingCandidateWithSeries F P m B L (k.val-i.val) τ C c D T σ a.val b.val else 0
  else if k < i then
    if H < i.val-k.val ∧ i.val-k.val < T then
      countingCandidateWithSeries F P m B L (i.val-k.val) τ C c D T σ b.val a.val else 0
  else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingForwardRows
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The periodic graph row as a finite-feature convolution -/
namespace JointDickman
open Finset Classical

noncomputable def countingForwardRow (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) : ℂ :=
  ∑ k : Fin M, if i < k then
    (countingSiteWithSeries F P m B L T H M τ C c D σ i k
      ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩
      ⟨coefficientPrimeSet B (u+(k.val+1)),by simp [coefficientPrimeSet]⟩ : ℂ)*
      star (z (u+(i.val+1)))*z (u+(k.val+1)) else 0

noncomputable def countingTermRow (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B T H M u : ℕ) (c : ℕ → ℝ) (D : ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) (a b : Fin m) : ℂ :=
  ∑ j ∈ range (T+1),
    ((cutLagWeight H (min T (M-i.val)) (fun k =>
      countingTermCoefficient P d m B k c D T σ a b/(k : ℝ)) j : ℝ) : ℂ)*(F j : ℂ)*
    (z (u+(i.val+1)+j)*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B a) (u+(i.val+1)+j) : ℂ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingFeatureRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single finite index for the actual counting-model row -/
namespace JointDickman
open Finset Classical

abbrev CountingFeatureIndex (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) :=
  Σ d : P.support, Fin (m d.val) × Fin (m d.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ForwardQuadraticEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a symmetric quadratic form from its forward rows -/
namespace JointDickman
open Finset Classical

noncomputable def forwardKernelRow {M : ℕ} (K : Fin M → Fin M → ℝ)
    (z : Fin M → ℂ) (i : Fin M) : ℂ :=
  ∑ k, if i < k then (K i k : ℂ)*star (z i)*z k else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingPeriodicEnergy
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the actual periodic finite graph -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def countingArithmeticKernel (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) : ℝ :=
  countingSiteWithSeries F P m B L T H M τ C c D σ i k
    ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩
    ⟨coefficientPrimeSet B (u+(k.val+1)),by simp [coefficientPrimeSet]⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingApplicationScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scales used to apply the counting model -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def countingSmoothingLength (B : ℕ) : ℕ := ⌊(B : ℝ)^(1/10 : ℝ)⌋₊
noncomputable def countingMajorDenominator (B : ℕ) : ℕ := ⌈(B : ℝ)^(2/5 : ℝ)⌉₊

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingOriginParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving block origin is a bounded, slowly varying parameter -/
namespace JointDickman
open Finset Classical

noncomputable def countingOriginParameter (T N u : ℕ) : ℝ :=
  min 3 ((u : ℝ)/((T : ℝ)*(N+1)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingErrorRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing error profile for the counting candidate comparison -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def countingErrorRate (R Kr Kc Kp η : ℝ)
    (er ec ep ef : ℕ → ℝ) (B : ℕ) : ℝ :=
  R*(Kr*(er B+1)*|ep B|+
    (amplificationMultiplier B : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)))+
    Kc*ec B+|ef B|+(Kr*Kp/η)*er B)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateExpectedDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform conditional degrees of the actual latent graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def latentPrimeSiteKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M)
    (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  candidateSiteKernel B L T H M τ C χ i k a.val b.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstPairMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining mass of first coefficient pairs -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidateFirstPairMass (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
    if BlockCandidateAdmissible B L T H τ C ((i,t),ab) then
      candidateCoefficientFactor B L τ C χ ((i,t),ab)*
      (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
      (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ)) else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Using the tilted multiplicity estimate after fixing a first pair -/

namespace JointDickman
open Finset Classical

noncomputable def candidateMultiplicityMoment (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
    (candidatePairRepresentations B L T H τ C i t S R).card*
    candidateSiteKernel B L T H M τ C χ i t S R

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated square of an actual latent edge -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidateSquareMoment (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      (candidateSiteKernel B L T H M τ C χ i t S R)^2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same independent endpoint tests in subset and Boolean coordinates -/
namespace JointDickman
open Finset Classical

noncomputable def extendSubsetTest (B : ℕ) (g : (auxiliaryPrimes B).powerset → ℝ)
    (x : auxiliaryPrimes B → Bool) : ℝ :=
  g ((subsetHitEquiv (auxiliaryPrimes B)).symm x)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single good event for degrees and total square mass -/

namespace JointDickman
open Finset Classical
open PublishedInputs

noncomputable def siteTotalSquare {ι A : Type*} [Fintype ι]
    (K : ι → ι → A → A → ℝ) (x : ι → A) : ℝ :=
  ∑ i, ∑ j, (K i j (x i) (x j))^2

/-- The one common event used before taking a finite union of concentration
tails. Its complement is charged once, not once per column sample. -/
def SiteKernelGood {ι A : Type*} [Fintype ι]
    (E H : ι → ι → A → A → ℝ) (d Q : ℝ) (x : ι → A) : Prop :=
  (∀ i, siteRowSum H i x ≤ d) ∧ siteTotalSquare E x ≤ Q

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FrozenSiteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on a fixed collection of sampled sites -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Sampled coordinates are fixed; every other coordinate keeps its law. -/
noncomputable def frozenSiteMass (p : ι → A → ℝ) (J : Finset ι) (t : ι → A)
    (i : ι) (a : A) : ℝ :=
  if i ∈ J then if a = t i then 1 else 0 else p i a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_MaskedSiteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleting the sampled sites preserves the moment bounds -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def maskedSiteKernel (J : Finset ι) (K : ι → ι → A → A → ℝ)
    (i j : ι) (a b : A) : ℝ :=
  if i ∉ J ∧ j ∉ J then K i j a b else 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SiteTestRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single-site tests after fixing sampled coordinates -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def maskedSiteTest (J : Finset ι) (g : ι → A → ℝ) (i : ι) (a : A) : ℝ :=
  if i ∈ J then 0 else g i a

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block test estimate for the actual counting-feature error -/
namespace JointDickman
open Finset Classical PublishedInputs

noncomputable def countingSiteError (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k a b-
    countingSiteModel P m B L T H M τ C c D σ i k a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive sampling envelope for the latent-minus-model error -/
namespace JointDickman
open Finset PublishedInputs

noncomputable def addLagEnvelope {M : ℕ} {A : Type*}
    (K : Fin M → Fin M → A → A → ℝ) (T : ℕ) (D : ℝ)
    (i k : Fin M) (a b : A) : ℝ := K i k a b+lagEnvelope T D i k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingArithmeticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of the counting-model error to actual integer sites -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def arithmeticSiteCutMean {B M : ℕ}
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ) : ℝ :=
  arithmeticSquareMean B (fun u => kernelCutNorm
    (realizedSiteKernel K (blockPatternEquiv B M (arithmeticPrimePatterns B M u))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact error when the finite counting cutoff is replaced by its ramp -/
namespace JointDickman
open Finset

noncomputable def smoothCandidateCutoff {M : ℕ} (B T : ℕ) (e : BlockCandidateIndex M) : ℝ :=
  candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointCountingCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the exact endpoint cutoff to the common block-scale ramp -/
namespace JointDickman
open Finset

noncomputable def endpointRampedCutoff {M : ℕ} (B T N u : ℕ) (δ : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  rampedCandidateCutoff B T δ (((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))) e

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicCandidateCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic averaging of the error for each actual candidate representation -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def baseCandidateContribution (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (u : ℕ) : ℝ :=
  if e ∈ blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) then
    candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (smoothCandidateCutoff B T) e else 0

noncomputable def residueBaseContribution (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (r : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  baseCandidateContribution B L T H M τ C e r.val

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteRampMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaged error mass of the hard counting cutoff over the finite candidate pool -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointRampErrorMass (B L T H M N u : ℕ) (τ C δ : ℝ) : ℝ :=
  ∑ e ∈ primeCandidatePool B M, baseCandidateContribution B L T H M τ C e u*
    |(if ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) <
        (candidateLow e : ℝ)/(T*candidateQuotient e) then 1 else 0)-
      countingRamp δ (((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)))
        ((candidateLow e : ℝ)/(T*candidateQuotient e))|

noncomputable def baseCandidateMassMean (B L T H M : ℕ) (τ C : ℝ) : ℝ :=
  ∑ e ∈ primeCandidatePool B M,
    (∑ r, residueBaseContribution B L T H M τ C e r)/(auxiliarySquarePeriod B : ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSlowMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the periodic sampling error to the moving counting scale -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def countingArithmeticCutError (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) (u : ℕ) : ℝ :=
  kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D σ)
    (blockPatternEquiv B M (arithmeticPrimePatterns B M u)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteRampApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the exact counting cutoff by a common block-origin ramp -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteRampCutError (B L T H M N u : ℕ) (τ C δ : ℝ) : ℝ :=
  kernelCutNorm (fun i k =>
    latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (finiteCandidateCutoff B T N u) i k-
    latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinDecorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered bin labels at consecutive integers decorrelate -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def centeredBinCorrelation {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (k₁ : ι → ℕ) (z₁ : ι → ℂ) (J₂ : ℕ)
    (z₂ : Fin (J₂-1) → ℂ) (μ : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, star (movingBinLabel J₁ k₁ z₁ N n) *
    (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ N (n+1)-μ))/(N : ℂ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteStatistics
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite character tests determine joint statistics

This is the finite Fourier inversion step in `sections/distribution.tex`.
It is an algebraic transfer lemma, not an assumed arithmetic decorrelation
result. The arithmetic correlation limits still have to be established.
-/

open Filter Finset Module
open scoped Topology

namespace JointDickman

/-- The product of the two marginal statistics. -/
noncomputable def productMean {G H : Type*}
    (μ : (G → ℂ) →ₗ[ℂ] ℂ) (ν : (H → ℂ) →ₗ[ℂ] ℂ) :
    (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g => μ f * ν g
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [mul_left_comm] }
  map_add' f g := by ext h; simp [add_mul]
  map_smul' c f := by ext h; simp [mul_assoc]

/-- The ordinary empirical joint statistic; `s` is the counting range and
`w` is the normalization. The observations may depend on the scale. -/
noncomputable def jointStatistic {G H : Type*} (s : Finset ℕ) (w : ℂ)
    (u : ℕ → G) (v : ℕ → H) :
    (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g => w * ∑ n ∈ s, f (u n) * g (v n)
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm] }
  map_add' f g := by ext h; simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by ext h; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_BinCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characters of the finite bin-count group are unit bin labels -/
namespace JointDickman
open Finset Classical
open scoped Fin.NatCast

noncomputable def binCharacterNodes {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (i : Fin (J-1)) : ℂ := χ (Pi.single i 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinJointEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Fourier inversion gives every joint bin event -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def higherBinEvent (J k : ℕ) (r : BinCountState J) : Prop :=
  ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinApplicationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Qualitative application scales for the multiscale energy bound

The large fixed logarithmic exponent pays the explicit factorial budget.
The application needs only a vanishing error as the short length grows.
-/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

noncomputable def mellinFirstPrime (H : ℝ) : ℝ := (Real.log H)^(300000 : ℝ)
noncomputable def mellinLastPrime (H : ℝ) : ℝ := H^(1/2 : ℝ)
noncomputable def mellinResolution (H : ℝ) : ℝ :=
  mrtBaseResolution (mellinFirstPrime H) (mellinLastPrime H) (1/12)

noncomputable def mellinWindowCost (H : ℝ) : ℝ :=
  2816*Real.exp 1*(H⁻¹+1)*(8/(mellinFirstPrime H)+4/(mellinResolution H)) +
  1024*Real.exp 2*(mellinLastPrime H/H+1)/(mellinResolution H) +
  2*(H⁻¹+1)/(mellinFirstPrime H)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CanonicalAffineCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant and linear frequency costs in the canonical estimate -/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

noncomputable def canonicalAffineBase (C H : ℝ) : ℝ :=
  5632*Real.exp 1*(8/mellinFirstPrime H+4/mellinResolution H)+
    2048*Real.exp 2/mellinResolution H+4/mellinFirstPrime H+
    96*Real.exp 1*C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)

noncomputable def canonicalAffineSlope (C H : ℝ) : ℝ :=
  5632*Real.exp 1*(8/mellinFirstPrime H+4/mellinResolution H)+
    2048*Real.exp 2*mellinLastPrime H/mellinResolution H+4/mellinFirstPrime H+
    48*Real.exp 1*C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteHoeffding
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite weighted Hoeffding inequality -/
namespace JointDickman
open Finset MeasureTheory ProbabilityTheory

noncomputable def finiteMassLaw {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hone]
    simp)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HalfArithmetic
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a two-bounded arithmetic coefficient for the analytic transfer -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

noncomputable def halfArithmetic (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n/2,by simp⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_MainStatements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The joint Dickman law and strict ordering densities

The moving smoothness thresholds for both consecutive integers use the base `n`.
Counting is ordinary natural density through real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

/-- Theorem 1 (`thm:main`): the moving-threshold joint Dickman law, through
all real endpoints with ordinary counting. Both powers use the base `n`. -/
def JointDickmanLaw : Prop :=
  ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
    Tendsto (realDensity (movingEvent a b)) atTop
      (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b)))

/-- Corollary 2 (`cor:comparison`), first strict ordering. -/
def IncreasingOrderLaw : Prop :=
  Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
    atTop (𝓝 (1 / 2))

/-- The reverse ordering has the same density. -/
def DecreasingOrderLaw : Prop :=
  Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
    atTop (𝓝 (1 / 2))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MovingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From rational fixed thresholds to the manuscript's main limit

Rational approximation compares fixed-scale thresholds with moving
thresholds and extends the counting limit to real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def fixedDensity (a b : ℝ) (N : ℕ) : ℝ :=
  (empiricalCount (fixedScaleEvent a b N) N : ℝ) / N

/-- The joint limit for rational fixed-scale thresholds. -/
def RationalFixedScaleLaw : Prop :=
  ∀ c d : ℚ, 0 < c → c < 1 → 0 < d → d < 1 →
    Tendsto (fixedDensity c d) atTop (𝓝 (dickmanCDF c * dickmanCDF d))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_Ordering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The ordering corollary of the joint Dickman law

The proof uses disjoint strips between interior quantiles of the continuous
Dickman distribution. Every strip is a difference of two rectangles appearing
in the main theorem. No weak-convergence or boundary-event hypothesis is used.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

/-- The normalized rectangle has exactly the same count as the paper's
moving-power event. -/
def normalizedRectangle (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n n ≤ a ∧ normalizedPrimeFactor n (n + 1) ≤ b

/-- A horizontal strip below the strict ordering diagonal. -/
def increasingStrip (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n n ≤ a ∧
    a < normalizedPrimeFactor n (n + 1) ∧ normalizedPrimeFactor n (n + 1) ≤ b

/-- The reflected strip above the strict ordering diagonal. -/
def decreasingStrip (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n (n + 1) ≤ a ∧
    a < normalizedPrimeFactor n n ∧ normalizedPrimeFactor n n ≤ b

/-- The mass of the finite disjoint strip approximation. -/
noncomputable def orderingGridMass (m : ℕ) : ℝ :=
  ((m : ℝ) / (m + 2)) * (((m : ℝ) + 1) / (m + 2)) / 2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.ResidueCalcOnRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaContourRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative zero-free region for the finite contour

The logarithmic ninth-power zero-free region suffices for fixed-order
contour estimates.
-/
namespace JointDickman
open Set

noncomputable def zetaContourWidth (A T : ℝ) : ℝ := A/(1+Real.log (T+3))^9

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRectangleLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic logarithms on the character zero-free rectangles -/
namespace JointDickman
open Set

noncomputable def characterContourWidth (A ε : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  A * (((q:ℝ)+2)*(T+2))^(-ε)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic cancellation in the squarefree Euler logarithm -/
namespace JointDickman

noncomputable def squarefreeEulerLog (z : ℝ) (w : ℂ) : ℂ :=
  Complex.log (1+(z:ℂ)*w)+(z:ℂ)*Complex.log (1-w)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent Euler correction for squarefree character sums -/
namespace JointDickman

noncomputable def characterPrimePower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (p : Nat.Primes) : ℂ := χ (p.val : ZMod q) * (p.val:ℂ)^(-s)

noncomputable def squarefreeCharacterPrimeLog {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  squarefreeEulerLog z (characterPrimePower χ s p)

noncomputable def squarefreeCharacterLogFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) : ℂ := ∑' p : Nat.Primes, squarefreeCharacterPrimeLog χ z s p

noncomputable def squarefreeCharacterAnalyticFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) : ℂ := Complex.exp (squarefreeCharacterLogFactor χ z s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic factorization of the twisted squarefree Dirichlet series -/
namespace JointDickman

noncomputable def primeCharacterLog {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1-characterPrimePower χ s p)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the continued character series on the Perron line -/
namespace JointDickman
open Set

noncomputable def characterContourSeries {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*f s)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterEulerRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear prime sum in a character Euler logarithm

The nonlinear Euler terms have one absolute summable majorant throughout
Re(s) > 1, independent of both the character and its modulus.
-/
namespace JointDickman
open Complex

noncomputable def primeCharacterLinearSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, characterPrimePower χ s p

noncomputable def primeEulerRemainderConstant : ℝ :=
  ∑' p : Nat.Primes, 2 * (p.val : ℝ)^(-2:ℝ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPrimeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing finite character distances with damped prime sums -/
namespace JointDickman
open Complex Finset
open scoped BigOperators

noncomputable def characterPrimePhase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  χ (p.val : ZMod q)*Complex.exp (-((t*Real.log p.val:ℝ):ℂ)*Complex.I)

noncomputable def primeCutoff (X : ℝ) : Finset Nat.Primes :=
  (Icc 2 ⌊X⌋₊).subtype Nat.Prime

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalPowerBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two boundary values on the fractional-power branch cut -/
namespace JointDickman
open Filter Set
open scoped Topology

noncomputable def fractionalPowerKernel (z : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(z:ℂ)*Complex.log w)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalContourRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite rectangles on either side of the fractional-power cut -/
namespace JointDickman
open Complex Set

noncomputable def fractionalContourIntegrand (z : ℝ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  F w * fractionalPowerKernel z w

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factorization of the squarefree Dirichlet series -/
namespace JointDickman

noncomputable def primeZetaLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1-(p.val:ℂ)^(-s))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PrimeZetaPoleLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler logarithm of the pole-removed zeta function -/
namespace JointDickman

noncomputable def primeZetaPoleLog (s : ℂ) : ℂ := primeZetaLog s+Complex.log (s-1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRieszKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular character Riesz kernel and its vertical bound -/
namespace JointDickman
open Complex Set MeasureTheory

noncomputable def characterNormalizedPerron {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) : ℂ :=
  LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w) *
    exp ((L:ℂ)*w) / ((1+w)*(2+w))

noncomputable def characterRieszKernel {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  characterContourSeries χ z f (1+w) * exp ((L:ℂ)*w) / ((1+w)*(2+w))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogRieszDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the logarithmic monomials in the Riesz expansion -/
namespace JointDickman

noncomputable def logRieszMonomial (β x : ℝ) : ℝ := x^2*(Real.log x)^β

noncomputable def logRieszDerivative (β x : ℝ) : ℝ :=
  x*(2*(Real.log x)^β+β*(Real.log x)^(β-1))

noncomputable def logRieszSecondDerivative (β x : ℝ) : ℝ :=
  2*(Real.log x)^β+3*β*(Real.log x)^(β-1)+β*(β-1)*(Real.log x)^(β-2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszLogPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth finite logarithmic polynomials used to remove Riesz smoothing -/
namespace JointDickman
open Finset

noncomputable def rieszLogPolynomial (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszMonomial (z-1-j) x

noncomputable def rieszLogDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszDerivative (z-1-j) x

noncomputable def rieszLogSecondDerivative (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (K+1), b j*logRieszSecondDerivative (z-1-j) x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszUnsmoothCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficients obtained by differentiating a Riesz expansion -/
namespace JointDickman
open Finset

noncomputable def rieszUnsmoothCoefficients (b : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => 2*b 0
  | j+1 => 2*b (j+1)+(z-1-j)*b j

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPerronScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete height and width for fixed-order Perron estimates -/
namespace JointDickman

noncomputable def perronScaleWidth (A q : ℝ) : ℝ :=
  zetaContourWidth A (Real.exp q) / 4

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszPerronLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local expansion at the concrete Perron cutoff -/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

noncomputable def perronLogScaleWidth (A L : ℝ) : ℝ :=
  perronScaleWidth A (L^(1/10:ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePresencePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oscillatory divisor expansion for prime-presence weights -/
namespace JointDickman
open Finset TwoPointCorrelations

noncomputable def primePresence (P : Finset ℕ) (z : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∏ p ∈ P, if p ∣ n then z p else 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal mass of prime products near a cutoff -/
namespace JointDickman
open Finset

noncomputable def reciprocalPrimeTupleTail (P : Finset ℕ) (h : ℕ) (Y N : ℝ) : ℝ := by
  classical
  exact ∑ v ∈ (Fintype.piFinset (fun _ : Fin h => P)).filter
    (fun v => Y < ∏ i, (v i:ℝ) ∧ (∏ i, (v i:ℝ)) ≤ N), 1/(∏ i, (v i:ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSubsetTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutoff tails for the squarefree divisor expansion -/
namespace JointDickman
open Finset

noncomputable def primeSubsetTail (P : Finset ℕ) (Y N : ℝ) : ℝ := by
  classical
  exact ∑ D ∈ P.powerset.filter
    (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N),
      1/(∏ p ∈ D, (p:ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AuxiliaryPowerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional energy on an actual power-scale auxiliary band -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

noncomputable def auxiliarySquareError (α X : ℝ) : ℝ :=
  11264*Real.exp 1*(2/X^α+(2/X^α)^2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteWeightedCoefficient
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coefficient with a fixed finite-prime weight -/
namespace JointDickman
open Finset
open scoped Classical

noncomputable def finiteWeightedCoefficient (f : ArithmeticFunction ℂ)
    (E : Finset ℕ) (w : ℕ → ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n*(finitePrimeWeight E w n:ℂ),by simp⟩

end JointDickman

end OAI
end



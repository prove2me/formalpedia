-- Prove2me | Definitions.Def_OAIQ247J003
-- name    : OAIQ247J003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:39.202702+00:00
-- url     : https://prove2.me/theorems/8f2db5a3-d02e-42d3-bdaa-3c4343df3207
-- title:
--   Definitions bundle OAIQ247J003 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 944 declarations of OpenAI's Lean: 780 definitions, 9 inductive types or structures, 15 instances and 140 theorems. The definitions and types are `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.retainedLength`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszDifferenceWeight`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszProfile`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszRecovery`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszSum`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszWeight`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.sharpSum`, `OAI.Erdos970.ErdosAlignedProgression.parameterCandidates`, `OAI.Erdos970.ErdosAlignedProgression.parameterInterval`, `OAI.Erdos970.ErdosAlignedProgression.parameterLower`, `OAI.Erdos970.ErdosAlignedProgression.parameterOf`, `OAI.Erdos970.ErdosAlignedProgression.parameterUpper`, `OAI.Erdos970.ErdosAlignedProgression.parameterValue`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.IntegerLineIncidence`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.MonomialIndex`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.ResidueSystem`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.boxHeight`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.boxLift`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.constraintMap`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.constraintVolume`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.encode`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.encodeHom`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.evalReal`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.exponent`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.lineSub`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.logarithmicCost`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.logarithmicValueBudget`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.residueFintype`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.residueSlopes`, `OAI.Erdos970.ErdosAuxiliaryPolynomial.valueBudget`, `OAI.Erdos970.ErdosBivariateResultant.Bivariate`, `OAI.Erdos970.ErdosBivariateResultant.beval`, `OAI.Erdos970.ErdosBivariateResultant.commonZeroFinset`, `OAI.Erdos970.ErdosBivariateResultant.commonZeroSet`, `OAI.Erdos970.ErdosBivariateResultant.pointEvalHom`, `OAI.Erdos970.ErdosBivariateResultant.resultantRoots`, `OAI.Erdos970.ErdosBivariateResultant.rootPairs`, `OAI.Erdos970.ErdosBivariateResultant.specialize`, `OAI.Erdos970.ErdosBivariateResultant.verticalRoots`, `OAI.Erdos970.ErdosBivariateResultant.xResultant` and 749 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Jacobsthal_Analysis_BonferroniDensity`, `Jacobsthal_Analysis_BoundaryProductLimit`, `Jacobsthal_Analysis_ContinuousReference`, `Jacobsthal_Analysis_HarmonicReferenceMeasure`, `Jacobsthal_Analysis_JointModelDensity`, `Jacobsthal_Analysis_PairDensityExpansion`, `Jacobsthal_Analysis_SmallModelMeasure`, `Jacobsthal_Analysis_ThirdMovingIntegrals`, `Jacobsthal_Conclusions_IteratedLogScales`, `Jacobsthal_Conclusions_JacobsthalSourceScale`, `Jacobsthal_Conclusions_JacobsthalTerminalScales`, `Jacobsthal_Estimates_ActualCollisionBound`, `Jacobsthal_Estimates_ActualModelTargets`, `Jacobsthal_Estimates_ActualPatternClass`, `Jacobsthal_Estimates_ActualPointSlopes`, `Jacobsthal_Estimates_ActualSourceInverse`, `Jacobsthal_Estimates_ActualUnalignedIncidence`, `Jacobsthal_Estimates_ActualUnitClasses`, `Jacobsthal_Estimates_BivariateCalculus`, `Jacobsthal_Estimates_BivariateMonomialIndex`, `Jacobsthal_Estimates_BonferroniBlocks`, `Jacobsthal_Estimates_CandidateExceptionMass`, `Jacobsthal_Estimates_CoefficientHeightChoice`, `Jacobsthal_Estimates_ConditionalPatternCounts`, `Jacobsthal_Estimates_CorrectionFloorRemainder`, `Jacobsthal_Estimates_DisjointBlockExpansion`, `Jacobsthal_Estimates_EffectiveAvoidance`, `Jacobsthal_Estimates_EffectiveNumerator`, `Jacobsthal_Estimates_EffectiveSurvivors`, `Jacobsthal_Estimates_FactorDividesAbscissa`, `Jacobsthal_Estimates_FiniteMonotoneComparison`, `Jacobsthal_Estimates_FinitePairOccurrence`, `Jacobsthal_Estimates_FiniteSampleSpace`, `Jacobsthal_Estimates_FullEndpointData`, `Jacobsthal_Estimates_FundamentalBlockEstimate`, `Jacobsthal_Estimates_GrowingFarTail`, `Jacobsthal_Estimates_HarmonicConditioning`, `Jacobsthal_Estimates_HeightBlockCount`, `Jacobsthal_Estimates_HypotheticalPairRows`, `Jacobsthal_Estimates_LargeGapCountErrors`, `Jacobsthal_Estimates_LineSubstitution`, `Jacobsthal_Estimates_LocalGraphIff`, `Jacobsthal_Estimates_LossBounds`, `Jacobsthal_Estimates_LowStateHorizon`, `Jacobsthal_Estimates_MarginalGrowth`, `Jacobsthal_Estimates_MovingLocalReference`, `Jacobsthal_Estimates_NonstructuredCounts`, `Jacobsthal_Estimates_OmissionSeries`, `Jacobsthal_Estimates_PairCollisionCount`, `Jacobsthal_Estimates_ParentProgression`, `Jacobsthal_Estimates_PatternMainTerm`, `Jacobsthal_Estimates_PositionDensities`, `Jacobsthal_Estimates_PositiveGapMajorant`, `Jacobsthal_Estimates_PositiveProgression`, `Jacobsthal_Estimates_ProductRestriction`, `Jacobsthal_Estimates_RationalCandidateSets`, `Jacobsthal_Estimates_RealCriticalPoints`, `Jacobsthal_Estimates_RealProgressionPoints`, `Jacobsthal_Estimates_ReciprocalEnvelope`, `Jacobsthal_Estimates_RecoveryScale`, `Jacobsthal_Estimates_ReferenceProductsBasics`, `Jacobsthal_Estimates_ReferenceWeightedQuadrature`, `Jacobsthal_Estimates_RegularImplicitArc`, `Jacobsthal_Estimates_RieszIntegrand`, `Jacobsthal_Estimates_ScalarErrorBudget`, `Jacobsthal_Estimates_ScalarFreeGate`, `Jacobsthal_Estimates_SmallModelSourceScales`, `Jacobsthal_Estimates_SortedRealGaps`, `Jacobsthal_Estimates_SourceCenteredGap`, `Jacobsthal_Estimates_SourceEdgeClasses`, `Jacobsthal_Estimates_SourceInitialDiscard`, `Jacobsthal_Estimates_SourceLargePairBound`, `Jacobsthal_Estimates_SourcePairRemainder`, `Jacobsthal_Estimates_SourceSamplePopulation`, `Jacobsthal_Estimates_UniformJointModel`, `Jacobsthal_Estimates_UniformLower`, `Jacobsthal_Estimates_UnitCyclicBounds`, `Jacobsthal_Estimates_WeightedMonotoneBound`, `Jacobsthal_Harmonic_AuxiliaryPolynomialLifting`, `Jacobsthal_Harmonic_BudgetPolynomialBound`, `Jacobsthal_Harmonic_CharacterChord`, `Jacobsthal_Harmonic_CompactAnomalyTest`, `Jacobsthal_Harmonic_ComplexSquareScaling`, `Jacobsthal_Harmonic_NormalizedSpectralError`, `Jacobsthal_Harmonic_OriginalSourcePolynomial`, `Jacobsthal_Harmonic_PolynomialLocalGraph`, `Jacobsthal_Harmonic_PolynomialStripPoints`, `Jacobsthal_Harmonic_PolynomialValueBound`, `Jacobsthal_Harmonic_PrimitiveResultant`, `Jacobsthal_Harmonic_StationaryPhase`, `Jacobsthal_Harmonic_ZeroFrequencyBounds`, `Jacobsthal_Partitions_ActualBoxFourSum`, `Jacobsthal_Partitions_ActualCoordinateBlocks`, `Jacobsthal_Partitions_ActualPatternCoordinates`, `Jacobsthal_Partitions_BinCutGapMovement`, `Jacobsthal_Partitions_BoundedEdgeBins`, `Jacobsthal_Partitions_BoxInflation`, `Jacobsthal_Partitions_CellLengthLower`, `Jacobsthal_Partitions_CoefficientBoxCollision`, `Jacobsthal_Partitions_CommonCellSum`, `Jacobsthal_Partitions_CommonSliceGeometry`, `Jacobsthal_Partitions_CompletedParentInterval`, `Jacobsthal_Partitions_CrossingBandGeometry`, `Jacobsthal_Partitions_DilationCoordinates`, `Jacobsthal_Partitions_EdgeBinBounds`, `Jacobsthal_Partitions_EffectiveCommonInterval`, `Jacobsthal_Partitions_EffectiveCoordinates`, `Jacobsthal_Partitions_EligibleBoxLists`, `Jacobsthal_Partitions_EvenThresholdGeometry`, `Jacobsthal_Partitions_FiberCardinalityConstancy`, `Jacobsthal_Partitions_FiniteWeightedChoiceBox`, `Jacobsthal_Partitions_FullPatternCoordinates`, `Jacobsthal_Partitions_GeometricSelectionHardMass`, `Jacobsthal_Partitions_IntervalCuts`, `Jacobsthal_Partitions_IntervalHyperbolaAdapter`, `Jacobsthal_Partitions_IntervalPairCount`, `Jacobsthal_Partitions_IntervalSpectrumCoefficients`, `Jacobsthal_Partitions_MarginalTransport`, `Jacobsthal_Partitions_MeshBoundaryGeometry`, `Jacobsthal_Partitions_NestedCoordinates`, `Jacobsthal_Partitions_PaperGeometricRegularity`, `Jacobsthal_Partitions_ParentEdgeCoordinates`, `Jacobsthal_Partitions_RationalParameterInterval`, `Jacobsthal_Partitions_SignedIntervalGeometry`, `Jacobsthal_Partitions_SlopeCellPartition`, `Jacobsthal_Partitions_SourceBlockFibreBound`, `Jacobsthal_Partitions_SourceLabelCount`, `Jacobsthal_Partitions_StationaryFibres`, `Jacobsthal_Partitions_TwoSingletonBins`, `Jacobsthal_Paths_ActualSampleWitness`, `Jacobsthal_Paths_ActualTagFreezing`, `Jacobsthal_Paths_ActualThresholdArrival`, `Jacobsthal_Paths_ActualWordSelection`, `Jacobsthal_Paths_CanonicalKeyWitness`, `Jacobsthal_Paths_CorrectSearchTags`, `Jacobsthal_Paths_FiniteBoxWordMass`, `Jacobsthal_Paths_FiniteHistorySupport`, `Jacobsthal_Paths_FlagMeasurePartition`, `Jacobsthal_Paths_FlaggedHarmonicPaths`, `Jacobsthal_Paths_FlaggedHarmonicTransform`, `Jacobsthal_Paths_FlaggedSourceStart`, `Jacobsthal_Paths_FullWordHighAlignment`, `Jacobsthal_Paths_GeometricRegularWords`, `Jacobsthal_Paths_GlobalFiniteBranches`, `Jacobsthal_Paths_HighPrefixBounds`, `Jacobsthal_Paths_HighPrefixState`, `Jacobsthal_Paths_NearPrefixOccurrence`, `Jacobsthal_Paths_OutsideExceptionsWitness`, `Jacobsthal_Paths_RepresentativeStopGeometry`, `Jacobsthal_Paths_SampleWitnessAverage`, `Jacobsthal_Paths_StoppedReferenceFinite`, `Jacobsthal_Paths_TagPairBinding`, `Jacobsthal_Paths_TagSubbinWidths`, `Jacobsthal_Primes_ActualPrimeQuadrature`, `Jacobsthal_Primes_BadPrimeProduct`, `Jacobsthal_Primes_CanonicalTagPrimePartition`, `Jacobsthal_Primes_CrossingPrimeBin`, `Jacobsthal_Primes_FrozenPrimeGroup`, `Jacobsthal_Primes_FullPrimeEventFibres`, `Jacobsthal_Primes_GuardedHardPrimeSets`, `Jacobsthal_Primes_HighPrimeRemoval`, `Jacobsthal_Primes_IgnoredDenominatorPrimes`, `Jacobsthal_Primes_LargePrimeDeletion`, `Jacobsthal_Primes_OddPrimeRoots`, `Jacobsthal_Primes_OriginalPrimeBlocks`, `Jacobsthal_Primes_PrimeBinCounting`, `Jacobsthal_Primes_PrimeBinRepresentatives`, `Jacobsthal_Primes_PrimeCountAbel`, `Jacobsthal_Primes_PrimeDensityBlocks`, `Jacobsthal_Primes_PrimeEventCounting`, `Jacobsthal_Primes_PrimeFibreInterval`, `Jacobsthal_Primes_PrimeGridGeometry`, `Jacobsthal_Primes_PrimeHitRepresentative`, `Jacobsthal_Primes_PrimeLaw`, `Jacobsthal_Primes_PrimePowerBound`, `Jacobsthal_Primes_PrimeProductOmissions`, `Jacobsthal_Primes_PrimeRatioBins`, `Jacobsthal_Primes_PrimeWordArithmetic`, `Jacobsthal_Primes_ReferenceSourcePrimeSets`, `Jacobsthal_Primes_RieszMellinKernel`, `Jacobsthal_Primes_TagSmallPrimeData`, `Jacobsthal_Primes_TwoPrimeObservableSum`, `Jacobsthal_Primes_WeightedPrimeMultiplePairs`, `Jacobsthal_Probability_ActualCouplingUpdates`, `Jacobsthal_Probability_ArrivalKernelGeometry`, `Jacobsthal_Probability_CemeteryHistoryLaw`, `Jacobsthal_Probability_CouplingEvent`, `Jacobsthal_Probability_CouplingLabelEvents`, `Jacobsthal_Probability_EvenThresholdEvent`, `Jacobsthal_Probability_FiniteHistoryPairLaw`, `Jacobsthal_Probability_HarmonicPrefixKernel`, `Jacobsthal_Probability_HighPrefixKernel`, `Jacobsthal_Probability_MarkedStripTotal`, `Jacobsthal_Probability_OrderedAffineMoment`, `Jacobsthal_Probability_OrderedWindowKernel`, `Jacobsthal_Probability_SourceFullEventCount`, `Jacobsthal_Probability_StableFiniteVariance`, `Jacobsthal_Probability_StableSourceVariance`, `Jacobsthal_Probability_SubMarkovFlagPowers`, `Jacobsthal_Probability_ThirdInnerKernel`, `Jacobsthal_Probability_UniformMoment`, `Jacobsthal_Renewal_FlaggedOccupationBound`, `Jacobsthal_Sieve_ActualCofactorCellData`, `Jacobsthal_Sieve_AdmittedExponentMarginal`, `Jacobsthal_Sieve_AlignedCofactorSplit`, `Jacobsthal_Sieve_AlignedPrimeCongruence`, `Jacobsthal_Sieve_AugmentedCRTCell`, `Jacobsthal_Sieve_BoxWitnessFactorization`, `Jacobsthal_Sieve_CRTPrimeCost`, `Jacobsthal_Sieve_CoprimePositionSieve`, `Jacobsthal_Sieve_DivisorHarmonic`, `Jacobsthal_Sieve_EulerProductRatio`, `Jacobsthal_Sieve_ExceptionalResidues`, `Jacobsthal_Sieve_ExponentialMesh`, `Jacobsthal_Sieve_ExponentialTailBound`, `Jacobsthal_Sieve_FrozenSieveMean`, `Jacobsthal_Sieve_HypotheticalResidues`, `Jacobsthal_Sieve_IntegerLaw`, `Jacobsthal_Sieve_IntegerResidueVariance`, `Jacobsthal_Sieve_IntegerSlopeConstruction`, `Jacobsthal_Sieve_IntervalBoundingSieve`, `Jacobsthal_Sieve_LargePrimeDivisors`, `Jacobsthal_Sieve_LineCongruenceConstruction`, `Jacobsthal_Sieve_LinearSieveFunctions`, `Jacobsthal_Sieve_OddEulerCorrection`, `Jacobsthal_Sieve_OriginalCofactorPoints`, `Jacobsthal_Sieve_OriginalPairSieve`, `Jacobsthal_Sieve_PrimeExponentialTail`, `Jacobsthal_Sieve_PrimeFibreBrunBound`, `Jacobsthal_Sieve_RealCoprimeResidueCount`, `Jacobsthal_Sieve_RefinementPrimeCongruences`, `Jacobsthal_Sieve_ResidueCountDifference`, `Jacobsthal_Sieve_ResidueFibres`, `Jacobsthal_Sieve_ResidueProjection`, `Jacobsthal_Sieve_SieveScale`, `Jacobsthal_Sieve_SourcePairSieve`, `Jacobsthal_Sieve_TagCRTPeriodicity`, `Jacobsthal_Sieve_TagUnitSieveLower`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ247J007`; the statements `OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_primitive_zero_free_region_jb247`, `OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_sharp_character_exponential_jb247`, `OAI_Erdos970_ErdosContinuousAnomaly_boundaryProduct_tendsto_half_jb247`, `OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247`, `OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247`, `OAI.Erdos970.ErdosInverseFrozen.frozen_exceptional_mean_jb247`, `OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247`, `OAI.Erdos970.ErdosInverseRefinement.source_parentSlope_mem_jb247`, `OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247`, `OAI_Erdos970_ErdosRichLine_integer_polynomial_rich_line_jb247`, `OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_moving_weighted_pair_lower_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_moving_subbin_prime_lower_jb247`, `OAI.Erdos970.ErdosVarianceCommon.source_actual_bad_to_common_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_interval_slack_jb247`, `OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247`, `OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247`, `OAI.Erdos970.ErdosVarianceMoments.finite_joint_moment_estimate_jb247`, `OAI.Erdos970.ErdosVarianceSmallModel.source_residue_fibre_bound_jb247`, `OAI_Erdos970_ErdosVarianceUniformMoments_uniform_density_inverse_jb247`, `OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247`, `OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247` and `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247`; the proofs of `OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247`, `OAI_Erdos970_ErdosRandomVariance_stable_source_chebyshev_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_interval_slack_jb247` and `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma

section
-- module Solutions.OAIQ247_JB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BivariateCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosImplicitCurvature

abbrev Bivariate := MvPolynomial (Fin 2) ℝ

noncomputable def peval (Q : Bivariate) (x y : ℝ) : ℝ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) Q

noncomputable def partialX (Q : Bivariate) : Bivariate := MvPolynomial.pderiv 0 Q
noncomputable def partialY (Q : Bivariate) : Bivariate := MvPolynomial.pderiv 1 Q

@[simp] theorem peval_C (c x y : ℝ) : peval (MvPolynomial.C c) x y = c := by
  simp [peval]
@[simp] theorem peval_add (P Q : Bivariate) (x y : ℝ) :
    peval (P+Q) x y = peval P x y+peval Q x y := by simp [peval]
@[simp] theorem peval_mul (P Q : Bivariate) (x y : ℝ) :
    peval (P*Q) x y = peval P x y*peval Q x y := by simp [peval]
@[simp] theorem peval_X_zero (x y : ℝ) : peval (MvPolynomial.X 0) x y = x := by simp [peval]
@[simp] theorem peval_X_one (x y : ℝ) : peval (MvPolynomial.X 1) x y = y := by simp [peval]
@[simp] theorem peval_zero (x y : ℝ) : peval 0 x y = 0 := by simp [peval]
@[simp] theorem peval_one (x y : ℝ) : peval 1 x y = 1 := by simp [peval]

theorem hasDerivAt_peval (Q : Bivariate) (u v : ℝ → ℝ) (du dv x : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x) :
    HasDerivAt (fun t => peval Q (u t) (v t))
      (peval (partialX Q) (u x) (v x)*du+peval (partialY Q) (u x) (v x)*dv) x := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [partialX, partialY, MvPolynomial.pderiv_C] using hasDerivAt_const x c
  | add P Q hP hQ =>
      have h := (hP.add hQ).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t => peval_add P Q (u t) (v t)))
      apply h.congr_deriv
      simp only [partialX, partialY, map_add, peval_add]
      ring
  | mul_X P i hP =>
      fin_cases i
      · have h := (hP.mul hu).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun t => show peval (P*MvPolynomial.X 0) (u t) (v t) =
            peval P (u t) (v t)*u t by simp))
        apply h.congr_deriv
        simp [partialX, partialY]
        ring
      · have h := (hP.mul hv).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun t => show peval (P*MvPolynomial.X 1) (u t) (v t) =
            peval P (u t) (v t)*v t by simp))
        apply h.congr_deriv
        simp [partialX, partialY]
        ring

end ErdosImplicitCurvature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RegularImplicitArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosLatticeChain

def vectorLength (v : ℕ × ℕ) : ℕ := v.1+v.2

def totalLength (V : Finset (ℕ × ℕ)) : ℕ := ∑ v ∈ V, vectorLength v

def shortVectors (V : Finset (ℕ × ℕ)) (T : ℕ) : Finset (ℕ × ℕ) :=
  V.filter fun v => vectorLength v ≤ T

def longVectors (V : Finset (ℕ × ℕ)) (T : ℕ) : Finset (ℕ × ℕ) :=
  V.filter fun v => T < vectorLength v

def shortSquareEmbedding (V : Finset (ℕ × ℕ)) (T : ℕ) :
    ↥(shortVectors V T) ↪ (Fin (T+1) × Fin (T+1)) where
  toFun v :=
    (⟨v.1.1, by
      have h := (Finset.mem_filter.mp v.2).2
      dsimp [vectorLength] at h
      omega⟩,
     ⟨v.1.2, by
      have h := (Finset.mem_filter.mp v.2).2
      dsimp [vectorLength] at h
      omega⟩)
  inj' := by
    intro u v h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun w : Fin (T+1) × Fin (T+1) => w.1.val) h
    · exact congrArg (fun w : Fin (T+1) × Fin (T+1) => w.2.val) h

end ErdosLatticeChain

end

section

open scoped BigOperators
namespace ErdosLatticeChain

def coordinateVariation {n : ℕ} (f : Fin (n+1) → ℤ) : ℕ :=
  ∑ i : Fin n, (f i.succ-f i.castSucc).natAbs

end ErdosLatticeChain

end


section

open scoped BigOperators
namespace ErdosLatticeChain

def earlierIndex {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def laterIndex {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val+1, by have := i.isLt; omega⟩

def consecutiveDifference {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℤ × ℤ :=
  ((P (laterIndex i)).1-(P (earlierIndex i)).1,
   (P (laterIndex i)).2-(P (earlierIndex i)).2)

def natIncrement {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℕ × ℕ :=
  ((consecutiveDifference P i).1.natAbs, (consecutiveDifference P i).2.natAbs)

noncomputable def incrementVectors {n : ℕ} (P : Fin n → ℤ × ℤ) : Finset (ℕ × ℕ) :=
  Finset.univ.image (natIncrement P)

end ErdosLatticeChain

end


namespace ErdosImplicitCurvature

noncomputable def inflectionPolynomial (Q : Bivariate) : Bivariate :=
  partialX (partialX Q)*(partialY Q)^2 -
    2*partialX (partialY Q)*partialX Q*partialY Q +
    partialY (partialY Q)*(partialX Q)^2

end ErdosImplicitCurvature



namespace ErdosLatticeChain

noncomputable def consecutiveSlope {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℝ :=
  ((consecutiveDifference P i).2 : ℝ)/((consecutiveDifference P i).1 : ℝ)

end ErdosLatticeChain



namespace ErdosConvexGraph

open ErdosLatticeChain

noncomputable def secantSlopes {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ)
    (i : Fin (n-1)) : ℝ :=
  (f (x (laterIndex i))-f (x (earlierIndex i)))/(x (laterIndex i)-x (earlierIndex i))

end ErdosConvexGraph



namespace ErdosConvexGraph

open ErdosLatticeChain

def OnGraph (I : Set ℝ) (f : ℝ → ℝ) (p : ℤ × ℤ) : Prop :=
  (p.1 : ℝ) ∈ I ∧ (p.2 : ℝ) = f (p.1 : ℝ)

def InSquare (S : ℝ) (p : ℤ × ℤ) : Prop :=
  (0 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ S) ∧ (0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ S)

end ErdosConvexGraph



namespace ErdosConvexGraph

def graphAbscissae (G : Finset (ℤ × ℤ)) : Finset ℤ := G.image Prod.fst

noncomputable def graphEnumeration (G : Finset (ℤ × ℤ)) (f : ℝ → ℝ)
    (i : Fin (graphAbscissae G).card) : ℤ × ℤ :=
  ((graphAbscissae G).orderEmbOfFin rfl i,
    ⌊f (((graphAbscissae G).orderEmbOfFin rfl i : ℤ) : ℝ)⌋)





attribute [local instance] Classical.propDecidable

noncomputable def graphLatticePoints (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter (OnGraph I f)

end ErdosConvexGraph



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_NestedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

abbrev Nested := Polynomial (Polynomial R)

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialLocalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology ContDiff
namespace ErdosDivisibleInflection

open ErdosImplicitCurvature

noncomputable def planeEval (Q : Bivariate) (p : ℝ × ℝ) : ℝ := peval Q p.1 p.2

theorem contDiff_planeEval (Q : Bivariate) (n : ℕ∞ω) : ContDiff ℝ n (planeEval Q) := by
  unfold planeEval
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [planeEval] using (contDiff_const (c := c) : ContDiff ℝ n (fun _ : ℝ × ℝ => c))
  | add P Q hP hQ =>
      simpa only [planeEval, peval_add] using hP.add hQ
  | mul_X P i hP =>
      fin_cases i
      · simpa [peval] using hP.mul contDiff_fst
      · simpa [peval] using hP.mul contDiff_snd

theorem fderiv_planeEval_inr (Q : Bivariate) (x y : ℝ) :
    fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (peval (partialY Q) x y) := by
  have hF := ((contDiff_planeEval Q 1).differentiable (by norm_num) (x,y)).hasFDerivAt
  have hp : HasFDerivAt (fun t : ℝ => (x,t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) y := by
    have hlin : HasFDerivAt (ContinuousLinearMap.inr ℝ ℝ ℝ) (ContinuousLinearMap.inr ℝ ℝ ℝ) y :=
      (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
    simpa using hlin.const_add (x,0)
  have hc := hF.comp y hp
  have hy : HasDerivAt (fun t => peval Q x t) (peval (partialY Q) x y) y := by
    simpa using hasDerivAt_peval Q (fun _ => x) id 0 1 y (hasDerivAt_const y x) (hasDerivAt_id y)
  exact hc.unique hy.hasFDerivAt

theorem scalar_map_invertible (b : ℝ) (hb : b ≠ 0) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight b).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1 : ℝ →L[ℝ] ℝ).smulRight b⁻¹)
  · ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb]
  · ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb]

end ErdosDivisibleInflection

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection ErdosCriticalGeometry

def boundedFiber (Q : Bivariate) (x L U : ℝ) : Set ℝ :=
  {y | y ∈ Icc L U ∧ peval Q x y = 0}

theorem boundedFiber_interior (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0) :
    boundedFiber Q x L U ⊆ Ioo L U := by
  intro y hy
  constructor
  · exact lt_of_le_of_ne hy.1.1 (fun he => hL (he ▸ hy.2))
  · exact lt_of_le_of_ne hy.1.2 (fun he => hU (he ▸ hy.2))

theorem compact_nonzero_eventually (Q : Bivariate) (x : ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hne : ∀ y ∈ K, peval Q x y ≠ 0) :
    ∀ᶠ t in 𝓝 x, ∀ y ∈ K, peval Q t y ≠ 0 := by
  have ho : IsOpen {p : ℝ × ℝ | planeEval Q p ≠ 0} :=
    isOpen_ne.preimage (contDiff_planeEval Q 0).continuous
  obtain ⟨A,B,hA,_,hxA,hKB,hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hK ho (by
      rintro ⟨t,y⟩ ⟨ht,hy⟩
      have ht' : t = x := ht
      subst t
      exact hne y hy)
  filter_upwards [hA.mem_nhds (hxA (mem_singleton x))] with t ht
  intro y hy
  exact hAB (a := (t,y)) ⟨ht,hKB hy⟩

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PrimitiveResultant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosBivariateResultant

abbrev Bivariate := Polynomial (Polynomial ℂ)

noncomputable def specialize (P : Bivariate) (x : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom x)

noncomputable def pointEvalHom (x y : ℂ) : Bivariate →+* ℂ :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))

noncomputable def beval (P : Bivariate) (x y : ℂ) : ℂ := pointEvalHom x y P

noncomputable def xResultant (P Q : Bivariate) : Polynomial ℂ := P.resultant Q

@[simp] theorem beval_add (P Q : Bivariate) (x y : ℂ) :
    beval (P+Q) x y = beval P x y+beval Q x y := (pointEvalHom x y).map_add P Q
@[simp] theorem beval_mul (P Q : Bivariate) (x y : ℂ) :
    beval (P*Q) x y = beval P x y*beval Q x y := (pointEvalHom x y).map_mul P Q
@[simp] theorem beval_C (p : Polynomial ℂ) (x y : ℂ) :
    beval (Polynomial.C p) x y = p.eval x := by
  simp [beval, pointEvalHom]

end ErdosBivariateResultant

end

section

open scoped BigOperators
namespace ErdosBivariateResultant

attribute [local instance] Classical.propDecidable

noncomputable def resultantRoots (P Q : Bivariate) : Finset ℂ := (xResultant P Q).roots.toFinset
noncomputable def verticalRoots (P : Bivariate) (x : ℂ) : Finset ℂ := (specialize P x).roots.toFinset

noncomputable def rootPairs (P Q : Bivariate) : Finset (ℂ × ℂ) :=
  (resultantRoots P Q).biUnion fun x => (verticalRoots P x).image fun y => (x,y)

noncomputable def commonZeroFinset (P Q : Bivariate) : Finset (ℂ × ℂ) :=
  (rootPairs P Q).filter fun p => beval Q p.1 p.2 = 0

def commonZeroSet (P Q : Bivariate) : Set (ℂ × ℂ) :=
  {p | beval P p.1 p.2 = 0 ∧ beval Q p.1 p.2 = 0}

end ErdosBivariateResultant

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RealCriticalPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry

noncomputable def affineInner (A B : ℂ) : Polynomial ℂ :=
  Polynomial.C A*Polynomial.X+Polynomial.C B

end ErdosDivisibleInflection

end

section

namespace ErdosCriticalGeometry

def complexPoint (p : ℝ × ℝ) : ℂ × ℂ := ((p.1 : ℂ),(p.2 : ℂ))

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LocalGraphIff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter Set
open scoped Topology ContDiff
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection

theorem exists_local_graph_iff (Q : Bivariate) (x y : ℝ)
    (hQ : peval Q x y = 0) (hQy : peval (partialY Q) x y ≠ 0)
    (V : Set ℝ) (hV : IsOpen V) (hyV : y ∈ V) :
    ∃ (a b : ℝ) (W : Set ℝ) (f : ℝ → ℝ),
      a < x ∧ x < b ∧ IsOpen W ∧ y ∈ W ∧ W ⊆ V ∧ f x = y ∧
      ContDiffOn ℝ 2 f (Ioo a b) ∧
      (∀ t ∈ Ioo a b, f t ∈ W) ∧
      (∀ t ∈ Ioo a b, peval (partialY Q) t (f t) ≠ 0) ∧
      (∀ t ∈ Ioo a b, ∀ z ∈ W, peval Q t z = 0 ↔ z = f t) := by
  have hc : ContDiffAt ℝ 2 (planeEval Q) (x,y) := (contDiff_planeEval Q 2).contDiffAt
  have hi : (fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [fderiv_planeEval_inr]
    exact scalar_map_invertible _ hQy
  let f := hc.implicitFunction (by norm_num) hi
  have hfx : f x = y := hc.implicitFunction_apply_self (by norm_num) hi
  have hcf : ContDiffAt ℝ 2 f x := hc.contDiffAt_implicitFunction (by norm_num) hi
  have heq : ∀ᶠ v in 𝓝 (x,y), peval Q v.1 v.2 = 0 ↔ v.2 = f v.1 := by
    have h := hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi
    exact h.mono fun v hv => by simpa only [planeEval, hQ, eq_comm] using hv
  obtain ⟨U,V₀,hU,hxU,hV₀,hyV₀,hUV⟩ := mem_nhds_prod_iff'.mp heq
  let W := V ∩ V₀
  have hW : IsOpen W := hV.inter hV₀
  have hyW : y ∈ W := ⟨hyV,hyV₀⟩
  have hmem : ∀ᶠ t in 𝓝 x, f t ∈ W :=
    hcf.continuousAt.preimage_mem_nhds (hfx ▸ hW.mem_nhds hyW)
  have hpair : ContinuousAt (fun t : ℝ => (t,f t)) x :=
    continuousAt_id.prodMk hcf.continuousAt
  have hplane : ContinuousAt (planeEval (partialY Q)) (x,f x) :=
    (contDiff_planeEval (partialY Q) 0).continuous.continuousAt
  have hcy : ContinuousAt (fun t => peval (partialY Q) t (f t)) x := by
    change ContinuousAt (planeEval (partialY Q) ∘ (fun t : ℝ => (t,f t))) x
    exact ContinuousAt.comp (f := fun t : ℝ => (t,f t)) hplane hpair
  have hny : ∀ᶠ t in 𝓝 x, peval (partialY Q) t (f t) ≠ 0 := by
    apply hcy.eventually_ne
    rwa [hfx]
  obtain ⟨D,hD,hfD⟩ := hcf.contDiffOn (m := 2) le_rfl (by norm_num)
  have hN : U ∩ D ∩ {t | f t ∈ W} ∩ {t | peval (partialY Q) t (f t) ≠ 0} ∈ 𝓝 x :=
    inter_mem (inter_mem (inter_mem (hU.mem_nhds hxU) hD) hmem) hny
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hs : Ioo (x-eps) (x+eps) ⊆
      U ∩ D ∩ {t | f t ∈ W} ∩ {t | peval (partialY Q) t (f t) ≠ 0} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨x-eps,x+eps,W,f,by linarith,by linarith,hW,hyW,
    inter_subset_left,hfx,hfD.mono (fun t ht => (hs ht).1.1.2),
    (fun t ht => (hs ht).1.2),(fun t ht => (hs ht).2),?_⟩
  intro t ht z hz
  exact hUV (a := (t,z)) ⟨(hs ht).1.1.1,hz.2⟩

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiberCardinalityConstancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosGlobalFiberBranches

noncomputable def orderIsoOfNatCardEq (α β : Type*) [LinearOrder α] [LinearOrder β]
    [Finite α] [Finite β] (h : Nat.card α = Nat.card β) : α ≃o β := by
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  exact (Fintype.orderIsoFinOfCardEq α rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq β (by simpa only [Nat.card_eq_fintype_card] using h.symm))

noncomputable def orderIsoOfStrictMonoSurjective {α β : Type*}
    [LinearOrder α] [LinearOrder β] (f : α → β) (hf : StrictMono f)
    (hs : Function.Surjective f) : α ≃o β :=
  { Equiv.ofBijective f ⟨hf.injective,hs⟩ with map_rel_iff' := hf.le_iff_le }

end ErdosGlobalFiberBranches

end

section

open Filter Set
open scoped Topology ContDiff
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature

structure FiberCharts (Q : Bivariate) (x L U : ℝ) where
  a : ℝ
  b : ℝ
  left : a < x
  right : x < b
  finite_base : (boundedFiber Q x L U).Finite
  graph : boundedFiber Q x L U → ℝ → ℝ
  tube : boundedFiber Q x L U → Set ℝ
  tube_open : ∀ r, IsOpen (tube r)
  tube_base : ∀ r, (r : ℝ) ∈ tube r
  tube_interior : ∀ r, tube r ⊆ Ioo L U
  tube_disjoint : Pairwise fun r s => Disjoint (tube r) (tube s)
  graph_base : ∀ r, graph r x = r
  graph_smooth : ∀ r, ContDiffOn ℝ 2 (graph r) (Ioo a b)
  graph_inside : ∀ r, ∀ t ∈ Ioo a b, graph r t ∈ tube r
  graph_regular : ∀ r, ∀ t ∈ Ioo a b, peval (partialY Q) t (graph r t) ≠ 0
  zero_iff : ∀ r, ∀ t ∈ Ioo a b, ∀ y ∈ tube r, peval Q t y = 0 ↔ y = graph r t
  coverage : ∀ t ∈ Ioo a b, boundedFiber Q t L U = range (fun r => graph r t)
  ordered : ∀ t ∈ Ioo a b, StrictMono (fun r => graph r t)

end ErdosLocalFiberGraphs

end

section

open Set
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

noncomputable def chartOrderIso {Q : Bivariate} {x L U : ℝ}
    (c : FiberCharts Q x L U) (t : ℝ) (ht : t ∈ Ioo c.a c.b) :
    boundedFiber Q x L U ≃o boundedFiber Q t L U := by
  let f : boundedFiber Q x L U → boundedFiber Q t L U := fun r =>
    ⟨c.graph r t,by rw [c.coverage t ht]; exact mem_range_self r⟩
  apply orderIsoOfStrictMonoSurjective f
  · exact fun r s hrs => (c.ordered t ht) hrs
  · intro y
    have hy := (c.coverage t ht).subset y.property
    obtain ⟨r,hr⟩ := hy
    exact ⟨r,Subtype.ext hr⟩

end ErdosGlobalFiberBranches

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosCriticalGeometry

namespace FiberCharts
variable {Q : Bivariate} {x L U : ℝ} (c : FiberCharts Q x L U)

theorem fiber_finite {t : ℝ} (ht : t ∈ Ioo c.a c.b) :
    (boundedFiber Q t L U).Finite := by
  let := c.finite_base.fintype
  rw [c.coverage t ht]
  exact finite_range _

theorem fiber_card_eq {t : ℝ} (ht : t ∈ Ioo c.a c.b) :
    (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  rw [c.coverage t ht,ncard_range_of_injective (c.ordered t ht).injective,
    Nat.card_coe_set_eq]

end FiberCharts

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection

def regularParameters (Q : Bivariate) (L U : ℝ) : Set ℝ :=
  {x | peval Q x L ≠ 0 ∧ peval Q x U ≠ 0 ∧
    ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0}

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GlobalFiniteBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
open scoped Topology
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

structure RegularDomain (Q : Bivariate) (x L U : ℝ) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  isPreconnected : IsPreconnected I
  base_mem : x ∈ I
  regular : I ⊆ regularParameters Q L U

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialStripPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def polynomialStripPoints (Q : Bivariate) (a b S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => (p.1 : ℝ) ∈ Ioo a b ∧ peval Q p.1 p.2 = 0)

end ErdosRegularStrip

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SortedRealGaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips

noncomputable def gapLeft (E : Finset ℝ) (i : Fin (E.card-1)) : ℝ :=
  E.orderEmbOfFin rfl ⟨i.val,by have h := i.isLt; omega⟩

noncomputable def gapRight (E : Finset ℝ) (i : Fin (E.card-1)) : ℝ :=
  E.orderEmbOfFin rfl ⟨i.val+1,by have h := i.isLt; omega⟩

end ErdosMarkedStrips

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedStripTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def polynomialSquarePoints (Q : Bivariate) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => peval Q p.1 p.2 = 0)

noncomputable def markedFiberPoints (Q : Bivariate) (t S : ℝ) : Finset (ℤ × ℤ) :=
  (polynomialSquarePoints Q S).filter (fun p => (p.1 : ℝ) = t)

end ErdosMarkedStrips

end

section

open Set
namespace ErdosMarkedStrips
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosRegularStrip ErdosConvexGraph

def RegularOff (Q : Bivariate) (S : ℝ) (E : Finset ℝ) : Prop :=
  ∀ t ∉ E, (peval Q t 0 ≠ 0 ∧ peval Q t S ≠ 0) ∧
    ∀ y ∈ Icc 0 S, peval Q t y = 0 →
      peval (partialX Q) t y ≠ 0 ∧ peval (partialY Q) t y ≠ 0 ∧
        peval (inflectionPolynomial Q) t y ≠ 0

end ErdosMarkedStrips

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_ComplexSquareScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosMarkedStrips ErdosConvexGraph
attribute [local instance] Classical.propDecidable

def complexIntPoint (p : ℤ × ℤ) : ℂ × ℂ := ((p.1 : ℂ),(p.2 : ℂ))

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CharacterChord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

noncomputable def characterProgression (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) : ℂ :=
  ∑ j ∈ Finset.range J, ZMod.stdAddChar (start + (j : ZMod N)*step)

end ErdosHyperbolaFourier

end

section

namespace ErdosHyperbolaFourier

def cyclicDistance (N : ℕ) (step : ZMod N) : ℕ := min step.val (N-step.val)

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_DivisorHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

noncomputable def harmonicWeight (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, 1/(n : ℝ)

end ErdosHyperbola

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UnitCyclicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbola

noncomputable def harmonicConstant : ℝ := 1 + 1/Real.log 2

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

def mulUnitEquiv (N : ℕ) (u : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun r := r*(u : ZMod N)
  invFun r := r*(↑u⁻¹ : ZMod N)
  left_inv r := by simp [mul_assoc]
  right_inv r := by simp [mul_assoc]

@[simp] theorem mulUnitEquiv_apply (N : ℕ) (u : (ZMod N)ˣ) (r : ZMod N) :
    mulUnitEquiv N u r = r*(u : ZMod N) := rfl

end ErdosHyperbola

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FactorDividesAbscissa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInverseIncidence
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def bit {α β : Type*} (R : α → β → Prop) (a : α) (p : β) : ℝ := if R a p then 1 else 0
noncomputable def degree {α β : Type*} (P : Finset β) (R : α → β → Prop) (a : α) : ℕ :=
  (P.filter (R a)).card
noncomputable def multiplicity {α β : Type*} (A : Finset α) (R : α → β → Prop) (p : β) : ℝ :=
  ∑ a ∈ A, bit R a p

end ErdosInverseIncidence

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def aligns (a : ℕ → ℤ) (q : ℚ) (p : ℕ) : Prop :=
  (q.den : ZMod p) * (a p : ZMod p) = (q.num : ZMod p)

def determinant (q r : ℚ) : ℤ := q.num*(r.den : ℤ)-r.num*(q.den : ℤ)

noncomputable def commonAligners (P : Finset ℕ) (a : ℕ → ℤ) (q r : ℚ) : Finset ℕ :=
  P.filter (fun p => aligns a q p ∧ aligns a r p)

end ErdosInverseAlignment

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def heightCandidates (HA HD : ℕ) : Finset ℚ :=
  (((Finset.Icc (-(HA : ℤ)) (HA : ℤ)).product (Finset.Icc 1 HD)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ)/(z.2 : ℚ))).filter
      (fun q => q.num.natAbs ≤ HA ∧ q.den ≤ HD)

noncomputable def rationalList (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (c : ℝ) : Finset ℚ :=
  (heightCandidates HA HD).filter
    (fun q => c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ))

end ErdosInverseAlignment

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry

structure PrimitiveIntegerLine where
  denominator : ℕ
  slope : ℤ
  intercept : ℤ
  denominator_pos : 0 < denominator
  reduced : Nat.Coprime slope.natAbs denominator

def PrimitiveIntegerLine.Contains (l : PrimitiveIntegerLine) (p : ℤ × ℤ) : Prop :=
  (l.denominator : ℤ)*p.2 = l.slope*p.1+l.intercept

end ErdosRichLine

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine

structure InterceptReduction (l : PrimitiveIntegerLine) where
  rational : ℚ
  factor : ℕ
  factor_pos : 0 < factor
  denominator_eq : l.denominator = factor*rational.den
  intercept_eq : l.intercept = (factor : ℤ)*rational.num

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositiveProgression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

def hitLength (Y M b : ℕ) : ℕ := (Y+M-b)/M

end ErdosInverseHits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeHitRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem modEq_prime_product_iff (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (n b : ℕ) :
    Nat.ModEq (∏ p ∈ P,p) n b ↔ ∀ p ∈ P,Nat.ModEq p n b := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _;simp [Nat.modEq_one]
  | @insert p P hp ih =>
    intro hP
    have hprime := hP p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ P,q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ P,q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (by intro heq;exact hp (heq ▸ hq))
    rw [Finset.prod_insert hp,← Nat.modEq_and_modEq_iff_modEq_mul hco,ih hrest]
    simp only [Finset.forall_mem_insert]

theorem exists_prime_hit_representative (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    ∃ b : ℕ,1 ≤ b ∧ b ≤ q ∧ ∀ n : ℕ,
      (∀ p ∈ q.primeFactors,n%p = a p%p) ↔ Nat.ModEq q n b := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hnz : ∀ p ∈ q.primeFactors,(id p : ℕ) ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpair : Set.Pairwise (q.primeFactors : Set ℕ) (fun p r => Nat.Coprime (id p) (id r)) := by
    intro p hp r hr hpr
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hr)).mpr hpr
  let c := Nat.chineseRemainderOfFinset a id q.primeFactors hnz hpair
  have hcq : c.val < q := by
    have hh := Nat.chineseRemainderOfFinset_lt_prod a id hnz hpair
    simpa only [id_eq,Nat.prod_primeFactors_of_squarefree hq] using hh
  have hbp : ∃ b : ℕ,1 ≤ b ∧ b ≤ q ∧ ∀ p ∈ q.primeFactors,Nat.ModEq p b (a p) := by
    by_cases hc : c.val = 0
    · refine ⟨q,hq0,le_rfl,?_⟩
      intro p hp
      have hd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      have ht := c.property p hp
      change Nat.ModEq p c.val (a p) at ht
      rw [hc] at ht
      exact hd.modEq_zero_nat.trans ht
    · exact ⟨c.val,by omega,hcq.le,c.property⟩
  obtain ⟨b,hb1,hbq,hbp⟩ := hbp
  refine ⟨b,hb1,hbq,?_⟩
  intro n
  have hprod := modEq_prime_product_iff q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) n b
  rw [Nat.prod_primeFactors_of_squarefree hq] at hprod
  rw [hprod]
  constructor
  · intro hn p hp
    exact (show Nat.ModEq p n (a p) from hn p hp).trans (hbp p hp).symm
  · intro hn p hp
    exact (hn p hp).trans (hbp p hp)

noncomputable def primeHitRepresentative (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) : ℕ :=
  (exists_prime_hit_representative q hq a).choose

end ErdosInverseHits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedPrimeCongruence
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

noncomputable def residueCandidates (Y : ℕ) (H small : Finset ℕ)
    (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter fun n =>
    (∀ p ∈ H, residueBad a p n) ∧ ∀ q ∈ small, ¬ residueBad a q n

@[simp] theorem mem_residueCandidates {Y : ℕ} {H small : Finset ℕ}
    {a : ℕ → ℕ} {n : ℕ} :
    n ∈ residueCandidates Y H small a ↔
      1 ≤ n ∧ n ≤ Y ∧
        (∀ p ∈ H, residueBad a p n) ∧ ∀ q ∈ small, ¬ residueBad a q n := by
  classical
  simp only [residueCandidates, Finset.mem_filter, Finset.mem_Icc]
  tauto

end NumberTheoryLean.SievePartition

end

section

namespace ErdosInverseCounts
open NumberTheoryLean NumberTheoryLean.SievePartition

noncomputable def modulusCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  residueCandidates Y m.primeFactors small a

noncomputable def modulusCount (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : ℤ :=
  (modulusCandidates Y small a m).card

end ErdosInverseCounts

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_LargePrimeDeletion
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

def largePrimeFactors (n z : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => z < p

@[simp] theorem mem_largePrimeFactors {n z p : ℕ} :
    p ∈ largePrimeFactors n z ↔ p ∈ n.primeFactors ∧ z < p := by
  simp [largePrimeFactors]

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

def CompatibleSmallResidues (n z : ℕ) (a : ℤ) (residue : ℕ → ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ≤ z → residue p % p = divisibilityResidue a p % p

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntervalBoundingSieve
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BonferroniBlocks
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_BonferroniDensity
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_WeightedMonotoneBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosMonotoneQuadrature

noncomputable def reciprocalWeight (u x : ℝ) : ℝ := (max u x)⁻¹

noncomputable def reciprocalMeasure (μ : Measure ℝ) (u : ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (reciprocalWeight u x))

end ErdosMonotoneQuadrature

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin

noncomputable def primeBin (R xi : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊(1+xi)*R⌋₊ \ Nat.primesLE ⌊R⌋₊

theorem mem_primeBin {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) (p : ℕ) :
    p ∈ primeBin R xi ↔ p.Prime ∧ R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R := by
  have hb : 0 ≤ (1+xi)*R := by positivity
  constructor
  · intro hp
    obtain ⟨hpB,hpR⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hup,hprime⟩ := Nat.mem_primesLE.mp hpB
    refine ⟨hprime,?_,(Nat.le_floor_iff hb).mp hup⟩
    by_contra! hlow
    exact hpR (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hR).mpr hlow,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hb).mpr hhi,hprime⟩,?_⟩
    intro hpR
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hR).mp (Nat.mem_primesLE.mp hpR).1)

end ErdosInversePrimeBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter _root_.Asymptotics
open scoped Topology

noncomputable def errorScale (c x : ℝ) : ℝ :=
  x * Real.exp (-c * Real.sqrt (Real.log x))

theorem errorScale_nonneg (c : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ errorScale c x := by
  exact mul_nonneg hx (Real.exp_pos _).le

theorem sqrt_le_errorScale {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ errorScale c x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 * c) ^ 2))] with x hx hlog
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hy0 := Real.sqrt_nonneg (Real.log x)
  have hy2 := Real.sq_sqrt hl0
  have hy : 2 * c ≤ Real.sqrt (Real.log x) := by nlinarith
  have hmul := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have hlin : Real.log x * (1 / 2) ≤ Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith
  calc
    Real.sqrt x = Real.exp (Real.log x * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    _ ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) := Real.exp_le_exp.mpr hlin
    _ = errorScale c x := by
      rw [Real.exp_sub, Real.exp_log hx0, errorScale, neg_mul, Real.exp_neg]
      ring

theorem sqrt_isBigO_errorScale {c : ℝ} (hc : 0 < c) :
    Real.sqrt =O[atTop] errorScale c := by
  apply IsBigO.of_bound 1
  filter_upwards [sqrt_le_errorScale hc, eventually_ge_atTop (0 : ℝ)] with x hb hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (errorScale_nonneg c hx), one_mul] using hb

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeAbel

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped Topology

noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
noncomputable def reciprocalPrimes (a b : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n : ℝ)⁻¹
noncomputable def invLogWeight (t : ℝ) : ℝ := 1 / (t * Real.log t)
noncomputable def errorKernel (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

theorem prefix_primeLogWeight (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem reciprocal_eq_weighted (a b : ℝ) :
    reciprocalPrimes a b = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, invLogWeight n * primeLogWeight n := by
  rw [reciprocalPrimes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hnl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
    simp only [primeLogWeight, hp, ite_true, if_true, invLogWeight]
    field_simp
  · simp [primeLogWeight, hp]

theorem hasDerivAt_invLogWeight {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLogWeight (-errorKernel t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl0) using 1
  · ext x
    simp [invLogWeight, one_div]
  · dsimp [errorKernel]
    field_simp

theorem deriv_invLogWeight {t : ℝ} (ht : 1 < t) : deriv invLogWeight t = -errorKernel t :=
  (hasDerivAt_invLogWeight ht).deriv

theorem invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn invLogWeight (Set.Icc a b) := by
  intro t ht
  exact (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt

theorem deriv_invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (deriv invLogWeight) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t => -errorKernel t) (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    apply ContinuousAt.continuousWithinAt
    unfold errorKernel
    fun_prop (disch := simp [ht0, hl0])
  apply hc.congr
  intro t ht
  exact deriv_invLogWeight (lt_of_lt_of_le ha ht.1)

theorem abel_theta {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b = invLogWeight b * Chebyshev.theta b - invLogWeight a * Chebyshev.theta a -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t := by
  rw [reciprocal_eq_weighted]
  have h := sum_mul_eq_sub_sub_integral_mul primeLogWeight (le_of_lt (lt_trans zero_lt_one ha)) hab
    (fun t ht => (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).differentiableAt)
    (deriv_invLogWeight_continuousOn ha).integrableOn_Icc
  simpa only [prefix_primeLogWeight] using h

theorem error_identity {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b - (∫ t in Set.Ioc a b, invLogWeight t) =
      invLogWeight b * (Chebyshev.theta b - b) - invLogWeight a * (Chebyshev.theta a - a) -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t) := by
  have hf : IntegrableOn invLogWeight (Set.Ioc a b) :=
    (invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hfd : ContinuousOn (deriv invLogWeight) (Set.Icc a b) := deriv_invLogWeight_continuousOn ha
  have hlin : IntegrableOn (fun t => deriv invLogWeight t * t) (Set.Ioc a b) :=
    (hfd.mul continuousOn_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htheta : IntegrableOn (fun t => deriv invLogWeight t * Chebyshev.theta t) (Set.Ioc a b) := by
    have h := integrableOn_mul_sum_Icc primeLogWeight (m := 0)
      (le_of_lt (lt_trans zero_lt_one ha)) hfd.integrableOn_Icc
    simp only [prefix_primeLogWeight] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hmain : (∫ t in Set.Ioc a b, deriv invLogWeight t * t) +
      (∫ t in Set.Ioc a b, invLogWeight t) = invLogWeight b * b - invLogWeight a * a := by
    rw [← integral_add hlin hf, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      rw [deriv_invLogWeight (lt_of_lt_of_le ha ht.1)]
      simpa only [one_mul, mul_one] using!
        ((hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).mul (hasDerivAt_id t))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hlin.add hf)
  have hrem : (∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)) =
      (∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t) -
      (∫ t in Set.Ioc a b, deriv invLogWeight t * t) := by
    simp_rw [mul_sub]
    exact integral_sub htheta hlin
  have hAbel := abel_theta ha hab
  linear_combination hAbel - hmain + hrem

theorem hasDerivAt_loglog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => Real.log (Real.log x)) (invLogWeight t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! (Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0) using 1
  all_goals try with_reducible_and_instances rfl
  simp [invLogWeight, one_div, mul_inv_rev, mul_comm]

theorem integral_invLogWeight {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, invLogWeight t) = Real.log (Real.log b) - Real.log (Real.log a) := by
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_loglog (lt_of_lt_of_le ha ht.1)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

end ErdosPrimeInputs.PrimeAbel



namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset
open PrimeAbel

noncomputable def intervalGuard (leftClosed rightClosed : Bool) (a b t : ℝ) : Prop :=
  (if leftClosed then a ≤ t else a < t) ∧ (if rightClosed then t ≤ b else t < b)

noncomputable def intervalSum (leftClosed rightClosed : Bool) (a b : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ Nat.primesLE ⌊b⌋₊,
    if intervalGuard leftClosed rightClosed a b (n : ℝ) then (n : ℝ)⁻¹ else 0

lemma reciprocal_eq_core {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) :
    reciprocalPrimes a b = ∑ n ∈ Nat.primesLE ⌊b⌋₊, if a < (n : ℝ) then (n : ℝ)⁻¹ else 0 := by
  rw [reciprocalPrimes, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  rw [Nat.floor_lt ha]
  tauto

lemma selection_difference_bound (p q : Prop) [Decidable p] [Decidable q] {w : ℝ} (hw : 0 ≤ w) :
    |(if p then w else 0) - (if q then w else 0)| ≤ w := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, abs_of_nonneg hw, hw]

lemma fiber_sum_le (s : Finset ℕ) (x : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (∑ n ∈ s, if (n : ℝ) = x then w else 0) ≤ w := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (s.filter (fun n : ℕ => (n : ℝ) = x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro n hn m hm
    have h := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
    exact_mod_cast h
  have hr : ((s.filter (fun n : ℕ => (n : ℝ) = x)).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hw

end ErdosPrimeInputs.PrimeEndpoints



namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter _root_.Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel

noncomputable def decay (c t : ℝ) : ℝ := Real.exp (-c * Real.sqrt (Real.log t))
noncomputable def tailKernel (c t : ℝ) : ℝ := decay c t / (t * Real.sqrt (Real.log t))

lemma decay_pos (c t : ℝ) : 0 < decay c t := Real.exp_pos _

lemma decay_antitone {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    decay c b ≤ decay c a := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (Real.log_le_log ha hab)
  nlinarith

lemma hasDerivAt_decay {c t : ℝ} (ht : 1 < t) :
    HasDerivAt (decay c) (-(c / 2) * tailKernel c t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht))
  have h := (((Real.hasDerivAt_sqrt hl0).comp t (Real.hasDerivAt_log ht0)).const_mul (-c)).exp
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [tailKernel, decay]
  field_simp

lemma tailKernel_continuousOn {c a b : ℝ} (ha : 1 < a) :
    ContinuousOn (tailKernel c) (Set.Icc a b) := by
  intro t ht
  have ht1 := lt_of_lt_of_le ha ht.1
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht1))
  apply ContinuousAt.continuousWithinAt
  unfold tailKernel decay
  fun_prop (disch := simp [ht0, hs0])

lemma hasDerivAt_tailPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (fun t => -(2 / c) * decay c t) (tailKernel c t) t := by
  convert! (hasDerivAt_decay ht).const_mul (-(2 / c)) using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma tailIntegral {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) = (2 / c) * (decay c a - decay c b) := by
  have h : (∫ t in a..b, tailKernel c t) = -(2 / c) * decay c b - (-(2 / c) * decay c a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hasDerivAt_tailPrimitive hc (lt_of_lt_of_le ha ht.1)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  rw [intervalIntegral.integral_of_le hab] at h
  rw [h]
  ring

lemma tailIntegral_le {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) ≤ (2 / c) * decay c a := by
  rw [tailIntegral hc ha hab]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (decay_pos c b).le) (by positivity)

lemma kernel_comparison {t : ℝ} (ht : 1 < t) (hl : 1 ≤ Real.log t) :
    errorKernel t * t ≤ 2 / (t * Real.sqrt (Real.log t)) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  have hs0 : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hl0
  have hsle : Real.sqrt (Real.log t) ≤ Real.log t := by
    have hs2 := Real.sq_sqrt hl0.le
    have hs := Real.sqrt_nonneg (Real.log t)
    nlinarith
  calc
    errorKernel t * t = (Real.log t + 1) / (t * Real.log t ^ 2) := by
      unfold errorKernel
      field_simp
    _ ≤ (2 * Real.log t) / (t * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 / (t * Real.log t) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hs0)
      (mul_le_mul_of_nonneg_left hsle ht0.le)

lemma endpoint_error_bound {c C t : ℝ} (hC : 0 ≤ C) (ht : 1 < t) (hl : 1 ≤ Real.log t)
    (hθ : |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |invLogWeight t * (Chebyshev.theta t - t)| ≤ C * decay c t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  rw [abs_mul, abs_of_nonneg (show 0 ≤ invLogWeight t by unfold invLogWeight; positivity)]
  calc
    _ ≤ invLogWeight t * (C * errorScale c t) :=
      mul_le_mul_of_nonneg_left hθ (by unfold invLogWeight; positivity)
    _ = C * decay c t / Real.log t := by unfold invLogWeight errorScale decay; field_simp
    _ ≤ C * decay c t := div_le_self (mul_nonneg hC (decay_pos c t).le) hl

lemma integral_error_bound {c C a b : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 1 < a) (hla : 1 ≤ Real.log a) (hab : a ≤ b)
    (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| ≤
      (4 * C / c) * decay c a := by
  have hi : IntegrableOn (fun t => (2 * C) * tailKernel c t) (Set.Ioc a b) :=
    ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have hb : ∀ t ∈ Set.Ioc a b,
      ‖deriv invLogWeight t * (Chebyshev.theta t - t)‖ ≤ (2 * C) * tailKernel c t := by
    intro t ht
    have ht1 : 1 < t := lt_trans ha ht.1
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlt : 1 ≤ Real.log t := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) ht.1.le)
    have hk0 : 0 ≤ errorKernel t := by unfold errorKernel; positivity
    rw [deriv_invLogWeight ht1, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hk0]
    calc
      _ ≤ errorKernel t * (C * errorScale c t) := mul_le_mul_of_nonneg_left (hθ t ⟨ht.1.le, ht.2⟩) hk0
      _ = (errorKernel t * t) * (C * decay c t) := by unfold errorScale decay; ring
      _ ≤ (2 / (t * Real.sqrt (Real.log t))) * (C * decay c t) :=
        mul_le_mul_of_nonneg_right (kernel_comparison ht1 hlt) (mul_nonneg hC (decay_pos c t).le)
      _ = _ := by unfold tailKernel; ring
  have hint := norm_integral_le_of_norm_le hi (ae_restrict_of_forall_mem measurableSet_Ioc hb)
  rw [integral_const_mul] at hint
  calc
    _ ≤ (2 * C) * ∫ t in Set.Ioc a b, tailKernel c t := hint
    _ ≤ (2 * C) * ((2 / c) * decay c a) :=
      mul_le_mul_of_nonneg_left (tailIntegral_le hc ha hab) (by positivity)
    _ = _ := by ring

end ErdosPrimeInputs.PrimeErrorDecay



namespace ErdosPrimeInputs.HarmonicPrimeMeasure

open _root_.Filter _root_.Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay

lemma reciprocal_le_decay {c : ℝ} (hc : 0 < c) :
    ∀ᶠ a : ℝ in atTop, a⁻¹ ≤ decay c a := by
  filter_upwards [sqrt_le_errorScale hc, eventually_ge_atTop (1 : ℝ)] with a hs ha
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h := le_trans (Real.one_le_sqrt.mpr ha) hs
  rw [inv_eq_one_div]
  apply (div_le_iff₀ ha0).mpr
  simpa only [errorScale, decay, mul_comm] using h

noncomputable def primeExponent (w : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log w

noncomputable def harmonicMass (w : ℝ) (lc rc : Bool) (u v : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ Nat.primesLE ⌊w ^ v⌋₊,
    if intervalGuard lc rc u v (primeExponent w p) then (p : ℝ)⁻¹ else 0

lemma exponent_le_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    Real.log p / Real.log w ≤ t ↔ p ≤ w ^ t := by
  rw [div_le_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_le_log_iff hp (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t)]

lemma exponent_lt_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    Real.log p / Real.log w < t ↔ p < w ^ t := by
  rw [div_lt_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_lt_log_iff hp (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t)]

lemma le_exponent_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    t ≤ Real.log p / Real.log w ↔ w ^ t ≤ p := by
  rw [le_div_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_le_log_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t) hp]

lemma lt_exponent_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    t < Real.log p / Real.log w ↔ w ^ t < p := by
  rw [lt_div_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t) hp]

lemma harmonicMass_eq_intervalSum {w : ℝ} (hw : 1 < w) (lc rc : Bool) (u v : ℝ) :
    harmonicMass w lc rc u v = intervalSum lc rc (w ^ u) (w ^ v) := by
  classical
  unfold harmonicMass intervalSum
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hg : intervalGuard lc rc u v (primeExponent w p) ↔
      intervalGuard lc rc (w ^ u) (w ^ v) (p : ℝ) := by
    cases lc <;> cases rc <;>
      simp only [intervalGuard, primeExponent, Bool.false_eq_true, ite_true, if_true, ite_false, if_false,
        exponent_le_iff hw hp0, exponent_lt_iff hw hp0, le_exponent_iff hw hp0, lt_exponent_iff hw hp0]
  simp only [hg]

end ErdosPrimeInputs.HarmonicPrimeMeasure



namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter _root_.Asymptotics _root_.Finset
open scoped Topology
open PrimeAbel PrimeErrorDecay

noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)

end ErdosPrimeInputs.MertensStrong



namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure

noncomputable def primesBetween (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter (fun p => a < (p : ℝ))

def decreasingPrefixes (s : Finset ℕ) : Finset (List ℕ) :=
  s.powerset.image (fun t => t.sort (· ≥ ·))

noncomputable def prefixWeight (l : List ℕ) : ℝ := (l.map (fun p : ℕ => (p : ℝ)⁻¹)).prod

lemma mem_decreasingPrefixes {s : Finset ℕ} {l : List ℕ} :
    l ∈ decreasingPrefixes s ↔ l.Pairwise (· > ·) ∧ ∀ p ∈ l, p ∈ s := by
  constructor
  · intro hl
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨t.sortedGT_sort.pairwise, ?_⟩
    intro p hp
    apply (Finset.mem_powerset.mp ht)
    simpa using hp
  · rintro ⟨hp, hs⟩
    have hn : l.Nodup := hp.imp (fun h => ne_of_gt h)
    have hge : l.Pairwise (· ≥ ·) := hp.imp (fun h => le_of_lt h)
    apply Finset.mem_image.mpr
    refine ⟨l.toFinset, Finset.mem_powerset.mpr ?_, (List.toFinset_sort (· ≥ ·) hn).mpr hge⟩
    intro p hp
    exact hs p (List.mem_toFinset.mp hp)

end ErdosPrimeInputs.PrimePrefixMass



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

noncomputable def longPrefixMass (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ l ∈ (decreasingPrefixes s).filter (fun l => m ≤ l.length), prefixWeight l

end ErdosPrimeInputs.PrimePrefixTail



namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset
open HarmonicPrimeMeasure PrimePrefixMass

noncomputable def remainingGap (r₀ w : ℝ) (l : List ℕ) : ℝ :=
  r₀ - (l.map (primeExponent w)).sum

def cutoff (x : ℕ → ℝ) : ℝ → List ℕ → ℝ
  | B, [] => B
  | _, p :: ps => cutoff x (x p) ps

noncomputable def primeCutoff (w B : ℝ) (l : List ℕ) : ℝ := cutoff (primeExponent w) B l

lemma exponent_monotone {w : ℝ} (hw : 1 < w) : Monotone (primeExponent w) := by
  intro p q hpq
  have hlogw : 0 ≤ Real.log w := (Real.log_pos hw).le
  by_cases hp : p = 0
  · subst p
    simp only [primeExponent, Nat.cast_zero, Real.log_zero, zero_div]
    exact div_nonneg (Real.log_natCast_nonneg q) hlogw
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    exact div_le_div_of_nonneg_right (Real.log_le_log hp0 (by exact_mod_cast hpq)) hlogw

noncomputable def hasHighState (r₀ w B S : ℝ) (l : List ℕ) : Prop :=
  ∃ pre suf : List ℕ, l = pre ++ suf ∧
    S < remainingGap r₀ w pre / primeCutoff w B pre

end ErdosPrimeInputs.HighPrimeGeometry



namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset
open PrimePrefixMass PrimePrefixTail HighPrimeGeometry

noncomputable def lowGapHighMass (r₀ w B ell S K : ℝ) : ℝ := by
  classical
  exact ∑ l ∈ (decreasingPrefixes (primesBetween (w ^ ell) (w ^ B))).filter
    (fun l => remainingGap r₀ w l ≤ K ∧ hasHighState r₀ w B S l), prefixWeight l

noncomputable def rewardedHighMass (r₀ w B ell S c : ℝ) : ℝ := by
  classical
  exact ∑ l ∈ (decreasingPrefixes (primesBetween (w ^ ell) (w ^ B))).filter
    (fun l => hasHighState r₀ w B S l ∧ 0 ≤ remainingGap r₀ w l),
      prefixWeight l * Real.exp (-c * remainingGap r₀ w l)

end ErdosPrimeInputs.HighPrimeMass



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_HarmonicReferenceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicReferenceMeasure

open _root_.MeasureTheory _root_.Set
open ErdosMonotoneQuadrature ErdosPrimeInputs.PrimeEndpoints

noncomputable def referenceMeasure (u v : ℝ) : Measure ℝ :=
  reciprocalMeasure (volume.restrict (Icc u v)) u

end NumberTheoryLean.HarmonicReferenceMeasure

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ActualPrimeQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicPrimeAtomicMeasure

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def primeAtom (w : ℝ) (p : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((p:ℝ)⁻¹) • Measure.dirac (primeExponent w p)

noncomputable def primeMeasure (w V : ℝ) : Measure ℝ :=
  ∑ p ∈ Nat.primesLE ⌊w^V⌋₊,primeAtom w p

instance primeAtom_finite (w : ℝ) (p : ℕ) : IsFiniteMeasure (primeAtom w p) := by
  constructor
  simp [primeAtom,Measure.smul_apply]

instance primeMeasure_finite (w V : ℝ) : IsFiniteMeasure (primeMeasure w V) := by
  unfold primeMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.HarmonicPrimeAtomicMeasure

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open ErdosMonotoneQuadrature ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure

noncomputable def boundaryPrimeError (c C w : ℝ) : ℝ := C*Real.exp (-c*Real.sqrt (Real.log w))

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LinearSieveFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LinearSieveFunctions

open MeasureTheory Filter
open scoped Topology

noncomputable def startingExtension (A s : ℝ) : ℝ := A * Real.log (s - 1) / s

end NumberTheoryLean.LinearSieveFunctions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set

noncomputable def nextExponent (r t : ℝ) : ℝ := r / (t + 1)
noncomputable def nextGap (r t : ℝ) : ℝ := r * t / (t + 1)

noncomputable def finalGap : ℝ → List ℝ → ℝ
  | r, [] => r
  | r, t :: ts => finalGap (nextGap r t) ts

def finalRatio : ℝ → List ℝ → ℝ
  | s, [] => s
  | _, t :: ts => finalRatio t ts

theorem nextGap_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < nextGap r t := by
  unfold nextGap
  positivity

theorem gap_exponent_conservation {r t : ℝ} (ht : 0 < t) :
    nextGap r t + nextExponent r t = r := by
  unfold nextGap nextExponent
  field_simp

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped ENNReal

abbrev Hist (X : Type*) (n : ℕ) := ∀ _ : Finset.Iic n, X

def last {X : Type*} (n : ℕ) (h : Hist X n) : X := h ⟨n, by simp⟩

def mapHist {X Y : Type*} (f : X → Y) (n : ℕ) (h : Hist X n) : Hist Y n :=
  fun k => f (h k)

noncomputable def extend {X : Type*} [MeasurableSpace X] (n : ℕ)
    (h : Hist X n) (x : X) : Hist X (n+1) :=
  _root_.IicProdIoc (X := fun _ => X) n (n+1) (h, piSingleton (X := fun _ => X) n x)

theorem mapHist_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) (n : ℕ) : Measurable (mapHist f n) := by
  exact Measurable.of_eval (fun k => hf.comp (measurable_pi_apply k))

theorem last_measurable_for_comap {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (last (X := X) n) := measurable_pi_apply _

noncomputable def pastKernel {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) (n : ℕ) : Kernel (Hist X n) X :=
  K.comap (last n) (last_measurable_for_comap n)

instance pastKernel_sfinite {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (pastKernel K n) := by
  unfold pastKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def pathKernel {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) (n : ℕ) : Kernel (Hist X 0) (Hist X n) :=
  Kernel.partialTraj (X := fun _ => X) (pastKernel K) 0 n

instance pathKernel_sfinite {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (pathKernel K n) := by
  unfold pathKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

instance pastKernel_markov (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (pastKernel K n) := by
  unfold pastKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance pathKernel_markov (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (pathKernel K n) := by
  unfold pathKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem last_measurable (n : ℕ) : Measurable (last (X := X) n) :=
  measurable_pi_apply _

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryOccurrence
open Set MeasureTheory ProbabilityTheory FiniteHistoryTransport
variable {X : Type*} [MeasurableSpace X]

def atIndex (N : ℕ) (h : Hist X N) (j : Fin (N+1)) : X :=
  h ⟨j.1,Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩

noncomputable def arrivalOccurrence (E : Set X) (N : ℕ) : Set (Hist X N) :=
  ⋃ j : Fin N,{h | atIndex N h j.succ ∈ E}

end NumberTheoryLean.FiniteHistoryOccurrence



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

noncomputable def pathSum (F : X → ℝ) (n : ℕ) (h : Hist X n) : ℝ :=
  ∑ j : Fin n, F (h ⟨j,by exact Finset.mem_Iic.mpr j.isLt.le⟩)

end NumberTheoryLean.FiniteHistoryTransport


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def childRatio (w r : ℝ) (p : ℕ) : ℝ := r / primeExponent w p - 1

noncomputable def capGuard (closed : Bool) (cap x : ℝ) : Prop :=
  if closed then x ≤ cap else x < cap

theorem nextExponent_childRatio {w r : ℝ} {p : ℕ} (hr : 0 < r) (hp : 0 < primeExponent w p) :
    nextExponent r (childRatio w r p) = primeExponent w p := by
  unfold nextExponent childRatio
  simp only [sub_add_cancel]
  field_simp

theorem nextGap_childRatio {w r : ℝ} {p : ℕ} (hr : 0 < r) (hp : 0 < primeExponent w p)
    (ht : 0 < childRatio w r p) : nextGap r (childRatio w r p) = r - primeExponent w p := by
  have h := gap_exponent_conservation (r := r) ht
  rw [nextExponent_childRatio hr hp] at h
  linarith

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeRatioBins

open FinitePathGeometry PrimeTiltGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def ratioBin (w r a b : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w ^ (r/(a+1))⌋₊).filter
    (fun p => a ≤ childRatio w r p ∧ childRatio w r p < b)

theorem primeExponent_pos {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p.Prime) : 0 < primeExponent w p := by
  apply div_pos
  · apply Real.log_pos
    exact_mod_cast hp.one_lt
  · exact Real.log_pos hw

theorem bin_log_width {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    Real.log (r/(a+1)) - Real.log (r/(b+1)) = Real.log (b+1)-Real.log (a+1) := by
  rw [Real.log_div hr.ne' (by linarith : a+1 ≠ 0), Real.log_div hr.ne' (by linarith : b+1 ≠ 0)]
  ring

end NumberTheoryLean.PrimeRatioBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

noncomputable def boundaryPrimes (w : ℝ) : Finset ℕ := primesBetween w (w^(2:ℝ))

end NumberTheoryLean.ReferenceAdmission


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def survivorProduct (P : Finset ℕ) : ℝ := ∏ p ∈ P,(1-(p : ℝ)⁻¹)

end NumberTheoryLean.ReferencePruning

end

section

namespace NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable
open _root_.Finset
open ReferencePruning ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.MertensStrong

noncomputable def availablePrimes (a x : ℝ) (closed : Bool) : Finset ℕ :=
  (primesBetween a x).filter (fun p => closed=true ∨ (p:ℝ)<x)

noncomputable def availableProduct (a x : ℝ) (closed : Bool) : ℝ :=
  survivorProduct (availablePrimes a x closed)

@[simp] theorem availablePrimes_closed (a x : ℝ) : availablePrimes a x true=primesBetween a x := by
  simp [availablePrimes]

end NumberTheoryLean.ReferenceProductsBasics

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ReferenceSourcePrimeSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ReferenceMertens

open _root_.Filter _root_.Asymptotics
open scoped Topology
open ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

noncomputable def referenceProduct (w b : ℝ) (closed : Bool) : ℝ :=
  availableProduct w (w^b) closed

end NumberTheoryLean.ReferenceMertens

end

section

namespace NumberTheoryLean.ReferenceSourcePrimeSets

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeTiltGeometry ReferenceAdmission ReferencePruning ReferenceProductsBasics
open ReferenceMertens
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

noncomputable def sourcePrimes (w b : ℝ) (closed : Bool) : Finset ℕ := availablePrimes w (w^b) closed
noncomputable def highPrimes (w b : ℝ) (closed : Bool) : Finset ℕ :=
  (sourcePrimes w b closed).filter (fun p => w^(2:ℝ)<(p:ℝ))

@[simp] theorem sourcePrimes_boundary (w : ℝ) : sourcePrimes w 2 true=boundaryPrimes w := by
  simp only [sourcePrimes,availablePrimes_closed,boundaryPrimes]

end NumberTheoryLean.ReferenceSourcePrimeSets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_BoundaryProductLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.ReferenceAdmission NumberTheoryLean.ReferencePruning
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ReferenceMertens

noncomputable def boundaryProduct (w : ℝ) : ℝ := survivorProduct (boundaryPrimes w)

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def referenceDepth (r : ℝ) : ℕ := ⌈max r 0⌉₊+3

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagSubbinWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins

noncomputable def count (w Cs : ℝ) : ℕ := ⌈w ^ (2 * Cs + 10)⌉₊
noncomputable def step (R theta : ℝ) (N : ℕ) : ℝ := R * theta / N
noncomputable def left (R theta : ℝ) (N i : ℕ) : ℝ := R + i * step R theta N
noncomputable def right (R theta : ℝ) (N i : ℕ) : ℝ := R + (i + 1 : ℕ) * step R theta N
noncomputable def width (R theta : ℝ) (N i : ℕ) : ℝ := step R theta N / left R theta N i

theorem step_pos {R theta : ℝ} {N : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < step R theta N := by unfold step; positivity

theorem left_lower {R theta : ℝ} {N i : ℕ} (hs : 0 ≤ step R theta N) :
    R ≤ left R theta N i := by unfold left; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hs)

theorem right_sub_left (R theta : ℝ) (N i : ℕ) :
    right R theta N i - left R theta N i = step R theta N := by
  simp only [right, left, Nat.cast_add, Nat.cast_one] <;> ring

theorem right_eq_left_add (R theta : ℝ) (N i : ℕ) :
    right R theta N i = left R theta N i + step R theta N := by
  linarith [right_sub_left R theta N i]

theorem total_step {R theta : ℝ} {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * step R theta N = R * theta := by
  unfold step; field_simp

theorem left_pos {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < left R theta N i :=
  hR.trans_le (left_lower (step_pos hR ht hN).le)

theorem width_pos {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < width R theta N i :=
  div_pos (step_pos hR ht hN) (left_pos hR ht hN)

theorem local_endpoint {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : (1 + width R theta N i) * left R theta N i = right R theta N i := by
  have hl := ne_of_gt (left_pos (i := i) hR ht hN)
  rw [width, add_mul, one_mul, div_mul_cancel₀ _ hl, right_eq_left_add]

theorem endpoints_ordered {R theta : ℝ} {N i j : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) (hij : i < j) : right R theta N i ≤ left R theta N j := by
  have hij' : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hij
  unfold right left
  exact add_le_add_right (mul_le_mul_of_nonneg_right hij' (step_pos hR ht hN).le) R

theorem exists_unique_index {R theta x : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hx : R < x) (hx' : x ≤ (1 + theta) * R) :
    ∃! i : Fin N, left R theta N i < x ∧ x ≤ right R theta N i := by
  let u := (x - R) / step R theta N
  have hs := step_pos hR ht hN
  have hu : 0 < u := div_pos (sub_pos.mpr hx) hs
  have hceil : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.mpr hu
  have huN : u ≤ N := by
    apply (div_le_iff₀ hs).mpr
    rw [total_step hN]
    nlinarith only [hx']
  have hkN : ⌈u⌉₊ ≤ N := Nat.ceil_le.mpr huN
  let i : Fin N := ⟨⌈u⌉₊ - 1, by omega⟩
  have hki : (i : ℕ) + 1 = ⌈u⌉₊ := by dsimp [i]; omega
  have hceil0 : ⌈u⌉₊ ≠ 0 := by omega
  have hlo := ((Nat.ceil_eq_iff hceil0).mp rfl).1
  have hhi := Nat.le_ceil u
  have himem : left R theta N i < x ∧ x ≤ right R theta N i := by
    constructor
    · have h := (lt_div_iff₀ hs).mp hlo
      change R + (↑(⌈u⌉₊ - 1) : ℝ) * step R theta N < x
      linarith only [h]
    · have h := (div_le_iff₀ hs).mp hhi
      dsimp [right]
      rw [hki]
      linarith only [h]
  refine ⟨i, himem, ?_⟩
  intro j hj
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjlt | hilt
  · have h := endpoints_ordered hR ht hN hjlt
    linarith only [h, himem.1, hj.2]
  · have h := endpoints_ordered hR ht hN hilt
    linarith only [h, himem.2, hj.1]

end ErdosTagSubbins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_CanonicalTagPrimePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins
open ErdosInversePrimeBin

noncomputable def subbin (R theta : ℝ) (N i : ℕ) : Finset ℕ :=
  primeBin (left R theta N i) (width R theta N i)

theorem mem_subbin {R theta : ℝ} {N i p : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : p ∈ subbin R theta N i ↔
      p.Prime ∧ left R theta N i < (p : ℝ) ∧ (p : ℝ) ≤ right R theta N i := by
  unfold subbin
  rw [mem_primeBin (left_pos hR ht hN).le (width_pos hR ht hN).le,
    local_endpoint hR ht hN]

theorem unique_prime_subbin {R theta : ℝ} {N p : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hp : p ∈ primeBin R theta) :
    ∃! i : Fin N, p ∈ subbin R theta N i := by
  obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBin hR.le ht.le p).mp hp
  obtain ⟨i, hi, hu⟩ := exists_unique_index hR ht hN hlo hhi
  refine ⟨i, (mem_subbin hR ht hN).mpr ⟨hprime, hi⟩, ?_⟩
  intro j hj
  exact hu j ((mem_subbin hR ht hN).mp hj).2

end ErdosTagSubbins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HeightBlockCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosLargeHeightBlocks

noncomputable def blockCount (C0 : ℤ) (R xi : ℝ) (H : ℕ) : ℕ :=
  max 1 ⌈xi*|(C0 : ℝ)|/(R*(H : ℝ))⌉₊

theorem blockCount_pos (C0 : ℤ) (R xi : ℝ) (H : ℕ) : 0 < blockCount C0 R xi H := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

end ErdosLargeHeightBlocks


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

noncomputable def incrementProbability (p : ℝ) : ℝ := 1 / (p - 1) ^ 2
noncomputable def geometricMass (p : ℝ) (j : ℕ) : ℝ := (1 - 1 / p) * (1 / p) ^ j
noncomputable def bernoulliMass (p : ℝ) (b : Bool) : ℝ :=
  if b then incrementProbability p else 1 - incrementProbability p
noncomputable def eulerMass (p : ℝ) : ℕ → ℝ
  | 0 => (p - 2) / (p - 1)
  | j + 1 => (1 / p) ^ (j + 1)

abbrev Sample := Bool × ℕ
noncomputable def jointMass (p : ℝ) (s : Sample) : ℝ :=
  bernoulliMass p s.1 * geometricMass p s.2
def lowerExponent (s : Sample) : ℕ := s.2
def upperExponent (s : Sample) : ℕ := s.2 + if s.1 then 1 else 0

end EulerPrimeLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_UniformMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

noncomputable def integerLogMoment (n : ℕ) : ℝ := Real.log (n : ℝ) / ((n : ℝ) - 1) ^ 2

noncomputable def uniformMomentBound : ℝ := 1 + ∑' n : ℕ, integerLogMoment n

end EulerPrimeLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ProductRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

abbrev Outcomes (E : Finset ℕ) := E → Sample
noncomputable def productMass (E : Finset ℕ) (s : Outcomes E) : ℝ :=
  ∏ p : E, jointMass (p : ℝ) (s p)
noncomputable def excessLog (E : Finset ℕ) (s : Outcomes E) : ℝ :=
  ∑ p : E, ((upperExponent (s p) - lowerExponent (s p) : ℕ) : ℝ) * Real.log (p : ℝ)
noncomputable def eventMass (E : Finset ℕ) (A : Outcomes E → Prop) : ℝ :=
  ∑' s : Outcomes E, if A s then productMass E s else 0

end EulerWeightedLower



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

def integerProduct (E : Finset ℕ) (k : E → ℕ) : ℕ := ∏ p : E, (p : ℕ) ^ k p

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CouplingEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

noncomputable def lowerInteger (E : Finset ℕ) (s : Outcomes E) : ℕ :=
  integerProduct E (fun p => lowerExponent (s p))
noncomputable def upperInteger (E : Finset ℕ) (s : Outcomes E) : ℕ :=
  integerProduct E (fun p => upperExponent (s p))

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

noncomputable def paperWeight (E : Finset ℕ) (d : ℕ) : ℝ :=
  ∏ p ∈ E with ¬p ∣ d, (1 - 1 / ((p : ℝ) - 1))
noncomputable def ordinaryProduct (E : Finset ℕ) : ℝ :=
  ∏ p ∈ E, (1 - 1 / (p : ℝ))

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

def supportedIntegers (E : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ E)
noncomputable def weightedSmallSum (E : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ d ∈ supportedIntegers E N, paperWeight E d / (d : ℝ)
noncomputable def ordinarySmallSum (E : Finset ℕ) (N : ℕ) : ℝ :=
  ordinaryProduct E * ∑ d ∈ supportedIntegers E N, 1 / (d : ℝ)

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

def restrictOutcomes {E F : Finset ℕ} (hEF : E ⊆ F) (s : Outcomes F) : Outcomes E :=
  fun p => s ⟨p, hEF p.property⟩

def retainedIndexEquiv {E F : Finset ℕ} (hEF : E ⊆ F) :
    {p : F // (p : ℕ) ∈ E} ≃ E where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨⟨p, hEF p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def primesThrough (P : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊P⌋₊).filter Nat.Prime

noncomputable def uniformLowerEnvelope (P : ℝ) : ℝ :=
  (94 / 100 : ℝ) * Real.log P * ordinaryProduct (primesThrough P) -
    100 * uniformMomentBound / Real.log P

end EulerWeightedLower


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_RieszMellinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def rieszWeight (x : ℝ) : ℝ := max (1-x) 0
noncomputable def rieszProfile (x : ℝ) : ℂ :=
  (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) x -
    (Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ)) x

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped BigOperators

noncomputable def rieszSum (f : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), f n*(rieszWeight ((n:ℝ)/X):ℂ)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RecoveryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace Erdos970Dependency.SiegelWalfisz

noncomputable def rieszDifferenceWeight (delta u : ℝ) : ℝ :=
  (max (1+delta-u) 0-max (1-u) 0)/delta




open scoped BigOperators

noncomputable def sharpSum (f : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), f n
noncomputable def rieszRecovery (f : ℕ → ℂ) (X delta : ℝ) : ℂ :=
  (((1+delta:ℝ):ℂ)*rieszSum f ((1+delta)*X)-rieszSum f X)/(delta:ℂ)

end Erdos970Dependency.SiegelWalfisz



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCountAbel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.PrimeCountAbel

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology

noncomputable def logarithmicIntegral (x : ℝ) : ℝ := ∫ t in 2..x, 1 / Real.log t

end ErdosPrimeInputs.PrimeCountAbel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SignedIntervalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def retainedLength (a b t : ℝ) : ℝ := if t ≤ b-a then b-a else 0

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

noncomputable def admissiblePairs (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    Finset (ℕ × ℤ) := (T.product M).filter (fun pm => good pm.1 pm.2)

end ErdosStoppedArithmetic



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RationalParameterInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
attribute [local instance] Classical.decEq

def parameterLower (r : ℚ) (d : ℕ) : ℤ := -((r.num-(r.den : ℤ))/(d : ℤ))
def parameterUpper (Y : ℕ) (r : ℚ) (d : ℕ) : ℤ := ((r.den : ℤ)*(Y : ℤ)-r.num)/(d : ℤ)
noncomputable def parameterInterval (Y : ℕ) (r : ℚ) (d : ℕ) : Finset ℤ :=
  Finset.Icc (parameterLower r d) (parameterUpper Y r d)

def parameterValue (r : ℚ) (d : ℕ) (m : ℤ) : ℕ :=
  ((r.num+(d : ℤ)*m)/(r.den : ℤ)).toNat

end ErdosAlignedProgression

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RationalCandidateSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment

def parameterOf (r : ℚ) (d t : ℕ) : ℤ := ((r.den : ℤ)*(t : ℤ)-r.num)/(d : ℤ)

end ErdosAlignedProgression

end

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def parameterCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) : Finset ℤ :=
  (parameterInterval Y r d).filter (fun m =>
    (r.den : ℤ) ∣ r.num+(d : ℤ)*m ∧ ∀ p ∈ small, parameterValue r d m % p ≠ a p % p)

end ErdosAlignedProgression

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_HypotheticalResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts
attribute [local instance] Classical.decEq

noncomputable def hypotheticalResidue (r : ℚ) (p : ℕ) [NeZero p] : ℕ :=
  ((r.num : ZMod p)*(r.den : ZMod p)⁻¹).val

noncomputable def hypotheticalClass (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p] : ℕ → ℕ :=
  Function.update a p (hypotheticalResidue r p)

end ErdosHypotheticalTag

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HypotheticalPairRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedArithmetic
open ErdosAlignedProgression ErdosHypotheticalTag ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.propDecidable

noncomputable def hypotheticalRowCount (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T) : ℝ :=
  (modulusCount Y small (@hypotheticalClass a r p.val ⟨(hT p.val p.property).ne_zero⟩) (p.val*q) : ℝ)

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonSliceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosCommonParameterInterval

noncomputable def commonLower (a R T : ℝ) : ℝ := max (a/R) (a/T)
noncomputable def commonUpper (b R T : ℝ) : ℝ := min (b/R) (b/T)

end ErdosCommonParameterInterval



namespace ErdosCommonMInterval
open ErdosCommonParameterInterval

noncomputable def lower (A q R T : ℝ) : ℝ := commonLower (-A/q) R T + 1
noncomputable def upper (A D Y q R T : ℝ) : ℝ := commonUpper ((D*Y-A)/q) R T
noncomputable def interval (A D Y q R T : ℝ) : Set ℝ :=
  Set.Icc (lower A q R T) (upper A D Y q R T)
noncomputable def referenceLength (Y R q : ℝ) : ℝ := Y/(R*q)
noncomputable def lengthExponent (P Y R q : ℝ) : ℝ := Real.log (referenceLength Y R q)/Real.log P

def decode (A m : ℤ) (D q p : ℕ) : ℕ :=
  ((A+(p : ℤ)*q*m)/(D : ℤ)).toNat

end ErdosCommonMInterval



section

open _root_.Filter
open scoped Topology
namespace ErdosCommonMInterval

noncomputable def relativeError (w : ℝ) : ℝ := 4*w^(-8 : ℝ)+w^(-2 : ℝ)

end ErdosCommonMInterval

end


namespace ErdosLargeHeightBlocks

noncomputable def blockLeft (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  ErdosTagSubbins.left R xi (blockCount C0 R xi H) i
noncomputable def blockRight (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  ErdosTagSubbins.right R xi (blockCount C0 R xi H) i

noncomputable def coordinateLower (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)
noncomputable def coordinateUpper (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)+(H : ℝ)

end ErdosLargeHeightBlocks



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_OriginalPrimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosLargeHeightBlocks


noncomputable def blockPrimes (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : Finset ℕ :=
  ErdosTagSubbins.subbin R xi (blockCount C0 R xi H) i

theorem unique_original_prime_block (C0 : ℤ) (R xi : ℝ) (H p : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hp : p ∈ ErdosInversePrimeBin.primeBin R xi) :
    ∃! i : Fin (blockCount C0 R xi H), p ∈ blockPrimes C0 R xi H i :=
  ErdosTagSubbins.unique_prime_subbin hR hxi (blockCount_pos C0 R xi H) hp

end ErdosLargeHeightBlocks


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualCoordinateBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceEffective

noncomputable def intervalK (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) : ℕ :=
  ((-(C0 : ZMod p))*(↑((ZMod.unitOfCoprime H hHp)⁻¹) : ZMod p)).val

noncomputable def intervalM0 (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) : ℤ :=
  (C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ))/(p : ℤ)

end ErdosVarianceEffective



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FiniteMonotoneComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteMonotoneComparison

open Filter Set Finset MeasureTheory
open scoped ENNReal

 theorem finite_level_bound (μ ν : Measure ℝ) (A : Finset ℝ) (f : ℝ → ℝ) (a M t : ℝ) (E : ℝ≥0∞)
    (hsupport : ∀ᵐ x ∂μ, x ∈ A) (hloc : ∀ x ∈ A, a ≤ x)
    (hanti : AntitoneOn f (Ici a)) (hM : ∀ x ∈ A, f x ≤ M)
    (hcdf : ∀ x ∈ A, μ (Icc a x) ≤ ν (Icc a x) + E) :
    μ {x | t < f x} ≤ ν {x | t < f x} + (Iio M).indicator (fun _ => E) t := by
  classical
  let B := A.filter (fun x => t < f x)
  by_cases hB : B.Nonempty
  · let x := B.max' hB
    have hxB : x ∈ B := B.max'_mem hB
    have hx : x ∈ A := (Finset.mem_filter.mp hxB).1
    have htx : t < f x := (Finset.mem_filter.mp hxB).2
    have htM : t < M := htx.trans_le (hM x hx)
    rw [indicator_of_mem (show t ∈ Iio M from htM)]
    have hμ : μ {y | t < f y} ≤ μ (Icc a x) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with y hy
      intro hyt
      exact ⟨hloc y hy, B.le_max' y (Finset.mem_filter.mpr ⟨hy,hyt⟩)⟩
    have hν : ν (Icc a x) ≤ ν {y | t < f y} := by
      apply measure_mono
      intro y hy
      exact htx.trans_le (hanti hy.1 (hloc x hx) hy.2)
    exact hμ.trans ((hcdf x hx).trans (add_le_add hν le_rfl))
  · have hz : μ {x | t < f x} = 0 := by
      have hAE : ∀ᵐ x ∂μ, ¬ t < f x := by
        filter_upwards [hsupport] with x hx
        intro hxt
        exact hB ⟨x, Finset.mem_filter.mpr ⟨hx,hxt⟩⟩
      simpa only [ae_iff, not_not] using hAE
    rw [hz]
    exact zero_le

theorem level_measure_measurable (ν : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => ν {x | t < f x}) := by
  have h : Antitone (fun t : ℝ => ν {x | t < f x}) := by
    intro s t hst
    apply measure_mono
    intro x hx
    exact hst.trans_lt hx
  exact h.measurable

theorem finite_monotone_integral_le (μ ν : Measure ℝ) (A : Finset ℝ) (f : ℝ → ℝ) (a M : ℝ) (E : ℝ≥0∞)
    (hf : Measurable f) (hsupport : ∀ᵐ x ∂μ, x ∈ A) (hloc : ∀ x ∈ A, a ≤ x)
    (hnonneg : ∀ x ∈ A, 0 ≤ f x) (hνnonneg : 0 ≤ᵐ[ν] f)
    (hanti : AntitoneOn f (Ici a)) (hM : ∀ x ∈ A, f x ≤ M)
    (hcdf : ∀ x ∈ A, μ (Icc a x) ≤ ν (Icc a x) + E) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂ν) + E * ENNReal.ofReal M := by
  have hμnonneg : 0 ≤ᵐ[μ] f := hsupport.mono (fun x hx => hnonneg x hx)
  rw [lintegral_eq_lintegral_meas_lt μ hμnonneg hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν hνnonneg hf.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ν {x | t < f x} + (Iio M).indicator (fun _ => E) t :=
      lintegral_mono (fun t => finite_level_bound μ ν A f a M t E hsupport hloc hanti hM hcdf)
    _ = (∫⁻ t in Ioi (0 : ℝ), ν {x | t < f x}) +
        ∫⁻ t in Ioi (0 : ℝ), (Iio M).indicator (fun _ => E) t :=
      lintegral_add_left (level_measure_measurable ν f) _
    _ = _ := by
      rw [lintegral_indicator measurableSet_Iio, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iio]
      have hi : Iio M ∩ Ioi (0 : ℝ) = Ioo 0 M := by ext t; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto
      rw [hi, Real.volume_Ioo, sub_zero]

end NumberTheoryLean.FiniteMonotoneComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelWeightTransform

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

structure PositiveWeight (α : Type*) [MeasurableSpace α] where
  value : α → ℝ≥0∞
  measurable_value : Measurable value
  ne_zero : ∀ a, value a ≠ 0
  ne_top : ∀ a, value a ≠ ∞

instance instCoeFunPositiveWeightForallENNReal : CoeFun (PositiveWeight α) (fun _ => α → ℝ≥0∞) := ⟨PositiveWeight.value⟩

noncomputable def conjugate (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) : Kernel α α :=
  K.withDensity (fun a b => w b / w a)

instance kernelPower_isSFiniteKernel (K : Kernel α α) [IsSFiniteKernel K] (n : ℕ) :
    IsSFiniteKernel (K ^ n) := by
  induction n with
  | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih =>
    have hp : K ^ (n + 1) = K ∘ₖ (K ^ n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.KernelWeightTransform

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry

noncomputable def sourceHorizon (S B : ℝ) : ℕ := ⌈(S + 1) * (Real.log B + 2)⌉₊ + 1

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HarmonicPrefixKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.WeightedKernelMass

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def mass (K : Kernel α α) (n : ℕ) (x : α) : ℝ≥0∞ := (K^n) x univ

@[simp] theorem mass_zero (K : Kernel α α) (x : α) : mass K 0 x = 1 := by
  change (Measure.dirac x) univ = 1
  simp

end ErdosPrimeInputs.WeightedKernelMass

end

section

namespace ErdosPrimeInputs.HarmonicPrefixKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass

noncomputable def density (ell B t : ℝ) : ℝ≥0∞ :=
  if ell<t ∧ t≤B then ENNReal.ofReal (t⁻¹) else 0

noncomputable def kernel (ell : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity (density ell)

instance kernel_isSFinite (ell : ℝ) : IsSFiniteKernel (kernel ell) := by
  unfold kernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro B t
  unfold density
  split_ifs <;> simp

noncomputable def bound (ell B : ℝ) : ℝ := max 1 (B/ell)

end ErdosPrimeInputs.HarmonicPrefixKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AdmittedExponentMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicExponentMeasure

open Set MeasureTheory
open scoped ENNReal
open FinitePathGeometry

noncomputable def ratioMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ici a)).withDensity (fun t : ℝ => ENNReal.ofReal (1 / (t + 1)))

noncomputable def exponentMeasure (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 b)).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)

noncomputable def inverseRatio (r x : ℝ) : ℝ := r / x - 1

end NumberTheoryLean.HarmonicExponentMeasure

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.PrimeTiltMonotone

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry
open HarmonicExponentMeasure

theorem ratioMeasure_ae_above (a : ℝ) : ∀ᵐ t ∂ratioMeasure a, a ≤ t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ici)

end NumberTheoryLean.PrimeTiltMonotone



namespace NumberTheoryLean.PrimeRatioMeasure

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltMonotone
open PrimeRatioBins HarmonicExponentMeasure

theorem ratioMeasure_Icc {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    ratioMeasure a (Icc a x) = ENNReal.ofReal (Real.log (x+1)-Real.log (a+1)) := by
  rw [ratioMeasure, withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (show Icc a x ⊆ Ici a from fun _ ht => ht.1)]
  have hi : IntegrableOn (fun t : ℝ => 1/(t+1)) (Icc a x) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_const.div (continuousOn_id.add continuousOn_const)
    intro t ht
    change t+1 ≠ 0
    linarith [ht.1]
  have hn : ∀ᵐ t ∂volume.restrict (Icc a x), 0 ≤ 1/(t+1) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    exact (one_div_pos.mpr (by linarith [ht.1] : 0 < t+1)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hax,
    intervalIntegral.integral_comp_add_right (f := fun t : ℝ => 1/t) 1,
    integral_one_div_of_pos (by linarith : 0 < a+1) (by linarith : 0 < x+1),
    Real.log_div (by linarith : x+1 ≠ 0) (by linarith : a+1 ≠ 0)]

end NumberTheoryLean.PrimeRatioMeasure



namespace NumberTheoryLean.PrimeCumulativeBound

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltMonotone PrimeRatioBins
open PrimeRatioMeasure HarmonicExponentMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def closedBin (w r a b : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^(r/(a+1))⌋₊).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p ≤ b)

noncomputable def closedMass (w r a b : ℝ) : ℝ := ∑ p ∈ closedBin w r a b, (p : ℝ)⁻¹

theorem closed_interval_iff {r a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    (a ≤ r/x-1 ∧ r/x-1 ≤ b) ↔ r/(b+1) ≤ x ∧ x ≤ r/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (div_le_iff₀ hb1).mpr
      have h := (div_le_iff₀ hx).mp (show r/x ≤ b+1 by linarith)
      nlinarith
    · apply (le_div_iff₀ ha1).mpr
      have h := (le_div_iff₀ hx).mp (show a+1 ≤ r/x by linarith)
      nlinarith
  · rintro ⟨hlo,hhi⟩
    constructor
    · have h := (le_div_iff₀ ha1).mp hhi
      have hh : a+1 ≤ r/x := (le_div_iff₀ hx).mpr (by nlinarith)
      linarith
    · have h := (div_le_iff₀ hb1).mp hlo
      have hh : r/x ≤ b+1 := (div_le_iff₀ hx).mpr (by nlinarith)
      linarith

theorem closedMass_eq_harmonic {w r a b : ℝ} (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    closedMass w r a b = harmonicMass w true true (r/(b+1)) (r/(a+1)) := by
  classical
  unfold closedMass closedBin harmonicMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have h := closed_interval_iff (r := r) ha hab (PrimeRatioBins.primeExponent_pos hw (Nat.mem_primesLE.mp hp).2)
  simp only [childRatio, intervalGuard, ite_true, if_true, h]

end NumberTheoryLean.PrimeCumulativeBound



namespace NumberTheoryLean.PrimeRowNormalization

open _root_.Filter _root_.Set _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeTiltGeometry

 theorem polynomial_absorption {c C : ℝ} (hc : 0 < c) (hC : 0 < C) : ∀ᶠ w : ℝ in atTop,
    ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
      C*(1+S)^2 * Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w)) ≤
        Real.exp (-(c/4)*Real.sqrt (Real.log w)) := by
  have hd : 0 < c/4 := by positivity
  have ht : Tendsto (fun x : ℝ => 4*C*x^12 * Real.exp (-(c/4)*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 : ℝ) (c/4) hd).const_mul (4*C)
    simpa only [Real.rpow_ofNat, mul_zero, mul_assoc] using h
  have hcomp := ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hcomp.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with w hsmall hlog
  intro S hS0 hS
  let L := Real.log w
  let Y := Real.sqrt L
  have hL : 1 ≤ L := hlog
  have hL0 : 0 ≤ L := by linarith
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y^2 = L := Real.sq_sqrt hL0
  have hY12 : Y^12 = L^6 := by
    calc
      _ = (Y^2)^6 := by ring
      _ = _ := by rw [hY2]
  have hL3 : 1 ≤ L^3 := one_le_pow₀ hL
  have hlin : 1+S ≤ 2*L^3 := by change S ≤ L^3 at hS; linarith
  have hpoly : (1+S)^2 ≤ 4*Y^12 := by
    calc
      _ ≤ (2*L^3)^2 := pow_le_pow_left₀ (by linarith) hlin 2
      _ = _ := by rw [hY12]; ring
  have hhalf : Y/2 ≤ Real.sqrt ((1/2 : ℝ)*L) := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Y/2) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ (1/2 : ℝ)*L)]
    nlinarith [hY2]
  have he : Real.exp (-c*Real.sqrt ((1/2 : ℝ)*L)) ≤ Real.exp (-(c/2)*Y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hc.le]
  have hsml : 4*C*Y^12*Real.exp (-(c/4)*Y) ≤ 1 := hsmall.le
  calc
    _ ≤ (4*C*Y^12) * Real.exp (-(c/2)*Y) :=
      mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left hpoly hC.le]) he (Real.exp_pos _).le (by positivity)
    _ = (4*C*Y^12*Real.exp (-(c/4)*Y)) * Real.exp (-(c/4)*Y) := by
      rw [show -(c/2)*Y = -(c/4)*Y + -(c/4)*Y by ring, Real.exp_add]
      ring
    _ ≤ 1 * Real.exp (-(c/4)*Y) := mul_le_mul_of_nonneg_right hsml (Real.exp_pos _).le
    _ = _ := one_mul _

end NumberTheoryLean.PrimeRowNormalization



namespace NumberTheoryLean.PrimeGridGeometry

open _root_.Set
open FinitePathGeometry

noncomputable def width (m : ℕ) : ℝ := 1/(m:ℝ)
noncomputable def point (m j : ℕ) : ℝ := (j:ℝ)/(m:ℝ)

end NumberTheoryLean.PrimeGridGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CemeteryHistoryLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CemeteryKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

abbrev Space (α : Type*) := α ⊕ Unit

def dead : Space α := Sum.inr ()

noncomputable def cemeteryPart (K : Kernel α α) : Kernel α (Space α) :=
  (Kernel.const α (Measure.dirac dead)).withDensity (fun x _ => 1-K x univ)

theorem cemeteryPart_measurable (K : Kernel α α) :
    Measurable (Function.uncurry (fun (x : α) (_ : Space α) => 1-K x univ)) :=
  measurable_const.sub ((K.measurable_coe MeasurableSet.univ).comp measurable_fst)

theorem cemeteryPart_apply (K : Kernel α α) (x : α) :
    cemeteryPart K x = (1-K x univ) • Measure.dirac dead := by
  rw [cemeteryPart, Kernel.withDensity_apply _ (cemeteryPart_measurable K) x, Kernel.const_apply, withDensity_const]

noncomputable def liveRow (K : Kernel α α) : Kernel α (Space α) := K.map Sum.inl + cemeteryPart K

theorem liveRow_apply (K : Kernel α α) (x : α) :
    liveRow K x = (K x).map Sum.inl + (1-K x univ) • Measure.dirac dead := by
  rw [liveRow, _root_.add_apply, Kernel.map_apply _ measurable_inl, cemeteryPart_apply]

noncomputable def complete (K : Kernel α α) : Kernel (Space α) (Space α) where
  toFun := Sum.elim (liveRow K) (fun _ => Measure.dirac dead)
  measurable' := (liveRow K).measurable.sumElim measurable_const

@[simp] theorem complete_live (K : Kernel α α) (x : α) : complete K (.inl x) = liveRow K x := rfl
@[simp] theorem complete_dead (K : Kernel α α) : complete K dead = Measure.dirac dead := rfl

theorem complete_live_mass (K : Kernel α α) (x : α) {B : Set α} (hB : MeasurableSet B) :
    complete K (.inl x) (Sum.inl '' B) = K x B := by
  rw [complete_live, liveRow_apply, Measure.add_apply,
    Measure.map_apply measurable_inl hB.inl_image, Measure.smul_apply]
  have hpre : Sum.inl ⁻¹' (Sum.inl '' B : Set (Space α)) = B := Set.preimage_image_eq _ Sum.inl_injective
  rw [hpre]
  have hd : Measure.dirac (dead : Space α) (Sum.inl '' B) = 0 := by
    rw [Measure.dirac_apply' _ hB.inl_image, indicator_of_notMem (by simp [dead])]
  rw [hd, smul_zero, add_zero]

end NumberTheoryLean.CemeteryKernel

end

section

namespace NumberTheoryLean.CemeteryPowers

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel

variable {α : Type*} [MeasurableSpace α]

noncomputable def liftReward (F : α → ℝ≥0∞) : Space α → ℝ≥0∞ := Sum.elim F (fun _ => 0)

end NumberTheoryLean.CemeteryPowers

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport CemeteryKernel

variable {X : Type*} [MeasurableSpace X]

def live (z : Space X) : Prop := Sum.elim (fun _ => True) (fun _ => False) z

noncomputable def killStep (E : Set X) (z : Space X) (x : X) : Space X := by
  classical
  exact if live z ∧ x ∈ E then Sum.inl x else dead

noncomputable def killHist (E : Set X) : (n : ℕ) → Hist X n → Hist (Space X) n
  | 0,h => mapHist (fun x : X => (Sum.inl x : Space X)) 0 h
  | n+1,h =>
      let past := killHist E n (frestrictLe₂ (π := fun _ => X) n.le_succ h)
      extend n past (killStep E (last n past) (last (n+1) h))

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open FiniteHistoryTransport CemeteryKernel

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X]

def aliveThrough (E : Set X) (n : ℕ) (h : Hist X n) : Prop :=
  ∀ j : Finset.Iic n, 0 < (j:ℕ) → h j ∈ E

end NumberTheoryLean.CemeteryHistoryMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompletedParentInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ContinuousRatioBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltMonotone
open PrimeRatioMeasure HarmonicExponentMeasure

instance ratioMeasure_noAtoms (a : ℝ) : NullSingletonClass (ratioMeasure a) := by
  unfold ratioMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.ContinuousRatioBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BadPrimeProduct
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine ErdosInverseAlignment

noncomputable def badPrimeFactors (a : ℕ → ℤ) (t : ℚ) (q : ℕ) : Finset ℕ := by
  classical
  exact q.primeFactors.filter (fun ell => ¬aligns a t ell)

noncomputable def badPrimeProduct (a : ℕ → ℤ) (t : ℚ) (q : ℕ) : ℕ :=
  ∏ ell ∈ badPrimeFactors a t q, ell

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LargePrimeDivisors
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision

noncomputable def dividingPrimes (P : Finset ℕ) (m : ℤ) : Finset ℕ := by
  classical
  exact P.filter (fun p => (p : ℤ) ∣ m)

end ErdosLineCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualCollisionBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def sourceRationalList (P : Finset ℕ) (a : ℕ → ℤ) (Sq R Z c : ℝ) : Finset ℚ :=
  rationalList P a ⌊Sq*R*Z^10⌋₊ ⌊R*Z^10⌋₊ c

end ErdosInverseAlignment



namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine

def Structured (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) : Prop :=
  ∃ t ∈ sourceRationalList P a S R Z cp, aligns a t p ∧
    ((t.den*badPrimeProduct a t q : ℕ) : ℝ) ≤ R*Z^10

def Nonstructured (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) : Prop :=
  ¬Structured P a S R Z cp p q

end ErdosInverseStructured



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def slopeClass (l : PrimitiveIntegerLine) (a : ℤ) (p : ℕ) (hp : Nat.Prime p) (s : ℤ) : ZMod p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ((l.denominator : ZMod p)*(a : ZMod p)-(l.intercept : ZMod p))/
    ((l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p))

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def incidentPoints (X : Finset (ℤ × ℤ)) (a : ℤ) (p : ℕ) (T : Finset ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact X.filter (fun v => ∃ s ∈ T,
    (v.2 : ZMod p) = (a : ZMod p)-(s : ZMod p)*(v.1 : ZMod p))

noncomputable def occupiedClasses (X : Finset (ℤ × ℤ)) (a : ℤ) (p : ℕ) (T : Finset ℤ) : Finset (ZMod p) := by
  classical
  exact (incidentPoints X a p T).image (fun v => (v.1 : ZMod p))

end ErdosLineCollision



namespace ErdosLineCollision
attribute [local instance] Classical.propDecidable

noncomputable def occupiedRows (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) : Finset (ℕ × ℕ) := by
  classical
  exact P.biUnion (fun p => (occupiedClasses X (a p) p (T p)).image (fun c => (p,c.val)))

def RowIncidence (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) (row : ℕ × ℕ) : Prop :=
  v ∈ incidentPoints X (a row.1) row.1 (T row.1) ∧ (v.1 : ZMod row.1).val = row.2

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def commonRows (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v w : ℤ × ℤ) : Finset (ℕ × ℕ) :=
  (occupiedRows P X a T).filter (fun row => RowIncidence X a T v row ∧ RowIncidence X a T w row)

end ErdosLineCollision



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RepresentativeStopGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RepresentativeStopGeometry

open NumberTheoryLean.ReferenceAdmission

def sourceHeight (x : ℝ) : ℝ := max (2*x) (x+2)

end NumberTheoryLean.RepresentativeStopGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRepresentatives
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeBinRepresentatives

open ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def leftExponent (w R : ℝ) : ℝ := Real.log R/Real.log w
noncomputable def rightExponent (w R xi : ℝ) : ℝ := Real.log ((1+xi)*R)/Real.log w

end NumberTheoryLean.PrimeBinRepresentatives

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CorrectSearchTags
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ActualBinOwners

open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

def eligible (Y w Cs : ℝ) (q : ℚ) : Prop :=
  (q.den:ℝ) ≤ w^Cs ∧ (q.num.natAbs:ℝ) ≤ Y*w^(Cs+2)

noncomputable def ownerCandidates (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) : Finset ℚ :=
  sourceRationalList (primeBin R xi) a (Y*w^2) (w^Cs) 1 (1-eta)

noncomputable def chooseOwner (C : Finset ℚ) : Option ℚ :=
  if h : C.Nonempty then some (C.min' h) else none

noncomputable def owner (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) : Option ℚ :=
  chooseOwner (ownerCandidates Y w Cs eta R xi a)

end NumberTheoryLean.ActualBinOwners

end

section

namespace NumberTheoryLean.FiniteFirstTag


structure Tag (n : ℕ) where
  index : ℕ
  bin : Fin n
  rational : ℚ
  deriving DecidableEq

def firstTagFrom {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) : ℕ → List ℕ → Option (Tag n)
  | _,[] => none
  | k,p::ps => match F p with
      | none => firstTagFrom F (k+1) ps
      | some (b,q) => some ⟨k,b,q⟩

def firstTag {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ) : Option (Tag n) :=
  firstTagFrom F 0 ps

end NumberTheoryLean.FiniteFirstTag

end

section

namespace NumberTheoryLean.ActualSourceTags

open ActualBinOwners FiniteFirstTag PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

def searchBin (w R : ℝ) : Prop := w^((1/4:ℝ)) ≤ leftExponent w R

noncomputable def tagCandidate {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) : Option (Fin n × ℚ) :=
  if p ∈ primeBin (lower (label p)) (width (label p)) ∧ searchBin w (lower (label p)) then
    match owner Y w Cs eta (lower (label p)) (width (label p)) a with
    | none => none
    | some q => if aligns a q p then some (label p,q) else none
  else none

noncomputable def sourceTag {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) : Option (Tag n) :=
  firstTag (tagCandidate Y w Cs eta lower width label a) ps

end NumberTheoryLean.ActualSourceTags

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualTagFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.StoppedTraceSets

open _root_.Set _root_.Finset
open FinitePathGeometry
attribute [local instance] Classical.propDecidable

noncomputable def childrenTraces (P : Finset ℕ) (T : ℕ → Finset (List ℕ)) : Finset (List ℕ) :=
  P.biUnion (fun p => (T p).image (List.cons p))

end NumberTheoryLean.StoppedTraceSets



namespace NumberTheoryLean.SourceStopPredicate

open _root_.Set _root_.Finset
open FinitePathGeometry ReferenceAdmission RepresentativeStopGeometry
open PrimeBinRepresentatives ActualSourceTags ActualBinOwners FiniteFirstTag
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def sourceClass (a : ℕ → ℕ) (p : ℕ) : ℤ := a p

noncomputable def representative {n : ℕ} (w : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (p : ℕ) : ℝ := rightExponent w (lower (label p)) (width (label p))

def boxed {n : ℕ} (lower width : Fin n → ℝ) (label : ℕ → Fin n) (ps : List ℕ) : Prop :=
  ∀ p ∈ ps,p ∈ primeBin (lower (label p)) (width (label p))

end NumberTheoryLean.SourceStopPredicate



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.LogarithmicBinScale


noncomputable def binCount (w z xi : ℝ) : ℕ := ⌈Real.log (z/w)/Real.log (1+xi)⌉₊
noncomputable def logWidth (w z xi : ℝ) : ℝ := Real.log (z/w)/(binCount w z xi:ℝ)
noncomputable def effectiveWidth (w z xi : ℝ) : ℝ := Real.exp (logWidth w z xi)-1

theorem span_log_pos {w z : ℝ} (hw : 0 < w) (hwz : w < z) : 0 < Real.log (z/w) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hwz)

theorem binCount_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < binCount w z xi :=
  Nat.ceil_pos.mpr (div_pos (span_log_pos hw hwz) (Real.log_pos (by linarith)))

end NumberTheoryLean.LogarithmicBinScale



namespace NumberTheoryLean.LogarithmicBinEndpoints

open LogarithmicBinScale PrimeBinRepresentatives ErdosInversePrimeBin

noncomputable def endpoint (w z xi : ℝ) (k : ℕ) : ℝ := w*Real.exp ((k:ℝ)*logWidth w z xi)
noncomputable def lower (w z xi : ℝ) (i : Fin (binCount w z xi)) : ℝ := endpoint w z xi i.1
noncomputable def width (w z xi : ℝ) (_i : Fin (binCount w z xi)) : ℝ := effectiveWidth w z xi
noncomputable def upper (w z xi : ℝ) (i : Fin (binCount w z xi)) : ℝ :=
  (1+width w z xi i)*lower w z xi i

end NumberTheoryLean.LogarithmicBinEndpoints



namespace NumberTheoryLean.LogarithmicBinLabels

open LogarithmicBinScale LogarithmicBinEndpoints ErdosInversePrimeBin

noncomputable def coordinate (w z xi : ℝ) (p : ℕ) : ℝ := Real.log ((p:ℝ)/w)/logWidth w z xi

noncomputable def index (w z xi : ℝ) (p : ℕ) : ℕ :=
  min (binCount w z xi-1) (⌈coordinate w z xi p⌉₊-1)

theorem index_lt {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) (p : ℕ) :
    index w z xi p < binCount w z xi := by
  have hn := binCount_pos hw hwz hxi
  have hm : index w z xi p ≤ binCount w z xi-1 := min_le_left _ _
  omega

noncomputable def label {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    (p : ℕ) : Fin (binCount w z xi) := ⟨index w z xi p,index_lt hw hwz hxi p⟩

end NumberTheoryLean.LogarithmicBinLabels



namespace NumberTheoryLean.LogarithmicBinPartition

open _root_.Set _root_.Finset
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels ErdosInversePrimeBin

noncomputable def sourcePrimeSet (w z : ℝ) : Finset ℕ := Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊

end NumberTheoryLean.LogarithmicBinPartition



namespace NumberTheoryLean.IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open PrimeBinRepresentatives SourceStopPredicate
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def isolatedBin (w top xi B alpha beta : ℝ) (b : Fin (binCount w top xi)) : Prop :=
  alpha*B ≤ leftExponent w (lower w top xi b) ∧ rightExponent w (lower w top xi b) (width w top xi b) ≤ beta*B

end NumberTheoryLean.IsolatedBinGeometry



namespace NumberTheoryLean.CrossingBandGeometry
open _root_.Set FinitePathGeometry

noncomputable def crossingLower (H : ℝ) : ℝ := (3/10)*H
noncomputable def crossingUpper (H : ℝ) : ℝ := (11/10)*H
noncomputable def crossingWidth : ℝ := Real.log ((11:ℝ)/3)
noncomputable def crossingCenter (v H : ℝ) : ℝ := v-Real.log (crossingUpper H)

end NumberTheoryLean.CrossingBandGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MeshBoundaryGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MeshRatioLabels

open Set MeasureTheory

noncomputable def binCount (S h : ℝ) : ℕ := ⌊S/h⌋₊
abbrev Label (S h : ℝ) := Fin (binCount S h+2)

noncomputable def cemeteryLabel (S h : ℝ) : Label S h := ⟨binCount S h+1,by omega⟩

noncomputable def ratioLabel (S h t : ℝ) : Label S h :=
  if t ≤ S then Fin.ofNat (binCount S h+2) ⌊t/h⌋₊ else cemeteryLabel S h

theorem ratioLabel_measurable (S h : ℝ) : Measurable (ratioLabel S h) := by
  have hm : Measurable (fun n : ℕ => Fin.ofNat (binCount S h+2) n) := measurable_of_countable _
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (hm.comp (Nat.measurable_floor.comp (measurable_id.div_const h))) measurable_const

end NumberTheoryLean.MeshRatioLabels

end

section

namespace NumberTheoryLean.MeshBoundaryGeometry

open Set MeshRatioLabels

noncomputable def lowerEdge {S mesh : ℝ} (j : Label S mesh) : ℝ := (j.val:ℝ)*mesh
noncomputable def upperEdge {S mesh : ℝ} (j : Label S mesh) : ℝ := ((j.val:ℝ)+1)*mesh

def fullCell {S mesh : ℝ} (Ld Lc Ud Uc : ℝ) (j : Label S mesh) : Prop :=
  max Ld Lc < lowerEdge j ∧ upperEdge j ≤ min Ud Uc

noncomputable def lowerPacket (mesh Ld Lc : ℝ) : Set ℝ := Icc (min Ld Lc) (max Ld Lc+mesh)
noncomputable def upperPacket (mesh Ud Uc : ℝ) : Set ℝ := Icc (min Ud Uc-mesh) (max Ud Uc)

end NumberTheoryLean.MeshBoundaryGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelBinConditioning

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def conditional (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) : Kernel α β where
  toFun x := if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B
  measurable' := by
    classical
    have hm := K.measurable_coe hB
    have hscaled : Measurable (fun x => (K x B)⁻¹ • (K x).restrict B) := by
      apply Measure.measurable_of_measurable_coe
      intro A hA
      simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
      exact hm.inv.mul (K.measurable_coe (hA.inter hB))
    exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const hscaled

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def labelMass (K : Kernel α β) (label : β → ι) (x : α) (i : ι) : ℝ :=
  (K x (label ⁻¹' {i})).toReal

end NumberTheoryLean.KernelBinConditioning

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry
open LowStateHorizon
open PrimeTiltGeometry

variable {w ell S : ℝ}

def liftPredicate {α : Type*} (P : α → Prop) : CemeteryKernel.Space α → Prop :=
  Sum.elim P (fun _ => True)

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonCellSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ActualSupportIntervals

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry
open PrimeTiltGeometry ActualCouplingUpdates LowStateHorizon

noncomputable def upperSupport (S ell r : ℝ) : ℝ := min S (r/ell-1)

end NumberTheoryLean.ActualSupportIntervals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CouplingLabelEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CoupledBoundaryEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry
open ActualSupportIntervals MeshBoundaryGeometry MeshRatioLabels

noncomputable def lowerA (Ld Lc : ℝ) : ℝ := max (1/2) (min Ld Lc)
noncomputable def lowerB (mesh Ld Lc : ℝ) : ℝ := max (1/2) (max Ld Lc+mesh)
noncomputable def upperA (mesh Ud Uc : ℝ) : ℝ := max (1/2) (min Ud Uc-mesh)
noncomputable def upperB (Ud Uc : ℝ) : ℝ := max (1/2) (max Ud Uc)

end NumberTheoryLean.CoupledBoundaryEvents

end

section


namespace NumberTheoryLean.CouplingLabelEvents

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry
open MeshRatioLabels MeshBoundaryGeometry
open CoupledBoundaryEvents KernelBinConditioning

noncomputable def interiorLabels (S mesh Ld Lc Ud Uc : ℝ) : Finset (Label S mesh) := by
  classical
  exact Finset.univ.filter (fullCell Ld Lc Ud Uc)

noncomputable def boundaryLabels (S mesh Ld Lc Ud Uc : ℝ) : Finset (Label S mesh) := by
  classical
  exact (Finset.univ.erase (cemeteryLabel S mesh)).filter (fun j => ¬fullCell Ld Lc Ud Uc j)

end NumberTheoryLean.CouplingLabelEvents

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.PersistentFailureFlag

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

abbrev FlagState (α : Type*) := α × Bool

noncomputable def badBit (Bad : α → Prop) (x : α) : Bool := by
  classical
  exact if Bad x then true else false

noncomputable def update (Bad : α → Prop) (z : FlagState α × α) : FlagState α :=
  (z.2,z.1.2 || badBit Bad z.2)

noncomputable def marked (K : Kernel α α) {Bad : α → Prop} (_hBad : MeasurableSet {x | Bad x}) :
    Kernel (FlagState α) (FlagState α) :=
  (Kernel.id ×ₖ (K.comap Prod.fst measurable_fst)).map (update Bad)

def failed : Set (FlagState α) := {z | z.2 = true}

noncomputable def law (K : Kernel α α) {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x})
    (x : α) (n : ℕ) : Measure (FlagState α) := ((marked K hBad)^n) (x,false)

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FailureFlagBounds

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

def surviving (Good : α → Prop) (z : FlagState α) : Prop := z.2 = false → Good z.1

end NumberTheoryLean.FailureFlagBounds



namespace NumberTheoryLean.FullHistoryFailureFlag

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport PersistentFailureFlag

variable {X : Type*} [MeasurableSpace X]

def noResetPath (n : ℕ) (h : Hist (FlagState X) n) : Prop :=
  ∀ j : Finset.Iic n, (last n h).2 = false → (h j).2 = false

end NumberTheoryLean.FullHistoryFailureFlag



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

noncomputable def mesh (κ w : ℝ) : ℝ := 1/(⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊:ℝ)

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_BudgetPolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section


namespace NumberTheoryLean.BudgetPolynomialBound

noncomputable def coefficient (A C₁ C₂ C₃ D : ℝ) : ℝ :=
  2*(224*C₁+1+24*D+4*C₂*(24*A+5)+4*C₃*(24*A+3))

end NumberTheoryLean.BudgetPolynomialBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MarginalGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MarginalGrowth

open _root_.Set _root_.Filter
open scoped Topology
open ExponentialMesh

noncomputable def factor (L κ w S : ℝ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
    Real.exp (L*(1+S)^3*mesh κ w)*(1+20*mesh κ w)

end NumberTheoryLean.MarginalGrowth

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MarginalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section


namespace NumberTheoryLean.MarginalTransport

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeGridGeometry
open ExponentialMesh

noncomputable def rowFactor (L κ w S : ℝ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*Real.exp (L*(1+S)^3*mesh κ w)

end NumberTheoryLean.MarginalTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrimeExponentialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ExponentialMeshTail

open _root_.Finset

noncomputable def envelope (c K t : ℝ) : ℝ :=
  (8/c^2)*Real.exp (-c*K/4)*Real.exp (-c*t/4)

end NumberTheoryLean.ExponentialMeshTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_FlaggedOccupationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlaggedOccupationBound

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

noncomputable def selected (f : α → ℝ≥0∞) : FlagState α → ℝ≥0∞ :=
  failed.indicator (fun z => f z.1)

omit [MeasurableSpace α] in
@[simp] theorem selected_false (f : α → ℝ≥0∞) (x : α) : selected f (x,false) = 0 := by
  simp [selected,failed]

omit [MeasurableSpace α] in
@[simp] theorem selected_true (f : α → ℝ≥0∞) (x : α) : selected f (x,true) = f x := by
  simp [selected,failed]

end NumberTheoryLean.FlaggedOccupationBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GrowingFarTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SourceModerateFailure

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry
open PersistentFailureFlag FlaggedOccupationBound
open ExponentialMesh LowStateHorizon

noncomputable def growingCutoff (w : ℝ) : ℝ := (Real.log w)^((1:ℝ)/10)

end NumberTheoryLean.SourceModerateFailure

end

section

namespace NumberTheoryLean.GrowingFarTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry
open SourceModerateFailure LowStateHorizon

noncomputable def farBudget (C c d w : ℝ) : ℝ :=
  (5*d^3*(C*(8/c^2)*(1+4/c)))*(Real.log w)^3*Real.exp (-(c/4)*growingCutoff w)

end NumberTheoryLean.GrowingFarTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HighPrefixState
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HarmonicPrefixTilt

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel

noncomputable def squareBoundE (ell B : ℝ) : ℝ≥0∞ := ENNReal.ofReal (bound ell B ^ 2)

end ErdosPrimeInputs.HarmonicPrefixTilt

end

section

namespace ErdosPrimeInputs.HarmonicLongPrefixes

open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt

noncomputable def tailMass (a : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, if m≤n then a n else 0

end ErdosPrimeInputs.HarmonicLongPrefixes

end

section

namespace ErdosPrimeInputs.HighPrefixState

open Set MeasureTheory

abbrev State := ℝ × ℝ × Bool

noncomputable def initial (S B R : ℝ) : State :=
  (B,R,if S<R/B then true else false)

noncomputable def update (S : ℝ) (z : State) (t : ℝ) : State :=
  (t,z.2.1-t,if z.2.2=true ∨ S<(z.2.1-t)/t then true else false)

def Invariant (ell S : ℝ) (n : ℕ) (z : State) : Prop :=
  ell≤z.1 ∧ (z.2.2=true → (S-(n:ℝ))*z.1<z.2.1)

end ErdosPrimeInputs.HighPrefixState

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HighPrefixKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixKernel

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt HarmonicLongPrefixes HighPrefixState

noncomputable def kernel (ell S : ℝ) : Kernel State State :=
  ((Kernel.id : Kernel State State).prod
    ((HarmonicPrefixKernel.kernel ell).comap (fun z : State => z.1) measurable_fst)).map
      (Function.uncurry (update S))

instance kernel_isSFinite (ell S : ℝ) : IsSFiniteKernel (kernel ell S) := by
  unfold kernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end ErdosPrimeInputs.HighPrefixKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HighPrefixBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicLongPrefixes HighPrefixState
open HighPrefixKernel

noncomputable def lowHighMass (ell S B R K : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (kernel ell S ^ n) (initial S B R) {z | z.2.2=true ∧ z.2.1≤K}

end ErdosPrimeInputs.HighPrefixBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlaggedHarmonicPaths

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
abbrev ExponentState := ErdosPrimeInputs.HighPrefixState.State

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SubMarkovFlagPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SubMarkovFlagPowers

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound

variable {α : Type*} [MeasurableSpace α]

instance marked_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : IsSFiniteKernel (marked K hBad) := by
  unfold marked
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.SubMarkovFlagPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlagMeasurePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlagMeasurePartition

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound SubMarkovFlagPowers

variable {α : Type*} [MeasurableSpace α]

noncomputable def highPart (K : Kernel α α) {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) : Measure α :=
  ((((marked K hBad)^n) (x,false)).restrict failed).map Prod.fst

end NumberTheoryLean.FlagMeasurePartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlagWeightConjugation
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform PersistentFailureFlag SubMarkovFlagPowers FlaggedOccupationBound

variable {α : Type*} [MeasurableSpace α]

def flagWeight (w : PositiveWeight α) : PositiveWeight (FlagState α) where
  value z := w z.1
  measurable_value := w.measurable_value.comp measurable_fst
  ne_zero z := w.ne_zero z.1
  ne_top z := w.ne_top z.1

end NumberTheoryLean.FlagWeightConjugation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FiniteHistoryPairLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteHistoryPairLaw
open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence
variable {X : Type*} [MeasurableSpace X]

def adjacentPair (N : ℕ) (h : Hist X N) (j : Fin N) : X×X :=
  (atIndex N h j.castSucc,atIndex N h j.succ)

noncomputable def pairProbability (K : Kernel X X) (E : Set (X×X)) (x : X) : ℝ≥0∞ :=
  K x ((Prod.mk x) ⁻¹' E)

end NumberTheoryLean.FiniteHistoryPairLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EvenThresholdGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set NumberTheoryLean.FinitePathGeometry

noncomputable def thresholdSlack (R t : ℝ) : ℝ :=
  nextGap R t-max (2*nextExponent R t) (nextExponent R t+2)
noncomputable def thresholdStrip (R d : ℝ) : Set ℝ :=
  {t | 2 ≤ t ∧ 1 < nextExponent R t ∧ 0 ≤ thresholdSlack R t ∧ thresholdSlack R t ≤ d}

end ErdosEvenThreshold

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_EvenThresholdEvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set MeasureTheory NumberTheoryLean
open FinitePathGeometry

noncomputable def nearThreshold (R d : ℝ) : Set ℝ :=
  {t | 1 < nextExponent R t ∧ 0 ≤ thresholdSlack R t ∧ thresholdSlack R t ≤ d}

end ErdosEvenThreshold

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualThresholdArrival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CompletedArrivalOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FiniteHistoryTransport FiniteHistoryOccurrence
open CemeteryKernel CemeteryHistoryMap

def liveMember {X : Type*} (E : Set X) : Space X → Prop
  | .inl y => y ∈ E
  | .inr _ => False

def completedOccurrence {X : Type*} (E : Set X) (N : ℕ) (h : Hist (Space X) N) : Prop :=
  ∃ j : Fin N,liveMember E (atIndex N h j.succ)

end NumberTheoryLean.CompletedArrivalOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_NearPrefixOccurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CompactPrefixOccurrence

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PersistentFailureFlag
open FiniteHistoryTransport

attribute [local instance] Classical.propDecidable

variable {w ell S B R : ℝ}

noncomputable def listSelection (E : Set (List ℕ)) (ps : List ℕ) : ℝ :=
  if ps ∈ E then 1 else 0

end NumberTheoryLean.CompactPrefixOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositiveGapMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PositiveGapMajorant

open _root_.Set

theorem exists_positive_gap_majorant (K : ℝ) : ∃ H : C(ℝ×ℝ,ℝ),
    HasCompactSupport H ∧ (∀ x,0 ≤ H x ∧ H x ≤ 1) ∧
    (∀ r s,2 ≤ r → r ≤ K → 0 ≤ s → s ≤ K → H (r,s)=1) ∧
    ∀ r s,r < 1 ∨ K+1 < r → H (r,s)=0 := by
  let A : Set (ℝ×ℝ) := Icc (2,0) (K,K)
  let Z : Set (ℝ×ℝ) := {x | x.1 ≤ 1} ∪ {x | K+1 ≤ x.1}
  have hA : IsCompact A := isCompact_Icc
  have hZ : IsClosed Z := (isClosed_le continuous_fst continuous_const).union
    (isClosed_le continuous_const continuous_fst)
  have hd : Disjoint A Z := by
    apply Set.disjoint_left.mpr
    intro x hx hz
    have hlow : 2 ≤ x.1 := hx.1.1
    have hhigh : x.1 ≤ K := hx.2.1
    rcases hz with hz | hz
    · change x.1 ≤ 1 at hz
      linarith
    · change K+1 ≤ x.1 at hz
      linarith
  obtain ⟨H,hHA,hHZ,hcompact,hbounds⟩ := exists_continuous_one_zero_of_isCompact hA hZ hd
  refine ⟨H,hcompact,hbounds,?_,?_⟩
  · intro r s hr hrK hs hsK
    exact hHA ⟨⟨hr,hs⟩,⟨hrK,hsK⟩⟩
  · intro r s hbad
    apply hHZ
    rcases hbad with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le

end NumberTheoryLean.PositiveGapMajorant

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CompactAnomalyTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set
namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PositiveGapMajorant

noncomputable def compactCutoff (K : ℝ) : C(ℝ×ℝ,ℝ) :=
  Classical.choose (exists_positive_gap_majorant K)

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MovingLocalReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.GlobalResidualScale

noncomputable def powerDecay (M B : ℝ) : ℝ := Real.exp (-M*Real.log B)

end NumberTheoryLean.GlobalResidualScale



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_JacobsthalSourceScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.JacobsthalSourceScale

open _root_.Filter _root_.Asymptotics
open scoped Topology

noncomputable def sourceW (L : ℝ) : ℝ := L/(Real.log L)^2
noncomputable def sourceB (L : ℝ) : ℝ := L/Real.log (sourceW L)

end NumberTheoryLean.JacobsthalSourceScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CoefficientHeightChoice
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def boxHeight (M N : ℕ) : ℕ := ⌈(M : ℝ)^((N : ℝ)⁻¹)⌉₊

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BivariateMonomialIndex
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

abbrev MonomialIndex (D : ℕ) := Σ k : Fin (D+1), Fin (k.val+1)

noncomputable def exponent {D : ℕ} (i : MonomialIndex D) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.2.val + Finsupp.single 1 (i.1.val-i.2.val)

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialValueBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def encode {D : ℕ} (v : MonomialIndex D → ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ i, MvPolynomial.monomial (exponent i) (v i)

noncomputable def encodeHom (D : ℕ) : (MonomialIndex D → ℤ) →+ MvPolynomial (Fin 2) ℤ where
  toFun := encode
  map_zero' := by simp [encode]
  map_add' v w := by simp [encode,Finset.sum_add_distrib]

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

noncomputable def evalReal (Q : MvPolynomial (Fin 2) ℤ) (x y : ℝ) : ℝ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℝ) ![x,y] Q

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LineSubstitution
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def lineSub {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R) :
    MvPolynomial (Fin 2) ℤ →+* Polynomial R :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp φ)
    ![Polynomial.X,Polynomial.C a-Polynomial.C s*Polynomial.X]

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CoefficientBoxCollision
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

def boxLift {ι : Type*} {H : ℕ} (x : ι → Fin (H+1)) : ι → ℤ := fun i => (x i).val

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LineCongruenceConstruction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

abbrev ResidueSystem (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :=
  ∀ p : P, ∀ _s : T p, Fin (D+1) → ZMod p.val

@[implicit_reducible]
noncomputable def residueFintype (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : Fintype (ResidueSystem P T D) := by
  letI (p : P) : NeZero p.val := ⟨Nat.ne_of_gt (hP p p.property)⟩
  exact inferInstance

noncomputable def constraintMap (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val))
    (a : ∀ p : P, ZMod p.val) (D : ℕ) : (MonomialIndex D → ℤ) →+ ResidueSystem P T D where
  toFun v p s k := (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode v)).coeff k
  map_zero' := by
    funext p s k
    simp [encode]
  map_add' v w := by
    funext p s k
    change (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode (v+w))).coeff k =
      (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode v)).coeff k +
      (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode w)).coeff k
    rw [show encode (v+w) = encode v+encode w from (encodeHom D).map_add v w,
      map_add,Polynomial.coeff_add]

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_AuxiliaryPolynomialLifting
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

def constraintVolume (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : ℕ :=
  ∏ p : P, p.val^((D+1)*(T p).card)

noncomputable def logarithmicCost (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) : ℝ :=
  ∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

noncomputable def valueBudget (D H : ℕ) (S : ℝ) : ℝ :=
  ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D

noncomputable def logarithmicValueBudget (D H : ℕ) (S : ℝ) : ℝ :=
  Real.log ((D+2).choose 2 : ℝ)+Real.log (H : ℝ)+(D : ℝ)*Real.log (max 1 S)

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoxInflation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosInverseBoxHeight

noncomputable def sourceZ (z : ℝ) : ℝ := Real.exp (Real.log z/Real.log (Real.log z))

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionFloorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

noncomputable def sourceW (z : ℝ) : ℝ := Real.log z/(Real.log (Real.log z))^2
noncomputable def sourceB (z : ℝ) : ℝ := Real.log z/Real.log (sourceW z)
noncomputable def sourceY (z : ℝ) : ℕ := ⌊z^2/(Real.log z)^2⌋₊

end ErdosInverseBoxHeight

end

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

noncomputable def sourceDegree (z R : ℝ) : ℕ := ⌊R/(Real.log z)^2⌋₊

end ErdosSourcePolynomial

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def paperGap (a : ℝ) (e : ℝ → ℝ) (L : ℝ) : ℝ :=
  2*sourceB L-a+2-2*Real.log L/Real.log (sourceW L)+e L

end ErdosCorrectionLimit

end

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def unroundedY (L : ℝ) : ℝ := Real.exp (2*L)/L^2

noncomputable def floorRemainder (L : ℝ) : ℝ :=
  (Real.log (⌊unroundedY L⌋₊ : ℝ)-(2*L-2*Real.log L))/Real.log (sourceW L)

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReciprocalEnvelope
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel

noncomputable def interceptScale (R C0 : ℝ) : ℝ := |C0|/R
noncomputable def totalScale (R H C0 : ℝ) : ℝ := max H (interceptScale R C0)

noncomputable def primeWidth (R xi H C0 : ℝ) : ℝ :=
  min (xi*R) (R*H/totalScale R H C0)

noncomputable def modelLength (R xi H C0 : ℝ) : ℝ := H+xi*interceptScale R C0

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel

noncomputable def modelLeft (R xi C0 : ℝ) : ℝ := min (C0/R) (C0/((1+xi)*R))
noncomputable def modelRight (R xi H C0 : ℝ) : ℝ := modelLeft R xi C0+modelLength R xi H C0

noncomputable def modelIntegers (R xi H C0 : ℝ) : Finset ℤ :=
  Finset.Ico ⌈modelLeft R xi C0⌉ ⌈modelRight R xi H C0⌉

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalCuts
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

noncomputable def lowerCut (x : ℝ) (closed : Bool) : ℤ :=
  if closed then ⌈x⌉ else ⌊x⌋+1

noncomputable def upperCut (x : ℝ) (closed : Bool) : ℤ := lowerCut x (!closed)

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RealProgressionPoints
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

def progressionPoint (a : ℤ) (T : ℕ) (j : ℤ) : ℤ := a + (T : ℤ)*j

noncomputable def lowerIndex (x : ℝ) (T : ℕ) (a : ℤ) (closed : Bool) : ℤ :=
  lowerCut ((x-a)/T) closed

noncomputable def upperIndex (y : ℝ) (T : ℕ) (a : ℤ) (closed : Bool) : ℤ :=
  upperCut ((y-a)/T) closed

noncomputable def progressionPoints (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) : Finset ℤ :=
  (Finset.Ico (lowerIndex x T a lc) (upperIndex y T a rc)).image (progressionPoint a T)

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairCollisionCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

noncomputable def sum {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, ψ (a * (u : R) + b * (↑u⁻¹ : R))

noncomputable def standardSum (N : ℕ) [NeZero N] (h k : ℤ) : ℂ :=
  sum ZMod.stdAddChar (h : ZMod N) (k : ZMod N)

end ErdosKloosterman

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

noncomputable def integerWeight (N : ℕ) [NeZero N] (I : Finset ℤ) (h : ZMod N) : ℂ :=
  ∑ x ∈ I, ZMod.stdAddChar (-h*(x : ZMod N))

noncomputable def unitClass (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) : Finset (ZMod N)ˣ :=
  Finset.univ.filter fun u => ZMod.unitsMap hT u = a

noncomputable def restrictedSum (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (h k : ZMod N) : ℂ :=
  ∑ u ∈ unitClass N T hT a,
    ZMod.stdAddChar (h*(u : ZMod N) + k*(c : ZMod N)*(↑u⁻¹ : ZMod N))

noncomputable def hyperbolaPairs (N T : ℕ) [NeZero N] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) : Finset (ℤ × ℤ) :=
  (I.product J).filter fun xy =>
    (xy.1 : ZMod N)*(xy.2 : ZMod N) = (c : ZMod N) ∧
      (xy.1 : ZMod T) = (a : ZMod T)

noncomputable def integerFibre (N : ℕ) (I : Finset ℤ) (u : ZMod N) : Finset ℤ :=
  I.filter fun x => (x : ZMod N) = u

noncomputable def pairFibre (N : ℕ) [NeZero N] (c u : (ZMod N)ˣ) (I J : Finset ℤ) :
    Finset (ℤ × ℤ) :=
  (integerFibre N I (u : ZMod N)).product
    (integerFibre N J ((c : ZMod N)*(↑u⁻¹ : ZMod N)))

@[simp] theorem mem_unitClass (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (u : (ZMod N)ˣ) :
    u ∈ unitClass N T hT a ↔ ZMod.unitsMap hT u = a := by simp [unitClass]

@[simp] theorem mem_integerFibre (N : ℕ) (I : Finset ℤ) (u : ZMod N) (x : ℤ) :
    x ∈ integerFibre N I u ↔ x ∈ I ∧ (x : ZMod N) = u := by simp [integerFibre]

end ErdosHyperbolaIdentities

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

noncomputable def productChar {R S : Type*} [AddMonoid R] [AddMonoid S]
    (ψ : AddChar R ℂ) (φ : AddChar S ℂ) : AddChar (R × S) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

end ErdosKloosterman

end

section

namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R]

theorem shift_mul_inverse (u : Rˣ) (t : R) (ht : t^2 = 0) :
    ((u : R) + t) * ((↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2) = 1 := by
  calc
    _ = (u : R) * ↑u⁻¹ + t * ↑u⁻¹ * (1 - (u : R) * ↑u⁻¹) -
        t^2 * (↑u⁻¹ : R)^2 := by ring
    _ = 1 := by simp [ht]

def shiftUnit (u : Rˣ) (t : R) (ht : t^2 = 0) : Rˣ :=
  Units.mkOfMulEqOne ((u : R) + t) ((↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2)
    (shift_mul_inverse u t ht)

@[simp] theorem shiftUnit_val (u : Rˣ) (t : R) (ht : t^2 = 0) :
    (shiftUnit u t ht : R) = (u : R) + t := rfl

@[simp] theorem shiftUnit_inv_val (u : Rˣ) (t : R) (ht : t^2 = 0) :
    (↑(shiftUnit u t ht)⁻¹ : R) = (↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2 := rfl

def shiftEquiv (t : R) (ht : t^2 = 0) : Rˣ ≃ Rˣ where
  toFun u := shiftUnit u t ht
  invFun u := shiftUnit u (-t) (by simpa using ht)
  left_inv u := by apply Units.ext; simp
  right_inv u := by apply Units.ext; simp

end ErdosKloosterman.PrimePower

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable (F : Type*) [Field F] [Fintype F]

noncomputable def pairCollisions : Finset ((Fˣ × Fˣ) × (Fˣ × Fˣ)) :=
  Finset.univ.filter fun x =>
    (x.1.1 : F) + x.1.2 = x.2.1 + x.2.2 ∧
      (↑x.1.1⁻¹ : F) + ↑x.1.2⁻¹ = ↑x.2.1⁻¹ + ↑x.2.2⁻¹

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalHyperbolaAdapter
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

noncomputable def intervalWeight (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) : ℂ :=
  ∑ z ∈ progressionPoints x y lc rc T a, ZMod.stdAddChar (-h*(z : ZMod N))

end ErdosHyperbolaFourier

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

structure ProgressionInterval where
  left : ℝ
  right : ℝ
  leftClosed : Bool
  rightClosed : Bool
  step : ℕ
  residue : ℤ
  step_pos : 0 < step

noncomputable def ProgressionInterval.points (P : ProgressionInterval) : Finset ℤ :=
  ErdosHyperbolaFourier.progressionPoints P.left P.right P.leftClosed P.rightClosed P.step P.residue

noncomputable def ProgressionInterval.weight (P : ProgressionInterval) (N : ℕ) [NeZero N]
    (h : ZMod N) : ℂ :=
  ErdosHyperbolaFourier.intervalWeight N h P.left P.right P.leftClosed P.rightClosed P.step P.residue

end ErdosHyperbolaIdentities

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_DilationCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def nonzeroFrequencies (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.filter (· ≠ 0)

noncomputable def intervalLength (P : ProgressionInterval) : ℝ := P.right-P.left

noncomputable def l1Norm (N : ℕ) [NeZero N] (P : ProgressionInterval) : ℝ :=
  ∑ h ∈ nonzeroFrequencies N, ‖P.weight N h‖

noncomputable def gcdL1Norm (N : ℕ) [NeZero N] (P : ProgressionInterval) : ℝ :=
  ∑ h ∈ nonzeroFrequencies N, ‖P.weight N h‖*Real.sqrt (Nat.gcd h.val N)

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def inverseResidue (T l : ℕ) (hlT : l.Coprime T) (r : ℤ) : ℤ :=
  (((↑(ZMod.unitOfCoprime l hlT)⁻¹ : ZMod T)*(r : ZMod T)).val : ℕ)

noncomputable def pulledInterval (P : ProgressionInterval) (l : ℕ) (hlT : l.Coprime P.step) :
    ProgressionInterval where
  left := P.left/(l : ℝ)
  right := P.right/(l : ℝ)
  leftClosed := P.leftClosed
  rightClosed := P.rightClosed
  step := P.step
  residue := inverseResidue P.step l hlT P.residue
  step_pos := P.step_pos

def dilatePair (l : ℕ) (xy : ℤ × ℤ) : ℤ × ℤ := ((l : ℤ)*xy.1,xy.2)

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_StationaryPhase
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] Classical.decEq

noncomputable def stationaryUnits (q a b : R) : Finset Rˣ :=
  Finset.univ.filter fun u => q * (a - b * (↑u⁻¹ : R)^2) = 0

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueFibres
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

def reduction (n d : ℕ) : ZMod (n*d) →+* ZMod d :=
  ZMod.castHom (dvd_mul_left d n) (ZMod d)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_StationaryFibres
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

noncomputable def quadraticUnitRoots (d : ℕ) [NeZero d] (a b : ZMod d) : Finset (ZMod d) :=
  Finset.univ.filter fun x => IsUnit x ∧ a * x^2 = b

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_OddPrimeRoots
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

def primeReduction (p s : ℕ) (hs : 0 < s) : ZMod (p^s) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimePowerBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

noncomputable def envelope (p a : ℕ) (h k : ℤ) : ℝ :=
  ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
    ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarErrorBudget
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

def frequencyGcd (N : ℕ) (h k : ℤ) : ℕ := Nat.gcd N (Int.gcd h k)

end ErdosKloosterman

end

section

namespace ErdosKloosterman

noncomputable def envelope (N : ℕ) (h k : ℤ) : ℝ :=
  (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
    (frequencyGcd N h k : ℝ)^((1 : ℝ)/4)

def BoundAt (N : ℕ) : Prop := ∀ [NeZero N] (h k : ℤ),
  ‖standardSum N h k‖ ≤ envelope N h k

end ErdosKloosterman

end

section

namespace ErdosHyperbolaError

noncomputable def completeScale (N : ℕ) : ℝ :=
  (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4)

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def logFactor (N : ℕ) : ℝ :=
  ErdosHyperbola.harmonicConstant * Real.log (2*(N : ℝ))

noncomputable def errorBase (N T : ℕ) : ℝ :=
  completeScale N * (N.divisors.card : ℝ) * Real.sqrt T * (logFactor N)^2

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_NormalizedSpectralError
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def spectralTerm (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (h k : ZMod (H*T)) : ℂ :=
  P.weight (H*T) h * Q.weight (H*T) k * restrictedSum (H*T) T (dvd_mul_left T H) a c h k

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_ZeroFrequencyBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def restrictionCount (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ) : ℝ :=
  (unitClass (H*T) T (dvd_mul_left T H) a).card

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_DisjointBlockExpansion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeDensityBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped BigOperators

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

noncomputable def actualLowerCoefficient (V m : ℕ) (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.lowerCoefficient (blockIndices V) (primeBlock P)
    (reverseOrder m (lastBlock V)) T

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FundamentalBlockEstimate
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalPairCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

noncomputable def congruenceIndicator (d i j : ℕ) : ℝ := if Nat.ModEq d i j then 1 else 0

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PairDensityExpansion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

noncomputable def sieveProduct (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1-(1 : ℝ)/p)
noncomputable def pairKernel (P : Finset ℕ) (i j : ℕ) : ℝ :=
  ∏ p ∈ P, (((1 : ℝ)/p)*congruenceIndicator p i j+(1-2/(p : ℝ)))
noncomputable def pairCoefficient (P S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 : ℝ)/p)*(∏ p ∈ P \ S, (1-2/(p : ℝ)))

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PositionDensities
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.decEq

noncomputable def positionResidues (S : Finset ℕ) (p : ℕ) : Finset (ZMod p) := S.image (fun j : ℕ => (j : ZMod p))

noncomputable def forbiddenClasses (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) : Finset (ZMod p) :=
  S.image (fun j : ℕ => c-(u : ZMod p)*(j : ZMod p))

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def positionDensity (S : Finset ℕ) (p : ℕ) : ℝ :=
  ((positionResidues S p).card : ℝ)/(p : ℝ)

noncomputable def jointDensity (P S : Finset ℕ) : ℝ := ∏ p ∈ P,(1-positionDensity S p)

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RealCoprimeResidueCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

noncomputable def crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) : Finset (ZMod (∏ i,m i)) :=
  (Fintype.piFinset E).map (ZMod.prodEquivPi m hcop).symm.toEquiv.toEmbedding

end ErdosInverseCRT



namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def allowedClasses (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) : Finset (ZMod p) :=
  Finset.univ \ forbiddenClasses S p u c

end ErdosVarianceMoments



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

noncomputable def integerCRTResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (E : ∀ i,Finset (ZMod (m i))) : Finset ℤ :=
  (crtResidues m hcop E).image (fun r => (r.val : ℤ))

end ErdosInverseCRT



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def crtSlopes {ι : Type*} [Fintype ι] (a b : ℤ) (m : ι → ℕ)
    (E : ∀ i,Finset (ZMod (m i))) : Finset ℤ :=
  (Finset.Ico a b).filter (fun s => ∀ i,(s : ZMod (m i)) ∈ E i)

end ErdosInverseCRT



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

abbrev binaryModuli (d l : ℕ) (i : Bool) : ℕ := match i with
  | false => d
  | true => l

theorem binary_coprime (d l : ℕ) (h : d.Coprime l) :
    Pairwise (fun i j => Nat.Coprime (binaryModuli d l i) (binaryModuli d l j)) := by
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact h
  · exact h.symm
  · exact False.elim (hij rfl)

noncomputable def binaryClasses (d l : ℕ) (A : Finset (ZMod l)) (i : Bool) :
    Finset (ZMod (binaryModuli d l i)) := match i with
  | false => {0}
  | true => A

noncomputable def divisibleResidues (d l : ℕ) (h : d.Coprime l) (A : Finset (ZMod l)) : Finset ℤ :=
  ErdosInverseCRT.integerCRTResidues (binaryModuli d l) (binary_coprime d l h) (binaryClasses d l A)

end ErdosCoprimeResidueInterval



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

def affineEquiv {R : Type*} [CommRing R] (c : Rˣ) (b : R) : R ≃ R where
  toFun s := (c : R)*s+b
  invFun t := (↑(c⁻¹) : R)*(t-b)
  left_inv s := by
    change (↑(c⁻¹) : R)*((c : R)*s+b-b) = s
    have he : (c : R)*s+b-b = (c : R)*s := by ring
    rw [he,Units.inv_mul_cancel_left]
  right_inv t := by
    change (c : R)*((↑(c⁻¹) : R)*(t-b))+b = t
    rw [Units.mul_inv_cancel_left]
    ring

noncomputable def affineResidues {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) : Finset R :=
  E.map (affineEquiv c b).symm.toEmbedding

end ErdosInverseCRT



namespace ErdosCoprimeResidueInterval
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable

noncomputable def coprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℤ) : Finset ℤ :=
  (Finset.Ico b c).filter (fun m => H.Coprime m.natAbs ∧ (m : ZMod l) ∈ A)

end ErdosCoprimeResidueInterval



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

noncomputable def realCoprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℝ) : Finset ℤ :=
  coprimeResidues H l A ⌈b⌉ ⌈c⌉

end ErdosCoprimeResidueInterval


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def primeResidueSet (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) : Finset (ZMod (∏ p ∈ P,p)) := by
  letI : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  exact Finset.univ.filter (fun r => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)

noncomputable def integerPrimeIntersection (H : ℕ) (P : Finset ℕ)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈b⌉ ⌈c⌉).filter (fun n => H.Coprime n.natAbs ∧ ∀ p ∈ P,(n : ZMod p) ∈ E p)

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
open NumberTheoryLean
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def unitIntervalIntegers (H : ℕ) (b c : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈b⌉ ⌈c⌉).filter (fun n => H.Coprime n.natAbs)

noncomputable def residueDensity (E : ∀ p : ℕ,Finset (ZMod p)) (p : ℕ) : ℝ :=
  ((E p).card : ℝ)/(p : ℝ)

end ErdosVarianceMoments

end

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped BigOperators

noncomputable def smallEuler (z : ℕ) : ℝ :=
  ∏ p ∈ LargePrimeDeletion.cutoffPrimes z, (1 - (p : ℝ)⁻¹)

end NumberTheoryLean.SmallSieveFinite

end

section

namespace NumberTheoryLean.EulerProductRatio

open scoped BigOperators

noncomputable def rootCutoff (u : ℝ) (h : ℕ) : ℝ := u ^ (((2 ^ h : ℕ) : ℝ)⁻¹)

end NumberTheoryLean.EulerProductRatio

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourcePairRemainder
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

theorem source_product_coprime (H T : ℕ) (hTH : T ∣ H) (C0 k0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    IsCoprime (C0+(H : ℤ)*k0) ((H*T : ℕ) : ℤ) := by
  have hCH : Int.gcd (C0+(H : ℤ)*k0) (H : ℤ) = 1 := by
    rw [add_comm C0, Int.gcd_mul_left_add_left]
    exact hC0
  have hcop : (C0+(H : ℤ)*k0).natAbs.Coprime H := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa only [Int.gcd_def, Int.natAbs_natCast] using hCH
  have hdiv : H*T ∣ H^2 := by
    simpa only [pow_two] using Nat.mul_dvd_mul_left H hTH
  have hcopN : (C0+(H : ℤ)*k0).natAbs.Coprime (H*T) :=
    Nat.Coprime.of_dvd_right hdiv (hcop.pow_right 2)
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hcopN.gcd_eq_one

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def reducedProduct (N l : ℕ) (hlN : l.Coprime N) (c : (ZMod N)ˣ) : (ZMod N)ˣ :=
  (ZMod.unitOfCoprime l hlN)⁻¹*c

noncomputable def reducedClass (N T l : ℕ) (hT : T ∣ N) (hlN : l.Coprime N)
    (a : (ZMod T)ˣ) : (ZMod T)ˣ :=
  (ZMod.unitsMap hT (ZMod.unitOfCoprime l hlN))⁻¹*a

noncomputable def dilatedPairs (N T : ℕ) [NeZero N] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval) (l : ℕ) : Finset (ℤ × ℤ) :=
  (hyperbolaPairs N T a c P.points Q.points).filter fun xy => (l : ℤ) ∣ xy.1

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def realIntervalIntegers (x y : ℝ) (lc rc : Bool) : Finset ℤ :=
  (Finset.Icc ⌈x⌉ ⌊y⌋).filter fun z : ℤ =>
    (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
    (if rc then (z : ℝ) ≤ y else (z : ℝ) < y)

noncomputable def sourcePairs (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ) (l : ℕ)
    (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) : Finset (ℤ × ℤ) :=
  ((realIntervalIntegers x0 x1 lcI rcI).product (realIntervalIntegers y0 y1 lcJ rcJ)).filter
    (fun pm : ℤ × ℤ => (l : ℤ) ∣ pm.1 ∧ Int.ModEq (T0 : ℤ) pm.1 p0 ∧
      Int.ModEq (T1 : ℤ) pm.1 p1 ∧ Int.ModEq (T1 : ℤ) pm.2 m1 ∧
      Int.ModEq ((H*T0 : ℕ) : ℤ) (pm.1*pm.2) (C0+(H : ℤ)*k0))

def sourceInterval (x y : ℝ) (lc rc : Bool) (T : ℕ) (r : ℤ) (hT : 0 < T) : ProgressionInterval where
  left := x
  right := y
  leftClosed := lc
  rightClosed := rc
  step := T
  residue := r
  step_pos := hT

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def zeroDensity (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (P Q : ProgressionInterval) : ℝ :=
  (P.points.card : ℝ)*(Q.points.card : ℝ)*restrictionCount H T a/((H*T : ℕ) : ℝ)^2

noncomputable def mainDensity (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (P Q : ProgressionInterval) : ℝ :=
  (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*
    restrictionCount H T a/((H*T : ℕ) : ℝ)^2

noncomputable def completionConstant : ℝ := 16*ErdosHyperbola.harmonicConstant^2

end ErdosHyperbolaError

end

section

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def sourceMain (H T0 T1 : ℕ) (U V : ℝ) : ℝ :=
  U*V*((H*T0).totient : ℝ)/
    ((T1 : ℝ)^2*((H*T0 : ℕ) : ℝ)^2*(T0.totient : ℝ))

noncomputable def hyperbolaEnvelope (H T0 : ℕ) : ℝ :=
  completionConstant*((H*T0).divisors.card : ℝ)^3*(Real.log (2*((H*T0 : ℕ) : ℝ)))^2*
    (((H*T0 : ℕ) : ℝ)^((3 : ℝ)/4))*Real.sqrt T0

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CellLengthLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseTail
open ErdosInverseHits

noncomputable def commonParentLength (Y p : ℕ) (Qplus : ℝ) : ℕ :=
  ⌊(Y : ℝ)/((p : ℝ)*Qplus)⌋₊

end ErdosInverseTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ParentProgression
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

noncomputable def parentSlope (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) : ℕ :=
  (((a : ZMod p)-(b : ZMod p))*(↑((ZMod.unitOfCoprime q hqp)⁻¹) : ZMod p)).val

end ErdosInverseHits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AugmentedCRTCell
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def augmentedModuli {ι : Type*} (M0 : ℕ) (u : ι → ℕ) : Option ι → ℕ
  | none => M0
  | some i => u i

noncomputable def cellResidues {ι : Type*} (M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    ∀ j : Option ι,Finset (ZMod (augmentedModuli M0 u j))
  | none => {v}
  | some i => affineResidues (c i) (b i) (E i)

noncomputable def slopeCell {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter (fun s => (s : ZMod M0) = v ∧ ∀ i,(c i : ZMod (u i))*(s : ZMod (u i))+b i ∈ E i)

end ErdosInverseCRT

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SlopeCellPartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def sampledSlopes {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter
    (fun s => ∀ i,(c i : ZMod (u i))*(s : ZMod (u i))+b i ∈ E (s : ZMod M0) i)

end ErdosInverseCRT

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceEdgeClasses
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def sourceEdgeResidue (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b s : ℤ) : ZMod u :=
  ((a : ZMod u)-(b : ZMod u)-(q : ZMod u)*(s : ZMod u))*
    (↑((ZMod.unitOfCoprime p hp*ZMod.unitOfCoprime q hq)⁻¹) : ZMod u)

noncomputable def sourceCoefficient (p u : ℕ) (hp : Nat.Coprime p u) : (ZMod u)ˣ :=
  -(ZMod.unitOfCoprime p hp)⁻¹

noncomputable def sourceShift (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b : ℤ) : ZMod u :=
  ((a : ZMod u)-(b : ZMod u))*(↑((ZMod.unitOfCoprime p hp*ZMod.unitOfCoprime q hq)⁻¹) : ZMod u)

noncomputable def sourceTestedSlopes {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter
    (fun s => ∀ i,sourceEdgeResidue p q0 (u i) (hp i) (hq i) (a (u i)) b0 s ∈ E (s : ZMod M0) i)

end ErdosInverseCRT

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ParentEdgeCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits
open ErdosInverseCounts

noncomputable def sourceParentBase (p q : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (a : ℕ → ℕ) : ℕ :=
  primeHitRepresentative q hq a+q*parentSlope p q hqp (a p) (primeHitRepresentative q hq a)

noncomputable def parentSurvivorCoordinates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (hq : Squarefree q) : Finset ℕ := by
  classical
  exact (Finset.range (hitLength Y (p*q) (sourceParentBase p q hqp hq a))).filter
    (fun j => ∀ t ∈ small,(sourceParentBase p q hqp hq a+p*q*j)%t ≠ a t%t)

end ErdosInverseHits

end

section

namespace ErdosInverseHits
open ErdosInverseCounts NumberTheoryLean NumberTheoryLean.SievePartition ErdosInverseCRT

noncomputable def parentEdgeResidue (p q u : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) (a : ℕ → ℕ) : ZMod u :=
  sourceEdgeResidue p q u hpu hqu (a u) (primeHitRepresentative q hq a)
    (parentSlope p q hqp (a p) (primeHitRepresentative q hq a))

end ErdosInverseHits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueCountDifference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.ProgressionSmallSieve

def progressionHit (a : ℤ) (q : ℕ) (residue : ℕ → ℕ) (p i : ℕ) : Prop :=
  Int.ModEq (p : ℤ) (a + (q : ℤ) * i) (residue p : ℤ)

noncomputable def progressionSurvivors (N z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.range N) (LargePrimeDeletion.cutoffPrimes z)
    (progressionHit a q residue)

end NumberTheoryLean.ProgressionSmallSieve



namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean
attribute [local instance] Classical.propDecidable

noncomputable def modulusOffsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) : Finset ℕ :=
  (Finset.range (hitLength Y d (primeHitRepresentative d hd a))).filter
    (fun j => ∀ p ∈ small,(primeHitRepresentative d hd a+d*j)%p ≠ a p%p)

end ErdosModulusRelative



namespace ErdosPrimeInputs.SubsetPrimeSieve

open Finset
open NumberTheoryLean
open SmallSieveFinite IntervalBoundingSieve

noncomputable def euler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

end ErdosPrimeInputs.SubsetPrimeSieve



namespace ErdosInverseTail
open NumberTheoryLean

noncomputable def sieveTail (J N z : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.Ico J N) (LargePrimeDeletion.cutoffPrimes z)
    (ProgressionSmallSieve.progressionHit b step a)

end ErdosInverseTail



namespace ErdosInverseTail
open NumberTheoryLean ErdosInverseHits

noncomputable def residueOffset (J u : ℕ) [NeZero u] (e : ZMod u) : ℕ := (e-(J : ZMod u)).val

end ErdosInverseTail



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SmallModelSourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseHits

noncomputable def frozenCoordinates (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) : Finset ℕ :=
  ProgressionSmallSieve.progressionSurvivors N ⌊w⌋₊ (b+(q : ℤ)*v) (p*q) a

end ErdosInverseFrozen

end

section

namespace ErdosInverseEuler
open NumberTheoryLean

noncomputable def smallModulus (w : ℝ) : ℕ := IntervalBoundingSieve.cutoffProduct ⌊w⌋₊

theorem smallModulus_pos (w : ℝ) : 0 < smallModulus w := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  exact Finset.prod_pos (fun p hp => (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1.pos)

end ErdosInverseEuler

end

section

namespace ErdosVarianceSmallModel
open NumberTheoryLean ErdosInverseEuler ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def divisorPrimes (w : ℝ) (H : ℕ) : Finset ℕ :=
  (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊).filter (fun t => t ∣ H)
noncomputable def coprimePrimes (w : ℝ) (H : ℕ) : Finset ℕ :=
  (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊).filter (fun t => ¬t ∣ H)
noncomputable def divisorModulus (w : ℝ) (H : ℕ) : ℕ := ∏ t ∈ divisorPrimes w H,t
noncomputable def coprimeModulus (w : ℝ) (H : ℕ) : ℕ := ∏ t ∈ coprimePrimes w H,t

theorem divisorModulus_pos (w : ℝ) (H : ℕ) : 0 < divisorModulus w H :=
  Finset.prod_pos (fun _t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.pos)

theorem coprimeModulus_pos (w : ℝ) (H : ℕ) : 0 < coprimeModulus w H :=
  Finset.prod_pos (fun _t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.pos)

theorem divisorModulus_dvd_H (w : ℝ) (H : ℕ) : divisorModulus w H ∣ H := by
  apply Finset.prod_primes_dvd
  · intro t ht
    exact (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.prime
  · intro t ht
    exact (Finset.mem_filter.mp ht).2

theorem coprimeModulus_coprime_H (w : ℝ) (H : ℕ) : (coprimeModulus w H).Coprime H := by
  apply Nat.coprime_prod_left_iff.mpr
  intro t ht
  have hh := Finset.mem_filter.mp ht
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hh.1).1.coprime_iff_not_dvd.mpr hh.2

theorem pattern_moduli_coprime (w : ℝ) (H : ℕ) : (divisorModulus w H).Coprime (coprimeModulus w H) :=
  (coprimeModulus_coprime_H w H).symm.of_dvd_left (divisorModulus_dvd_H w H)

theorem effective_pattern_coprime (w : ℝ) (H : ℕ) :
    (H*divisorModulus w H).Coprime (coprimeModulus w H) :=
  (coprimeModulus_coprime_H w H).symm.mul_left (pattern_moduli_coprime w H)

theorem prime_coprime_small_pattern (w : ℝ) (hw : 0 ≤ w) (H p : ℕ)
    (hp : p.Prime) (hwp : w < (p : ℝ)) : p.Coprime (coprimeModulus w H) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro t ht
  have hh := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
  have htw := (Nat.le_floor_iff hw).mp hh.2
  apply (Nat.coprime_primes hp hh.1).mpr
  intro he
  subst t
  linarith

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel

instance instNeZeroNatDivisorModulus (w : ℝ) (H : ℕ) : NeZero (divisorModulus w H) := ⟨(divisorModulus_pos w H).ne'⟩
instance instNeZeroNatCoprimeModulus (w : ℝ) (H : ℕ) : NeZero (coprimeModulus w H) := ⟨(coprimeModulus_pos w H).ne'⟩

abbrev Pattern (w : ℝ) (H : ℕ) := (ZMod (coprimeModulus w H))ˣ × ZMod (divisorModulus w H)
abbrev ModelPoint (w : ℝ) (H : ℕ) := ℤ × Pattern w H

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ActualCofactorCellData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

noncomputable def selections {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) : Finset (ι → Finset ℕ) :=
  Fintype.piFinset (fun i => (P i).powersetCard (m i))

def selectionProduct {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) : ℕ :=
  ∏ i, ∏ p ∈ f i, p

noncomputable def selectionPrimes {ι : Type*} [Fintype ι]
    (f : ι → Finset ℕ) : Finset ℕ := Finset.univ.biUnion f

end ErdosCofactorChoices

end

section

namespace ErdosCofactorChoices
attribute [local instance] Classical.decEq

noncomputable def cofactorChoices {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (m : ι → ℕ) : Finset ℕ :=
  (selections P m).image selectionProduct

end ErdosCofactorChoices

end

section

open _root_.Filter
namespace ErdosCofactorChoices
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
open NumberTheoryLean.LogarithmicBinPartition

noncomputable def actualBins (z xi : ℝ) : Fin (binCount (sourceW z) z xi) → Finset ℕ :=
  fun i => primeBin (lower (sourceW z) z xi i) (width (sourceW z) z xi i)

noncomputable def cofactorScale (z xi : ℝ) (m : Fin (binCount (sourceW z) z xi) → ℕ) : ℝ :=
  ∏ i, (upper (sourceW z) z xi i)^(m i)

end ErdosCofactorChoices

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceLabelCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

noncomputable def labelFiber {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) : Finset ℕ :=
  Q.filter (fun q => label q = i)

noncomputable def smallLabels {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => ((labelFiber Q label i).card : ℝ) < tau)

noncomputable def discardedPoints {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) : Finset ℕ :=
  (smallLabels Q label tau).biUnion (labelFiber Q label)

end ErdosInverseCells

end

section

namespace ErdosGeometricValueCells

noncomputable def coordinate (B xi q : ℝ) : ℝ := Real.log (B/q)/Real.log (1+xi)

noncomputable def valueIndex (B xi : ℝ) (k : ℕ) (q : ℝ) : Fin (k+1) :=
  ⟨min k ⌊coordinate B xi q⌋₊, Nat.lt_succ_of_le (min_le_left _ _)⟩

end ErdosGeometricValueCells

end

section

namespace ErdosInverseCells
open ErdosInverseHits ErdosGeometricValueCells
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def cofactorHit (q : ℕ) (a : ℕ → ℕ) : ℕ :=
  if hq : Squarefree q then primeHitRepresentative q hq a else 0

abbrev InitialLabel (k M0 : ℕ) := Fin (k+1) × ZMod M0 × ZMod M0

noncomputable def initialLabel (a : ℕ → ℕ) (B xi : ℝ) (k M0 q : ℕ) : InitialLabel k M0 :=
  ⟨valueIndex B xi k (q : ℝ),(q : ZMod M0),(cofactorHit q a : ZMod M0)⟩

noncomputable def initialCell (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) : Finset ℕ := labelFiber Q (initialLabel a B xi k M0) i

noncomputable def cellUpper (B xi : ℝ) {k M0 : ℕ} (i : InitialLabel k M0) : ℝ :=
  B/(1+xi)^i.1.val

end ErdosInverseCells

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells

abbrev RefinementLabel (W : ℕ) := ZMod W × ZMod W

noncomputable def refinementLabel (a : ℕ → ℕ) (W q : ℕ) : RefinementLabel W :=
  ⟨(q : ZMod W),(cofactorHit q a : ZMod W)⟩

noncomputable def refinementCell (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) (i : RefinementLabel W) : Finset ℕ :=
  labelFiber C (refinementLabel a W) i

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedCofactorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def alignedPrimeFactors (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : Finset ℕ :=
  qf.primeFactors.filter (aligns a r)

noncomputable def alignedPrimeProduct (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : ℕ :=
  ∏ p ∈ alignedPrimeFactors a r qf,p

noncomputable def alignedCofactor (a : ℕ → ℤ) (r : ℚ) (qf : ℕ) : ℕ :=
  qf/badPrimeProduct a r qf

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def hitNumerator (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℤ :=
  (r.den : ℤ)*(cofactorHit qf a : ℤ)-r.num

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EffectiveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

noncomputable def effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℕ :=
  r.den*badPrimeProduct (fun t => (a t : ℤ)) r qf

noncomputable def effectiveIntercept (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℤ :=
  hitNumerator a r qf/(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveSurvivors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells ErdosInverseHits ErdosHypotheticalTag ErdosInverseCounts ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def effectiveBase (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) : ℕ :=
  cofactorHit qf a+qf*intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)

noncomputable def effectiveSurvivors (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) : Finset ℕ :=
  (Finset.range (hitLength Y (p*qf) (effectiveBase a r qf p hHp))).filter
    (fun j => ∀ t ∈ small,(effectiveBase a r qf p hHp+p*qf*j)%t ≠ a t%t)

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EffectiveAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells

noncomputable def effectiveInteger (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (j : ℤ) : ℤ :=
  (cofactorHit qf a : ℤ)+(qf : ℤ)*
    ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)+(p : ℤ)*j)

end ErdosVarianceEffective

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EffectiveCommonInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceCommon
open ErdosVarianceEffective ErdosInverseTail ErdosInverseHits

noncomputable def commonLength (Y qf : ℕ) (R xi : ℝ) : ℕ :=
  commonParentLength Y qf ((1+xi)*R)

end ErdosVarianceCommon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SmallModelMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def modelUnitIntegers (R xi : ℝ) (H : ℕ) (C0 : ℤ) : Finset ℤ :=
  (modelIntegers R xi (H : ℝ) (C0 : ℝ)).filter (fun m => m.natAbs.Coprime H)

noncomputable def modelUniverse (R xi w : ℝ) (H : ℕ) (C0 : ℤ) : Finset (ModelPoint w H) :=
  (modelUnitIntegers R xi H C0).product Finset.univ

noncomputable def atomWeight (R xi w : ℝ) (H : ℕ) (C0 : ℤ) : ℝ :=
  (H : ℝ)/((H.totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)*
    (divisorModulus w H : ℝ)*((coprimeModulus w H).totient : ℝ))

noncomputable def modelMass (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (E : ModelPoint w H → Prop) : ℝ :=
  ∑ _v ∈ (modelUniverse R xi w H C0).filter E,atomWeight R xi w H C0

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualPatternClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel
open ErdosHyperbolaError

noncomputable def coordinateUnit (w : ℝ) (H : ℕ) (m : ℤ) (hm : m.natAbs.Coprime H) :
    (ZMod (H*divisorModulus w H))ˣ :=
  ZMod.unitOfIsCoprime m (by
    have hgm : Int.gcd m (H : ℤ) = 1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hm.gcd_eq_one
    have hh := source_product_coprime H (divisorModulus w H) (divisorModulus_dvd_H w H) m 0 hgm
    simpa only [mul_zero,add_zero] using hh)

noncomputable def liftedNumeratorUnit (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (k : ZMod (divisorModulus w H)) :
    (ZMod (H*divisorModulus w H))ˣ :=
  ZMod.unitOfIsCoprime (C0+(H : ℤ)*(k.val : ℤ))
    (source_product_coprime H (divisorModulus w H) (divisorModulus_dvd_H w H) C0 k.val hC0)

noncomputable def restrictionUnit (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H)
    (k : ZMod (divisorModulus w H)) : (ZMod (H*divisorModulus w H))ˣ :=
  liftedNumeratorUnit w H C0 hC0 k*(coordinateUnit w H m hm)⁻¹

noncomputable def patternClass (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H) (s : Pattern w H) : ℕ :=
  (Nat.chineseRemainder (effective_pattern_coprime w H)
    (restrictionUnit w H C0 hC0 m hm s.2).val.val s.1.val.val).val

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeProductOmissions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_SieveScale
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.AffinePrimeSieve

open _root_.Finset
open NumberTheoryLean IntervalBoundingSieve SubsetPrimeSieve PrimeProductOmissions

noncomputable def value (a : ℤ) (q i : ℕ) : ℤ := a + (q:ℤ)*i
noncomputable def survivors (N : ℕ) (a : ℤ) (q : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (range N).filter (fun i => ∀ p ∈ P, ¬Int.ModEq (p:ℤ) (value a q i) 0)
noncomputable def primeIndices (N : ℕ) (a : ℤ) (q : ℕ) : Finset ℕ :=
  (range N).filter (fun i => (value a q i).natAbs.Prime ∧ 0 ≤ value a q i)
noncomputable def smallPrimeIndices (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) : Finset ℕ :=
  (primeIndices N a q).filter (fun i => ((value a q i).natAbs : ℝ) ≤ u)

end ErdosPrimeInputs.AffinePrimeSieve

end

section

namespace ErdosPrimeInputs.SieveScale

open _root_.Filter
open scoped Topology

noncomputable def level : ℝ := 480024
noncomputable def exponent : ℝ := 1 / (2*level)
noncomputable def cutoff (J : ℝ) : ℝ := J ^ exponent

end ErdosPrimeInputs.SieveScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeFibreInterval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

noncomputable def geometricFibre (P : Finset ℕ) (H C0 : ℝ) (m : ℤ) : Finset ℕ :=
  P.filter (fun p => C0/(p : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) < C0/(p : ℝ)+H)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrimeFibreBrunBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

noncomputable def residueFibre (P : Finset ℕ) (H C0 : ℝ) (m : ℤ) (M : ℕ) (b : ℤ) : Finset ℕ :=
  (geometricFibre P H C0 m).filter (fun p => Int.ModEq (M : ℤ) (p : ℤ) b)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeEventCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel
open ErdosVarianceEffective
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def goodPrimes (P : Finset ℕ) (H : ℕ) : Finset ℕ := P.filter (fun p => H.Coprime p)

noncomputable def primeM (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) : ℤ := by
  letI : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0 p.val H (Finset.mem_filter.mp p.property).2 C0

noncomputable def primeK (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) : ℕ := by
  letI : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalK p.val H (Finset.mem_filter.mp p.property).2 C0

noncomputable def primePoint (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) : ModelPoint w H :=
  ⟨primeM P H C0 hP p,
    ZMod.unitOfCoprime p.val (prime_coprime_small_pattern w hw H p.val
      (hP _ (Finset.mem_filter.mp p.property).1) (hlarge _ (Finset.mem_filter.mp p.property).1)),
    (primeK P H C0 hP p : ZMod (divisorModulus w H))⟩

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def primeFibre (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (v : ModelPoint w H) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => primePoint P w H C0 hw hP hlarge p = v)

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def indexedPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => E (primePoint P w H C0 hw hP hlarge p))

noncomputable def actualPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) : Finset ℕ :=
  (indexedPrimeEvent P w H C0 hw hP hlarge E).image Subtype.val

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel

theorem int_isCoprime_of_natAbs (m : ℤ) (H : ℕ) (hm : m.natAbs.Coprime H) : IsCoprime m (H : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def,Int.natAbs_natCast] using hm.gcd_eq_one

noncomputable def divisorPhase (C0 m : ℤ) (t : ℕ) : ZMod t := (C0 : ZMod t)*(m : ZMod t)⁻¹

noncomputable def patternPValue (w : ℝ) (H : ℕ) (s : Pattern w H) (t : ℕ) : ZMod t :=
  (s.1.val.val : ZMod t)
noncomputable def patternKValue (w : ℝ) (H : ℕ) (s : Pattern w H) (t : ℕ) : ZMod t :=
  (s.2.val : ZMod t)

noncomputable def divisorPhaseUnit (H : ℕ) (C0 m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hm : m.natAbs.Coprime H) (t : ℕ) (htH : t ∣ H) : (ZMod t)ˣ :=
  (ZMod.unitOfIsCoprime C0 (int_isCoprime_of_natAbs C0 t (by
    have hc : C0.natAbs.Coprime H := by
      rw [Nat.coprime_iff_gcd_eq_one]
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hC0
    exact hc.of_dvd_right htH))) *
    (ZMod.unitOfIsCoprime m (int_isCoprime_of_natAbs m t (hm.of_dvd_right htH)))⁻¹

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualModelTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

def modelSurvives (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) : Prop :=
  (∀ t ∈ divisorPrimes w H,patternKValue w H v.2 t+divisorPhase C0 v.1 t*(j : ZMod t) ≠ beta t) ∧
  (∀ t ∈ coprimePrimes w H,patternPValue w H v.2 t*(qA : ZMod t)*
    ((v.1 : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t)

noncomputable def modelIndicator (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) (v : ModelPoint w H) : ℝ :=
  if modelSurvives w H C0 qA beta delta j v then 1 else 0

def jointCondition (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) : Prop :=
  ∀ j ∈ S,modelSurvives w H C0 qA beta delta j v

noncomputable def jointIndicator (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (v : ModelPoint w H) : ℝ :=
  if jointCondition w H C0 qA beta delta S v then 1 else 0

end ErdosVarianceMoments

end

section

namespace ErdosVarianceCommon
open NumberTheoryLean

noncomputable def referenceCount (Y : ℕ) (w : ℝ) (p qf : ℕ) : ℝ :=
  (Y : ℝ)/((p : ℝ)*qf)*SmallSieveFinite.smallEuler ⌊w⌋₊

noncomputable def commonReference (J : ℕ) (w : ℝ) : ℝ :=
  (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊

end ErdosVarianceCommon

end

section

namespace ErdosVarianceCommon
open NumberTheoryLean ErdosVarianceEffective ErdosInverseCounts ErdosHypotheticalTag
  ErdosInverseHits ErdosInverseTail
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def commonSurvivors (J : ℕ) (w : ℝ) (a : ℕ → ℕ) (r : ℚ)
    (qf p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) : Finset ℕ :=
  ProgressionSmallSieve.progressionSurvivors J ⌊w⌋₊ (effectiveBase a r qf p hHp) (p*qf) a

end ErdosVarianceCommon

end

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel ErdosVarianceEffective ErdosInverseCells ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def actualDivisorTarget (a : ℕ → ℕ) (qf t : ℕ) : ZMod t :=
  ((a t : ZMod t)-(cofactorHit qf a : ZMod t))*(qf : ZMod t)⁻¹

noncomputable def actualCoprimeTarget (a : ℕ → ℕ) (r : ℚ) (t : ℕ) : ZMod t :=
  (r.den : ZMod t)*(a t : ZMod t)-(r.num : ZMod t)

def actualModelSurvives (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf j : ℕ)
    (v : ModelPoint w (effectiveModulus a r qf)) : Prop :=
  modelSurvives w (effectiveModulus a r qf) (effectiveIntercept a r qf)
    (alignedCofactor (fun t => (a t : ℤ)) r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v

noncomputable def actualModelIndicator (w : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf j : ℕ)
    (v : ModelPoint w (effectiveModulus a r qf)) : ℝ :=
  modelIndicator w (effectiveModulus a r qf) (effectiveIntercept a r qf)
    (alignedCofactor (fun t => (a t : ℤ)) r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) j v

end ErdosVarianceMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CoprimePositionSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def divisorJoint (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (k : ZMod (divisorModulus w H)) : Prop :=
  ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k.val : ZMod t)+divisorPhase C0 m t*(j : ZMod t) ≠ beta t

def coprimeJoint (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (p : (ZMod (coprimeModulus w H))ˣ) : Prop :=
  ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(p.val.val : ZMod t)*(qA : ZMod t)*
    ((m : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def patternPrimeUnit (w : ℝ) (H : ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (t : ℕ) (ht : t ∣ coprimeModulus w H) : (ZMod t)ˣ :=
  Units.map (ZMod.castHom ht (ZMod t)).toMonoidHom p

noncomputable def coprimeCoefficientUnit (w : ℝ) (H qA : ℕ)
    (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) : (ZMod t)ˣ :=
  patternPrimeUnit w H p t (Finset.dvd_prod_of_mem _ ht)*ZMod.unitOfCoprime qA hqA

noncomputable def coprimeShiftUnit (w : ℝ) (H t : ℕ) (ht : t ∈ coprimePrimes w H) : (ZMod t)ˣ :=
  ZMod.unitOfCoprime H ((LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp ht).2).symm

noncomputable def coprimeForbidden (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) : Finset (ZMod t) :=
  forbiddenClasses S t (coprimeShiftUnit w H t ht)
    ((coprimeCoefficientUnit w H qA p t ht hqA)⁻¹*delta t)

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def coprimeForbiddenFamily (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (t : ℕ) : Finset (ZMod t) :=
  if ht : t ∈ coprimePrimes w H then coprimeForbidden w H qA delta S p t ht (hqA t ht) else ∅

noncomputable def coprimePositionSurvivors (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (b c : ℝ) : Finset ℤ :=
  (unitIntervalIntegers H b c).filter (fun m => coprimeJoint w H qA delta S m p)

end ErdosVarianceMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OddEulerCorrection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosOddEulerCorrection

noncomputable def correction (k : ℕ) : ℝ := 1-1/((k : ℝ)+2)^2

end ErdosOddEulerCorrection


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_JointModelDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosRandomVariance ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def densityInverseConstant : ℝ := 8*(Real.exp Real.eulerMascheroniConstant)^2

end ErdosVarianceUniformMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LossBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosBoundaryLoss
noncomputable def loss2Kernel (t x : ℝ) : ℝ :=
  ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
noncomputable def loss3Kernel (t u x : ℝ) : ℝ :=
  ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
noncomputable def L2 : ℝ := ∫ t : ℝ in 1..2,∫ x : ℝ in t..2,
  ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
noncomputable def L3 : ℝ := ∫ t : ℝ in 1..2,∫ u : ℝ in t..2,∫ x : ℝ in u..2,
  ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

noncomputable def inner2Primitive (t x : ℝ) : ℝ :=
  x
  + ((-1:ℝ) * x * (t^2)⁻¹)
  + ((-2:ℝ) * (t^1)⁻¹ * (Real.log x))
  + ((1/4:ℝ) * (t^1)⁻¹ * (x^2))
  + ((1/36:ℝ) * (t^2)⁻¹ * (x^3))
  + ((2/3:ℝ) * t * (Real.log x))
  + ((4/3:ℝ) * (t^2)⁻¹ * (Real.log x))

noncomputable def middle3Kernel (t u : ℝ) : ℝ :=
  (-1:ℝ)
  + ((1/2:ℝ) * (t^2)⁻¹)
  + ((-1:ℝ) * (Real.log u))
  + ((2:ℝ) * (t^1)⁻¹)
  + ((2:ℝ) * (u^1)⁻¹)
  + ((t^1)⁻¹ * (u^1)⁻¹)
  + ((1/2:ℝ) * u * (t^2)⁻¹)
  + ((-14/9:ℝ) * (t^2)⁻¹ * (u^1)⁻¹)
  + ((-13/72:ℝ) * (t^2)⁻¹ * (u^2))
  + ((-5/4:ℝ) * u * (t^1)⁻¹)
  + ((1/2:ℝ) * u * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-2/3:ℝ) * t * (u^1)⁻¹ * (Real.log u))
  + ((-1/2:ℝ) * u * (t^1)⁻¹ * (Real.log u))
  + ((-1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log u))
  + ((1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log (2:ℝ)))
  + ((2/3:ℝ) * t * (u^1)⁻¹ * (Real.log (2:ℝ)))
  + (Real.log (2:ℝ))

noncomputable def inner3Primitive (t u x : ℝ) : ℝ :=
  (x * (t^1)⁻¹)
  + (x * (u^1)⁻¹)
  + ((1/8:ℝ) * (t^2)⁻¹ * (x^2))
  + ((1/2:ℝ) * u * (t^1)⁻¹ * (Real.log x))
  + ((-7/36:ℝ) * (t^2)⁻¹ * (u^1)⁻¹ * (x^3))
  + ((1/4:ℝ) * u * x * (t^2)⁻¹)
  + ((1/4:ℝ) * (t^1)⁻¹ * (u^1)⁻¹ * (x^2))
  + ((1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log x))
  + ((2/3:ℝ) * t * (u^1)⁻¹ * (Real.log x))
  + (Real.log x)

noncomputable def middle3Primitive (t u : ℝ) : ℝ :=
  ((2:ℝ) * (Real.log u))
  + (u * (Real.log (2:ℝ)))
  + ((t^1)⁻¹ * (Real.log u))
  + ((1/2:ℝ) * u * (t^2)⁻¹)
  + ((-1:ℝ) * u * (Real.log u))
  + ((2:ℝ) * u * (t^1)⁻¹)
  + ((-14/9:ℝ) * (t^2)⁻¹ * (Real.log u))
  + ((-11/216:ℝ) * (t^2)⁻¹ * (u^3))
  + ((-1/2:ℝ) * (t^1)⁻¹ * (u^2))
  + ((-1/3:ℝ) * t * ((Real.log u)^2))
  + ((1/4:ℝ) * (t^2)⁻¹ * (u^2))
  + ((-1/4:ℝ) * (t^1)⁻¹ * (u^2) * (Real.log u))
  + ((-1/36:ℝ) * (t^2)⁻¹ * (u^3) * (Real.log u))
  + ((1/4:ℝ) * (t^1)⁻¹ * (u^2) * (Real.log (2:ℝ)))
  + ((1/36:ℝ) * (t^2)⁻¹ * (u^3) * (Real.log (2:ℝ)))
  + ((2/3:ℝ) * t * (Real.log (2:ℝ)) * (Real.log u))

noncomputable def reduced2 (t : ℝ) : ℝ :=
  (2:ℝ)
  + ((2:ℝ) * (t^1)⁻¹)
  + ((-23/18:ℝ) * t)
  + ((-16/9:ℝ) * (t^2)⁻¹)
  + ((-2:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((2:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((-4/3:ℝ) * (t^2)⁻¹ * (Real.log t))
  + ((-2/3:ℝ) * t * (Real.log t))
  + ((2/3:ℝ) * t * (Real.log (2:ℝ)))
  + ((4/3:ℝ) * (t^2)⁻¹ * (Real.log (2:ℝ)))

noncomputable def reduced3 (t : ℝ) : ℝ :=
  (-9/4:ℝ)
  + ((-2:ℝ) * (Real.log t))
  + ((2:ℝ) * (Real.log (2:ℝ)))
  + ((3/2:ℝ) * (t^1)⁻¹)
  + ((43/27:ℝ) * (t^2)⁻¹)
  + ((119/216:ℝ) * t)
  + ((t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-1:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((-23/18:ℝ) * t * (Real.log (2:ℝ)))
  + ((-14/9:ℝ) * (t^2)⁻¹ * (Real.log (2:ℝ)))
  + ((1/3:ℝ) * t * ((Real.log (2:ℝ))^2))
  + ((1/3:ℝ) * t * ((Real.log t)^2))
  + ((14/9:ℝ) * (t^2)⁻¹ * (Real.log t))
  + ((23/18:ℝ) * t * (Real.log t))
  + ((-2/3:ℝ) * t * (Real.log (2:ℝ)) * (Real.log t))

noncomputable def outer2Primitive (t : ℝ) : ℝ :=
  ((Real.log t)^2)
  + ((2:ℝ) * t)
  + ((2:ℝ) * (Real.log t))
  + ((-17/36:ℝ) * (t^2))
  + ((28/9:ℝ) * (t^1)⁻¹)
  + ((-2:ℝ) * (Real.log (2:ℝ)) * (Real.log t))
  + ((-4/3:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-1/3:ℝ) * (t^2) * (Real.log t))
  + ((1/3:ℝ) * (t^2) * (Real.log (2:ℝ)))
  + ((4/3:ℝ) * (t^1)⁻¹ * (Real.log t))

noncomputable def outer3Primitive (t : ℝ) : ℝ :=
  ((-85/27:ℝ) * (t^1)⁻¹)
  + ((-1/2:ℝ) * ((Real.log t)^2))
  + ((-1/4:ℝ) * t)
  + ((3/2:ℝ) * (Real.log t))
  + ((17/432:ℝ) * (t^2))
  + ((Real.log (2:ℝ)) * (Real.log t))
  + ((-2:ℝ) * t * (Real.log t))
  + ((2:ℝ) * t * (Real.log (2:ℝ)))
  + ((-17/36:ℝ) * (t^2) * (Real.log (2:ℝ)))
  + ((-14/9:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((1/6:ℝ) * (t^2) * ((Real.log (2:ℝ))^2))
  + ((1/6:ℝ) * (t^2) * ((Real.log t)^2))
  + ((14/9:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((17/36:ℝ) * (t^2) * (Real.log t))
  + ((-1/3:ℝ) * (t^2) * (Real.log (2:ℝ)) * (Real.log t))

end ErdosBoundaryLoss

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OmissionSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def baseCutoff (b : ℝ) : ℝ := max 1 (min 2 b)
noncomputable def survivorBaseline (b : ℝ) : ℝ := (baseCutoff b)⁻¹

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarFreeGate
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail

noncomputable def lastWindowCoefficient (S a b c : ℝ) : ℝ :=
  ((S+a+b+2*c)^3-(S+2*a)^3)/(12*c)

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedMass : ℕ → ℝ → ℝ
  | 0,_ => 1
  | n+1,b => ∫ x in (1:ℝ)..baseCutoff b,orderedMass n x/(max 1 x)

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

abbrev ScalarProfile := ℝ → ℝ → ℝ
def ScalarContinuous (H : ScalarProfile) : Prop := Continuous (fun p : ℝ×ℝ => H p.1 p.2)
noncomputable def scalarFreeGate (H : ScalarProfile) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..baseCutoff b,H (r-x) x/(max 1 x)

noncomputable def scalarFreeIterate : ℕ → ScalarProfile → ScalarProfile
  | 0,H => H
  | n+1,H => scalarFreeGate (scalarFreeIterate n H)

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ThirdInnerKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

noncomputable def clampedThird (x u t : ℝ) : ℝ :=
  loss3Kernel (baseCutoff t) (baseCutoff u) (baseCutoff x)

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ThirdMovingIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary ErdosBoundaryLoss

noncomputable def thirdLowerIntegral (p : ℝ×ℝ) : ℝ :=
  ∫ t : ℝ in 1..baseCutoff p.2,clampedThird p.1 p.2 t

noncomputable def thirdUpperIntegral (p : ℝ×ℝ) : ℝ :=
  ∫ x : ℝ in baseCutoff p.1..2,clampedThird x p.1 p.2

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_JacobsthalTerminalScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.JacobsthalTerminalScales
open _root_.Filter _root_.Asymptotics JacobsthalSourceScale
open scoped Topology

noncomputable def terminalTop (x : ℝ) : ℝ := x*Real.log x
noncomputable def terminalY (x : ℝ) : ℕ := ErdosInverseBoxHeight.sourceY (terminalTop x)
noncomputable def terminalCutoff (x : ℝ) : ℕ := ⌊terminalTop x⌋₊

end NumberTheoryLean.JacobsthalTerminalScales


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_IteratedLogScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970.NumberTheoryLean.IteratedLogScales

open _root_.Filter JacobsthalTerminalScales
open scoped Topology

noncomputable def loglog (x : ℝ) : ℝ := Real.log (Real.log (3 * x))

noncomputable def rescale (A x : ℝ) : ℝ := A * x / loglog x

end Erdos970.NumberTheoryLean.IteratedLogScales

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EdgeBinBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open ErdosInversePrimeBin

noncomputable def edgeFrequencyCap (U : ℝ) : ℕ := ⌈2*U⌉₊

end ErdosInverseSaving

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FiniteSampleSpace
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

abbrev Sample {α : Type*} (U : Finset α) (h : ℕ) := Fin h ↪ U

noncomputable def goodSamples {α : Type*} (U W : Finset α) (h : ℕ) : Finset (Sample U h) := by
  classical
  exact Finset.univ.filter (fun e => ∀ i, (e i).val ∈ W)

noncomputable def goodSampleEquiv {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    (goodSamples U W h) ≃ Sample W h where
  toFun e :=
    { toFun := fun i => ⟨(e.val i).val,(Finset.mem_filter.mp e.property).2 i⟩
      inj' := by
        intro i j he
        apply e.val.injective
        exact Subtype.ext (congrArg (fun x : W => x.val) he) }
  invFun f :=
    ⟨{ toFun := fun i => ⟨(f i).val,hWU (f i).property⟩
       inj' := by
         intro i j he
         apply f.injective
         exact Subtype.ext (congrArg (fun x : U => x.val) he) },by
       classical
       apply Finset.mem_filter.mpr
       exact ⟨Finset.mem_univ _,fun i => (f i).property⟩⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

noncomputable def sampleFrequency {α : Type*} (U W : Finset α) (h : ℕ) : ℝ :=
  ((goodSamples U W h).card : ℝ)/(Fintype.card (Sample U h) : ℝ)

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceSamplePopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def sampleAverage {α : Type*} (U : Finset α) (h : ℕ) (f : Sample U h → ℝ) : ℝ :=
  (∑ e : Sample U h,f e)/(Fintype.card (Sample U h) : ℝ)

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CRTPrimeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def primeCost (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (s : Sample U h) : ℝ :=
  ((p : ℝ)/(M0 : ℝ))*(∑ v : ZMod M0,∏ i : Fin h,((E p v (s i)).card : ℝ)/((s i).val : ℝ))+
    (M0 : ℝ)*(∏ i : Fin h,((s i).val : ℝ))

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerResidueVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

noncomputable def residueCount (N : ℕ) (S : Finset ℤ) (e : ZMod N) : ℕ :=
  (integerFibre N S e).card

noncomputable def spectrum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) : ℂ :=
  integerWeight N S (-a)

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

noncomputable def integerResidueCount (N : ℕ) (S : Finset ℤ) (e : ℕ) : ℕ :=
  (S.filter (fun x => x % (N : ℤ) = (e : ℤ))).card

noncomputable def integerResidueVariance (N : ℕ) (S : Finset ℤ) : ℝ :=
  ∑ e ∈ Finset.range N,((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalSpectrumCoefficients
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

noncomputable def intervalCoordinates (S : Finset ℤ) (M : ℤ) (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun j : ℕ => M+(j : ℤ) ∈ S)

noncomputable def indicatorCoefficient (S : Finset ℤ) (x : ℤ) : ℂ := if x ∈ S then 1 else 0

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExceptionalResidues
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def deviationResidues (N : ℕ) (S : Finset ℤ) (T : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun e => T/(N : ℝ) < |(integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ)|)

noncomputable def exceptionalResidues (N : ℕ) (S : Finset ℤ) (T : ℝ) : Finset (ZMod N) :=
  (deviationResidues N S T).image (fun e : ℕ => (e : ZMod N))

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_FrozenSieveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseFrozen
open ErdosInverseSpectrum ErdosHyperbolaIdentities

noncomputable def frozenIntegers (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) : Finset ℤ :=
  (frozenCoordinates N w p q b v a).image (fun j : ℕ => (j : ℤ))

noncomputable def frozenExceptional (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (u : ℕ) (delta V0 : ℝ) : Finset (ZMod u) :=
  exceptionalResidues u (frozenIntegers N w p q b v a) (delta*(N : ℝ)*V0)

end ErdosInverseFrozen

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerSlopeConstruction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def residueSlopes (P : Finset ℕ) (T : P → Finset ℤ) (p : P) : Finset (ZMod p.val) := by
  classical
  exact (T p).image (fun s : ℤ => (s : ZMod p.val))

def IntegerLineIncidence (P : Finset ℕ) (T : P → Finset ℤ)
    (a : P → ℤ) (x y : ℤ) (p : P) : Prop :=
  ∃ s ∈ T p, (y : ZMod p.val) = (a p : ZMod p.val)-(s : ZMod p.val)*(x : ZMod p.val)

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_OriginalSourcePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial ErdosInversePrimeBin

structure SourcePolynomialWitness (z R xi S eta c : ℝ)
    (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ) where
  polynomial : MvPolynomial (Fin 2) ℤ
  height : ℕ
  nonzero : polynomial ≠ 0
  degree_le : polynomial.totalDegree ≤ sourceDegree z R
  height_pos : 0 < height
  coefficient_bound : ∀ m : Fin 2 →₀ ℕ, |polynomial.coeff m| ≤ (height : ℤ)
  line_vanishing : ∀ p : primeBin R xi, ∀ s ∈ T p,
    lineSub (Int.castRingHom (ZMod p.val)) (a p : ZMod p.val) (s : ZMod p.val) polynomial = 0
  height_bound : Real.log (2*(height : ℝ)) ≤ Real.log 4+8*R/(Real.log z)^4
  value_budget : logarithmicValueBudget (sourceDegree z R) height S < c*eta*R/4
  rich_vanishing : ∀ (x y : ℤ), (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) →
    (0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) → ∀ (I : Finset ℕ) (hIP : I ⊆ primeBin R xi),
    c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) →
    (∀ p : I, IntegerLineIncidence (primeBin R xi) T a x y ⟨p.val,hIP p.property⟩) →
    MvPolynomial.eval ![x,y] polynomial = 0

end ErdosSourcePolynomial

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualUnalignedIncidence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph

noncomputable def unalignedPrimes (P : Finset ℕ) (a : ℕ → ℤ) {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) : Finset ℕ := by
  classical
  exact P.filter (fun p => ¬p ∣ l.denominator ∧ ¬aligns a r.rational p)

end ErdosSourceCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_IgnoredDenominatorPrimes
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosInverseBoxHeight

noncomputable def ignoredPrimes (P : Finset ℕ) (d : ℕ) : Finset ℕ := by
  classical
  exact P.filter (fun p => p ∣ d)

end ErdosSourceCollision

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonstructuredCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial ErdosAuxiliaryPolynomial ErdosInversePrimeBin
open ErdosRichLine ErdosConvexGraph

def RichPoint (R xi c : ℝ) (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ)
    (v : ℤ × ℤ) : Prop :=
  ∃ (I : Finset ℕ) (hIP : I ⊆ primeBin R xi), c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) ∧
    ∀ r : I, IntegerLineIncidence (primeBin R xi) T a v.1 v.2 ⟨r.val,hIP r.property⟩

end ErdosSourceLineBudget

end

section

namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine ErdosInversePrimeBin ErdosConvexGraph
attribute [local instance] Classical.propDecidable

def SlopeIncidence (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v : ℤ × ℤ) (p : ℕ) : Prop :=
  ∃ s ∈ T p, (v.2 : ZMod p) = (a p : ZMod p)-(s : ZMod p)*(v.1 : ZMod p)

def NonstructuredIncidence (P : Finset ℕ) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (S R Z cp : ℝ) (v : ℤ × ℤ) (p : ℕ) : Prop :=
  SlopeIncidence a T v p ∧ Nonstructured P a S R Z cp p v.1.toNat

noncomputable def nonstructuredPrimes (P : Finset ℕ) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (S R Z cp : ℝ) (v : ℤ × ℤ) : Finset ℕ :=
  P.filter (NonstructuredIncidence P a T S R Z cp v)

noncomputable def nonstructuredPoints (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ) (p : ℕ) : Finset (ℤ × ℤ) :=
  X.filter (fun v => NonstructuredIncidence P a T S R Z cp v p)

end ErdosInverseStructured

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_SampleWitnessAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def witnessPairs {α β : Type*} (A : Finset α) (U : Finset β) (witness : α → β → Prop) :
    Finset (α × β) :=
  (A.product U).filter (fun v => witness v.1 v.2)

end ErdosInverseSampling

end

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def selectedPairs {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) : Finset α :=
  A.filter (fun a => ∀ i,witness a (e i).val)

noncomputable def selectedFraction {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) : ℝ :=
  ((selectedPairs A U witness h e).card : ℝ)/(A.card : ℝ)

end ErdosInverseSampling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualSampleWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCounts
open NumberTheoryLean

def NodeBadEdge (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (m u : ℕ) : Prop :=
  |(modulusCount Y small a (m*u) : ℝ)-(modulusCount Y small a m : ℝ)/(u : ℝ)| >
    delta*(Y : ℝ)*V0/((m : ℝ)*(u : ℝ))

def WitnessingBadEdge (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (p q u : ℕ) : Prop :=
  NodeBadEdge Y small a delta V0 (p*q) u

end ErdosInverseCounts

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseStructured ErdosInverseCounts ErdosInverseSampling

def actualWitness (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (P : Finset ℕ) (S R Z cp : ℝ) (pair : ℕ × ℕ) (u : ℕ) : Prop :=
  Nonstructured P (fun p => (a p : ℤ)) S R Z cp pair.1 pair.2 ∧
    WitnessingBadEdge Y small a delta V0 pair.1 pair.2 u

end ErdosInverseSampleCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OriginalCofactorPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def selectedRow (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) : Finset ℕ :=
  P.filter (fun p => ∀ i : Fin h,witness (p,q) (s i).val)

noncomputable def rowReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) : ℝ := (selectedRow P U witness h s q).card/(P.card : ℝ)

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def richCofactors (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) : Finset ℕ :=
  D.filter (fun q => gamma/8 ≤ rowReward P U witness h s q)

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosConvexGraph
attribute [local instance] Classical.decEq

noncomputable def cofactorPoint (a : ℕ → ℕ) (q : ℕ) : ℤ × ℤ :=
  ((q : ℤ),(cofactorHit q a : ℤ))

noncomputable def cofactorPoints (D : Finset ℕ) (a : ℕ → ℕ) : Finset (ℤ × ℤ) :=
  D.image (cofactorPoint a)

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualPointSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def totalCost (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (s : Sample U h) : ℝ :=
  (∑ p ∈ P,primeCost U h M0 E p s)/(P.card : ℝ)

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open NumberTheoryLean ErdosInversePrimeBin ErdosInverseFrozen ErdosInverseEuler

noncomputable def frozenPrimeMean (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (delta U theta : ℝ) : ℝ :=
  (∑ u ∈ primeBin U theta,((frozenExceptional N w p q b v a u delta
    (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))/((primeBin U theta).card : ℝ)

noncomputable def meanCoefficient (C K xi delta : ℝ) : ℝ :=
  32*(4+8*Real.pi^2)*C*K*Real.exp Real.eulerMascheroniConstant/(xi*delta^2)

end ErdosInverseSaving

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInverseFrozen ErdosInverseTail ErdosInverseEuler ErdosInversePrimeBin
attribute [local instance] Classical.decEq

noncomputable def actualFamily (Y : ℕ) (w Qplus : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (U : Finset ℕ) (M0 : ℕ) : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val) :=
  fun p v u => frozenExceptional (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a u.val delta
    (SmallSieveFinite.smallEuler ⌊w⌋₊)

noncomputable def actualCost (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h) : ℝ := by
  letI : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  exact totalCost P U h (smallModulus w) (actualFamily Y w Qplus q0 b0 a delta U (smallModulus w)) s/R

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

noncomputable def sampleGamma (beta : ℝ) (h : ℕ) : ℝ := (beta/2)*(beta/4)^h

end ErdosInverseSampleCost

end

section

namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseCRT ErdosInverseEuler ErdosInverseHits ErdosInverseStructured
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def pointSlopes (Y : ℕ) (w Qplus : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u) (qRef : ℕ) (bRef : ℤ)
    (hqRef : ∀ u ∈ U,qRef.Coprime u) (p : ℕ) : Finset ℤ :=
  if hpP : p ∈ P then
    sourceTestedSlopes p qRef (smallModulus w) (fun i => (s i).val)
      (fun i => hp p hpP _ (s i).property) (fun i => hqRef _ (s i).property)
      (fun u => (a u : ℤ)) bRef
      (fun v i => actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w) p v (s i))
  else ∅

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HarmonicConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCells
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def harmonicMass (Q : Finset ℕ) : ℝ := ∑ q ∈ Q,(q : ℝ)⁻¹

noncomputable def tripleSpace (P Q U : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) := (P ×ˢ Q) ×ˢ U

noncomputable def tripleWeight (x : (ℕ × ℕ) × ℕ) : ℝ :=
  (x.1.1 : ℝ)⁻¹*(x.1.2 : ℝ)⁻¹*(x.2 : ℝ)⁻¹

noncomputable def weightedWitness (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ x ∈ witnessPairs (P.product Q) U witness,tripleWeight x

noncomputable def cofactorReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ p ∈ P,∑ u ∈ U,if witness (p,q) u then (p : ℝ)⁻¹*(u : ℝ)⁻¹ else 0

noncomputable def conditionalReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop) (q : ℕ) : ℝ :=
  cofactorReward P U witness q/(harmonicMass P*harmonicMass U)

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceInitialDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler
open NumberTheoryLean.LogarithmicBinScale

noncomputable def initialDiscarded (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k : ℕ) (w Z : ℝ) : Finset ℕ := by
  letI : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  exact discardedPoints Q (initialLabel a B xi k (smallModulus w)) (B/Z)

end ErdosInverseCells

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RefinementPrimeCongruences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open ErdosInverseSampling ErdosInverseSampleCost ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

noncomputable def sampleModulus (U : Finset ℕ) (h : ℕ) (s : Sample U h) : ℕ := ∏ i : Fin h,(s i).val

end ErdosInverseRefinement

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualSourceInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def actualInverseException (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  witnessPairs (P.product Q) U (actualWitness Y small a delta V0 P S R Z cp)

end ErdosInverseBoxApplication

end

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable

def SourceInverseConclusion (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp sigma : ℝ) (F : ℕ) (P Q U : Finset ℕ) : Prop :=
  (sourceRationalList P (fun p => (a p : ℤ)) S R Z cp).card ≤ F ∧
  (∀ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
    (t.num.natAbs : ℝ) ≤ S*R*Z^10 ∧ (t.den : ℝ) ≤ R*Z^10 ∧
      cp*(P.card : ℝ) ≤ ((P.filter (aligns (fun p => (a p : ℤ)) t)).card : ℝ)) ∧
  (∑ e ∈ actualInverseException Y small a delta V0 S R Z cp P Q U,tripleWeight e)/
    (harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma ∧
  (∀ p ∈ P,∀ q ∈ Q,∀ u ∈ U,
    ((p,q),u) ∉ actualInverseException Y small a delta V0 S R Z cp P Q U →
    WitnessingBadEdge Y small a delta V0 p q u →
    ∃ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
      aligns (fun p => (a p : ℤ)) t p ∧
        ((t.den*badPrimeProduct (fun p => (a p : ℤ)) t q : ℕ) : ℝ) ≤ R*Z^10)

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualUnitClasses
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

def radical (D : ℕ) : ℕ := ∏ t ∈ D.primeFactors, t

abbrev PrimeIndex (D : ℕ) := {t // t ∈ D.primeFactors}

noncomputable def localAllowed (t : ℕ) [NeZero t] (n B a : ℤ) : Finset (ZMod t) :=
  Finset.univ.filter (fun x => (n : ZMod t) + B * x ≠ a)

noncomputable def crtNat {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i, Finset (ZMod (m i))) : Finset ℕ :=
  (ErdosInverseCRT.crtResidues m hcop E).image ZMod.val

noncomputable def allowedK (D : ℕ) (n B : ℤ) (a : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (radical D)).filter (fun k => ∀ t ∈ D.primeFactors,
    ((n + B * k : ℤ) : ZMod t) ≠ a t)

end ErdosUnitLifts

end

section

open scoped BigOperators
namespace ErdosUnitLifts
attribute [local instance] Classical.decEq

def actualN (D : ℕ) (A B : ℤ) (p : ℕ) : ℤ := (A + B * p) / D

noncomputable def actualClasses (D : ℕ) (A B : ℤ) (a : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (D * radical D)).filter (fun p =>
    (D : ℤ) ∣ A + B * p ∧ ∀ t ∈ D.primeFactors,
      (actualN D A B p : ZMod t) ≠ a t)

noncomputable def baseResidue (D : ℕ) (A B : ℤ) : ℕ :=
  (-(A : ZMod D) * (B : ZMod D)⁻¹).val

end ErdosUnitLifts

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FrozenPrimeGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FrozenPrimeGroup
open _root_.Finset FiniteFirstTag ActualSourceTags ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

noncomputable def frozenGroup (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ) :
    Finset (List ℕ) := ((primeBin R xi).filter (aligns a q)).image (fun p => pre++p::tail)

end NumberTheoryLean.FrozenPrimeGroup

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagSmallPrimeData
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace ErdosStoppedTagSieve
open ErdosUnitLifts
attribute [local instance] Classical.propDecidable

noncomputable def smallPrimeSet (P : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊P⌋₊).filter (fun t => (t:ℝ)<P)

noncomputable def unalignedPrimes (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) : Finset ℕ :=
  (smallPrimeSet P).filter (fun t => ¬t∣D ∧ (D:ZMod t)*(residue t)-A≠0)
noncomputable def restrictedPrimes (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) : Finset ℕ :=
  (unalignedPrimes P D A residue).filter (fun t => ¬t∣d0)
noncomputable def forbiddenClass (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (t : ℕ) : ZMod t :=
  (B:ZMod t)⁻¹*((D:ZMod t)*(residue t)-A)

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_TagCRTPeriodicity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
attribute [local instance] Classical.decEq

abbrev IntersectionIndex (T : Finset ℕ) := {t // t∈T}
def intersectionModuli (Q : ℕ) (T : Finset ℕ) : Option (IntersectionIndex T) → ℕ
  | none => Q
  | some t => t.val

lemma intersection_moduli_pairwise (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    Pairwise (fun i j => Nat.Coprime (intersectionModuli Q T i) (intersectionModuli Q T j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some t => exact hQT t.val t.property
  | some t =>
    cases j with
    | none => exact (hQT t.val t.property).symm
    | some u =>
      apply (hT t.val t.property).coprime_iff_not_dvd.mpr
      intro hd
      rcases (hT u.val u.property).eq_one_or_self_of_dvd t.val hd with he | he
      · exact (hT t.val t.property).ne_one he
      · exact hij (congrArg Option.some (Subtype.ext he))

noncomputable def baseClasses (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  A.image (fun a : ℕ => (a:ZMod Q))

noncomputable def intersectionClasses (Q : ℕ) (T : Finset ℕ) (A : Finset ℕ) (rho : (t : ℕ) → ZMod t) :
    (i : Option (IntersectionIndex T)) → Finset (ZMod (intersectionModuli Q T i))
  | none => baseClasses Q A
  | some t => {rho t.val}

noncomputable def intersectionResidues (Q : ℕ) (T : Finset ℕ) (A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) : Finset ℕ :=
  ErdosUnitLifts.crtNat (intersectionModuli Q T) (intersection_moduli_pairwise Q T hT hQT)
    (intersectionClasses Q T A rho)

end ErdosStoppedTagSieve



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_TagUnitSieveLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve

open scoped BigOperators

noncomputable def primeFactor (p : ℕ) : ℝ := 1-1/((p:ℝ)-1)
noncomputable def eulerWeight (S : Finset ℕ) : ℝ := ∏ p∈S,primeFactor p

end ErdosStoppedTagSieve



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagPairBinding
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosUnitLifts
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

def actualTagGood (P : ℝ) (r : ℚ) (q : ℕ) (a : ℕ → ℕ) (p : ℕ) (m : ℤ) : Prop :=
  (r.den : ℤ) ∣ r.num+(q : ℤ)*m*p ∧
    ∀ t ∈ smallPrimeSet P,
      (actualN r.den r.num ((q : ℤ)*m) p : ZMod t) ≠ (a t : ℤ)

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeWordArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  ErdosInverseCounts ErdosInverseAlignment ErdosHypotheticalTag
  ErdosPrimeInputs.MertensStrong NumberTheoryLean

attribute [local instance] Classical.propDecidable

noncomputable def primeHypothetical (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) : ℝ :=
  if hp : p.Prime then
    (modulusCount Y small (@hypotheticalClass a r p ⟨hp.ne_zero⟩) (p*q) : ℝ)
  else 0

end ErdosStoppedArithmetic



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalKeyWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.CanonicalStopKey
open ActualSourceTags FiniteFirstTag
open SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment


structure Key (n : ℕ) where
  tag : Tag n
  pre : List ℕ
  tail : List ℕ
  deriving DecidableEq

noncomputable def stopKey {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) : Option (Key n) :=
  (sourceTag Y w Cs eta lower width label a ps).map
    (fun t => ⟨t,ps.take t.index,ps.drop (t.index+1)⟩)

end NumberTheoryLean.CanonicalStopKey



namespace NumberTheoryLean.ActualStopGroupFiber
open FinitePathGeometry SourceStopPredicate ActualSourceTags FiniteFirstTag CanonicalStopKey
open StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open FrozenPrimeGroup ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

noncomputable def key (Y : ℕ) (w top Cs eta xi : ℝ) (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (a : ℕ → ℕ) (ps : List ℕ) : Option (Key (binCount w top xi)) :=
  stopKey (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps

noncomputable def keyGroup (w top xi : ℝ) (a : ℕ → ℕ) (k : Key (binCount w top xi)) :
    Finset (List ℕ) := frozenGroup (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
      (sourceClass a) k.tag.rational k.pre k.tail

end NumberTheoryLean.ActualStopGroupFiber



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiniteWeightedChoiceBox
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FiniteWeightedChoiceBox

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}

noncomputable def points (P : ∀ i,Finset (α i)) : Finset (∀ i,α i) := Fintype.piFinset P
noncomputable def pointWeight (W : ∀ i,α i → ℝ) (f : ∀ i,α i) : ℝ := ∏ i,W i (f i)
noncomputable def boxMass (P : ∀ i,Finset (α i)) (W : ∀ i,α i → ℝ) : ℝ :=
  ∑ f ∈ points P,pointWeight W f
noncomputable def restrictedPoints (P : ∀ i,Finset (α i)) (S : Finset ι) (E : ∀ i,α i → Prop) :
    Finset (∀ i,α i) := (points P).filter (fun f => ∀ i ∈ S,E i (f i))

end NumberTheoryLean.FiniteWeightedChoiceBox


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_TwoSingletonBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.CanonicalSubsetBox
open _root_.Filter FiniteWeightedChoiceBox
open ActualBinOwners ErdosInversePrimeBin ErdosInverseAlignment ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def selectionMass {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) : ℝ :=
  ∑ f ∈ selections P mult,(selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.CanonicalSubsetBox



namespace NumberTheoryLean.SingletonBinSelection
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def eraseSelection {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) : Fin n → Finset ℕ :=
  fun k => if k=i then ∅ else f k
end NumberTheoryLean.SingletonBinSelection



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCenteredGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def sourceRootGap (a z : ℝ) : ℝ :=
  Real.log (ErdosInverseBoxHeight.sourceY z : ℝ)/Real.log (ErdosInverseBoxHeight.sourceW z)-a+2

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrderedWindowKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary

noncomputable def windowKernel (S a u c : ℝ) : ℝ :=
  ((S+a+u+2*c)^3-(S+2*a)^3)/(12*(max 1 a)*(max 1 u)*(max 1 c)^2)
noncomputable def windowMiddle (S a u : ℝ) : ℝ :=
  ∫ c : ℝ in 1..baseCutoff u,windowKernel S a u c
noncomputable def windowOuter (S a : ℝ) : ℝ :=
  ∫ u : ℝ in 1..baseCutoff a,windowMiddle S a u
noncomputable def windowMass (S b : ℝ) : ℝ :=
  ∫ a : ℝ in 1..baseCutoff b,windowOuter S a

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrderedAffineMoment
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedFirstMoment : ℕ → ℝ → ℝ
  | 0,_ => 0
  | n+1,b => ∫ x in (1:ℝ)..baseCutoff b,
      (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedAffine (m : ℝ) (n : ℕ) (S b : ℝ) : ℝ :=
  (3*S/m-2)*orderedMass n b+(3/m)*orderedFirstMoment n b

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialTailBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosOmissionTail

noncomputable def expTerm (x : ℝ) (n : ℕ) : ℝ := x^n/(n.factorial:ℝ)
noncomputable def firstExpTerm (x : ℝ) (n : ℕ) : ℝ := (n:ℝ)*expTerm x n
noncomputable def secondExpTerm (x : ℝ) (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)-1)*expTerm x n
noncomputable def weightedExpTerm (x : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)^2*expTerm x n

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_StoppedReferenceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosStoppedReferenceUpper
open _root_.Filter
open NumberTheoryLean FinitePathGeometry
open ReferenceAdmission ReferencePruning ReferenceProductsBasics ReferenceMertens
open ReferenceSourcePrimeSets
open ErdosPrimeInputs.MertensStrong

noncomputable def strictEuler (P : ℝ) : ℝ := availableProduct 0 P false

end ErdosStoppedReferenceUpper

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualPatternCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def nearFull (eta R width : ℝ) (a : ℕ → ℤ) (q : ℚ) : Prop :=
  (1-eta)*((primeBin R width).card:ℝ) ≤ (((primeBin R width).filter (aligns a q)).card:ℝ)

end ErdosTagEvent


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteBoxWordMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosSubsetWord
open ErdosCofactorChoices

attribute [local instance] Classical.decEq

noncomputable def descendingWord {ι : Type*} [Fintype ι] (f : ι → Finset ℕ) : List ℕ :=
  (selectionPrimes f).sort (· ≥ ·)

end ErdosSubsetWord



namespace ErdosSearchCount
open NumberTheoryLean FinitePathGeometry PrimeTiltGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure


noncomputable def selectedCount (P : ℕ → Bool) (ps : List ℕ) : ℕ := (ps.filter P).length
noncomputable def remainderSum (w : ℝ) (P : ℕ → Bool) (ps : List ℕ) : ℝ :=
  ((ps.filter (fun p => !(P p))).map (primeExponent w)).sum

end ErdosSearchCount



namespace ErdosSearchCount
open NumberTheoryLean PrimeBinRepresentatives ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def searchFlag {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (p : ℕ) : Bool := decide (searchBin w (lower (label p)))
noncomputable def searchCount {n : ℕ} (w : ℝ) (lower : Fin n → ℝ)
    (label : ℕ → Fin n) (ps : List ℕ) : ℕ := selectedCount (searchFlag w lower label) ps

end ErdosSearchCount



namespace ErdosSearchCount
open _root_.Filter NumberTheoryLean FinitePathGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition


noncomputable def searchConstant : ℝ := 1/(4*Real.log 3)

end ErdosSearchCount



namespace ErdosSubsetWord
open ErdosCofactorChoices ErdosSearchCount ErdosTagEvent
open NumberTheoryLean ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

noncomputable def globalBins (w top xi : ℝ) : Fin (binCount w top xi) → Finset ℕ :=
  fun b => primeBin (lower w top xi b) (width w top xi b)
noncomputable def occupiedSearch (w top xi : ℝ) (mult : Fin (binCount w top xi) → ℕ) :
    Finset (Fin (binCount w top xi)) :=
  Finset.univ.filter (fun b => searchBin w (lower w top xi b) ∧ 0 < mult b)

end ErdosSubsetWord



namespace NumberTheoryLean.FiniteBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord CanonicalSubsetBox
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

noncomputable def wordBox {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) : Finset (List ℕ) :=
  (selections P mult).image descendingWord

noncomputable def boxWords {n : ℕ} (P : Fin n → Finset ℕ) (M : Finset (Fin n → ℕ)) : Finset (List ℕ) :=
  M.biUnion (wordBox P)

end NumberTheoryLean.FiniteBoxWordMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualWordSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.ActualWordSelection
open FinitePathGeometry SourceStopPredicate
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosCofactorChoices ErdosSubsetWord

attribute [local instance] Classical.propDecidable

noncomputable def wordSelection {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ) (b : Fin n) : Finset ℕ :=
  ps.toFinset.filter (fun p => lab p=b)

noncomputable def wordMultiplicity {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ) (b : Fin n) : ℕ :=
  (wordSelection lab ps b).card

end NumberTheoryLean.ActualWordSelection


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FinitePairOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePairOccurrence
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw

variable {X : Type*} [MeasurableSpace X]

noncomputable def pairOccurrence (E : Set (X×X)) (N : ℕ) : Set (Hist X N) :=
  ⋃ j : Fin N,(fun h => adjacentPair N h j) ⁻¹' E

end NumberTheoryLean.FinitePairOccurrence


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_CrossingPrimeBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.CrossingPrimeBin
open FinitePathGeometry PrimeTiltGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open IsolatedBinGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def isolatedAlpha (theta T : ℝ) : ℝ := theta/(10*(T+1))

end NumberTheoryLean.CrossingPrimeBin


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GeometricRegularWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.NonisolatedWordOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FiniteHistoryTransport
open CrossingPrimeBin IsolatedBinGeometry
open CompletedArrivalOccurrence LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open PersistentFailureFlag

noncomputable def noIsolatedWord {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (B alpha beta : ℝ) (ps : List ℕ) : Prop :=
    ∀ p ∈ ps,¬isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p)

end NumberTheoryLean.NonisolatedWordOccurrence



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BinCutGapMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.BinCutSelections
open ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def aboveMultiplicity {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun k => if j<k then m k else 0
noncomputable def aboveSelection {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : Fin n → Finset ℕ :=
  fun k => if j<k then f k else ∅

noncomputable def belowMultiplicity {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun k => if k<j then m k else 0
noncomputable def belowSelection {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : Fin n → Finset ℕ :=
  fun k => if k<j then f k else ∅

end NumberTheoryLean.BinCutSelections



namespace NumberTheoryLean.AssembleAtBin
open ErdosCofactorChoices BinCutSelections SingletonBinSelection
attribute [local instance] Classical.propDecidable

noncomputable def assemble {n : ℕ} (anchor parent : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) : Fin n → Finset ℕ :=
  fun k => if j<k then parent k else if k=j then {u} else anchor k

end NumberTheoryLean.AssembleAtBin



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LargeGapCountErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.ActualCountErrorEdges
open ErdosInverseCounts


noncomputable def relativeCountError (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (d : ℕ) : ℝ :=
  (modulusCount Y small a d:ℝ)/(((Y:ℝ)/(d:ℝ))*V0)-1
noncomputable def wordCountError (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (ps : List ℕ) : ℝ :=
  relativeCountError Y small a V0 ps.prod

end NumberTheoryLean.ActualCountErrorEdges



namespace NumberTheoryLean.CountErrorClassification
open ActualCountErrorEdges ErdosInverseCounts

attribute [local instance] Classical.propDecidable

noncomputable def errorSum (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ) (F : Finset (List ℕ)) : ℝ :=
  ∑ ps∈F,|(modulusCount Y small a ps.prod:ℝ)-((Y:ℝ)/(ps.prod:ℝ))*V0|
end NumberTheoryLean.CountErrorClassification



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TwoPrimeObservableSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.TwoPrimeObservableSum
open ErdosCofactorChoices SingletonBinSelection

attribute [local instance] Classical.propDecidable

noncomputable def pickedPrime {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) : ℕ := (f i).toList.getLastD 0
end NumberTheoryLean.TwoPrimeObservableSum


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoundedEdgeBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FullBoxLengthBounds
open FinitePathGeometry
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition


noncomputable def parentLength (w : ℝ) (Y : ℕ) {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) : ℝ :=
  Real.log ((Y:ℝ)/(selectionProduct (aboveSelection f j):ℝ))/Real.log w
noncomputable def childLength (w : ℝ) (Y : ℕ) {n : ℕ} (f : Fin n → Finset ℕ) (j : Fin n) (u : ℕ) : ℝ :=
  Real.log ((Y:ℝ)/((selectionProduct (aboveSelection f j):ℝ)*(u:ℝ)))/Real.log w

end NumberTheoryLean.FullBoxLengthBounds



namespace NumberTheoryLean.BoundedEdgeBins
open ErdosCofactorChoices ErdosSubsetWord FullBoxLengthBounds
open FinitePathGeometry
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def boundedEdgeBin (w top xi : ℝ) (Y : ℕ)
    (m : Fin (binCount w top xi) → ℕ) (M X : ℝ) (j : Fin (binCount w top xi)) : Prop :=
  ∃ f ∈ selections (globalBins w top xi) m,∃ u : ℕ,f j={u} ∧ parentLength w Y f j ≤ M ∧ primeExponent w u ≤ X

end NumberTheoryLean.BoundedEdgeBins


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualBoxFourSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.ParentTailPartition
open ErdosCofactorChoices SingletonBinSelection TwoPrimeObservableSum
open BinCutSelections

attribute [local instance] Classical.propDecidable

noncomputable def parentCofactorSelection {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) : Fin n → Finset ℕ :=
  eraseSelection (aboveSelection f j) i

end NumberTheoryLean.ParentTailPartition



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FullWordHighAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.HardTagBoxMass
open ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels PrimeBinRepresentatives
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseAlignment
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def hardBadSelections {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (Fin (binCount w top xi) → Finset ℕ) :=
  (selections (globalBins w top xi) mult).filter (fun f =>
    (∀ p ∈ descendingWord f,Cs < primeExponent w p → aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q)

noncomputable def hardBadMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : ℝ :=
  ∑ f ∈ hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,(selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.HardTagBoxMass



namespace NumberTheoryLean.HardTagWordFamily
open HardTagBoxMass FiniteBoxWordMass ErdosCofactorChoices ErdosSubsetWord
open LogarithmicBinScale LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

noncomputable def hardBadWords {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (List ℕ) :=
  (hardBadSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q).image descendingWord

noncomputable def hardWordFamily {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (M : Finset (Fin (binCount w top xi) → ℕ)) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (a : ℕ → ℤ) : Finset (List ℕ) :=
  M.biUnion (fun mult => (Q mult).biUnion (fun q => hardBadWords (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q))

end NumberTheoryLean.HardTagWordFamily



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_PaperGeometricRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.ExpandedCompactPartition
open FinitePathGeometry SourceStopPredicate ActualWordSelection
open StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open CountErrorClassification
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def listedWord {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Cs : ℝ) (a : ℕ → ℕ)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (ps : List ℕ) : Prop :=
  ∃ q∈Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
    ∀ p∈ps,Cs < primeExponent w p → aligns (sourceClass a) q p

end NumberTheoryLean.ExpandedCompactPartition



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_BoxWitnessFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.BoxWitnessFactorization
open ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling
open TwoPrimeObservableSum ParentTailPartition BinCutSelections CanonicalSubsetBox

attribute [local instance] Classical.propDecidable

noncomputable def selectionWitnessMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (W : (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ f ∈ (selections P m).filter (fun f => W (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)),
    (selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.BoxWitnessFactorization


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CandidateExceptionMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.MultiplicitySuffixRank
open BinCutSelections

attribute [local instance] Classical.propDecidable

noncomputable def lowerIndices {n : ℕ} (j : Fin n) : Finset (Fin n) := Finset.univ.filter (fun k => k<j)
noncomputable def suffixRank {n : ℕ} (m : Fin n → ℕ) (j : Fin n) : ℕ := 1+∑ k ∈ lowerIndices j,m k

end NumberTheoryLean.MultiplicitySuffixRank



namespace NumberTheoryLean.BoundedCandidateCount
open FinitePathGeometry
open BoundedEdgeBins MultiplicitySuffixRank
open LogarithmicBinScale LogarithmicBinLabels

attribute [local instance] Classical.propDecidable

noncomputable def candidateBins (w top xi : ℝ) (Y : ℕ) (m : Fin (binCount w top xi) → ℕ) (M X : ℝ) :
    Finset (Fin (binCount w top xi)) := Finset.univ.filter (boundedEdgeBin w top xi Y m M X)

end NumberTheoryLean.BoundedCandidateCount



namespace NumberTheoryLean.CandidateExceptionMass
open ErdosCofactorChoices BoxWitnessFactorization CanonicalSubsetBox TwoPrimeObservableSum ParentTailPartition

attribute [local instance] Classical.propDecidable

noncomputable def someWitnessMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (J : Finset (Fin n)) (W : Fin n → (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ f ∈ (selections P m).filter (fun f => ∃ j∈J,W j (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)),
    (selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.CandidateExceptionMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ConditionalPatternCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosLargePatternLaw
open ErdosVarianceSmallModel

attribute [local instance] Classical.propDecidable

abbrev FullPattern (w : ℝ) (H : ℕ) :=
  (ZMod (divisorModulus w H))ˣ × ZMod (divisorModulus w H) ×
    (ZMod (coprimeModulus w H))ˣ × ZMod (coprimeModulus w H)

noncomputable def weight (w : ℝ) (H : ℕ) : ℝ :=
  1/(((divisorModulus w H).totient : ℝ)*(divisorModulus w H : ℝ)*
    ((coprimeModulus w H).totient : ℝ)*(coprimeModulus w H : ℝ))

noncomputable def expectation (w : ℝ) (H : ℕ) (F : FullPattern w H → ℝ) : ℝ :=
  ∑ v,weight w H*F v

def survives (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : Prop :=
  (∀ t ∈ divisorPrimes w H,(v.2.1.val : ZMod t)+(v.1.val.val : ZMod t)*(j : ZMod t) ≠ beta t) ∧
  (∀ t ∈ coprimePrimes w H,(v.2.2.1.val.val : ZMod t)*(qA : ZMod t)*
    ((v.2.2.2.val : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t)

def jointCondition (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (v : FullPattern w H) : Prop := ∀ j ∈ S,survives w H qA beta delta j v

noncomputable def indicator (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : ℝ := if survives w H qA beta delta j v then 1 else 0

noncomputable def survivorCount (w : ℝ) (H qA J : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (v : FullPattern w H) : ℕ := ((Finset.range J).filter (fun j => survives w H qA beta delta j v)).card

end ErdosLargePatternLaw



namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def projectedUnit (M t : ℕ) [NeZero M] (ht : t ∣ M) (p : (ZMod M)ˣ) : (ZMod t)ˣ :=
  Units.map (ZMod.castHom ht (ZMod t)).toMonoidHom p

def divisorCondition (w : ℝ) (H : ℕ) (beta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p0 : (ZMod (divisorModulus w H))ˣ) (k0 : ZMod (divisorModulus w H)) : Prop :=
  ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k0.val : ZMod t)+(p0.val.val : ZMod t)*(j : ZMod t) ≠ beta t

def coprimeCondition (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p1 : (ZMod (coprimeModulus w H))ˣ) (m1 : ZMod (coprimeModulus w H)) : Prop :=
  ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(p1.val.val : ZMod t)*(qA : ZMod t)*
    ((m1.val : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t

end ErdosLargePatternLaw


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FullEndpointData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceEffective
open ErdosInverseCells

noncomputable def effectiveSize (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R : ℝ) : ℝ :=
  max (effectiveModulus a r qf : ℝ) (|(effectiveIntercept a r qf : ℝ)|/R)

end ErdosVarianceEffective



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_SourcePairSieve
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def siftedSourcePairs (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ)
    (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) (P : Finset ℕ) : Finset (ℤ × ℤ) :=
  (sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ).filter
    (fun pm => ∀ t ∈ P,¬(t : ℤ) ∣ pm.1)

end ErdosVarianceLargeCount


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PatternMainTerm
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def patternCard (T0 T1 : ℕ) : ℕ := T0*T0.totient*T1*T1.totient

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FullPatternCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

noncomputable def actualFullPattern (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) : ErdosLargePatternLaw.FullPattern w H :=
  (ZMod.unitOfCoprime p.val ((Finset.mem_filter.mp p.property).2.symm.of_dvd_right (divisorModulus_dvd_H w H)),
    (primeK P H C0 hP p : ZMod (divisorModulus w H)),
    (primePoint P w H C0 hw hP hlarge p).2.1,
    (primeM P H C0 hP p : ZMod (coprimeModulus w H)))

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_OriginalPairSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def largeSieveLevel : ℝ := 480024
noncomputable def largeSieveExponent : ℝ := 1/(10*largeSieveLevel)
noncomputable def largeSieveCutoff (R : ℝ) : ℝ := R^largeSieveExponent

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceLargePairBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosVarianceSmallModel

noncomputable def slowHyperbolaFactor (N T0 : ℕ) : ℝ :=
  completionConstant*(N.divisors.card : ℝ)^3*(Real.log (2*(N : ℝ)))^2*Real.sqrt T0

end ErdosVarianceLargeScale

end


open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StableFiniteVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
open scoped BigOperators

noncomputable def weightedMoment {α : Type*} (C : Finset α) (w f : α → ℝ) : ℝ :=
  ∑ x ∈ C, w x * f x

noncomputable def indicatorSum {ι α : Type*} (J : Finset ι) (I : ι → α → ℝ) (x : α) : ℝ :=
  ∑ j ∈ J, I j x

end ErdosRandomVariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StableSourceVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosRandomVariance

noncomputable def variancePrimes (w : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊w⌋₊).filter Nat.Prime

end ErdosRandomVariance

end


open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformJointModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
namespace ErdosUniformMobiusRemainder

def cutoffExponent (M : ℝ) : ℝ := 2*M+12

end ErdosUniformMobiusRemainder

end



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EligibleBoxLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.EligibleBoxLists
open ActualBinOwners LogarithmicBinScale

attribute [local instance] Classical.propDecidable

noncomputable def eligibleLists {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (m : Fin n → ℕ) : Finset ℚ :=
  if m∈M then (Q m).filter (eligible Y w Cs) else ∅

end NumberTheoryLean.EligibleBoxLists


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceBlockFibreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosHyperbolaError
  ErdosLargeHeightBlocks ErdosInversePrimeBin ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def blockPatternPrimes (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ primeBin R theta,p.Prime)
    (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H) :
    Finset (goodPrimes (primeBin R theta) H) :=
  Finset.univ.filter (fun p => p.val ∈ blockPrimes C0 R theta H i ∧
    actualFullPattern (primeBin R theta) w H C0 hw hP hlarge p = v)

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FullPrimeEventFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosLargeHeightBlocks ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def actualBlockIndex (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (p : goodPrimes (primeBin R theta) H) :
    Fin (blockCount C0 R theta H) :=
  Classical.choose (unique_original_prime_block C0 R theta H p.val hR htheta
    (Finset.mem_filter.mp p.property).1).exists

noncomputable def indexedFullPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => E (actualFullPattern P w H C0 hw hP hlarge p))

noncomputable def fullPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ErdosLargePatternLaw.FullPattern w H → Prop) : Finset ℕ :=
  (indexedFullPrimeEvent P w H C0 hw hP hlarge E).image Subtype.val

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceFullEventCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosVarianceLargeCount
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def patternEventWeight (w : ℝ) (H : ℕ) (E : ErdosLargePatternLaw.FullPattern w H → Prop) : ℝ :=
  ∑ _v ∈ Finset.univ.filter E,ErdosLargePatternLaw.weight w H

end ErdosVarianceLargeMap



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_GuardedHardPrimeSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def modelBadEvent (J : ℕ) (w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (eta : ℝ) (v : ModelPoint w H) : Prop :=
  eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |indicatorSum (Finset.range J) (modelIndicator w H C0 qA beta delta) v-
      (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|

end ErdosVarianceUniformMoments

end



namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseCounts ErdosInverseAlignment ErdosVarianceCommon
attribute [local instance] Classical.propDecidable

noncomputable def badAligningPrimes (P : Finset ℕ) (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (r : ℚ) (qf : ℕ) (eps : ℝ) : Finset ℕ :=
  P.filter (fun p => aligns (fun t => (a t : ℤ)) r p ∧
    eps < |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*qf) : ℝ)/
      referenceCount Y w p qf-1|)

end ErdosVarianceSmallPrime



namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosVarianceMoments ErdosVarianceLargeMap
attribute [local instance] Classical.propDecidable

noncomputable def fullPatternBadEvent (J : ℕ) (w : ℝ) (H qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (eta : ℝ) (v : ErdosLargePatternLaw.FullPattern w H) : Prop :=
  eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(ErdosLargePatternLaw.survivorCount w H qA J beta delta v : ℝ)-
      (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|

end ErdosVarianceLargePrime


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def hardCandidate (z R : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs : ℝ) : Prop :=
  (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 ∧
  effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 ∧
  (sourceW z)^Cs ≤ effectiveSize a r qf R

noncomputable def guardedHardPrimes (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs eps : ℝ) : Finset ℕ :=
  if hardCandidate z R a r qf Cs then
    badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps else ∅

noncomputable def rawHardPrimeUnion (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) : Finset ℕ :=
  Q.biUnion (fun r => guardedHardPrimes z R theta a r qf Cs eps)

end ErdosVarianceWeighted


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GeometricSelectionHardMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices SingletonBinSelection TwoPrimeObservableSum
attribute [local instance] Classical.propDecidable

def hardSelection {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (i : Fin n) (Cs eps : ℝ) (f : Fin n → Finset ℕ) : Prop :=
  pickedPrime f i ∈ rawHardPrimeUnion Q z R theta a (selectionProduct (eraseSelection f i)) Cs eps

end ErdosVarianceWeighted


open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_OutsideExceptionsWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FilteredBoxWordMass
open ErdosCofactorChoices ErdosSubsetWord FiniteBoxWordMass
open ErdosPrimeInputs.PrimePrefixMass
open ExpandedCompactPartition ActualWordSelection
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def selectedWordMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (F : Finset (List ℕ)) : ℝ :=
  ∑ f∈(selections P m).filter (fun f => descendingWord f∈F),(selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.FilteredBoxWordMass



namespace ErdosVarianceEligible
open NumberTheoryLean ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
  ActualBinOwners SourceStopPredicate ActualCountErrorEdges
  ErdosVarianceSmallPrime ErdosVarianceCommon ErdosInverseAlignment
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def eligibleWordWitness (Y : ℕ) (w Cs : ℝ) (residue : ℕ → ℕ) (Q : Finset ℚ) (ps : List ℕ) : Prop :=
  ∃ r ∈ Q,eligible (Y : ℝ) w Cs r ∧
    ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass residue) r p

end ErdosVarianceEligible



open _root_.Filter


end Erdos970

end OAI
end



-- Prove2me | Definitions.Def_OAIQ247J007
-- name    : OAIQ247J007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:40.010132+00:00
-- url     : https://prove2.me/theorems/525b86ec-3983-472d-ad91-dfa7608498ef
-- title:
--   Definitions bundle OAIQ247J007 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 697 declarations of OpenAI's Lean: 415 definitions, 4 inductive types or structures, 50 instances and 228 theorems. The definitions and types are `Erdos970.RectangleIntegral'`, `Erdos970.SmoothedChebyshev`, `OAI.Erdos970.Erdos970Dependency.IncomingDensityIdentities.incomingEven`, `OAI.Erdos970.Erdos970Dependency.IncomingDensityIdentities.incomingOdd`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.initialIncoming`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.initialTwoDensity`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.regThreeIncoming`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.regTwoIncoming`, `OAI.Erdos970.Erdos970Dependency.InvariantCostBound.costMass`, `OAI.Erdos970.Erdos970Dependency.InvariantCostBound.evenCost`, `OAI.Erdos970.Erdos970Dependency.InvariantCostBound.oddCost`, `OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure`, `OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.regThreeMeasure`, `OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.regTwoMeasure`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.FiniteRawHistory`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.FirstPairWitness`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.MarkedOddCost`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.RawCycleWordTrace`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.RawHistory`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.anyPairHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.boundedPairCylinder`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalEvenPairVisitKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.closedNoHitEvent`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveMarkedHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.continueMarkUpdate`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.finiteRawLast`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstArrivalMark`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstPairHitEvent`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstPairProjection`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstPrefixMarkEvent`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.historyGoodInput`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.increasingCosts` and 379 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_Fourier`, `Erdos970_MellinCalculus`, `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Erdos970_ResidueCalcOnRectangles`, `Erdos970_SmoothExistence`, `Erdos970_ZetaBounds`, `Jacobsthal_Analysis_ActualLossDensity`, `Jacobsthal_Analysis_ContinuousCorrectionLimit`, `Jacobsthal_Analysis_ContinuousReference`, `Jacobsthal_Analysis_CorrectedCompactTransfer`, `Jacobsthal_Analysis_CorrectionWeightedIntegral`, `Jacobsthal_Analysis_DensityComparison`, `Jacobsthal_Analysis_DensityConservation`, `Jacobsthal_Analysis_RealCoefficientNormalization`, `Jacobsthal_Analysis_RetainedNormalizedReward`, `Jacobsthal_Analysis_TerminalForceIntegral`, `Jacobsthal_Analysis_WeightIntegrals`, `Jacobsthal_Estimates_BoundaryGateSets`, `Jacobsthal_Estimates_BoundaryRadialCoefficient`, `Jacobsthal_Estimates_BoundaryReferenceConvergence`, `Jacobsthal_Estimates_CanonicalPairCylinders`, `Jacobsthal_Estimates_ConsecutivePowerProjection`, `Jacobsthal_Estimates_CorrectionEnvelope`, `Jacobsthal_Estimates_CorrectionFloorRemainder`, `Jacobsthal_Estimates_CorrectionStateSections`, `Jacobsthal_Estimates_DivisibleInflection`, `Jacobsthal_Estimates_EvenInverseBands`, `Jacobsthal_Estimates_GateIterates`, `Jacobsthal_Estimates_HypotheticalSubbinLower`, `Jacobsthal_Estimates_InitialOddDraw`, `Jacobsthal_Estimates_InverseWeightGrowth`, `Jacobsthal_Estimates_LowStateHorizon`, `Jacobsthal_Estimates_MarginalProfiles`, `Jacobsthal_Estimates_OmissionSeries`, `Jacobsthal_Estimates_OnePairCost`, `Jacobsthal_Estimates_PairTraceBridge`, `Jacobsthal_Estimates_PairedCostGrouping`, `Jacobsthal_Estimates_RawSuppliedPast`, `Jacobsthal_Estimates_RealCriticalPoints`, `Jacobsthal_Estimates_ReferenceCutoffRecurrence`, `Jacobsthal_Estimates_ReferenceLocalResidual`, `Jacobsthal_Estimates_ReferenceProductsBasics`, `Jacobsthal_Estimates_ReferenceSourceDecomposition`, `Jacobsthal_Estimates_ReferenceWeightedQuadrature`, `Jacobsthal_Estimates_RepeatedStepRowBound`, `Jacobsthal_Estimates_RichLinearFactor`, `Jacobsthal_Estimates_RieszTermCalculus`, `Jacobsthal_Estimates_ScalarFreeGate`, `Jacobsthal_Estimates_ScalarTailRecurrence`, `Jacobsthal_Estimates_ScaledOriginalTail`, `Jacobsthal_Estimates_SignedCompletedPowers`, `Jacobsthal_Estimates_SourceLowRemoval`, `Jacobsthal_Estimates_SourceParentBenchmark`, `Jacobsthal_Estimates_SquarefreeHarmonic`, `Jacobsthal_Estimates_StandardBoundaryCoefficient`, `Jacobsthal_Estimates_TwoSidedThresholdHazard`, `Jacobsthal_Estimates_TwoSidedThresholdOccurrence`, `Jacobsthal_Harmonic_CompactAnomalyTest`, `Jacobsthal_Harmonic_ComplexSquareScaling`, `Jacobsthal_Harmonic_PolynomialLocalGraph`, `Jacobsthal_Harmonic_WeightedAnomalyConvergence`, `Jacobsthal_Partitions_BandShiftTransport`, `Jacobsthal_Partitions_CompactTestGeometry`, `Jacobsthal_Partitions_CompletedParentInterval`, `Jacobsthal_Partitions_ContinuousHighPartition`, `Jacobsthal_Partitions_FiberCardinalityConstancy`, `Jacobsthal_Partitions_NestedCoordinates`, `Jacobsthal_Partitions_OmissionPartition`, `Jacobsthal_Partitions_ReferenceHighIntervals`, `Jacobsthal_Partitions_ReferenceIntervalBound`, `Jacobsthal_Partitions_RetainedIntervalUpper`, `Jacobsthal_Partitions_RieszRectangle`, `Jacobsthal_Partitions_SourceParentBin`, `Jacobsthal_Partitions_TwoSidedThresholdGeometry`, `Jacobsthal_Paths_ActualTagFreezing`, `Jacobsthal_Paths_ActualThresholdArrival`, `Jacobsthal_Paths_AdmittedHarmonicPaths`, `Jacobsthal_Paths_CanonicalHighRatioVisit`, `Jacobsthal_Paths_CanonicalUniformMissingVisit`, `Jacobsthal_Paths_ConsecutivePairStop`, `Jacobsthal_Paths_ContinuousArrivalSupport`, `Jacobsthal_Paths_CostPrefixTransport`, `Jacobsthal_Paths_FiniteHistorySupport`, `Jacobsthal_Paths_FiniteVisitMass`, `Jacobsthal_Paths_FlaggedHarmonicTransform`, `Jacobsthal_Paths_FlaggedSourceStart`, `Jacobsthal_Paths_FullWordHighAlignment`, `Jacobsthal_Paths_GeometricRegularWords`, `Jacobsthal_Paths_GlobalFiniteBranches`, `Jacobsthal_Paths_HistoryRestrictionAlgebra`, `Jacobsthal_Paths_PairBranchFullProjection`, `Jacobsthal_Paths_PairCaptureProjection`, `Jacobsthal_Paths_PairedHitting`, `Jacobsthal_Paths_PrefixCompletions`, `Jacobsthal_Paths_RawBoxRationalWitness`, `Jacobsthal_Paths_RawIncreasingPrefix`, `Jacobsthal_Paths_RawWordSpaces`, `Jacobsthal_Paths_ReferencePrefixRecurrence`, `Jacobsthal_Paths_TagAffineConditions`, `Jacobsthal_Paths_TwoSidedThresholdArrival`, `Jacobsthal_Paths_WrongOwnerBoxMass`, `Jacobsthal_Primes_BoundaryPrimeMass`, `Jacobsthal_Primes_HighPrimeRemoval`, `Jacobsthal_Primes_IntervalPrimesDefinition`, `Jacobsthal_Primes_PrimeCompactWeights`, `Jacobsthal_Primes_PrimeDensityBlocks`, `Jacobsthal_Primes_PrimeGridGeometry`, `Jacobsthal_Primes_PrimeMarginalRecursion`, `Jacobsthal_Primes_PrimeOccupationDensity`, `Jacobsthal_Primes_PrimeRatioBins`, `Jacobsthal_Primes_PrimeTailSplit`, `Jacobsthal_Primes_ReferenceSourcePrimeSets`, `Jacobsthal_Primes_TagPrimePartition`, `Jacobsthal_Primes_WeightedPrimeMultiplePairs`, `Jacobsthal_Probability_ActualCouplingUpdates`, `Jacobsthal_Probability_ArrivalKernelGeometry`, `Jacobsthal_Probability_CanonicalPairHitEvents`, `Jacobsthal_Probability_CanonicalPairVisitLaw`, `Jacobsthal_Probability_CompletedMarkEvents`, `Jacobsthal_Probability_CouplingLabelEvents`, `Jacobsthal_Probability_FirstHitKernels`, `Jacobsthal_Probability_HorizontalBoundaryMarks`, `Jacobsthal_Probability_MarkedCostSublaws`, `Jacobsthal_Probability_MarkedVisitGeometry`, `Jacobsthal_Probability_OrdinaryMarkedWindow`, `Jacobsthal_Probability_PairedDrift`, `Jacobsthal_Probability_RawFirstPrefixLaw`, `Jacobsthal_Probability_RealExceptionalMarks`, `Jacobsthal_Probability_RepeatedWordEvents`, `Jacobsthal_Probability_SecondLossKernel`, `Jacobsthal_Probability_StateKernelInvariance`, `Jacobsthal_Probability_SubMarkovFlagPowers`, `Jacobsthal_Probability_ThirdInnerKernel`, `Jacobsthal_Probability_TransitionKernels`, `Jacobsthal_Probability_TwoSidedThresholdKernel`, `Jacobsthal_Renewal_ContinuousCompletedOccupation`, `Jacobsthal_Renewal_FiniteAdmittedOccupation`, `Jacobsthal_Renewal_MarkedCycleCompletion`, `Jacobsthal_Renewal_OccupationAge`, `Jacobsthal_Renewal_OccupationDensityIntegral`, `Jacobsthal_Renewal_OddPairCycleGrouping`, `Jacobsthal_Renewal_RegenerationBandBounds`, `Jacobsthal_Renewal_RegenerationDrift`, `Jacobsthal_Renewal_RegenerativeOddOccupation`, `Jacobsthal_Renewal_RetainedOccupationLimit`, `Jacobsthal_Renewal_SourceCycleDuration`, `Jacobsthal_Renewal_UniformCycleMoments`, `Jacobsthal_Siegel_ConductorCompletedL`, `Jacobsthal_Siegel_DerivationJet`, `Jacobsthal_Siegel_HilbertSeries`, `Jacobsthal_Siegel_HomogeneousDeformation`, `Jacobsthal_Siegel_PolynomialLinearCoefficients`, `Jacobsthal_Siegel_RectangleThreshold`, `Jacobsthal_Sieve_AlignedPrimeCongruence`, `Jacobsthal_Sieve_CofactorAllChoiceBounds`, `Jacobsthal_Sieve_CompactExponentialMoments`, `Jacobsthal_Sieve_IntegerResidueVariance`, `Jacobsthal_Sieve_IntegerRichLine`, `Jacobsthal_Sieve_MarkedCycleFactorization`, `Jacobsthal_Sieve_TagUnitSieveLower`.
--
--   **Imports.** It imports the bundles `OAIQ247J000`, `OAIQ247J001`, `OAIQ247J002`, `OAIQ247J003`, `OAIQ247J004` and `OAIQ247J005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ247J008`, `OAIQ247J009`, `OAIQ247J011` and `OAIQ247J012`; the statements `OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247`, `OAI_Erdos970_Erdos970Dependency_MarkedVisits_moving_marked_window_capture_jb247`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_first_loss_eq_one_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_loss_summable_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_signed_loss_series_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.compact_limiting_integral_tendsto_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.fullWeighted_section_radial_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247`, `OAI.Erdos970.ErdosOmissionBindings.actual_first_three_partial_sum_lt_jb247`, `OAI_Erdos970_ErdosOmissionBindings_actual_third_loss_eq_L3_jb247`, `OAI.Erdos970.ErdosOmissionBindings.second_loss_bounded_jb247`, `OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_omission_tail_lt_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integrable_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integral_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.actual_reference_limit_positive_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_hypothetical_subbin_lower_jb247`, `OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247`, `OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247`, `OAI_Erdos970_ErdosVarianceLargeCount_source_pair_remainder_bound_jb247`, `OAI_Erdos970_ErdosVarianceSmallPrime_source_small_H_bad_prime_fraction_jb247`, `OAI.Erdos970.NumberTheoryLean.ContinuousLowOccupationLimit.source_continuous_low_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.ContinuousOccupationIdentification.full_admitted_eq_response_jb247`, `OAI.Erdos970.NumberTheoryLean.IteratedLogBound.of_source_root_lower_jb247`, `OAI.Erdos970.NumberTheoryLean.RegenerationBandBounds.regeneration_uniform_band_jb247` and `OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247`; the proofs of `OAI.Erdos970.ErdosContinuousOmission.actual_first_loss_eq_one_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_loss_summable_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_signed_loss_series_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.compact_limiting_integral_tendsto_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.fullWeighted_section_radial_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247`, `OAI.Erdos970.ErdosInverseFrozen.frozen_exceptional_mean_jb247`, `OAI.Erdos970.ErdosInverseRefinement.source_parentSlope_mem_jb247`, `OAI.Erdos970.ErdosOmissionBindings.actual_first_three_partial_sum_lt_jb247`, `OAI.Erdos970.ErdosOmissionBindings.second_loss_bounded_jb247`, `OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integrable_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integral_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.actual_reference_limit_positive_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_hypothetical_subbin_lower_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247`, `OAI.Erdos970.ErdosVarianceCommon.source_actual_bad_to_common_jb247`, `OAI_Erdos970_ErdosVarianceLargeCount_source_pair_remainder_bound_jb247`, `OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247`, `OAI.Erdos970.ErdosVarianceMoments.finite_joint_moment_estimate_jb247`, `OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247`, `OAI.Erdos970.WeightedTorusJets.actual_biquadratic_rectangle_span_jb247`, `OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247` and `OAI.Erdos970.WeightedTorusJets.source_given_determinant_finite_lower_of_real_zero_jb247`.
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
import Definitions.Def_OAIQ247J000
import Definitions.Def_OAIQ247J001
import Definitions.Def_OAIQ247J002
import Definitions.Def_OAIQ247J003
import Definitions.Def_OAIQ247J004
import Definitions.Def_OAIQ247J005

section
-- module Solutions.OAIQ247_JB.Erdos970_Fourier
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace Erdos970

open FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance instCoeForallRealForallComplex_solutions_r195863_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_MellinCalculus
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open scoped ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory
  _root_.Set _root_.Function

open Erdos970.Complex Erdos970.MeasureTheory

variable {𝕂 : Type*} [RCLike 𝕂]

open Erdos970.Filter

local notation "𝓜" => mellin

lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ
      (fun (ε : ℝ) ↦ 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [Erdos970.Function.support_ofReal (f := ν)]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [Erdos970.Function.support_ofReal (f := ν)]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert! (preTransparency := .instances) this using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  funext ε
  congr 1
  symm
  calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
      = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast <;> ring)
    _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [mass_one, ofReal_one]

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos : 0 < ε) :
    x < 2 ^ (-ε) := by
  calc
    x ≤ 1 - Real.log 2 * ε := hx
    _ < 2 ^ (-ε) := ?_
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos

lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  set c := Real.log 2; use c
  refine ⟨_root_.Real.log_pos (by norm_num), rfl, ?_⟩
  intro ε x εpos xpos hx
  have hx2 := Smooth1Properties_below_aux hx εpos
  rewrite [← DeltaSpikeMass mass_one εpos]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        indicator (Ioc 0 1) (fun y ↦ DeltaSpike ν ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike ν ε (x / y) / y := ?_
    _ = _ := integral_comp_div_I0i_haar (fun y ↦ DeltaSpike ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have : y ≠ 0 := by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff, this, or_false]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    apply DeltaSpikeSupport εpos ?_ suppν
    · simp only [mem_Icc, not_and, not_le]; intro
      linarith [(by apply (div_lt_iff₀ (by linarith)).mpr; nlinarith : x / y < 2 ^ (-ε))]
    · rw [le_div_iff₀ (by linarith), zero_mul]; exact xpos.le

lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε

lemma Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT3_RiemannZeta
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open scoped BigOperators Topology

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

lemma lem_zfroms_calc (s : ℂ) (t : ℝ) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re = s.re + (3/2 : ℝ) ∧ z.im = s.im + t) := by
  constructor
  ·                           
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
                                                                       
    have h1 : I.re = 0 := Complex.I_re
    have h2 : I.im * 0 = 0 := mul_zero _
    rw [h1, h2]
    simp
  ·                   
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
                                                                   
    have h1 : I.re * 0 = 0 := mul_zero _
    have h2 : I.im = 1 := Complex.I_im
    rw [h1, h2]
    simp

lemma lem_zfroms_conditions (s : ℂ) (t : ℝ)
    (hs : ‖s‖ ≤ (1 : ℝ)) (ht : (2 : ℝ) < |t|) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im|) := by
                                                        
  have h_calc := lem_zfroms_calc s t
  simp only [h_calc.1, h_calc.2]
  constructor

  ·                                                   
                                                                
    have hs_re_bound : |s.re| ≤ 1 :=
      (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at hs_re_bound

    rw [Set.mem_Ico]
    constructor
    ·                                     
      linarith [hs_re_bound.1]
    ·                                    
      linarith [hs_re_bound.2]

  ·                                            
    have hs_im_bound : |s.im| ≤ 1 :=
      (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at hs_im_bound

    by_cases h : 0 ≤ t
    ·                                        
      have ht_pos : t > 2 := by
        rwa [abs_of_nonneg h] at ht
                                       
      have lower_bound : s.im + t ≥ 1 := by
        linarith [hs_im_bound.1, ht_pos]
      have nonneg : 0 ≤ s.im + t := by linarith
      rw [abs_of_nonneg nonneg]
      linarith [lower_bound]
    ·                                                     
      push Not at h
      have ht_neg : t < -2 := by
        rw [abs_of_neg h] at ht
        linarith [ht]
                                                                 
      have upper_bound : s.im + t ≤ -1 := by
        linarith [hs_im_bound.2, ht_neg]
      have neg : s.im + t < 0 := by linarith
      rw [abs_of_neg neg]
      linarith [upper_bound]

lemma lem_zetaUppBound :
    ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ (1 : ℝ) → (2 : ℝ) < |t| →
      ‖riemannZeta (s + (3/2 : ℝ) + I * t)‖ < (10 : ℝ) + 2 * |t| := by
  intro t s hs ht
  set z := s + (3/2 : ℝ) + I * t with hz_def
                                                       
  have hz_cond : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| :=
    lem_zfroms_conditions s t hs ht
                        
  have h_bound : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| :=
    lem_zetaUppBd z hz_cond.1 hz_cond.2
                                         
  have hz_im_calc : z.im = s.im + t := (lem_zfroms_calc s t).2
  have h_im_bound : |z.im| ≤ 1 + |t| := by
    rw [hz_im_calc]
    exact lem_abs_im_bound s t hs
                   
  have h_intermediate : ‖riemannZeta z‖ < (8 : ℝ) + 2 * (1 + |t|) := by
    calc ‖riemannZeta z‖
      < (8 : ℝ) + 2 * |z.im| := h_bound
      _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by linarith [h_im_bound]
                           
  have h_algebra : (8 : ℝ) + 2 * (1 + |t|) = (10 : ℝ) + 2 * |t| := by ring
                
  have h_final : ‖riemannZeta z‖ < (10 : ℝ) + 2 * |t| := by
    linarith [h_intermediate, h_algebra]
                                                
  rwa [hz_def] at h_final

open Metric _root_.Set _root_.Filter _root_.Asymptotics BigOperators

lemma zeta32upper_pre : ∃ b > 1, ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → (2 : ℝ) < |t| → ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < b * |t| := by
  refine ⟨(12 : ℝ), by norm_num, ?_⟩
  intro t s hs ht
  have hlt : ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < (10 : ℝ) + 2 * |t| := by
    simpa using! (lem_zetaUppBound t s hs ht)
  have honele : (1 : ℝ) ≤ |t| := by
    have : (1 : ℝ) < |t| := lt_trans (by norm_num) ht
    exact le_of_lt this
  have h10le : (10 : ℝ) ≤ 10 * |t| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right honele (by norm_num : (0 : ℝ) ≤ (10 : ℝ)))
  have hle2 : (10 : ℝ) + 2 * |t| ≤ (12 : ℝ) * |t| := by
    have htmp := add_le_add_left h10le (2 * |t|)
    have hcalc : 10 * |t| + 2 * |t| = (12 : ℝ) * |t| := by ring
    simpa [hcalc] using! htmp
  exact lt_of_lt_of_le hlt hle2

lemma zeta32upper : ∃ b > 1, ∀ t : ℝ, |t| > 2 →
  let c := (3/2 : ℂ) + I * t
  ∀ s ∈ closedBall c 1, ‖riemannZeta s‖ < b * |t| := by
                                         
  obtain ⟨b, hb_gt, hbound⟩ := zeta32upper_pre
  refine ⟨b, hb_gt, ?_⟩
  intro t ht c s hs
                                         
  rw [mem_closedBall] at hs
                                         
  set s_pre := s - c with hs_pre_def
  have hs_pre_bound : ‖s_pre‖ ≤ 1 := by
    rw [hs_pre_def]
    rwa [Complex.dist_eq] at hs
                                            
  have hs_eq : s = s_pre + 3/2 + I * t := by
    rw [hs_pre_def]
    ring
                          
  rw [hs_eq]
  exact hbound t s_pre hs_pre_bound ht

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ResidueCalcOnRectangles
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open _root_.Complex BigOperators _root_.Nat Classical _root_.Real Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * _root_.Complex.I)) • RectangleIntegral f z w

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * _root_.Complex.I))) :
    VerticalIntegral f σ =
      _root_.Complex.I • (∫ t in Iic a, f (σ + t * _root_.Complex.I)) + VIntegral f σ a b +
      _root_.Complex.I • ∫ t in Ici b, f (σ + t * _root_.Complex.I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + _root_.Complex.I • ?_ - _root_.Complex.I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, sub_neg_eq_add, smul_neg, sub_neg_eq_add,
    ← sub_eq_add_neg, neg_add_eq_sub, sub_add_eq_add_sub]

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * _root_.Complex.I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * _root_.Complex.I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * _root_.Complex.I) = A * x / (x ^ 2 + y ^ 2) - A * _root_.Complex.I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [Complex.inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * _root_.Complex.I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * _root_.Complex.I) =
    A / _root_.Complex.I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / _root_.Complex.I * _root_.Complex.I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * _root_.Complex.I) = A / _root_.Complex.I / (y + ↑(-x) * _root_.Complex.I) := by
    have e1 : x + y * _root_.Complex.I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + _root_.Complex.I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * _root_.Complex.I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * _root_.Complex.I) * (2 * _root_.Complex.I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ZetaBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
                            
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    ext; simp <;> ring
                  
  rw[this]
  have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul f_near_p ?_
                               
    have g_cont : ContinuousAt g p := by
                                                              
      exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
                                        
    have := g_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono this inf_le_left
  ·                                                              

    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert! (preTransparency := .instances) this using 2
      all_goals try with_reducible_and_instances rfl
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left

    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt

    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert! (preTransparency := .instances) h1 using 2
      all_goals try with_reducible_and_instances rfl
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simpa

lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, inf_of_le_left] at him_lower
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, sup_of_le_right] at him_upper
    exact ⟨him_lower, him_upper⟩

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rwa [← this]

  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    · apply s_in_U_im_le3 _ hs
    · apply s_in_U_re_ges2 _ hs

open _root_.ArithmeticFunction (vonMangoldt)

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT4_ZeroFreeRegion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I)) := by
  apply zeta1zetaseries

  have h : (x + y * I).re = x := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_add_re_ofReal_mul_I (x y : ℝ) : (x + y * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
                                  
  have h : I.re = 0 := Complex.I_re
  rw [h]
  simp

lemma helper_zerosetKfR_eq_center0 (r : ℝ) (hr : r > 0) (f : ℂ → ℂ) :
  zerosetKfR r hr f = zerosetKfRc r (0 : ℂ) f := by
  ext ρ; simp [zerosetKfR, zerosetKfRc]

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_SmoothExistence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.MeasureTheory _root_.Set _root_.Real
open scoped ContDiff

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert (preTransparency := .instances) hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT5_Strong
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

theorem MellinInversion (σ : ℝ) {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    MellinInverseTransform (MellinTransform f) σ x = f x := by
  rw [MellinInverseTransform_eq, mellinInv_mellin_eq σ f hx hf hFf hfx]

local notation "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    apply continuousOn_univ.mp
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    . refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one hz).continuousAt
    . fun_prop
    . simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
                
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq] <;> linarith)]
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y:= σ) (x:= i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  have x_neq_zero : X ≠ 0 := by linarith
  . intro i
    by_cases i_eq_zero : i = 0
    . simpa [i_eq_zero] using aestronglyMeasurable_const
    . apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  . rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal, Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp), ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top
    . rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (preTransparency := .instances) (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re] <;> linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    . simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one: ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos: 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (by linarith : 0 < X)]
    linarith [Real.exp_one_lt_d9]
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0; simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + t * I) ?_ ?_
    push_cast at this ⊢
    rw [mul_comm I (↑t : ℂ)]
    rw [← this, div_mul_cancel₀]
    · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg (by linarith : 0 ≤ X); simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, not_and, not_not]
      intro hn; exfalso; exact n_ne_zero hn
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    congr 1
    funext n

    simp_rw [ht, h, hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0; simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    rw [(by rw [div_mul]; simp : 1 / (2 * π) = 1 / (2 * π * I) * I), mul_assoc]
    conv => lhs; rhs; rhs; rhs; intro t; rw [mul_comm]; norm_cast
    have := MellinInversion σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [MellinInverseTransform, VerticalIntegral] at this
      rw [this]
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  have vonManBnd (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log

  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    rfl
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    exact Real.log_nonneg (by norm_num)
    positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  unfold ChebyshevPsi

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have X_ne_zero : X ≠ 0 := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    have : 1 / Real.log 2 < 2 := by
      nth_rewrite 2 [← one_div_one_div 2]
      rw[one_div_lt_one_div]
      exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
      exact Real.log_pos (by norm_num)
      norm_num
    apply le_of_lt
    exact gt_trans X_bound this
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    have : 1 / (2 * Real.log 2) < 2 := by
      nth_rewrite 3 [← one_div_one_div 2]
      rw[one_div_lt_one_div, ← one_mul (1 / 2)]
      apply mul_lt_mul
      norm_num
      apply le_of_lt
      exact lt_trans (by norm_num) (Real.log_two_gt_d9)
      all_goals norm_num
      exact Real.log_pos (by norm_num)

    apply le_of_lt
    exact gt_trans X_bound this
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert (preTransparency := .instances) SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε ε_pos ε_lt_one
    X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow smoothIs1 smoothIs0

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw[← intervalIntegral.integral_add_adjacent_intervals (b := a), ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals apply IntervalIntegrable.mono_set hf; apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) = (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) = -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 ((Smooth1 ν ε) ·) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_ofPred_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h

open _root_.Filter Topology

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter _root_.Asymptotics
open scoped Topology

theorem psi_eq_original {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x = _root_.Erdos970.ChebyshevPsi x := by
  rw [Chebyshev.psi_eq_sum_Icc, _root_.Erdos970.ChebyshevPsi, Nat.floor_add_one hx,
    Nat.range_succ_eq_Icc_zero]

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset
open PrimeAbel

theorem endpoint_difference {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (lc rc : Bool) : |intervalSum lc rc a b - reciprocalPrimes a b| ≤ 2 / a := by
  classical
  have hw : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  rw [intervalSum, reciprocal_eq_core ha.le hab, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        |(if intervalGuard lc rc a b (n : ℝ) then (n : ℝ)⁻¹ else 0) -
          (if a < (n : ℝ) then (n : ℝ)⁻¹ else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        ((if (n : ℝ) = a then a⁻¹ else 0) + (if (n : ℝ) = b then a⁻¹ else 0)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hp : n.Prime := (Nat.mem_primesLE.mp hn).2
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hp.pos
      have hnw : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
      have hnb : (n : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha.le hab)).mp (Nat.mem_primesLE.mp hn).1
      by_cases hna : (n : ℝ) = a
      · have hd := selection_difference_bound (intervalGuard lc rc a b (n : ℝ)) (a < (n : ℝ)) hnw
        calc
          _ ≤ (n : ℝ)⁻¹ := hd
          _ ≤ _ := by rw [hna]; split_ifs <;> simp_all
      · by_cases hneqb : (n : ℝ) = b
        · calc
            _ ≤ (n : ℝ)⁻¹ := selection_difference_bound _ _ hnw
            _ ≤ a⁻¹ := by rw [hneqb]; exact inv_anti₀ ha hab
            _ = _ := by rw [ite_eq_right hna, ite_eq_left hneqb, zero_add]
        · have hguard : intervalGuard lc rc a b (n : ℝ) ↔ a < (n : ℝ) := by
            have hne : a ≠ (n : ℝ) := Ne.symm hna
            cases lc <;> cases rc <;> simp_all [intervalGuard, le_iff_lt_or_eq]
          simp [hguard, hna, hneqb]
    _ ≤ a⁻¹ + a⁻¹ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (fiber_sum_le _ _ hw) (fiber_sum_le _ _ hw)
    _ = 2 / a := by ring

end ErdosPrimeInputs.PrimeEndpoints



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_TransitionKernels
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_even _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_odd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TransitionKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DerivativeWeights WeightFutureIntegrals

noncomputable def evenDensity (s : EvenState) : ℝ → ℝ :=
  tailDensity (s.1 - 1) (phiEven s.1) (fun t => W t * phiOdd t)

noncomputable def oddDensity (s : OddState) : ℝ → ℝ :=
  tailDensity (max 2 (s.1 - 1)) (phiOdd s.1) (fun t => W t * phiEven t)

theorem evenDensity_measurable : Measurable (Function.uncurry evenDensity) := by
  change Measurable (fun x : EvenState × ℝ =>
    if x.1.1 - 1 ≤ x.2 then W x.2 * phiOdd x.2 / phiEven x.1.1 else 0)
  apply Measurable.ite
    (measurableSet_le ((measurable_subtype_coe.comp measurable_fst).sub measurable_const) measurable_snd)
  · exact ((W_measurable.comp measurable_snd).mul
      (phiOdd_continuous.measurable.comp measurable_snd)).div
      (phiEven_measurable.comp (measurable_subtype_coe.comp measurable_fst))
  · exact measurable_const

theorem oddDensity_measurable : Measurable (Function.uncurry oddDensity) := by
  change Measurable (fun x : OddState × ℝ =>
    if max 2 (x.1.1 - 1) ≤ x.2 then W x.2 * phiEven x.2 / phiOdd x.1.1 else 0)
  apply Measurable.ite
    (measurableSet_le (measurable_const.max
      ((measurable_subtype_coe.comp measurable_fst).sub measurable_const)) measurable_snd)
  · exact ((W_measurable.comp measurable_snd).mul
      (phiEven_measurable.comp measurable_snd)).div
      (phiOdd_continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst))
  · exact measurable_const

theorem evenDensity_nonneg (s : EvenState) (t : ℝ) : 0 ≤ evenDensity s t := by
  have hs : 1 < s.1 := by linarith [s.2]
  apply tailDensity_nonneg (phiEven_pos hs) ?_ t
  intro u hu
  exact (mul_pos (W_pos (by linarith)) (phiOdd_pos u)).le

theorem oddDensity_nonneg (s : OddState) (t : ℝ) : 0 ≤ oddDensity s t := by
  apply tailDensity_nonneg (phiOdd_pos s.1) ?_ t
  intro u hu
  have hu1 : 1 < u := by linarith [le_max_left (2 : ℝ) (s.1 - 1)]
  exact (mul_pos (W_pos (by linarith)) (phiEven_pos hu1)).le

theorem evenDensity_integrable (s : EvenState) : Integrable (evenDensity s) :=
  tailDensity_integrable (phiEven_future_integral (s := s.1) (by linarith [s.2])).1

theorem oddDensity_integrable (s : OddState) : Integrable (oddDensity s) :=
  tailDensity_integrable (phiOdd_future_integral s.1).1

theorem evenDensity_integral (s : EvenState) : ∫ t, evenDensity s t = 1 :=
  tailDensity_integral (phiEven_pos (by linarith [s.2]))
    (phiEven_future_integral (s := s.1) (by linarith [s.2])).2

theorem oddDensity_integral (s : OddState) : ∫ t, oddDensity s t = 1 :=
  tailDensity_integral (phiOdd_pos s.1) (phiOdd_future_integral s.1).2

noncomputable def evenKernel : Kernel EvenState ℝ :=
  (Kernel.const EvenState volume).withDensity (fun s t => ENNReal.ofReal (evenDensity s t))

noncomputable def oddKernel : Kernel OddState ℝ :=
  (Kernel.const OddState volume).withDensity (fun s t => ENNReal.ofReal (oddDensity s t))

theorem evenKernel_apply (s : EvenState) (B : Set ℝ) :
    evenKernel s B = ∫⁻ t in B, ENNReal.ofReal (evenDensity s t) := by
  exact Kernel.withDensity_apply' (Kernel.const EvenState volume)
    (f := fun s t => ENNReal.ofReal (evenDensity s t))
    (ENNReal.measurable_ofReal.comp evenDensity_measurable) s B

theorem oddKernel_apply (s : OddState) (B : Set ℝ) :
    oddKernel s B = ∫⁻ t in B, ENNReal.ofReal (oddDensity s t) := by
  exact Kernel.withDensity_apply' (Kernel.const OddState volume)
    (f := fun s t => ENNReal.ofReal (oddDensity s t))
    (ENNReal.measurable_ofReal.comp oddDensity_measurable) s B

instance evenKernel_isMarkovKernel : IsMarkovKernel evenKernel := by
  constructor
  intro s
  constructor
  rw [evenKernel_apply, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (evenDensity_integrable s)
      (Eventually.of_forall (evenDensity_nonneg s)), evenDensity_integral]
  norm_num

instance oddKernel_isMarkovKernel : IsMarkovKernel oddKernel := by
  constructor
  intro s
  constructor
  rw [oddKernel_apply, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (oddDensity_integrable s)
      (Eventually.of_forall (oddDensity_nonneg s)), oddDensity_integral]
  norm_num

theorem evenKernel_below_support (s : EvenState) : evenKernel s (Iio (s.1 - 1)) = 0 := by
  rw [evenKernel_apply]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro t ht
  have hn : t ∉ Ici (s.1 - 1) := by
    change ¬s.1 - 1 ≤ t
    change t < s.1 - 1 at ht
    exact not_le_of_gt ht
  simp only [evenDensity, tailDensity, indicator_of_notMem hn, ENNReal.ofReal_zero, Pi.zero_apply]

theorem oddKernel_below_support (s : OddState) : oddKernel s (Iio (max 2 (s.1 - 1))) = 0 := by
  rw [oddKernel_apply]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro t ht
  have hn : t ∉ Ici (max 2 (s.1 - 1)) := by
    change ¬max 2 (s.1 - 1) ≤ t
    change t < max 2 (s.1 - 1) at ht
    exact not_le_of_gt ht
  simp only [oddDensity, tailDensity, indicator_of_notMem hn, ENNReal.ofReal_zero, Pi.zero_apply]

theorem evenKernel_ae_support (s : EvenState) : ∀ᵐ t ∂evenKernel s, s.1 - 1 ≤ t := by
  apply ae_iff.mpr
  convert! evenKernel_below_support s using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_Iio, not_le]

theorem oddKernel_ae_support (s : OddState) : ∀ᵐ t ∂oddKernel s, max 2 (s.1 - 1) ≤ t := by
  apply ae_iff.mpr
  convert! oddKernel_below_support s using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_Iio, not_le]

theorem evenKernel_ae_odd_domain (s : EvenState) : ∀ᵐ t ∂evenKernel s, 95 / 100 ≤ t := by
  filter_upwards [evenKernel_ae_support s] with t ht
  linarith [s.2]

theorem oddKernel_ae_even_domain (s : OddState) : ∀ᵐ t ∂oddKernel s, 198 / 100 ≤ t := by
  filter_upwards [oddKernel_ae_support s] with t ht
  linarith [le_max_left (2 : ℝ) (s.1 - 1)]

end NumberTheoryLean.TransitionKernels

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_even _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_odd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

def Side.flip : Side → Side | .even => .odd | .odd => .even

noncomputable def weight : Side → ℝ → ℝ | .even => phiEven | .odd => phiOdd

def Valid : Side → ℝ → Prop
  | .even, s => 198 / 100 ≤ s
  | .odd, s => 95 / 100 ≤ s

noncomputable def minRatio : Side → ℝ → ℝ
  | .even, s => s - 1
  | .odd, s => max 2 (s - 1)

noncomputable def transitionDensity (i : Side) (s : ℝ) : ℝ → ℝ :=
  tailDensity (minRatio i s) (weight i s) (fun t => W t * weight i.flip t)

def Admissible : Side → ℝ → List ℝ → Prop
  | _, _, [] => True
  | i, s, t :: ts => minRatio i s ≤ t ∧ Admissible i.flip t ts

def finalSide : Side → List ℝ → Side
  | i, [] => i
  | i, _ :: ts => finalSide i.flip ts

noncomputable def pathCost : List ℝ → ℝ
  | [] => 0
  | t :: ts => cost t + pathCost ts

theorem valid_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < s := by
  cases i <;> dsimp [Valid] at hs <;> linarith

theorem weight_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < weight i s := by
  cases i with
  | even => exact phiEven_pos (by dsimp [Valid] at hs <;> linarith)
  | odd => exact phiOdd_pos s

theorem valid_next {i : Side} {s t : ℝ} (hs : Valid i s) (ht : minRatio i s ≤ t) :
    Valid i.flip t := by
  cases i with
  | even => dsimp [Valid, minRatio, Side.flip] at * <;> linarith
  | odd =>
    change 198 / 100 ≤ t
    change max 2 (s - 1) ≤ t at ht
    linarith [le_max_left (2 : ℝ) (s - 1)]

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.FinitePathMeasures

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry

noncomputable def evenToOdd : Kernel EvenState OddState :=
  evenKernel.comapRight (MeasurableEmbedding.subtype_coe measurableSet_Ici)

noncomputable def oddToEven : Kernel OddState EvenState :=
  oddKernel.comapRight (MeasurableEmbedding.subtype_coe measurableSet_Ici)

instance evenToOdd_isMarkovKernel : IsMarkovKernel evenToOdd := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have h := (ae_mem_iff_measure_eq (μ := evenKernel s)
    (s := Ici (95 / 100 : ℝ)) measurableSet_Ici.nullMeasurableSet).mp (evenKernel_ae_odd_domain s)
  rw [measure_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext t
  simp
  rfl

instance oddToEven_isMarkovKernel : IsMarkovKernel oddToEven := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have h := (ae_mem_iff_measure_eq (μ := oddKernel s)
    (s := Ici (198 / 100 : ℝ)) measurableSet_Ici.nullMeasurableSet).mp (oddKernel_ae_even_domain s)
  rw [measure_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext t
  simp
  rfl

noncomputable def evenBranch : Kernel EvenState State := evenToOdd.map Sum.inr
noncomputable def oddBranch : Kernel OddState State := oddToEven.map Sum.inl

instance evenBranch_isMarkovKernel : IsMarkovKernel evenBranch :=
  Kernel.IsMarkovKernel.map _ measurable_inr

instance oddBranch_isMarkovKernel : IsMarkovKernel oddBranch :=
  Kernel.IsMarkovKernel.map _ measurable_inl

noncomputable def stateKernel : Kernel State State where
  toFun := Sum.elim evenBranch oddBranch
  measurable' := evenBranch.measurable.sumElim oddBranch.measurable

instance stateKernel_isMarkovKernel : IsMarkovKernel stateKernel := by
  constructor
  intro s
  cases s with
  | inl s => change IsProbabilityMeasure (evenBranch s); infer_instance
  | inr s => change IsProbabilityMeasure (oddBranch s); infer_instance

def stateSide : State → Side := Sum.elim (fun _ => .even) (fun _ => .odd)

theorem stateRatio_valid (s : State) : Valid (stateSide s) (stateRatio s) := by
  cases s with
  | inl s => exact s.2
  | inr s => exact s.2

theorem stateRatio_measurable : Measurable stateRatio :=
  measurable_subtype_coe.sumElim measurable_subtype_coe

theorem cost_measurable : Measurable cost := by
  unfold cost
  exact Real.measurable_log.comp (measurable_const.add (measurable_const.div measurable_id))

noncomputable def addCost (z : CostState × State) : CostState :=
  (z.2, z.1.2 + cost (stateRatio z.2))

theorem addCost_measurable : Measurable addCost :=
  measurable_snd.prodMk ((measurable_snd.comp measurable_fst).add
    (cost_measurable.comp (stateRatio_measurable.comp measurable_snd)))

noncomputable def costKernel : Kernel CostState CostState :=
  (Kernel.id ×ₖ stateKernel.prodMkRight ℝ).map addCost

instance costKernel_isMarkovKernel : IsMarkovKernel costKernel :=
  Kernel.IsMarkovKernel.map _ addCost_measurable

theorem costKernel_apply (z : CostState) {B : Set CostState} (hB : MeasurableSet B) :
    costKernel z B = stateKernel z.1 {s | (s, z.2 + cost (stateRatio s)) ∈ B} := by
  rw [costKernel, Kernel.map_apply' _ addCost_measurable _ hB,
    Kernel.prod_apply' _ _ _ (addCost_measurable hB), Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (addCost_measurable hB)

noncomputable def historyKernel (n : ℕ) :
    Kernel (∀ _ : Finset.Iic n, CostState) CostState :=
  costKernel.comap (fun h => h ⟨n, by simp⟩) (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n))

instance historyKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (historyKernel n) := by
  unfold historyKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def finitePathKernel (n : ℕ) :
    Kernel (∀ _ : Finset.Iic (0 : ℕ), CostState) (∀ _ : Finset.Iic n, CostState) :=
  Kernel.partialTraj (X := fun _ => CostState) historyKernel 0 n

instance finitePathKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (finitePathKernel n) := by
  unfold finitePathKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def finitePathMeasure (s : State) (n : ℕ) : Measure (∀ _ : Finset.Iic n, CostState) :=
  finitePathKernel n (fun _ => (s, 0))

instance finitePathMeasure_isProbabilityMeasure (s : State) (n : ℕ) :
    IsProbabilityMeasure (finitePathMeasure s n) := by
  unfold finitePathMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.FinitePathMeasures



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InverseWeightGrowth
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightTailBounds

open Filter Set
open scoped Topology
open DerivativeWeights WeightDickmanComparison

theorem ratio_upper_from_rho {s c C p q : ℝ} (hs : 4 ≤ s)
    (hc : 0 < c) (hC : 0 < C) (hp : 0 < p)
    (hpl : c * Dickman.rho (s - 2) ≤ p) (hqu : q ≤ C * Dickman.rho (s - 3)) :
    q / p ≤ (4 * C / c) * s ^ 2 := by
  have hr : Dickman.rho (s - 3) ≤ 4 * (s - 2) ^ 2 * Dickman.rho (s - 2) := by
    convert! Dickman.rho_lower_comparison (u := s - 2) (by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hr' : Dickman.rho (s - 3) ≤ 4 * s ^ 2 * Dickman.rho (s - 2) := by
    apply le_trans hr
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Dickman.rho_nonneg _)
  have hρ : Dickman.rho (s - 2) ≤ p / c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hq : q ≤ ((4 * C / c) * s ^ 2) * p := by
    calc
      q ≤ C * Dickman.rho (s - 3) := hqu
      _ ≤ C * (4 * s ^ 2 * Dickman.rho (s - 2)) := mul_le_mul_of_nonneg_left hr' hC.le
      _ ≤ C * (4 * s ^ 2 * (p / c)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hρ (by positivity)) hC.le
      _ = _ := by ring
  exact (div_le_iff₀ hp).mpr hq

theorem weights_ratio_bound : ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 4 ≤ s →
    phiOdd (s - 1) / phiEven s ≤ K * s ^ 2 ∧
    phiEven (s - 1) / phiOdd s ≤ K * s ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := weights_dickman_bounds
  refine ⟨4 * C / c, by positivity, ?_⟩
  intro s hs
  have hsp : 2 ≤ s - 1 := by linarith
  have he := (hb (s - 1) hsp).1.2
  have ho := (hb (s - 1) hsp).2.2
  rw [show s - 1 - 2 = s - 3 by ring] at he ho
  exact ⟨ratio_upper_from_rho hs hc hC (phiEven_pos (by linarith)) (hb s (by linarith)).1.1 ho,
    ratio_upper_from_rho hs hc hC (phiOdd_pos s) (hb s (by linarith)).2.1 he⟩

end NumberTheoryLean.WeightTailBounds

end

section

namespace NumberTheoryLean.WeightGlobalBounds

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge DerivativeWeights WeightTailBounds

theorem weights_global_ratio_bound : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s → phiOdd (s - 1) / phiEven s ≤ C * (1 + s) ^ 2) ∧
    (∀ s : ℝ, 95 / 100 ≤ s → phiEven (max 2 (s - 1)) / phiOdd s ≤ C * (1 + s) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := weights_ratio_bound
  let E : ℝ := sieveA / phiEven 4
  let O : ℝ := phiEven 2 / phiOdd 4
  have hE : 0 < E := div_pos sieveA_pos (phiEven_pos (by norm_num))
  have hO : 0 < O := div_pos (phiEven_pos (by norm_num)) (phiOdd_pos 4)
  let C := K + E + O
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hKC : K ≤ C := by dsimp [C] <;> linarith
  have hEC : E ≤ C := by dsimp [C] <;> linarith
  have hOC : O ≤ C := by dsimp [C] <;> linarith
  have hlarge : ∀ s : ℝ, 0 ≤ s → K * s ^ 2 ≤ C * (1 + s) ^ 2 := by
    intro s hs
    exact mul_le_mul hKC (by nlinarith) (sq_nonneg _) hC.le
  have hsmall : ∀ s : ℝ, 0 ≤ s → C ≤ C * (1 + s) ^ 2 := by
    intro s hs
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (1 + s) ^ 2 by nlinarith) hC.le]
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    have hs1 : 1 < s := by linarith
    by_cases hs4 : s ≤ 4
    · have hden : phiEven 4 ≤ phiEven s :=
        phiEven_strictAntiOn.antitoneOn hs1 (by norm_num) hs4
      rw [phiOdd_initial (s := s - 1) (by linarith)]
      exact le_trans (div_le_div_of_nonneg_left sieveA_pos.le (phiEven_pos (by norm_num)) hden)
        (le_trans hEC (hsmall s (by linarith)))
    · exact le_trans (hb s (le_of_not_ge hs4)).1 (hlarge s (by linarith))
  · intro s hs
    by_cases hs4 : s ≤ 4
    · have hm2 : 2 ≤ max 2 (s - 1) := le_max_left _ _
      have hnum : phiEven (max 2 (s - 1)) ≤ phiEven 2 :=
        phiEven_strictAntiOn.antitoneOn (by norm_num) (by change 1 < max 2 (s - 1); linarith) hm2
      have hden : phiOdd 4 ≤ phiOdd s := phiOdd_antitone hs4
      have hr : phiEven (max 2 (s - 1)) / phiOdd s ≤ O := by
        calc
          _ ≤ phiEven 2 / phiOdd s := div_le_div_of_nonneg_right hnum (phiOdd_pos s).le
          _ ≤ _ := div_le_div_of_nonneg_left (phiEven_pos (by norm_num)).le (phiOdd_pos 4) hden
      exact le_trans hr (le_trans hOC (hsmall s (by linarith)))
    · rw [max_eq_right (show 2 ≤ s - 1 by linarith)]
      exact le_trans (hb s (le_of_not_ge hs4)).2 (hlarge s (by linarith))

end NumberTheoryLean.WeightGlobalBounds

end

section

namespace NumberTheoryLean.InverseWeightGrowth
open FinitePathGeometry DerivativeWeights WeightGlobalBounds

def reference : Side → ℝ | .even => 2 | .odd => 1

end NumberTheoryLean.InverseWeightGrowth

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open _root_.Erdos970.Set
open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def children (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^cap⌋₊).filter (fun p => ell < primeExponent w p ∧
    capGuard closed cap (primeExponent w p) ∧ minRatio i s ≤ childRatio w r p ∧ childRatio w r p ≤ S)

theorem mem_children_iff {w ell S s r cap : ℝ} (hw : 1 < w) (i : Side) (closed : Bool) (p : ℕ) :
    p ∈ children w ell S i s r cap closed ↔ p.Prime ∧ ell < primeExponent w p ∧
      capGuard closed cap (primeExponent w p) ∧ minRatio i s ≤ childRatio w r p ∧ childRatio w r p ≤ S := by
  classical
  unfold children
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,hp⟩,hx,hcap,ht,hS⟩
    exact ⟨hp,hx,hcap,ht,hS⟩
  · rintro ⟨hp,hx,hcap,ht,hS⟩
    refine ⟨⟨?_,hp⟩,hx,hcap,ht,hS⟩
    have hc : primeExponent w p ≤ cap := by
      cases closed with
      | false => exact (show primeExponent w p < cap from hcap).le
      | true => exact hcap
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hreal : (p : ℝ) ≤ w^cap := (exponent_le_iff hw hp0).mp hc
    exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) cap).le).mpr hreal

theorem child_valid {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) : Valid i.flip (childRatio w r p) := by
  classical
  have ht := (Finset.mem_filter.mp hp).2.2.2.1
  exact valid_next hs ht

theorem child_exponent_positive {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hp : p ∈ children w ell S i s r cap closed) : 0 < primeExponent w p := by
  classical
  exact lt_of_le_of_lt hell (Finset.mem_filter.mp hp).2.1

theorem child_gap_positive {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    0 < r - primeExponent w p := by
  have ht := valid_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  exact nextGap_pos hr ht

noncomputable def primeTilt (w r : ℝ) (i : Side) (s : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * ((childRatio w r p + 1) / childRatio w r p)^2 *
    weight i.flip (childRatio w r p) / weight i s

theorem primeTilt_nonneg {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) : 0 ≤ primeTilt w r i s p := by
  unfold primeTilt
  exact div_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (sq_nonneg _))
    (weight_pos (child_valid hs hp)).le) (weight_pos hs).le

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def PrimeAdmissible (w ell S : ℝ) : Side → ℝ → ℝ → ℝ → Bool → List ℕ → Prop
  | _, _, _, _, _, [] => True
  | i, s, r, cap, closed, p::ps => p ∈ children w ell S i s r cap closed ∧
      PrimeAdmissible w ell S i.flip (childRatio w r p) (r-primeExponent w p) (primeExponent w p) false ps

noncomputable def primeRatios (w : ℝ) : ℝ → List ℕ → List ℝ
  | _, [] => []
  | r, p::ps => childRatio w r p :: primeRatios w (r-primeExponent w p) ps

noncomputable def primeFinalGap (w : ℝ) : ℝ → List ℕ → ℝ
  | r, [] => r
  | r, p::ps => primeFinalGap w (r-primeExponent w p) ps

noncomputable def tiltProduct (w : ℝ) : Side → ℝ → ℝ → List ℕ → ℝ
  | _, _, _, [] => 1
  | i, s, r, p::ps => primeTilt w r i s p * tiltProduct w i.flip (childRatio w r p) (r-primeExponent w p) ps

noncomputable def normalizedTiltProduct (e w : ℝ) : Side → ℝ → ℝ → List ℕ → ℝ
  | _, _, _, [] => 1
  | i, s, r, p::ps => (primeTilt w r i s p / (1+e)) *
      normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeTiltBounds

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry WeightGlobalBounds DerivativeWeights

noncomputable def multiplier (i : Side) (s t : ℝ) : ℝ :=
  ((t+1)/t)^2 * weight i.flip t / weight i s

theorem primeTilt_eq_multiplier (w r : ℝ) (i : Side) (s : ℝ) (p : ℕ) :
    primeTilt w r i s p = (p : ℝ)⁻¹ * multiplier i s (childRatio w r p) := by
  unfold primeTilt multiplier
  ring

theorem multiplier_pos {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i.flip t) :
    0 < multiplier i s t := by
  have ht0 := valid_pos ht
  exact div_pos (mul_pos (sq_pos_of_pos (div_pos (by linarith) ht0)) (weight_pos ht)) (weight_pos hs)

theorem valid_ge_half {i : Side} {t : ℝ} (ht : Valid i t) : (1/2 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem multiplier_envelope : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s t : ℝ,
    Valid i s → s ≤ S → minRatio i s ≤ t → multiplier i s t ≤ C * (1+S)^2 := by
  obtain ⟨C,hC,he,ho⟩ := weights_global_ratio_bound
  refine ⟨9*C, by positivity, ?_⟩
  intro S i s t hs hsS hst
  have ht := valid_next hs hst
  have ht0 := valid_pos ht
  have hhalf := valid_ge_half ht
  have hrat : weight i.flip t / weight i s ≤ C * (1+s)^2 := by
    cases i with
    | even =>
      have hm : phiOdd t ≤ phiOdd (s-1) := phiOdd_antitone hst
      exact (div_le_div_of_nonneg_right hm (weight_pos hs).le).trans (he s hs)
    | odd =>
      change max 2 (s-1) ≤ t at hst
      have hm2 : 2 ≤ max 2 (s-1) := le_max_left _ _
      have hm : phiEven t ≤ phiEven (max 2 (s-1)) :=
        phiEven_strictAntiOn.antitoneOn (by change 1 < max 2 (s-1); linarith)
          (by change 1 < t; linarith) hst
      exact (div_le_div_of_nonneg_right hm (weight_pos hs).le).trans (ho s hs)
  have hq : (t+1)/t ≤ 3 := (div_le_iff₀ ht0).mpr (by linarith)
  have hq0 : 0 ≤ (t+1)/t := (div_pos (by linarith) ht0).le
  have hsq : ((t+1)/t)^2 ≤ 9 := by nlinarith
  have hs0 := valid_pos hs
  calc
    _ = ((t+1)/t)^2 * (weight i.flip t / weight i s) := by unfold multiplier; ring
    _ ≤ 9 * (C * (1+s)^2) := mul_le_mul hsq hrat (div_pos (weight_pos ht) (weight_pos hs)).le (by norm_num)
    _ ≤ (9*C) * (1+S)^2 := by
      have hp : (1+s)^2 ≤ (1+S)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 9*C by positivity)]

end NumberTheoryLean.PrimeTiltBounds

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

structure Node where
  side : Side
  ratio : ℝ
  gap : ℝ
  cutoff : ℝ
  closed : Bool

noncomputable def nodeChildren (w ell S : ℝ) (z : Node) : Finset ℕ :=
  children w ell S z.side z.ratio z.gap z.cutoff z.closed

noncomputable def step (w : ℝ) (z : Node) (p : ℕ) : Node where
  side := z.side.flip
  ratio := childRatio w z.gap p
  gap := z.gap - primeExponent w p
  cutoff := primeExponent w p
  closed := false

noncomputable def terminal (w : ℝ) (z : Node) (ps : List ℕ) : Node := ps.foldl (step w) z

noncomputable def allowed (w ell S : ℝ) (z : Node) (ps : List ℕ) : Prop :=
  PrimeAdmissible w ell S z.side z.ratio z.gap z.cutoff z.closed ps

@[simp] theorem terminal_nil (w : ℝ) (z : Node) : terminal w z [] = z := rfl
@[simp] theorem terminal_cons (w : ℝ) (z : Node) (p : ℕ) (ps : List ℕ) :
    terminal w z (p::ps) = terminal w (step w z p) ps := rfl

theorem allowed_nil (w ell S : ℝ) (z : Node) : allowed w ell S z [] := trivial

theorem allowed_cons (w ell S : ℝ) (z : Node) (p : ℕ) (ps : List ℕ) :
    allowed w ell S z (p::ps) ↔ p ∈ nodeChildren w ell S z ∧ allowed w ell S (step w z p) ps := Iff.rfl

theorem allowed_append (w ell S : ℝ) (z : Node) (ps qs : List ℕ) :
    allowed w ell S z (ps++qs) ↔ allowed w ell S z ps ∧ allowed w ell S (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp only [List.nil_append, terminal_nil, iff_true_intro (allowed_nil w ell S z), true_and]
  | cons p ps ih =>
    rw [List.cons_append, allowed_cons, ih, allowed_cons, terminal_cons]
    tauto

theorem terminal_valid {w ell S : ℝ} {z : Node} {ps : List ℕ} (hs : Valid z.side z.ratio)
    (hp : allowed w ell S z ps) : Valid (terminal w z ps).side (terminal w z ps).ratio := by
  induction ps generalizing z with
  | nil => exact hs
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (child_valid hs hchild) hpath

theorem terminal_gap_positive {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) :
    0 < (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact hr
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (child_gap_positive hell hr hs hchild) (child_valid hs hchild) hpath

theorem terminal_ratio_le {w ell S : ℝ} {z : Node} {ps : List ℕ} (hs : z.ratio ≤ S)
    (hp : allowed w ell S z ps) : (terminal w z ps).ratio ≤ S := by
  classical
  induction ps generalizing z with
  | nil => exact hs
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (Finset.mem_filter.mp hchild).2.2.2.2 hpath

structure History (w ell S : ℝ) (start : Node) where
  primes : List ℕ
  admissible : allowed w ell S start primes

namespace History

variable {w ell S : ℝ} {start : Node}

@[ext] theorem ext {h k : History w ell S start} (heq : h.primes = k.primes) : h = k := by
  cases h
  cases k
  cases heq
  rfl

instance instCountable : Countable (History w ell S start) := (show Function.Injective (History.primes : History w ell S start → List ℕ) from fun _ _ h => ext h).countable
instance instMeasurableSpace : MeasurableSpace (History w ell S start) := ⊤
instance instMeasurableSingletonClass : MeasurableSingletonClass (History w ell S start) := ⟨fun _ => trivial⟩

def empty : History w ell S start := ⟨[],allowed_nil w ell S start⟩
noncomputable def node (h : History w ell S start) : Node := terminal w start h.primes

noncomputable def append (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) : History w ell S start where
  primes := h.primes ++ [p]
  admissible := (allowed_append w ell S start h.primes [p]).mpr ⟨h.admissible,
    (allowed_cons w ell S h.node p []).mpr ⟨hp,allowed_nil w ell S _⟩⟩

@[simp] theorem append_primes (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).primes = h.primes ++ [p] := rfl

end History
end NumberTheoryLean.PrimeHistories

end

section

namespace NumberTheoryLean.PrimeRatioBins

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def ratioBinMass (w r a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, (p : ℝ)⁻¹

end NumberTheoryLean.PrimeRatioBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceBenchmarkDecay

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open Dickman

noncomputable def benchmark : Side → ℝ → ℝ
  | .even => f sieveA
  | .odd => F sieveA

@[simp] theorem benchmark_even_below_two {s : ℝ} (hs : s ≤ 2) : benchmark .even s=0 :=
  f_initial sieveA hs

end NumberTheoryLean.ReferenceBenchmarkDecay



namespace NumberTheoryLean.ReferenceDifferentiation

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay

noncomputable def parentBenchmark : Side → ℝ → ℝ
  | .even, s => if s ≤ 2 then startingExtension sieveA s else f sieveA s
  | .odd, s => F sieveA s

def ParentDomain : Side → ℝ → Prop
  | .even, s => 1 < s
  | .odd, s => 0 < s

end NumberTheoryLean.ReferenceDifferentiation



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

def childAdmitted : Side → ℝ → ℝ → Prop
  | .even,_,_ => True
  | .odd,r,x => max (2*x) (x+2) ≤ r-x

noncomputable def admitted (w : ℝ) : Side → ℝ → List ℕ → Prop
  | _,_,[] => True
  | i,r,p::ps => childAdmitted i r (primeExponent w p) ∧ admitted w i.flip (r-primeExponent w p) ps

def endSide : Side → List ℕ → Side
  | i,[] => i
  | i,_::ps => endSide i.flip ps

noncomputable def FirstOmitted (w : ℝ) (i : Side) (r : ℝ) (ps : List ℕ) : Prop :=
  ∃ pre : List ℕ,∃ p : ℕ,ps=pre++[p] ∧ admitted w i r pre ∧
    ¬childAdmitted (endSide i pre) (primeFinalGap w r pre) (primeExponent w p)

noncomputable def referencePrefixes (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes P).filter (admitted w i r)

noncomputable def firstOmissions (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes P).filter (FirstOmitted w i r)

noncomputable def referencePolynomial (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : ℝ :=
  ∑ ps ∈ referencePrefixes w P i r,(-1:ℝ)^ps.length*prefixWeight ps

end NumberTheoryLean.ReferenceAdmission


section

open _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

noncomputable def upperCutoff : Side → ℝ → ℝ → ℝ
  | .even,_,b => max 1 (min 2 b)
  | .odd,r,b => max 1 (min (min 2 b) ((r-2)/2))

end ErdosContinuousBoundary

end


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundaryPrimeMass
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.VariablePrimeTilt

open _root_.Finset
open ReferenceAdmission FinitePathGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def omissionMass (w r : ℝ) (i : Side) : ℝ :=
  ∑ ps ∈ firstOmissions w (boundaryPrimes w) i r,prefixWeight ps

end NumberTheoryLean.VariablePrimeTilt

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PrefixCompletions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def completions (P : Finset ℕ) (pre : List ℕ) : Finset (List ℕ) :=
  (decreasingPrefixes (suffixPrimes P pre)).image (fun suf => pre++suf)

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_OmissionPartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open FinitePathGeometry ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass

noncomputable def rejectedPrefixes (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) :=
  (decreasingPrefixes P).filter (fun ps => ¬admitted w i r ps)

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def signedWeight (ps : List ℕ) : ℝ := (-1 : ℝ)^ps.length*prefixWeight ps

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferencePrefixRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePrefixRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def nonemptyPrefixes (P : Finset ℕ) : Finset (List ℕ) :=
  (decreasingPrefixes P).filter (fun ps => ps ≠ [])

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceCutoffRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceWeightedRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def weightedValue (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (F : List ℕ → ℝ) : ℝ :=
  ∑ ps ∈ referencePrefixes w P i r,signedWeight ps*F ps

end NumberTheoryLean.ReferenceWeightedRecurrence

end

section

namespace NumberTheoryLean.ReferenceForestTelescoping

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def forestSum (w : ℝ) (P : Finset ℕ) (z : Node) (G : Finset ℕ → Node → ℝ) : ℝ :=
  weightedValue w P z.side z.gap (fun ps => G (suffixPrimes P ps) (terminal w z ps))

noncomputable def recurrenceResidual (w : ℝ) (G : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) : ℝ :=
  G P z+∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
    (p:ℝ)⁻¹*G (P.filter (fun q => q<p)) (step w z p) else 0

end NumberTheoryLean.ReferenceForestTelescoping

end

section

namespace NumberTheoryLean.ReferenceCutoffRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ReferenceWeightedRecurrence ReferenceForestTelescoping
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def cutoffInsertion (w : ℝ) (Q : Finset ℕ) (B : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) : ℝ :=
  referencePolynomial w Q z.side z.gap-B P z-
    ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*B (P.filter (fun q => q<p)) (step w z p) else 0

end NumberTheoryLean.ReferenceCutoffRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ReferenceSourcePrimeSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceMertens

open _root_.Filter _root_.Asymptotics
open scoped Topology
open ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

noncomputable def normalization (w : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant)/(Real.log w*primeProduct w)

end NumberTheoryLean.ReferenceMertens

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryGateSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def boundaryTerm : ℕ → Side → ℝ → ℝ → ℝ
  | 0,_,_,_ => 1
  | n+1,i,r,b => ∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/(max 1 x)

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def boundaryIntegrand (n : ℕ) (i : Side) (r x : ℝ) : ℝ :=
  boundaryTerm n i.flip (r-x) x/(max 1 x)

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure
open ErdosMonotoneQuadrature

def boundaryGateSet (i : Side) (r b : ℝ) (closed : Bool) : Set ℝ :=
  {x | 1 < x ∧ x ≤ 2 ∧ (if closed then x ≤ b else x < b) ∧ childAdmitted i r x}

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousReference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def truncatedReference (N : ℕ) (i : Side) (r b : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm n i r b

noncomputable def boundaryReference (i : Side) (r b : ℝ) : ℝ :=
  truncatedReference (referenceDepth r) i r b

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryReferenceConvergence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.DiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def D (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : ℝ :=
  ∑ ps ∈ (referencePrefixes w P i r).filter (fun ps => ps.length=n),prefixWeight ps

end NumberTheoryLean.DiscreteBoundaryTerms

end

section

namespace NumberTheoryLean.ActualDiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable

open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferenceProductsBasics ReferenceSourcePrimeSets
open DiscreteBoundaryTerms
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def actualD (n : ℕ) (w b : ℝ) (closed : Bool) (i : Side) (r : ℝ) : ℝ :=
  D n w (availablePrimes w (w^b) closed) i r

end NumberTheoryLean.ActualDiscreteBoundaryTerms

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_WeightedAnomalyConvergence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.BoundaryAnomaly

open FinitePathGeometry ReferenceAdmission ReferencePruning
open VariablePrimeTilt ReferenceBenchmarkDecay

noncomputable def anomaly (w : ℝ) (i : Side) (r : ℝ) : ℝ :=
  referencePolynomial w (boundaryPrimes w) i r-
    survivorProduct (boundaryPrimes w)*benchmark i (r/2)

end NumberTheoryLean.BoundaryAnomaly

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open _root_.Erdos970.MeasureTheory _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceBenchmarkDecay NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

noncomputable def continuousAnomaly (i : Side) (r : ℝ) : ℝ :=
  boundaryReference i r 2-(1/2)*benchmark i (r/2)

end ErdosContinuousAnomaly

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry

noncomputable def shiftedAnomaly (i : Side) (y : ℝ) : ℝ := continuousAnomaly i (2*y+2)

end ErdosBoundaryIntegral

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryRadialCoefficient
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosBoundaryIntegral
open ErdosContinuousBoundary ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceBenchmarkDecay
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

noncomputable def lowerReference (y : ℝ) : ℝ := 2*boundaryReference .even (2*y+2) 2
noncomputable def upperReference (y : ℝ) : ℝ := 2*boundaryReference .odd (2*y+2) 2

noncomputable def signedCoefficientI : ℝ :=
  (∫ y in Ioi 1,(y^2-1)*(lowerReference y-f sieveA (y+1)))-
    ∫ y in Ioi 0,y^2*(upperReference y-F sieveA (y+1))

end ErdosBoundaryIntegral

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GateIterates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

abbrev Profile := Side → ℝ → ℝ → ℝ

def JointContinuous (H : Profile) : Prop := ∀ i,Continuous (fun p : ℝ×ℝ => H i p.1 p.2)

noncomputable def gate (H : Profile) (i : Side) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..upperCutoff i r b,H i.flip (r-x) x/(max 1 x)

end ErdosContinuousOmission

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def gateIterate : ℕ → Profile → Profile
  | 0,H => H
  | n+1,H => gate (gateIterate n H)

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OmissionSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def omissionForce : Profile
  | .even,_,_ => 0
  | .odd,r,b => (upperCutoff .odd r b)⁻¹-survivorBaseline b

end ErdosContinuousOmission

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def omissionDefect : Profile
  | .even,r,b => survivorBaseline b-boundaryReference .even r b
  | .odd,r,b => boundaryReference .odd r b-survivorBaseline b

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_StandardBoundaryCoefficient
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits

noncomputable def standardCoefficient : ℝ :=
  (∫ y in Ioi 1,(y^2-1)*(1-f sieveA (y+1)))-
    ∫ y in Ioi 0,y^2*(1-F sieveA (y+1))

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ActualLossDensity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open ErdosBoundaryIntegral Erdos970Dependency.StandardBoundary

noncomputable def sourceWeight : Side → ℝ → ℝ
  | .even,y => y^2-1
  | .odd,y => y^2

def sourceDomain : Side → Set ℝ
  | .even => Ioi 1
  | .odd => Ioi 0

noncomputable def lossDensity (i : Side) (y : ℝ) : ℝ :=
  2*sourceWeight i y*omissionDefect i (2*y+2) 2
noncomputable def omissionDensity (n : ℕ) (i : Side) (y : ℝ) : ℝ :=
  2*sourceWeight i y*gateIterate n omissionForce i (2*y+2) 2

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceLocalResidual
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceLocalResidual

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ReferenceAdmission ReferencePruning
open ReferenceSourcePrimeSets ReferenceMertens ReferenceDifferentiation
open ReferenceBenchmarkDecay BoundaryAnomaly
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def nodeBenchmark (w : ℝ) (z : Node) : ℝ :=
  referenceProduct w z.cutoff z.closed*parentBenchmark z.side z.ratio

noncomputable def sourceResidual (w : ℝ) (z : Node) : ℝ :=
  referenceProduct w 2 true*(benchmark z.side (z.gap/2)-1)-
    referenceProduct w z.cutoff z.closed*(parentBenchmark z.side z.ratio-1)-
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def sourceInsertion (w : ℝ) (z : Node) : ℝ :=
  referencePolynomial w (boundaryPrimes w) z.side z.gap-nodeBenchmark w z-
    ∑ p ∈ highPrimes w z.cutoff z.closed,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*nodeBenchmark w (step w z p) else 0

end NumberTheoryLean.ReferenceLocalResidual

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

noncomputable def baseRatio : Side → ℝ | .even => 198 / 100 | .odd => 95 / 100

theorem two_step_density_eq {i : Side} {s t u : ℝ} (hs : Valid i s)
    (ht : minRatio i s ≤ t) (hu : minRatio i.flip t ≤ u) :
    transitionDensity i s t * transitionDensity i.flip t u =
      (W t * W u) * (weight i u / weight i s) := by
  have htV := valid_next hs ht
  have hw := weight_pos hs
  have hwt := weight_pos htV
  have hflip : i.flip.flip = i := by cases i <;> rfl
  unfold transitionDensity TransitionKernels.tailDensity
  rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht),
    indicator_of_mem (show u ∈ Ici (minRatio i.flip t) from hu), hflip]
  field_simp

end NumberTheoryLean.TwoStepDensityBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationDrift
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_even _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_odd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RegenerationTails

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels FinitePathMeasures

theorem evenKernel_tail (s : EvenState) {h : ℝ} (hh : 0 ≤ h) :
    evenKernel s (Ici (s.1 - 1 + h)) = ENNReal.ofReal (phiEven (s.1 + h) / phiEven s.1) := by
  rw [evenKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (evenDensity_integrable s).integrableOn (Eventually.of_forall (evenDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (s.1 - 1 + h), tailDensity (s.1 - 1) (phiEven s.1) (fun t => W t * phiOdd t) t) = _
  rw [tailDensity_setIntegral (by linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiEven_future_integral (s := s.1 + h) (by linarith [s.2])).2
  rw [show s.1 + h - 1 = s.1 - 1 + h by ring] at hf
  rw [← hf]

theorem oddKernel_tail (s : OddState) (hs : 3 ≤ s.1) {h : ℝ} (hh : 0 ≤ h) :
    oddKernel s (Ici (s.1 - 1 + h)) = ENNReal.ofReal (phiOdd (s.1 + h) / phiOdd s.1) := by
  rw [oddKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable s).integrableOn (Eventually.of_forall (oddDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (s.1 - 1 + h), tailDensity (max 2 (s.1 - 1)) (phiOdd s.1)
    (fun t => W t * phiEven t) t) = _
  rw [tailDensity_setIntegral (by apply max_le <;> linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiOdd_future_integral (s.1 + h)).2
  rw [max_eq_right (show 2 ≤ s.1 + h - 1 by linarith),
    show s.1 + h - 1 = s.1 - 1 + h by ring] at hf
  rw [← hf]

theorem kernel_exponential_tails (rate : ℝ) : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → ∀ h : ℝ, 0 ≤ h →
      evenKernel s (Ici (s.1 - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-rate * h))) ∧
    (∀ s : OddState, U ≤ s.1 → ∀ h : ℝ, 0 ≤ h →
      oddKernel s (Ici (s.1 - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-rate * h))) := by
  obtain ⟨U, hU, hb⟩ := weights_logDeriv_growth rate
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs h hh
    rw [evenKernel_tail s hh]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiEven_pos (by linarith))).mpr
    have he := exponential_comparison (P := phiEven)
      (fun t ht => phiEven_pos (by linarith))
      (fun t ht => (phiEven_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).1) hs (show s.1 ≤ s.1 + h by linarith)
    simpa only [add_sub_cancel_left, mul_comm] using he
  · intro s hs h hh
    rw [oddKernel_tail s (by linarith) hh]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiOdd_pos s.1)).mpr
    have ho := exponential_comparison (P := phiOdd) (fun t _ => phiOdd_pos t)
      (fun t ht => (phiOdd_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).2) hs (show s.1 ≤ s.1 + h by linarith)
    simpa only [add_sub_cancel_left, mul_comm] using ho

def regenerationState : OddState := ⟨1, by norm_num⟩

end NumberTheoryLean.RegenerationTails

end

section

namespace NumberTheoryLean.RegenerationDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open TransitionKernels RegenerationTails

theorem kernel_exponential_drift : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → Integrable Real.exp (evenKernel s) ∧
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) ≤ ENNReal.ofReal (driftFactor * Real.exp s.1)) ∧
    (∀ s : OddState, U ≤ s.1 → Integrable Real.exp (oddKernel s) ∧
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂oddKernel s) ≤ ENNReal.ofReal (driftFactor * Real.exp s.1)) := by
  obtain ⟨U, hU, he, ho⟩ := kernel_exponential_tails 2
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs
    refine ⟨exponential_integrable_of_tail _ (s.1 - 1) (evenKernel_ae_support s) (he s hs), ?_⟩
    simpa only [drift_scale] using exponential_moment_of_tail _ (s.1 - 1) (evenKernel_ae_support s) (he s hs)
  · intro s hs
    have hsupport : ∀ᵐ t ∂oddKernel s, s.1 - 1 ≤ t := by
      filter_upwards [oddKernel_ae_support s] with t ht
      exact le_trans (le_max_right _ _) ht
    refine ⟨exponential_integrable_of_tail _ (s.1 - 1) hsupport (ho s hs), ?_⟩
    simpa only [drift_scale] using exponential_moment_of_tail _ (s.1 - 1) hsupport (ho s hs)

theorem kernel_drift_expectation : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ driftFactor * Real.exp s.1) ∧
    (∀ s : OddState, U ≤ s.1 → Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ driftFactor * Real.exp s.1) := by
  obtain ⟨U, hU, he, ho⟩ := kernel_exponential_drift
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs
    obtain ⟨hi, hb⟩ := he s hs
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_pos driftFactor_pos (Real.exp_pos _)).le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact hb
  · intro s hs
    obtain ⟨hi, hb⟩ := ho s hs
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_pos driftFactor_pos (Real.exp_pos _)).le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact hb

end NumberTheoryLean.RegenerationDrift

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CompactExponentialMoments
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_even _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_odd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CompactExponentialMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels RegenerationTails RegenerationDrift

theorem evenKernel_tail_above (s : EvenState) {v : ℝ} (hv : s.1 ≤ v) :
    evenKernel s (Ici (v - 1)) = ENNReal.ofReal (phiEven v / phiEven s.1) := by
  have h := evenKernel_tail s (sub_nonneg.mpr hv)
  rw [show s.1 - 1 + (v - s.1) = v - 1 by ring,
    show s.1 + (v - s.1) = v by ring] at h
  exact h

theorem oddKernel_tail_above (s : OddState) {v : ℝ} (hv : max 3 s.1 ≤ v) :
    oddKernel s (Ici (v - 1)) = ENNReal.ofReal (phiOdd v / phiOdd s.1) := by
  rw [oddKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable s).integrableOn (Eventually.of_forall (oddDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (v - 1), tailDensity (max 2 (s.1 - 1)) (phiOdd s.1)
    (fun t => W t * phiEven t) t) = _
  have hv3 := le_trans (le_max_left (3 : ℝ) s.1) hv
  have hvs := le_trans (le_max_right (3 : ℝ) s.1) hv
  rw [tailDensity_setIntegral (by apply max_le <;> linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiOdd_future_integral v).2
  rw [max_eq_right (show 2 ≤ v - 1 by linarith)] at hf
  rw [← hf]

theorem kernel_uniform_upper_tails : ∃ U : ℝ, 4 ≤ U ∧
    (∀ V : ℝ, U ≤ V → ∀ s : EvenState, s.1 ≤ V → ∀ h : ℝ, 0 ≤ h →
      evenKernel s (Ici (V - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) ∧
    (∀ V : ℝ, U ≤ V → ∀ s : OddState, s.1 ≤ V → ∀ h : ℝ, 0 ≤ h →
      oddKernel s (Ici (V - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) := by
  obtain ⟨U, hU, hb⟩ := weights_logDeriv_growth 2
  refine ⟨U, hU, ?_, ?_⟩
  · intro V hV s hs h hh
    rw [show V - 1 + h = V + h - 1 by ring, evenKernel_tail_above s (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiEven_pos (by linarith [s.2]))).mpr
    have hx := exponential_comparison (P := phiEven)
      (fun t ht => phiEven_pos (by linarith))
      (fun t ht => (phiEven_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).1) hV (show V ≤ V + h by linarith)
    rw [add_sub_cancel_left] at hx
    have hm : phiEven V ≤ phiEven s.1 :=
      phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by change 1 < V; linarith) hs
    exact le_trans hx (by nlinarith [mul_le_mul_of_nonneg_right hm (Real.exp_pos (-2 * h)).le])
  · intro V hV s hs h hh
    rw [show V - 1 + h = V + h - 1 by ring, oddKernel_tail_above s (by apply max_le <;> linarith)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiOdd_pos s.1)).mpr
    have hx := exponential_comparison (P := phiOdd) (fun t _ => phiOdd_pos t)
      (fun t ht => (phiOdd_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).2) hV (show V ≤ V + h by linarith)
    rw [add_sub_cancel_left] at hx
    have hm := phiOdd_antitone hs
    exact le_trans hx (by nlinarith [mul_le_mul_of_nonneg_right hm (Real.exp_pos (-2 * h)).le])

theorem kernel_compact_exponential_moments (S : ℝ) : ∃ C : ℝ, 0 < C ∧
    (∀ s : EvenState, s.1 ≤ S → Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ C) ∧
    (∀ s : OddState, s.1 ≤ S → Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ C) := by
  obtain ⟨U, _, he, ho⟩ := kernel_uniform_upper_tails
  let V := max U S
  let C := 2 * Real.exp (V - 1)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    have ht := he V (le_max_left _ _) s (le_trans hs (le_max_right _ _))
    have hi := exponential_integrable_of_upper_tail (evenKernel s) (V - 1) ht
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hC.le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact exponential_moment_of_upper_tail _ (V - 1) ht
  · intro s hs
    have ht := ho V (le_max_left _ _) s (le_trans hs (le_max_right _ _))
    have hi := exponential_integrable_of_upper_tail (oddKernel s) (V - 1) ht
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hC.le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact exponential_moment_of_upper_tail _ (V - 1) ht

theorem kernel_global_drift : ∃ C : ℝ, 0 < C ∧
    (∀ s : EvenState, Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ driftFactor * Real.exp s.1 + C) ∧
    (∀ s : OddState, Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ driftFactor * Real.exp s.1 + C) := by
  obtain ⟨U, _, he, ho⟩ := kernel_drift_expectation
  obtain ⟨C, hC, heC, hoC⟩ := kernel_compact_exponential_moments U
  refine ⟨C, hC, ?_, ?_⟩
  · intro s
    by_cases hs : U ≤ s.1
    · exact ⟨(he s hs).1, by linarith [(he s hs).2]⟩
    · exact ⟨(heC s (le_of_not_ge hs)).1, by
        nlinarith [(heC s (le_of_not_ge hs)).2, mul_pos driftFactor_pos (Real.exp_pos s.1)]⟩
  · intro s
    by_cases hs : U ≤ s.1
    · exact ⟨(ho s hs).1, by linarith [(ho s hs).2]⟩
    · exact ⟨(hoC s (le_of_not_ge hs)).1, by
        nlinarith [(hoC s (le_of_not_ge hs)).2, mul_pos driftFactor_pos (Real.exp_pos s.1)]⟩

end NumberTheoryLean.CompactExponentialMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FirstHitKernels
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelDensityBridge

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights TransitionKernels FinitePathGeometry FinitePathMeasures

theorem evenToOdd_map_ratio (s : EvenState) :
    (evenToOdd s).map (Subtype.val : OddState → ℝ) = evenKernel s := by
  calc
    _ = (evenKernel s).restrict (Ici (95 / 100 : ℝ)) := by
      change ((evenKernel s).comap (Subtype.val : OddState → ℝ)).map Subtype.val = _
      exact map_comap_subtype_coe (μ := evenKernel s) (s := Ici (95 / 100 : ℝ)) measurableSet_Ici
    _ = _ := Measure.restrict_eq_self_of_ae_mem (evenKernel_ae_odd_domain s)

theorem oddToEven_map_ratio (s : OddState) :
    (oddToEven s).map (Subtype.val : EvenState → ℝ) = oddKernel s := by
  calc
    _ = (oddKernel s).restrict (Ici (198 / 100 : ℝ)) := by
      change ((oddKernel s).comap (Subtype.val : EvenState → ℝ)).map Subtype.val = _
      exact map_comap_subtype_coe (μ := oddKernel s) (s := Ici (198 / 100 : ℝ)) measurableSet_Ici
    _ = _ := Measure.restrict_eq_self_of_ae_mem (oddKernel_ae_even_domain s)

theorem stateKernel_even_ratio (s : EvenState) :
    (stateKernel (.inl s)).map stateRatio = evenKernel s := by
  change (evenBranch s).map stateRatio = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr,
    Measure.map_map stateRatio_measurable measurable_inr]
  exact evenToOdd_map_ratio s

theorem stateKernel_odd_ratio (s : OddState) :
    (stateKernel (.inr s)).map stateRatio = oddKernel s := by
  change (oddBranch s).map stateRatio = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl,
    Measure.map_map stateRatio_measurable measurable_inl]
  exact oddToEven_map_ratio s

theorem evenToOdd_lintegral_ratio (s : EvenState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t : OddState, H t.1 ∂evenToOdd s) = ∫⁻ t, H t ∂evenKernel s := by
  rw [← evenToOdd_map_ratio, lintegral_map hH measurable_subtype_coe]

theorem oddToEven_lintegral_ratio (s : OddState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t : EvenState, H t.1 ∂oddToEven s) = ∫⁻ t, H t ∂oddKernel s := by
  rw [← oddToEven_map_ratio, lintegral_map hH measurable_subtype_coe]

theorem evenKernel_lintegral_density (s : EvenState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t, H t ∂evenKernel s) =
      ∫⁻ t, ENNReal.ofReal (transitionDensity .even s.1 t) * H t := by
  exact Kernel.lintegral_withDensity (Kernel.const EvenState volume)
    (f := fun s t => ENNReal.ofReal (evenDensity s t))
    (ENNReal.measurable_ofReal.comp evenDensity_measurable) s hH

theorem oddKernel_lintegral_density (s : OddState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t, H t ∂oddKernel s) =
      ∫⁻ t, ENNReal.ofReal (transitionDensity .odd s.1 t) * H t := by
  exact Kernel.lintegral_withDensity (Kernel.const OddState volume)
    (f := fun s t => ENNReal.ofReal (oddDensity s t))
    (ENNReal.measurable_ofReal.comp oddDensity_measurable) s hH

theorem transitionDensity_joint_measurable (i : Side) :
    Measurable (Function.uncurry (transitionDensity i)) := by
  cases i with
  | even =>
    change Measurable (fun x : ℝ × ℝ =>
      if x.1 - 1 ≤ x.2 then W x.2 * phiOdd x.2 / phiEven x.1 else 0)
    apply Measurable.ite (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd)
    · exact ((W_measurable.comp measurable_snd).mul
        (phiOdd_continuous.measurable.comp measurable_snd)).div (phiEven_measurable.comp measurable_fst)
    · exact measurable_const
  | odd =>
    change Measurable (fun x : ℝ × ℝ =>
      if max 2 (x.1 - 1) ≤ x.2 then W x.2 * phiEven x.2 / phiOdd x.1 else 0)
    apply Measurable.ite (measurableSet_le
      (measurable_const.max (measurable_fst.sub measurable_const)) measurable_snd)
    · exact ((W_measurable.comp measurable_snd).mul
        (phiEven_measurable.comp measurable_snd)).div (phiOdd_continuous.measurable.comp measurable_fst)
    · exact measurable_const

noncomputable def oddTwoStep : Kernel OddState (ℝ × ℝ) :=
  (oddToEven ⊗ₖ evenToOdd.prodMkLeft OddState).map (fun x : EvenState × OddState => (x.1.1, x.2.1))

instance oddTwoStep_isMarkovKernel : IsMarkovKernel oddTwoStep :=
  Kernel.IsMarkovKernel.map _ ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))

theorem oddTwoStep_lintegral (s : OddState) {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x, H x ∂oddTwoStep s) = ∫⁻ t, ∫⁻ u,
      ENNReal.ofReal (transitionDensity .odd s.1 t) *
        ENNReal.ofReal (transitionDensity .even t u) * H (t, u) := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [oddTwoStep, Kernel.lintegral_map _ hm _ hH]
  rw [Kernel.lintegral_compProd oddToEven (evenToOdd.prodMkLeft OddState) s
    (f := fun x : EvenState × OddState => H (x.1.1, x.2.1)) (hH.comp hm)]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, H (t.1, u.1) ∂evenToOdd t ∂oddToEven s) = _
  have hinner : ∀ t : EvenState, (∫⁻ u : OddState, H (t.1, u.1) ∂evenToOdd t) =
      ∫⁻ u, ENNReal.ofReal (transitionDensity .even t.1 u) * H (t.1, u) := by
    intro t
    rw [evenToOdd_lintegral_ratio t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left),
      evenKernel_lintegral_density t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left)]
  simp_rw [hinner]
  have hJ : Measurable (fun t : ℝ => ∫⁻ u,
      ENNReal.ofReal (transitionDensity .even t u) * H (t, u)) :=
    ((ENNReal.measurable_ofReal.comp (transitionDensity_joint_measurable .even)).mul hH).lintegral_prod_right
  rw [oddToEven_lintegral_ratio s hJ, oddKernel_lintegral_density s hJ]
  apply lintegral_congr
  intro t
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  ring

noncomputable def jointDensity (i : Side) (s : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (transitionDensity i s x.1) * ENNReal.ofReal (transitionDensity i.flip x.1 x.2)

theorem jointDensity_measurable (i : Side) (s : ℝ) : Measurable (jointDensity i s) := by
  exact (ENNReal.measurable_ofReal.comp ((transitionDensity_joint_measurable i).comp
    (measurable_const.prodMk measurable_fst))).mul
    (ENNReal.measurable_ofReal.comp (transitionDensity_joint_measurable i.flip))

theorem oddTwoStep_eq_withDensity (s : OddState) :
    oddTwoStep s = ((volume : Measure ℝ).prod volume).withDensity (jointDensity .odd s.1) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [oddTwoStep_lintegral s hH,
    lintegral_withDensity_eq_lintegral_mul _ (jointDensity_measurable .odd s.1) hH]
  have hp := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => jointDensity .odd s.1 x * H x) ((jointDensity_measurable .odd s.1).mul hH).aemeasurable
  exact hp.symm

end NumberTheoryLean.KernelDensityBridge

end

section

namespace NumberTheoryLean.JointMinorization

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights TransitionKernels FinitePathGeometry FinitePathMeasures
open KernelDensityBridge TwoStepDensityBounds

theorem transitionDensity_nonneg {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    0 ≤ transitionDensity i s t := by
  cases i with
  | even => exact evenDensity_nonneg ⟨s, hs⟩ t
  | odd => exact oddDensity_nonneg ⟨s, hs⟩ t

end NumberTheoryLean.JointMinorization

end

section

namespace NumberTheoryLean.GoodPairTransitions

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals TransitionKernels
open FinitePathGeometry FinitePathMeasures KernelDensityBridge TwoStepDensityBounds JointMinorization

theorem goodPair_density_lower {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M)
    {t u : ℝ} (hg : (t, u) ∈ goodPair s.1) :
    goodPairDensityLower M ≤ transitionDensity .odd s.1 t * transitionDensity .even t u := by
  obtain ⟨ht2, hu1, htM, huM⟩ := goodPair_bounds hM hs hg
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have heq := two_step_density_eq (i := .odd) s.2 hg.1.1 hg.2.1
  change transitionDensity .odd s.1 t * transitionDensity .even t u =
    (W t * W u) * (phiOdd u / phiOdd s.1) at heq
  rw [heq]
  have hW : (1 / M) ^ 2 ≤ W t * W u := by
    simpa only [pow_two] using mul_le_mul (W_lower ht0 htM) (W_lower hu0 huM)
      (one_div_nonneg.mpr (by linarith)) (W_pos ht0).le
  have hr : phiOdd M / sieveA ≤ phiOdd u / phiOdd s.1 := by
    calc
      _ ≤ phiOdd M / phiOdd s.1 := div_le_div_of_nonneg_left (phiOdd_pos M).le (phiOdd_pos s.1) (phiOdd_le_A s.1)
      _ ≤ _ := div_le_div_of_nonneg_right (phiOdd_antitone huM) (phiOdd_pos s.1).le
  exact mul_le_mul hW hr (div_pos (phiOdd_pos M) sieveA_pos).le (mul_pos (W_pos ht0) (W_pos hu0)).le

theorem goodPair_measure_lower {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairDensityLower M / 16) ≤ oddTwoStep s (goodPair s.1) := by
  have hdom : ENNReal.ofReal (goodPairDensityLower M) •
      ((volume : Measure ℝ).prod volume).restrict (goodPair s.1) ≤ oddTwoStep s := by
    rw [oddTwoStep_eq_withDensity, ← withDensity_const,
      ← withDensity_indicator (goodPair_measurable s.1)]
    apply withDensity_mono
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ goodPair s.1
    · rw [indicator_of_mem hx]
      change ENNReal.ofReal (goodPairDensityLower M) ≤
        ENNReal.ofReal (transitionDensity .odd s.1 x.1) * ENNReal.ofReal (transitionDensity .even x.1 x.2)
      rw [← ENNReal.ofReal_mul (transitionDensity_nonneg (i := .odd) s.2 x.1)]
      exact ENNReal.ofReal_le_ofReal (goodPair_density_lower hM s hs hx)
    · rw [indicator_of_notMem hx]
      exact zero_le
  have h := hdom (goodPair s.1)
  rw [Measure.smul_apply, Measure.restrict_apply (goodPair_measurable s.1), inter_self,
    goodPair_volume, smul_eq_mul, ← ENNReal.ofReal_mul (goodPairDensityLower_pos hM).le] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem odd_terminal_progress {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairProbability M) ≤
      oddTwoStep s {x : ℝ × ℝ | x.2 ≤ max (3 / 2) (s.1 - 3 / 2)} := by
  calc
    _ ≤ ENNReal.ofReal (goodPairDensityLower M / 16) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ ≤ oddTwoStep s (goodPair s.1) := goodPair_measure_lower hM s hs
    _ ≤ _ := measure_mono (fun x hx => goodPair_terminal hx)

end NumberTheoryLean.GoodPairTransitions

end

section

namespace NumberTheoryLean.FirstHitKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open FinitePathMeasures

theorem regenerationStateSet_measurable : MeasurableSet regenerationStateSet := by
  apply measurableSet_sum_iff.mpr
  constructor
  · exact MeasurableSet.empty
  · exact measurableSet_le measurable_subtype_coe measurable_const

theorem regenerationSet_measurable : MeasurableSet regenerationSet :=
  regenerationStateSet_measurable.preimage measurable_fst

end NumberTheoryLean.FirstHitKernels

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityConservation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.IncomingDensityIdentities
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open Erdos970Dependency.InvariantDensities

noncomputable def incomingOdd (t s : ℝ) : ℝ :=
  oddDensity s * transitionDensity .odd s t
noncomputable def incomingEven (t s : ℝ) : ℝ :=
  evenDensity s * transitionDensity .even s t

end Erdos970Dependency.IncomingDensityIdentities

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StateKernelInvariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OrdinaryKernelInvariance
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.IncomingDensityIdentities

noncomputable def evenLift (s : ℝ) : EvenState := ⟨max (198 / 100) s, le_max_left _ _⟩
noncomputable def oddLift (s : ℝ) : OddState := ⟨max (95 / 100) s, le_max_left _ _⟩

theorem evenLift_measurable : Measurable evenLift :=
  (measurable_const.max measurable_id).subtype_mk

theorem oddLift_measurable : Measurable oddLift :=
  (measurable_const.max measurable_id).subtype_mk

noncomputable def evenRealKernel : Kernel ℝ ℝ := evenKernel.comap evenLift evenLift_measurable
noncomputable def oddRealKernel : Kernel ℝ ℝ := oddKernel.comap oddLift oddLift_measurable

instance evenRealKernel_isMarkovKernel : IsMarkovKernel evenRealKernel := by unfold evenRealKernel; infer_instance
instance oddRealKernel_isMarkovKernel : IsMarkovKernel oddRealKernel := by unfold oddRealKernel; infer_instance

end Erdos970Dependency.OrdinaryKernelInvariance

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateKernelInvariance
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.OrdinaryKernelInvariance

noncomputable def evenStateMeasure : Measure EvenState := evenMeasure.map evenLift
noncomputable def oddStateMeasure : Measure OddState := oddMeasure.map oddLift

noncomputable def stateMeasure : Measure State :=
  evenStateMeasure.map Sum.inl + oddStateMeasure.map Sum.inr

end Erdos970Dependency.StateKernelInvariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityComparison
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InitialDensityFormulas
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.WeightFutureIntegrals NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.RegenerationTails NumberTheoryLean.TwoStepDensityBounds
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.OrdinaryKernelInvariance

noncomputable def initialTwoDensity (s : EvenState) (t : ℝ) : ℝ :=
  (Ici (2 : ℝ)).indicator (fun t ↦ (W t * phiEven t / phiEven s.1) * wMass (s.1 - 1) (t + 1)) t

noncomputable def initialIncoming (s : EvenState) (t u : ℝ) : ℝ :=
  TransitionKernels.evenDensity s u * transitionDensity .odd (oddLift u).1 t

noncomputable def regTwoIncoming (u y : ℝ) : ℝ :=
  TransitionKernels.oddDensity regenerationState y * transitionDensity .even (evenLift y).1 u

noncomputable def regThreeIncoming (t u : ℝ) : ℝ :=
  regTwoDensity u * transitionDensity .odd (oddLift u).1 t

end Erdos970Dependency.InitialDensityFormulas

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.MarginalDensityMeasures
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.KernelDensityBridge NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InitialDensityFormulas

noncomputable def initialTwoMeasure (s : EvenState) : Measure ℝ := oddRealKernel ∘ₘ evenKernel s
noncomputable def regTwoMeasure : Measure ℝ := evenRealKernel ∘ₘ oddKernel regenerationState
noncomputable def regThreeMeasure : Measure ℝ := oddRealKernel ∘ₘ regTwoMeasure

instance initialTwoMeasure_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (initialTwoMeasure s) := by
  unfold initialTwoMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
instance regTwoMeasure_isProbabilityMeasure : IsProbabilityMeasure regTwoMeasure := by unfold regTwoMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
instance regThreeMeasure_isProbabilityMeasure : IsProbabilityMeasure regThreeMeasure := by unfold regThreeMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

end Erdos970Dependency.MarginalDensityMeasures

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairedHitting
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedHitting

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures KernelDensityBridge GoodPairTransitions

noncomputable def pairedOdd : Kernel OddState OddState := evenToOdd ∘ₖ oddToEven

instance pairedOdd_isMarkovKernel : IsMarkovKernel pairedOdd := by unfold pairedOdd; infer_instance

theorem pairedOdd_map_ratio (s : OddState) :
    (pairedOdd s).map (Subtype.val : OddState → ℝ) = (oddTwoStep s).map Prod.snd := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [pairedOdd, Kernel.comp_eq_snd_compProd, Kernel.snd_apply, oddTwoStep,
    Kernel.map_apply _ hm, Measure.map_map measurable_snd hm,
    Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem pairedOdd_progress {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairProbability M) ≤
      pairedOdd s {t : OddState | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)} := by
  have heq := congrArg (fun μ : Measure ℝ => μ (Iic (max (3 / 2) (s.1 - 3 / 2)))) (pairedOdd_map_ratio s)
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic,
    Measure.map_apply measurable_snd measurableSet_Iic] at heq
  change pairedOdd s {t : OddState | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)} =
    oddTwoStep s {x : ℝ × ℝ | x.2 ≤ max (3 / 2) (s.1 - 3 / 2)} at heq
  rw [heq]
  exact odd_terminal_progress hM s hs

noncomputable def hitBy : ℕ → OddState → ℝ≥0∞
  | 0, _ => 0
  | n + 1, s => ∫⁻ t, if t.1 ≤ 3 then 1 else hitBy n t ∂pairedOdd s

theorem hitBy_lower {M : ℝ} (hM : 4 ≤ M) (n : ℕ) (hn : 0 < n)
    (s : OddState) (hsM : s.1 ≤ M) (hsn : s.1 ≤ 3 + (3 / 2) * (n : ℝ)) :
    (ENNReal.ofReal (goodPairProbability M)) ^ n ≤ hitBy n s := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    let q : ℝ≥0∞ := ENNReal.ofReal (goodPairProbability M)
    let B : Set OddState := {t | t.1 ≤ max (3 / 2) (s.1 - 3 / 2)}
    have hB : MeasurableSet B := measurableSet_le measurable_subtype_coe measurable_const
    have hq1 : q ≤ 1 := by
      change ENNReal.ofReal (goodPairProbability M) ≤ 1
      exact (ENNReal.ofReal_le_one).mpr (goodPairProbability_le_one M)
    have hpoint : ∀ t ∈ B, q ^ n ≤ (if t.1 ≤ 3 then 1 else hitBy n t) := by
      intro t ht
      have htbound : t.1 ≤ max (3 / 2) (s.1 - 3 / 2) := ht
      have htM : t.1 ≤ M := le_trans htbound (max_le (by linarith) (by linarith))
      have htn : t.1 ≤ 3 + (3 / 2) * (n : ℝ) := by
        apply le_trans htbound
        apply max_le
        · nlinarith [Nat.cast_nonneg (α := ℝ) n]
        · push_cast at hsn
          linarith
      by_cases htR : t.1 ≤ 3
      · rw [ite_eq_left htR]
        exact pow_le_one₀ zero_le hq1
      · rw [ite_eq_right htR]
        have hn0 : 0 < n := by
          by_contra h
          have hnz : n = 0 := Nat.eq_zero_of_not_pos h
          subst n
          norm_num at htn
          exact htR htn
        exact ih hn0 t htM htn
    change q ^ (n + 1) ≤ _
    calc
      q ^ (n + 1) = q ^ n * q := pow_succ q n
      _ ≤ q ^ n * pairedOdd s B := mul_le_mul le_rfl (pairedOdd_progress hM s hsM) zero_le zero_le
      _ = ∫⁻ t in B, q ^ n ∂pairedOdd s := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in B, (if t.1 ≤ 3 then 1 else hitBy n t) ∂pairedOdd s := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hB] with t ht
        exact hpoint t ht
      _ ≤ ∫⁻ t, (if t.1 ≤ 3 then 1 else hitBy n t) ∂pairedOdd s := setLIntegral_le_lintegral _ _
      _ = hitBy (n + 1) s := rfl

theorem compact_paired_hit {M : ℝ} (hM : 4 ≤ M) : ∃ n : ℕ, 0 < n ∧ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
    ∀ s : OddState, s.1 ≤ M → ENNReal.ofReal p ≤ hitBy n s := by
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨n + 1, by omega, goodPairProbability M ^ (n + 1),
    pow_pos (goodPairProbability_pos hM) _, pow_le_one₀ (goodPairProbability_pos hM).le (goodPairProbability_le_one M), ?_⟩
  intro s hs
  rw [ENNReal.ofReal_pow (goodPairProbability_pos hM).le]
  apply hitBy_lower hM (n + 1) (by omega) s hs
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end NumberTheoryLean.PairedHitting

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PairedDrift
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures KernelDensityBridge
open RegenerationDrift CompactExponentialMoments PairedHitting

noncomputable def V (s : OddState) : ℝ := Real.exp s.1

theorem V_pos (s : OddState) : 0 < V s := Real.exp_pos _
theorem V_one_le (s : OddState) : 1 ≤ V s := Real.one_le_exp_iff.mpr (by linarith [s.2])
theorem V_measurable : Measurable V := Real.measurable_exp.comp measurable_subtype_coe

theorem paired_drift : ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 < C ∧ ∀ s : OddState,
    (∫⁻ t, ENNReal.ofReal (V t) ∂pairedOdd s) ≤ ENNReal.ofReal a * ENNReal.ofReal (V s) + ENNReal.ofReal C := by
  obtain ⟨C, hC, he, ho⟩ := kernel_global_drift
  have hκ := driftFactor_pos
  have hκ1 := driftFactor_lt_one
  have he' : ∀ s : EvenState, (∫⁻ t : OddState, ENNReal.ofReal (Real.exp t.1) ∂evenToOdd s) ≤
      ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C := by
    intro s
    rw [evenToOdd_lintegral_ratio s (H := fun x : ℝ => ENNReal.ofReal (Real.exp x)) (ENNReal.measurable_ofReal.comp Real.measurable_exp)]
    have h := ENNReal.ofReal_le_ofReal (he s).2
    rw [ofReal_integral_eq_lintegral_ofReal (he s).1 (Eventually.of_forall (fun t => (Real.exp_pos t).le)),
      ENNReal.ofReal_add (mul_pos hκ (Real.exp_pos _)).le hC.le, ENNReal.ofReal_mul hκ.le] at h
    exact h
  have ho' : ∀ s : OddState, (∫⁻ t : EvenState, ENNReal.ofReal (Real.exp t.1) ∂oddToEven s) ≤
      ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C := by
    intro s
    rw [oddToEven_lintegral_ratio s (H := fun x : ℝ => ENNReal.ofReal (Real.exp x)) (ENNReal.measurable_ofReal.comp Real.measurable_exp)]
    have h := ENNReal.ofReal_le_ofReal (ho s).2
    rw [ofReal_integral_eq_lintegral_ofReal (ho s).1 (Eventually.of_forall (fun t => (Real.exp_pos t).le)),
      ENNReal.ofReal_add (mul_pos hκ (Real.exp_pos _)).le hC.le, ENNReal.ofReal_mul hκ.le] at h
    exact h
  refine ⟨driftFactor ^ 2, (1 + driftFactor) * C, sq_pos_of_pos hκ, by nlinarith,
    mul_pos (by linarith) hC, ?_⟩
  intro s
  rw [pairedOdd, Kernel.lintegral_comp evenToOdd oddToEven s (g := fun t : OddState => ENNReal.ofReal (V t)) (ENNReal.measurable_ofReal.comp V_measurable)]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, ENNReal.ofReal (Real.exp u.1) ∂evenToOdd t ∂oddToEven s) ≤ _
  have hEV : Measurable (fun t : EvenState => ENNReal.ofReal (Real.exp t.1)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_subtype_coe)
  calc
    _ ≤ ∫⁻ t : EvenState, ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp t.1) + ENNReal.ofReal C ∂oddToEven s :=
      lintegral_mono he'
    _ = ENNReal.ofReal driftFactor * (∫⁻ t : EvenState, ENNReal.ofReal (Real.exp t.1) ∂oddToEven s) + ENNReal.ofReal C := by
      rw [lintegral_add_left (f := fun t : EvenState => ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp t.1)) (measurable_const.mul hEV) (fun _ => ENNReal.ofReal C), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp
    _ ≤ ENNReal.ofReal driftFactor * (ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C) + ENNReal.ofReal C :=
      add_le_add (mul_le_mul le_rfl (ho' s) zero_le zero_le) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_pow hκ.le, ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + driftFactor),
        ENNReal.ofReal_add zero_le_one hκ.le, ENNReal.ofReal_one]
      dsimp [V]
      ring

end NumberTheoryLean.PairedDrift

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostProcess

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open JointMinorization RegenerationTails PairedHitting

noncomputable def pairedDraws : Kernel OddState (EvenState × OddState) :=
  oddToEven ⊗ₖ evenToOdd.prodMkLeft OddState

instance pairedDraws_isMarkovKernel : IsMarkovKernel pairedDraws := by unfold pairedDraws; infer_instance

noncomputable def pairUpdate (x : OddCost × (EvenState × OddState)) : OddCost :=
  (x.2.2, x.1.2 + cost x.2.1.1 + cost x.2.2.1)

theorem pairUpdate_measurable : Measurable pairUpdate :=
  (measurable_snd.comp measurable_snd).prodMk
    (((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

noncomputable def pairedCostKernel : Kernel OddCost OddCost :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map pairUpdate

instance pairedCostKernel_isMarkovKernel : IsMarkovKernel pairedCostKernel :=
  Kernel.IsMarkovKernel.map _ pairUpdate_measurable

theorem pairedCostKernel_apply (z : OddCost) {B : Set OddCost} (hB : MeasurableSet B) :
    pairedCostKernel z B = pairedDraws z.1 {x | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈ B} := by
  rw [pairedCostKernel, Kernel.map_apply' _ pairUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (pairUpdate_measurable hB), Kernel.id_apply, lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (pairUpdate_measurable hB)

theorem pairedCost_map_state (z : OddCost) : (pairedCostKernel z).map Prod.fst = pairedOdd z.1 := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB, pairedCostKernel_apply _ (measurable_fst hB),
    pairedOdd, Kernel.comp_eq_snd_compProd, Kernel.snd_apply' _ _ hB]
  rfl

def shiftCost (T : ℝ) (z : OddCost) : OddCost := (z.1, z.2 + T)

theorem shiftCost_measurable (T : ℝ) : Measurable (shiftCost T) :=
  measurable_fst.prodMk (measurable_snd.add measurable_const)

end NumberTheoryLean.PairedCostProcess

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.RegenerationTails

noncomputable def sourceMark (t : EvenState) : Bool := if (209/100:ℝ) ≤ t.1 ∧ t.1 ≤ 213/100 then true else false

lemma sourceMark_measurable : Measurable sourceMark := by
  unfold sourceMark
  exact Measurable.ite (measurableSet_Icc.preimage measurable_subtype_coe) measurable_const measurable_const

abbrev MarkedOddCost := Bool × OddCost

noncomputable def markedPairUpdate (x : OddCost × (EvenState × OddState)) : MarkedOddCost :=
  (sourceMark x.2.1,pairUpdate x)

lemma markedPairUpdate_measurable : Measurable markedPairUpdate :=
  (sourceMark_measurable.comp (measurable_fst.comp measurable_snd)).prodMk pairUpdate_measurable

noncomputable def markedPairKernel : Kernel OddCost MarkedOddCost :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map markedPairUpdate

instance markedPairKernel_isMarkovKernel : IsMarkovKernel markedPairKernel :=
  Kernel.IsMarkovKernel.map _ markedPairUpdate_measurable

def markedShift (a : ℝ) (z : MarkedOddCost) : MarkedOddCost := (z.1,shiftCost a z.2)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegenerationTails
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelDensityBridge

noncomputable def markProbability : ℝ≥0∞ :=
  oddKernel regenerationState (Icc (209/100:ℝ) (213/100))

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairedCostGrouping
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostGrouping

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess

def embedOdd (z : OddCost) : CostState := (.inr z.1, z.2)

theorem embedOdd_measurable : Measurable embedOdd :=
  (measurable_inr.comp measurable_fst).prodMk measurable_snd

theorem costKernel_eq_map (z : CostState) : costKernel z =
    (stateKernel z.1).map (fun s => (s, z.2 + cost (stateRatio s))) := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  ext B hB
  rw [costKernel_apply _ hB, Measure.map_apply hm hB]
  rfl

end NumberTheoryLean.PairedCostGrouping

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerativeOddOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.RegenerativeOddOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting
open NumberTheoryLean.RegenerationTails NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance

noncomputable def ratioVisits : Kernel OddState State :=
  oddToEven.map Sum.inl + pairedOdd.map Sum.inr

instance ratioVisits_isFiniteKernel : IsFiniteKernel ratioVisits := by unfold ratioVisits; infer_instance

end Erdos970Dependency.RegenerativeOddOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationAge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CycleRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels PairedCostProcess RegenerationTails

noncomputable def shiftKernel (a : ℝ) : Kernel OddCost OddCost :=
  Kernel.deterministic (shiftCost a) (shiftCost_measurable a)

end NumberTheoryLean.CycleRegeneration

end

section

namespace NumberTheoryLean.MarkedCycleLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open PairedCostProcess CycleRegeneration

abbrev MarkedReturn := ℕ × OddCost

def markReturn (n : ℕ) (z : OddCost) : MarkedReturn := (2 * (n + 1), z)

end NumberTheoryLean.MarkedCycleLaw

end

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping

noncomputable def pairSampling : Kernel OddCost (OddCost × (EvenState × OddState)) :=
  Kernel.id ×ₖ pairedDraws.prodMkRight ℝ

instance pairSampling_isMarkovKernel : IsMarkovKernel pairSampling := by unfold pairSampling; infer_instance

noncomputable def evenVisitMap (x : OddCost × (EvenState × OddState)) : CostState :=
  (.inl x.2.1, x.1.2 + cost x.2.1.1)

noncomputable def oddVisitMap (x : OddCost × (EvenState × OddState)) : CostState :=
  (.inr x.2.2, x.1.2 + cost x.2.1.1 + cost x.2.2.1)

noncomputable def evenVisit : Kernel OddCost CostState := pairSampling.map evenVisitMap
noncomputable def oddVisit : Kernel OddCost CostState := pairSampling.map oddVisitMap

noncomputable def pairVisits : Kernel OddCost CostState := evenVisit + oddVisit

end NumberTheoryLean.CycleOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.CycleResponse

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation
open AbsorptionCutoff.Renewal

abbrev Test := ℝ × State → ℝ

end NumberTheoryLean.CycleResponse



namespace NumberTheoryLean.AdmissibleCycleTests

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation CycleResponse

noncomputable def mask (B : Set (ℝ × State)) (F : Test) : Test := B.indicator F

def HasCompactBound (F : Test) : Prop := ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
  (∀ x, ‖F x‖ ≤ C) ∧ (∀ x, M < |x.1| → F x = 0)

inductive Admissible : Test → Prop
  | base {F : Test} (hF : Measurable F) (hc : ∀ s : State, Continuous (fun u => F (u, s)))
      (hb : HasCompactBound F) : Admissible F
  | upper {F : Test} (hF : Admissible F) (a : ℝ) : Admissible (mask {x | x.1 ≤ a} F)
  | upperOpen {F : Test} (hF : Admissible F) (a : ℝ) : Admissible (mask {x | x.1 < a} F)
  | state {F : Test} (hF : Admissible F) (B : Set State) (hB : MeasurableSet B) :
      Admissible (mask (Prod.snd ⁻¹' B) F)
  | arrival {F : Test} (hF : Admissible F) (ell : ℝ) (hell : 0 < ell) :
      Admissible (mask {x | stateRatio x.2 < Real.exp x.1 / ell} F)
  | add {F G : Test} (hF : Admissible F) (hG : Admissible G) : Admissible (fun x => F x + G x)
  | scale {F : Test} (hF : Admissible F) (c : ℝ) : Admissible (fun x => c * F x)

end NumberTheoryLean.AdmissibleCycleTests



namespace NumberTheoryLean.OccupationDecomposition

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CycleOccupation KernelPotential

noncomputable def pairedOccupation : Kernel OddCost CostState := potential pairVisits pairedCostKernel

noncomputable def oddEmbeddingKernel : Kernel OddCost CostState :=
  Kernel.deterministic embedOdd embedOdd_measurable

noncomputable def fullOccupation : Kernel CostState CostState :=
  Kernel.sum (fun n : ℕ => costKernel ^ (n + 1))

end NumberTheoryLean.OccupationDecomposition



namespace NumberTheoryLean.OccupationRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CycleRegeneration CycleOccupation
open OccupationDecomposition CycleResponse

def shiftFullCost (a : ℝ) (z : CostState) : CostState := (z.1, z.2 + a)

theorem shiftFullCost_measurable (a : ℝ) : Measurable (shiftFullCost a) :=
  measurable_fst.prodMk (measurable_snd.add measurable_const)

noncomputable def shiftFullKernel (a : ℝ) : Kernel CostState CostState :=
  Kernel.deterministic (shiftFullCost a) (shiftFullCost_measurable a)

end NumberTheoryLean.OccupationRegeneration



namespace NumberTheoryLean.CycleResponseFubini

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CycleOccupation CycleResponse AdmissibleCycleTests

noncomputable def ageShear (x : CostState × ℝ) : CostState × ℝ := (x.1, x.2 - x.1.2)

end NumberTheoryLean.CycleResponseFubini



namespace NumberTheoryLean.OccupationConstant

open Set MeasureTheory
open FinitePathMeasures CycleResponse CycleResponseFubini AdmissibleCycleTests
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance

noncomputable def integratedStateTest (F : Test) (s : State) : ℝ := ∫ u : ℝ, F (u, s)

end NumberTheoryLean.OccupationConstant



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InitialOddDraw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialOddDraw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open KernelDensityBridge PairedDrift CompactExponentialMoments

noncomputable def firstOddUpdate (t : OddState) : OddCost := (t, cost t.1)

noncomputable def firstOdd : Kernel EvenState OddCost := evenToOdd.map firstOddUpdate

end NumberTheoryLean.InitialOddDraw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OnePairCost
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities

noncomputable def evenCost (s : ℝ) : ℝ := evenDensity s * cost s
noncomputable def oddCost (s : ℝ) : ℝ := oddDensity s * cost s

noncomputable def costMass : ℝ := (∫ s, evenCost s) + ∫ s, oddCost s

end Erdos970Dependency.InvariantCostBound

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OnePairCost
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CycleOccupation
open Erdos970Dependency.RawStateCost

noncomputable def pairIncrement (z : OddCost) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂pairVisits z

end Erdos970Dependency.OnePairCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationBandBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialOccupation

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CycleOccupation OccupationDecomposition KernelPotential
open InitialOddDraw

noncomputable def evenEmbeddingKernel : Kernel EvenState CostState :=
  Kernel.deterministic (fun s : EvenState => (.inl s, 0)) (measurable_inl.prodMk measurable_const)

end NumberTheoryLean.InitialOccupation

end

section

namespace NumberTheoryLean.FullOccupationCovariance

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CycleResponse AdmissibleCycleTests
open OccupationDecomposition OccupationRegeneration InitialOccupation

noncomputable def fullResponse (F : Test) (v : ℝ) : ℝ :=
  ∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))

end NumberTheoryLean.FullOccupationCovariance

end

section

namespace NumberTheoryLean.EvenStartOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CycleResponse AdmissibleCycleTests OccupationDecomposition
open InitialOccupation
open FullOccupationCovariance

noncomputable def evenResponse (F : Test) (s : EvenState) (v : ℝ) : ℝ :=
  F (v, .inl s) + ∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (.inl s, 0)

end NumberTheoryLean.EvenStartOccupation

end

section

namespace NumberTheoryLean.NormalizedOccupationLimit

open Filter Set MeasureTheory
open scoped Topology
open FinitePathMeasures CycleResponse AdmissibleCycleTests OccupationConstant
open EvenStartOccupation FullOccupationCovariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.StateKernelInvariance

noncomputable def invariantAverage (F : Test) : ℝ :=
  (∫ s : State, integratedStateTest F s ∂stateMeasure) / costMass

end NumberTheoryLean.NormalizedOccupationLimit

end

section

namespace NumberTheoryLean.RegenerationBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails
open CycleOccupation OccupationDecomposition OccupationRegeneration
open AbsorptionCutoff.Renewal
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance

noncomputable def stateBandReward (Q : State → ℝ≥0∞) (v h : ℝ) : CostState → ℝ≥0∞ :=
  (Prod.snd ⁻¹' Icc v (v + h)).indicator (fun y => Q y.1)

end NumberTheoryLean.RegenerationBandBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CostPrefixTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CostPrefixTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationDecomposition OccupationRegeneration
open InitialOccupation FullOccupationCovariance KernelPotential

instance costKernel_pow_markov (n : ℕ) : IsMarkovKernel (costKernel ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel CostState CostState); infer_instance
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def stateProjection : Kernel CostState State := Kernel.deterministic Prod.fst measurable_fst

noncomputable def inclusiveOccupation : Kernel CostState CostState := Kernel.id + fullOccupation

noncomputable def prefixOccupation (n : ℕ) : Kernel CostState CostState := inclusiveOccupation ∘ₖ (costKernel ^ n)

end NumberTheoryLean.CostPrefixTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BandShiftTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BandShiftTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures OccupationRegeneration RegenerationBandBounds CostPrefixTransport

noncomputable def bandExpectation (Q : State → ℝ≥0∞) (v h : ℝ) (z : CostState) : ℝ≥0∞ :=
  ∫⁻ y, stateBandReward Q v h y ∂inclusiveOccupation z

noncomputable def zeroBandExpectation (Q : State → ℝ≥0∞) (v h : ℝ) (s : State) : ℝ≥0∞ :=
  bandExpectation Q v h (s, 0)

end NumberTheoryLean.BandShiftTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EvenInverseBands
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InvariantInverseWeights

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights TransitionKernels FinitePathMeasures
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

noncomputable def stateWeight : State → ℝ :=
  Sum.elim (fun s : EvenState => phiEven s.1) (fun s : OddState => phiOdd s.1)

theorem stateWeight_pos (s : State) : 0 < stateWeight s := by
  cases s with
  | inl s => exact phiEven_pos (by linarith [s.2])
  | inr s => exact phiOdd_pos s.1

theorem stateWeight_measurable : Measurable stateWeight :=
  (phiEven_measurable.comp measurable_subtype_coe).sumElim
    (phiOdd_continuous.measurable.comp measurable_subtype_coe)

noncomputable def inverseWeightCutoff (L : ℝ) : State → ℝ≥0∞ :=
  {s | stateRatio s < L}.indicator (fun s => (ENNReal.ofReal (stateWeight s))⁻¹)

end NumberTheoryLean.InvariantInverseWeights

end

section

namespace NumberTheoryLean.FirstStepInverseWeight

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathMeasures
open KernelDensityBridge InvariantInverseWeights

noncomputable def firstDensityConstant : ℝ := 3 / phiEven (23 / 10)

end NumberTheoryLean.FirstStepInverseWeight

end

section

namespace NumberTheoryLean.RegeneratingInverseBands

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open RegenerationBandBounds InvariantInverseWeights FirstStepInverseWeight

noncomputable def gapValue (v : ℝ) (z : CostState) : ℝ := Real.exp (v - z.2)

noncomputable def inverseArrivalBand (v R ell : ℝ) : CostState → ℝ≥0∞ :=
  {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧
    stateRatio z.1 < gapValue v z / ell}.indicator
    (fun z => (ENNReal.ofReal (stateWeight z.1))⁻¹)

end NumberTheoryLean.RegeneratingInverseBands

end

section

namespace NumberTheoryLean.WeightedGapTail

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open InvariantInverseWeights RegeneratingInverseBands

noncomputable def tailReward (c v ell : ℝ) (N : ℕ) : CostState → ℝ≥0∞ :=
  {z | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell}.indicator
    (fun z => ENNReal.ofReal ((gapValue v z) ^ 2 * Real.exp (-c * gapValue v z)) *
      (ENNReal.ofReal (stateWeight z.1))⁻¹)

end NumberTheoryLean.WeightedGapTail

end

section

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.RegenerationBandBounds NumberTheoryLean.BandShiftTransport
open NumberTheoryLean.CostPrefixTransport
open Erdos970Dependency.StateKernelInvariance

def highStates (T : ℝ) : Set State := {s | T ≤ stateRatio s}

noncomputable def highReward (T : ℝ) : State → ℝ≥0∞ :=
  (highStates T).indicator (fun _ => 1)

def highBand (T v h : ℝ) : Set CostState :=
  {z | T ≤ stateRatio z.1 ∧ z.2 ∈ Icc v (v+h)}

end ErdosHighRatioBandTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicWeightKernel

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathGeometry
open FinitePathMeasures InvariantInverseWeights
open KernelWeightTransform CostPrefixTransport OccupationDecomposition

noncomputable def harmonicWeight : PositiveWeight CostState where
  value z := ENNReal.ofReal (Real.exp (-2 * z.2) / stateWeight z.1)
  measurable_value := ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).div
      (stateWeight_measurable.comp measurable_fst))
  ne_zero z := (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) (stateWeight_pos z.1))).ne'
  ne_top _ := ENNReal.ofReal_ne_top

noncomputable def harmonicKernel : Kernel CostState CostState := conjugate costKernel harmonicWeight

noncomputable def correction (i : Side) (s t : ℝ) : ℝ :=
  (t / (t + 1)) ^ 2 * (weight i s / weight i.flip t)

noncomputable def harmonicRatioDensity (i : Side) (s : ℝ) : ℝ → ℝ≥0∞ :=
  (Ici (minRatio i s)).indicator (fun t => ENNReal.ofReal (1 / (t + 1)))

end NumberTheoryLean.HarmonicWeightKernel

end

section

namespace NumberTheoryLean.HarmonicKernelDensities

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open KernelDensityBridge InvariantInverseWeights KernelWeightTransform HarmonicWeightKernel
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

noncomputable def evenUpdateReal (T t : ℝ) : CostState := (.inr (oddLift t), T + cost t)
noncomputable def oddUpdateReal (T t : ℝ) : CostState := (.inl (evenLift t), T + cost t)

end NumberTheoryLean.HarmonicKernelDensities

end

section

namespace NumberTheoryLean.ArrivalKernelGeometry

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open RegeneratingInverseBands KernelDensityBridge
open HarmonicWeightKernel KernelWeightTransform

noncomputable def currentExponent (v : ℝ) (z : CostState) : ℝ := gapValue v z / stateRatio z.1

theorem gapValue_measurable (v : ℝ) : Measurable (gapValue v) :=
  Real.measurable_exp.comp (measurable_const.sub measurable_snd)

theorem currentExponent_measurable (v : ℝ) : Measurable (currentExponent v) :=
  (gapValue_measurable v).div (stateRatio_measurable.comp measurable_fst)

def arrivalSet (v ell : ℝ) : Set CostState := {z | ell < currentExponent v z}

theorem arrivalSet_measurable (v ell : ℝ) : MeasurableSet (arrivalSet v ell) :=
  measurableSet_lt measurable_const (currentExponent_measurable v)

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_AdmittedHarmonicPaths
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHarmonicPaths

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open HarmonicWeightKernel KernelWeightTransform

noncomputable def admittedTilted (v ell : ℝ) : Kernel CostState CostState :=
  costKernel.restrict (arrivalSet_measurable v ell)

noncomputable def admittedHarmonic (v ell : ℝ) : Kernel CostState CostState :=
  harmonicKernel.restrict (arrivalSet_measurable v ell)

instance admittedTilted_isFiniteKernel (v ell : ℝ) : IsFiniteKernel (admittedTilted v ell) := by
  unfold admittedTilted
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.AdmittedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

def lowDomain (v ell S : ℝ) : Set CostState := arrivalSet v ell ∩ {z | stateRatio z.1 ≤ S}

theorem lowDomain_measurable (v ell S : ℝ) : MeasurableSet (lowDomain v ell S) :=
  (arrivalSet_measurable v ell).inter (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const)

noncomputable def lowKernel (K : Kernel CostState CostState) (v ell S : ℝ) : Kernel CostState CostState :=
  K.restrict (lowDomain_measurable v ell S)

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ContinuousRatioBins.ratioMeasure_noAtoms _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeTiltMonotone

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltBounds DerivativeWeights TransitionKernels
open HarmonicExponentMeasure

theorem multiplier_measurable (i : Side) (s : ℝ) : Measurable (multiplier i s) := by
  have hw : Measurable (weight i.flip) := by
    cases i with
    | even => exact phiOdd_continuous.measurable
    | odd => exact phiEven_measurable
  exact ((((measurable_id.add_const 1).div measurable_id).pow_const 2).mul hw).div_const (weight i s)

theorem minRatio_pos {i : Side} {s : ℝ} (hs : Valid i s) : 0 < minRatio i s :=
  valid_pos (valid_next hs le_rfl)

theorem multiplier_antitone {i : Side} {s : ℝ} (hs : Valid i s) :
    AntitoneOn (multiplier i s) (Ici (minRatio i s)) := by
  intro u hu v hv huv
  have hu0 := valid_pos (valid_next hs hu)
  have hv0 := valid_pos (valid_next hs hv)
  have hphi : weight i.flip v ≤ weight i.flip u := by
    cases i with
    | even => exact phiOdd_antitone huv
    | odd =>
      have h2 : 2 ≤ minRatio .odd s := le_max_left _ _
      apply phiEven_strictAntiOn.antitoneOn
      · change 1 < u
        change minRatio .odd s ≤ u at hu
        linarith
      · change 1 < v
        change minRatio .odd s ≤ v at hv
        linarith
      · exact huv
  have hq : (v+1)/v ≤ (u+1)/u := by
    have h := one_div_le_one_div_of_le hu0 huv
    have heU : (u+1)/u = 1+1/u := by field_simp
    have heV : (v+1)/v = 1+1/v := by field_simp
    rw [heU,heV]
    linarith
  have hqU : 0 ≤ (u+1)/u := (div_pos (by linarith) hu0).le
  have hqV : 0 ≤ (v+1)/v := (div_pos (by linarith) hv0).le
  have hsq : ((v+1)/v)^2 ≤ ((u+1)/u)^2 := by nlinarith
  unfold multiplier
  apply div_le_div_of_nonneg_right _ (weight_pos hs).le
  exact mul_le_mul hsq hphi (weight_pos (valid_next hs hv)).le (sq_nonneg _)

theorem multiplier_nonnegative_ae {i : Side} {s : ℝ} (hs : Valid i s) :
    0 ≤ᵐ[ratioMeasure (minRatio i s)] multiplier i s :=
  (ratioMeasure_ae_above _).mono (fun _ ht => (multiplier_pos hs (valid_next hs ht)).le)

theorem weighted_ratio_density_eq {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    (Ici (minRatio i s)).indicator (fun t => ENNReal.ofReal (1/(t+1)) * ENNReal.ofReal (multiplier i s t)) t =
      ENNReal.ofReal (transitionDensity i s t) := by
  classical
  by_cases ht : minRatio i s ≤ t
  · have ht0 := valid_pos (valid_next hs ht)
    rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(t+1)), transitionDensity, tailDensity,
      indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    congr 1
    unfold multiplier W
    field_simp
  · rw [indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht), transitionDensity, tailDensity,
      indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht), ENNReal.ofReal_zero]

theorem transitionDensity_mass {i : Side} {s : ℝ} (hs : Valid i s) :
    (∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity i s t)) = 1 := by
  cases i with
  | even =>
    let x : EvenState := ⟨s,hs⟩
    have h := evenKernel_apply x univ
    simp only [setLIntegral_univ, measure_univ] at h
    exact h.symm
  | odd =>
    let x : OddState := ⟨s,hs⟩
    have h := oddKernel_apply x univ
    simp only [setLIntegral_univ, measure_univ] at h
    exact h.symm

theorem multiplier_ratio_integral {i : Side} {s : ℝ} (hs : Valid i s) :
    (∫⁻ t, ENNReal.ofReal (multiplier i s t) ∂ratioMeasure (minRatio i s)) = 1 := by
  rw [ratioMeasure, lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal (1/(t+1)))
    (g := fun t : ℝ => ENNReal.ofReal (multiplier i s t)) (by fun_prop)
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s)), ← lintegral_indicator measurableSet_Ici]
  calc
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity i s t) := lintegral_congr (fun t => weighted_ratio_density_eq hs t)
    _ = 1 := transitionDensity_mass hs

end NumberTheoryLean.PrimeTiltMonotone



namespace NumberTheoryLean.PrimeRatioMeasure

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioBins HarmonicExponentMeasure

noncomputable def primeAtoms (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Finset ℝ := by
  classical
  exact (children w ell S i s r cap closed).image (childRatio w r)

noncomputable def finitePrimeMeasure (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Measure ℝ :=
  ∑ p ∈ children w ell S i s r cap closed, ENNReal.ofReal (p : ℝ)⁻¹ • Measure.dirac (childRatio w r p)

theorem finitePrimeMeasure_apply (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool)
    {B : Set ℝ} [DecidablePred (fun x => x ∈ B)] (hB : MeasurableSet B) :
    finitePrimeMeasure w ell S i s r cap closed B =
      ∑ p ∈ children w ell S i s r cap closed, if childRatio w r p ∈ B then ENNReal.ofReal (p : ℝ)⁻¹ else 0 := by
  classical
  simp only [finitePrimeMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hB, Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

theorem finitePrimeMeasure_support (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) :
    ∀ᵐ t ∂finitePrimeMeasure w ell S i s r cap closed, t ∈ primeAtoms w ell S i s r cap closed := by
  classical
  apply ae_iff.mpr
  change finitePrimeMeasure w ell S i s r cap closed ((↑(primeAtoms w ell S i s r cap closed) : Set ℝ)ᶜ) = 0
  rw [finitePrimeMeasure_apply _ _ _ _ _ _ _ _ (Finset.finite_toSet _).measurableSet.compl]
  apply Finset.sum_eq_zero
  intro p hp
  have hm : childRatio w r p ∈ primeAtoms w ell S i s r cap closed := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  simp only [Set.mem_compl_iff, Finset.mem_coe, hm, not_true_eq_false, ite_false, if_false]

theorem primeAtoms_above (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) :
    ∀ t ∈ primeAtoms w ell S i s r cap closed, minRatio i s ≤ t := by
  classical
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  exact (Finset.mem_filter.mp hp).2.2.2.1

theorem finitePrimeMeasure_Icc (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (x : ℝ) :
    finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) =
      ENNReal.ofReal (∑ p ∈ children w ell S i s r cap closed,
        if childRatio w r p ≤ x then (p : ℝ)⁻¹ else 0) := by
  classical
  rw [finitePrimeMeasure_apply _ _ _ _ _ _ _ _ measurableSet_Icc,
    ENNReal.ofReal_sum_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  apply Finset.sum_congr rfl
  intro p hp
  have ha : minRatio i s ≤ childRatio w r p := (Finset.mem_filter.mp hp).2.2.2.1
  by_cases hx : childRatio w r p ≤ x <;> simp [Set.mem_Icc,ha,hx]

theorem finitePrimeMeasure_tilt (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (hs : Valid i s) :
    (∫⁻ t, ENNReal.ofReal (multiplier i s t) ∂finitePrimeMeasure w ell S i s r cap closed) =
      ENNReal.ofReal (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) := by
  rw [finitePrimeMeasure, lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac' _ (f := fun t => ENNReal.ofReal (multiplier i s t))
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s))]
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_sum_of_nonneg (fun p hp => primeTilt_nonneg hs hp)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeTilt_eq_multiplier, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg p))]

end NumberTheoryLean.PrimeRatioMeasure



namespace NumberTheoryLean.PrimeCumulativeBound

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltMonotone PrimeRatioBins
open PrimeRatioMeasure HarmonicExponentMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem cumulative_subset_closed {w ell S s r cap b : ℝ} (hw : 1 < w) {i : Side} (hs : Valid i s) (closed : Bool) :
    (children w ell S i s r cap closed).filter (fun p => childRatio w r p ≤ b) ⊆
      closedBin w r (minRatio i s) b := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hchild,hb⟩
  have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hchild).1).2
  have ha : minRatio i s ≤ childRatio w r p := (Finset.mem_filter.mp hchild).2.2.2.1
  have hab : minRatio i s ≤ b := ha.trans hb
  have hinterval := (closed_interval_iff (r := r) (minRatio_pos hs) hab (PrimeRatioBins.primeExponent_pos hw hprime)).mp ⟨ha,hb⟩
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,ha,hb⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hreal : (p : ℝ) ≤ w^(r/(minRatio i s+1)) := (exponent_le_iff hw hp0).mp hinterval.2
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal

theorem cumulative_sum_le_closed {w ell S s r cap b : ℝ} (hw : 1 < w) {i : Side} (hs : Valid i s) (closed : Bool) :
    (∑ p ∈ children w ell S i s r cap closed, if childRatio w r p ≤ b then (p : ℝ)⁻¹ else 0) ≤
      closedMass w r (minRatio i s) b := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (cumulative_subset_closed hw hs closed)
    (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))

end NumberTheoryLean.PrimeCumulativeBound



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

variable (w ell S : ℝ) (start : Node)
abbrev ChainState := Option (History w ell S start)

instance instMeasurableSpaceChainState : MeasurableSpace (ChainState w ell S start) := ⊤
instance instMeasurableSingletonClassChainState : MeasurableSingletonClass (ChainState w ell S start) := ⟨fun _ => trivial⟩

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeSideSupport

open _root_.Set _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain

def sideAfter (i : Side) : ℕ → Side
  | 0 => i
  | n+1 => (sideAfter i n).flip

def regularLower : Side → ℝ | .even => 2 | .odd => 1
noncomputable def weakLower : Side → ℝ | .even => 2 | .odd => 98/100

end NumberTheoryLean.PrimeSideSupport



namespace NumberTheoryLean.PrimeGridGeometry

open _root_.Set _root_.Erdos970.Set
open FinitePathGeometry PrimeHistories PrimeSideSupport

def lowerIndex (m : ℕ) : Side → ℕ | .even => 2*m | .odd => m

end NumberTheoryLean.PrimeGridGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompletedParentInterval
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousRatioBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry TransitionKernels PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioMeasure HarmonicExponentMeasure

noncomputable def weightedRatioLaw (i : Side) (s : ℝ) : Measure ℝ :=
  (ratioMeasure (minRatio i s)).withDensity (fun t => ENNReal.ofReal (multiplier i s t))

theorem weightedRatioLaw_eq_density {i : Side} {s : ℝ} (hs : Valid i s) :
    weightedRatioLaw i s = volume.withDensity (fun t => ENNReal.ofReal (transitionDensity i s t)) := by
  unfold weightedRatioLaw ratioMeasure
  rw [← withDensity_mul _ (f := fun t : ℝ => ENNReal.ofReal (1/(t+1)))
    (g := fun t : ℝ => ENNReal.ofReal (multiplier i s t))
    (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (1/(t+1))))
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s)), ← withDensity_indicator measurableSet_Ici]
  apply congrArg (fun f : ℝ → ℝ≥0∞ => volume.withDensity f)
  funext t
  exact weighted_ratio_density_eq hs t

theorem weightedRatioLaw_even (s : EvenState) : weightedRatioLaw .even s.1 = evenKernel s := by
  apply Measure.ext
  intro B hB
  rw [weightedRatioLaw_eq_density (i := .even) (s := s.1) s.2, withDensity_apply _ hB, evenKernel_apply]
  rfl

theorem weightedRatioLaw_odd (s : OddState) : weightedRatioLaw .odd s.1 = oddKernel s := by
  apply Measure.ext
  intro B hB
  rw [weightedRatioLaw_eq_density (i := .odd) (s := s.1) s.2, withDensity_apply _ hB, oddKernel_apply]
  rfl

noncomputable def continuousBin (i : Side) (s a b : ℝ) : ℝ :=
  (weightedRatioLaw i s (Ico a b)).toReal

end NumberTheoryLean.ContinuousRatioBins

end

section

namespace NumberTheoryLean.ContinuousKilledBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open LowStateHorizon RegeneratingInverseBands KernelDensityBridge ContinuousRatioBins

noncomputable def continuousChain (v ell S : ℝ) : Kernel (CemeteryKernel.Space CostState) (CemeteryKernel.Space CostState) :=
  CemeteryKernel.complete (lowKernel costKernel v ell S)

def ratioBinSet (a b : ℝ) : Set CostState := {z | a ≤ stateRatio z.1 ∧ stateRatio z.1 < b}

theorem costKernel_ratioLaw (z : CostState) :
    (costKernel z).map (fun y : CostState => stateRatio y.1) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) := by
  have hU : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, Measure.map_map (g := fun y : CostState => stateRatio y.1)
    (stateRatio_measurable.comp measurable_fst) hU]
  change (stateKernel z.1).map stateRatio = _
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    rw [stateKernel_even_ratio]
    exact (weightedRatioLaw_even s).symm
  | inr s =>
    rw [stateKernel_odd_ratio]
    exact (weightedRatioLaw_odd s).symm

end NumberTheoryLean.ContinuousKilledBins

end

section

namespace NumberTheoryLean.ContinuousIntervalUpper

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeTiltBounds PrimeTiltMonotone
open ContinuousRatioBins ContinuousKilledBins LowStateHorizon

theorem transition_density_upper : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s : ℝ,
    Valid i s → s ≤ S → ∀ t : ℝ,
      ENNReal.ofReal (transitionDensity i s t) ≤ ENNReal.ofReal (C*(1+S)^2) := by
  obtain ⟨C,hC,henv⟩ := multiplier_envelope
  refine ⟨C,hC,?_⟩
  intro S i s hs hsS t
  rw [← weighted_ratio_density_eq hs t]
  by_cases ht : minRatio i s ≤ t
  · rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    have ht0 := valid_pos (valid_next hs ht)
    have hinv : ENNReal.ofReal (1/(t+1)) ≤ 1 := by
      apply (ENNReal.ofReal_le_one).mpr
      exact (div_le_iff₀ (by linarith : 0 < t+1)).mpr (by linarith)
    calc
      _ ≤ 1*ENNReal.ofReal (C*(1+S)^2) := mul_le_mul hinv (ENNReal.ofReal_le_ofReal (henv S i s t hs hsS ht)) zero_le zero_le
      _ = _ := one_mul _
  · rw [indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht)]
    exact zero_le

theorem weighted_interval_upper : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s a b : ℝ,
    Valid i s → s ≤ S →
      weightedRatioLaw i s (Icc a b) ≤ ENNReal.ofReal (C*(1+S)^2) * ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := transition_density_upper
  refine ⟨C,hC,?_⟩
  intro S i s a b hs hsS
  rw [weightedRatioLaw_eq_density hs,withDensity_apply _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal (C*(1+S)^2) := lintegral_mono (hbound S i s hs hsS)
    _ = _ := by rw [setLIntegral_const,Real.volume_Icc]

def closedCostBin (a b : ℝ) : Set CostState :=
  {z | a ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ b}

theorem closedCostBin_measurable (a b : ℝ) : MeasurableSet (closedCostBin a b) :=
  (stateRatio_measurable.comp measurable_fst) measurableSet_Icc

theorem costKernel_closedBin (z : CostState) (a b : ℝ) :
    costKernel z (closedCostBin a b) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Icc a b) := by
  have h := congrArg (fun μ : Measure ℝ => μ (Icc a b)) (costKernel_ratioLaw z)
  rw [Measure.map_apply (f := fun y : CostState => stateRatio y.1) (stateRatio_measurable.comp measurable_fst) measurableSet_Icc] at h
  exact h

end NumberTheoryLean.ContinuousIntervalUpper

end

section

namespace NumberTheoryLean.CompletedParentInterval
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures ContinuousIntervalUpper ContinuousRatioBins ContinuousKilledBins LowStateHorizon

theorem completed_parent_interval_upper : ∃ C : ℝ,0 < C ∧
    ∀ v ell S U a b : ℝ,∀ z : CostState,stateRatio z.1 ≤ U →
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin a b) ≤
        ENNReal.ofReal (C*(1+U)^2)*ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := weighted_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S U a b z hz
  rw [continuousChain,CemeteryKernel.complete_live_mass _ _ (closedCostBin_measurable a b),
    lowKernel,Kernel.restrict_apply,Measure.restrict_apply (closedCostBin_measurable a b)]
  calc
    _ ≤ costKernel z (closedCostBin a b) := measure_mono inter_subset_left
    _ = _ := costKernel_closedBin z a b
    _ ≤ _ := hbound U (stateSide z.1) (stateRatio z.1) a b (stateRatio_valid z.1) hz
end NumberTheoryLean.CompletedParentInterval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.WeightedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioBins ContinuousRatioBins

noncomputable def weightedPrimeBin (w r : ℝ) (i : Side) (s a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, primeTilt w r i s p

end NumberTheoryLean.WeightedPrimeBins

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain
open PrimeTiltGeometry DerivativeWeights

noncomputable def inverseBound (K : ℝ) : ℝ := max (1/weight .even K) (1/weight .odd K)

noncomputable def compactConstant (K : ℝ) : ℝ :=
  2*K^2*weight .even (199/100)*inverseBound K

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_NestedCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

noncomputable def nestedX : MV R ≃ₐ[R] Nested R :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

noncomputable def nestedY : MV R ≃ₐ[R] Nested R :=
  (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).trans (nestedX R)

@[simp] theorem nestedX_C (c : R) : nestedX R (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  simpa using (nestedX R).commutes c

@[simp] theorem nestedX_X_zero : nestedX R (MvPolynomial.X 0) = Polynomial.X := by
  simp [nestedX, Polynomial.coe_mapAlgEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem nestedX_X_one : nestedX R (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

@[simp] theorem nestedY_C (c : R) : nestedY R (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  simp [nestedY]

@[simp] theorem nestedY_X_zero : nestedY R (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp [nestedY]

@[simp] theorem nestedY_X_one : nestedY R (MvPolynomial.X 1) = Polynomial.X := by
  simp [nestedY]

noncomputable def nestedEvalHom (x y : R) : Nested R →+* R :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))

@[simp] theorem nestedEvalHom_C (p : Polynomial R) (x y : R) :
    nestedEvalHom R x y (Polynomial.C p) = p.eval x := by simp [nestedEvalHom]

@[simp] theorem nestedEvalHom_X (x y : R) :
    nestedEvalHom R x y Polynomial.X = y := by simp [nestedEvalHom]

theorem eval_nestedY (Q : MV R) (x y : R) :
    nestedEvalHom R x y (nestedY R Q) = MvPolynomial.eval ![x,y] Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [nestedEvalHom]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [map_mul, hP]
      · simp [map_mul, hP]

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_PolynomialLocalGraph
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection ErdosCriticalGeometry

noncomputable def verticalPolynomial (Q : Bivariate) (x : ℝ) : Polynomial ℝ :=
  (nestedY ℝ Q).map (Polynomial.evalRingHom x)

theorem verticalPolynomial_eval (Q : Bivariate) (x y : ℝ) :
    (verticalPolynomial Q x).eval y = peval Q x y := by
  have hv : (fun i : Fin 2 => if i = 0 then x else y) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  have h := eval_nestedY ℝ Q x y
  change (verticalPolynomial Q x).eval y = MvPolynomial.eval ![x,y] Q at h
  simpa only [peval,hv] using h

theorem boundedFiber_finite (Q : Bivariate) (x L U z : ℝ)
    (hz : peval Q x z ≠ 0) : (boundedFiber Q x L U).Finite := by
  have hp : verticalPolynomial Q x ≠ 0 := by
    intro he
    apply hz
    rw [← verticalPolynomial_eval, he, Polynomial.eval_zero]
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro y hy
  change (verticalPolynomial Q x).eval y = 0
  exact (verticalPolynomial_eval Q x y).trans hy.2

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RealCriticalPoints
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

open ErdosBivariateResultant

@[simp] theorem beval_nested (Q : MV ℂ) (x y : ℂ) :
    beval (nestedY ℂ Q) x y = MvPolynomial.eval ![x,y] Q := eval_nestedY ℂ Q x y

def intersectionPoints (Q G : MV ℂ) : Set (ℂ × ℂ) :=
  {p | MvPolynomial.eval ![p.1,p.2] Q = 0 ∧ MvPolynomial.eval ![p.1,p.2] G = 0}

def intersectionAbscissae (Q G : MV ℂ) : Set ℂ := Prod.fst '' intersectionPoints Q G

end ErdosCriticalGeometry

end

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry

noncomputable def affineLine (A B : ℂ) : MV ℂ :=
  MvPolynomial.X 1-(MvPolynomial.C A*MvPolynomial.X 0+MvPolynomial.C B)

end ErdosDivisibleInflection

end

section

namespace ErdosCriticalGeometry

def criticalPoints (Q : MV ℂ) : Set (ℂ × ℂ) :=
  intersectionPoints Q (MvPolynomial.pderiv 0 Q) ∪ intersectionPoints Q (MvPolynomial.pderiv 1 Q)

def criticalAbscissae (Q : MV ℂ) : Set ℂ := Prod.fst '' criticalPoints Q

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

noncomputable def inflection (Q : MV ℂ) : MV ℂ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)*(MvPolynomial.pderiv 1 Q)^2 +
    MvPolynomial.C (-2 : ℂ)*MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)*
      MvPolynomial.pderiv 0 Q*MvPolynomial.pderiv 1 Q +
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 Q)*(MvPolynomial.pderiv 0 Q)^2

def exceptionalPoints (Q : MV ℂ) : Set (ℂ × ℂ) := criticalPoints Q ∪ intersectionPoints Q (inflection Q)

def exceptionalAbscissae (Q : MV ℂ) : Set ℂ := Prod.fst '' exceptionalPoints Q

end ErdosCriticalGeometry

end

section

namespace ErdosCriticalGeometry

noncomputable def complexify (Q : MV ℝ) : MV ℂ := MvPolynomial.map (algebraMap ℝ ℂ) Q

def realCriticalPoints (Q : MV ℝ) : Set (ℝ × ℝ) :=
  {p | MvPolynomial.eval ![p.1,p.2] Q = 0 ∧
    (MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 0 Q) = 0 ∨
     MvPolynomial.eval ![p.1,p.2] (MvPolynomial.pderiv 1 Q) = 0)}

def realCriticalAbscissae (Q : MV ℝ) : Set ℝ := Prod.fst '' realCriticalPoints Q

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_DivisibleInflection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry ErdosImplicitCurvature

noncomputable def swapVars (R : Type*) [CommSemiring R] : MV R ≃ₐ[R] MV R :=
  MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)

end ErdosDivisibleInflection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiberCardinalityConstancy
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open ErdosImplicitCurvature

theorem exists_bounded_fiber_charts (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0)
    (hregular : ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0) :
    Nonempty (FiberCharts Q x L U) := by
  classical
  let R := boundedFiber Q x L U
  have hR : R.Finite := boundedFiber_finite Q x L U L hL
  let : Fintype R := hR.fintype
  obtain ⟨V,hV,hsep⟩ := hR.t2_separation
  have hcharts (r : R) := exists_local_graph_iff Q x r r.property.2
    (hregular r r.property) (V r ∩ Ioo L U) ((hV r).2.inter isOpen_Ioo)
    ⟨(hV r).1,boundedFiber_interior Q x L U hL hU r.property⟩
  choose a b W f ha hb hWo hrW hWV hbase hC hmem hder hiff using hcharts
  have hWint (r : R) : W r ⊆ Ioo L U := fun y hy => (hWV r hy).2
  have hWd : Pairwise fun r s : R => Disjoint (W r) (W s) := by
    intro r s hrs
    apply (hsep r.property s.property (fun he => hrs (Subtype.ext he))).mono
    · exact fun y hy => (hWV r hy).1
    · exact fun y hy => (hWV s hy).1
  let K := Icc L U \ ⋃ r : R, W r
  have hK : IsCompact K := isCompact_Icc.diff (isOpen_iUnion hWo)
  have hKzero : ∀ y ∈ K, peval Q x y ≠ 0 := by
    intro y hy hzero
    have hyR : y ∈ R := ⟨hy.1,hzero⟩
    exact hy.2 (mem_iUnion.mpr ⟨⟨y,hyR⟩,hrW ⟨y,hyR⟩⟩)
  have hnoextra := compact_nonzero_eventually Q x K hK hKzero
  have hdomains : ∀ᶠ t in 𝓝 x, ∀ r : R, t ∈ Ioo (a r) (b r) :=
    eventually_all.mpr fun r => isOpen_Ioo.mem_nhds ⟨ha r,hb r⟩
  have hcont (r : R) : ContinuousAt (f r) x :=
    (hC r).continuousOn.continuousAt (isOpen_Ioo.mem_nhds ⟨ha r,hb r⟩)
  have horder : ∀ᶠ t in 𝓝 x, ∀ r s : R, r < s → f r t < f s t := by
    apply eventually_all.mpr
    intro r
    apply eventually_all.mpr
    intro s
    by_cases hrs : r < s
    · have hlt : f r x < f s x := by simpa only [hbase] using (show (r : ℝ) < (s : ℝ) from hrs)
      exact ((hcont r).eventually_lt (hcont s) hlt).mono fun t ht _ => ht
    · exact Eventually.of_forall fun t ht => (hrs ht).elim
  have hN : {t | (∀ r : R, t ∈ Ioo (a r) (b r)) ∧
      (∀ y ∈ K, peval Q t y ≠ 0) ∧ (∀ r s : R, r < s → f r t < f s t)} ∈ 𝓝 x :=
    hdomains.and (hnoextra.and horder)
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hs : Ioo (x-eps) (x+eps) ⊆ {t | (∀ r : R, t ∈ Ioo (a r) (b r)) ∧
      (∀ y ∈ K, peval Q t y ≠ 0) ∧ (∀ r s : R, r < s → f r t < f s t)} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨{
    a := x-eps
    b := x+eps
    left := by linarith
    right := by linarith
    finite_base := hR, graph := f, tube := W, tube_open := hWo, tube_base := hrW,
    tube_interior := hWint, tube_disjoint := hWd, graph_base := hbase,
    graph_smooth := fun r => (hC r).mono (fun t ht => (hs ht).1 r),
    graph_inside := fun r t ht => hmem r t ((hs ht).1 r),
    graph_regular := fun r t ht => hder r t ((hs ht).1 r),
    zero_iff := fun r t ht => hiff r t ((hs ht).1 r),
    coverage := ?_, ordered := fun t ht => (hs ht).2.2 }⟩
  intro t ht
  ext y
  constructor
  · intro hy
    have hyW : y ∈ ⋃ r : R, W r := by
      by_contra hn
      exact (hs ht).2.1 y ⟨hy.1,hn⟩ hy.2
    obtain ⟨r,hyr⟩ := mem_iUnion.mp hyW
    exact ⟨r,((hiff r t ((hs ht).1 r) y hyr).mp hy.2).symm⟩
  · rintro ⟨r,rfl⟩
    have hfW := hmem r t ((hs ht).1 r)
    exact ⟨Ioo_subset_Icc_self (hWint r hfW),
      (hiff r t ((hs ht).1 r) (f r t) hfW).mpr rfl⟩

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosCriticalGeometry

theorem locally_constant_fiber_card (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0)
    (hregular : ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ ∀ t ∈ Ioo a b,
      (boundedFiber Q t L U).Finite ∧
      (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  obtain ⟨c⟩ := exists_bounded_fiber_charts Q x L U hL hU hregular
  exact ⟨c.a,c.b,c.left,c.right,fun t ht => ⟨c.fiber_finite ht,c.fiber_card_eq ht⟩⟩

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection

theorem fiber_card_eventually_eq (Q : Bivariate) (L U : ℝ) {x : ℝ}
    (hx : x ∈ regularParameters Q L U) :
    ∀ᶠ t in 𝓝 x, (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  obtain ⟨a,b,ha,hb,h⟩ := locally_constant_fiber_card Q x L U hx.1 hx.2.1 hx.2.2
  filter_upwards [isOpen_Ioo.mem_nhds ⟨ha,hb⟩] with t ht
  exact (h t ht).2

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

theorem continuousOn_fiber_card (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hI : I ⊆ regularParameters Q L U) :
    ContinuousOn (fun x => (boundedFiber Q x L U).ncard) I := by
  intro x hx
  have he : (fun t => (boundedFiber Q t L U).ncard) =ᶠ[𝓝 x]
      (fun _ => (boundedFiber Q x L U).ncard) := fiber_card_eventually_eq Q L U (hI hx)
  have hc : ContinuousAt (fun t => (boundedFiber Q t L U).ncard) x :=
    continuousAt_const.congr he.symm
  exact hc.continuousWithinAt

theorem fiber_card_eq_on_preconnected (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hconn : IsPreconnected I) (hI : I ⊆ regularParameters Q L U)
    {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    (boundedFiber Q x L U).ncard = (boundedFiber Q t L U).ncard :=
  hconn.constant (continuousOn_fiber_card Q L U I hI) hx ht

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GlobalFiniteBranches
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

namespace RegularDomain
variable {Q : Bivariate} {x L U : ℝ} {I : Set ℝ} (d : RegularDomain Q x L U I)
include d

theorem fiber_finite {t : ℝ} (ht : t ∈ I) : (boundedFiber Q t L U).Finite :=
  boundedFiber_finite Q t L U L (d.regular ht).1

noncomputable def transport (t : ℝ) (ht : t ∈ I) :
    boundedFiber Q x L U ≃o boundedFiber Q t L U := by
  letI := (d.fiber_finite d.base_mem).fintype
  letI := (d.fiber_finite ht).fintype
  exact orderIsoOfNatCardEq _ _ (fiber_card_eq_on_preconnected Q L U I
    d.isPreconnected d.regular d.base_mem ht)

noncomputable def branch (r : boundedFiber Q x L U) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ I then (d.transport t ht r : ℝ) else r

end RegularDomain

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HorizontalBoundaryMarks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

def boundaryAbscissae (Q : MV ℝ) (y : ℝ) : Set ℝ := {x | peval Q x y = 0}

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RealExceptionalMarks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

def realExceptionalAbscissae (Q : MV ℝ) : Set ℝ :=
  Complex.ofReal ⁻¹' exceptionalAbscissae (complexify Q)

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_ComplexSquareScaling
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

noncomputable def conjugateEquiv : MV ℂ ≃+* MV ℂ :=
  MvPolynomial.mapEquiv (Fin 2) Complex.conjAe.toRingEquiv

noncomputable def conjugate (F : MV ℂ) : MV ℂ := MvPolynomial.map (starRingEnd ℂ) F

end ErdosComplexCurveFactors

end

section

open Set
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosMarkedStrips ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def complexSquarePoints (F : MV ℂ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RealCoefficientNormalization
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

noncomputable def realCoefficients (F : MV ℂ) : MV ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff F))

def RealScalable (F : MV ℂ) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ ∃ R : MV ℝ, F = MvPolynomial.C a * complexify R

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RichLinearFactor
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

@[implicit_reducible]
noncomputable def complexPolynomialNormalization : StrongNormalizationMonoid (MV ℂ) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

attribute [local instance] complexPolynomialNormalization

noncomputable def nonlinearFactors (P : MV ℂ) : Finset (MV ℂ) := by
  classical
  exact (normalizedFactors P).toFinset.filter (fun F => 1 < F.totalDegree)

end ErdosComplexCurveFactors

end

section

open Set UniqueFactorizationMonoid
namespace ErdosComplexCurveFactors
attribute [local instance] complexPolynomialNormalization
open ErdosCriticalGeometry ErdosConvexGraph
attribute [local instance] Classical.propDecidable

def OnNonlinearComponent (P : MV ℂ) (p : ℤ × ℤ) : Prop :=
  ∃ F : MV ℂ, Irreducible F ∧ F ∣ P ∧ 1 < F.totalDegree ∧
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0

noncomputable def nonlinearSquarePoints (P : MV ℂ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter (OnNonlinearComponent P)

end ErdosComplexCurveFactors

end

section

open UniqueFactorizationMonoid
namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph
attribute [local instance] complexPolynomialNormalization

noncomputable def linearFactors (P : MV ℂ) : Finset (MV ℂ) := by
  classical
  exact (normalizedFactors P).toFinset.filter (fun F => F.totalDegree = 1)

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedPrimeCongruence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped BigOperators
open SievePartition

noncomputable def mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℤ :=
  (residueCandidates Y v.1 small a).card

end NumberTheoryLean.ResidueSieveTree

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualTagFreezing
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StoppedCountVertex

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePrefixRecurrence
open ReferenceForestTelescoping ReferencePruning SievePartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

structure Vertex where
  node : Node
  required : Finset ℕ
  available : Finset ℕ
  past : List ℕ
  scale : ℝ

noncomputable def child (w : ℝ) (v : Vertex) (p : ℕ) : Vertex where
  node := step w v.node p
  required := insert p v.required
  available := v.available.filter (fun q => q < p)
  past := v.past++[p]
  scale := v.scale/(p:ℝ)

noncomputable def includedPrimes (w : ℝ) (v : Vertex) : Finset ℕ :=
  v.available.filter fun p => childAdmitted v.node.side v.node.gap (primeExponent w p)

noncomputable def countMass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℝ :=
  ((residueCandidates Y v.required small a).card : ℝ)

noncomputable def countSurvivors (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℝ :=
  ((survivors (residueCandidates Y v.required small a) v.available (residueBad a)).card : ℝ)

noncomputable def referenceValue (w : ℝ) (v : Vertex) : ℝ :=
  v.scale*referencePolynomial w v.available v.node.side v.node.gap

end NumberTheoryLean.StoppedCountVertex



namespace NumberTheoryLean.StoppedEvaluation

open _root_.Finset
open FinitePathGeometry StoppedCountVertex
attribute [local instance] Classical.propDecidable

def lowerStop (stop : List ℕ → Prop) (v : Vertex) : Prop :=
  v.node.side = .even ∧ stop v.past

noncomputable def evaluate (w : ℝ) (stop : List ℕ → Prop)
    (mass exit : Vertex → ℝ) : ℕ → Vertex → ℝ
  | 0,v => if lowerStop stop v then exit v else mass v
  | n+1,v => if lowerStop stop v then exit v else
      mass v - ∑ p ∈ includedPrimes w v,evaluate w stop mass exit n (child w v p)

noncomputable def stoppedCount (w : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : ℝ :=
  evaluate w stop (countMass Y small a) (countSurvivors Y small a) n v

end NumberTheoryLean.StoppedEvaluation



namespace NumberTheoryLean.StoppedVertexHistory

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex ReferenceForestTelescoping ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def after (w : ℝ) : Vertex → List ℕ → Vertex
  | v,[] => v
  | v,p::ps => after w (child w v p) ps

end NumberTheoryLean.StoppedVertexHistory



namespace NumberTheoryLean.StoppedTraceSets

open _root_.Set _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory
attribute [local instance] Classical.propDecidable

noncomputable def traces (w : ℝ) (stop : List ℕ → Prop) : ℕ → Vertex →
    Finset (List ℕ) × Finset (List ℕ)
  | 0,v => if lowerStop stop v then (∅,{[]}) else ({[]},∅)
  | n+1,v => if lowerStop stop v then (∅,{[]}) else
      (insert [] (childrenTraces (includedPrimes w v) (fun p => (traces w stop n (child w v p)).1)),
        childrenTraces (includedPrimes w v) (fun p => (traces w stop n (child w v p)).2))

noncomputable def expanded (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : Finset (List ℕ) :=
  (traces w stop n v).1

noncomputable def stopped (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex) : Finset (List ℕ) :=
  (traces w stop n v).2

end NumberTheoryLean.StoppedTraceSets



namespace NumberTheoryLean.FirstStopSemantics

open _root_.Finset
open StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

def FirstStop (w : ℝ) (stop : List ℕ → Prop) (v : Vertex) (ps : List ℕ) : Prop :=
  lowerStop stop (after w v ps) ∧ ∀ pre tail : List ℕ,
    ps = pre++tail → tail ≠ [] → ¬lowerStop stop (after w v pre)

end NumberTheoryLean.FirstStopSemantics



namespace NumberTheoryLean.FlatStoppedIdentity

open _root_.Finset
open FinitePathGeometry StoppedCountVertex StoppedEvaluation StoppedVertexHistory StoppedTraceSets
attribute [local instance] Classical.propDecidable

def sideSign : Side → ℝ
  | .even => 1
  | .odd => -1

end NumberTheoryLean.FlatStoppedIdentity



namespace NumberTheoryLean.StoppedCountAdapters

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedEvaluation StoppedVertexHistory
open StoppedTraceSets FlatStoppedIdentity ReferenceAdmission ReferencePruning
attribute [local instance] Classical.propDecidable

noncomputable def rootVertex (z : Node) (H P : Finset ℕ) (mu : ℝ) : Vertex :=
  ⟨z,H,P,[],mu⟩

end NumberTheoryLean.StoppedCountAdapters



namespace NumberTheoryLean.SourceStopPredicate

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission RepresentativeAdmission RepresentativeStopGeometry
open PrimeBinRepresentatives ActualSourceTags ActualBinOwners FiniteFirstTag
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def representativeSafe (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ) : Prop :=
  ∀ qs ∈ ps.inits,qs ≠ [] → (terminal w z qs).side = .even →
    sourceHeight (rep (qs.getLastD 0))+3*Delta ≤ representativeGap rep z.gap qs

noncomputable def representativeWindow (rep : ℕ → ℝ) (z : Node) (b₀ b₁ : ℝ) (ps : List ℕ) : Prop :=
  b₀ ≤ rep (ps.getLastD 0) ∧ rep (ps.getLastD 0) ≤ b₁ ∧
    206/100 ≤ representativeGap rep z.gap ps/rep (ps.getLastD 0) ∧
    representativeGap rep z.gap ps/rep (ps.getLastD 0) ≤ 216/100

noncomputable def stopCandidate {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node) (ps : List ℕ) : Prop :=
  ps ≠ [] ∧ (ps.length:ℝ) ≤ Clen*Real.log B ∧ boxed lower width label ps ∧
    representativeSafe w (representative w lower width label) z (2*Clen*xi) ps ∧
    representativeWindow (representative w lower width label) z b₀ b₁ ps ∧
    ∃ t : Tag n,sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps = some t ∧
      (ps.map label).count t.bin = 1 ∧ ∀ p ∈ ps,aligns (sourceClass a) t.rational p

end NumberTheoryLean.SourceStopPredicate



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.KernelCouplingWeights

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning Erdos970Dependency.MaximalCoupling
attribute [local instance] Classical.propDecidable

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def weight (K : Kernel α β) (L : Kernel α γ) (f : β → ι) (g : γ → ι)
    (x : α) (i j : ι) : ℝ := matrix (labelMass K f x) (labelMass L g x) i j

noncomputable def errorMass (K : Kernel α β) (L : Kernel α γ) (f : β → ι) (g : γ → ι) (x : α) : ℝ :=
  residual (labelMass K f x) (labelMass L g x)

end NumberTheoryLean.KernelCouplingWeights

end

section

namespace NumberTheoryLean.KernelCouplingLift

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)

noncomputable def component (i j : ι) : Kernel α (β × γ) :=
  ((conditional K (hf (measurableSet_singleton i)) dβ).prod
    (conditional L (hg (measurableSet_singleton j)) dγ)).withDensity
      (fun x _ => ENNReal.ofReal (weight K L f g x i j))

instance component_isSFinite (i j : ι) : IsSFiniteKernel (component K L hf hg dβ dγ i j) := by
  unfold component
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

noncomputable def coupled : Kernel α (β × γ) :=
  Kernel.sum (fun p : ι × ι => component K L hf hg dβ dγ p.1 p.2)

instance coupled_isSFinite : IsSFiniteKernel (coupled K L hf hg dβ dγ) := by
  unfold coupled
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

noncomputable def continuousLabel (S mesh : ℝ) : CemeteryKernel.Space CostState → Label S mesh :=
  Sum.elim (fun z => ratioLabel S mesh (stateRatio z.1)) (fun _ => cemeteryLabel S mesh)

theorem continuousLabel_measurable (S mesh : ℝ) : Measurable (continuousLabel S mesh) :=
  ((ratioLabel_measurable S mesh).comp (stateRatio_measurable.comp measurable_fst)).sumElim measurable_const

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels ActualProcessCoupling LowStateHorizon

variable {w ell S : ℝ} {start : Node}

def continuousSupported (S : ℝ) : CemeteryKernel.Space CostState → Prop
  | .inl z => stateRatio z.1 ≤ S
  | .inr _ => True

def badRatio (S : ℝ) : Set CostState := {z | ¬stateRatio z.1 ≤ S}

end NumberTheoryLean.ActualCouplingSupport

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

def continuousFollows (z y : CostState) : Prop :=
  y.2 = z.2+cost (stateRatio y.1) ∧ stateSide y.1 = (stateSide z.1).flip

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RetainedIntervalUpper
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RetainedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeCumulativeBound PrimeRatioBins ContinuousRatioBins
open PrimeHistories PrimeKilledChain ContinuousKilledBins FinitePathMeasures
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def retainedInterval (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (a b : ℝ) : Finset ℕ := by
  classical
  exact (children w ell S i s r cap closed).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p ≤ b)

noncomputable def retainedIntervalTilt (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (a b : ℝ) : ℝ :=
  ∑ p ∈ retainedInterval w ell S i s r cap closed a b, primeTilt w r i s p

end NumberTheoryLean.RetainedIntervalUpper


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CouplingLabelEvents
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CoupledBoundaryEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualSupportIntervals MeshBoundaryGeometry MeshRatioLabels
open ContinuousIntervalUpper ActualCouplingSupport
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

def continuousBadCells (S mesh Ld Lc Ud Uc : ℝ) : Set (CemeteryKernel.Space CostState) :=
  fun p => match p with
    | .inr _ => False
    | .inl z => ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh (stateRatio z.1))

end NumberTheoryLean.CoupledBoundaryEvents

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

def typedState : (i : Side) → (s : ℝ) → Valid i s → State
  | .even,s,hs => .inl ⟨s,hs⟩
  | .odd,s,hs => .inr ⟨s,hs⟩

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MarginalProfiles
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarginalProfiles

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeSideSupport PrimeGridGeometry DerivativeWeights WeightFutureIntegrals

noncomputable def profile (m : ℕ) : Side → ℝ → ℝ
  | .even,_ => 1
  | .odd,t => 1-1/t^2+3*width m*W t

end NumberTheoryLean.MarginalProfiles

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeMarginalRecursion
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeGridKernel

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry

variable {w ell S : ℝ} {start : Node}

noncomputable def weakIndices (m j : ℕ) (i : Side) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 (j+m+1)).filter (fun k => Valid i (point m k))

end NumberTheoryLean.PrimeGridKernel

end

section


namespace NumberTheoryLean.PrimeMarginalRecursion

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel ExponentialMesh
open DerivativeWeights

noncomputable def entry (L κ w S : ℝ) (m : ℕ) (i : Side) (j k : ℕ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*Real.exp (L*(1+S)^3*mesh κ w)*
    width m*W (point m j)*(weight i.flip (point m j)/weight i (point m k))

end NumberTheoryLean.PrimeMarginalRecursion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceParentBin
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceParentBin

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalRecursion DerivativeWeights

noncomputable def initialConstant : ℝ := 1/phiEven (23/10)

end NumberTheoryLean.SourceParentBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompactTestGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactTestGeometry

open _root_.Set _root_.MeasureTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling RegeneratingInverseBands

variable {w ell S : ℝ} {start : Node}

noncomputable def continuousTest (v : ℝ) (F : Side → ℝ×ℝ → ℝ) : CemeteryKernel.Space CostState → ℝ
  | .inr _ => 0
  | .inl z => F (stateSide z.1) (gapValue v z,stateRatio z.1)

end NumberTheoryLean.CompactTestGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ContinuousCompletedOccupation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.ContinuousCompletedOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathMeasures ContinuousKilledBins LowStateHorizon CemeteryKernel
open PairedCostGrouping OccupationDecomposition CostPrefixTransport

noncomputable abbrev liftReward := @CemeteryPowers.liftReward CostState

end NumberTheoryLean.ContinuousCompletedOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ContinuousArrivalSupport
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousArrivalSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins CemeteryKernel LowStateHorizon ArrivalKernelGeometry

def arrivalSupported (v ell : ℝ) : Space CostState → Prop
  | .inl z => z ∈ arrivalSet v ell
  | .inr _ => True

end NumberTheoryLean.ContinuousArrivalSupport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeTailSplit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.InitialPrimeTail

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain DerivativeWeights
open ExponentialMeshTail

noncomputable def initialConstant : ℝ := 8/weight .even (23/10)

noncomputable def initialBudget (c B : ℝ) : ℝ := (initialConstant/c^2)*Real.exp (-(c/2)*B)

end NumberTheoryLean.InitialPrimeTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ScaledOriginalTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain DerivativeWeights
open PrimeCompactWeights LowStateHorizon

noncomputable def prefactorBound : ℝ := 2*weight .even (199/100)

end NumberTheoryLean.ScaledOriginalTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SignedCompletedPowers
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SignedCompletedPowers

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel

variable {α : Type*} [MeasurableSpace α]

noncomputable def liftReal (F : α → ℝ) : Space α → ℝ := Sum.elim F (fun _ => 0)

open FinitePathMeasures ContinuousKilledBins LowStateHorizon

end NumberTheoryLean.SignedCompletedPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SubMarkovFlagPowers
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SubMarkovFlagPowers

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound

variable {α : Type*} [MeasurableSpace α]

noncomputable def goodSelect (F : α → ℝ≥0∞) : FlagState α → ℝ≥0∞ := failedᶜ.indicator (fun z => F z.1)

end NumberTheoryLean.SubMarkovFlagPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ContinuousHighPartition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousHighPartition

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open AdmittedHarmonicPaths LowStateHorizon SubMarkovFlagPowers
open PersistentFailureFlag FlaggedOccupationBound

def high (S : ℝ) (z : CostState) : Prop := S < stateRatio z.1

theorem high_measurable (S : ℝ) : MeasurableSet {z | high S z} :=
  measurableSet_lt measurable_const (stateRatio_measurable.comp measurable_fst)

noncomputable def tiltedFlagged (v ell S : ℝ) : Kernel (CostState×Bool) (CostState×Bool) :=
  marked (admittedTilted v ell) (high_measurable S)

end NumberTheoryLean.ContinuousHighPartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_FiniteAdmittedOccupation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OriginalHarmonicOccupation

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths ArrivalKernelGeometry
open KernelWeightTransform HarmonicWeightKernel
open InvariantInverseWeights CostPrefixTransport RegeneratingInverseBands

noncomputable def occupation (K : Kernel CostState CostState) : Kernel CostState CostState :=
  Kernel.sum (fun n : ℕ => K^n)

instance occupation_isSFinite (K : Kernel CostState CostState) [IsSFiniteKernel K] :
    IsSFiniteKernel (occupation K) := by unfold occupation; infer_instance

noncomputable def gapSquaredWeight (v : ℝ) (z : CostState) : ℝ≥0∞ :=
  ENNReal.ofReal ((gapValue v z)^2 / stateWeight z.1)

end NumberTheoryLean.OriginalHarmonicOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicTransform
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlaggedHarmonicTransform

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths HarmonicWeightKernel
open KernelWeightTransform FlagWeightConjugation PersistentFailureFlag
open FlaggedOccupationBound ContinuousHighPartition OriginalHarmonicOccupation

instance tiltedFlagged_sfinite (v ell S : ℝ) : IsSFiniteKernel (tiltedFlagged v ell S) := by
  unfold tiltedFlagged
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.FlaggedHarmonicTransform

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectedCompactTransfer
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SignedCompactTransfer

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open CompactTestGeometry
open ActualProcessCoupling PersistentFailureFlag ContinuousKilledBins LowStateHorizon
open ExponentialMesh

noncomputable def continuousExpectation (F : Side → ℝ×ℝ → ℝ) (v ell S : ℝ) (z : CostState) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ y,continuousTest v F y ∂((continuousChain v ell S)^n) (.inl z)

end NumberTheoryLean.SignedCompactTransfer

end

section

namespace NumberTheoryLean.CompactInverseTest

open _root_.Set
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open DerivativeWeights CompactTestGeometry SignedCompactTransfer InvariantInverseWeights

noncomputable def lowerRatio : Side → ℝ | .even => 198/100 | .odd => 95/100

noncomputable def safeWeight (i : Side) (s : ℝ) : ℝ := weight i (max (lowerRatio i) s)

noncomputable def inverseTest (H : Side → ℝ×ℝ → ℝ) (i : Side) (x : ℝ×ℝ) : ℝ :=
  x.1^2*H i x/safeWeight i x.2

end NumberTheoryLean.CompactInverseTest

end

section

namespace NumberTheoryLean.ContinuousCompactHighError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CompactTestGeometry CompactInverseTest
open RegeneratingInverseBands InvariantInverseWeights OriginalHarmonicOccupation
open ContinuousHighPartition FlaggedHarmonicTransform
open LowStateHorizon AdmittedHarmonicPaths

noncomputable def baseReward (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) : ℝ :=
  H (stateSide z.1) (gapValue v z,stateRatio z.1)

noncomputable def inverseReward (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) : ℝ :=
  continuousTest v (inverseTest H) (.inl z)

end NumberTheoryLean.ContinuousCompactHighError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceLowRemoval
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceLowRemoval

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures TransitionKernels FinitePathGeometry DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousCompactHighError OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon

noncomputable def scaleConstant : ℝ := (23/10:ℝ)^2/phiEven (23/10)

end NumberTheoryLean.SourceLowRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_TwoSidedThresholdGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdGeometry
open Set MeasureTheory FinitePathGeometry ErdosEvenThreshold

noncomputable def normalizedSlack (R t : ℝ) : ℝ := thresholdSlack R t/R

noncomputable def thickStrip (R delta : ℝ) : Set ℝ :=
  {t | 2 ≤ t ∧ t ≤ 5 ∧ |normalizedSlack R t| ≤ delta}

end NumberTheoryLean.TwoSidedThresholdGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_MarkedCycleCompletion
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.RegenerationTails
open NumberTheoryLean.FinitePathGeometry

noncomputable def continueMarkUpdate (x : MarkedOddCost × OddCost) : MarkedOddCost := (x.1.1,x.2)

lemma continueMarkUpdate_measurable : Measurable continueMarkUpdate :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostSublaws
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.RegenerationTails

def sourceMarkSet : Set MarkedOddCost := {z | z.1=true}

def sourceCostProjection (z : MarkedOddCost) : ℝ := z.2.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_MarkedCycleFactorization
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.RegenerationTails

def markCostProjection (z : MarkedOddCost) : Bool × ℝ := (z.1,z.2.2)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_SourceCycleDuration
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.MarkedCycleLaw

abbrev FirstPairWitness := EvenState × OddCost

noncomputable def pairWitnessUpdate (x : OddCost × (EvenState × OddState)) : FirstPairWitness :=
  (x.2.1,pairUpdate x)

noncomputable def pairWitnessKernel : Kernel OddCost FirstPairWitness :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map pairWitnessUpdate

noncomputable def firstPairProjection (z : FirstPairWitness) : MarkedOddCost := (sourceMark z.1,z.2)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairTraceBridge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CycleOccupation

noncomputable def pairTraceOfWitness (z : OddCost) (x : FirstPairWitness) : CostState × CostState :=
  ((Sum.inl x.1,z.2+cost x.1.1),embedOdd x.2)

noncomputable def fullPairTraceKernel : Kernel CostState (CostState × CostState) :=
  costKernel ⊗ₖ costKernel.prodMkLeft CostState

instance fullPairTraceKernel_isMarkovKernel : IsMarkovKernel fullPairTraceKernel := by
  unfold fullPairTraceKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HistoryRestrictionAlgebra
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

abbrev RawHistory (n : ℕ) := ∀ _ : Finset.Iic n, CostState

def rawPrefix {a b : ℕ} (hab : a ≤ b) : RawHistory b → RawHistory a :=
  frestrictLe₂ (π := fun _ => CostState) hab

lemma rawPrefix_measurable {a b : ℕ} (hab : a ≤ b) : Measurable (rawPrefix hab) :=
  measurable_frestrictLe₂ (X := fun _ => CostState) hab

noncomputable def rawExtension (a b : ℕ) : Kernel (RawHistory a) (RawHistory b) :=
  Kernel.partialTraj (X := fun _ => CostState) historyKernel a b

instance rawExtension_isMarkovKernel (a b : ℕ) : IsMarkovKernel (rawExtension a b) := by
  unfold rawExtension
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairCaptureProjection
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

def rawLast (n : ℕ) (h : RawHistory n) : CostState := h ⟨n,by simp⟩

lemma rawLast_measurable (n : ℕ) : Measurable (rawLast n) := measurable_pi_apply _

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawWordSpaces
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

noncomputable def firstArrivalMark (s : CostState) : Bool := Sum.elim sourceMark (fun _ => false) s.1

lemma firstArrivalMark_measurable : Measurable firstArrivalMark :=
  (sourceMark_measurable.sumElim measurable_const).comp measurable_fst

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

@[reducible] def RawCycleWordTrace : ℕ → ℕ → Type
  | a, 0 => RawHistory a
  | a, k+1 => Σ n : ℕ, RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) k

@[reducible] noncomputable def rawCycleWordMeasurable : (a k : ℕ) → MeasurableSpace (RawCycleWordTrace a k)
  | a, 0 => inferInstanceAs (MeasurableSpace (RawHistory a))
  | a, k+1 => by
    letI : ∀ n : ℕ, MeasurableSpace (RawCycleWordTrace (a+2*(n+1)) k) :=
      fun n => rawCycleWordMeasurable (a+2*(n+1)) k
    exact inferInstanceAs (MeasurableSpace (Σ n : ℕ, RawHistory (a+2*(n+1)) × RawCycleWordTrace (a+2*(n+1)) k))

noncomputable instance instMeasurableSpaceRawCycleWordTrace (a k : ℕ) : MeasurableSpace (RawCycleWordTrace a k) := rawCycleWordMeasurable a k

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrdinaryMarkedWindow
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelPotential

noncomputable def ordinaryCostWindow (v H : ℝ) : Set OddCost := Prod.snd ⁻¹' Icc v (v+H)

lemma ordinaryCostWindow_measurable (v H : ℝ) : MeasurableSet (ordinaryCostWindow v H) :=
  measurableSet_Icc.preimage measurable_snd

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawIncreasingPrefix
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

noncomputable def increasingCosts (a b : ℕ) : Set (RawHistory b) :=
  {h | ∀ i j : Finset.Iic b, a ≤ i.1 → i.1 ≤ j.1 → (h i).2 ≤ (h j).2}

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawSuppliedPast
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

variable (F : CostState → ℝ) (hF : Measurable F)
variable (hStep : ∀ z, ∀ᵐ y ∂costKernel z, F z ≤ F y)

noncomputable def scalarHistory (b : ℕ) (h : RawHistory b) : RawHistory b := fun i => ((h i).1,F (h i))

noncomputable def scalarIncreasing (a b : ℕ) : Set (RawHistory b) :=
  scalarHistory F b ⁻¹' increasingCosts a b

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteVisitMass
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.TransitionKernels

abbrev FiniteRawHistory := Σ n : ℕ, RawHistory n

noncomputable def finiteRawLast (h : FiniteRawHistory) : CostState := rawLast h.1 h.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RawFirstPrefixLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

local instance instMeasurableSingletonClassState_3_r195863_1 : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e => simpa only [image_singleton] using ((measurableSet_singleton e).inl_image : MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o => simpa only [image_singleton] using ((measurableSet_singleton o).inr_image : MeasurableSet (Sum.inr '' {o} : Set State))
noncomputable def firstPrefixMarkEvent (a : ℕ) (b : Bool) : Set (RawHistory (a+1)) :=
  {h | firstArrivalMark (rawLast (a+1) h)=b}

lemma firstPrefixMarkEvent_measurable (a : ℕ) (b : Bool) : MeasurableSet (firstPrefixMarkEvent a b) :=
  (firstArrivalMark_measurable.comp (rawLast_measurable (a+1))) (measurableSet_singleton b)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CanonicalPairHitEvents
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

noncomputable def pairHitTest (a k b : ℕ) (hab : a+2*k+1 ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  {h | h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩ ∈ regenerationSet ∧
    firstArrivalMark (h ⟨a+2*k+1,Finset.mem_Iic.mpr hab⟩)=true ∧
    (h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩).2 ∈ Icc v (v+H)}

lemma pairHitTest_measurable (a k b : ℕ) (hab : a+2*k+1 ≤ b) (v H : ℝ) :
    MeasurableSet (pairHitTest a k b hab v H) :=
  (regenerationSet_measurable.preimage (measurable_pi_apply _)).inter
    (((firstArrivalMark_measurable.comp (measurable_pi_apply _)) (measurableSet_singleton true)).inter
      (measurableSet_Icc.preimage (measurable_snd.comp (measurable_pi_apply _))))

noncomputable def noPairHits (a m b : ℕ) (hab : a+2*m ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  {h | ∀ k : Fin m, h ∉ pairHitTest a k.1 b (by have hk:=k.2; omega) v H}

lemma noPairHits_measurable (a m b : ℕ) (hab : a+2*m ≤ b) (v H : ℝ) :
    MeasurableSet (noPairHits a m b hab v H) := by
  unfold noPairHits
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (pairHitTest_measurable a k.1 b (by have hk:=k.2; omega) v H).compl

noncomputable def firstPairHitEvent (a n b : ℕ) (hab : a+2*n+1 ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  noPairHits a n b (by omega) v H ∩ pairHitTest a n b hab v H

lemma firstPairHitEvent_measurable (a n b : ℕ) (hab : a+2*n+1 ≤ b) (v H : ℝ) :
    MeasurableSet (firstPairHitEvent a n b hab v H) :=
  (noPairHits_measurable a n b (by omega) v H).inter (pairHitTest_measurable a n b hab v H)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalPairCylinders
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable def pairSurvivingHistory (a n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2*n)) :=
  (rawExtension a (a+2*n)).restrict (noPairHits_measurable a n (a+2*n) le_rfl v H)

noncomputable def pairStoppedHistory (a n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2*n+1)) :=
  (rawExtension a (a+2*n+1)).restrict (firstPairHitEvent_measurable a n (a+2*n+1) le_rfl v H)

instance pairSurvivingHistory_isFiniteKernel (a n : ℕ) (v H : ℝ) : IsFiniteKernel (pairSurvivingHistory a n v H) := by
  unfold pairSurvivingHistory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance pairStoppedHistory_isFiniteKernel (a n : ℕ) (v H : ℝ) : IsFiniteKernel (pairStoppedHistory a n v H) := by
  unfold pairStoppedHistory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ConsecutivePairStop
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

noncomputable def boundedPairCylinder (a N n : ℕ) (v H : ℝ) : Set (RawHistory N) :=
  if hn : a+2*n+1 ≤ N then firstPairHitEvent a n N hn v H else ∅

lemma boundedPairCylinder_measurable (a N n : ℕ) (v H : ℝ) : MeasurableSet (boundedPairCylinder a N n v H) := by
  unfold boundedPairCylinder
  split_ifs with hn
  · exact firstPairHitEvent_measurable a n N hn v H
  · exact MeasurableSet.empty

noncomputable def anyPairHit (a N : ℕ) (v H : ℝ) : Set (RawHistory N) :=
  {h | ∃ n : ℕ, ∃ hn : a+2*n+1 ≤ N, h ∈ pairHitTest a n N hn v H}

lemma anyPairHit_measurable (a N : ℕ) (v H : ℝ) : MeasurableSet (anyPairHit a N v H) := by
  unfold anyPairHit
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact pairHitTest_measurable a n N hn v H

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

noncomputable def completedPairHit (a N n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory N) :=
  (rawExtension a N).restrict (boundedPairCylinder_measurable a N n v H)

instance completedPairHit_isFiniteKernel (a N n : ℕ) (v H : ℝ) : IsFiniteKernel (completedPairHit a N n v H) := by
  unfold completedPairHit
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.KernelPotential

noncomputable def regenerativeCostWindow (v H : ℝ) : Set CostState :=
  regenerationSet ∩ (Prod.snd ⁻¹' Icc v (v+H))

lemma regenerativeCostWindow_measurable (v H : ℝ) : MeasurableSet (regenerativeCostWindow v H) :=
  regenerationSet_measurable.inter (measurableSet_Icc.preimage measurable_snd)

noncomputable def markedArrival : Set CostState := {z | firstArrivalMark z=true}
lemma markedArrival_measurable : MeasurableSet markedArrival := firstArrivalMark_measurable (measurableSet_singleton true)

noncomputable def consecutiveCapture (v H : ℝ) : Kernel CostState CostState :=
  (costKernel.restrict markedArrival_measurable) ∘ₖ stateFilter (regenerativeCostWindow_measurable v H)

noncomputable def consecutiveFirstContinue (v H : ℝ) : Kernel CostState CostState :=
  Kernel.piecewise (regenerativeCostWindow_measurable v H)
    (costKernel.restrict markedArrival_measurable.compl) costKernel

noncomputable def consecutiveContinue (v H : ℝ) : Kernel CostState CostState :=
  costKernel ∘ₖ consecutiveFirstContinue v H

instance consecutiveCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveCapture v H) := by
  unfold consecutiveCapture
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance consecutiveFirstContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveFirstContinue v H) := by
  unfold consecutiveFirstContinue
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance consecutiveContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveContinue v H) := by
  unfold consecutiveContinue
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def consecutiveMarkedHit (v H : ℝ) : Kernel CostState CostState :=
  potential (consecutiveCapture v H) (consecutiveContinue v H)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ConsecutivePowerProjection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

noncomputable def historyGoodInput (a : ℕ) (v H : ℝ) : Set (RawHistory a) :=
  rawLast a ⁻¹' regenerativeCostWindow v H

lemma historyGoodInput_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (historyGoodInput a v H) :=
  (regenerativeCostWindow_measurable v H).preimage (rawLast_measurable a)

noncomputable def firstNoHitHistory (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+1)) :=
  (rawExtension a (a+1)).restrict (pairHitTest_measurable a 0 (a+1) (by omega) v H).compl

instance firstNoHitHistory_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (firstNoHitHistory a v H) := by
  unfold firstNoHitHistory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

noncomputable def noHitPairHistory (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2)) :=
  (rawExtension a (a+2)).restrict (pairHitTest_measurable a 0 (a+2) (by omega) v H).compl

instance noHitPairHistory_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (noHitPairHistory a v H) := by
  unfold noHitPairHistory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CanonicalPairVisitLaw
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelPotential

noncomputable def canonicalPairVisitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) FiniteRawHistory :=
  Kernel.sum (fun n : ℕ => (pairStoppedHistory a n v H).map (@Sigma.mk ℕ RawHistory (a+2*n+1)))

instance canonicalPairVisitKernel_isSFiniteKernel (a : ℕ) (v H : ℝ) : IsSFiniteKernel (canonicalPairVisitKernel a v H) := by
  unfold canonicalPairVisitKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def extendFinitePrefix (N : ℕ) : Kernel FiniteRawHistory (RawHistory N) where
  toFun q := if q.1 ≤ N then rawExtension q.1 N q.2 else 0
  measurable' := by
    apply measurable_sigma_family
    intro n
    by_cases hn : n ≤ N
    · simpa only [hn,ite_true, if_true] using (rawExtension n N).measurable
    · simp only [hn,ite_false, if_false]
      exact measurable_const

instance extendFinitePrefix_isFiniteKernel (N : ℕ) : IsFiniteKernel (extendFinitePrefix N) := by
  refine ⟨⟨1,by simp,?_⟩⟩
  intro q
  change (if q.1 ≤ N then rawExtension q.1 N q.2 else 0) univ ≤ 1
  split_ifs <;> simp

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairBranchFullProjection
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess

noncomputable def pairBranchKernel (b : Bool) : Kernel OddCost OddCost :=
  (markedPairKernel.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd

instance pairBranchKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (pairBranchKernel b) := by
  unfold pairBranchKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OddPairCycleGrouping
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelPotential

noncomputable def pairWindowContinue (v H : ℝ) : Kernel OddCost OddCost :=
  pairBranchKernel false+pairBranchKernel true ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl

instance pairWindowContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (pairWindowContinue v H) := by
  unfold pairWindowContinue
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalUniformMissingVisit
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw

noncomputable def canonicalEvenPairVisitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) FiniteRawHistory :=
  canonicalPairVisitKernel (a+1) v H ∘ₖ rawExtension a (a+1)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.ArrivalKernelGeometry

noncomputable def closedNoHitEvent (a N : ℕ) (r b0 b1 ell : ℝ) : Set (RawHistory N) :=
  (anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ ∩
    {past | gapAt r (rawLast N past).2 < 10*b0 ∨ currentExponent (Real.log r) (rawLast N past) ≤ ell}

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualThresholdArrival
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CanonicalGapExposure
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures ArrivalKernelGeometry RegeneratingInverseBands
open Erdos970Dependency.MarkedVisits
attribute [local instance] Classical.propDecidable

def coordinate (N : ℕ) (h : RawHistory N) (j : Fin (N+1)) : CostState :=
  h ⟨j.1,Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩

noncomputable def pathExposure (v a L : ℝ) (N : ℕ) (h : RawHistory N) : ℝ :=
  ∑ j : Fin (N+1),if a ≤ gapValue v (coordinate N h j) ∧ stateRatio (coordinate N h j).1 ≤ L
    then 1/gapValue v (coordinate N h j) else 0

end NumberTheoryLean.CanonicalGapExposure

end

section

namespace NumberTheoryLean.CanonicalEvenArrivalSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ActualCouplingUpdates ActualSupportIntervals CanonicalGapExposure

def evenArrivalSupport (y : CostState) : Prop := stateSide y.1=.even → 2 ≤ stateRatio y.1

end NumberTheoryLean.CanonicalEvenArrivalSupport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_TwoSidedThresholdKernel
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdKernel
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels KernelDensityBridge DerivativeWeights
open TwoSidedThresholdGeometry ErdosEvenThreshold CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

noncomputable def thickDensityBound : ℝ := (3/2:ℝ)*phiEven 2/phiOdd 6
noncomputable def thickConstant : ℝ := 42*thickDensityBound

end NumberTheoryLean.TwoSidedThresholdKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoSidedThresholdHazard
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdHazard
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels
open TwoSidedThresholdGeometry TwoSidedThresholdKernel CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

noncomputable def thickHazard (R d e : ℝ) : State → ℝ
  | .inl _ => 0
  | .inr s => if 3 ≤ R then
      (oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R (d/R+e))).toReal else 0

end NumberTheoryLean.TwoSidedThresholdHazard

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TwoSidedThresholdArrival
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdArrival
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels ArrivalKernelGeometry RegeneratingInverseBands
open TwoSidedThresholdGeometry TwoSidedThresholdKernel TwoSidedThresholdHazard
open RepresentativeStopGeometry ActualCouplingUpdates

noncomputable def reconstructedParent (v : ℝ) (y : CostState) : ℝ := gapValue v y+currentExponent v y

noncomputable def thickArrival (v d e : ℝ) : Set CostState :=
  {y | stateSide y.1=.even ∧ 3 ≤ reconstructedParent v y ∧
    stateRatio y.1 ∈ thickStrip (reconstructedParent v y) (d/reconstructedParent v y+e)}

end NumberTheoryLean.TwoSidedThresholdArrival

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoSidedThresholdOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ArrivalKernelGeometry RegeneratingInverseBands CanonicalGapExposure
open TwoSidedThresholdArrival TwoSidedThresholdHazard TwoSidedThresholdKernel

noncomputable def thickOccurrence (v d e : ℝ) (N : ℕ) : Set (Hist CostState N) :=
  arrivalOccurrence (thickArrival v d e) N

end NumberTheoryLean.TwoSidedThresholdOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RetainedOccupationLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactLogOccupationTest

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactTestGeometry ActualCouplingUpdates
open CycleResponse AdmissibleCycleTests ArrivalKernelGeometry RegeneratingInverseBands
open NormalizedOccupationLimit EvenStartOccupation

noncomputable def logTest (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) : ℝ :=
  inverseTest H (stateSide x.2) (Real.exp x.1,stateRatio x.2)

noncomputable def arrivalTest (ell : ℝ) (H : Side → ℝ×ℝ → ℝ) : Test :=
  AdmissibleCycleTests.mask {x | stateRatio x.2 < Real.exp x.1/ell} (logTest H)

end NumberTheoryLean.CompactLogOccupationTest

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeOccupationDensity
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeOccupationDensity

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def baseMeasure : Measure (ℝ×State) := (volume : Measure ℝ).prod stateMeasure

noncomputable def density (ell : ℝ) (x : ℝ×State) : ℝ :=
  if stateRatio x.2 < Real.exp x.1/ell then (Real.exp x.1)^2/(stateWeight x.2*costMass) else 0

noncomputable def limitingMeasure (ell : ℝ) : Measure (ℝ×State) :=
  baseMeasure.withDensity (fun x => ENNReal.ofReal (density ell x))

end NumberTheoryLean.PrimeOccupationDensity

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceSourceDecomposition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBoundaryDomain

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ErdosPrimeInputs.HarmonicPrimeMeasure

def BoundaryDomain : Side → ℝ → Prop
  | .even, r => 4 ≤ r
  | .odd, r => 2 ≤ r

end NumberTheoryLean.ActualBoundaryDomain

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CompactAnomalyTest
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def sideSign : Side → ℝ | .even => 1 | .odd => -1

noncomputable def signedAnomaly (i : Side) (r : ℝ) : ℝ := sideSign i*continuousAnomaly i r

end ErdosContinuousAnomaly

end

section

open _root_.Set
namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PositiveGapMajorant

noncomputable def extendedSignedAnomaly (i : Side) (r : ℝ) : ℝ :=
  sideSign i*continuousAnomaly i (max 2 r)

noncomputable def compactAnomalyTest (K : ℝ) (i : Side) (x : ℝ×ℝ) : ℝ :=
  compactCutoff K x*extendedSignedAnomaly i x.1

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationDensityIntegral
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OccupationDensityIntegral

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open CompactInverseTest CompactLogOccupationTest PrimeOccupationDensity
open CycleResponse AdmissibleCycleTests NormalizedOccupationLimit OccupationConstant
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def rawTest (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) : ℝ :=
  H (stateSide x.2) (Real.exp x.1,stateRatio x.2)

end NumberTheoryLean.OccupationDensityIntegral

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionEnvelope
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.ActualCouplingUpdates

noncomputable def fullAnomalyTest (i : Side) (x : ℝ×ℝ) : ℝ := extendedSignedAnomaly i x.1

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectionWeightedIntegral
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.InvariantInverseWeights
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def densityEnvelope (c : ℝ) (x : ℝ×State) : ℝ :=
  density 2 x*Real.exp (-c*Real.exp x.1)

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance

noncomputable def fullWeighted (x : ℝ×State) : ℝ := density 2 x*rawTest fullAnomalyTest x

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionStateSections
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.InvariantInverseWeights
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound

noncomputable def cutoffAmplitude (L A B : ℝ) (s : State) : ℝ :=
  if stateRatio s < L then Sum.elim (fun _ => A) (fun _ => B) s else 0

noncomputable def radialNumerator (r : ℝ) : ℝ :=
  (if 4 < r then r*(r/2-2)*continuousAnomaly .even r else 0)-
    (if 2 < r then (r^2/2-2*r+2)*continuousAnomaly .odd r else 0)

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousCorrectionLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.InvariantCostBound

noncomputable def evenRadial (r : ℝ) : ℝ := r*(r/2-2)*continuousAnomaly .even r
noncomputable def oddRadial (r : ℝ) : ℝ := (r^2/2-2*r+2)*continuousAnomaly .odd r

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RetainedNormalizedReward
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosRetainedRewardTransfer
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeKilledChain NumberTheoryLean.PrimeCompactWeights
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def transferConstant : ℝ := 2*weight .even (199/100)

end ErdosRetainedRewardTransfer

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarFreeGate
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosContinuousOmission
open NumberTheoryLean.FinitePathGeometry
open ErdosBoundaryIntegral Erdos970Dependency.StandardBoundary

noncomputable def omissionLossTerm (n : ℕ) : ℝ :=
  (∫ y in sourceDomain .even,omissionDensity n .even y)+
    ∫ y in sourceDomain .odd,omissionDensity n .odd y

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def freeGate (H : Profile) (i : Side) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..baseCutoff b,H i.flip (r-x) x/(max 1 x)

noncomputable def freeGateIterate : ℕ → Profile → Profile
  | 0,H => H
  | n+1,H => freeGate (freeGateIterate n H)

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def terminalBlock (r b : ℝ) : ℝ := gateIterate 2 omissionForce .odd r b

noncomputable def combinedDensity (n : ℕ) (y : ℝ) : ℝ :=
  (if 1 < y then omissionDensity n .even y else 0)+omissionDensity n .odd y

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarTailRecurrence
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosOmissionBindings

noncomputable def scalarTailIntegrand (n : ℕ) (S b y : ℝ) : ℝ :=
  2*y^2*scalarFreeIterate n terminalBlock (2*y+2-S) b
noncomputable def scalarTailMass (n : ℕ) (S b : ℝ) : ℝ :=
  ∫ y in Ioi 0,scalarTailIntegrand n S b y

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_TerminalForceIntegral
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings
open NumberTheoryLean.FinitePathGeometry

noncomputable def terminalOuterIntegrand (S : ℝ) (p : ℝ×ℝ) : ℝ :=
  if S/2+p.2 ≤ p.1 then
    2*p.1^2*gate omissionForce .even (2*p.1+2-S-p.2) p.2/(max 1 p.2) else 0

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ReferenceHighIntervals
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHighIntervals

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry ReferenceSourcePrimeSets ReferenceMertens
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def highInterval (b : ℝ) (closed : Bool) : Set ℝ :=
  {x | 2<x ∧ capGuard closed b x}

end NumberTheoryLean.ReferenceHighIntervals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionFloorRemainder
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def sourcePrefactor (s : ℝ) : ℝ := phiEven s/s^2

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConductorCompletedL
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section
open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology
open _root_.Filter _root_.Set _root_.Asymptotics

namespace RealCharacterAnalysis

open _root_.Complex _root_.Erdos970.Complex _root_.Erdos970.Complex.Hadamard

noncomputable def divisorIndexEquivAnalytic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    divisorZeroIndex₀ f Set.univ ≃ Σ z : ℂ, Fin (analyticOrderNatAt f z) := by
  have horder : analyticOrderNatAt f 0 = 0 := by
    rw [analyticOrderNatAt, (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
    rfl
  have horigin : ∀ p : divisorZeroIndex f Set.univ, p.1 ≠ 0 := by
    rintro ⟨z, i⟩ hz
    dsimp at hz
    subst z
    have hi : Fin 0 := by
      simpa only [toNat_divisor_eq_analyticOrderNatAt hf, horder] using i
    exact Fin.elim0 hi
  exact (Equiv.subtypeUnivEquiv horigin).trans
    (Equiv.sigmaCongrRight fun z => finCongr (toNat_divisor_eq_analyticOrderNatAt hf z))

end RealCharacterAnalysis

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

open scoped BigOperators

namespace WeightedTorusJets

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

noncomputable def homogeneousDeformation (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial σ (Polynomial R) :=
  homogeneousComponent d (polynomialDeformation f d i)

end WeightedTorusJets

open Module

open MvPolynomial

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HilbertSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertSeries_eq_add_X_mul_colon {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (i : σ) :
    hilbertSeries I = hilbertSeries (I ⊔ Ideal.span {X i}) +
      PowerSeries.X * hilbertSeries (I.colon {X i}) := by
  ext n
  rw [map_add, ← pow_one (PowerSeries.X : PowerSeries ℚ), PowerSeries.coeff_X_pow_mul']
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  have h := finrank_degreePiece_sup_span_add_colon hI (isHomogeneous_X K i) n
  split_ifs with hn
  · rw [ite_eq_left hn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hn, add_zero] at h
    simpa only [add_zero] using congrArg (Nat.cast : ℕ → ℚ) h.symm

theorem exists_hilbertSeries_numerator (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ d : ℕ, ∃ p : Polynomial ℚ,
      (1 - PowerSeries.X) ^ d * hilbertSeries I = (p : PowerSeries ℚ) := by
  apply hilbertRational_of_noetherian_recurrence hilbertSeries
    (fun J ↦ J.IsHomogeneous (homogeneousSubmodule σ K)) ?_ I hI
  intro J hJ
  by_cases hvars : ∀ i : σ, X i ∈ J
  · left
    have hconstant : hilbertSeries J =
        (Polynomial.C (Module.finrank K (degreePiece J 0) : ℚ) : PowerSeries ℚ) := by
      ext n
      cases n with
      | zero => simp [hilbertSeries]
      | succ n =>
        simp [hilbertSeries, finrank_degreePiece_eq_zero_of_variables_mem J hvars (Nat.succ_pos n)]
    rw [hconstant]
    exact HilbertRational.polynomial _
  · right
    push Not at hvars
    obtain ⟨i, hi⟩ := hvars
    refine ⟨J ⊔ Ideal.span {X i}, J.colon {X i}, ?_, Ideal.le_colon,
      ?_, colon_isHomogeneous hJ (isHomogeneous_X K i),
      hilbertSeries_eq_add_X_mul_colon hJ i⟩
    · refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply hi
      rw [heq]
      exact (le_sup_right : Ideal.span {X i} ≤ J ⊔ Ideal.span {X i})
        (Ideal.subset_span (Set.mem_singleton (X i)))
    · apply hJ.sup
      apply Ideal.homogeneous_span
      intro f hf
      rcases hf with rfl
      exact ⟨1, isHomogeneous_X K i⟩

theorem exists_hilbertSeries_eq_mul_invOneSubPow (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℚ, ∃ d : ℕ,
      hilbertSeries I = p * PowerSeries.invOneSubPow ℚ d :=
  HilbertRational.exists_mul_invOneSubPow (exists_hilbertSeries_numerator I hI)

theorem existsUnique_hilbertPolynomial (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃! P : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨p, d, hpd⟩ := exists_hilbertSeries_eq_mul_invOneSubPow I hI
  have h := Polynomial.existsUnique_hilbertPoly p d
  simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h

noncomputable def hilbertPolynomial (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : Polynomial ℚ :=
  (existsUnique_hilbertPolynomial I hI).choose

theorem hilbertPolynomial_spec (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = (hilbertPolynomial I hI).eval (n : ℚ) :=
  (existsUnique_hilbertPolynomial I hI).choose_spec.1

theorem hilbertPolynomial_eq_of_eventual_eval (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {P : Polynomial ℚ}
    (hP : ∃ N : ℕ, ∀ n > N,
      (Module.finrank K (degreePiece I n) : ℚ) = P.eval (n : ℚ)) :
    hilbertPolynomial I hI = P :=
  ((existsUnique_hilbertPolynomial I hI).choose_spec.2 P hP).symm

theorem exists_reduced_hilbertSeries (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℚ, ∃ d : ℕ,
      hilbertSeries I = p * PowerSeries.invOneSubPow ℚ d ∧
        (d = 0 ∨ p.eval 1 ≠ 0) := by
  obtain ⟨p, d, hpd⟩ := exists_hilbertSeries_eq_mul_invOneSubPow I hI
  obtain ⟨q, e, hqe, hred⟩ := PowerSeries.exists_reduced_mul_invOneSubPow p d
  exact ⟨q, e, hpd.trans hqe, hred⟩

end WeightedTorusJets.Geometry.GradedQuotient

open _root_.Filter

open scoped BigOperators

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial _root_.Filter

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hne : hilbertPolynomial I hI ≠ 0) :
    ∃ z : ℤ, 0 < z ∧ (z : ℚ) =
      ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
        (hilbertPolynomial I hI).leadingCoeff := by
  obtain ⟨p, d, hpd, hred⟩ := exists_reduced_hilbertSeries I hI
  have hP : hilbertPolynomial I hI = Polynomial.hilbertPoly p d := by
    apply hilbertPolynomial_eq_of_eventual_eval
    refine ⟨p.natDegree, fun n hn ↦ ?_⟩
    have h := Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (p := p) d hn
    simpa only [← hpd, hilbertSeries, PowerSeries.coeff_mk] using h
  have hd : d ≠ 0 := by
    intro hd
    apply hne
    rw [hP, hd, Polynomial.hilbertPoly_zero_right]
  have hp : p.eval 1 ≠ 0 := hred.resolve_left hd
  have hclear : (1 - PowerSeries.X) ^ d * hilbertSeries I = (p : PowerSeries ℚ) := by
    rw [hpd, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    simp only [mul_left_comm (PowerSeries.invOneSubPow ℚ d).inv,
      Units.inv_val, mul_one]
  obtain ⟨z, hz⟩ := numerator_eval_one_is_integer (hilbertSeries I)
    (fun n => ⟨(Module.finrank K (degreePiece I n) : ℤ), by simp [hilbertSeries]⟩) p d hclear
  have heq : ((hilbertPolynomial I hI).natDegree.factorial : ℚ) *
      (hilbertPolynomial I hI).leadingCoeff = p.eval 1 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    rw [hP, Polynomial.natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp,
      Polynomial.factorial_mul_leadingCoeff_hilbertPoly_succ hp]
  have hlead : 0 < (hilbertPolynomial I hI).leadingCoeff := by
    apply leadingCoeff_pos_of_eventually_nat_eval_nonneg _ hne
    obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
    filter_upwards [eventually_gt_atTop N] with n hn
    rw [← hN n hn]
    positivity
  refine ⟨z, ?_, hz.trans heq.symm⟩
  have hpos : 0 < (z : ℚ) := by
    rw [hz, ← heq]
    exact mul_pos (by positivity) hlead
  exact_mod_cast hpos

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def projectiveDegree (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : ℕ :=
  if h : hilbertPolynomial I hI = 0 then 0
  else (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI h).choose.toNat

end WeightedTorusJets.Geometry.GradedQuotient

end
end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RectangleThreshold
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets.Geometry



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def coefficientDerivation (σ : Type*) (D : Derivation ℚ A A) :
    Derivation ℚ (MvPolynomial σ A) (MvPolynomial σ A) where
  toLinearMap := coefficientDerivationLinear σ D
  map_one_eq_zero' := by
    rw [MvPolynomial.one_def, coefficientDerivationLinear_monomial]
    simp
  leibniz' p q := by
    induction p using MvPolynomial.induction_on' with
    | add p r hp hr =>
        simp only [add_mul, map_add, hp, hr, smul_eq_mul]
        ring
    | monomial d a =>
        induction q using MvPolynomial.induction_on' with
        | add q r hq hr =>
            simp only [mul_add, map_add, hq, hr, smul_eq_mul]
            ring
        | monomial e b =>
            simp only [MvPolynomial.monomial_mul_monomial,
              coefficientDerivationLinear_monomial, Derivation.leibniz, smul_eq_mul,
              map_add, add_comm e d]

@[simp] theorem coefficientDerivation_coeff (σ : Type*) (D : Derivation ℚ A A)
    (p : MvPolynomial σ A) (d : σ →₀ ℕ) :
    (coefficientDerivation σ D p).coeff d = D (p.coeff d) := rfl

@[simp] theorem coefficientDerivation_monomial (σ : Type*) (D : Derivation ℚ A A)
    (d : σ →₀ ℕ) (a : A) :
    coefficientDerivation σ D (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (D a) :=
  coefficientDerivationLinear_monomial σ D d a

@[simp] theorem coefficientDerivation_C (σ : Type*) (D : Derivation ℚ A A) (a : A) :
    coefficientDerivation σ D (MvPolynomial.C a) = MvPolynomial.C (D a) :=
  coefficientDerivation_monomial σ D 0 a

@[simp] theorem coefficientDerivation_X (σ : Type*) (D : Derivation ℚ A A) (i : σ) :
    coefficientDerivation σ D (MvPolynomial.X i) = 0 := by
  simp [MvPolynomial.X]

theorem derivation_mem_span_of_vanishes (D : Derivation ℚ A A) (s : Set A)
    (h : ∀ a ∈ s, D a = 0) {a : A} (ha : a ∈ Ideal.span s) :
    D a ∈ Ideal.span s := by
  induction ha using Submodule.span_induction with
  | mem a ha => simp [h a ha]
  | zero => simp
  | add a b ha hb hda hdb => simpa using (Ideal.span s).add_mem hda hdb
  | smul r a ha hda =>
      simpa only [Derivation.leibniz, smul_eq_mul] using
        (Ideal.span s).add_mem ((Ideal.span s).mul_mem_left r hda)
          ((Ideal.span s).mul_mem_right (D r) ha)

@[simp] theorem quotientDerivation_mk (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (a : A) :
    quotientDerivation D I hI (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (D a) := by
  unfold quotientDerivation
  apply Derivation.liftOfSurjective_apply

theorem coefficientDerivation_mem_rectangularIdeal (σ : Type*)
    (k : σ → ℕ) (D : Derivation ℚ A A) {p : MvPolynomial σ A}
    (hp : p ∈ rectangularIdeal k) :
    coefficientDerivation σ D p ∈ rectangularIdeal k := by
  apply derivation_mem_span_of_vanishes _ _ _ hp
  rintro _ ⟨i, rfl⟩
  simp

def rectangularCoefficientDerivation (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) :
    Derivation ℚ (MvPolynomial σ A ⧸ rectangularIdeal k)
      (MvPolynomial σ A ⧸ rectangularIdeal k) :=
  quotientDerivation (coefficientDerivation σ D) (rectangularIdeal k)
    (fun _ hp => coefficientDerivation_mem_rectangularIdeal σ k D hp)

@[simp] theorem rectangularCoefficientDerivation_mk (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (p : MvPolynomial σ A) :
    rectangularCoefficientDerivation σ k D (Ideal.Quotient.mk (rectangularIdeal k) p) =
      Ideal.Quotient.mk (rectangularIdeal k) (coefficientDerivation σ D p) :=
  quotientDerivation_mk _ _ _ p

theorem rectangularCoefficientDerivation_X (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) :
    rectangularCoefficientDerivation σ k D
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i)) = 0 := by
  simp

theorem rectangularVariable_pow_eq_zero {σ R : Type*} [CommRing R]
    (k : σ → ℕ) (i : σ) :
    (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i : MvPolynomial σ R)) ^ k i =
      0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {σ R S : Type*} [CommRing R] [CommRing S]

def rectangularMap (k : σ → ℕ) (f : R →+* S) :
    (MvPolynomial σ R ⧸ rectangularIdeal k) →+*
      (MvPolynomial σ S ⧸ rectangularIdeal k) := by
  let g := (Ideal.Quotient.mk (rectangularIdeal k)).comp (MvPolynomial.map f)
  apply Ideal.Quotient.lift (rectangularIdeal k) g
  have hg : rectangularIdeal k ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g ((MvPolynomial.X i) ^ k i) = 0
    simp only [g, RingHom.comp_apply, map_pow, MvPolynomial.map_X]
    exact rectangularVariable_pow_eq_zero k i
  exact fun p hp => hg hp

@[simp] theorem rectangularMap_mk (k : σ → ℕ) (f : R →+* S) (p : MvPolynomial σ R) :
    rectangularMap k f (Ideal.Quotient.mk (rectangularIdeal k) p) =
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.map f p) := rfl

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def nilpotentDerivationExp (D : Derivation ℚ A A)
    (hD : IsNilpotent D.toLinearMap) : A →ₐ[ℚ] A where
  toFun := fun a => (IsNilpotent.exp D.toLinearMap : Module.End ℚ A) a
  map_zero' := (IsNilpotent.exp D.toLinearMap : Module.End ℚ A).map_zero
  map_add' := (IsNilpotent.exp D.toLinearMap : Module.End ℚ A).map_add
  map_one' := by
    simpa using IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := (1 : A))
      (k := 1) (by simp) hD
  map_mul' := Module.End.exp_mul_of_derivation ℚ A D.toLinearMap
    (fun x y => by simp [smul_eq_mul, mul_comm]) hD
  commutes' r := by
    have hone : IsNilpotent.exp D.toLinearMap (1 : A) = 1 := by
      simpa using IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := (1 : A))
        (k := 1) (by simp) hD
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hone]

theorem scaledDerivation_pow_apply (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) (n : ℕ) (a : A) :
    ((u • D).toLinearMap ^ n) a = u ^ n * (D.toLinearMap ^ n) a := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe,
        Derivation.smul_apply, smul_eq_mul, ih, Derivation.leibniz,
        Derivation.leibniz_pow, hu, smul_zero, mul_zero, add_zero]
      ring

theorem scaledDerivation_pow_eq_zero (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) :
    (u • D).toLinearMap ^ n = 0 := by
  ext a
  change ((u • D).toLinearMap ^ n) a = 0
  rw [scaledDerivation_pow_apply D u hu, hn, zero_mul]

def truncatedTaylor (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) : A →ₐ[ℚ] A :=
  nilpotentDerivationExp (u • D) ⟨n, scaledDerivation_pow_eq_zero D u hu hn⟩

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def rectangularTaylorAlong (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) :
    (MvPolynomial σ A ⧸ rectangularIdeal k) →ₐ[ℚ]
      (MvPolynomial σ A ⧸ rectangularIdeal k) :=
  truncatedTaylor (rectangularCoefficientDerivation σ k D)
    (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i))
    (rectangularCoefficientDerivation_X σ k D i)
    (rectangularVariable_pow_eq_zero k i)

@[simp] theorem rectangularCoefficientDerivation_zero (σ : Type*) (k : σ → ℕ) :
    rectangularCoefficientDerivation σ k (0 : Derivation ℚ A A) = 0 := by
  apply Derivation.ext
  intro p
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [rectangularCoefficientDerivation_mk]
  have hp : coefficientDerivation σ (0 : Derivation ℚ A A) p = 0 := by
    ext d
    simp
  simp [hp]

@[simp] theorem rectangularTaylorAlong_zero (σ : Type*) (k : σ → ℕ) (i : σ) :
    rectangularTaylorAlong σ k (0 : Derivation ℚ A A) i = AlgHom.id ℚ _ := by
  ext p
  simp [rectangularTaylorAlong, truncatedTaylor, nilpotentDerivationExp]

end

end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DerivationJet
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators

noncomputable section

namespace WeightedTorusJets.Geometry

open MvPolynomial

instance finite_rectangularQuotient {σ K : Type*} [Fintype σ] [CommRing K] (k : σ → ℕ) :
    Module.Finite K (MvPolynomial σ K ⧸ rectangularIdeal k) :=
  Module.Finite.of_basis (rectangularQuotientBasis k)

open MvPolynomial

def rectangularAugmentation {σ K : Type*} [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    (MvPolynomial σ K ⧸
      Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i)) →ₐ[K] K :=
  quotientAugmentation _ (rectangularIdeal_le_ker_constantCoeff k hk)

end WeightedTorusJets.Geometry

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLinearCoefficients
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section
noncomputable section
namespace WeightedTorusJets.Geometry
open MvPolynomial

theorem varsCotangentCoefficients_injective {σ K : Type*} [CommRing K] :
    Function.Injective (varsCotangentCoefficients (σ := σ) (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := (idealOfVars σ K).toCotangent_surjective x
  apply ((idealOfVars σ K).toCotangent_eq_zero p).mpr
  rw [mem_vars_square_iff]
  refine ⟨?_, fun i => congrFun hx i⟩
  exact (mem_pow_idealOfVars_iff' 1 (p : MvPolynomial σ K)).mp
    (by simpa only [pow_one] using p.property) 0 (by simp)

theorem varsCotangentCoefficients_surjective
    {σ K : Type*} [Fintype σ] [CommRing K] :
    Function.Surjective (varsCotangentCoefficients (σ := σ) (K := K)) := by
  classical
  intro v
  let p : MvPolynomial σ K := ∑ i, v i • X i
  have hp : p ∈ idealOfVars σ K := by
    apply Ideal.sum_mem
    intro i _
    exact ((idealOfVars σ K).restrictScalars K).smul_mem (v i)
      (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨(idealOfVars σ K).toCotangent ⟨p, hp⟩, ?_⟩
  ext i
  simp [p, coeff_X, Finsupp.single_left_inj, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]

def varsCotangentEquiv {σ K : Type*} [Fintype σ] [CommRing K] :
    (idealOfVars σ K).Cotangent ≃ₗ[K] (σ → K) :=
  LinearEquiv.ofBijective varsCotangentCoefficients
    ⟨varsCotangentCoefficients_injective, varsCotangentCoefficients_surjective⟩

theorem quotientVarsCotangentMap_surjective {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) :
    Function.Surjective (quotientVarsCotangentMap J) := by
  intro x
  obtain ⟨b, rfl⟩ := ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent_surjective x
  obtain ⟨p, hp, hpb⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective).mp b.property
  refine ⟨(idealOfVars σ K).toCotangent ⟨p, hp⟩, ?_⟩
  change ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent
    ⟨Ideal.Quotient.mk J p, _⟩ = _
  congr 1
  exact Subtype.ext hpb

def polynomialQuotientCotangentEquiv {σ K : Type*} [Fintype σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2) :
    ((idealOfVars σ K).map (Ideal.Quotient.mk J)).Cotangent ≃ₗ[K] (σ → K) :=
  (LinearEquiv.ofBijective (quotientVarsCotangentMap J)
    ⟨quotientVarsCotangentMap_injective J hJ, quotientVarsCotangentMap_surjective J⟩).symm.trans
      varsCotangentEquiv

@[simp] theorem polynomialQuotientCotangentEquiv_map_toCotangent
    {σ K : Type*} [Fintype σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2)
    (p : idealOfVars σ K) (i : σ) :
    polynomialQuotientCotangentEquiv J hJ
      (quotientVarsCotangentMap J ((idealOfVars σ K).toCotangent p)) i =
        (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := by
  let e := LinearEquiv.ofBijective (quotientVarsCotangentMap J)
    ⟨quotientVarsCotangentMap_injective J hJ, quotientVarsCotangentMap_surjective J⟩
  change varsCotangentEquiv (e.symm (e ((idealOfVars σ K).toCotangent p))) i = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszTermCalculus
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

noncomputable def rieszDirichletTerm (f : ℕ → ℂ) (sigma X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n *
    rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RieszRectangle
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex

noncomputable def rieszContourLeft (a : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  1-a/(modulusHeight q T)^2
noncomputable def rieszContourRectangle (a : ℝ) (q : ℕ) (sigma T : ℝ) : Set ℂ :=
  Icc (rieszContourLeft a q T) sigma ×ℂ Icc (-T) T

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_IntervalPrimesDefinition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open Finset

theorem mem_intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) (p : ℕ) :
    p ∈ intervalPrimes x H q r ↔
      p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),h⟩
    exact (Nat.le_floor_iff (le_max_right _ _)).mpr (h.2.2.1.trans (le_max_left _ _))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset

noncomputable def retainedPrimes (d : ℕ) (a b t : ℝ) : Finset ℕ :=
  if t ≤ b-a then primeIntervalFlags false false (a/(d:ℝ)) (b/(d:ℝ)) else ∅

end Erdos970Dependency.SiegelWalfisz



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SquarefreeHarmonic
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable def cutoffNormalization (z R : ℕ) : ℝ :=
  normalization (IntervalBoundingSieve.intervalSieve 0 0
    (IntervalBoundingSieve.cutoffProduct z) (IntervalBoundingSieve.cutoffProduct_squarefree z)) R

end NumberTheoryLean.SelbergOptimization

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeDensityBlocks
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped BigOperators

def supportCost (m J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (J + 1), 2 ^ (j + 1) * (2 * reverseOrder m J j + 1)

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TagPrimePartition
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

noncomputable def intersectionPrimes (R V : ℝ) (Q : ℕ) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t)

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
open scoped _root_.Erdos970



namespace ErdosStoppedTagSieve





open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
open NumberTheoryLean
attribute [local instance] Classical.propDecidable

noncomputable def basePrimes (R V : ℝ) (Q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => p%Q∈A)
noncomputable def survivorPrimes (R V : ℝ) (Q : ℕ) (S A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) : Finset ℕ :=
  (basePrimes R V Q A).filter (fun p => ∀ t∈S,(p:ZMod t)≠rho t)

end ErdosStoppedTagSieve



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TagAffineConditions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

noncomputable def actualSurvivorPrimes (P R V : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => (D:ℤ)∣A+B*p ∧
    ∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t)

end ErdosStoppedTagSieve


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HypotheticalSubbinLower
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosCommonMInterval ErdosAlignedProgression
  ErdosInverseAlignment ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem subbin_primality (R V : ℝ) : ∀ p ∈ intervalPrimes R V 1 0,p.Prime := by
  intro p hp
  exact ((mem_intervalPrimes R V 1 0 p).mp hp).1

end ErdosStoppedArithmetic


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepeatedStepRowBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedStepRowBound
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open PersistentFailureFlag ActualCouplingUpdates
open CompletedParentInterval ContinuousIntervalUpper
open ContinuousKilledBins
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


noncomputable def repeatDensityConstant : ℝ := Classical.choose completed_parent_interval_upper

noncomputable def repeatBudget (U X xi w mesh : ℝ) : ℝ :=
  repeatDensityConstant*(U+2)^2*(U*(xi/Real.log w)/X+2*mesh)

end NumberTheoryLean.RepeatedStepRowBound


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceParentBenchmark
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
attribute [local instance] Classical.propDecidable
open ErdosCorrectionLimit
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.ReferenceDifferentiation
open NumberTheoryLean.ReferenceLocalResidual NumberTheoryLean.ReferenceMertens

noncomputable def startingSlope (s : ℝ) : ℝ :=
  Function.update (fun t => (startingExtension sieveA t-startingExtension sieveA 2)/(t-2))
    2 (Real.exp Real.eulerMascheroniConstant) s

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ReferenceIntervalBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceIntervalCutoff

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def primeInterval (a b : ℝ) (closed : Bool) : Set ℝ :=
  {x | a<x ∧ capGuard closed b x}

noncomputable def intervalPrimes (w a b : ℝ) (closed : Bool) : Finset ℕ :=
  (highPrimes w b closed).filter (fun p => a<primeExponent w p)

end NumberTheoryLean.ReferenceIntervalCutoff

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalHighRatioVisit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FiniteHistoryTransport NumberTheoryLean.OccupationDecomposition

def positiveVisit (E : Set CostState) (N : ℕ) : Set (∀ _ : Finset.Iic N, CostState) :=
  ⋃ j : Fin N, {path | path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ ∈ E}

end ErdosHighRatioBandTail


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_WrongOwnerBoxMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WrongOwnerBinMass
open PrimeBinAlignmentMass ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def wrongOwnerPrimes (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) : Finset ℕ :=
  (primeBin R xi).filter (fun p => aligns a q p ∧ ∃ r,
    owner Y w Cs eta R xi a=some r ∧ r ≠ q ∧ aligns a r p)

end NumberTheoryLean.WrongOwnerBinMass



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SecondLossKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def secondKernel (p : ℝ×ℝ) : ℝ :=
  (2*(p.1^2-1)/(max 1 p.2))*omissionForce .odd (2*p.1+2-p.2) p.2

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ThirdInnerKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

noncomputable def thirdKernel (p : ℝ×ℝ) : ℝ :=
  if p.2≤p.1 then (2*p.1^2/(max 1 p.2))*gate omissionForce .even (2*p.1+2-p.2) p.2 else 0

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def thirdInnerKernel (x : ℝ) (p : ℝ×ℝ) : ℝ :=
  (p.1^2/(max 1 p.2))*omissionForce .odd (2*p.1+2-x-p.2) p.2

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RepeatedWordEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedWordEvents
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels


noncomputable def searchRepeatedWord {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) : Prop := ∃ b : Fin (binCount w top xi),searchBin w (lower w top xi b) ∧
      2 ≤ (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b

end NumberTheoryLean.RepeatedWordEvents


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
open scoped _root_.Erdos970


namespace NumberTheoryLean.GoodCrossingVisit
open _root_.Set _root_.MeasureTheory FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeTiltGeometry
open RegeneratingInverseBands ArrivalKernelGeometry CrossingPrimeBin CrossingBandGeometry
open IsolatedBinGeometry LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

noncomputable def crossingHighEvent (v H T : ℝ) : Set CostState :=
  {y | T < stateRatio y.1 ∧ y.2 ∈ Icc (crossingCenter v H) (crossingCenter v H+crossingWidth)}

end NumberTheoryLean.GoodCrossingVisit



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CofactorAllChoiceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ParentCofactorChoices
open ErdosCofactorChoices ErdosSubsetWord BinCutSelections AssembleAtBin SingletonBinSelection
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

noncomputable def parentCofactorMultiplicity {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  eraseMultiplicity (aboveMultiplicity m j) i
noncomputable def completeParent {n : ℕ} (anchor f : Fin n → Finset ℕ) (i j : Fin n) (p u : ℕ) : Fin n → Finset ℕ :=
  assemble anchor (fillSelection f i p) j u

end NumberTheoryLean.ParentCofactorChoices



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CompletedMarkEvents
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompletedMarkEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CemeteryKernel
open ArrivalKernelGeometry RegeneratingInverseBands ActualCouplingUpdates

def strongMark (v b₀ b₁ : ℝ) (z : CostState) : Prop :=
  stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
    10*b₀/(313/100) ≤ currentExponent v z ∧ currentExponent v z ≤ b₁/(309/100)

def markedPoint (v b₀ b₁ : ℝ) : Space CostState → Prop :=
  Sum.elim (strongMark v b₀ b₁) (fun _ => False)

def compactPoint (v R : ℝ) : Space CostState → Prop :=
  Sum.elim (fun z => gapValue v z ≤ R) (fun _ => False)

def noStrongBefore (v b₀ b₁ : ℝ) (N k : ℕ) (h : Hist (Space CostState) N) : Prop :=
  ∀ i : Finset.Iic N,i.1 ≤ k → ¬markedPoint v b₀ b₁ (h i)

def badCompactPath (v R b₀ b₁ : ℝ) (N : ℕ) : Set (Hist (Space CostState) N) :=
  {h | ∃ j : Finset.Iic N,compactPoint v R (h j) ∧ noStrongBefore v b₀ b₁ N j.1 h}

end NumberTheoryLean.CompletedMarkEvents

end

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
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetTagFailureMass
open ErdosCofactorChoices ErdosSubsetWord ErdosTagEvent ActualSourceTags ActualBinOwners
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels CanonicalSubsetBox
open WrongOwnerBinMass ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def badSelections {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : Finset (Fin (binCount w top xi) → Finset ℕ) :=
  (selections (globalBins w top xi) mult).filter (fun f =>
    (∀ b ∈ occupiedSearch w top xi mult,∀ p ∈ f b,aligns a q p) ∧
    ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (descendingWord f)=some t ∧ t.rational=q)

noncomputable def badMass {Y w top Cs eta xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (mult : Fin (binCount w top xi) → ℕ) (a : ℕ → ℤ) (q : ℚ) : ℝ :=
  ∑ f ∈ badSelections (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi mult a q,(selectionProduct f:ℝ)⁻¹

end NumberTheoryLean.SubsetTagFailureMass



namespace NumberTheoryLean.RegularBadTagWords
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord ErdosCofactorChoices HardTagWordFamily HardTagBoxMass ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def badWordTest {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) (ps : List ℕ) : Prop :=
    ∃ q ∈ Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      (∀ p ∈ ps,Cs < primeExponent w p → aligns a q p) ∧
      ¬∃ t,sourceTag Y w Cs eta (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) htop hxi) a ps=some t ∧ t.rational=q

end NumberTheoryLean.RegularBadTagWords



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerResidueVariance
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

noncomputable def exponentialSum (S : Finset ℤ) (a q : ℕ) : ℂ :=
  ∑ x ∈ S,AdditiveLargeSieve.exponential (((x : ℝ)*(a : ℝ))/(q : ℝ))

end ErdosInverseSpectrum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerRichLine
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph

noncomputable def integerComplexification (P : MV ℤ) : MV ℂ :=
  MvPolynomial.map (Int.castRingHom ℂ) P

end ErdosRichLine

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawBoxRationalWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.RawBoxRationalWitness
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseCounts ErdosInverseBoxApplication ErdosInverseSampleCost
open ErdosInverseAlignment ErdosInverseStructured ErdosPrimitiveIntercept
open TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def rawBoxList {n : ℕ} (P : Fin n → Finset ℕ) (i : Fin n) (J : Finset (Fin n))
    (a : ℕ → ℕ) (S : Fin n → ℝ) (R Z cp : ℝ) : Finset ℚ :=
  J.biUnion (fun j => sourceRationalList (P i) (fun p => (a p:ℤ)) (S j) R Z cp)

end NumberTheoryLean.RawBoxRationalWitness


end Erdos970

end OAI
end



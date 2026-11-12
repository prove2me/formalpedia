-- Prove2me | Definitions.Def_OAIQ247J010
-- name    : OAIQ247J010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T19:00:26.935479+00:00
-- url     : https://prove2.me/theorems/30f05821-01bd-4eeb-8dbf-9a1023fb8d49
-- title:
--   Definitions bundle OAIQ247J010 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 130 declarations of OpenAI's Lean: 110 definitions, 1 inductive type or structure, 11 instances and 8 theorems. The definitions and types are `OAI.Erdos970.NumberTheoryLean.ActualPrimeHigh.uncappedLowGapHighMass`, `OAI.Erdos970.NumberTheoryLean.ActualPrimeHigh.uncappedRewardedHighMass`, `OAI.Erdos970.NumberTheoryLean.ActualRegularBoxes.regularBoxes`, `OAI.Erdos970.NumberTheoryLean.ActualStopGroupFiber.family`, `OAI.Erdos970.NumberTheoryLean.AdmissibleCycleTests.ShiftContinuous`, `OAI.Erdos970.NumberTheoryLean.AdmittedHighRemoval.lowHighMass`, `OAI.Erdos970.NumberTheoryLean.CanonicalKeyWitness.Witness`, `OAI.Erdos970.NumberTheoryLean.CanonicalStopPartition.keys`, `OAI.Erdos970.NumberTheoryLean.CompactCouplingError.difference`, `OAI.Erdos970.NumberTheoryLean.CompactNormalizationCorrection.correctedExpectation`, `OAI.Erdos970.NumberTheoryLean.CompactNormalizationCorrection.correctedTest`, `OAI.Erdos970.NumberTheoryLean.CompactPrefixOccurrence.occurs`, `OAI.Erdos970.NumberTheoryLean.CompactPrefixOccurrence.selectedNode`, `OAI.Erdos970.NumberTheoryLean.CompactTestGeometry.primeTest`, `OAI.Erdos970.NumberTheoryLean.CostReturnLaw.cycleCostLaw`, `OAI.Erdos970.NumberTheoryLean.CountErrorClassification.badCompactWords`, `OAI.Erdos970.NumberTheoryLean.CountErrorClassification.largeGapWords`, `OAI.Erdos970.NumberTheoryLean.CountErrorClassification.smallErrorWords`, `OAI.Erdos970.NumberTheoryLean.CoupledBoundaryEvents.primeBadCells`, `OAI.Erdos970.NumberTheoryLean.CouplingData.joint`, `OAI.Erdos970.NumberTheoryLean.CouplingData.sourceLaw`, `OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.actualArrivalLaw`, `OAI.Erdos970.NumberTheoryLean.CycleDurationMoments.durationFrom`, `OAI.Erdos970.NumberTheoryLean.CycleOccupation.occupationKernel`, `OAI.Erdos970.NumberTheoryLean.CycleOccupation.occupationMeasure`, `OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw`, `OAI.Erdos970.NumberTheoryLean.CycleResponse.response`, `OAI.Erdos970.NumberTheoryLean.ExpandedCompactPartition.unlistedGeometric`, `OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw`, `OAI.Erdos970.NumberTheoryLean.FullHistoryPrimeOccupation.fullListReward`, `OAI.Erdos970.NumberTheoryLean.FullPathCompactSelection.fullCompactReward`, `OAI.Erdos970.NumberTheoryLean.GeometricBoxImages.geometricBoxes`, `OAI.Erdos970.NumberTheoryLean.HighResidualSum.highResidualAbsoluteSum`, `OAI.Erdos970.NumberTheoryLean.InitialOccupation.beforeRegeneration`, `OAI.Erdos970.NumberTheoryLean.InitialOccupation.initialOccupation`, `OAI.Erdos970.NumberTheoryLean.InitialRegeneration.delayedCostLaw`, `OAI.Erdos970.NumberTheoryLean.LiteralCompactRemoval.uncappedFamilyValue`, `OAI.Erdos970.NumberTheoryLean.LiteralPrimeOccupation.familyValue`, `OAI.Erdos970.NumberTheoryLean.LiteralPrimeOccupation.nodeReward`, `OAI.Erdos970.NumberTheoryLean.LiteralPrimeOccupation.sourceFactor` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Jacobsthal_Analysis_CorrectedCompactTransfer`, `Jacobsthal_Analysis_LiteralCompactRemoval`, `Jacobsthal_Analysis_UncappedCompactMass`, `Jacobsthal_Estimates_AdmittedHighRemoval`, `Jacobsthal_Estimates_GrowingFarTail`, `Jacobsthal_Estimates_LargeGapCountErrors`, `Jacobsthal_Estimates_MovingLocalReference`, `Jacobsthal_Estimates_ReferenceSourceDecomposition`, `Jacobsthal_Estimates_RepeatedStepRowBound`, `Jacobsthal_Estimates_ScaledOriginalTail`, `Jacobsthal_Estimates_SourceReferenceRemainders`, `Jacobsthal_Estimates_UniformFailureBudget`, `Jacobsthal_Partitions_ActualSafeBoxMass`, `Jacobsthal_Partitions_BinCutGapMovement`, `Jacobsthal_Partitions_CompactTestGeometry`, `Jacobsthal_Partitions_PaperGeometricRegularity`, `Jacobsthal_Partitions_ReferenceIntervalBound`, `Jacobsthal_Partitions_RegularityDefectPartition`, `Jacobsthal_Partitions_SourceParentBin`, `Jacobsthal_Partitions_StrongReferenceTransport`, `Jacobsthal_Partitions_SuccessfulTailTransport`, `Jacobsthal_Paths_CanonicalKeyWitness`, `Jacobsthal_Paths_FlaggedSourceStart`, `Jacobsthal_Paths_FullPathCompactSelection`, `Jacobsthal_Paths_FullWordHighAlignment`, `Jacobsthal_Paths_NearPrefixOccurrence`, `Jacobsthal_Paths_PairedHitting`, `Jacobsthal_Primes_AdjacentPrimeRecovery`, `Jacobsthal_Primes_ConditionalPrimeBins`, `Jacobsthal_Primes_FullHistoryPrimeOccupation`, `Jacobsthal_Primes_LiteralUniformPrimeTail`, `Jacobsthal_Primes_PaperMissingPrimeWindow`, `Jacobsthal_Primes_PrimeCompactWeights`, `Jacobsthal_Primes_PrimeGridGeometry`, `Jacobsthal_Primes_PrimeInverseBins`, `Jacobsthal_Primes_PrimeMarginalRecursion`, `Jacobsthal_Probability_ActualCouplingUpdates`, `Jacobsthal_Probability_CouplingLabelEvents`, `Jacobsthal_Probability_MarkedVisitGeometry`, `Jacobsthal_Probability_RegularStoppedEvent`, `Jacobsthal_Probability_RepeatedPairEvents`, `Jacobsthal_Probability_RepeatedPairProbability`, `Jacobsthal_Probability_SourceCompactCoupling`, `Jacobsthal_Probability_SourceThresholdCoupling`, `Jacobsthal_Probability_SuccessfulMarkedCoordinates`, `Jacobsthal_Renewal_NonnegativeOriginalOccupation`, `Jacobsthal_Renewal_OccupationAge`, `Jacobsthal_Renewal_RegenerationBandBounds`, `Jacobsthal_Renewal_SourceSelectedCompactOccupation`, `Jacobsthal_Renewal_UniformCycleMoments`, `Jacobsthal_Sieve_PrimeExponentialTail`, `Jacobsthal_Sieve_UniformExponentialOccupation`.
--
--   **Imports.** It imports the bundles `OAIQ247J008` and `OAIQ247J009` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_Erdos970_Erdos970Final_source_root_survivor_lower_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.root_anomaly_replacement_tendsto_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.root_source_remainder_tendsto_jb247`, `OAI.Erdos970.ErdosVarianceEligible.geometric_selection_recent_witness_jb247`, `OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247`, `OAI.Erdos970.NumberTheoryLean.ActualFiniteCoupling.actual_finite_failure_jb247`, `OAI.Erdos970.NumberTheoryLean.BasicRegularMass.basic_regular_defect_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247`, `OAI.Erdos970.NumberTheoryLean.EvenStartOccupation.source_start_occupation_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247`, `OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.GrowingFarTail.source_growing_far_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.HighGapResidual.high_gap_residual_power_jb247`, `OAI.Erdos970.NumberTheoryLean.HighResidualSum.high_residual_sum_bound_jb247`, `OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247`, `OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.PaperMissingPrimeWindow.paper_missing_prime_window_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceCountEnvelope.reference_count_envelope_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceRepeatedExclusion.uniform_reference_repeated_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceResidualSum.summed_source_residual_bound_jb247`, `OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceCompactErrorMass.source_compact_error_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceSuccessfulTail.source_successful_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247`, `OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247` and `OAI.Erdos970.NumberTheoryLean.UniformGeometricRegularMass.geometric_defect_uniform_in_L_jb247`; the proofs of `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential_jb247`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247`, `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, `OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.root_anomaly_replacement_tendsto_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.root_source_remainder_tendsto_jb247`, `OAI.Erdos970.ErdosVarianceEligible.geometric_selection_recent_witness_jb247`, `OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247`, `OAI.Erdos970.NumberTheoryLean.ActualFiniteCoupling.actual_finite_failure_jb247`, `OAI.Erdos970.NumberTheoryLean.BasicRegularMass.basic_regular_defect_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247`, `OAI.Erdos970.NumberTheoryLean.ContinuousLowOccupationLimit.source_continuous_low_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.ContinuousOccupationIdentification.full_admitted_eq_response_jb247`, `OAI.Erdos970.NumberTheoryLean.EvenStartOccupation.source_start_occupation_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247`, `OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.GrowingFarTail.source_growing_far_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.HighGapResidual.high_gap_residual_power_jb247`, `OAI.Erdos970.NumberTheoryLean.HighResidualSum.high_residual_sum_bound_jb247`, `OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247`, `OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.PaperMissingPrimeWindow.paper_missing_prime_window_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceCountEnvelope.reference_count_envelope_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceRepeatedExclusion.uniform_reference_repeated_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceResidualSum.summed_source_residual_bound_jb247`, `OAI.Erdos970.NumberTheoryLean.RegenerationBandBounds.regeneration_uniform_band_jb247`, `OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceCompactErrorMass.source_compact_error_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247`, `OAI_Erdos970_NumberTheoryLean_SourceModerateFailure_source_moderate_failure_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceRootErrorLower.source_root_lower_with_stopped_correction_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceSuccessfulTail.source_successful_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247`, `OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247`, `OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247`, `OAI.Erdos970.NumberTheoryLean.UniformGeometricRegularMass.geometric_defect_uniform_in_L_jb247` and `OAI_Erdos970_WeightedTorusJets_Geometry_DegreeBezout_coefficient_localization_finrank_le_pow_jb247`.
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
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Definitions.Def_OAIQ247J008
import Definitions.Def_OAIQ247J009

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairedHitting
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

instance pairedKilled_isFiniteKernel : IsFiniteKernel pairedKilled := by unfold pairedKilled; infer_instance

instance pairedKilled_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (pairedKilled ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddState OddState); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (pairedKilled ∘ₖ (pairedKilled ^ n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PairedHitting

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CostReturnLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels PairedHitting PairedBlockContraction PairedCostProcess

instance costKilled_isFiniteKernel : IsFiniteKernel costKilled := by unfold costKilled; infer_instance
instance costCaptured_isFiniteKernel : IsFiniteKernel costCaptured := by unfold costCaptured; infer_instance

instance costKilled_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (costKilled ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (costKilled ∘ₖ (costKilled ^ n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance firstReturn_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstReturn n) := by unfold firstReturn; infer_instance

noncomputable def cycleCostLaw : Measure ℝ := (returnLaw (RegenerationTails.regenerationState, 0)).map Prod.snd

instance cycleCostLaw_isProbabilityMeasure : IsProbabilityMeasure cycleCostLaw :=
  (Measure.isProbabilityMeasure_map_iff (μ := returnLaw (RegenerationTails.regenerationState, 0))
    measurable_snd.aemeasurable).mpr inferInstance

end NumberTheoryLean.CostReturnLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationAge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open TransitionKernels PairedCostProcess CostReturnLaw RegenerationTails

noncomputable def cycleJointLaw : Measure OddCost := returnLaw (regenerationState, 0)

instance cycleJointLaw_isProbabilityMeasure : IsProbabilityMeasure cycleJointLaw := by
  unfold cycleJointLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.CycleRegeneration

end

section

namespace NumberTheoryLean.MarkedCycleLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open PairedCostProcess CostReturnLaw CycleRegeneration

noncomputable def firstMarkedReturn (n : ℕ) : Kernel OddCost MarkedReturn :=
  (firstReturn n).map (markReturn n)

noncomputable def markedReturnLaw : Kernel OddCost MarkedReturn := Kernel.sum firstMarkedReturn

noncomputable def markedCycleLaw : Measure MarkedReturn :=
  markedReturnLaw (RegenerationTails.regenerationState, 0)

end NumberTheoryLean.MarkedCycleLaw

end

section

namespace NumberTheoryLean.CycleDurationMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels PairedHitting PairedDrift PairedBlockContraction PairedCostProcess
open CostReturnLaw MarkedCycleLaw

noncomputable def durationFrom (z : OddCost) : Measure ℕ := (markedReturnLaw z).map Prod.fst

end NumberTheoryLean.CycleDurationMoments

end

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw

noncomputable def occupationKernel : Kernel OddCost CostState := Kernel.sum visitBlock

noncomputable def occupationMeasure : Measure CostState := occupationKernel (RegenerationTails.regenerationState, 0)

end NumberTheoryLean.CycleOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.CycleConvolutionLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open PairedCostProcess CostReturnLaw CycleRegeneration
open AbsorptionCutoff.Renewal

instance returnLaw_pow_isMarkovKernel (n : ℕ) : IsMarkovKernel (returnLaw ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsMarkovKernel (returnLaw ∘ₖ (returnLaw ^ n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def actualArrivalLaw (n : ℕ) : Measure ℝ :=
  ((returnLaw ^ n) (RegenerationTails.regenerationState, 0)).map Prod.snd

end NumberTheoryLean.CycleConvolutionLaw



namespace NumberTheoryLean.CycleResponse

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation
open AbsorptionCutoff.Renewal

noncomputable def response (F : Test) (v : ℝ) : ℝ :=
  ∫ y : CostState, F (v - y.2, y.1) ∂occupationMeasure

end NumberTheoryLean.CycleResponse



namespace NumberTheoryLean.AdmissibleCycleTests

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation CycleResponse

def ShiftContinuous (F : Test) : Prop :=
  ∀ v : ℝ, ∀ᵐ y ∂occupationMeasure, ContinuousAt (fun u => F (u - y.2, y.1)) v

end NumberTheoryLean.AdmissibleCycleTests



namespace NumberTheoryLean.OccupationRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleRegeneration CycleOccupation
open OccupationDecomposition CycleResponse CycleConvolutionLaw

noncomputable def positiveResponse (F : ℝ × State → ℝ≥0∞) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, F (v - y.2, y.1) ∂occupationMeasure

end NumberTheoryLean.OccupationRegeneration



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationBandBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess
open CostReturnLaw CycleRegeneration PairedDrift
open InitialOddDraw

noncomputable def delayedCostLaw (s : EvenState) : Measure ℝ := (delayedRegeneration s).map Prod.snd

end NumberTheoryLean.InitialRegeneration

end

section

namespace NumberTheoryLean.InitialOccupation

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation OccupationDecomposition KernelPotential
open InitialOddDraw InitialRegeneration

noncomputable def beforeRegeneration : Kernel OddCost CostState := by
  classical
  exact Kernel.piecewise returnSet_measurable 0 occupationKernel

noncomputable def initialOccupation : Kernel EvenState CostState :=
  firstOdd.map embedOdd + beforeRegeneration ∘ₖ firstOdd

end NumberTheoryLean.InitialOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

variable (w ell S : ℝ) (start : Node)

variable {w ell S : ℝ} {start : Node}

instance chain_pow_markov [IsMarkovKernel (chain w ell S start)] (n : ℕ) :
    IsMarkovKernel ((chain w ell S start)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (ChainState w ell S start) (ChainState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def pathLaw (w ell S : ℝ) (start : Node) (n : ℕ) : Measure (ChainState w ell S start) :=
  ((chain w ell S start)^n) (some History.empty)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainProbabilities

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeKilledChain

variable {w ell S : ℝ} {start : Node}

noncomputable def nodeProduct (e w : ℝ) (z : Node) (ps : List ℕ) : ℝ :=
  normalizedTiltProduct e w z.side z.ratio z.gap ps

end NumberTheoryLean.PrimeChainProbabilities



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain LowStateHorizon

variable {w ell S : ℝ} {start : Node}

def stage (n : ℕ) : ChainState w ell S start → Prop
  | none => True
  | some h => h.primes.length = n

end NumberTheoryLean.PrimeChainHorizon



namespace NumberTheoryLean.PrimeCorrectionFactor

open _root_.Filter _root_.Set
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain LowStateHorizon

noncomputable def correctionBudget (d w : ℝ) : ℝ :=
  Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1

end NumberTheoryLean.PrimeCorrectionFactor



namespace NumberTheoryLean.PrimeSideSupport

open _root_.Set _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon

def Regular (z : Node) : Prop := regularLower z.side ≤ z.ratio
def WeakRegular (z : Node) : Prop := weakLower z.side ≤ z.ratio

end NumberTheoryLean.PrimeSideSupport



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

namespace NumberTheoryLean.NormalizedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeRatioBins PrimeTiltBounds
open WeightedPrimeBins ContinuousRatioBins PrimeKilledChain

noncomputable def normalizedPrimeBin (w r : ℝ) (i : Side) (s a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, primeTilt w r i s p/(1+epsilon w)

end NumberTheoryLean.NormalizedPrimeBins

end

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

def Consistent (z : Node) : Prop := z.cutoff = z.gap/z.ratio

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem allowed_prime_bounds {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) : ∀ p ∈ ps,
      p.Prime ∧ ell < primeExponent w p ∧ capGuard z.closed z.cutoff (primeExponent w p) := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
    have hdata := (mem_children_iff hw z.side z.closed p).mp hc
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hdata.1,hdata.2.1,hdata.2.2.1⟩
    · have htail := ih ht q hq
      have hqp : primeExponent w q < primeExponent w p := htail.2.2
      refine ⟨htail.1,htail.2.1,?_⟩
      have hpcap := hdata.2.2.1
      cases he : z.closed <;> simp only [capGuard,he,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hpcap ⊢
      · exact hqp.trans hpcap
      · exact hqp.le.trans hpcap

theorem allowed_decreasing {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) : ps.Pairwise (· > ·) := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
    refine List.pairwise_cons.mpr ⟨?_,ih ht⟩
    intro q hq
    have hqp : primeExponent w q < primeExponent w p := (allowed_prime_bounds hw ht q hq).2.2
    exact lt_of_not_ge (fun hpq => (not_lt_of_ge (exponent_monotone hw hpq)) hqp)

theorem allowed_mem_decreasing {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) :
    ps ∈ decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff)) := by
  apply mem_decreasingPrefixes.mpr
  refine ⟨allowed_decreasing hw hpath,?_⟩
  intro p hp
  obtain ⟨hprime,hlo,hcap⟩ := allowed_prime_bounds hw hpath p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hup : primeExponent w p ≤ z.cutoff := by
    cases he : z.closed <;> simp only [capGuard,he,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hcap
    · exact hcap.le
    · exact hcap
  have hlow : w^ell < (p : ℝ) := (lt_exponent_iff hw hp0).mp hlo
  have hhigh : (p : ℝ) ≤ w^z.cutoff := (exponent_le_iff hw hp0).mp hup
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,hlow⟩
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hhigh

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem allowed_mono {w ell U V : ℝ} (hUV : U ≤ V) {z : Node} {ps : List ℕ}
    (hp : allowed w ell U z ps) : allowed w ell V z ps := by
  classical
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hp
    obtain ⟨hprime,hlo,hcap,hmin,hmax⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell V z p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hmax.trans hUV⟩,ih ht⟩

theorem uncapped_iff_exists_ceiling (w ell : ℝ) (z : Node) (ps : List ℕ) :
    uncappedAllowed w ell z ps ↔ ∃ U : ℝ, z.ratio ≤ U ∧ allowed w ell U z ps := by
  classical
  induction ps generalizing z with
  | nil => exact ⟨fun _ => ⟨z.ratio,le_rfl,trivial⟩,fun _ => trivial⟩
  | cons p ps ih =>
    constructor
    · rintro ⟨hc,ht⟩
      obtain ⟨U,hchildU,hrest⟩ := (ih (step w z p)).mp ht
      let V := max U z.ratio
      refine ⟨V,le_max_right _ _,?_⟩
      obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
      apply (allowed_cons w ell V z p ps).mpr
      refine ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,?_⟩,
        allowed_mono (le_max_left _ _) hrest⟩
      exact hchildU.trans (le_max_left _ _)
    · rintro ⟨U,_hstart,hpath⟩
      obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
      obtain ⟨hprime,hlo,hcap,hmin,hmax⟩ := Finset.mem_filter.mp hc
      refine ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin⟩,?_⟩
      exact (ih (step w z p)).mpr ⟨U,hmax,ht⟩

theorem uncapped_mem_decreasing {w ell : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell z ps) :
    ps ∈ decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff)) := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact allowed_mem_decreasing hw hU

theorem mem_uncappedPrefixes {w ell : ℝ} (hw : 1 < w) (z : Node) (ps : List ℕ) :
    ps ∈ uncappedPrefixes w ell z ↔ uncappedAllowed w ell z ps := by
  classical
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨uncapped_mem_decreasing hw h,h⟩⟩

end NumberTheoryLean.ActualPrimeHigh

end

section

open scoped BigOperators
namespace NumberTheoryLean.ActualPrimeHigh
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HighPrimeGeometry

noncomputable def uncappedLowGapHighMass (w ell : ℝ) (z : Node) (T K : ℝ) : ℝ := by
  classical
  exact ∑ ps ∈ (uncappedPrefixes w ell z).filter
    (fun ps => (terminal w z ps).gap ≤ K ∧ actualHasHigh w T z ps), prefixWeight ps

noncomputable def uncappedRewardedHighMass (w ell : ℝ) (z : Node) (T c : ℝ) : ℝ := by
  classical
  exact ∑ ps ∈ (uncappedPrefixes w ell z).filter (actualHasHigh w T z),
    prefixWeight ps * Real.exp (-c*(terminal w z ps).gap)

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open FinitePathGeometry PrimeHistories PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ActualPrimeHigh

noncomputable def retainedPrefixes (w ell S : ℝ) (start : Node) : Finset (List ℕ) := by
  classical
  exact (uncappedPrefixes w ell start).filter (allowed w ell S start)

theorem mem_retainedPrefixes {w ell S : ℝ} (hw : 1 < w) (start : Node) (ps : List ℕ) :
    ps ∈ retainedPrefixes w ell S start ↔ allowed w ell S start ps := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨(mem_uncappedPrefixes hw start ps).mpr ?_,h⟩
    apply (uncapped_iff_exists_ceiling w ell start ps).mpr
    exact ⟨max S start.ratio,le_max_right _ _,allowed_mono (le_max_left _ _) h⟩

noncomputable def retainedHistoryEquiv {w ell S : ℝ} (hw : 1 < w) (start : Node) :
    {ps // ps ∈ retainedPrefixes w ell S start} ≃ History w ell S start where
  toFun ps := ⟨ps.val,(mem_retainedPrefixes hw start ps.val).mp ps.property⟩
  invFun h := ⟨h.primes,(mem_retainedPrefixes hw start h.primes).mpr h.admissible⟩
  left_inv ps := by cases ps; rfl
  right_inv h := by cases h; rfl

noncomputable abbrev historyFintype {w ell S : ℝ} (hw : 1 < w) (start : Node) :
    Fintype (History w ell S start) :=
  Fintype.ofEquiv {ps // ps ∈ retainedPrefixes w ell S start} (retainedHistoryEquiv hw start)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

noncomputable def scaledWeight (w B : ℝ) {ell S : ℝ} (start : Node) : ChainState w ell S start → ℝ
  | none => 0
  | some h => B^2*(1+epsilon w)^h.primes.length*(h.node.gap/start.gap)^2*
      (weight start.side start.ratio/weight h.node.side h.node.ratio)

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

instance primeParent_isMarkov (w ell S : ℝ) (start : Node) [IsMarkovKernel (chain w ell S start)] :
    IsMarkovKernel (primeParent w ell S start) := by unfold primeParent; infer_instance

end NumberTheoryLean.ActualProcessCoupling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ConditionalPrimeBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeCompletedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain
open RetainedIntervalUpper

variable {w ell S : ℝ} {start : Node}

def closedLiveBin (a b : ℝ) : Set (ChainState w ell S start) :=
  fun z => match z with
    | none => False
    | some h => a ≤ h.node.ratio ∧ h.node.ratio ≤ b

end NumberTheoryLean.PrimeCompletedIntervalUpper



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
open PrimeCompletedIntervalUpper ContinuousIntervalUpper ActualCouplingSupport
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

def primeBadCells (mesh Ld Lc Ud Uc : ℝ) : Set (ChainState w ell S start) :=
  fun p => match p with
    | none => False
    | some h => ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh h.node.ratio)

end NumberTheoryLean.CoupledBoundaryEvents

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def sourceLaw (mesh : ℝ) (n : ℕ) : Measure (FlagState (JointState w ell S start)) :=
  law (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh) (mismatch_measurable mesh)
    (sourceJoint w ell S start hs) n

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformFailureBudget
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformFailureBudget

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant ActualCouplingUpdates
open ActualSupportIntervals PrimeBinMembership RegeneratingInverseBands

noncomputable def stepBudget (c₁ c₂ C₁ C₂ C₃ D w S mesh : ℝ) (N : ℕ) : ℝ :=
  2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
    epsilon w+(Real.exp (D*(1+S)^3*mesh)-1)+
    C₂*(1+S)^2*(upperDisplacement S mesh N+3*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
    C₃*(1+S)^2*(upperDisplacement S mesh N+3*mesh))

end NumberTheoryLean.UniformFailureBudget

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeMarginalRecursion
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

noncomputable def bin (m j : ℕ) : Set (ChainState w ell S start) :=
  ActualPrimeBins.liveBin (point m j) (point m (j+1))

noncomputable def mass (w ell S : ℝ) (start : Node) (m n j : ℕ) : ℝ≥0∞ :=
  pathLaw w ell S start n (bin m j)

end NumberTheoryLean.PrimeGridKernel

end

section


namespace NumberTheoryLean.PrimeMarginalRecursion

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel ExponentialMesh
open DerivativeWeights

def coveredParents {w ell S : ℝ} {start : Node} (m j : ℕ) (i : Side) (I : Finset ℕ) :
    ChainState w ell S start → Prop
  | none => True
  | some g => g.node.side = i ∧ (g.node.ratio < point m (j+m+2) →
      ∃ k ∈ I, some g ∈ bin m k ∧ Valid i (point m k))

end NumberTheoryLean.PrimeMarginalRecursion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceParentBin
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

noncomputable def index (m : ℕ) (start : Node) : ℕ := ⌊start.ratio*(m:ℝ)⌋₊

end NumberTheoryLean.SourceParentBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeInverseBins
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeInverseBins

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel DerivativeWeights MarginalProfiles

variable {w ell S : ℝ} {start : Node}

noncomputable def inverseWeight : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => ENNReal.ofReal (1/weight h.node.side h.node.ratio)

noncomputable def inverseBin (w ell S : ℝ) (start : Node) (m n j : ℕ) : ℝ≥0∞ :=
  ∫⁻ z in bin m j,inverseWeight z ∂pathLaw w ell S start n

end NumberTheoryLean.PrimeInverseBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrimeExponentialTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeExponentialTail

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins PrimeCompactWeights ExponentialMeshTail DerivativeWeights

variable {w ell S : ℝ} {start : Node}

noncomputable def tailReward (c K : ℝ) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => if K < h.node.gap then
      ENNReal.ofReal (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) else 0

end NumberTheoryLean.PrimeExponentialTail

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
open ActualProcessCoupling ActualFlagInvariant RegeneratingInverseBands

variable {w ell S : ℝ} {start : Node}

noncomputable def primeTest (F : Side → ℝ×ℝ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => F h.node.side (h.node.gap,h.node.ratio)

end NumberTheoryLean.CompactTestGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_AdmittedHighRemoval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHighRemoval

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures ArrivalKernelGeometry AdmittedHarmonicPaths
open RegeneratingInverseBands FlaggedHarmonicPaths

noncomputable def lowHighMass (v ell S : ℝ) (z : CostState) (K : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ((FlaggedHarmonicPaths.kernel v ell S)^n) (initial S z)
    {y : FlagState | y.2 = true ∧ gapValue v y.1 ≤ K}

end NumberTheoryLean.AdmittedHighRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CouplingData

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant KernelCouplingLift PersistentFailureFlag

noncomputable def joint (w ell S : ℝ) (start : Node) (v mesh : ℝ) :
    Kernel (JointState w ell S start) (JointState w ell S start) :=
  coupled (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead

noncomputable def sourceLaw (w ell S : ℝ) (start : Node) (hs : Valid start.side start.ratio)
    (mesh : ℝ) (n : ℕ) : Measure (FlagState (JointState w ell S start)) :=
  law (joint w ell S start (Real.log start.gap) mesh) (mismatch_measurable mesh)
    (FlaggedSourceStart.sourceJoint w ell S start hs) n

end NumberTheoryLean.CouplingData

end

section

namespace NumberTheoryLean.CompactCouplingError

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open CompactTestGeometry PrimeCompactVisits

variable {w ell S : ℝ} {start : Node}

noncomputable def difference (v : ℝ) (F : Side → ℝ×ℝ → ℝ)
    (q : FlagState (JointState w ell S start)) : ℝ≥0∞ :=
  ENNReal.ofReal |primeTest F q.1.1-continuousTest v F q.1.2|

end NumberTheoryLean.CompactCouplingError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectedCompactTransfer
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open CompactTestGeometry CompactCouplingError
open ActualProcessCoupling PersistentFailureFlag ContinuousKilledBins LowStateHorizon
open ExponentialMesh

noncomputable def primeExpectation (F : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ z,primeTest F z ∂pathLaw w ell S start n

end NumberTheoryLean.SignedCompactTransfer

end

section

namespace NumberTheoryLean.CompactNormalizationCorrection

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open CompactTestGeometry SignedCompactTransfer PrimeCorrectionFactor

variable {w ell S : ℝ} {start : Node}

noncomputable def correctedTest (F : Side → ℝ×ℝ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => (1+epsilon w)^h.primes.length*F h.node.side (h.node.gap,h.node.ratio)

noncomputable def correctedExpectation (F : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ z,correctedTest F z ∂pathLaw w ell S start n

end NumberTheoryLean.CompactNormalizationCorrection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GrowingFarTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ModerateFailedReward

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights ActualProcessCoupling
open FlaggedOccupationBound ActualFlaggedCompact PersistentFailureFlag
open DerivativeWeights ExponentialMeshTail InverseWeightGrowth

variable {w ell S : ℝ} {start : Node}

noncomputable def moderateReward (c K : ℝ) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => ENNReal.ofReal (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio)*
      ENNReal.ofReal (visit K (some h))

end NumberTheoryLean.ModerateFailedReward

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SuccessfulTailTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulTailTransport

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling PersistentFailureFlag ActualFlagInvariant
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousArrivalSupport ContinuousCompletedOccupation
open ContinuousKilledBins CostPrefixTransport

variable {w ell S : ℝ} {start : Node}

noncomputable def cleanReward (c K : ℝ) (q : FlagState (JointState w ell S start)) : ℝ≥0∞ :=
  if q.2 = false then PrimeExponentialTail.tailReward c K q.1.1 else 0

end NumberTheoryLean.SuccessfulTailTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_NonnegativeOriginalOccupation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCompactOccupation

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights PrimeCorrectionFactor
open FlaggedOccupationBound PersistentFailureFlag ActualProcessCoupling ActualFlaggedCompact

variable {w ell S B : ℝ} {start : Node}

noncomputable def compactReward (K w B : ℝ) {ell S : ℝ} (start : Node)
    (z : ChainState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (scaledWeight w B start z*visit K z)

end NumberTheoryLean.SourceCompactOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open PrimeCompactWeights SourceCompactOccupation
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

noncomputable def listReward (F : List ℕ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => F h.primes

end NumberTheoryLean.PrimeFamilyOccupation

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
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership DerivativeWeights
open PrimeCompactWeights PrimeCorrectionFactor PrimeExponentialTail LowStateHorizon

noncomputable def scaledTail (c K w B : ℝ) {ell S : ℝ} (start : Node) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => if K < h.node.gap then ENNReal.ofReal
      (scaledWeight w B start (some h)*Real.exp (-c*h.node.gap)) else 0

end NumberTheoryLean.ScaledOriginalTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceThresholdCoupling
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReconstructedParentCoupling
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RepresentativeStopGeometry ActualFlagInvariant
open TwoSidedThresholdArrival TwoSidedThresholdGeometry
open ArrivalKernelGeometry RegeneratingInverseBands ErdosEvenThreshold

def primeNearThreshold (d : ℝ) (z : Node) : Prop :=
  z.side=.even ∧ 1 < z.cutoff ∧ 0 ≤ z.gap-sourceHeight z.cutoff ∧ z.gap-sourceHeight z.cutoff ≤ d

end NumberTheoryLean.ReconstructedParentCoupling

end

section

namespace NumberTheoryLean.SourceThresholdCoupling
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport FiniteHistoryOccurrence ActualProcessCoupling ActualCoupledHistories
open ActualFlagInvariant PersistentFailureFlag
open ReconstructedParentCoupling CompletedArrivalOccurrence
open TwoSidedThresholdArrival TwoSidedThresholdKernel TwoSidedThresholdOccurrence
open CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

variable {w ell S : ℝ} {start : Node}

def nearPrimeNode (d : ℝ) : ChainState w ell S start → Prop
  | none => False
  | some h => primeNearThreshold d h.node

def primeThresholdOccurs (d : ℝ) (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) : Prop :=
  ∃ j : Fin N,nearPrimeNode d (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.1

end NumberTheoryLean.SourceThresholdCoupling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SuccessfulMarkedCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulMarkedCoordinates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualProcessCoupling ActualFlagInvariant ActualCoupledHistories
open FiniteHistoryTransport ArrivalKernelGeometry

def primeWindow (b₀ b₁ : ℝ) (z : Node) : Prop :=
  z.side = .even ∧ 208/100 ≤ z.ratio ∧ z.ratio ≤ 214/100 ∧
    2*b₀ ≤ z.cutoff ∧ z.cutoff ≤ b₁/2 ∧ 6*b₀ < z.gap

end NumberTheoryLean.SuccessfulMarkedCoordinates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_AdjacentPrimeRecovery
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryPrefixOrder

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualCouplingUpdates
open FiniteHistoryTransport ActualCoupledHistories

variable {w ell S : ℝ} {start : Node}

def prefixRel : ChainState w ell S start → ChainState w ell S start → Prop
  | _,none => True
  | none,some _ => False
  | some a,some b => ∃ tail : List ℕ,b.primes = a.primes++tail

def orderedPast (N : ℕ) (h : Hist (ChainState w ell S start) N) : Prop :=
  ∀ i j : Finset.Iic N, i.1 ≤ j.1 → prefixRel (h i) (h j)

end NumberTheoryLean.PrimeHistoryPrefixOrder

end

section

namespace NumberTheoryLean.PriorPrimeWindow

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport ActualCoupledHistories PrimeHistoryPrefixOrder
open ActualProcessCoupling SuccessfulMarkedCoordinates ArrivalKernelGeometry

def hasPrimeWindow (w b₀ b₁ : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ, ps = pre++tail ∧ primeWindow b₀ b₁ (terminal w start pre)

end NumberTheoryLean.PriorPrimeWindow

end

section

namespace NumberTheoryLean.PrimePrefixRecovery
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open FiniteHistoryTransport ActualCoupledHistories FlaggedSourceStart ActualProcessCoupling
open PriorPrimeWindow SourceThresholdCoupling ReconstructedParentCoupling

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

def hasNearThresholdPrefix (w d : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ≠ [] ∧ primeNearThreshold d (terminal w start pre)

end NumberTheoryLean.PrimePrefixRecovery

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FullPathCompactSelection
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullPathCompactSelection

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories
open PrimeCompactVisits PrimeCompactWeights SourceCompactOccupation

variable {w ell S B : ℝ} {start : Node}

noncomputable def fullCompactReward (R w B : ℝ) {ell S : ℝ} (start : Node) (N : ℕ)
    (h : Hist (FlagState (JointState w ell S start)) N) : ℝ≥0∞ :=
  ∑ j : Fin N, compactReward R w B start (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1

end NumberTheoryLean.FullPathCompactSelection

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_SourceSelectedCompactOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSelectedCompactOccupation

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullPathCompactSelection
open PrimeCompactWeights PrimeCorrectionFactor PrimeBinMembership

noncomputable def fullSourceLaw (w ell S : ℝ) (start : Node)
    (hs : Valid start.side start.ratio) (mesh : ℝ) (N : ℕ) :
    Measure (Hist (FlagState (JointState w ell S start)) N) :=
  pathKernel (marked (CouplingData.joint w ell S start (Real.log start.gap) mesh)
    (ActualFlagInvariant.mismatch_measurable mesh)) N
    (fun _ => (FlaggedSourceStart.sourceJoint w ell S start hs,false))

end NumberTheoryLean.SourceSelectedCompactOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_FullHistoryPrimeOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullHistoryPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open PrimeCompactWeights PrimeFamilyOccupation ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def fullListReward (w B : ℝ) {ell S : ℝ} (start : Node)
    (F : List ℕ → ℝ) (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) : ℝ≥0∞ :=
  ∑ j : Fin N, ENNReal.ofReal
    (scaledWeight w B start (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 *
      listReward F (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1)

end NumberTheoryLean.FullHistoryPrimeOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_NearPrefixOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactPrefixOccurrence

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open FullHistoryPrimeOccupation FullPathCompactSelection SourceCompactOccupation
open PrimeCompactWeights PrimeCompactVisits PrimeFamilyOccupation

attribute [local instance] Classical.propDecidable

variable {w ell S B R : ℝ} {start : Node}

def selectedNode (E : Set (List ℕ)) : ChainState w ell S start → Prop
  | none => False
  | some h => h.primes ∈ E

def occurs (E : Set (List ℕ)) (N : ℕ)
    (h : Hist (FlagState (JointState w ell S start)) N) : Prop :=
  ∃ j : Fin N, selectedNode E (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1

end NumberTheoryLean.CompactPrefixOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_LiteralUniformPrimeTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.LiteralPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeFamilyOccupation
open PrimeCompactWeights CompactInverseTest CompactNormalizationCorrection ScaledOriginalTail DerivativeWeights
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def nodeReward (H : Side → ℝ×ℝ → ℝ) (w : ℝ) (start : Node) (ps : List ℕ) : ℝ :=
  H (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio)

noncomputable def familyValue (H : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) : ℝ :=
  (start.gap^2/weight start.side start.ratio)*
    (∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*nodeReward H w start ps)

noncomputable def sourceFactor (B : ℝ) (start : Node) : ℝ :=
  B^2*weight start.side start.ratio/start.gap^2

noncomputable def tailListReward (c K w : ℝ) (start : Node) (ps : List ℕ) : ℝ :=
  if K < (terminal w start ps).gap then Real.exp (-c*(terminal w start ps).gap) else 0

end NumberTheoryLean.LiteralPrimeOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_LiteralCompactRemoval
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.LiteralCompactRemoval

open _root_.Set _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualPrimeHigh PrimeFamilyOccupation LiteralPrimeOccupation
open ContinuousCompactHighError SourceLowRemoval DerivativeWeights
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def uncappedFamilyValue (H : Side → ℝ×ℝ → ℝ) (w ell : ℝ) (start : Node) : ℝ :=
  (start.gap^2/weight start.side start.ratio)*
    (∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*nodeReward H w start ps)

end NumberTheoryLean.LiteralCompactRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_UncappedCompactMass
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UncappedCompactMass

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeCompactWeights
open ActualPrimeHigh LiteralCompactRemoval LiteralPrimeOccupation
open PositiveGapMajorant CompactLogOccupationTest NormalizedOccupationLimit
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def compactPrefixMass (K w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
    (if 2 ≤ (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ K then 1 else 0)

end NumberTheoryLean.UncappedCompactMass

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_UniformExponentialOccupation
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformExponentialOccupation

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open UncappedCompactMass LiteralPrimeOccupation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def exponentialPrefixMass (c w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*positiveGapEnvelope c (terminal w start ps).gap

end NumberTheoryLean.UniformExponentialOccupation

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

namespace NumberTheoryLean.UniformBoundaryCorrection

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open BoundaryAnomaly UniformExponentialOccupation ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def boundaryCorrection (w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*((-1:ℝ)^ps.length*
    anomaly w (terminal w start ps).side (terminal w start ps).gap)

end NumberTheoryLean.UniformBoundaryCorrection

end

section

namespace NumberTheoryLean.ReferenceSourceDecomposition

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence ReferenceForestTelescoping ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceLocalResidual
open BoundaryAnomaly UniformBoundaryCorrection
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def sourceReference (w : ℝ) (z : Node) : ℝ :=
  referencePolynomial w (sourcePrimes w z.cutoff z.closed) z.side z.gap

noncomputable def residualCorrection (w : ℝ) (z : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w 2 z,prefixWeight ps*((-1:ℝ)^ps.length*sourceResidual w (terminal w z ps))

end NumberTheoryLean.ReferenceSourceDecomposition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MovingLocalReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ReferenceResidualErrors

open _root_.Finset _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualBoundaryDomain
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def boundaryProductError (w : ℝ) (z : Node) : ℝ :=
  (referenceProduct w 2 true-normalization w/2)*(benchmark z.side (z.gap/2)-1)

noncomputable def parentProductError (w : ℝ) (z : Node) : ℝ :=
  (referenceProduct w z.cutoff z.closed-normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)

noncomputable def primeProductError (w : ℝ) (z : Node) : ℝ :=
  ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
    (referenceProduct w (primeExponent w p) false-normalization w/primeExponent w p)*
    (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def quadratureError (w : ℝ) (z : Node) : ℝ :=
  (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
    (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p)-
  ∫ x in highInterval z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2

end NumberTheoryLean.ReferenceResidualErrors



namespace NumberTheoryLean.ReferenceResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open ReferenceSourceDecomposition ReferenceProductErrorBounds
open ReferenceLocalResidual TwoStepDensityBounds
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def residualAbsoluteSum (w : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w 2 start,prefixWeight ps*|sourceResidual w (terminal w start ps)|

end NumberTheoryLean.ReferenceResidualSum



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_StrongReferenceTransport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StrongReferenceTransport
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure
attribute [local instance] Classical.propDecidable

def StrongState (z : Node) : Prop := 2 ≤ z.gap ∧ (z.side=.even → z.cutoff+2 ≤ z.gap)

end NumberTheoryLean.StrongReferenceTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalKeyWitness
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ActualStopGroupFiber
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag CanonicalStopKey
open StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open FrozenPrimeGroup ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

noncomputable def family (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) : Finset (List ℕ) :=
  stopped w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z) (sourcePrimeSet w top).card
    (rootVertex z ∅ (sourcePrimeSet w top) mu)

end NumberTheoryLean.ActualStopGroupFiber



namespace NumberTheoryLean.CanonicalStopPartition
open PrimeHistories CanonicalStopKey ActualStopGroupFiber

attribute [local instance] Classical.propDecidable

noncomputable def keys (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) :
    Finset (Key (LogarithmicBinScale.binCount w top xi)) :=
  (family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).biUnion
    (fun ps => (key Y w top Cs eta xi hw htop hxi a ps).toFinset)

end NumberTheoryLean.CanonicalStopPartition



namespace NumberTheoryLean.CanonicalKeyWitness
open PrimeHistories CanonicalStopKey CanonicalStopPartition ActualStopGroupFiber
open SourceStopPredicate ActualSourceTags ActualBinOwners
open StoppedCountAdapters StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

structure Witness {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ mu : ℝ) (a : ℕ → ℕ) (z : Node)
    (k : Key (binCount w top xi)) where
  p₀ : ℕ
  mem_family : k.pre++p₀::k.tail∈family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z
  candidate : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z (k.pre++p₀::k.tail)
  tag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) (k.pre++p₀::k.tail)=some k.tag
  prime_tag : tagCandidate Y w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) p₀=some (k.tag.bin,k.tag.rational)
  index : k.tag.index=k.pre.length
  ordered : (k.pre++p₀::k.tail).Pairwise (· > ·)
  source : ∀ p∈k.pre++p₀::k.tail,p∈sourcePrimeSet w top
  singleton : ((k.pre++p₀::k.tail).map (label (zero_lt_one.trans hw) htop hxi)).count k.tag.bin=1
  eligible : ActualBinOwners.eligible Y w Cs k.tag.rational
  near_full : (1-eta)*((primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).card:ℝ) ≤
    (((primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).filter (aligns (sourceClass a) k.tag.rational)).card:ℝ)
  aligned : ∀ p∈k.pre++p₀::k.tail,aligns (sourceClass a) k.tag.rational p
  prime_bin : p₀∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
  bin_eq : k.tag.bin=label (zero_lt_one.trans hw) htop hxi p₀
  search : searchBin w (lower w top xi k.tag.bin)
  owner : ActualBinOwners.owner Y w Cs eta (lower w top xi k.tag.bin) (width w top xi k.tag.bin) (sourceClass a)=some k.tag.rational
  tail_nonempty : k.tail≠[]

end NumberTheoryLean.CanonicalKeyWitness


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
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals ReferenceResidualErrors
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def rebase (z : Node) (a : ℝ) : Node :=
  {z with ratio := z.gap/a,cutoff := a,closed := true}

noncomputable def intervalResidual (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  referenceProduct w a true*(parentBenchmark z.side (z.gap/a)-1)-
    referenceProduct w z.cutoff z.closed*(parentBenchmark z.side z.ratio-1)-
    ∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1)

end NumberTheoryLean.ReferenceIntervalCutoff

end

section

namespace NumberTheoryLean.ReferenceIntervalErrors

open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceMertens ReferenceResidualErrors ReferenceIntervalCutoff
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def lowerProductError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  (referenceProduct w a true-normalization w/a)*(parentBenchmark z.side (z.gap/a)-1)

noncomputable def intervalPrimeError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  ∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
    (referenceProduct w (primeExponent w p) false-normalization w/primeExponent w p)*
    (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def intervalQuadratureError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
    (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p)-
  ∫ x in primeInterval a z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2

end NumberTheoryLean.ReferenceIntervalErrors

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceReferenceRemainders
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.HighResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh ActualBoundaryDomain
open ReferenceSourceDecomposition ReferenceResidualSum ReferenceLocalResidual ReferenceProductErrorBounds
open GlobalResidualScale
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def highResidualAbsoluteSum (w B : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ (uncappedPrefixes w 2 start).filter (actualHasHigh w ((Real.log B)^2) start),
    prefixWeight ps*|sourceResidual w (terminal w start ps)|

end NumberTheoryLean.HighResidualSum



namespace NumberTheoryLean.SharpRetainedResidual

attribute [local instance] Classical.propDecidable
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeKilledChain PrimeCorrectionFactor PrimeFamilyOccupation
open LowStateHorizon ActualPrimeHigh
open ReferenceLocalResidual ReferenceProductErrorBounds
open ErdosPrimeInputs.PrimePrefixMass ErdosRetainedRewardTransfer

noncomputable def retainedResidualAbsoluteSum (w B : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ retainedPrefixes w 2 ((Real.log B)^2) start,prefixWeight ps*|sourceResidual w (terminal w start ps)|

end NumberTheoryLean.SharpRetainedResidual



open _root_.Set _root_.Filter
open scoped Topology


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualSafeBoxMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SafeSubsetBoxGeometry
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ReferenceAdmission ErdosCofactorChoices ErdosSubsetWord
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

noncomputable def SafeAnchor {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) (mult : Fin (binCount w top xi) → ℕ) : Prop :=
  ∃ anchor ∈ selections (globalBins w top xi) mult,
    ((descendingWord anchor).length:ℝ) ≤ Clen*Real.log B ∧
    representativeSafe w (representative w (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi)) z (2*Clen*xi) (descendingWord anchor) ∧
    (terminal w z (descendingWord anchor)).gap ≤ K

end NumberTheoryLean.SafeSubsetBoxGeometry



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
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag ActualCouplingUpdates
open CompletedParentInterval ContinuousIntervalUpper
open ContinuousKilledBins
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


variable {w ell S : ℝ} {start : Node}

def nextRepeat {n : ℕ} (lab : ℕ → Fin n) (X : ℝ) (h : History w ell S start)
    (y : FlagState (JointState w ell S start)) : Prop :=
  match y.1.1 with
  | none => False
  | some k => lab (h.primes.getLastD 0)=lab (k.primes.getLastD 0) ∧ X ≤ k.node.cutoff

noncomputable def goodRepeatNext {n : ℕ} (lab : ℕ → Fin n) (X v mesh : ℝ) (N : ℕ)
    (h : History w ell S start) : Set (FlagState (JointState w ell S start)) :=
  {y | GoodAt v mesh N y.1 ∧ nextRepeat lab X h y}

end NumberTheoryLean.RepeatedStepRowBound


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RepeatedPairEvents
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairEvents
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound

variable {w ell S : ℝ} {start : Node}

def primeRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start)) :
    ChainState w ell S start × ChainState w ell S start → Prop
  | (some h,some k) => h.primes ≠ [] ∧ h.node.ratio ≤ U ∧ some h ∈ G ∧
      lab (h.primes.getLastD 0)=lab (k.primes.getLastD 0) ∧ X ≤ k.node.cutoff
  | _ => False

noncomputable def goodRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    (v mesh : ℝ) (N : ℕ) : Set (FlagState (JointState w ell S start) × FlagState (JointState w ell S start)) :=
  {xy | GoodAt v mesh N xy.1.1 ∧ GoodAt v mesh N xy.2.1 ∧ primeRepeatPair lab X U G (xy.1.1.1,xy.2.1.1)}

end NumberTheoryLean.RepeatedPairEvents


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RepeatedPairProbability
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairProbability
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound RepeatedPairEvents
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open PrimeCompactVisits
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

attribute [local instance] Classical.propDecidable
variable {w ell S : ℝ} {start : Node}

noncomputable def rawRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start)) :
    Set (FlagState (JointState w ell S start) × FlagState (JointState w ell S start)) :=
  {xy | primeRepeatPair lab X U G (xy.1.1.1,xy.2.1.1)}

noncomputable def compactParentGate (L : ℝ) : Set (ChainState w ell S start) :=
  {p | match p with | none => False | some h => h.node.gap ≤ L}

end NumberTheoryLean.RepeatedPairProbability


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RegularityDefectPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualRegularBoxes
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualPrefixClearance ActualWordSelection
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SafeSubsetBoxGeometry ErdosSubsetWord ErdosCofactorChoices ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

noncomputable def regularBoxes {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) : Finset (Fin (binCount w top xi) → ℕ) :=
  (regularWords hw htop hxi Clen B K z).image
    (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi))

end NumberTheoryLean.ActualRegularBoxes



namespace NumberTheoryLean.RegularityDefectPartition
open FinitePathGeometry PrimeHistories ActualRegularBoxes ActualPrefixClearance RepeatedWordEvents
open ReferenceAdmission LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
attribute [local instance] Classical.propDecidable

noncomputable def clearanceFailure (w Delta : ℝ) (z : Node) (ps : List ℕ) : Prop := ¬actualClearance w z Delta ps

end NumberTheoryLean.RegularityDefectPartition


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
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricBoxImages
open PrimeHistories ActualWordSelection ActualRegularBoxes GeometricRegularWords
open SafeSubsetBoxGeometry ErdosSubsetWord LogarithmicBinScale LogarithmicBinLabels
attribute [local instance] Classical.propDecidable

noncomputable def geometricBoxes {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (C B R L alpha beta : ℝ) (z : Node) : Finset (Fin (binCount w top xi) → ℕ) :=
  (geometricWords hw htop hxi C B R L alpha beta z).image
    (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi))

end NumberTheoryLean.GeometricBoxImages



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
open scoped _root_.Erdos970



namespace NumberTheoryLean.CountErrorClassification
open PrimeHistories ActualCountErrorEdges ErdosInverseCounts

attribute [local instance] Classical.propDecidable

noncomputable def largeGapWords (w K : ℝ) (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => K<(terminal w z ps).gap)
noncomputable def smallErrorWords (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => (terminal w z ps).gap ≤ K ∧ |wordCountError Y small a V0 ps| ≤ eps)
noncomputable def badCompactWords (w K eps : ℝ) (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (V0 : ℝ)
    (z : Node) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.filter (fun ps => (terminal w z ps).gap ≤ K ∧ eps < |wordCountError Y small a V0 ps|)

end NumberTheoryLean.CountErrorClassification



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PaperMissingPrimeWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MissingWindowPrimeMass

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh PriorPrimeWindow
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def missingWindowPrefixes (w ell R b₀ b₁ : ℝ) (start : Node) : Finset (List ℕ) := by
  classical
  exact (uncappedPrefixes w ell start).filter fun ps =>
    (terminal w start ps).gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start ps

end NumberTheoryLean.MissingWindowPrimeMass

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



namespace NumberTheoryLean.RegularBadTagWords
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord ErdosCofactorChoices HardTagWordFamily HardTagBoxMass ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def regularBadWords {Y w top xi Cs eta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Clen B K : ℝ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (a : ℕ → ℤ) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B K z).filter (badWordTest (Y := Y) (Cs := Cs) (eta := eta) hw htop hxi Q a)

end NumberTheoryLean.RegularBadTagWords



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RegularStoppedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RegularStoppedEvent
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate ActualWordSelection ActualRegularBoxes
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualPrefixClearance RegularBadTagWords
open StoppedTraceSets StoppedCountAdapters PriorPrimeWindow MissingWindowPrimeMass
open StrongReferenceTransport ActualPrimeHigh ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def hasSourceStop {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node) (ps : List ℕ) : Prop :=
  ∃ pre tail : List ℕ,ps=pre++tail ∧ pre ∈ stopped w
    (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a z)
    (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) 1)

noncomputable def uncapturedTest {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) (ps : List ℕ) : Prop :=
    (∃ q ∈ Q (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps),
      ∀ p ∈ ps,Cs < primeExponent w p → aligns (sourceClass a) q p) ∧
    ¬hasSourceStop hw htop hxi Y Cs eta Clen B b₀ b₁ a z ps

noncomputable def uncapturedRegular {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B K b₀ b₁ : ℝ) (a : ℕ → ℕ) (z : Node)
    (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B K z).filter (uncapturedTest hw htop hxi Y Cs eta Clen B b₀ b₁ a z Q)

end NumberTheoryLean.RegularStoppedEvent


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
open scoped _root_.Erdos970



namespace NumberTheoryLean.ExpandedCompactPartition
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualRegularBoxes ActualWordSelection
open StoppedCountAdapters StoppedTraceSets RegularStoppedEvent
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open GeometricRegularWords CountErrorClassification
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def unlistedGeometric {w top xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (Cs C B K L alpha beta : ℝ)
    (a : ℕ → ℕ) (z : Node) (Q : (Fin (binCount w top xi) → ℕ) → Finset ℚ)
    (F : Finset (List ℕ)) : Finset (List ℕ) :=
  (F∩geometricWords hw htop hxi C B K L alpha beta z).filter (fun ps => ¬listedWord hw htop hxi Cs a Q ps)

end NumberTheoryLean.ExpandedCompactPartition



end Erdos970

end OAI
end



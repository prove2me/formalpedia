-- Prove2me | Definitions.Def_OAIQ247J008
-- name    : OAIQ247J008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:57:06.811249+00:00
-- url     : https://prove2.me/theorems/bf1a55d7-2c73-4766-82e6-daa8b001b2d0
-- title:
--   Definitions bundle OAIQ247J008 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 242 declarations of OpenAI's Lean: 120 definitions, 15 instances and 107 theorems. The definitions and types are `Erdos970.deltaz`, `Erdos970.deltaz_t`, `Erdos970.zerofree_constant`, `OAI.Erdos970.Erdos970Dependency.CycleMeanCost.blockIncrement`, `OAI.Erdos970.Erdos970Dependency.CycleMeanCost.capturedAge`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.RegCost`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.actualSpacingLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.actualSpacingTerm`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.actualWaitingLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.actualWaitingTerm`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningBelow`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningCost`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningDomainKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningOver`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningOvershoot`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindowHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.branchCostLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockAtOrAbove`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockBelow`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockOver`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockOverReward`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockOvershoot`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockTailPiece`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockWindow`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.clockWindowHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.costCurrentHit`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.costMarkedLoop`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstMarkWaitingLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.geometricMarkedCostLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialBeginningReg`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedBeginning`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedCostLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedWindowFailure`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedWindowSuccess`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.jointMarkCostLaw`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.markInputWeightKernel` and 80 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Erdos970_ZetaZeroFree`, `Jacobsthal_Analysis_CompactCorrectionLimit`, `Jacobsthal_Analysis_PaperContinuousCorrection`, `Jacobsthal_Estimates_ActualOddPairLink`, `Jacobsthal_Estimates_CanonicalCoupledHistories`, `Jacobsthal_Estimates_PairedBlockContraction`, `Jacobsthal_Estimates_SourceCenteredGap`, `Jacobsthal_Harmonic_CompactAnomalyTest`, `Jacobsthal_Partitions_BeginningWindowTransport`, `Jacobsthal_Partitions_RegularityDefectPartition`, `Jacobsthal_Partitions_SourceRawBoxFactory`, `Jacobsthal_Paths_ActualFlaggedCompact`, `Jacobsthal_Paths_ActualPrefixClearance`, `Jacobsthal_Paths_FlaggedHarmonicPaths`, `Jacobsthal_Paths_FlaggedSourceStart`, `Jacobsthal_Paths_GeometricRegularWords`, `Jacobsthal_Paths_PairedHitting`, `Jacobsthal_Primes_HighPrimeRemoval`, `Jacobsthal_Primes_PrimeCompactWeights`, `Jacobsthal_Primes_PrimeGridGeometry`, `Jacobsthal_Probability_ActualCouplingUpdates`, `Jacobsthal_Probability_GeometricCostLaws`, `Jacobsthal_Probability_MarkedBeginningKernel`, `Jacobsthal_Probability_MarkedCostHitReduction`, `Jacobsthal_Probability_MarkedCostSublaws`, `Jacobsthal_Probability_MarkedReturnKernel`, `Jacobsthal_Probability_MarkedVisitGeometry`, `Jacobsthal_Probability_MovingMarkedWindow`, `Jacobsthal_Probability_OrdinaryMarkedWindow`, `Jacobsthal_Probability_PairedDrift`, `Jacobsthal_Probability_RepeatedWordEvents`, `Jacobsthal_Renewal_ClockTailReward`, `Jacobsthal_Renewal_ClockWindowPassage`, `Jacobsthal_Renewal_MarkedCycleCompletion`, `Jacobsthal_Renewal_MarkedCycleWords`, `Jacobsthal_Renewal_OccupationAge`, `Jacobsthal_Renewal_OddPairCycleGrouping`, `Jacobsthal_Renewal_RegenerationBandBounds`, `Jacobsthal_Renewal_RegenerationInputPotential`, `Jacobsthal_Renewal_RegenerativeOddOccupation`, `Jacobsthal_Sieve_MarkedCycleFactorization`.
--
--   **Imports.** It imports the bundles `OAIQ247J006` and `OAIQ247J007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ247J010`, `OAIQ247J011` and `OAIQ247J012`; the statements `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential_jb247`, `OAI_Erdos970_Erdos970Dependency_MarkedVisits_clock_renewal_reward_tail_bound_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247` and `OAI.Erdos970.NumberTheoryLean.SourceRootErrorLower.source_root_lower_with_stopped_correction_jb247`; the proofs of `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247`, `OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247`, `OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247`, `OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_loss_le_scalarTailMass_jb247`, `OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_hypothetical_subbin_lower_jb247`, `OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247`, `OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247`, `OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247`, `OAI.Erdos970.ErdosVarianceSmallModel.source_residue_fibre_bound_jb247`, `OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.IteratedLogBound.of_source_root_lower_jb247`, `OAI_Erdos970_WeightedTorusJets_Geometry_DegreeBezout_coefficient_localization_weighted_length_le_pow_jb247`, `OAI_Erdos970_WeightedTorusJets_Geometry_uniform_rectangular_multiplicity_jb247`, `OAI_Erdos970_WeightedTorusJets_real_zero_le_conductorCompletedL_logDeriv_jb247` and `OAI_Erdos970_WeightedTorusJets_source_real_zero_uniform_master_bound_jb247`.
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
import Definitions.Def_OAIQ247J006
import Definitions.Def_OAIQ247J007

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

open Metric _root_.Set _root_.Filter _root_.Asymptotics BigOperators

lemma Zeta1_Zeta_Expand :
    ∃ A > 1, ∃ b > 1,
    ∀ (t : ℝ) (_ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (_hr1_pos : 0 < r1) (_hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (_hr_lt_R1 : r < R1) (_hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
                                                           
  obtain ⟨b, hbgt1, hb⟩ := zeta32upper
  obtain ⟨A, hAgt1, hA⟩ := zeta32lower_log

  refine ⟨A, hAgt1, b, hbgt1, ?_⟩
  intro t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 c hfin z hz

  have hexp_lemma := log_Deriv_Expansion_Zeta t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1

  have htpos : (0 : ℝ) < |t| := by linarith [ht]
  have hBgt1 : b * |t| > 1 := by
    have hb_pos : (0 : ℝ) < b := by linarith [hbgt1]
    calc (1 : ℝ) < 1 * 2 := by norm_num
    _ < b * 2 := mul_lt_mul_of_pos_right (by linarith [hbgt1]) (by norm_num)
    _ < b * |t| := mul_lt_mul_of_pos_left ht hb_pos

  have hbound_ball : ∀ s ∈ closedBall (3/2 + I * t) R, ‖riemannZeta s‖ < b * |t| := by
    have hsubset : closedBall (3/2 + I * t) R ⊆ closedBall (3/2 + I * t) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1)
    intro s hs
    have hs1 : s ∈ closedBall (3/2 + I * t) 1 := hsubset hs
    have ht2 : |t| > 2 := by linarith [ht]
    specialize hb t ht2
    exact hb s hs1

  have hexp := hexp_lemma (b * |t|) hBgt1 hbound_ball hfin z hz

  have hζne : riemannZeta (3/2 + I * t) ≠ 0 := zetacnot0 t
  have hζpos : (0 : ℝ) < ‖riemannZeta (3/2 + I * t)‖ := norm_pos_iff.mpr hζne

  have hBpos : (0 : ℝ) < b * |t| := mul_pos (by linarith [hbgt1]) htpos
  have hBne : b * |t| ≠ 0 := ne_of_gt hBpos
  have htne : |t| ≠ 0 := ne_of_gt htpos
  have hbne : b ≠ 0 := ne_of_gt (by linarith [hbgt1])

  have hlog_bound : Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) ≤
                    Real.log |t| + Real.log b + A := by
    rw [Real.log_div hBne (ne_of_gt hζpos)]
    rw [Real.log_mul hbne htne]
                                  
    have hA_bound := hA t
    have : -Real.log ‖riemannZeta (3/2 + I * t)‖ ≤ A := by
      have eq_neg : Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) = -Real.log ‖riemannZeta (3/2 + I * t)‖ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hζpos)]
        simp
      rw [← eq_neg]
      exact hA_bound
    linarith

  have hcoeff_nonneg : (0 : ℝ) ≤ 16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) := by
    apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · apply sq_nonneg
      · apply le_of_lt
        apply pow_pos
        linarith [hr1_lt_r]
    · apply div_nonneg
      · norm_num
      · apply le_of_lt
        apply mul_pos
        ·                          
          have h_gt : R > R1 := hR1_lt_R
          have h1_pos : (1 : ℝ) < R/R1 := by
            rw [one_lt_div]
            · exact h_gt
            · exact hR1_pos
          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field_simp [ne_of_gt hR1_pos]
          rw [h_sq_div]
          have h_r_pos : (0 : ℝ) < R := by linarith [hR1_pos, h_gt]
          have : R * (R/R1) > R * 1 := by
            apply mul_lt_mul_of_pos_left h1_pos h_r_pos
          simp at this
          linarith [this]
        · apply Real.log_pos
          rw [one_lt_div]
          · exact hR1_lt_R
          · exact hR1_pos

  calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
      ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) := hexp
    _ ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
      exact mul_le_mul_of_nonneg_left hlog_bound hcoeff_nonneg

lemma Zeta1_Zeta_Expansion
    (r1 r : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < 5 / (6 : ℝ)) :
    ∃ C > 1,
    ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc (5 / (6 : ℝ)) c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      C * (1 / (r - r1)^3 + 1) * Real.log |t| := by
                                                             
  obtain ⟨A, hAgt1, b, hbgt1, hmain⟩ := Zeta1_Zeta_Expand
                      
  let R1 : ℝ := 5 / 6
  let R  : ℝ := 8 / 9
  have hR1_pos : 0 < R1 := by norm_num [R1]
  have hR1_lt_R : R1 < R := by norm_num [R1, R]
  have hR_lt_1  : R < 1 := by norm_num [R]
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                    
  let d : ℝ := (r - r1) ^ 3
  have hd_pos : 0 < d := by
    have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
    simpa [d] using pow_pos this 3
  let A0 : ℝ := 1 / ((R^2 / R1 - R1) * Real.log (R / R1))
  have hA0_pos : 0 < A0 := by
    have hx1 : 0 < R^2 / R1 - R1 := by
                                              
      norm_num [R, R1]
    have hx2 : 0 < Real.log (R / R1) := by
                         
      have : (1 : ℝ) < R / R1 := by norm_num [R, R1]
      exact Real.log_pos this
    have hxden : 0 < (R^2 / R1 - R1) * Real.log (R / R1) := mul_pos hx1 hx2
    simpa [A0] using (one_div_pos.mpr hxden)
                                                               
  let K : ℝ := 16 * r^2 / d + A0
                              
  let S : ℝ := Real.log b + A
  have hS_pos : 0 < S := by
    have hbpos : 0 < Real.log b := Real.log_pos hbgt1
    have hApos : 0 < A := lt_trans (by norm_num) hAgt1
    exact add_pos hbpos hApos
                                                                                          
  let Kcoeff : ℝ := max (16 * r^2) A0
  have hK_le : K ≤ Kcoeff * (1 / d + 1) := by
    have hx_nonneg : 0 ≤ 1 / d := by
      exact le_of_lt (one_div_pos.mpr hd_pos)
    have hα_le : 16 * r^2 / d ≤ Kcoeff * (1 / d) := by
        have hα : 16 * r^2 ≤ Kcoeff := le_max_left _ _
        have : (16 * r^2) * (1 / d) ≤ Kcoeff * (1 / d) :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hβ_le : A0 ≤ Kcoeff * 1 := by
      have hβ : A0 ≤ Kcoeff := le_max_right _ _
      simpa using hβ
    have : 16 * r^2 / d + A0 ≤ Kcoeff * (1 / d) + Kcoeff * 1 :=
      add_le_add hα_le hβ_le
    simpa [K, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using this
                                                  
  let C : ℝ := max (Kcoeff * (1 + S / Real.log 3)) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                                                          
  intro t ht
                                         
  simp only
  intro hfin z hz
                                                
  have ht2 : |t| > 2 := by linarith [ht]
  have hineq0 :=
    hmain t ht2 r1 r R1 R hr1_pos hr1_lt_r (lt_trans hr1_pos hr1_lt_r) hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
  have hineq1 := hineq0 hfin z hz
                                 
  have hK_eq : (16 * r^2 / (r - r1)^3 + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) = K := by
    simp [K, A0, d, R1, R]
  have hLS_eq : Real.log |t| + Real.log b + A = Real.log |t| + S := by
    simp [S, add_comm, add_assoc]
  have hineq2 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * (Real.log |t| + S) := by
    rw [← hK_eq, ← hLS_eq]
    exact hineq1
                                                             
  have hlog3pos : 0 < Real.log (3 : ℝ) := by
    have : (1 : ℝ) < 3 := by norm_num
    exact Real.log_pos this
                                           
  have hpos_t : 0 < |t| := lt_trans (by norm_num) ht
  have hL_ge_log3' : Real.log 3 ≤ Real.log |t| := by
    have hge : (3 : ℝ) ≤ |t| := le_of_lt ht
    exact Real.log_le_log (by norm_num) hge
  have hratio_nonneg : 0 ≤ S / Real.log 3 := le_of_lt (div_pos hS_pos hlog3pos)
  have hneq : Real.log 3 ≠ 0 := ne_of_gt hlog3pos

  have hS_le : S ≤ (S / Real.log 3) * Real.log |t| := by

    calc S
      = (S / Real.log 3) * Real.log 3 := by simp [hneq]
      _ ≤ (S / Real.log 3) * Real.log |t| := mul_le_mul_of_nonneg_left hL_ge_log3' hratio_nonneg

  have hsum_bound : Real.log |t| + S ≤ (1 + S / Real.log 3) * Real.log |t| := by
    have hstep : Real.log |t| + S ≤ Real.log |t| + (S / Real.log 3) * Real.log |t| :=
      add_le_add_right hS_le (Real.log |t|)
                                                                                           
    have h_factor : Real.log |t| + (S / Real.log 3) * Real.log |t| = (1 + S / Real.log 3) * Real.log |t| := by ring
    rw [← h_factor]
    exact hstep
                                      
  have hineq3 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * ((1 + S / Real.log 3) * Real.log |t|) :=
    le_trans hineq2 (mul_le_mul_of_nonneg_left hsum_bound (by
      have hr2_nonneg : 0 ≤ r^2 := by
        have : 0 ≤ r * r := mul_nonneg (le_of_lt hr_pos) (le_of_lt hr_pos)
        simpa [pow_two] using this
      have hterm1 : 0 ≤ 16 * r^2 / d :=
        div_nonneg (mul_nonneg (by norm_num) hr2_nonneg) (le_of_lt hd_pos)
      have : 0 ≤ K := add_nonneg hterm1 (le_of_lt hA0_pos)
      exact this))
                                    
  have hKcoeff : K * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|) :=
    mul_le_mul_of_nonneg_right hK_le (by
      have hLpos : 0 < Real.log |t| :=
        Real.log_pos (lt_trans (by norm_num) ht)
      have hcoef_pos : 0 < 1 + S / Real.log 3 :=
        add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos hS_pos hlog3pos))
      have : 0 ≤ (1 + S / Real.log 3) * Real.log |t| :=
        le_of_lt (mul_pos hcoef_pos hLpos)
      simpa using this)
                                                                     
  have hfinal := le_trans hineq3 hKcoeff
                                                    
  have hC_ge : Kcoeff * (1 + S / Real.log 3) ≤ C := by
    exact le_max_left _ _
                                           
  have : (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ C * (1 / d + 1) * Real.log |t| := by
    have hnonneg_term : 0 ≤ (1 / d + 1) * Real.log |t| := by
      have h1 : 0 ≤ 1 / d := le_of_lt (one_div_pos.mpr hd_pos)
      have h2 : 0 ≤ Real.log |t| := le_of_lt (Real.log_pos (lt_trans (by norm_num) ht))
      have : 0 ≤ (1 / d + 1) := add_nonneg h1 (by norm_num)
      exact mul_nonneg this h2
    have hstep := mul_le_mul_of_nonneg_left hC_ge hnonneg_term
                                         
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
                                                    
  have hfinal_le := le_trans hfinal this
  simp only [d] at hfinal_le
  exact hfinal_le

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


lemma lem_explicit1deltat :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                  (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))
                - logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)‖
          ≤ C * Real.log (abs t + 2) := by
  classical
                               
  let r1 : ℝ := (1/2 : ℝ)
  let r  : ℝ := (2/3 : ℝ)
  let R1 : ℝ := (5/6 : ℝ)
  let R  : ℝ := (9/10 : ℝ)
  have hr1_pos : 0 < r1 := by norm_num
  have hr_pos  : 0 < r := by norm_num
  have hr1_lt_r : r1 < r := by norm_num
  have hr_lt_R1 : r < R1 := by norm_num
  have hR1_pos : 0 < R1 := by norm_num
  have hR1_lt_R : R1 < R := by norm_num
  have hR_lt_1  : R < 1 := by norm_num
                     
  let F : ℝ := (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)))
                       
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨A, hA_gt1, hA_bound⟩ := zeta32lower_log
                                                      
  let K : ℝ := 1 + (Real.log b + A) / Real.log 4
                   
  let C : ℝ := max (F * K) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                             
  intro t ht δ hδ
  rcases hδ with ⟨hδ_pos, hδ_lt1⟩
                                 
  let c_std : ℂ := ((3/2 : ℂ) + Complex.I * (t : ℂ))
  let c_comm : ℂ := ((3/2 : ℂ) + (t : ℝ) * Complex.I)
  have hcenter_eq : c_std = c_comm := by simpa [c_std, c_comm] using (center_eq_comm t)
  let s : ℂ := (1 : ℂ) + δ + t * Complex.I
                            
  have hs_mem_comm : s ∈ Metric.closedBall c_comm r1 := s_in_closedBall_12 δ t hδ_pos hδ_lt1
  have hs_mem_std : s ∈ Metric.closedBall c_std r1 := by simpa [c_std, c_comm, hcenter_eq] using hs_mem_comm
                 
  have hs_notin_Zt : s ∉ ZetaZerosNearPoint t := s_notin_ZetaZerosNearPoint δ t hδ_pos
  have hzeros_eq : zerosetKfRc (5/6 : ℝ) c_comm riemannZeta = ZetaZerosNearPoint t := by
    simpa [c_comm] using zerosetKfRc_eq_ZetaZerosNearPoint t
  have hs_notin_comm : s ∉ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using hs_notin_Zt
  have hs_notin_std : s ∉ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [c_std, c_comm, hcenter_eq] using hs_notin_comm
                    
  have hfin_comm : (zerosetKfRc (5/6 : ℝ) c_comm riemannZeta).Finite := by
    simpa [hzeros_eq] using (ZetaZerosNearPoint_finite t)
  have hfin_std : (zerosetKfRc (5/6 : ℝ) c_std riemannZeta).Finite := by
    simpa [c_std, c_comm, hcenter_eq] using hfin_comm
                                                         
  have h_bound_R : ∀ z ∈ Metric.closedBall c_std R, ‖riemannZeta z‖ < b * |t| := by
    intro z hz
    have hsubs : Metric.closedBall c_std R ⊆ Metric.closedBall c_std (1 : ℝ) := by
      intro w hw; exact Metric.closedBall_subset_closedBall (by norm_num : (R : ℝ) ≤ (1 : ℝ)) hw
    exact hb_bound t (by simpa using ht) z (hsubs hz)
                                  
  have hmain :=
    log_Deriv_Expansion_Zeta t ht
      r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
                    
  have hbpos : 0 < b := lt_trans (by norm_num) hb_gt1
  have ht1 : 1 < |t| := lt_trans (by norm_num) ht
  have hmul : b * 1 < b * |t| := (mul_lt_mul_of_pos_left ht1 hbpos)
  have hB_gt1 : 1 < b * |t| := lt_trans hb_gt1 (by simpa using hmul)
  have hineq := hmain (b * |t|) hB_gt1 h_bound_R
  have hz_in : s ∈ Metric.closedBall c_std r1 \ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := ⟨hs_mem_std, hs_notin_std⟩
  have hineq2 := hineq hfin_std s hz_in
                                                           
  have hFinset_eq : hfin_std.toFinset = (ZetaZerosNearPoint_finite t).toFinset := by
    ext ρ; constructor <;> intro hρ
    · have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ ZetaZerosNearPoint t := by
        have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
                                                                                    
          simp [c_std, c_comm, hcenter_eq]
        simpa [hzeros_eq, heq]
          using this
      simpa [Set.mem_toFinset] using this
    · have : ρ ∈ ZetaZerosNearPoint t := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using this
      have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
        simp [c_std, c_comm, hcenter_eq]
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [heq] using this
      simpa [Set.mem_toFinset] using this
  have hLHS_le :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
    have :
        ‖logDerivZeta s -
            Finset.sum (hfin_std.toFinset)
              (fun ρ : ℂ => ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖
        ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
      simpa [F] using! hineq2
    simpa [norm_sub_comm', hFinset_eq]
      using this
                                   
  have hc_ne : riemannZeta c_std ≠ 0 := by simpa [c_std] using! zetacnot0 t
  have hnorm_pos : 0 < ‖riemannZeta c_std‖ := by simpa [norm_pos_iff] using hc_ne
  have hnorm_ne : ‖riemannZeta c_std‖ ≠ 0 := ne_of_gt hnorm_pos
  have hb_ne : b ≠ 0 := ne_of_gt hbpos
  have htpos0 : 0 < |t| := lt_trans (by norm_num) ht
  have ht_ne : |t| ≠ 0 := ne_of_gt htpos0
  have hlog_mul1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        = Real.log (b * |t|) + Real.log (1 / ‖riemannZeta c_std‖) := by
    simpa [div_eq_mul_inv] using Real.log_mul (mul_ne_zero hb_ne ht_ne) (inv_ne_zero hnorm_ne)
  have hlog_mul2 : Real.log (b * |t|) = Real.log b + Real.log (|t|) := by
    simpa using Real.log_mul hb_ne ht_ne
  have hζ_log_le : Real.log (1 / ‖riemannZeta c_std‖) ≤ A := by
    simpa [c_std] using! hA_bound t
  have hlog_bound1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ (Real.log b + Real.log (|t|)) + A := by
    have := add_le_add_right hζ_log_le (Real.log (b * |t|))
    simpa [hlog_mul1, hlog_mul2, add_comm, add_left_comm, add_assoc] using this
                                    
  have hlog_mono : Real.log (|t|) ≤ Real.log (|t| + 2) :=
    log_abs_le_log_abs_add_two (by simpa using ht)
  have hlog_bound2 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ Real.log (|t| + 2) + (Real.log b + A) := by
    have : Real.log b + Real.log (|t|) + A ≤ Real.log b + Real.log (|t| + 2) + A := by
      have := add_le_add_right hlog_mono (Real.log b)
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this A
    exact le_trans hlog_bound1 (by simpa [add_comm, add_left_comm, add_assoc] using this)
                                                
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hge5 : Real.log 4 ≤ Real.log (|t| + 2) := by
    have hxy : (4 : ℝ) ≤ |t| + 2 := by nlinarith [le_of_lt ht]
    exact Real.log_le_log (by norm_num) hxy
  have hconst_nonneg : 0 ≤ Real.log b + A := by
    have hbposlog : 0 < Real.log b := Real.log_pos hb_gt1
    have hApos : 0 < A := lt_trans (by norm_num) hA_gt1
    have : 0 ≤ Real.log b := le_of_lt hbposlog
    nlinarith
  have hnonneg : 0 ≤ (Real.log b + A) / Real.log 4 := div_nonneg hconst_nonneg (le_of_lt hlog5pos)
  have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
  have hconst_bound : (Real.log b + A)
        ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_left hge5 hnonneg
                             
    have : ((Real.log b + A) / Real.log 4) * Real.log 4 ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := this
                                        
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne5] using this
  have hlog_bound3 :
      Real.log (|t| + 2) + (Real.log b + A)
        ≤ K * Real.log (|t| + 2) := by
    have := add_le_add_right hconst_bound (Real.log (|t| + 2))

    simpa [K, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, one_mul]
      using this
  have hlog_bound_final :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ K * Real.log (|t| + 2) := le_trans hlog_bound2 hlog_bound3
               
  have hF_nonneg : 0 ≤ F := by
    have h1 : 0 ≤ 16 * r ^ 2 / (r - r1) ^ 3 := by
      have hnum : 0 ≤ 16 * r ^ 2 := by
        have : 0 ≤ (16 : ℝ) := by norm_num
        have : 0 ≤ r ^ 2 := by
          have := sq_nonneg r
          simpa [pow_two] using this
        simpa [mul_comm] using mul_nonneg (show 0 ≤ (16 : ℝ) by norm_num) this
      have hden : 0 < (r - r1) ^ 3 := by
        have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
        simpa using pow_pos this 3
      exact div_nonneg hnum (le_of_lt hden)
    have h2 : 0 ≤ 1 / ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := by
                           
      have hden1 : 0 < (R ^ 2 / R1 - R1) := by
        change 0 < ((9/10 : ℝ) ^ 2 / (5/6 : ℝ) - (5/6 : ℝ))
        norm_num
      have hden2 : 0 < Real.log (R / R1) := by
        have : 1 < R / R1 := by
          change (1 : ℝ) < (9/10 : ℝ) / (5/6 : ℝ)
          norm_num
        exact Real.log_pos this
      have hpos : 0 < ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := mul_pos hden1 hden2
      exact le_of_lt (one_div_pos.mpr hpos)
    have := add_nonneg h1 h2
    simpa [F] using this
                                       
  have hY_nonneg : 0 ≤ Real.log (|t| + 2) := by
                            
    have hgt1 : (1 : ℝ) < |t| + 2 := by
      have : (2 : ℝ) ≤ |t| + 2 := by
        have : 0 ≤ |t| := abs_nonneg t
        simp
      exact lt_of_lt_of_le (by norm_num) this
    exact le_of_lt (Real.log_pos hgt1)
  have hfinal1 :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * (K * Real.log (|t| + 2)) :=
    le_trans hLHS_le (by exact mul_le_mul_of_nonneg_left hlog_bound_final hF_nonneg)
  have hFactor_leC : F * K ≤ C := by exact le_trans (le_of_eq rfl) (le_max_left _ _)
  have hfinal2 : F * (K * Real.log (|t| + 2)) ≤ C * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_right hFactor_leC hY_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := le_trans hfinal1 hfinal2
  simpa [s]

lemma lem_explicit1RealReal :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs ((logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + t * Complex.I) - rho1)).re)))
          ≤ C * Real.log (|t| + 2) := by
  rcases lem_explicit1deltat with ⟨C, hCpos, hE⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  let s : ℂ := (1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I
  let S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  let g : ℂ → ℂ := fun rho1 : ℂ =>
    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1)
                                           
  have ht' : ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖
      ≤ C * Real.log (abs t + 2) := by
                                                 
    have h_app := hE t ht δ hδ
    rw [norm_sub_rev] at h_app
    exact h_app
                                
  have hleft_eq :
      abs ((logDerivZeta s).re - ∑ rho1 ∈ S, (g rho1).re)
        = abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re) := by
    simp [Complex.sub_re, Complex.re_sum]
                 
  have hbound :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖ := by
    simpa using Complex.abs_re_le_norm (logDerivZeta s - ∑ rho1 ∈ S, g rho1)
            
  have hfinal :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ C * Real.log (abs t + 2) :=
    le_trans hbound ht'
                                                      
  have hnorm : |t| = abs t := rfl
  simpa [s, S, g, hleft_eq, hnorm] using hfinal

lemma lem_explicit2Real :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs (
            (logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + (2 * t) * Complex.I) - rho1)).re))
          )
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit1RealReal with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                       
  have h_2t : 2 < |2 * t| := by
    rw [abs_mul, abs_two]
    linarith [ht]
  have h_bound := hEv (2 * t) h_2t δ hδ
                                 
  simp only [Complex.ofReal_mul] at h_bound
  exact h_bound

lemma lem_Re1delta2tge0 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t)) :
(((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re ≥ 0 := by
                                                      
  convert (preTransparency := .instances) lem_Re1deltatge0m delta hdelta (2 * t) hdelta_lt_1 rho1 h_rho1_in_Zt
  simp

lemma lem_sumrho2ge (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re) ≥ 0 := by
  apply Finset.sum_nonneg
  intro rho1 h_rho1_in_finset
                                                                   
  have h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t) := by
    rwa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite (2 * t))] at h_rho1_in_finset
                            
  exact lem_Re1delta2tge0 delta hdelta hdelta_lt_1 t rho1 h_rho1_in_Zt

lemma lem_sumrho2ge02 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
(fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re ≥ 0 := by
                                                                                   
  rw [lem_sumrho2 t delta hdelta hdelta_lt_1]
                                                             
  exact lem_sumrho2ge t delta hdelta hdelta_lt_1

lemma lem_explicit2Real2 :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ((-logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re)
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit2Real with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  set s : ℂ := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (s - rho1)).re)
                                                                  
  have h_bound :
      abs ((logDerivZeta s).re - Sre)
        ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa [s, S, Sre] using hEv t ht δ hδ
                                                                     
  have hS_nonneg : 0 ≤ Sre := by
                                                                       
    have h0 := lem_sumrho2ge02 t δ hδ.1 hδ.2

    simpa [s, S, Sre, lem_sumrho2 t δ hδ.1 hδ.2] using h0
                                             
  have h_left : -(C * Real.log (abs (2 * t) + 2)) ≤ (logDerivZeta s).re - Sre :=
    (abs_le.mp h_bound).1
                                        
  have h_neg : -((logDerivZeta s).re - Sre) ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa using neg_le_neg h_left
                                                                  
  have h_aux := sub_le_sub_right h_neg Sre
  have h_isol : - (logDerivZeta s).re ≤ C * Real.log (abs (2 * t) + 2) - Sre := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_aux
                                               
  have h_drop : C * Real.log (abs (2 * t) + 2) - Sre ≤ C * Real.log (abs (2 * t) + 2) :=
    sub_le_self _ hS_nonneg
             
  have h_final := le_trans h_isol h_drop
                                                            
  simpa [s, Complex.neg_re] using h_final

lemma lem_Z2bound :
  ∃ C > 1,
     ∀ t : ℝ, 2 < |t| →
      ∀ δ, 0 < δ ∧ δ < 1 →
        (-(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I))).re
          ≤ C * Real.log (abs t + 2) := by
                                                     
  obtain ⟨C₁, hC₁_pos, hbound₁⟩ := lem_explicit2Real2

  have h_log_comp :
      ∀ t : ℝ, 2 < |t| → Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := by
    intro t ht
    have h_pos_2t : 0 < abs (2 * t) + 2 := by linarith [abs_nonneg (2 * t)]
    have h_pos_t : 0 < abs t + 2 := by linarith [abs_nonneg t]
    have h_2t_eq : abs (2 * t) = 2 * abs t := by
      rw [abs_mul, abs_two]

    have h_bound : abs (2 * t) + 2 ≤ 4 * (abs t + 2) := by
      rw [h_2t_eq]
                                         
      linarith [abs_nonneg t]

    have h_4_pos : (0 : ℝ) < 4 := by norm_num
    have h_log_bound : Real.log (abs (2 * t) + 2) ≤ Real.log (4 * (abs t + 2)) :=
      Real.log_le_log h_pos_2t h_bound

    have h_log_mul_eq : Real.log (4 * (abs t + 2)) = Real.log 4 + Real.log (abs t + 2) := by
      exact Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h_pos_t)

    have h_4_le : (4 : ℝ) ≤ abs t + 2 := by linarith [ht]
    have h_log_4 : Real.log 4 ≤ Real.log (abs t + 2) :=
      Real.log_le_log (by norm_num) h_4_le

    calc Real.log (abs (2 * t) + 2)
      ≤ Real.log (4 * (abs t + 2)) := h_log_bound
      _ = Real.log 4 + Real.log (abs t + 2) := h_log_mul_eq
      _ ≤ Real.log (abs t + 2) + Real.log (abs t + 2) := add_le_add_left h_log_4 _
      _ = 2 * Real.log (abs t + 2) := by ring

  have hC₁_nonneg : 0 ≤ C₁ := le_of_lt (lt_trans zero_lt_one hC₁_pos)

  refine ⟨2 * C₁, ?_, ?_⟩
  ·                   
    linarith [hC₁_pos]
  ·              
    intro t ht δ hδ
    let s := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I

    have h1 : (-(logDerivZeta s)).re ≤ C₁ * Real.log (abs (2 * t) + 2) := hbound₁ t ht δ hδ

    have h3 : Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := h_log_comp t ht

    calc (-(logDerivZeta s)).re
      ≤ C₁ * Real.log (abs (2 * t) + 2) := h1
      _ ≤ C₁ * (2 * Real.log (abs t + 2)) := mul_le_mul_of_nonneg_left h3 hC₁_nonneg
      _ = (2 * C₁) * Real.log (abs t + 2) := by ring

lemma Z1bound :
  ∃ C > 1,
    ∀ (delta : ℝ), (0 < delta ∧ delta < 1) →
      ∀ t : ℝ, 2 < |t| →
        ∀ s : ℂ, s ∈ zeroZ ∧ s.im = t →
          (-(logDerivZeta ((1 : ℂ) + delta + t * Complex.I))).re
            ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
  classical
                                            
  obtain ⟨C0, hC0gt1, hExp⟩ := lem_explicit1RealReal
                                                                                  
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  let C : ℝ := max (C0 + 3 / Real.log 4) 2
  have hCgt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hCgt1, ?_⟩
  intro delta hdelta t ht s hs
                  
  set sp : ℂ := (1 : ℂ) + delta + t * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (sp - rho1)).re)
                                                                        
  have h_bound : abs ((logDerivZeta sp).re - Sre)
        ≤ C0 * Real.log (abs t + 2) := by
    simpa [sp, S, Sre] using hExp t ht delta hdelta
                                                                         
  have h_left : -(C0 * Real.log (abs t + 2)) ≤ (logDerivZeta sp).re - Sre :=
    (abs_le.mp h_bound).1
  have h_neg : -((logDerivZeta sp).re - Sre) ≤ C0 * Real.log (abs t + 2) := by
    simpa using neg_le_neg h_left
  have h_isol : - (logDerivZeta sp).re ≤ C0 * Real.log (abs t + 2) - Sre := by
    have := sub_le_sub_right h_neg Sre
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                              
  have hS_nonneg : 0 ≤ Sre := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    have hZt : rho1 ∈ ZetaZerosNearPoint t := by
      simpa [S, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite t)] using hmem
                                   
    simpa [sp] using
      (lem_Re1deltatge0m delta hdelta.1 t hdelta.2 rho1 hZt)
                                 
  have h_basic : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := by
    have h_drop : C0 * Real.log (abs t + 2) - Sre ≤ C0 * Real.log (abs t + 2) :=
      sub_le_self _ hS_nonneg
    exact le_trans h_isol h_drop
                                              
  by_cases hmem : s ∈ ZetaZerosNearPoint t
  ·                                                               
    set sigma : ℝ := s.re
    have h_rho_eq : s = (sigma : ℂ) + t * Complex.I := by
      have : s = s.re + s.im * Complex.I := by simp [Complex.re_add_im]
      simpa [sigma, hs.2] using this
                                              
    have hsum_rew := lem_sumrho1 t delta hdelta.1 hdelta.2
    have h_sum_ge' :=
      lem_Z1splitge3 delta hdelta.1 hdelta.2 sigma t s h_rho_eq hs.1 hmem
    have h_sum_ge : Sre ≥ 1 / ((1 : ℝ) + delta - sigma) := by
      simpa [sp, S, Sre, hsum_rew] using h_sum_ge'
                                                                                  
    have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      have : (1 / ((1 : ℝ) + delta - sigma)) ≤ Sre := h_sum_ge
      have := sub_le_sub_left this (C0 * Real.log (abs t + 2))
      exact le_trans h_isol (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
                                              
    have hCge : C0 ≤ C :=
      le_trans (by
        have : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
        have := add_le_add_right this C0
        simpa using this) (le_max_left _ _)
                                   
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have h_enlarge : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) :=
      mul_le_mul_of_nonneg_right hCge hY_nonneg
    have h2 : C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) ≤
              C * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (sub_le_sub_right h_enlarge (1 / ((1 : ℝ) + delta - sigma)))
    have := le_trans h1 h2
    simpa [sp, sigma, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  ·                                                                                           
                                                                             
    have h_notle : ¬ ‖s - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) := by
      intro hle
      exact hmem ⟨hs.1, hle⟩
    have hdist_gt : (5/6 : ℝ) < ‖s - ((3/2 : ℂ) + t * Complex.I)‖ := not_le.mp h_notle
                                                                                            
    have h_re : (s - ((3/2 : ℂ) + t * Complex.I)).re = s.re - (3/2 : ℝ) := by
      simp [Complex.sub_re, Complex.add_re]
    have h_im : (s - ((3/2 : ℂ) + t * Complex.I)).im = 0 := by
      have : (s - ((3/2 : ℂ) + t * Complex.I)).im = s.im - t := by
        simp [Complex.sub_im, Complex.add_im]
      simp [hs.2]
    have h_eq : s - ((3/2 : ℂ) + t * Complex.I) = (((s.re - (3/2 : ℝ)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [h_re]
      · simp [h_im]
    have hdist_real : ‖s - ((3/2 : ℂ) + t * Complex.I)‖ = |s.re - (3/2 : ℝ)| := by
      simpa [h_eq] using complex_abs_of_real (s.re - (3/2 : ℝ))
    have habs_gt : (5/6 : ℝ) < |s.re - (3/2 : ℝ)| := by simpa [hdist_real] using hdist_gt
                                 
    have h0 : riemannZeta (s.re + s.im * Complex.I) = 0 := by
      simpa [Complex.re_add_im] using! hs.1
    have hs_le1 : s.re ≤ 1 := lem_sigmale1 s.re s.im h0
                                                        
    have h_nonpos : s.re - (3/2 : ℝ) ≤ 0 := by linarith [hs_le1]
    have h_abs_eq : |s.re - (3/2 : ℝ)| = (3/2 : ℝ) - s.re := by
      have : |s.re - (3/2 : ℝ)| = -(s.re - (3/2 : ℝ)) := abs_of_nonpos h_nonpos
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h_gt' : (5/6 : ℝ) < (3/2 : ℝ) - s.re := by simpa [h_abs_eq] using habs_gt
    have hs_le_23 : s.re ≤ (2/3 : ℝ) := by linarith [h_gt']
                                                                    
    have hden_ge : (1/3 : ℝ) ≤ 1 + delta - s.re := by
      have : (1/3 : ℝ) ≤ 1 - s.re := by linarith [hs_le_23]
      have : 1 - s.re ≤ 1 + delta - s.re := by linarith [hdelta.1]
      exact le_trans ‹(1/3 : ℝ) ≤ 1 - s.re› this
    have hone_div_le3 : 1 / (1 + delta - s.re) ≤ (3 : ℝ) := by
      have : 1 / (1 + delta - s.re) ≤ 1 / (1/3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/3) hden_ge
      simpa [one_div] using this
    have hneg_ge : - (3 : ℝ) ≤ - (1 / (1 + delta - s.re)) := by
      simpa using (neg_le_neg hone_div_le3)
                                            
    have hlog_ge : Real.log 4 ≤ Real.log (abs t + 2) := by
      have : (4 : ℝ) < abs t + 2 := by linarith [ht]
      exact Real.log_le_log (by norm_num) (le_of_lt this)
    have hC_ge_add : C ≥ C0 + 3 / Real.log 4 := by exact le_max_left _ _
    have hCminus : C - C0 ≥ 3 / Real.log 4 := by linarith
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have hmul1 : (3 / Real.log 4) * Real.log 4 ≤ (3 / Real.log 4) * Real.log (abs t + 2) := by
      have hk_nonneg : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
      exact mul_le_mul_of_nonneg_left hlog_ge hk_nonneg
    have hmul2 : (3 / Real.log 4) * Real.log (abs t + 2) ≤ (C - C0) * Real.log (abs t + 2) := by
      exact mul_le_mul_of_nonneg_right hCminus hY_nonneg
    have hmul_ge3 : (3 : ℝ) ≤ (C - C0) * Real.log (abs t + 2) := by
      have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
      have hcalc : (3 / Real.log 4) * Real.log 4 = 3 := by
        simp [div_eq_mul_inv, hne5]
      have : (3 / Real.log 4) * Real.log 4 ≤ (C - C0) * Real.log (abs t + 2) :=
        le_trans hmul1 hmul2
      simpa [hcalc] using this
                                 
    have hCmul' : C0 * Real.log (abs t + 2) + 3 ≤ C * Real.log (abs t + 2) := by
      have : C0 * Real.log (abs t + 2) + 3 ≤ C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        exact add_le_add_right hmul_ge3 _
      have hcalc : C * Real.log (abs t + 2) =
          C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        ring
      simpa [hcalc, add_comm, add_left_comm, add_assoc] using this
                                                                              
    have : (-(logDerivZeta sp)).re ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
      have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := h_basic
      have h2 : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) - 3 := by
        linarith [hCmul']
      have h3 : C * Real.log (abs t + 2) - 3 ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
        have := add_le_add_left hneg_ge (C * Real.log (abs t + 2))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      exact le_trans h1 (le_trans h2 h3)
    simpa [sp, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (Complex.cpow (n : ℂ) ((-x) : ℂ)) * (Complex.cpow (n : ℂ) (-(y * I))) := by
                            
  rw [zeta1zetaseriesxy x y hx]
                                             
  congr 1
  ext n
                      
  rw [← Complex.cpow_eq_pow]
                                                          
  by_cases h : n = 0
  ·                                
    simp [h]
  ·                                 
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
                                                          
    ring

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
                                                        
  have h_zeta_ne_zero := Zconverges1 x y hx

  have h_series := lem_zeta1zetaseriesxy2 x y hx

  have h_re : 1 < (x + y * I).re := by
    rw [complex_add_re_ofReal_mul_I]
    exact hx

  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re

  exact LSeriesSummable_to_explicit_summable x y hx h_summable

lemma sumRealLambda (x y : ℝ) (hx : 1 < x) :
    (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
    ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
  apply Complex.re_tsum
  exact Zseriesconverges1 x y hx

lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                         
  rw [lem_zeta1zetaseriesxy2 x y hx]
                                                   
  exact sumRealLambda x y hx

lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← lem_eacosalog3 n hn y]
                                                                                          
    congr 1
                                                                        
    rw [Complex.cpow_eq_pow]
                                     
    simp [I]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
                                                  
  exact Rezetaseries_convergence x (2 * t) hx

lemma Z341bounds_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0) (_hδ1 : δ < 1), ∀ t : ℝ, 2 < |t| → ∀ σ : ℝ,
    (σ + t * Complex.I) ∈ zeroZ →
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re
    + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re
    +     (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
    ≤ 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by
                                                                                           
  rcases Z0boundRe_const3 with ⟨C0, hC0pos, hZ0⟩
  rcases Z1bound with ⟨C1, hC1pos, hZ1⟩
  rcases lem_Z2bound with ⟨C2, hC2pos, hZ2⟩

  let C := 3 * C0 + 4 * C1 + C2

  have hC_gt_one : 1 < C := by
    have h1 : 1 < C0 := hC0pos
    have h2 : 3 < 3 * C0 := by linarith [mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 3)]
    have h3 : 0 < 4 * C1 := mul_pos (by norm_num) (lt_trans zero_lt_one hC1pos)
    have h4 : 0 < C2 := lt_trans zero_lt_one hC2pos
    linarith [h2, h3, h4]

  use C
  constructor
  · exact hC_gt_one
  · intro δ hδpos hδ1 t ht σ hσ

    have hZ0_bound : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ C0 + (1 / δ) := by
      have := hZ0 δ hδpos
      linarith

    have hZ1_bound : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ -(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2) := by
      let s := σ + t * Complex.I
      have hs_mem : s ∈ zeroZ := hσ
      have hs_im : s.im = t := by simp [s]
      have hs_re : s.re = σ := by simp [s]
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      have := hZ1 δ hδ_cond t ht s ⟨hs_mem, hs_im⟩
      rw [hs_re] at this
      exact this

    have hZ2_bound : (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re ≤ C2 * Real.log (|t| + 2) := by
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      exact hZ2 t ht δ hδ_cond

    have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
      have h1 : 2 < |t| := ht
      have h2 : Real.exp 1 < 3 := lem_three_gt_e
      have he_lt_t2 : Real.exp 1 < |t| + 2 := by linarith
      have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
      exact Real.le_log_iff_exp_le ht2_pos |>.mpr (le_of_lt he_lt_t2)

    calc
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re + (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
        ≤ 3 * (C0 + (1 / δ)) + 4 * (-(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2)) + C2 * Real.log (|t| + 2) := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ0_bound (by norm_num)) (mul_le_mul_of_nonneg_left hZ1_bound (by norm_num))) hZ2_bound
      _ = 3 * C0 + 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + 3 * C0 + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + ((4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0) := by ring
      _ ≤ 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2) := by
                                                                           
        have hC0_pos : 0 < C0 := lt_trans zero_lt_one hC0pos
        have hC0_nonneg : 0 ≤ 3 * C0 := mul_nonneg (by norm_num) (le_of_lt hC0_pos)
        have h_absorb := absorb_pos_constant_into_log (L := Real.log (|t| + 2)) (A := 4 * C1 + C2) (c := 3 * C0) hlog_ge_one hC0_nonneg
                                                                                                               
        exact add_le_add_right h_absorb (3 / δ - 4 / (1 + δ - σ))
      _ = 3 / δ - 4 / (1 + δ - σ) + (3 * C0 + 4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by ring

lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
                                                         
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert (preTransparency := .instances) Rezeta1zetaseries (1 + delta) t h1
                                                
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
                                                             
  have h1 : 1 < 1 + delta := by linarith [hdelta]
                                                                                 
  have h2 : (1 : ℂ) + delta + (2 * t) * I = (1 + delta : ℝ) + ((2 * t) : ℝ) * I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
                                             
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      rw [lem_cost0 n hn 0 rfl, mul_one]

  rw [← h_lhs, h_series, h_rhs]

lemma Z341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
     4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
     ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Rezeta1zetaseries0 delta hdelta, Rezeta1zetaseries1 t delta hdelta, Rezeta1zetaseries2 t delta hdelta]

lemma lem341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))
    + (4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))
    + (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)))
    = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
                                       
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  rw [← Summable.tsum_mul_left 3 h2]
  rw [← Summable.tsum_mul_left 4 h3]

  rw [← Summable.tsum_add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)]
  rw [← Summable.tsum_add]

  congr 1
  ext n
  ring

  · exact Summable.add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)
  · exact h4

lemma lem_341series2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Z341series t delta hdelta]
  exact lem341series t delta hdelta

lemma Z341pos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ 3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
        4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
        (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re := by
  rw [lem_341series2 t delta hdelta]
  exact lem_seriespos t delta hdelta

lemma lem341tsC :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    4 / (1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2))) ≤ 7 * C * Real.log (abs s.im + 2) := by
                                             
  obtain ⟨C, hCpos, hbound⟩ := Z341bounds_const
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTim

  let L : ℝ := Real.log (|s.im| + 2)
  have hLpos : 0 < L := log_abs_two_pos (s.im)
  let δ : ℝ := 1 / (2 * C * L)

  have hCpos_weak : 0 < C := lt_trans zero_lt_one hCpos
  have hδpos : 0 < δ := pos_delta_from_C_L hCpos_weak hLpos

  have hδlt : δ < 1 := by
                                               
    have hL_gt_1 : 1 < L := by
      have h5_lt : 4 < |s.im| + 2 := by linarith [hTim]
      have hL_gt_log5 : Real.log 4 < L := Real.log_lt_log (by norm_num) h5_lt
      have hlog5_gt_1 : 1 < Real.log 4 := by
        have h5_gt_e : Real.exp 1 < 4 := by
          have h3_gt_e := lem_three_gt_e
          linarith [h3_gt_e]
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h5_gt_e
      linarith [hlog5_gt_1, hL_gt_log5]
                                                      
    have h2CL_gt_1 : 1 < 2 * C * L := by
                                                                             
      have hCL_gt_1 : 1 < C * L := by
        calc C * L
          > 1 * L := by exact mul_lt_mul_of_pos_right hCpos hLpos
          _ = L := by simp
          _ > 1 := hL_gt_1
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      calc 2 * C * L
        = 2 * (C * L) := by ring
        _ > 2 * 1 := by exact mul_lt_mul_of_pos_left hCL_gt_1 h2_pos
        _ = 2 := by simp
        _ > 1 := by norm_num
                                  
    simp only [δ]
    rw [div_lt_one_iff]
    left
    exact ⟨two_C_log_pos hCpos_weak, h2CL_gt_1⟩

  have hmem : (s.re + s.im * Complex.I) ∈ zeroZ := by
    simpa [Complex.re_add_im] using hs.1
  have hupper := hbound δ hδpos hδlt (s.im) hTim (s.re) hmem

  have hpos := Z341pos (s.im) δ hδpos

  have hRHS_nonneg : 0 ≤ 3 / δ - 4 / (1 + δ - s.re) + C * L := le_trans hpos hupper
  have hineq1 : 4 / (1 + δ - s.re) ≤ 3 / δ + C * L := by linarith [hRHS_nonneg]

  have hineq2 : 4 / (1 - s.re + δ) ≤ 3 / δ + C * L := by
    convert (preTransparency := .instances) hineq1 using 2
    all_goals try with_reducible_and_instances rfl
    ring

  have hinv : 1 / δ = 2 * C * L := by
    simp only [δ, one_div, inv_inv]

  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv

  have hfinal : 4 / (1 - s.re + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2

  convert (preTransparency := .instances) hfinal

lemma lem341tsC2 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
          1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) ≥ 4 / (7 * C * Real.log (abs s.im + 2)) := by
                                                 
  rcases lem341tsC with ⟨C, hCpos, hT⟩
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTs
                                                      
  set a := 1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) with ha
  set b := 7 * C * Real.log (abs s.im + 2) with hb
  have hineq : 4 / a ≤ b := by
    simpa [ha, hb] using hT s hs hTs
                  
  have h_abs_nonneg : 0 ≤ |s.im| := abs_nonneg _
  have h_two_le : (2 : ℝ) ≤ |s.im| + 2 := by
    have h' : (2 : ℝ) + 0 ≤ 2 + |s.im| := add_le_add_right h_abs_nonneg 2
    simp
  have h_one_lt : (1 : ℝ) < |s.im| + 2 := lt_of_lt_of_le one_lt_two h_two_le
  have hx0 : 0 ≤ |s.im| + 2 := by linarith [h_abs_nonneg]
  have hlogpos : 0 < Real.log (|s.im| + 2) := (Real.log_pos_iff hx0).2 h_one_lt
  have h7pos : 0 < (7 : ℝ) := by exact_mod_cast (by decide : (0 : ℕ) < 7)
  have hbpos : 0 < b := by
    have h7Cpos : 0 < 7 * C := by linarith
    exact mul_pos h7Cpos hlogpos
                  
  rcases hs with ⟨_, hRepos, hRelt⟩
  have h1 : 0 < 1 - s.re := sub_pos.mpr hRelt
  have h2pos : 0 < (2 : ℝ) := lt_trans zero_lt_one one_lt_two
  have h2Cpos : 0 < (2 : ℝ) * C := by linarith
  have hdenpos : 0 < 2 * C * Real.log (|s.im| + 2) := mul_pos h2Cpos hlogpos
  have hinvpos : 0 < 1 / (2 * C * Real.log (|s.im| + 2)) := one_div_pos.mpr hdenpos
  have hapos : 0 < a := by
    have := add_pos h1 hinvpos
    simpa [ha] using this
                                                           
  have hres := reciprocal_div_inequality a b hapos hbpos hineq
  simpa [ha, hb] using hres

lemma lem341tsC3 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    1 - s.re ≥ 1 / (14 * C * Real.log (abs s.im + 2)) := by
  obtain ⟨C, hCpos, hT⟩ := lem341tsC2
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTle
  have h := hT s hs hTle
                                                                             
  have h' : 4 / (7 * C * Real.log (abs s.im + 2)) ≤
      (1 - s.re) + 1 / (2 * C * Real.log (abs s.im + 2)) := by
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using h
                                            
  have h'' := fraction_diff_lower_bound C (Real.log (abs s.im + 2)) (1 - s.re) h'
             
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using h''

lemma zerofree :
    ∃ c, c > 0 ∧ c < 1 ∧ ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| → s.re ≤ 1 - c / (Real.log (abs s.im + 2)) := by
                                          
  rcases lem341tsC3 with ⟨C0, hC0pos, hT⟩
                                                 
  set C : ℝ := 1 / (14 * C0) with hCdef
               
  have h14pos : 0 < (14 : ℝ) := by norm_num
  have hC0pos' : 0 < C0 := lt_trans zero_lt_one hC0pos
  have hCpos : 0 < C := by
    have hdenpos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    exact one_div_pos.mpr hdenpos
                                                                             
  have hClt1 : C < 1 := by
    have h14C0_pos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    have h14C0_gt_1 : 1 < 14 * C0 := by
      have h14_gt_1 : (1 : ℝ) < 14 := by norm_num
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < 14 * 1 := by exact mul_lt_mul_of_pos_right h14_gt_1 zero_lt_one
        _ < 14 * C0 := by exact mul_lt_mul_of_pos_left hC0pos h14pos
    rw [hCdef]
    rw [div_lt_one_iff]
    left
    exact ⟨h14C0_pos, h14C0_gt_1⟩
                                                  
  refine ⟨C, hCpos, hClt1, ?_⟩
  intro s hs hTle
                                    
  set L := Real.log (abs s.im + 2) with hLdef
                                                          
  have hb0 := hT s hs hTle
                                                 
  have hb' : C / L ≤ 1 - s.re := by
    simpa [hLdef, hCdef, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb0
                                             
  have : s.re ≤ 1 - C / L := by linarith
  simpa [hLdef] using this

noncomputable def zerofree_constant : ℝ := Classical.choose zerofree

lemma zerofree_constant_pos : 0 < zerofree_constant :=
  (Classical.choose_spec zerofree).1

lemma zerofree_constant_lt_one : zerofree_constant < 1 :=
  (Classical.choose_spec zerofree).2.1

noncomputable def deltaz (z : ℂ) : ℝ := (zerofree_constant / 20) / Real.log (|z.im| + 2)

noncomputable def deltaz_t (t : ℝ) : ℝ := deltaz (t * Complex.I)

lemma lem_delta19 :
  (∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9)) ∧
  (∀ t : ℝ, |t| > 2 → (0 < deltaz_t t ∧ deltaz_t t < 1/9)) := by
                                          
  have h_complex : ∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9) := by
    intro z hz
    constructor
    ·                     
      have h_num_pos : 0 < zerofree_constant / 20 := by
        exact div_pos zerofree_constant_pos (by norm_num)
      have h_den_pos : 0 < Real.log (|z.im| + 2) := by
        have h_gt_one : (1 : ℝ) < |z.im| + 2 := by
          have h_nonneg : (0 : ℝ) ≤ |z.im| := abs_nonneg _
          linarith [hz]
        exact Real.log_pos h_gt_one
      unfold deltaz
      exact div_pos h_num_pos h_den_pos
    ·                       
                                       
      have h_den_ge_half : (1/2 : ℝ) ≤ Real.log (|z.im| + 2) := by
                                         
        have h_den_ge_log2 : Real.log 2 ≤ Real.log (|z.im| + 2) := by
          have h_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          have h_le : (2 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          exact Real.log_le_log (by norm_num) h_le
                                              
        have h_log2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
          have h_exp_half_le_two : Real.exp (1/2) ≤ 2 := by
                                                                 
            have h_exp_one_lt_three : Real.exp 1 < 3 := lem_three_gt_e
            have h_exp_sq : (Real.exp (1/2))^2 = Real.exp 1 := by
              rw [pow_two, ← Real.exp_add]; norm_num
            have h_exp_sq_lt_four : (Real.exp (1/2))^2 < 4 := by
              rw [h_exp_sq]; linarith [h_exp_one_lt_three]
                                               
            have h_exp_pos : 0 ≤ Real.exp (1/2) := le_of_lt (Real.exp_pos _)
            have h_two_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_four_eq : (2 : ℝ)^2 = 4 := by norm_num
            rw [← h_four_eq] at h_exp_sq_lt_four
            have h_lt_abs := (sq_lt_sq).mp h_exp_sq_lt_four
            rw [abs_of_nonneg h_exp_pos, abs_of_nonneg h_two_pos] at h_lt_abs
            exact le_of_lt h_lt_abs
          exact (Real.le_log_iff_exp_le (by norm_num : 0 < (2 : ℝ))).mpr h_exp_half_le_two
        exact le_trans h_log2_ge_half h_den_ge_log2
                                            
      have h_inv_le_two : 1 / Real.log (|z.im| + 2) ≤ 2 := by
        have h_pos_half : 0 < (1/2 : ℝ) := by norm_num
        have h_ineq := one_div_le_one_div_of_le h_pos_half h_den_ge_half
        convert (preTransparency := .instances) h_ineq using 1 <;> first | rfl | norm_num
                           
      have h_bound : deltaz z ≤ zerofree_constant / 10 := by
        unfold deltaz

        rw [div_eq_mul_inv]
                                                                                              
        have h_num_nonneg : 0 ≤ zerofree_constant / 20 := by
          exact le_of_lt (div_pos zerofree_constant_pos (by norm_num))
        have h_mul_ineq := mul_le_mul_of_nonneg_left h_inv_le_two h_num_nonneg
        convert (preTransparency := .instances) h_mul_ineq using 1 <;> first | rfl | ring
                                                         
      have h_lt_tenth : zerofree_constant / 10 < 1 / 10 := by
        exact div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
      have h_tenth_lt_ninth : (1 : ℝ) / 10 < 1 / 9 := by norm_num
      exact lt_trans (lt_of_le_of_lt h_bound h_lt_tenth) h_tenth_lt_ninth

  constructor
  · exact h_complex
  ·              
    intro t ht
                                                                             
    have h_eq : deltaz_t t = deltaz (t * Complex.I) := rfl
    rw [h_eq]
    have h_im_eq : |(t * Complex.I).im| = |t| := by simp
    rw [← h_im_eq] at ht
    exact h_complex (t * Complex.I) ht

lemma riemannZeta_zeros_finite_of_compact (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by

  by_contra h_not_finite
  push Not at h_not_finite

  let Z := {z ∈ K | riemannZeta z = 0}

  have hZ_inf : Z.Infinite := h_not_finite
  have hZ_sub : Z ⊆ K := fun z hz => hz.1

  obtain ⟨z₀, hz₀_K, hz₀_acc⟩ := lem_bolzano_weierstrass hK hZ_inf hZ_sub

  by_cases h_eq_one : z₀ = 1
  ·                                                               
    subst h_eq_one
                                                 
    have hZ_zeros : ∀ z ∈ Z, riemannZeta z = 0 := fun z hz => hz.2
                                                              
    exact riemannZeta_no_zeros_accumulate_at_one Z hZ_zeros hz₀_acc

  ·                                    
                                                                 
    have h_analytic : AnalyticAt ℂ riemannZeta z₀ :=
      zetaanalOnnot1 z₀ h_eq_one

    obtain h_ev_zero | h_ev_ne := h_analytic.eventually_eq_zero_or_eventually_ne_zero

    ·                                                                

      have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta z₀ h_ev_zero

      have h_eq_on_zero := zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        complex_minus_singleton_connected h_eq_one h_freq

      have : riemannZeta 0 = 0 := h_eq_on_zero (by simp : (0 : ℂ) ∈ {s | s ≠ 1})
      rw [riemannZeta_zero] at this
      norm_num at this

    ·                                                                       

      unfold AccPt at hz₀_acc

      have h_ev_not_Z : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∉ Z := by
        apply Filter.Eventually.mono h_ev_ne
        intro z hz hz_in_Z
        exact hz hz_in_Z.2

      have h_ev_false : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z, False := by
        rw [Filter.eventually_inf_principal]
        exact h_ev_not_Z

      have h_eq_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp h_ev_false

      have h_ne_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z ≠ ⊥ := hz₀_acc.ne

      exact h_ne_bot h_eq_bot

lemma lem_ZFRdelta :
  ∀ z : ℂ, 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0 := by
  intro z him hre
  by_cases h1 : 1 ≤ z.re
  ·                                     
    simpa using riemannZeta_ne_zero_of_one_le_re h1
                        
  have hzlt1 : z.re < 1 := lt_of_not_ge h1
                                                 
  have hgt : |z.im| > 2 := by simpa using him
  have hδ := (lem_delta19).1 z hgt
  rcases hδ with ⟨hδ_pos, hδ_lt_19⟩
                                                                  
  have h9δ_lt1 : 9 * deltaz z < 1 := by
    have h := mul_lt_mul_of_pos_left hδ_lt_19 (by norm_num : 0 < (9 : ℝ))
    have h9 : (9 : ℝ) * (1 / 9) = 1 := by norm_num
    simpa [h9] using h
  have hzre_pos : 0 < z.re := by
    have : 0 < 1 - 9 * deltaz z := sub_pos.mpr h9δ_lt1
    exact lt_trans this hre
                                           
  by_contra hzero
  have hzmem : z ∈ zeroZ := by simpa [zeroZ] using hzero
                                                                   
  have hprop := (Classical.choose_spec zerofree).2.2
  have hbound : z.re ≤ 1 - zerofree_constant / Real.log (|z.im| + 2) :=
    hprop z ⟨hzmem, hzre_pos, hzlt1⟩ him
                                           
  set L : ℝ := Real.log (|z.im| + 2) with hLdef
  have hLpos : 0 < L := by
    have hone_lt : (1 : ℝ) < |z.im| + 2 := by
      have : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have := Real.log_pos hone_lt
    simpa [hLdef] using this
                                     
  have hb_le_a' : ((9 : ℝ) / 20) * (zerofree_constant / L) ≤ zerofree_constant / L := by
    have hcoef_le1 : ((9 : ℝ) / 20) ≤ 1 := by norm_num
    have ha_nonneg : 0 ≤ zerofree_constant / L := le_of_lt (div_pos zerofree_constant_pos hLpos)
    have := mul_le_mul_of_nonneg_right hcoef_le1 ha_nonneg
    simpa [one_mul] using this
  have h9d_eq : 9 * deltaz z = ((9 : ℝ) / 20) * (zerofree_constant / L) := by
    simp [deltaz, hLdef, div_eq_mul_inv, mul_left_comm, mul_assoc]
  have hdelta_le : 9 * deltaz z ≤ zerofree_constant / L := by
    simpa [h9d_eq] using hb_le_a'
  have h_le_rhs : 1 - zerofree_constant / L ≤ 1 - 9 * deltaz z := by
    have hneg := neg_le_neg hdelta_le
    simpa [sub_eq_add_neg] using! add_le_add_right hneg 1
                              
  have hle : z.re ≤ 1 - 9 * deltaz z := le_trans hbound h_le_rhs
  have hcontr : z.re < z.re := lt_of_le_of_lt hle hre
  exact (lt_irrefl (z.re)) hcontr

lemma lem_ZFRinD (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∈ Metric.closedBall c (2/3) := by
  intro c h
  rcases h with ⟨h_low, hrest⟩
  rcases hrest with ⟨h_high, him⟩
  have hsub : z - c = ((z.re - (3/2)) : ℂ) := by
    simpa [c] using! complex_sub_ofReal_I_real_eq_ofReal z (3/2) t him
  have h1 : dist z c = ‖((z.re - (3/2)) : ℂ)‖ := by
    simp [dist_eq_norm, hsub]
  have h2 : ‖((z.re - (3/2)) : ℂ)‖ = ‖z.re - (3/2)‖ := by
    simpa using (Complex.norm_real (z.re - (3/2)))
  have hdist_abs : dist z c = |z.re - (3/2)| := by
    have h4 : dist z c = ‖z.re - (3/2)‖ := h1.trans h2
    simpa [Real.norm_eq_abs] using h4
  have hnonpos : z.re - (3/2) ≤ 0 := sub_nonpos_of_le h_high
  have habs : |z.re - (3/2)| = 3/2 - z.re := by
    have := abs_of_nonpos hnonpos
    simpa [neg_sub] using this
  have hdist_eq : dist z c = 3/2 - z.re := hdist_abs.trans habs
  have h_le : dist z c ≤ 1/2 + deltaz_t t := by
    calc
      dist z c = 3/2 - z.re := hdist_eq
      _ ≤ 3/2 - (1 - deltaz_t t) := by linarith
      _ = 1/2 + deltaz_t t := by ring
  have hδlt : deltaz_t t < 1/9 := (lem_delta19.2 t ht).2
  have h12δ_lt : (1/2 : ℝ) + deltaz_t t < (1/2 : ℝ) + 1/9 := by
    have := add_lt_add_left hδlt (1/2 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h123_lt : (1/2 : ℝ) + 1/9 < (2/3 : ℝ) := by norm_num
  have h_lt : (1/2 : ℝ) + deltaz_t t < (2/3 : ℝ) := lt_trans h12δ_lt h123_lt
  have hdist_le : dist z c ≤ 2/3 := le_trans h_le (le_of_lt h_lt)
  exact (Metric.mem_closedBall).2 hdist_le

lemma lem_ZFRnotK (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∉ zerosetKfRc (5/6) c riemannZeta := by
  intro c h

  obtain ⟨h_ge, h_le, h_im⟩ := h

  have h_delta_eq : deltaz z = deltaz_t t := by
    rw [deltaz_t, deltaz]
                                              
    congr 1
    congr 1
                                         
    rw [h_im]

    simp only [Complex.mul_I_im, Complex.ofReal_re]

  have h_ge_delta : 1 - deltaz z ≤ Complex.re z := by
    rwa [← h_delta_eq] at h_ge

  have h_im_gt : |z.im| > 2 := by
    rw [h_im]
    exact ht

  have h_delta_pos : 0 < deltaz z := by
    exact (lem_delta19.1 z h_im_gt).1

  have h_delta_lt_9delta : deltaz z < 9 * deltaz z := by
    linarith [h_delta_pos]

  have h_strict : Complex.re z > 1 - 9 * deltaz z := by
    linarith [h_ge_delta, h_delta_lt_9delta]

  have h_zeta_ne_zero : riemannZeta z ≠ 0 :=
    lem_ZFRdelta z h_im_gt h_strict

  intro h_mem
                                                                  
  have h_zero : riemannZeta z = 0 := h_mem.2
                                    
  exact h_zeta_ne_zero h_zero

lemma lem_Zeta_Expansion_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t;
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
        ‖(deriv riemannZeta z / riemannZeta z) -
          (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖
        ≤ C_1 * Real.log |t| := by
  obtain ⟨C, hC_gt_one, hC_expansion⟩ :=
    Zeta1_Zeta_Expansion (2/3) (3/4)
    (by norm_num : (0 : ℝ) < 2/3)
    (by norm_num : (2/3 : ℝ) < 3/4)
    (by norm_num : (3/4 : ℝ) < 5/6)
  let C_1 := C * (1 / ((3/4 : ℝ) - 2/3)^3 + 1)
  have hC_1_gt_1 : C_1 > 1 := by
    have h_coeff : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 + 1 > 1 := by
      have h_pos : ((3/4 : ℝ) - 2/3)^3 > 0 := by norm_num
      have h_div_pos : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 > 0 := div_pos one_pos h_pos
      linarith
    have h_ge_1 : (1 : ℝ) ≤ C := le_of_lt hC_gt_one
    exact one_lt_mul_of_le_of_lt h_ge_1 h_coeff
  refine ⟨C_1, hC_1_gt_1, ?_⟩
  intro t ht c hfin z hz
  have ht2 : |t| > 2 := by linarith
  have hz_in_ball : z ∈ Metric.closedBall c (2/3) := by
    simpa [c] using (lem_ZFRinD t ht2 z hz)
  have hz_not_in_K : z ∉ zerosetKfRc (5/6) c riemannZeta := by
    simpa [c] using (lem_ZFRnotK t ht2 z hz)
  have hz_in_diff : z ∈ Metric.closedBall c (2/3) \ zerosetKfRc (5/6) c riemannZeta :=
    ⟨hz_in_ball, hz_not_in_K⟩
  have h_expansion := hC_expansion t ht hfin z hz_in_diff
  rw [show logDerivZeta z = deriv riemannZeta z / riemannZeta z from rfl] at h_expansion
  exact h_expansion

lemma lem_Rerhotodeltarho {ρ : ℂ} :
  ∀ t : ℝ, |t| > 3 → ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) (3/2+ t* Complex.I) riemannZeta) → ρ.re ≤ 1 - 9 * deltaz ρ := by
  intro t ht h_mem
                                                   
  have h_zero : riemannZeta ρ = 0 := h_mem.2

  have h_ball : ρ ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6) := h_mem.1

  have h_dist : dist ρ (3/2 + t * Complex.I) ≤ 5/6 := by
    rwa [Metric.mem_closedBall] at h_ball

  have h_im : 2 < |ρ.im| := by
                                                                 
    have h_im_bound : |ρ.im - t| ≤ 5/6 := by
                                         
      have h_le_norm : |ρ.im - t| ≤ ‖ρ - (3/2 + t * Complex.I)‖ := by
        have : |(ρ - (3/2 + t * Complex.I)).im| ≤ ‖ρ - (3/2 + t * Complex.I)‖ :=
          Complex.abs_im_le_norm _
        have h_im_eq : (ρ - (3/2 + t * Complex.I)).im = ρ.im - t := by
          simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im]
        rwa [← h_im_eq]
      rw [← Complex.dist_eq] at h_le_norm
      linarith [h_le_norm, h_dist]

    have triangle := abs_sub_abs_le_abs_sub t ρ.im

    have eq_comm : |t - ρ.im| = |ρ.im - t| := abs_sub_comm t ρ.im
    rw [eq_comm] at triangle

    have h_ge : |ρ.im| ≥ |t| - |ρ.im - t| := by linarith [triangle]

    have : |ρ.im| ≥ |t| - 5/6 := by linarith [h_ge, h_im_bound]
    have : |ρ.im| > 3 - 5/6 := by linarith [ht]
    have h_calc : (3 : ℝ) - 5/6 = 13/6 := by norm_num
    have h_gt2 : (13 : ℝ)/6 > 2 := by norm_num
    rw [h_calc] at *
    linarith [h_gt2]

  have h_not_gt : ¬(ρ.re > 1 - 9 * deltaz ρ) := by
    intro h_gt
    have h_ne_zero := lem_ZFRdelta ρ h_im h_gt
    exact h_ne_zero h_zero

  exact le_of_not_gt h_not_gt

lemma lem_Ddt2dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    deltaz_t t ≤ 3 * deltaz z := by
  intro t ht z hz
  have h := lem_D1logtlog t ht z hz
  have hpos : 0 ≤ zerofree_constant / 20 := by
    have ha : 0 < zerofree_constant := zerofree_constant_pos
    have h9 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt ha) (le_of_lt h9)
  have h2 := mul_le_mul_of_nonneg_left h hpos
  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
            simp [deltaz_t, deltaz]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (3 / Real.log (|z.im| + 2)) := h2
    _ = 3 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
            simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
    _ = 3 * deltaz z := by simp [deltaz, div_eq_mul_inv, mul_left_comm, mul_assoc]

lemma lem_deltarhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → deltaz ρ ≥ (1/3) * deltaz_t t := by
  intro c hρK
  rcases hρK with ⟨hball, _hzero⟩
  have hball' : ρ ∈ Metric.closedBall ((3/2 : ℂ) + t * Complex.I) (5/6) := by
    simpa [c, mul_comm] using! hball
  have hmain : deltaz_t t ≤ 3 * deltaz ρ := lem_Ddt2dz t ht ρ hball'
  have hthird_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
  have h_mul : (1/3 : ℝ) * deltaz_t t ≤ (1/3 : ℝ) * (3 * deltaz ρ) :=
    mul_le_mul_of_nonneg_left hmain hthird_nonneg
  have h_simplify : (1/3 : ℝ) * (3 * deltaz ρ) = deltaz ρ := by
    ring
  have : (1/3 : ℝ) * deltaz_t t ≤ deltaz ρ := by
    simpa [h_simplify] using h_mul
  simpa [mul_comm] using this

lemma lem_Rerhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ρ.re ≤ 1 - 3 * deltaz_t t := by
  intros c h_rho_in
                                                          
  have h1 : ρ.re ≤ 1 - 9 * deltaz ρ :=
    lem_Rerhotodeltarho (ρ := ρ) t ht (by simpa [c, mul_comm] using! h_rho_in)
                                                         
  have h2 : deltaz ρ ≥ (1/3) * deltaz_t t := lem_deltarhotodeltat t ht ρ h_rho_in
                                                         
  have h3 : 9 * deltaz ρ ≥ 3 * deltaz_t t := by
    calc
      9 * deltaz ρ
          ≥ 9 * ((1/3) * deltaz_t t) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 9)
      _ = 9 * (1/3) * deltaz_t t := by ring
      _ = 3 * deltaz_t t := by norm_num
                                         
  have h4 : 1 - 9 * deltaz ρ ≤ 1 - 3 * deltaz_t t := by
    linarith [h3]
                                                        
  exact le_trans h1 h4

lemma lem_RezRerho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    z.re - ρ.re ≥ 2 * deltaz_t t := by
  intro c h_rho_mem h_z
                                                     
  have h_rho_bound := lem_Rerhotodeltat t ht ρ h_rho_mem
                                                
  have h_z_lower := h_z.1
                                                                                      
  linarith [h_z_lower, h_rho_bound]

lemma lem_abszrhodelta (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ ≥ 2 * deltaz_t t := by
  intro c h_rho_in_K h_z_conditions
                                                         
  have h1 : z.re - ρ.re ≥ 2 * deltaz_t t := (lem_RezRerho t ht z ρ) h_rho_in_K h_z_conditions
                                                     
  have h2 : ‖z - ρ‖ ≥ z.re - ρ.re := lem_abszrhoReRe z ρ
                                                                    
  exact le_trans h1 h2

lemma lem_1abszrho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) := by
  intro c hρ hz
                                                              
  apply one_div_le_one_div_of_le
                                           
  · have h_delta_pos : 0 < deltaz_t t := by
      have h_delta19 := lem_delta19
      exact (h_delta19.2 t (by linarith [ht] : |t| > 2)).1
    linarith [h_delta_pos]
                                                  
  · exact lem_abszrhodelta t ht z ρ hρ hz

lemma lem_finiteKzeta (t : ℝ) (_ht : |t| > 3) :
    let c := (3/2 : ℂ) + I * t
    (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite := by
  intro c
  have hK : IsCompact (Metric.closedBall c (5 / (6 : ℝ))) :=
    closedBall_compact_complex c (5 / (6 : ℝ))
  simpa [zerosetKfRc] using
    (riemannZeta_zeros_finite_of_compact (Metric.closedBall c (5 / (6 : ℝ))) hK)

lemma lem_triangle_ZFR (t : ℝ) (_ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) := by
                                                                                                  
  intros c hfin hz_cond

  apply le_trans (norm_sum_le _ _)

  apply Finset.sum_le_sum
  intro ρ hρ

  rw [norm_div]

  rw [Complex.norm_natCast]

lemma lem_Zeta_Triangle_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
        ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ +
        C_1 * Real.log |t| := by
  obtain ⟨C1, hC1, hbound⟩ := lem_Zeta_Expansion_ZFR
  refine ⟨C1, hC1, ?_⟩
  intro t ht c hfin z hz
                                           
  let S := (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))
  have hbound1 := hbound t ht hfin z hz
  have htri : ‖deriv riemannZeta z / riemannZeta z‖ ≤ ‖(deriv riemannZeta z / riemannZeta z) - S‖ + ‖S‖ := by
    have hn := norm_add_le ((deriv riemannZeta z / riemannZeta z) - S) S
    have hrewrite : (deriv riemannZeta z / riemannZeta z) - S + S = (deriv riemannZeta z / riemannZeta z) := by
      simp [sub_eq_add_neg]
    simpa [S, hrewrite] using hn
  have hsum := add_le_add_left hbound1 ‖S‖
  have : ‖deriv riemannZeta z / riemannZeta z‖ ≤ C1 * Real.log |t| + ‖S‖ := le_trans htri hsum
  simpa [S, add_comm] using this

lemma lem_sumK1abs (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
    (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := by
  intro c hfin hzcond
                                       
  have hptwise : ∀ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖ ≤
      (1 / (2 * deltaz_t t)) * ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    intro ρ hρmem
    have hρ_in : ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρmem
    have hbase : 1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) :=
      lem_1abszrho t ht z ρ hρ_in hzcond
    have hnonneg : 0 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le ((analyticOrderAt riemannZeta ρ).toNat))
    have := mul_le_mul_of_nonneg_left hbase hnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum hptwise
                                                                
  have hrw :=
    (Finset.mul_sum (s := hfin.toFinset)
      (f := fun ρ => ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
      (a := (1 / (2 * deltaz_t t))))
  have hsum2 := hsum
                                                        
  rw [← hrw] at hsum2
           
  simpa [div_eq_mul_inv] using hsum2

lemma helper_apply_jensen_to_g
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤ Real.log B / Real.log (R / R1) := by
  classical
                                                     
  have h_exists : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      ∃ hσ : ℂ → ℂ, AnalyticAt ℂ hσ σ ∧ hσ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * hσ z := by
    intro σ hσ
    exact lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 g h_g_analytic hg0_ne σ hσ
                                            
  let h_σ : ℂ → (ℂ → ℂ) :=
    fun σ => dite (σ ∈ zerosetKfR R1 (by linarith) g)
      (fun h => Classical.choose (h_exists σ h))
      (fun _ => fun _ => (1 : ℂ))
                                             
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      AnalyticAt ℂ (h_σ σ) σ ∧ (h_σ σ) σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * (h_σ σ) z := by
    intro σ hσin
    have hx := h_exists σ hσin
    dsimp [h_σ]
                                  
    simpa [hσin] using (Classical.choose_spec hx)
                                      
  have hbound :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1
      g h_g_analytic hg0_ne hg0_one hfin_g (h_σ := h_σ) hg_le_B h_σ_spec
                                         
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma helper_sum_f_equals_sum_g
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
  =
  (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
      ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) :=
by
  classical
             
  let S : Finset ℂ := hfin.toFinset
  let φ : ℂ → ℂ := fun ρ => ρ - c
  let g' : ℂ → ℂ := fun z => f (z + c) / f c

  have himg : (φ '' zerosetKfRc r c f).Finite := hfin.image φ
  have h_img_toFinset : ((hfin.image φ).toFinset) = S.image φ := by
    simpa [S] using (Set.Finite.toFinset_image (s := (zerosetKfRc r c f)) (f := φ)
      (hs := hfin) (h := himg))

  have h_orders_match :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρS
                                                                          
    have hρ_mem : ρ ∈ zerosetKfRc r c f :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρS
    have hρ_ball : ρ ∈ Metric.closedBall c r := hρ_mem.1
    have hρ_fzero : f ρ = 0 := hρ_mem.2
                                                                   
    have hρ'_ball : (φ ρ) ∈ Metric.closedBall (0 : ℂ) r := by
                     
      have hdist_le : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ_ball
                                               
      have : dist (φ ρ) 0 ≤ r := by
        simpa [φ, dist_eq_norm] using (by simpa [dist_eq_norm] using hdist_le)
      simpa [Metric.mem_closedBall] using this
    have hρ'_gzero : g' (φ ρ) = 0 := by
      simp [g', φ, hρ_fzero, sub_eq_add_neg, add_comm]
    have hρ'_mem : (φ ρ) ∈ zerosetKfRc r (0 : ℂ) g' := ⟨hρ'_ball, hρ'_gzero⟩
                                                
    have h_m_eq := fc_m_order r hr c f hc h_analytic (ρ' := φ ρ) hρ'_mem
                    
    have h_m_eq' : analyticOrderAt g' (φ ρ) = analyticOrderAt f ρ := by
      simpa [g', φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_m_eq
                                  
    have h_toNat : (analyticOrderAt g' (φ ρ)).toNat = (analyticOrderAt f ρ).toNat := by
      simpa using congrArg ENat.toNat h_m_eq'
    simp [h_toNat]

  have h_inj : Function.Injective φ := by
    intro x y hxy
                                                    
    have := congrArg (fun z => z + c) hxy
    simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have h_sum_image :
      (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    refine Finset.sum_image ?h
    intro x hx y hy hxy
                                
    exact h_inj hxy

  calc
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) := by rfl
    _ = (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := h_orders_match
    _ = (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) := h_sum_image.symm
    _ = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) := by
                                                     
          simp [S, φ, g', h_img_toFinset]

lemma helper_zero_set_shift_eq
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1)) :
  zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
  = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  simpa using fc_zeros r hr c f hc h_analytic

lemma helper_fin_zero_g_is_image
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  have hset : zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
      = (fun ρ => ρ - c) '' (zerosetKfRc r c f) :=
    by simpa using fc_zeros r hr c f hc h_analytic
  have hfin_img : ((fun ρ => ρ - c) '' (zerosetKfRc r c f)).Finite := hfin.image _
  simpa [hset] using hfin_img

lemma jensen_sum_bound_strict
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤
    Real.log B / Real.log (R / R1) := by
  exact helper_apply_jensen_to_g B R R1 hB hR1_pos hR1_lt_R hR_lt_1 g
    h_g_analytic hg0_ne hg0_one hfin_g hg_le_B

lemma lem_sum_m_rho_bound_c (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (hR_lt_1 : R < 1)
  (f : ℂ → ℂ)
  (c : ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
  (h_f_nonzero_at_zero : f c ≠ 0)
  (hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B)
  (hfin : (zerosetKfRc R1 c f).Finite) :
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
  classical
                                                   
  let g : ℂ → ℂ := fun z => f (z + c) / f c

  have h_g_analyticOn : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    helper_analyticOnNhd_shift_div f c h_f_analytic h_f_nonzero_at_zero
  have h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z :=
    helper_AnalyticOnNhd_to_pointwise h_g_analyticOn

  have hg0_one : g 0 = 1 := helper_g_zero_eq_one f c h_f_nonzero_at_zero
  have hg0_ne : g 0 ≠ 0 := by simp [hg0_one]

  have hAnal_f : AnalyticOnNhd ℂ f (Metric.closedBall c 1) :=
    helper_pointwise_to_AnalyticOnNhd h_f_analytic
  have hfin_g0 : (zerosetKfRc R1 (0 : ℂ) g).Finite :=
    helper_fin_zero_g_is_image R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f hfin
  have hZR_eq : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
    helper_zerosetKfR_eq_center0 R1 hR1_pos g
  have hfin_g : (zerosetKfR R1 (by exact hR1_pos) g).Finite := by
    simpa [hZR_eq] using hfin_g0

  have h_bound_shift : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_shifted B R hB (by exact lt_trans hR1_pos hR1_lt_R) hR_lt_1 c f
      h_f_nonzero_at_zero (fun z hz => hf_le_B z <| by simpa using hz)
  have hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_on_ball_to_norm_imp (R := R) (g := g) (M := B / ‖f c‖) h_bound_shift

  have hfc_le : ‖f c‖ ≤ B := by
    have : c ∈ Metric.closedBall c R := by
      have hRpos' : 0 ≤ R := le_of_lt (lt_trans hR1_pos hR1_lt_R)
      have : dist c c ≤ R := by simpa [dist_self] using hRpos'
      simpa [Metric.mem_closedBall] using this
    exact hf_le_B c this
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff).2 h_f_nonzero_at_zero
  have hBdiv_ge_one : 1 ≤ B / ‖f c‖ := by
    have hdiv := (div_le_div_iff_of_pos_right hfc_pos).mpr hfc_le
    simpa [div_self (ne_of_gt hfc_pos)] using hdiv

  have hsum_fg_eq :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt g ρ').toNat : ℝ)) :=
    helper_sum_f_equals_sum_g (r := R1) (hr := hR1_pos) (c := c)
      (f := f) (hc := h_f_nonzero_at_zero) (h_analytic := hAnal_f) (hfin := hfin)

  have hST_g_img : zerosetKfR R1 hR1_pos g
      = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) := by
    have h1 : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
      helper_zerosetKfR_eq_center0 R1 hR1_pos g
    have h2 : zerosetKfRc R1 (0 : ℂ) g
        = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
      helper_zero_set_shift_eq R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f
    simpa [h1] using h2

  rcases lt_or_eq_of_le hBdiv_ge_one with hBdiv_gt_one | hBdiv_eq_one
  ·                                                            
    have hsum_g_bound :=
      jensen_sum_bound_strict (B := B / ‖f c‖) (R := R) (R1 := R1)
        (hB := hBdiv_gt_one)
        (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
        (g := g) (h_g_analytic := h_g_analytic) (hg0_ne := hg0_ne)
        (hg0_one := hg0_one) (hfin_g := hfin_g) (hg_le_B := hg_le_B)
                                                                           
    have hsum_g_reindex :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
                                                                     
    have :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simpa [hsum_g_reindex] using hsum_g_bound
                                              
    simpa [hsum_fg_eq] using this
  ·                                                                                    
    have hBdiv_eq_one' : B / ‖f c‖ = 1 := by
      simpa [eq_comm] using hBdiv_eq_one
    have hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1 := by
      intro z hz
      have := hg_le_B z hz
      simpa [hBdiv_eq_one'] using this
    have g_nonzero_on_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 :=
      no_zero_of_bound_one_and_center_one R hR_lt_1 g h_g_analytic hg0_one hg_le_one
                                                                      
    have hS_empty : zerosetKfR R1 hR1_pos g = (∅ : Set ℂ) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzball, hzzero⟩
        have hzR1 : ‖z‖ ≤ R1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hzR : ‖z‖ ≤ R := le_trans hzR1 (le_of_lt hR1_lt_R)
        have hzR' : z ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
        exact (g_nonzero_on_ball z hzR') hzzero
      · intro hzfalse
        cases hzfalse
    have hsum_g_zero :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      have h :=
        helper_sum_over_equal_finite_sets_orders (g := g)
          (S := zerosetKfR R1 hR1_pos g) (T := (∅ : Set ℂ))
          (hS := hfin_g) (hT := Set.finite_empty) (hST := hS_empty)
      simpa using h
                                                                                         
    have hsum_reindex :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    have hsum_img_eq :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) := by
      simpa using hsum_reindex.symm
    have hsum_img_zero :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      simp [hsum_img_eq, hsum_g_zero]
                                                  
    have hsum_f_zero :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) = 0 := by
      simpa [hsum_img_zero] using hsum_fg_eq
                                                   
    have hRHS_zero : Real.log (B / ‖f c‖) / Real.log (R / R1) = 0 := by
      simp [hBdiv_eq_one']
                                      
    have :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simp [hsum_f_zero, hRHS_zero]
    exact this

lemma lem_sum_m_rho_zeta :
    ∃ C_2 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ C_2 * Real.log |t| := by
  classical
                                    
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
          
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
                                 
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := by
      have := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
      simp [C2]
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
                              
  have hR1_pos : 0 < R1 := by dsimp [R1] <;> norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R] <;> norm_num
  have hR_lt_1 : R < 1 := by dsimp [R] <;> norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R] <;> norm_num
                                                                                          
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    exact zetaanalOnnot1 z hz_ne_one
                      
  have h_nonzero : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
                                                          
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
                         
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := le_of_lt ht1
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
                                                                  
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hB := hBpos)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
                           
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1] <;> norm_num
    exact Real.log_pos this
                          
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using! ha_bound t

  have ht_abs_pos : 0 < |t| := lt_trans (by norm_num) ht
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
                                       
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      simpa [sub_eq_add_neg] using! add_le_add_right hneg (Real.log b + Real.log |t|)
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
                                
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
                                   
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                          
    have h3le : (3 : ℝ) ≤ |t| := le_of_lt ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := le_of_lt lem_three_gt_e
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by exact add_le_add_right haux1 _
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by exact add_le_add_right haux2 _
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
                              
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

lemma lem_sumKdeltatlogt :
  ∃ C_3 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t;
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      (C_3 / (deltaz_t t)) * Real.log |t| := by
                                        
  obtain ⟨C_2, hC_2_pos, hC_2_bound⟩ := lem_sum_m_rho_zeta

  use C_2

  constructor
  ·                                             
    exact hC_2_pos

  ·              
    intro t ht c hfin z hz

    have h1 := lem_sumK1abs t ht z hfin hz

    have h2 := hC_2_bound t ht hfin

    have ht2 : |t| > 2 := by linarith [ht]
    have h_delta_pos : 0 < deltaz_t t := (lem_delta19.2 t ht2).1

    have h_t_ge_one : (1 : ℝ) ≤ |t| := by linarith [ht]

    calc
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := h1
      _ ≤ (1 / (2 * deltaz_t t)) * (C_2 * Real.log |t|) := by
          apply mul_le_mul_of_nonneg_left h2
          apply div_nonneg (by norm_num)
          apply mul_nonneg (by norm_num) (le_of_lt h_delta_pos)
      _ = (C_2 / (2 * deltaz_t t)) * Real.log |t| := by ring
      _ ≤ (C_2 / deltaz_t t) * Real.log |t| := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg h_t_ge_one)
                                                           
          apply div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hC_2_pos))
          · exact h_delta_pos
          ·                                    
            calc deltaz_t t
              = 1 * deltaz_t t := by rw [one_mul]
            _ ≤ 2 * deltaz_t t := by
              apply mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt h_delta_pos)

lemma lem_sumKlogt2 :
  ∃ C_4 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      C_4 * Real.log |t|^2 := by
                                        
  obtain ⟨C_3, hC_3_gt, hC_3⟩ := lem_sumKdeltatlogt

  use max (100 * C_3 / zerofree_constant) 2

  constructor
  · exact lt_max_of_lt_right (by norm_num : (2 : ℝ) > 1)

  · intro t ht c hfin z hz
                                              
    have h_bound := hC_3 t ht hfin z hz

    have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
    have h_log_t_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
    have hC_3_pos : 0 < C_3 := lt_trans zero_lt_one hC_3_gt
    have h_zerofree_pos : 0 < zerofree_constant := zerofree_constant_pos

    have h_log_bound : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
      have h_ineq : |t| + 2 ≤ 2 * |t| := by linarith [ht]
      have h_log_ineq := Real.log_le_log (by linarith [abs_nonneg t] : 0 < |t| + 2) h_ineq
      rw [Real.log_mul (by norm_num) (ne_of_gt h_t_pos)] at h_log_ineq
      have h_log2_bound : Real.log 2 ≤ Real.log |t| :=
        Real.log_le_log (by norm_num) (by linarith [ht] : (2 : ℝ) ≤ |t|)
      linarith [h_log_ineq]

    have h_deltaz_eq : deltaz_t t = (zerofree_constant / 20) / Real.log (|t| + 2) := by
      simp [deltaz_t, deltaz]

    have h_main_bound : C_3 / deltaz_t t * Real.log |t| ≤
                        40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by
                                       
      rw [h_deltaz_eq]

      have h_div_rewrite : C_3 / ((zerofree_constant / 20) / Real.log (|t| + 2)) =
                          C_3 * Real.log (|t| + 2) * 20 / zerofree_constant := by
        field_simp [ne_of_gt h_zerofree_pos, ne_of_gt (Real.log_pos (by linarith [abs_nonneg t] : (1 : ℝ) < |t| + 2))]

      rw [h_div_rewrite]
                                                 
      have h_pos_factor : 0 ≤ C_3 * 20 / zerofree_constant :=
        div_nonneg (mul_nonneg (le_of_lt hC_3_pos) (by norm_num)) (le_of_lt h_zerofree_pos)

      calc C_3 * Real.log (|t| + 2) * 20 / zerofree_constant * Real.log |t|
          = C_3 * 20 / zerofree_constant * Real.log (|t| + 2) * Real.log |t| := by ring
      _ ≤ C_3 * 20 / zerofree_constant * (2 * Real.log |t|) * Real.log |t| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_log_bound h_pos_factor)
                (le_of_lt h_log_t_pos)
      _ = 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by simp [pow_two]; ring

    calc (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ C_3 / deltaz_t t * Real.log |t| := h_bound
    _ ≤ 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := h_main_bound
    _ ≤ max (100 * C_3 / zerofree_constant) 2 * (Real.log |t|)^2 := by
        have h_factor_bound : 40 * C_3 / zerofree_constant ≤ max (100 * C_3 / zerofree_constant) 2 := by
          have h_coeff_ineq : 40 * C_3 ≤ 100 * C_3 := by
                                                                                     
            have h_coeff : (40 : ℝ) ≤ 100 := by norm_num
            exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hC_3_pos)
          have h_div_ineq : 40 * C_3 / zerofree_constant ≤ 100 * C_3 / zerofree_constant := by
                                          
            exact div_le_div_of_nonneg_right h_coeff_ineq (le_of_lt h_zerofree_pos)
          exact le_trans h_div_ineq (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right h_factor_bound (sq_nonneg _)

lemma lem_logDerivZetalogt0 :
  ∃ C > 1,
  ∀ (t : ℝ) (_ht : |t| > 3),
    ∀ s : ℂ, (1 - deltaz_t t) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
                                                              
  obtain ⟨C_1, hC_1_gt, hC_1⟩ := lem_Zeta_Triangle_ZFR
  obtain ⟨C_4, hC_4_gt, hC_4⟩ := lem_sumKlogt2

  use C_1 + C_4

  constructor
  ·               
    linarith [hC_1_gt, hC_4_gt]

  ·              
    intro t ht s hs

    let c := (3/2 : ℂ) + I * t
    have hfin := lem_finiteKzeta t ht

    have h_triangle := hC_1 t ht hfin s hs

    have h_triangle_ineq := lem_triangle_ZFR t ht s hfin hs

    have h_sum_bound := hC_4 t ht hfin s hs

    have h_log_sq_ge : Real.log |t| ≤ Real.log |t|^2 := by
      have h_log_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                         
        have h_t_gt_e : Real.exp 1 < |t| := by
          have h_e_bound : Real.exp 1 < 3 := by
                                                          
            simpa using lem_three_gt_e
          linarith [ht]
                                                                  
        have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt h_t_gt_e)
      have h_log_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
      rw [pow_two]
      exact le_mul_of_one_le_right (le_of_lt h_log_pos) h_log_ge_one

    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖ + C_1 * Real.log |t| := h_triangle
      _ ≤ (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖s - ρ‖) + C_1 * Real.log |t| := by
          apply add_le_add_left h_triangle_ineq
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t| := by
          apply add_le_add_left h_sum_bound
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t|^2 := by
                                                    
          have h_c1_nonneg : 0 ≤ C_1 := le_of_lt (lt_trans zero_lt_one hC_1_gt)
          exact add_le_add_right (mul_le_mul_of_nonneg_left h_log_sq_ge h_c1_nonneg) _
      _ = (C_4 + C_1) * Real.log |t|^2 := by ring
      _ = (C_1 + C_4) * Real.log |t|^2 := by ring

lemma lem_logDerivZetalogt32 :
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C := by
                                                        
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
                                            
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro t ht σ hσ
                                                   
  have h_center := lem_zetacenterbd t σ hσ
                                  
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith [hσ]
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith [hσ]
                                                     
  have hZ0 := hC0_bound δ hδ_pos
                                                                                   
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
                                        
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
                                                          
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by
      simp
                                        
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
                                             
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
                                      
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by
      simp
    simpa [hnorm_div'] using this
                                                                                           
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ :=
      le_trans h_tri (add_le_add_left hZ0 _)
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 :=
      le_trans h1 (add_le_add_right h_norm_div_le_two _)
    simpa [norm_neg] using h2
                           
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_left_comm]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
                                                    
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
                                    
  exact le_trans h_center hR_bound

theorem thm_final_result :
  ∃ A : ℝ, A > 0 ∧ A < 1 ∧
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 1 - A / Real.log (abs t + 2) →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C * (Real.log (abs t)) ^ 2 := by
                                                                                          
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_logDerivZetalogt0
  obtain ⟨C₃₂, hC₃₂_pos, hC₃₂⟩ := lem_logDerivZetalogt32

  use zerofree_constant / 20

  constructor
  ·               
    apply div_pos zerofree_constant_pos
    norm_num

  constructor
  ·               
    rw [div_lt_one (by norm_num : (0 : ℝ) < 20)]
                                          
    have h1 : zerofree_constant < 1 := zerofree_constant_lt_one
    linarith

  use max C₀ C₃₂

  constructor
  ·               
    exact lt_max_of_lt_left hC₀_pos

  ·              
    intro t ht σ hσ

    have h_eq : zerofree_constant / 20 / Real.log (abs t + 2) = deltaz_t t := by
      unfold deltaz_t deltaz
      simp

    have hσ' : σ ≥ 1 - deltaz_t t := by
      rw [← h_eq]
      exact hσ

    by_cases h : σ ≥ 3/2
    ·                                            
      have bound := hC₃₂ t ht σ h
      have hC_le : C₃₂ ≤ max C₀ C₃₂ := le_max_right _ _
                                                      
      have hlog_ge_one : 1 ≤ Real.log (abs t) := by
        have h_ge : Real.exp 1 ≤ abs t := by
                                                     
          have he_lt_3 : Real.exp 1 < 3 := lem_three_gt_e                           
          linarith [ht, abs_nonneg t]
        exact (Real.le_log_iff_exp_le (by linarith [abs_nonneg t])).2 h_ge
      have h_one_le_sq : 1 ≤ (Real.log (abs t)) ^ 2 := by
        have h_sq : (Real.log (abs t)) ^ 2 = Real.log (abs t) * Real.log (abs t) := by
          rw [pow_two]
        rw [h_sq]
        have h_mul : 1 * 1 ≤ Real.log (abs t) * Real.log (abs t) :=
          mul_self_le_mul_self (zero_le_one) hlog_ge_one
        simpa using h_mul
      have h_pos : 0 < C₃₂ := lt_trans zero_lt_one hC₃₂_pos
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₃₂ := bound
        _ = C₃₂ * 1 := by rw [mul_one]
        _ ≤ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_one_le_sq (le_of_lt h_pos)
        _ ≤ max C₀ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

    ·                                           
      push Not at h
      have h_conditions : 1 - deltaz_t t ≤ σ ∧ σ ≤ 3/2 ∧ t = t := by
        exact ⟨hσ', le_of_lt h, rfl⟩
      have bound := hC₀ t ht ⟨σ, t⟩ h_conditions
      have hC_le : C₀ ≤ max C₀ C₃₂ := le_max_left _ _
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₀ * Real.log |t| ^ 2 := bound
        _ ≤ max C₀ C₃₂ * Real.log |t| ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
                                                                             
  obtain ⟨c, hc_pos, hc_lt_one, hbound⟩ := zerofree
                                               
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
                        
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
                                      
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
                                  
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
                          
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
                                   
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
                   
    have hlog_lt : Lp < 2 * L := by
      have h1 : 0 < |t| - 2 := by linarith
      have h2 : 0 < |t| + 1 := by linarith
      have hprod_pos : 0 < (|t| - 2) * (|t| + 1) := mul_pos h1 h2
      have hpoly : |t| * |t| - (|t| + 2) = (|t| - 2) * (|t| + 1) := by ring
      have hlt : |t| + 2 < |t| * |t| := by
        calc
          |t| + 2 < |t| + 2 + (|t| - 2) * (|t| + 1) := by linarith [hprod_pos]
          _ = |t| * |t| := by rw [← hpoly]; ring
      have hposb : 0 < |t| + 2 := by linarith
      have hlog_lt' : Real.log (|t| + 2) < Real.log (|t| * |t|) := Real.log_lt_log hposb hlt
      have hlogmul : Real.log (|t| ^ 2) = 2 * Real.log |t| := Real.log_pow |t| 2
      calc
        Lp = Real.log (|t| + 2) := by simp [hLpdef]
        _ < Real.log (|t| * |t|) := hlog_lt'
        _ = Real.log (|t| ^ 2) := by simp [pow_two]
        _ = 2 * Real.log |t| := by simp
        _ = 2 * L := by simp [hLdef]
                                               
    have h_inv_comp : 1 / (2 * L) < 1 / Lp := one_div_lt_one_div_of_lt hLp_pos hlog_lt
    have hstep2 : (c / 2) / L < c / Lp := by
      have hcpos' : 0 < c := hc_pos
      have : c * (1 / (2 * L)) < c * (1 / Lp) := mul_lt_mul_of_pos_left h_inv_comp hcpos'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
                                          
    have hstep1 : A / L ≤ (c / 2) / L := by
      have := div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
      simpa [div_eq_mul_inv] using this
    have hstrict_div : A / L < c / Lp := lt_of_le_of_lt hstep1 hstep2
                                                       
    have hσ_gt : 1 - c / Lp < σ := by
      have hneg' : - (c / Lp) < - (A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
      have : 1 - c / Lp < 1 - A / L := by simpa [sub_eq_add_neg] using! add_lt_add_right hneg' 1
      exact this.trans_le hlow
                                             
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hs_in_zeroZ : s ∈ zeroZ := by simpa [zeroZ] using hs_zero
    have hpre : s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1 := by
      refine ⟨hs_in_zeroZ, ?_, ?_⟩
      · simpa [s] using hσ_pos
      · simpa [s] using hσ_lt_one
    have him_bound : 2 < |s.im| := by
      have : 2 < |t| := lt_trans (by norm_num) htgt3
      simpa [s] using this
    have hbound_applied : s.re ≤ 1 - c / Real.log (abs s.im + 2) := hbound s hpre him_bound
    have hle : σ ≤ 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    have hcontr : σ < σ := lt_of_le_of_lt hle hσ_gt
    exact (lt_irrefl _ : ¬ σ < σ) hcontr

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real
lemma LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  classical
  obtain ⟨c, hc, hc2, K, hK, hfinal⟩ := thm_final_result
                     
  let A : ℝ := min (1/2 : ℝ) (c / 2)
  have hApos : 0 < A := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc this
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have hAle : A ≤ (1/2 : ℝ) := min_le_left _ _
  have hA_in : A ∈ Ioc 0 (1/2) := ⟨hApos, hAle⟩
  let C : ℝ := K
  have hCpos : 0 < C := by
    have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
    exact hKpos
  refine ⟨A, hA_in, C, hCpos, ?_⟩
  intro σ t htgt3 hσI
                      
  let x := |t|
  have hxpos : 0 ≤ x := abs_nonneg t
  have hxgt3 : 3 < x := htgt3
  let L := Real.log x
  let L' := Real.log (x + 2)
  have hLpos : 0 < L := (Real.log_pos_iff hxpos).2 (lt_trans (by norm_num) hxgt3)
  have hL'pos : 0 < L' :=
    (Real.log_pos_iff (by linarith : 0 ≤ x + 2)).2 (by linarith [hxpos, hxgt3])
                                             
  have hσ_ge : 1 - A / L ≤ σ := by simpa [pow_one, L, x] using hσI
                 
  have hprod_pos : 0 < (x - 2) * (x + 1) := by
    have hxgt2 : (2 : ℝ) < x := lt_trans (by norm_num) hxgt3
    exact mul_pos (sub_pos.mpr hxgt2) (add_pos_of_nonneg_of_pos hxpos (by norm_num))
  have hdiff_pos : 0 < x ^ 2 - (x + 2) := by
    have hpoly : x ^ 2 - (x + 2) = (x - 2) * (x + 1) := by ring
    simpa [hpoly] using hprod_pos
  have hlt_sq : x + 2 < x ^ 2 := by linarith
  have hlog_lt : L' < Real.log (x ^ 2) :=
    Real.log_lt_log (by linarith : 0 < x + 2) hlt_sq
  have hlog_pow : Real.log (x ^ 2) = 2 * L := by
    simp [L]
  have hL'_lt_2L : L' < 2 * L := by simpa [L', hlog_pow]
    using hlog_lt
                                       
  have hA_le_c2 : A ≤ c / 2 := min_le_right _ _
  have hstep0 : A / L ≤ (c / 2) / L :=
    div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
  have hrecip : 1 / (2 * L) < 1 / L' :=
    one_div_lt_one_div_of_lt hL'pos hL'_lt_2L
  have hmul : c * (1 / (2 * L)) < c * (1 / L') :=
    mul_lt_mul_of_pos_left hrecip hc
  have hstep2 : (c / 2) / L < c / L' := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hineq : A / L < c / L' := lt_of_le_of_lt hstep0 hstep2
  have hσ_gt : σ > 1 - c / L' := by
    have : 1 - c / L' < 1 - A / L := by linarith [hineq]
    exact lt_of_lt_of_le this hσ_ge
                                                 
  have hmain' : ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      K * (Real.log |t|) ^ 2 := by
    have h_eq : σ + t * Complex.I = Complex.mk σ t := by
      rw [Complex.mk_eq_add_mul_I]
    rw [h_eq]
    have hσ_ge_required : σ ≥ 1 - c / Real.log (abs t + 2) := by
      have h_abs_eq : abs t = |t| := by simp
      rw [h_abs_eq]
      exact le_of_lt hσ_gt
    exact hfinal t htgt3 σ hσ_ge_required
                                                  
  simpa [C, L, x] using hmain'

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ZetaZeroFree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox' 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp <;> ring

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT5_Strong
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

local notation "𝓜" => MellinTransform

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

local notation "ψ" => ChebyshevPsi

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    refine add_lt_add_of_le_of_lt ?_ ?_
    rfl
    rw[inv_pos, ← Real.log_one]
    apply Real.log_lt_log
    norm_num
    linarith
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    refine (add_lt_add_iff_left 1).mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    positivity
    have : rexp 1 < 3 := by exact lt_trans (Real.exp_one_lt_d9) (by norm_num)
    linarith
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  ·
    exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  ·
    have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by push_cast; rfl
    repeat rw[smul_eq_mul]
    unfold I₁
    rw[temp, mul_add, mul_add, add_assoc, sub_eq_add_neg]
    nth_rewrite 4 [add_assoc]
    nth_rewrite 3 [add_assoc]
    nth_rewrite 2 [add_assoc]
    rw[add_assoc, add_left_cancel_iff, add_assoc]
    nth_rewrite 7 [add_comm]
    rw[← add_assoc]
    unfold I₉
    rw[add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
      -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
      ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    rw[smul_eq_mul, temp, ← add_assoc, ← add_assoc]
    nth_rewrite 2 [div_mul_comm]
    rw[mul_one, ← neg_div, ← mul_neg]
    nth_rewrite 2 [← one_div_mul_eq_div]
    repeat rw[← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
      ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
      unfold fTempRR
      rw[temp]
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
      unfold fTempRR
      rw[Complex.ofReal_neg, neg_mul]
      rfl
    rw[this]
    have : ∫ (t : ℝ) in -T..T, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
      ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by rfl
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ + ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by rfl
    rw[this]
    repeat rw[← add_assoc]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
      -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
      I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -1 * RectangleIntegral fTempC ((1 : ℝ) + (Real.log X)⁻¹ + T * I) (σ₁ - T * I) := by
      unfold RectangleIntegral
      rw[HIntegral_symm, VIntegral_symm]
      nth_rewrite 2 [HIntegral_symm, VIntegral_symm]
      unfold HIntegral VIntegral
      repeat rw[smul_eq_mul]
      repeat rw[add_re]
      repeat rw[add_im]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[mul_re]
      repeat rw[mul_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      rw[I_re, I_im, mul_zero, zero_mul, mul_one]
      ring_nf
      unfold fTempC
      have : ∫ (y : ℝ) in -T..T, fTempRR (I * ↑y + ↑σ₁).re (I * ↑y + ↑σ₁).im =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by simp
      rw[this]
      have : ∫ (y : ℝ) in -T..T,
          fTempRR (I * ↑y + ↑(1 + (Real.log X)⁻¹)).re (I * ↑y + ↑(1 + (Real.log X)⁻¹)).im =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑T + ↑x).re (I * ↑T + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑(-T) + ↑x).re (I * ↑(-T) + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by simp
      rw[this]
      ring_nf
    rw[this, neg_one_mul, div_mul_comm, mul_one,
        ← add_right_inj
        (RectangleIntegral fTempC (1 + ↑(Real.log X)⁻¹ + ↑T * I) (↑σ₁ - ↑T * I) / (2 * ↑π * I)),
        ← add_assoc]
    simp only [ofReal_one, ofReal_inv, add_zero]
    rw[rectangleIntegral_symm]
    have : RectangleIntegral fTempC (↑σ₁ - ↑T * I) (1 + 1 / ↑(Real.log X) + ↑T * I) / (2 * ↑π * I) =
      RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
      unfold RectangleIntegral'
      rw [smul_eq_mul]
      simp only [one_div, ofReal_inv]
      ring

    simp only [one_div, ofReal_inv] at this
    rw [this]

    let holoMatch : ℂ → ℂ := fun z ↦
      (fTempC z - (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X) / (z - 1))
    have inv_log_X_pos: 0 < (Real.log X)⁻¹ := by
      rw[inv_pos, ← Real.log_one]
      apply Real.log_lt_log (by positivity) (by linarith)
    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      have : re 1 = 1 := by rfl
      rw[this]
      have : im 1 = 0 := by rfl
      rw[this]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[add_re]
      repeat rw[add_im]
      rw[mul_re, mul_im, I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have temp : 1 ∈ uIoo σ₁ (re 1 + (Real.log X)⁻¹) := by
        have : re 1 = 1 := by rfl
        rw[this]
        unfold uIoo
        have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
        rw[this]
        have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨σ₁_lt_one, (by linarith)⟩
      have : 0 ∈ uIoo (-T) (T + im 1) := by
        have : im 1 = 0 := by rfl
        rw[this, add_zero]
        unfold uIoo
        have : min (-T) T = -T := by exact min_eq_left (by linarith)
        rw[this]
        have : max (-T) T = T := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨(by linarith), (by linarith)⟩
      exact ⟨temp, this⟩
           
    have holoMatchHoloOn : HolomorphicOn holoMatch
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1}) := by
      unfold HolomorphicOn holoMatch
      refine DifferentiableOn.sub ?_ ?_
      · unfold fTempC fTempRR
        have : (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X (↑z.re + ↑z.im * I)) =
          (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X z) := by
          apply funext
          intro z
          have : (↑z.re + ↑z.im * I) = z := by exact re_add_im z
          rw[this]
        rw[this]
        refine DifferentiableOn.mul ?_ ?_
        · refine DifferentiableOn.mul ?_ ?_
          · have : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)) := by
              refine funext ?_
              intro x
              exact neg_div (ζ x) (ζ' x)
            rw[this]
            refine DifferentiableOn.neg ?_
            unfold DifferentiableOn
            intro x x_location
            unfold Rectangle at x_location
            rw[Set.mem_sdiff, Complex.mem_reProdIm, sub_re, add_re, sub_im, add_im, mul_re, mul_im,
              I_re, I_im, add_re, add_im] at x_location
            simp only [ofReal_re, mul_zero, ofReal_im, mul_one, sub_self, sub_zero, one_re,
              ofReal_inv, inv_re, normSq_ofReal, div_self_mul_self', add_zero, zero_sub, one_im,
              inv_im, neg_zero, zero_div, zero_add, mem_singleton_iff] at x_location

            obtain ⟨⟨xReIn, xImIn⟩, xOut⟩ := x_location
            unfold uIcc at xReIn xImIn
            have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
            rw[this] at xReIn
            have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
            rw[this] at xReIn
            have : min (-T) T = (-T) := by exact min_eq_left (by linarith)
            rw[this] at xImIn
            have : max (-T) T = T := by exact max_eq_right (by linarith)
            rw[this] at xImIn
            unfold HolomorphicOn DifferentiableOn at holoOn
            have temp : DifferentiableWithinAt ℂ (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) x := by
              have : x ∈ Icc σ₁ 2 ×ℂ Icc (-T) T \ {1} := by
                rw [Set.mem_sdiff, Complex.mem_reProdIm]
                have xReTemp : x.re ∈ Icc σ₁ 2 := by
                  have xReLb : σ₁ ≤ x.re := by exact xReIn.1
                  have xReUb : x.re ≤ 2 := by exact (lt_of_le_of_lt xReIn.2 X_eq_lt_two).le
                  exact ⟨xReLb, xReUb⟩
                have xImTemp : x.im ∈ Icc (-T) T := by exact ⟨xImIn.1, xImIn.2⟩
                exact ⟨⟨xReTemp, xImTemp⟩, xOut⟩
              exact holoOn x this

            have : ((↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) \ {1}) ⊆
              (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
              intro a a_location
              rw[Set.mem_sdiff, Complex.mem_reProdIm]
              rw[Set.mem_sdiff] at a_location
              obtain ⟨aIn, aOut⟩ := a_location
              unfold Rectangle uIcc at aIn
              rw[sub_re, add_re, add_re, sub_im, add_im, add_im, mul_re, mul_im, ofReal_re, ofReal_re, ofReal_re, ofReal_im, ofReal_im, ofReal_im, I_re, I_im] at aIn
              have : re 1 = 1 := by rfl
              rw[this] at aIn
              have : im 1 = 0 := by rfl
              rw[this] at aIn
              ring_nf at aIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by linarith
              rw[this] at aIn
              have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by linarith
              rw[this] at aIn
              have : min (-T) T = (-T) := by linarith
              rw[this] at aIn
              have : max (-T) T = T := by linarith
              rw[this] at aIn
              rw[Complex.mem_reProdIm] at aIn
              obtain ⟨aReIn, aImIn⟩ := aIn
              have aReInRedo : a.re ∈ Icc σ₁ 2 := by
                have : a.re ≤ 2 := by exact (lt_of_le_of_lt aReIn.2 X_eq_lt_two).le
                exact ⟨aReIn.1, this⟩
              exact ⟨⟨aReInRedo, aImIn⟩, aOut⟩
            exact DifferentiableWithinAt.mono temp this
          · unfold DifferentiableOn
            intro x x_location
            refine DifferentiableAt.differentiableWithinAt ?_
            have hε : ε ∈ Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
            have xRePos : 0 < x.re := by
              unfold Rectangle at x_location
              rw[Set.mem_sdiff, Complex.mem_reProdIm] at x_location
              obtain ⟨⟨xReIn, _⟩, _⟩ := x_location
              unfold uIcc at xReIn
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im] at xReIn
              repeat rw[ofReal_re] at xReIn
              repeat rw[ofReal_im] at xReIn
              ring_nf at xReIn
              have : re 1 = 1 := by rfl
              rw[this] at xReIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
              rw[this] at xReIn
              have : σ₁ ≤ x.re := by exact xReIn.1
              linarith
            exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one xRePos
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          unfold HPow.hPow instHPow
          simp only
          apply DifferentiableAt.const_cpow
          · exact differentiableAt_fun_id
          · left
            refine ne_zero_of_re_pos ?_
            simp only [ofReal_re]
            linarith
      · refine DifferentiableOn.mul ?_ ?_
        ·
          unfold DifferentiableOn
          intro x x_location
          rw[Set.mem_sdiff] at x_location
          obtain ⟨xInRect, xOut⟩ := x_location
          apply DifferentiableAt.differentiableWithinAt
          apply differentiableAt_const
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          apply DifferentiableAt.inv
          · fun_prop
          · intro h
            rw [sub_eq_zero] at h
            have := x_location.2
            simp only [mem_singleton_iff] at this
            exact this h

    have holoMatchBddAbove : BddAbove
        (norm ∘ holoMatch '' (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1})) := by
      let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
      let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      have bigO_holoMatch : holoMatch =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        unfold holoMatch fTempC fTempRR SmoothedChebyshevIntegrand
        simp only [re_add_im]
        have : (fun z ↦
            (-ζ' z / ζ z * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z -
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X / (z - 1))) =
            (fun z ↦ (f z * g z - 1 * g 1 / (z - 1))) := by
          apply funext
          intro x
          simp[f, g]
          rw[mul_assoc]
        rw[this]
        have g_holc : HolomorphicOn g U := by
          unfold HolomorphicOn DifferentiableOn
          intro u uInU
          refine DifferentiableAt.differentiableWithinAt ?_
          simp[g]
          refine DifferentiableAt.mul ?_ ?_
          have hε : ε ∈ Set.Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
          have hu : 0 < u.re := by
            simp[U] at uInU
            unfold Rectangle uIcc at uInU
            rw[Complex.mem_reProdIm] at uInU
            obtain ⟨uReIn, uImIn⟩ := uInU
            have : min (↑σ₁ - ↑T * I).re (1 + (↑(Real.log X))⁻¹ + ↑T * I).re = σ₁ := by
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im]
              repeat rw[ofReal_re]
              repeat rw[ofReal_im]
              simp
              linarith
            rw[this] at uReIn
            have : σ₁ ≤ u.re := by exact uReIn.1
            linarith
          exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one hu
          unfold HPow.hPow instHPow
          simp
          apply DifferentiableAt.const_cpow
          exact differentiableAt_fun_id
          refine Or.inl ?_
          refine ne_zero_of_re_pos ?_
          rw[ofReal_re]
          positivity
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
          simp[f]
          have : ((fun z ↦ -ζ' z / ζ z) - fun z ↦ (z - 1)⁻¹) =
            (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
            apply funext
            intro z
            simp
          rw[this]
          exact riemannZetaLogDerivResidueBigO
        exact ResidueMult g_holc U_in_nhds f_near_p
      have : ∃ V ∈ nhds 1, BddAbove (norm ∘ holoMatch '' (V \ {1})) := by exact IsBigO_to_BddAbove bigO_holoMatch
      obtain ⟨V, VInNhds_one, BddAboveV⟩ := this
      have : ∃ W ⊆ V, 1 ∈ W ∧ IsOpen W ∧ BddAbove (norm ∘ holoMatch '' (W \ {1})) := by
        rw[mem_nhds_iff] at VInNhds_one
        obtain ⟨W, WSubset, WOpen, one_in_W⟩ := VInNhds_one
        use W
        have : BddAbove (Norm.norm ∘ holoMatch '' (W \ {1})) := by
          have : Norm.norm ∘ holoMatch '' (W \ {1}) ⊆
            Norm.norm ∘ holoMatch '' (V \ {1}) := by
            exact image_mono (by exact sdiff_subset_sdiff_left WSubset)
          exact BddAbove.mono this BddAboveV
        exact ⟨WSubset, ⟨one_in_W, WOpen, this⟩⟩
      obtain ⟨W, WSubset, one_in_W, OpenW, BddAboveW⟩ := this
      have : (↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) = U := by rfl
      rw[this] at holoMatchHoloOn ⊢
      have one_in_U : 1 ∈ U := by
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        exact mem_of_mem_nhds U_in_nhds
      have (h1 : 1 ∈ U) (h2 : 1 ∈ W) : U \ {1} = (U \ W) ∪ ((U ∩ W) \ {1}) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff]
        constructor
        intro ⟨hxU, hx1⟩
        by_cases hw : x ∈ W
        · right
          exact ⟨⟨hxU, hw⟩, hx1⟩
        · left
          exact ⟨hxU, hw⟩
        · intro h
          cases' h with h_left h_right
          have : x ≠ 1 := by
            intro x_eq_1
            rw[x_eq_1] at h_left
            exact h_left.2 h2
          · exact ⟨h_left.1, this⟩
          · exact ⟨h_right.1.1, h_right.2⟩
      rw[this one_in_U one_in_W]
      have : Norm.norm ∘ holoMatch '' (U \ W ∪ (U ∩ W) \ {1}) =
        Norm.norm ∘ holoMatch '' (U \ W) ∪ Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) := by
        exact image_union (Norm.norm ∘ holoMatch) (U \ W) ((U ∩ W) \ {1})
      rw[this]
      refine BddAbove.union ?_ ?_
      refine IsCompact.bddAbove_image ?_ ?_
      refine IsCompact.diff ?_ ?_
      unfold U Rectangle
      apply IsCompact.reProdIm
      unfold uIcc
      exact isCompact_Icc
      unfold uIcc
      exact isCompact_Icc
      exact OpenW
      refine Continuous.comp_continuousOn ?_ ?_
      exact continuous_norm
      have : HolomorphicOn holoMatch (U \ W) := by
        have : U \ W ⊆ U \ {1} := by
          intro x x_location
          obtain ⟨xInU, xOutW⟩ := x_location
          rw[Set.mem_sdiff]
          apply And.intro
          exact xInU
          rw[Set.mem_singleton_iff]
          intro x_eq_1
          rw[x_eq_1] at xOutW
          exact xOutW one_in_W
        exact DifferentiableOn.mono holoMatchHoloOn this
      unfold HolomorphicOn at this
      exact DifferentiableOn.continuousOn this
      have : Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) ⊆
        Norm.norm ∘ holoMatch '' (W \ {1}) := by
        have : (U ∩ W) \ {1} ⊆ W \ {1} := by
          intro x x_location
          rw[Set.mem_sdiff] at x_location
          obtain ⟨⟨xInU, xInW⟩, xOut⟩ := x_location
          exact ⟨xInW, xOut⟩
        exact image_mono this
      exact BddAbove.mono this BddAboveW

    obtain ⟨g, gHolo_Eq⟩ := existsDifferentiableOn_of_bddAbove
      pInRectangleInterior holoMatchHoloOn holoMatchBddAbove
    obtain ⟨gHolo, gEq⟩ := gHolo_Eq

    have zRe_le_wRe : (σ₁ - ↑T * I).re ≤ (1 + (Real.log X)⁻¹ + T * I).re := by
      repeat rw[sub_re]
      repeat rw[add_re]
      repeat rw[mul_re]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : re 1 = 1 := by rfl
      rw[this]
      linarith
    have zIm_le_wIm : (σ₁ - ↑T * I).im ≤ (1 + (Real.log X)⁻¹ + T * I).im := by
      repeat rw[sub_im]
      repeat rw[add_im]
      repeat rw[mul_im]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : im 1 = 0 := by rfl
      rw[this]
      linarith
    have hres := ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm
      pInRectangleInterior gHolo gEq
    simp only [ofReal_inv] at hres
    rw [← hres]
    unfold RectangleIntegral'
    simp only [smul_eq_mul]
    ring

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith

  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
                                         
    intro x hx
    constructor
    .                                       
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
                                                      
      have hzw_re : z.re < w.re := by
        simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
        linarith
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simp only [z, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, mul_one] at h_left
          linarith
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        exact ⟨h_left', h_right'⟩
                                                           
      have hzw_im : z.im < w.im := by
        simp only [z, w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, sub_im, mul_im, mul_one, zero_sub]
        linarith
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simp only [z, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, sub_im, mul_im, mul_one, zero_sub] at h_left
          linarith
        have h_right' : x.im ≤ 3 := by
          simp only [w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, mul_im, mul_one] at h_right
          linarith
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
                                       
    . simp only [mem_singleton_iff]
                                    
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
                                                
        have hzw_re : z.re < w.re := by
          simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := by exact x_re_bounds.2
        simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one] at x_re_upper'
        linarith
                          
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF  ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using! realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        ·                        
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ - ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
                                                                                                                               
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by

  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd2⟩ := LogDerivZetaBndUnif2
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT'
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  ·                                                                                  
    intro σ t ht hσ
    have hσ' : σ ∈ Ici (1 - A₁ / Real.log |t| ^ 1) := by

      have hAle : min A₁ A₂ ≤ A₁ := min_le_left _ _
      have hlogpos : 0 < Real.log |t| := by
                               
        exact Real.log_pos (lt_trans (by norm_num) ht)
      have := sub_le_sub_left
        (div_le_div_of_nonneg_right (show min A₁ A₂ ≤ A₁ from hAle) (le_of_lt hlogpos)) 1
                                     
      have hthr : 1 - A₁ / Real.log |t| ^ 1 ≤ 1 - (min A₁ A₂) / Real.log |t| ^ 1 := by
        simpa [pow_one] using this
                                           
      have : σ ∈ Ici (1 - (min A₁ A₂) / Real.log |t| ^ 1) := by
        simpa [pow_one] using hσ
      exact le_trans hthr (mem_Ici.mp this)
                                                                           
    have hmain := zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
    have hlog_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                              
      have hpos : 0 < |t| := lt_trans (by norm_num) ht
      have hle : Real.exp 1 ≤ |t| := by
        have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        exact this.trans (le_of_lt ht)
      have := Real.log_le_log (Real.exp_pos 1) hle
      simpa [Real.log_exp] using this
    have hpow : Real.log |t| ^ (2 : ℕ) ≤ Real.log |t| ^ (9 : ℕ) := by
      exact pow_le_pow_right₀ hlog_ge_one (by decide : (2 : ℕ) ≤ 9)
                                   
    have : C * Real.log |t| ^ (2 : ℕ) ≤ C * Real.log |t| ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt C_pos)
    exact (le_trans hmain this)
  ·                                                                    
    intro T hT
                                                                           
    have hsubset :
        ((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) ⊆
        ((Icc ((1 : ℝ) - A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) := by
      intro s hs
      rcases hs with ⟨hs_box, hs_ne⟩
      rcases hs_box with ⟨hre, him⟩
      rcases hre with ⟨hre_left, hre_right⟩
                                     
      constructor
      ·                                                     
        constructor
        ·                                              
          constructor
          ·                                  
            have hAle : min A₁ A₂ ≤ A₂ := min_le_right _ _
            have hlogpos : 0 < Real.log T := by
              have hT' : 1 < T := by linarith
              exact Real.log_pos hT'
            have := sub_le_sub_left
              (div_le_div_of_nonneg_right hAle (le_of_lt hlogpos)) 1
            have hthr : 1 - A₂ / Real.log T ^ 1 ≤ 1 - (min A₁ A₂) / Real.log T ^ 1 := by
              simpa [pow_one] using this
            exact le_trans hthr hre_left
          · exact hre_right
        · exact him
      · exact hs_ne
    exact (holo T hT).mono hsubset

open _root_.Filter Topology

theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  clear ContDiffν ν_nonneg'  ν_massOne'
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by
    apply holo2'.mono
    intro s hs
    simp [mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    rcases hs.1.1 with ⟨left, right⟩
    constructor
    · apply le_trans _ left
      apply min_le_min_right
      apply le_max_left
    · rw [max_eq_right (by linarith)] at right ⊢
      exact right

  clear holo2' σ₂'_lt_one

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  ⟨σ₂_pos, σ₂_lt_one⟩
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / 2) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / 2) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 2)
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 2)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 2)))

  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg)]
    rw [zero_rpow (ne_of_lt B_minus_1_neg)]
    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop

  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have B_minus_1_neg : B - 1 < 0 := by linarith
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (preTransparency := .instances) (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring

    have eventually_pos : ∀ᶠ x in atTop, 0 < 1 - c * Real.log x ^ (B - 1) := by
      apply (tendsto_order.mp coeff_to_one).1
      norm_num

    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx

    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one

  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf

  have x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
    rw [tendsto_congr' (x_εx_eq c B)]
    exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x : ℝ) : -c_εx * Real.log x ^ ((1 : ℝ) / 2) = -(c_εx * Real.log x ^ ((1 : ℝ) / 2)) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    apply (tendsto_rpow_atTop (by norm_num)).comp
    exact tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx (by norm_num : (1 : ℝ) / 2 < 1)
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) := by
                                      
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (preTransparency := .instances) (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp [Function.comp, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 100] with x hx x_gt
        convert (preTransparency := .instances) hx using 1
        · rw [Real.norm_of_nonneg]
          apply Real.log_nonneg
          have : (1 : ℝ) = Real.log (rexp 1) := by
            exact Eq.symm (Real.log_exp 1)

          rw [this]
          apply Real.log_le_log
          · exact Real.exp_pos _
          · have := Real.exp_one_lt_d9
                       
            linarith
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this]
      rw [mul_assoc]
      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx
    have : 0 < (A ^ ((1 : ℝ) / 2) / 4) := by
        positivity
    have const1bnd : (A ^ ((1 : ℝ) / 2) / 4) < (A ^ ((1 : ℝ) / 2) / 2) := by
        linarith
    have const2bnd : (0 : ℝ) < 1 / 2 := by norm_num
    have this (x : ℝ) :
      C' * rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / 2
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have : 0 < A ^ const2 := by
      unfold const2
                                           
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1
    have this (x : ℝ) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / 2)
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (1 : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul]
    rw [Real.log_exp]
    rw [Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (1 : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le]
        rw [div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos]
        rw [(by linarith : 1 + -(const2 * 1) = const2)]
      rw [div_mul_eq_div_div]
      rw [neg_div]
      rw [this (A_in_Ioc.1)]

      rw [mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div]

      rw [this (y := Real.log x) logxpos]

      rw [← Real.exp_add]
      apply Real.exp_monotone

      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]

      gcongr

      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      rw [←Real.sqrt_eq_rpow]
      apply Real.sqrt_nonneg

    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / 2
    have const2eq : const2 = 1 / 2 := by rfl
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    have const1eq : const1 = (A ^ const2 / 2) := by rfl
    set const1' := (A ^ const2 / 4)
    have const1'eq : const1' = (A ^ const2 / 4) := by rfl
    have A_pow_pos : 0 < A ^ const2 := by
      unfold const2
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1

    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]

    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt

    have this (x : ℝ) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    rw [rpow_one] at x_bnd
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    rw [← sub_nonneg]
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [this]
    convert (preTransparency := .instances) hx using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
    congr! 1
    have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
        = const2 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / 2) / 4) * Real.log x ^ ((1 : ℝ) / 2)) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂_lt_one (A ^ ((1 : ℝ) / 2) / 2)
      (A ^ ((1 : ℝ) / 2) / 4) (by norm_num : (1 : ℝ) / 2 < 1)] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert (preTransparency := .instances) hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert (preTransparency := .instances) hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf

    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T)
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) >= 1 - (1/2) / 1 := by
      gcongr
      · exact A_in_Ioc.2
      · apply (Real.le_log_iff_exp_le (by positivity)).mpr
        linarith[Real.exp_one_lt_d9]
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo1_compat : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
                                          
    simpa [σ₁, pow_one] using! holo1

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 ((Smooth1 ν ε) ·) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1_compat ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1_compat holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    exact (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)

  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 ((Smooth1 ν ε) ·) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T) / ε
                    + c₄ * X * X ^ (-A / Real.log T) / ε
                    + c₆ * X * X ^ (-A / Real.log T) / ε
                    + c₇ * X * X ^ (-A / Real.log T) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! (preTransparency := .instances) h_close using 1
      all_goals try with_reducible_and_instances rfl
      rw [← norm_neg]
      congr
      ring

      change ‖I₂ ν ε (Tx X) X σ₁‖ ≤ c₂ * X / (ε * (Tx X))
      dsimp at hc₂
      dsimp [σ₁]
                                                    
      unfold sigma1Of at hc₂

      exact hc₂

    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem psi_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, h⟩ := _root_.Erdos970.Strong_PNT
  refine ⟨c, hc, h.congr' ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Pi.sub_apply, id_eq, psi_eq_original hx]
  · filter_upwards [] with x
    simp only [errorScale, Real.sqrt_eq_rpow]

theorem theta_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, hpsi⟩ := psi_strong
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans (sqrt_isBigO_errorScale hc)
  refine ⟨c, hc, (hpsi.sub hdiff).congr_left ?_⟩
  intro x
  simp only [Pi.sub_apply]
  ring

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter _root_.Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel

theorem uniform_prime_interval_error : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧
    1 < a₀ ∧ 1 ≤ Real.log a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b →
      |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  obtain ⟨c, hc, hstrong⟩ := theta_strong
  obtain ⟨K, hK, hbound⟩ := hstrong.exists_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hbound.bound
  let a₀ := max x₀ (Real.exp 1)
  have ha₀ : 1 < a₀ := by
    have he : 1 < Real.exp 1 := by linarith [Real.exp_one_gt_two]
    exact lt_of_lt_of_le he (le_max_right x₀ (Real.exp 1))
  have hlog₀ : 1 ≤ Real.log a₀ := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right x₀ (Real.exp 1))
    simpa only [Real.log_exp] using h
  refine ⟨c, 2 * K + 4 * K / c, a₀, hc, by positivity, ha₀, hlog₀, ?_⟩
  intro a b haa hab
  have ha : 1 < a := lt_of_lt_of_le ha₀ haa
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hla : 1 ≤ Real.log a := le_trans hlog₀ (Real.log_le_log (lt_trans zero_lt_one ha₀) haa)
  have hlb : 1 ≤ Real.log b := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) hab)
  have hθ : ∀ t, a₀ ≤ t → |Chebyshev.theta t - t| ≤ K * errorScale c t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (lt_trans zero_lt_one ha₀) ht)
    have h := hx₀ t (le_trans (le_max_left _ _) ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (errorScale_nonneg c ht0)] using h
  rw [← integral_invLogWeight ha hab, error_identity ha hab]
  calc
    _ ≤ |invLogWeight b * (Chebyshev.theta b - b)| + |invLogWeight a * (Chebyshev.theta a - a)| +
        |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K * decay c a + K * decay c a + (4 * K / c) * decay c a := by
      apply add_le_add
      · apply add_le_add
        · exact (endpoint_error_bound hK.le hb hlb (hθ b (le_trans haa hab))).trans
            (mul_le_mul_of_nonneg_left (decay_antitone hc.le (lt_trans zero_lt_one ha) hab) hK.le)
        · exact endpoint_error_bound hK.le ha hla (hθ a haa)
      · exact integral_error_bound hc hK.le ha hla hab (fun t ht => hθ t (le_trans haa ht.1))
    _ = _ := by ring

end ErdosPrimeInputs.PrimeErrorDecay



namespace ErdosPrimeInputs.HarmonicPrimeMeasure

open _root_.Filter _root_.Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay

theorem uniform_all_endpoints : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b → ∀ lc rc : Bool,
      |intervalSum lc rc a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  obtain ⟨c, C, a₀, hc, hC, ha₀, hlog₀, h⟩ := uniform_prime_interval_error
  obtain ⟨A, hA⟩ := eventually_atTop.mp (reciprocal_le_decay hc)
  refine ⟨c, C + 2, max a₀ A, hc, by positivity, lt_of_lt_of_le ha₀ (le_max_left _ _), ?_⟩
  intro a b haa hab lc rc
  have ha : 1 < a := lt_of_lt_of_le ha₀ (le_trans (le_max_left _ _) haa)
  have herr := h a b (le_trans (le_max_left _ _) haa) hab
  have hend := endpoint_difference (lt_trans zero_lt_one ha) hab lc rc
  have hinv := hA a (le_trans (le_max_right _ _) haa)
  calc
    _ ≤ |intervalSum lc rc a b - reciprocalPrimes a b| +
        |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| := abs_sub_le _ _ _
    _ ≤ 2 / a + C * decay c a := add_le_add hend herr
    _ ≤ 2 * decay c a + C * decay c a := add_le_add (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

theorem harmonic_prime_measure : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ v → ∀ lc rc : Bool,
      |harmonicMass w lc rc u v - (Real.log v - Real.log u)| ≤
        C * Real.exp (-c * Real.sqrt (u * Real.log w)) := by
  obtain ⟨c, C, a₀, hc, hC, ha₀, h⟩ := uniform_all_endpoints
  refine ⟨c, C, max 2 (a₀ ^ 2), hc, hC, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro w hw u v hu huv lc rc
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_trans (le_max_left _ _) hw)
  have hw0 : 0 < w := lt_trans zero_lt_one hw1
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hu
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hsqrt : a₀ ≤ Real.sqrt w := by
    have hs2 := Real.sq_sqrt hw0.le
    have hs0 := Real.sqrt_nonneg w
    have haw : a₀ ^ 2 ≤ w := le_trans (le_max_right _ _) hw
    nlinarith
  have hau : a₀ ≤ w ^ u := le_trans hsqrt (by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hw1.le hu)
  have huvpow : w ^ u ≤ w ^ v := Real.rpow_le_rpow_of_exponent_le hw1.le huv
  have hmain : Real.log (Real.log (w ^ v)) - Real.log (Real.log (w ^ u)) =
      Real.log v - Real.log u := by
    rw [Real.log_rpow hw0, Real.log_rpow hw0,
      Real.log_mul (ne_of_gt hv0) (ne_of_gt hlogw), Real.log_mul (ne_of_gt hu0) (ne_of_gt hlogw)]
    ring
  have hp := h (w ^ u) (w ^ v) hau huvpow lc rc
  rw [hmain] at hp
  rw [harmonicMass_eq_intervalSum hw1]
  simpa only [decay, Real.log_rpow hw0] using hp

end ErdosPrimeInputs.HarmonicPrimeMeasure



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairedHitting
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem pairedRegeneration_measurable : MeasurableSet pairedRegeneration :=
  measurableSet_le measurable_subtype_coe measurable_const

noncomputable def pairedKilled : Kernel OddState OddState :=
  pairedOdd.restrict pairedRegeneration_measurable.compl

theorem paired_survival_balance (n : ℕ) (s : OddState) :
    (pairedKilled ^ n) s univ + hitBy n s = 1 := by
  induction n generalizing s with
  | zero =>
    change (Measure.dirac s) univ + 0 = 1
    simp
  | succ n ih =>
    have hp : pairedKilled ^ (n + 1) = (pairedKilled ^ n) ∘ₖ pairedKilled := pow_succ pairedKilled n
    rw [hp, Kernel.comp_apply' _ _ _ MeasurableSet.univ, pairedKilled, Kernel.restrict_apply]
    rw [← lintegral_indicator pairedRegeneration_measurable.compl]
    change (∫⁻ t, pairedRegenerationᶜ.indicator (fun t => (pairedKilled ^ n) t univ) t ∂pairedOdd s) +
      (∫⁻ t, if t.1 ≤ 3 then 1 else hitBy n t ∂pairedOdd s) = 1
    rw [← lintegral_add_left ((Kernel.measurable_coe (pairedKilled ^ n) MeasurableSet.univ).indicator
      pairedRegeneration_measurable.compl)]
    have heq : ∀ t : OddState, pairedRegenerationᶜ.indicator (fun t => (pairedKilled ^ n) t univ) t +
        (if t.1 ≤ 3 then 1 else hitBy n t) = 1 := by
      intro t
      by_cases ht : t.1 ≤ 3
      · rw [ite_eq_left ht, indicator_of_notMem (show t ∉ pairedRegenerationᶜ from not_not_intro ht), zero_add]
      · rw [ite_eq_right ht, indicator_of_mem (show t ∈ pairedRegenerationᶜ from ht)]
        exact ih t
    rw [lintegral_congr heq]
    simp

theorem paired_survival_le_one (n : ℕ) (s : OddState) : (pairedKilled ^ n) s univ ≤ 1 := by
  calc
    _ ≤ (pairedKilled ^ n) s univ + hitBy n s := le_add_of_nonneg_right zero_le
    _ = 1 := paired_survival_balance n s

theorem paired_survival_antitone (s : OddState) : Antitone (fun n => (pairedKilled ^ n) s univ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : pairedKilled ^ (n + 1) = pairedKilled ∘ₖ (pairedKilled ^ n) := pow_succ' pairedKilled n
  rw [hp, Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ _t, (1 : ℝ≥0∞) ∂(pairedKilled ^ n) s := lintegral_mono (fun t => by
      simpa only [pow_one] using paired_survival_le_one 1 t)
    _ = _ := by simp

theorem compact_paired_survival {M : ℝ} (hM : 4 ≤ M) : ∃ n : ℕ, 0 < n ∧ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
    ∀ m : ℕ, n ≤ m → ∀ s : OddState, s.1 ≤ M →
      (pairedKilled ^ m) s univ ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨n, hn, p, hp, hp1, hh⟩ := compact_paired_hit hM
  refine ⟨n, hn, p, hp, hp1, ?_⟩
  intro m hnm s hs
  have hsum : ENNReal.ofReal p + (pairedKilled ^ n) s univ ≤ 1 := by
    calc
      _ ≤ hitBy n s + (pairedKilled ^ n) s univ := add_le_add (hh s hs) le_rfl
      _ = 1 := by rw [add_comm]; exact paired_survival_balance n s
  have hQ := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hsum
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp.le] at hQ
  exact le_trans (paired_survival_antitone s hnm) hQ

end NumberTheoryLean.PairedHitting

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PairedDrift
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem pairedKilled_drift : ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 < C ∧ ∀ s : OddState,
    (∫⁻ t, ENNReal.ofReal (V t) ∂pairedKilled s) ≤ ENNReal.ofReal a * ENNReal.ofReal (V s) + ENNReal.ofReal C := by
  obtain ⟨a, C, ha, ha1, hC, hb⟩ := paired_drift
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  intro s
  rw [pairedKilled, Kernel.lintegral_restrict]
  exact le_trans (setLIntegral_le_lintegral _ _) (hb s)

theorem pairedKilled_iterated_drift : ∃ a B : ℝ, 0 < a ∧ a < 1 ∧ 0 < B ∧
    ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) ≤
        ENNReal.ofReal (a ^ n * V s + B) := by
  obtain ⟨a, C, ha, ha1, hC, hOne⟩ := pairedKilled_drift
  let B := C / (1 - a)
  have hB : 0 < B := div_pos hC (by linarith)
  have hBE : a * B + C = B := by dsimp [B]; field_simp [show 1 - a ≠ 0 by linarith] <;> ring
  have hEE : ENNReal.ofReal a * ENNReal.ofReal B + ENNReal.ofReal C = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_add (mul_pos ha hB).le hC.le, hBE]
  have hV : Measurable (fun s : OddState => ENNReal.ofReal (V s)) := ENNReal.measurable_ofReal.comp V_measurable
  have hIter : ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) ≤
        (ENNReal.ofReal a) ^ n * ENNReal.ofReal (V s) + ENNReal.ofReal B := by
    intro n
    induction n with
    | zero =>
      intro s
      change (∫⁻ t, ENNReal.ofReal (V t) ∂Measure.dirac s) ≤ _
      rw [lintegral_dirac' s hV]
      simp only [pow_zero, one_mul]
      exact le_add_of_nonneg_right zero_le
    | succ n ih =>
      intro s
      have hp : pairedKilled ^ (n + 1) = pairedKilled ∘ₖ (pairedKilled ^ n) := pow_succ' pairedKilled n
      rw [hp, Kernel.lintegral_comp _ _ _ hV]
      calc
        _ ≤ ∫⁻ t, ENNReal.ofReal a * ENNReal.ofReal (V t) + ENNReal.ofReal C ∂(pairedKilled ^ n) s :=
          lintegral_mono hOne
        _ = ENNReal.ofReal a * (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) +
            ENNReal.ofReal C * (pairedKilled ^ n) s univ := by
          rw [lintegral_add_left (f := fun t : OddState => ENNReal.ofReal a * ENNReal.ofReal (V t)) (measurable_const.mul hV) (fun _ => ENNReal.ofReal C), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const]
        _ ≤ ENNReal.ofReal a * ((ENNReal.ofReal a) ^ n * ENNReal.ofReal (V s) + ENNReal.ofReal B) + ENNReal.ofReal C := by
          apply add_le_add
          · exact mul_le_mul le_rfl (ih s) zero_le zero_le
          · simpa only [mul_one] using mul_le_mul (le_refl (ENNReal.ofReal C)) (paired_survival_le_one n s) zero_le zero_le
        _ = _ := by rw [mul_add, add_assoc, hEE, pow_succ]; ring
  refine ⟨a, B, ha, ha1, hB, ?_⟩
  intro n s
  rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg ha.le _) (V_pos s).le) hB.le,
    ENNReal.ofReal_mul (pow_nonneg ha.le _), ENNReal.ofReal_pow ha.le]
  exact hIter n s

end NumberTheoryLean.PairedDrift

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairedBlockContraction
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedBlockContraction

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels PairedHitting PairedDrift

theorem moment_add_constant (n : ℕ) (s : OddState) {D : ℝ} (hD : 0 ≤ D) :
    (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ n) s) =
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) +
        ENNReal.ofReal D * (pairedKilled ^ n) s univ := by
  have heq : ∀ t : OddState, ENNReal.ofReal (V t + D) = ENNReal.ofReal (V t) + ENNReal.ofReal D :=
    fun t => ENNReal.ofReal_add (V_pos t).le hD
  rw [lintegral_congr heq, lintegral_add_left (f := fun t : OddState => ENNReal.ofReal (V t)) (ENNReal.measurable_ofReal.comp V_measurable) (fun _ => ENNReal.ofReal D), lintegral_const]

theorem actual_block_contraction : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ,
    0 < ρ ∧ ρ < 1 ∧ 0 < D ∧ ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ m) s) ≤
        ENNReal.ofReal (ρ * (V s + D)) := by
  obtain ⟨a, B, ha, ha1, hB, hDrift⟩ := pairedKilled_iterated_drift
  let M := max 4 (8 * B)
  have hM : 4 ≤ M := le_max_left _ _
  obtain ⟨m0, hm0, p, hp, hp1, hHit⟩ := compact_paired_survival hM
  have hpow : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1
  have hsmall : ∀ᶠ n in atTop, a ^ n < 1 / 4 := (tendsto_order.mp hpow).2 _ (by norm_num)
  obtain ⟨m, hma, hm⟩ := (hsmall.and (eventually_ge_atTop m0)).exists
  let D := 2 * B / p
  let ρ := 1 - p / 2
  have hD : 0 < D := div_pos (by linarith) hp
  have hρ : 0 < ρ := by dsimp [ρ] <;> linarith
  have hρ1 : ρ < 1 := by dsimp [ρ] <;> linarith
  refine ⟨m, lt_of_lt_of_le hm0 hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro s
  rw [moment_add_constant m s hD.le]
  have hE : 0 ≤ a ^ m * V s + B := add_nonneg (mul_nonneg (pow_nonneg ha.le _) (V_pos s).le) hB.le
  by_cases hs : s.1 ≤ M
  · calc
      _ ≤ ENNReal.ofReal (a ^ m * V s + B) + ENNReal.ofReal D * ENNReal.ofReal (1 - p) :=
        add_le_add (hDrift m s) (mul_le_mul le_rfl (hHit m hm s hs) zero_le zero_le)
      _ = ENNReal.ofReal (a ^ m * V s + B + D * (1 - p)) := by
        rw [← ENNReal.ofReal_mul hD.le, ← ENNReal.ofReal_add hE (mul_nonneg hD.le (by linarith))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (block_drift_algebra hma.le hB.le hp hp1 (V_pos s).le
        (le_refl _) (show 1 - p ≤ 1 by linarith) (Or.inl le_rfl))
  · have hlarge : 8 * B ≤ V s := by
      dsimp [V]
      have hMb : 8 * B ≤ M := le_max_right _ _
      linarith [Real.add_one_le_exp s.1]
    calc
      _ ≤ ENNReal.ofReal (a ^ m * V s + B) + ENNReal.ofReal D := by
        apply add_le_add (hDrift m s)
        simpa only [mul_one] using mul_le_mul (le_refl (ENNReal.ofReal D)) (paired_survival_le_one m s) zero_le zero_le
      _ = ENNReal.ofReal (a ^ m * V s + B + D) := (ENNReal.ofReal_add hE hD.le).symm
      _ ≤ _ := by
        have h := block_drift_algebra hma.le hB.le hp hp1 (V_pos s).le (le_refl _) (le_refl (1 : ℝ)) (Or.inr hlarge)
        simpa only [mul_one] using ENNReal.ofReal_le_ofReal h

theorem paired_survival_geometric : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ,
    0 < ρ ∧ ρ < 1 ∧ 0 < D ∧ ∀ n : ℕ, ∀ s : OddState,
      (pairedKilled ^ (m * n)) s univ ≤ ENNReal.ofReal (ρ ^ n * (V s + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hblock⟩ := actual_block_contraction
  have hW : Measurable (fun s : OddState => ENNReal.ofReal (V s + D)) :=
    ENNReal.measurable_ofReal.comp (V_measurable.add measurable_const)
  have hIter : ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s) ≤
        ENNReal.ofReal (ρ ^ n * (V s + D)) := by
    intro n
    induction n with
    | zero =>
      intro s
      change (∫⁻ t, ENNReal.ofReal (V t + D) ∂Measure.dirac s) ≤ _
      rw [lintegral_dirac' s hW]
      simp
    | succ n ih =>
      intro s
      have hp : pairedKilled ^ (m * (n + 1)) = (pairedKilled ^ m) ∘ₖ (pairedKilled ^ (m * n)) := by
        rw [show m * (n + 1) = m + m * n by ring, Kernel.pow_add]
      rw [hp, Kernel.lintegral_comp _ _ _ hW]
      calc
        _ ≤ ∫⁻ t, ENNReal.ofReal ρ * ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s := by
          apply lintegral_mono
          intro t
          simpa only [ENNReal.ofReal_mul hρ.le] using hblock t
        _ = ENNReal.ofReal ρ * (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ n * (V s + D)) := mul_le_mul le_rfl (ih s) zero_le zero_le
        _ = _ := by rw [← ENNReal.ofReal_mul hρ.le, pow_succ]; congr 1; ring
  refine ⟨m, hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro n s
  calc
    _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂(pairedKilled ^ (m * n)) s := by simp
    _ ≤ ∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s := lintegral_mono (fun t =>
      by exact (ENNReal.one_le_ofReal).mpr (by linarith [V_one_le t]))
    _ ≤ _ := hIter n s

theorem paired_survival_tendsto_zero (s : OddState) :
    Tendsto (fun n => (pairedKilled ^ n) s univ) atTop (𝓝 0) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := paired_survival_geometric
  have hdiv : Tendsto (fun n : ℕ => n / m) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨m * b, fun n hn => (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hn)⟩
  have hreal : Tendsto (fun n : ℕ => ρ ^ (n / m) * (V s + D)) atTop (𝓝 0) := by
    simpa only [zero_mul, Function.comp_apply] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).comp hdiv).mul_const (V s + D)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (ρ ^ (n / m) * (V s + D))) atTop (𝓝 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal using 1
    all_goals try with_reducible_and_instances rfl
    simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => show (0 : ℝ≥0∞) ≤ _ from zero_le))
  apply Eventually.of_forall
  intro n
  exact le_trans (paired_survival_antitone s (Nat.mul_div_le n m)) (hb (n / m) s)

end NumberTheoryLean.PairedBlockContraction

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

def returnSet : Set OddCost := Prod.fst ⁻¹' pairedRegeneration

theorem returnSet_measurable : MeasurableSet returnSet :=
  pairedRegeneration_measurable.preimage measurable_fst

noncomputable def costKilled : Kernel OddCost OddCost := pairedCostKernel.restrict returnSet_measurable.compl
noncomputable def costCaptured : Kernel OddCost OddCost := pairedCostKernel.restrict returnSet_measurable

theorem costKilled_map_state (z : OddCost) : (costKilled z).map Prod.fst = pairedKilled z.1 := by
  rw [costKilled, Kernel.restrict_apply]
  change ((pairedCostKernel z).restrict (Prod.fst ⁻¹' pairedRegeneration)ᶜ).map Prod.fst = _
  rw [← preimage_compl, ← Measure.restrict_map measurable_fst pairedRegeneration_measurable.compl,
    pairedCost_map_state]
  rfl

theorem costKilled_pow_map_state (n : ℕ) (z : OddCost) :
    ((costKilled ^ n) z).map Prod.fst = (pairedKilled ^ n) z.1 := by
  induction n generalizing z with
  | zero =>
    change (Measure.dirac z).map Prod.fst = Measure.dirac z.1
    exact Measure.map_dirac' measurable_fst z
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro H hH
    rw [lintegral_map hH measurable_fst]
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ costKilled n
    have hq : pairedKilled ^ (n + 1) = (pairedKilled ^ n) ∘ₖ pairedKilled := pow_succ pairedKilled n
    rw [hp, hq, Kernel.lintegral_comp _ _ _ (g := fun z : OddCost => H z.1) (hH.comp measurable_fst),
      Kernel.lintegral_comp _ _ _ hH]
    have hi : ∀ y : OddCost, (∫⁻ w : OddCost, H w.1 ∂(costKilled ^ n) y) =
        ∫⁻ t, H t ∂(pairedKilled ^ n) y.1 := by
      intro y
      rw [← ih y, lintegral_map hH measurable_fst]
    simp_rw [hi]
    have hJ : Measurable (fun t : OddState => ∫⁻ u, H u ∂(pairedKilled ^ n) t) := hH.lintegral_kernel
    rw [← costKilled_map_state z, lintegral_map hJ measurable_fst]

theorem costKilled_mass (n : ℕ) (z : OddCost) :
    (costKilled ^ n) z univ = (pairedKilled ^ n) z.1 univ := by
  have h := congrArg (fun μ : Measure OddState => μ univ) (costKilled_pow_map_state n z)
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h

theorem cost_survival_tendsto_zero (z : OddCost) :
    Tendsto (fun n => (costKilled ^ n) z univ) atTop (𝓝 0) := by
  apply (paired_survival_tendsto_zero z.1).congr
  intro n
  exact (costKilled_mass n z).symm

noncomputable def firstReturn (n : ℕ) : Kernel OddCost OddCost := costCaptured ∘ₖ (costKilled ^ n)

noncomputable def returnLaw : Kernel OddCost OddCost := Kernel.sum firstReturn

theorem costCaptured_add_costKilled : costCaptured + costKilled = pairedCostKernel := by
  ext z : 1
  change (pairedCostKernel z).restrict returnSet + (pairedCostKernel z).restrict returnSetᶜ = pairedCostKernel z
  exact Measure.restrict_add_restrict_compl returnSet_measurable

theorem return_mass_step (n : ℕ) (z : OddCost) :
    firstReturn n z univ + (costKilled ^ (n + 1)) z univ = (costKilled ^ n) z univ := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  calc
    _ = ((costCaptured + costKilled) ∘ₖ (costKilled ^ n)) z univ := by
      rw [Kernel.comp_add_left, add_apply, Measure.add_apply, hp]
      rfl
    _ = (pairedCostKernel ∘ₖ (costKilled ^ n)) z univ := by rw [costCaptured_add_costKilled]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

theorem return_finite_mass (n : ℕ) (z : OddCost) :
    (costKilled ^ n) z univ + ∑ k ∈ Finset.range n, firstReturn k z univ = 1 := by
  induction n with
  | zero =>
    change (Measure.dirac z) univ + 0 = 1
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, firstReturn k z univ) +
          (firstReturn n z univ + (costKilled ^ (n + 1)) z univ) := by ac_rfl
      _ = (∑ k ∈ Finset.range n, firstReturn k z univ) + (costKilled ^ n) z univ := by rw [return_mass_step]
      _ = 1 := by simpa only [add_comm] using ih

instance returnLaw_isMarkovKernel : IsMarkovKernel returnLaw := by
  constructor
  intro z
  constructor
  rw [returnLaw, Kernel.sum_apply' _ _ MeasurableSet.univ]
  have h := (cost_survival_tendsto_zero z).add (ENNReal.tendsto_nat_tsum (fun n => firstReturn n z univ))
  simp only [zero_add, return_finite_mass] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end NumberTheoryLean.CostReturnLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerativeOddOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedBlockContraction
open NumberTheoryLean.RegenerationTails NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance

noncomputable def ratioOccupation : Measure State :=
  potential ratioVisits pairedKilled regenerationState

end Erdos970Dependency.RegenerativeOddOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationAge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw

noncomputable def visitBlock (n : ℕ) : Kernel OddCost CostState := pairVisits ∘ₖ (costKilled ^ n)

end NumberTheoryLean.CycleOccupation

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.OccupationAge
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.RegenerationTails

noncomputable def blockAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂visitBlock n (regenerationState, 0)

noncomputable def residualAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂(costKilled ^ n) (regenerationState, 0)

end Erdos970Dependency.OccupationAge

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationBandBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BigOperators
namespace Erdos970Dependency.CycleMeanCost
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation
open NumberTheoryLean.RegenerationTails
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.RawStateCost Erdos970Dependency.OccupationAge Erdos970Dependency.OnePairCost

noncomputable def capturedAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂firstReturn n (regenerationState, 0)

noncomputable def blockIncrement (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂visitBlock n (regenerationState, 0)

end Erdos970Dependency.CycleMeanCost

end

section

namespace NumberTheoryLean.InitialRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess
open CostReturnLaw CycleRegeneration PairedDrift
open InitialOddDraw

noncomputable def hitOrReturn : Kernel OddCost OddCost := by
  classical
  exact Kernel.piecewise returnSet_measurable Kernel.id returnLaw

instance hitOrReturn_isMarkovKernel : IsMarkovKernel hitOrReturn := by unfold hitOrReturn; infer_instance

noncomputable def delayedRegeneration : Kernel EvenState OddCost := hitOrReturn ∘ₖ firstOdd

end NumberTheoryLean.InitialRegeneration

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ContinuousRatioBins.ratioMeasure_noAtoms _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeCumulativeBound

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltMonotone PrimeRatioBins
open PrimeRatioMeasure HarmonicExponentMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem actual_cumulative_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → ∀ x ∈ primeAtoms w ell S i s r cap closed,
        finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) ≤
          ratioMeasure (minRatio i s) (Icc (minRatio i s) x) +
            ENNReal.ofReal (C * Real.exp (-c * Real.sqrt ((1/2 : ℝ) * Real.log w))) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S i s r cap closed hell hr hs x hx
  have hw1 := hw₀.trans_le hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  let x := childRatio w r p
  have ha := minRatio_pos hs
  have hax : minRatio i s ≤ x := (Finset.mem_filter.mp hp).2.2.2.1
  have hxp : r/(x+1) = primeExponent w p := nextExponent_childRatio hr (child_exponent_positive (by linarith) hp)
  have hlow : (1/2 : ℝ) ≤ r/(x+1) := by
    rw [hxp]
    have h := (Finset.mem_filter.mp hp).2.1
    linarith
  have hend : r/(x+1) ≤ r/(minRatio i s+1) :=
    div_le_div_of_nonneg_left hr.le (by linarith : 0 < minRatio i s+1) (by linarith)
  have hprime := hbound w hw (r/(x+1)) (r/(minRatio i s+1)) hlow hend true true
  rw [← closedMass_eq_harmonic hw1 ha hax, bin_log_width hr ha hax] at hprime
  have hE : C * Real.exp (-c * Real.sqrt ((r/(x+1))*Real.log w)) ≤
      C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)
  have hraw : (∑ q ∈ children w ell S i s r cap closed, if childRatio w r q ≤ x then (q : ℝ)⁻¹ else 0) ≤
      (Real.log (x+1)-Real.log (minRatio i s+1)) + C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
    have h := cumulative_sum_le_closed (ell := ell) (S := S) (r := r) (cap := cap) (b := x) hw1 hs closed
    have hh := (abs_le.mp hprime).2
    linarith
  change finitePrimeMeasure w ell S i s r cap closed (Icc (minRatio i s) x) ≤ _
  rw [finitePrimeMeasure_Icc, ratioMeasure_Icc ha hax]
  have hmain : 0 ≤ Real.log (x+1)-Real.log (minRatio i s+1) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  rw [← ENNReal.ofReal_add hmain (by positivity)]
  exact ENNReal.ofReal_le_ofReal hraw

end NumberTheoryLean.PrimeCumulativeBound



namespace NumberTheoryLean.PrimeRowMass

open _root_.Set _root_.Finset _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioMeasure PrimeCumulativeBound HarmonicExponentMeasure FiniteMonotoneComparison

theorem retained_row_mass : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → s ≤ S →
      (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) ≤
        1 + C*(1+S)^2 * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hcdf⟩ := actual_cumulative_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  refine ⟨c,C*D,w₀,hc,mul_pos hC hD,hw₀,?_⟩
  intro w hw ell S i s r cap closed hell hr hs hsS
  let μ := finitePrimeMeasure w ell S i s r cap closed
  let ν := ratioMeasure (minRatio i s)
  let A := primeAtoms w ell S i s r cap closed
  let E := C * Real.exp (-c * Real.sqrt ((1/2 : ℝ)*Real.log w))
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hloc : ∀ t ∈ A, minRatio i s ≤ t := primeAtoms_above w ell S i s r cap closed
  have hcomp := finite_monotone_integral_le μ ν A (multiplier i s) (minRatio i s)
    (multiplier i s (minRatio i s)) (ENNReal.ofReal E) (multiplier_measurable i s)
    (finitePrimeMeasure_support w ell S i s r cap closed) hloc
    (fun t ht => (multiplier_pos hs (valid_next hs (hloc t ht))).le)
    (multiplier_nonnegative_ae hs) (multiplier_antitone hs)
    (fun t ht => multiplier_antitone hs (a := minRatio i s) (b := t)
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (hloc t ht)) (hloc t ht))
    (hcdf w hw ell S i s r cap closed hell hr hs)
  rw [finitePrimeMeasure_tilt w ell S i s r cap closed hs, multiplier_ratio_integral hs] at hcomp
  have hM := henv S i s (minRatio i s) hs hsS le_rfl
  have hn : 0 ≤ 1 + (C*D)*(1+S)^2 * Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w)) := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff hn).mp
  calc
    _ ≤ 1 + ENNReal.ofReal E * ENNReal.ofReal (multiplier i s (minRatio i s)) := hcomp
    _ ≤ 1 + ENNReal.ofReal E * ENNReal.ofReal (D*(1+S)^2) :=
      add_le_add le_rfl (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal hM) zero_le zero_le)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hE]
      have hprod : 0 ≤ E*(D*(1+S)^2) := by positivity
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num, ← ENNReal.ofReal_add (by norm_num) hprod]
      congr 1
      dsimp [E]
      ring

end NumberTheoryLean.PrimeRowMass



namespace NumberTheoryLean.PrimeRowNormalization

open _root_.Filter _root_.Set _root_.Finset
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeTiltGeometry PrimeRowMass

theorem retained_row_mass_one_add : ∃ c w₀ : ℝ, 0 < c ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
    ∀ i : Side, ∀ s r cap : ℝ, ∀ closed : Bool, 1 ≤ ell → 0 < r → Valid i s → s ≤ S →
      (∑ p ∈ children w ell S i s r cap closed, primeTilt w r i s p) ≤
        1 + Real.exp (-c * Real.sqrt (Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hrow⟩ := retained_row_mass
  obtain ⟨w₁,hw₁⟩ := (eventually_atTop.1 (polynomial_absorption hc hC))
  refine ⟨c/4,max w₀ w₁,by positivity,hw₀.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS0 hS i s r cap closed hell hr hs hsS
  exact (hrow w ((le_max_left _ _).trans hw) ell S i s r cap closed hell hr hs hsS).trans
    (add_le_add le_rfl (hw₁ w ((le_max_right _ _).trans hw) S hS0 hS))

end NumberTheoryLean.PrimeRowNormalization



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

noncomputable def normalizationRate : ℝ := Classical.choose retained_row_mass_one_add
noncomputable def normalizationThreshold : ℝ := Classical.choose (Classical.choose_spec retained_row_mass_one_add)

noncomputable def epsilon (w : ℝ) : ℝ := Real.exp (-normalizationRate * Real.sqrt (Real.log w))

theorem epsilon_pos (w : ℝ) : 0 < epsilon w := Real.exp_pos _
theorem normalizer_pos (w : ℝ) : 0 < 1+epsilon w := by linarith [epsilon_pos w]

theorem actual_row_bound {w ell S : ℝ} (hw : normalizationThreshold ≤ w) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (z : Node) (hell : 1 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hsS : z.ratio ≤ S) :
    (∑ p ∈ nodeChildren w ell S z, primeTilt w z.gap z.side z.ratio p) ≤ 1+epsilon w := by
  exact (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.2
    w hw ell S hS0 hS z.side z.ratio z.gap z.cutoff z.closed hell hr hs hsS

variable (w ell S : ℝ) (start : Node)

noncomputable def childProbability (h : History w ell S start) (p : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w))

noncomputable def liveMass (h : History w ell S start) : ℝ≥0∞ :=
  ∑ p ∈ nodeChildren w ell S h.node, childProbability w ell S start h p

noncomputable def liveLaw (h : History w ell S start) : Measure (ChainState w ell S start) :=
  ∑ p ∈ (nodeChildren w ell S h.node).attach,
    childProbability w ell S start h p.1 • Measure.dirac (some (h.append p.1 p.2))

theorem liveLaw_univ (h : History w ell S start) : liveLaw w ell S start h univ = liveMass w ell S start h := by
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
    Finset.sum_attach, liveMass]

noncomputable def completedLaw (h : History w ell S start) : Measure (ChainState w ell S start) :=
  liveLaw w ell S start h + (1-liveMass w ell S start h) • Measure.dirac none

noncomputable def chain : Kernel (ChainState w ell S start) (ChainState w ell S start) where
  toFun z := match z with
    | none => Measure.dirac none
    | some h => completedLaw w ell S start h
  measurable' := measurable_of_countable _

@[simp] theorem chain_none : chain w ell S start none = Measure.dirac none := rfl
@[simp] theorem chain_some (h : History w ell S start) : chain w ell S start (some h) = completedLaw w ell S start h := rfl

variable {w ell S : ℝ} {start : Node}

theorem liveMass_le_one (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (h : History w ell S start) :
    liveMass w ell S start h ≤ 1 := by
  have hnvalid := terminal_valid hs h.admissible
  have hngap := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs h.admissible
  have hnS := terminal_ratio_le hsS h.admissible
  have hrow := actual_row_bound hw hS0 hS h.node hell hngap hnvalid hnS
  have hZ := normalizer_pos w
  unfold liveMass childProbability
  have hnonneg : ∀ p ∈ nodeChildren w ell S h.node,
      0 ≤ primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w) := by
    intro p hp
    exact div_nonneg (primeTilt_nonneg (w := w) (r := h.node.gap) (i := h.node.side) (s := h.node.ratio) hnvalid hp) hZ.le
  rw [← ENNReal.ofReal_sum_of_nonneg (s := nodeChildren w ell S h.node)
    (f := fun p => primeTilt w h.node.gap h.node.side h.node.ratio p / (1+epsilon w)) hnonneg, ← Finset.sum_div]
  have hreal : (∑ p ∈ nodeChildren w ell S h.node, primeTilt w h.node.gap h.node.side h.node.ratio p) /
      (1+epsilon w) ≤ 1 := (div_le_iff₀ hZ).mpr (by simpa only [one_mul] using hrow)
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal

theorem chain_isMarkov (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) :
    IsMarkovKernel (chain w ell S start) := by
  constructor
  intro z
  constructor
  cases z with
  | none => simp only [chain_none, measure_univ]
  | some h =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (liveMass_le_one hw hell hS0 hS hr hs hsS h)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeCompactVisits

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry

variable {w ell S : ℝ} {start : Node}

noncomputable def potential (K : ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => min h.node.gap K + 1

noncomputable def visit (K : ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => if h.node.gap ≤ K then 1 else 0

end NumberTheoryLean.PrimeCompactVisits



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

namespace NumberTheoryLean.ActualPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeHistories PrimeKilledChain
open PrimeRatioBins

variable {w ell S : ℝ} {start : Node}

def liveBin (a b : ℝ) : Set (ChainState w ell S start) :=
  fun z => match z with
    | none => False
    | some h => a ≤ h.node.ratio ∧ h.node.ratio < b

end NumberTheoryLean.ActualPrimeBins

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

noncomputable def actualHasHigh (w T : ℝ) (z : Node) (ps : List ℕ) : Prop :=
  ∃ pre suf : List ℕ, ps = pre ++ suf ∧ T < (terminal w z pre).ratio

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

noncomputable def uncappedChildren (w ell : ℝ) (z : Node) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^z.cutoff⌋₊).filter (fun p => ell < primeExponent w p ∧
    capGuard z.closed z.cutoff (primeExponent w p) ∧
      minRatio z.side z.ratio ≤ childRatio w z.gap p)

noncomputable def uncappedAllowed (w ell : ℝ) : Node → List ℕ → Prop
  | _, [] => True
  | z, p::ps => p ∈ uncappedChildren w ell z ∧ uncappedAllowed w ell (step w z p) ps

noncomputable def uncappedPrefixes (w ell : ℝ) (z : Node) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff))).filter (uncappedAllowed w ell z)

end NumberTheoryLean.ActualPrimeHigh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

abbrev JointState (w ell S : ℝ) (start : Node) :=
  ChainState w ell S start × CemeteryKernel.Space CostState

noncomputable def primeLabel (w ell S mesh : ℝ) (start : Node) : ChainState w ell S start → Label S mesh
  | none => cemeteryLabel S mesh
  | some h => ratioLabel S mesh h.node.ratio

theorem primeLabel_measurable (w ell S mesh : ℝ) (start : Node) : Measurable (primeLabel w ell S mesh start) :=
  measurable_of_countable _

noncomputable def primeParent (w ell S : ℝ) (start : Node) : Kernel (JointState w ell S start) (ChainState w ell S start) :=
  (chain w ell S start).comap Prod.fst measurable_fst

noncomputable def continuousParent (w ell S : ℝ) (start : Node) (v : ℝ) :
    Kernel (JointState w ell S start) (CemeteryKernel.Space CostState) :=
  (continuousChain v ell S).comap Prod.snd measurable_snd

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def jointKernel
    (_hw : normalizationThreshold ≤ w) (_hell : 1 ≤ ell) (_hS0 : 0 ≤ S) (_hS : S ≤ (Real.log w)^3)
    (_hr : 0 < start.gap) (_hs : Valid start.side start.ratio) (_hsS : start.ratio ≤ S)
    (v mesh : ℝ) : Kernel (JointState w ell S start) (JointState w ell S start) := by
  letI := chain_isMarkov _hw _hell _hS0 _hS _hr _hs _hsS
  exact coupled (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels ActualProcessCoupling LowStateHorizon

variable {w ell S : ℝ} {start : Node}

def matchedOutcome (mesh : ℝ) : JointState w ell S start → Prop
  | (none,.inr _) => True
  | (some h,.inl z) => |h.node.ratio-stateRatio z.1| < mesh
  | _ => False

end NumberTheoryLean.ActualCouplingSupport

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins LowStateHorizon

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def jointPathLaw (v mesh : ℝ) (z : CostState) (n : ℕ) : Measure (JointState w ell S start) :=
  ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) (some History.empty,.inl z)

end NumberTheoryLean.ActualCouplingFinite

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

def primeFollows (h : History w ell S start) : ChainState w ell S start → Prop
  | none => True
  | some k => ∃ p, ∃ hp : p ∈ nodeChildren w ell S h.node, k = h.append p hp

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ActualFlagInvariant

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualCouplingUpdates ActualCouplingFinite
open PersistentFailureFlag FailureFlagBounds RegeneratingInverseBands ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

def mismatch (mesh : ℝ) (q : JointState w ell S start) : Prop :=
  primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2

theorem mismatch_measurable (mesh : ℝ) : MeasurableSet {q : JointState w ell S start | mismatch mesh q} := by
  let D : Set (MeshRatioLabels.Label S mesh × MeshRatioLabels.Label S mesh) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  exact (((primeLabel_measurable w ell S mesh start).comp measurable_fst).prodMk
    ((continuousLabel_measurable S mesh).comp measurable_snd)) hD

def liveGood (v mesh : ℝ) (n : ℕ) (h : History w ell S start) (z : CostState) : Prop :=
  stateRatio z.1 ≤ S ∧ h.node.side = stateSide z.1 ∧ |h.node.ratio-stateRatio z.1| ≤ mesh ∧
    |Real.log h.node.gap-Real.log (gapValue v z)| ≤ 4*(n:ℝ)*mesh

def GoodAt (v mesh : ℝ) (n : ℕ) : JointState w ell S start → Prop
  | (none,.inr _) => True
  | (some h,.inl z) => liveGood v mesh n h z
  | _ => False

end NumberTheoryLean.ActualFlagInvariant



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

def sourceCostState (hs : Valid start.side start.ratio) : CostState :=
  (typedState start.side start.ratio hs,0)

def sourceJoint (w ell S : ℝ) (start : Node) (hs : Valid start.side start.ratio) : JointState w ell S start :=
  (some History.empty,.inl (sourceCostState hs))

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualFlaggedCompact
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualFlaggedCompact

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open PrimeCompactVisits FlaggedOccupationBound PersistentFailureFlag ActualFlagInvariant

variable {w ell S : ℝ} {start : Node}

noncomputable def compactVisit (K : ℝ) (z : JointState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (visit K z.1)

noncomputable def compactPotential (K : ℝ) (z : JointState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (potential K z.1)

end NumberTheoryLean.ActualFlaggedCompact

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicPaths
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open AdmittedHarmonicPaths RegeneratingInverseBands

noncomputable def initial (S : ℝ) (z : CostState) : FlagState :=
  (z, if S < stateRatio z.1 then true else false)

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCoupledHistories
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open FlaggedSourceStart ContinuousKilledBins FiniteHistoryTransport

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

noncomputable def sourceTransition (mesh : ℝ) :
    Kernel (FlagState (JointState w ell S start)) (FlagState (JointState w ell S start)) :=
  marked (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh)

noncomputable def sourceHistoryLaw (mesh : ℝ) (n : ℕ) :
    Measure (Hist (FlagState (JointState w ell S start)) n) :=
  pathKernel (sourceTransition hw hell hS0 hS hr hs hsS mesh) n
    (fun _ => (sourceJoint w ell S start hs,false))

end NumberTheoryLean.ActualCoupledHistories



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_MarkedCycleCompletion
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.RegenerationTails
open NumberTheoryLean.FinitePathGeometry

noncomputable def markContinuation : Kernel MarkedOddCost MarkedOddCost :=
  (Kernel.id ×ₖ hitOrReturn.prodMkLeft Bool).map continueMarkUpdate

instance markContinuation_isMarkovKernel : IsMarkovKernel markContinuation :=
  Kernel.IsMarkovKernel.map _ continueMarkUpdate_measurable

noncomputable def completedMarkedKernel : Kernel OddCost MarkedOddCost :=
  markContinuation ∘ₖ markedPairKernel

instance completedMarkedKernel_isMarkovKernel : IsMarkovKernel completedMarkedKernel := by
  unfold completedMarkedKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostSublaws
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails

noncomputable def sourceCycleLaw : Measure MarkedOddCost := completedMarkedKernel (regenerationState,0)

instance sourceCycleLaw_isProbabilityMeasure : IsProbabilityMeasure sourceCycleLaw := by
  unfold sourceCycleLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def markedCostLaw : Measure ℝ :=
  (sourceCycleLaw.restrict sourceMarkSet).map sourceCostProjection

noncomputable def unmarkedCostLaw : Measure ℝ :=
  (sourceCycleLaw.restrict sourceMarkSetᶜ).map sourceCostProjection

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_MarkedCycleFactorization
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.RegenerationTails

noncomputable def jointMarkCostLaw : Measure (Bool × ℝ) := sourceCycleLaw.map markCostProjection

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_GeometricCostLaws
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open AbsorptionCutoff.Renewal

noncomputable def unmarkedPotential : Measure ℝ := renewalMeasure unmarkedCostLaw

noncomputable def geometricMarkedCostLaw : Measure ℝ := markedCostLaw ∗ unmarkedPotential

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_MarkedCycleWords
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

noncomputable def cycleBranchKernel (b : Bool) : Kernel OddCost OddCost :=
  (completedMarkedKernel.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd

instance cycleBranchKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (cycleBranchKernel b) := by
  unfold cycleBranchKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance cycleBranch_pow_isFiniteKernel (b : Bool) (n : ℕ) : IsFiniteKernel (cycleBranchKernel b ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (cycleBranchKernel b ∘ₖ (cycleBranchKernel b ^ n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def branchCostLaw (b : Bool) : Measure ℝ :=
  (sourceCycleLaw.restrict {z | z.1=b}).map sourceCostProjection

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedReturnKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails

noncomputable def nextMarkWeight (z : OddCost) : ℝ≥0∞ := cycleBranchKernel true z univ

noncomputable def actualWaitingTerm (n : ℕ) (z : OddCost) : Measure ℝ :=
  (((cycleBranchKernel false ^ n) z).withDensity nextMarkWeight).map (fun y => y.2-z.2)

noncomputable def actualSpacingTerm (n : ℕ) (z : OddCost) : Measure ℝ :=
  markProbability⁻¹ •
    ((((cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true) z).withDensity nextMarkWeight).map
      (fun y => y.2-z.2)

noncomputable def actualWaitingLaw (z : OddCost) : Measure ℝ := Measure.sum (fun n => actualWaitingTerm n z)
noncomputable def actualSpacingLaw (z : OddCost) : Measure ℝ := Measure.sum (fun n => actualSpacingTerm n z)

noncomputable def firstMarkWaitingLaw : Measure ℝ := actualWaitingLaw (regenerationState,0)
noncomputable def markedSpacingLaw : Measure ℝ := actualSpacingLaw (regenerationState,0)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

noncomputable def markedReturnKernel : Kernel OddCost OddCost :=
  potential (cycleBranchKernel true) (cycleBranchKernel false)

instance markedReturnKernel_isSFiniteKernel : IsSFiniteKernel markedReturnKernel := by
  unfold markedReturnKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedBeginningKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

noncomputable def rawBeginningKernel : Kernel OddCost OddCost :=
  Kernel.sum (fun n : ℕ => (cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true)

instance rawBeginningKernel_isSFiniteKernel : IsSFiniteKernel rawBeginningKernel := by
  unfold rawBeginningKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

abbrev RegCost := {z : OddCost // z ∈ returnSet}

noncomputable def beginningDomainKernel : Kernel RegCost OddCost :=
  rawBeginningKernel.comap Subtype.val measurable_subtype_coe

noncomputable def markedBeginningKernel : Kernel RegCost RegCost :=
  beginningDomainKernel.comapRight (MeasurableEmbedding.subtype_coe returnSet_measurable)

def beginningCost (z : RegCost) : ℝ := z.1.2

lemma beginningCost_measurable : Measurable beginningCost :=
  measurable_snd.comp measurable_subtype_coe

noncomputable def markedClockKernel : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ markedSpacingLaw).map (fun x : ℝ × ℝ => x.1+x.2)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ClockTailReward
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open AbsorptionCutoff.Renewal
open NumberTheoryLean.KernelPotential

noncomputable def clockBelow (v : ℝ) : Kernel ℝ ℝ := markedClockKernel.restrict (s := Iio v) measurableSet_Iio
noncomputable def clockOver (v H : ℝ) : Kernel ℝ ℝ := markedClockKernel.restrict (s := Ioi (v+H)) measurableSet_Ioi

noncomputable def clockOverReward (v H : ℝ) : Kernel ℝ ℝ := by
  classical
  exact Kernel.piecewise (s := Iio v) measurableSet_Iio (clockOver v H) 0

noncomputable def clockOvershoot (v H : ℝ) : ℝ≥0∞ := (potential (clockOver v H) (clockBelow v)) 0 univ

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal

noncomputable def clockTailPiece (v H : ℝ) (j : ℕ) : ℝ → ℝ≥0∞ :=
  (Icc (v-(j:ℝ)-1) (v-j)).indicator (fun _ => markedSpacingLaw (Ioi (H+j)))

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ClockWindowPassage
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.KernelPotential

noncomputable def clockAtOrAbove (v : ℝ) : Kernel ℝ ℝ :=
  markedClockKernel.restrict (s := Ici v) measurableSet_Ici

noncomputable def clockWindow (v H : ℝ) : Kernel ℝ ℝ :=
  markedClockKernel.restrict (s := Icc v (v+H)) measurableSet_Icc

noncomputable def clockWindowHit (v H : ℝ) : ℝ≥0∞ :=
  (potential (clockWindow v H) (clockBelow v)) 0 univ

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BeginningWindowTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.KernelPotential

def relativeBeginningCost (t : ℝ) (z : RegCost) : ℝ := beginningCost z-t

lemma relativeBeginningCost_measurable (t : ℝ) : Measurable (relativeBeginningCost t) :=
  beginningCost_measurable.sub measurable_const

noncomputable def beginningBelow (t v : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Iio v)
    ((relativeBeginningCost_measurable t) measurableSet_Iio)

noncomputable def beginningWindow (t v H : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Icc v (v+H))
    ((relativeBeginningCost_measurable t) measurableSet_Icc)

noncomputable def beginningOver (t v H : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Ioi (v+H))
    ((relativeBeginningCost_measurable t) measurableSet_Ioi)

noncomputable def beginningWindowHit (z : RegCost) (v H : ℝ) : ℝ≥0∞ :=
  (potential (beginningWindow (beginningCost z) v H) (beginningBelow (beginningCost z) v)) z univ

noncomputable def beginningOvershoot (z : RegCost) (v H : ℝ) : ℝ≥0∞ :=
  (potential (beginningOver (beginningCost z) v H) (beginningBelow (beginningCost z) v)) z univ

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MovingMarkedWindow
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential
open AbsorptionCutoff.Renewal

noncomputable def rawFirstMarkedBeginning : Kernel OddCost OddCost :=
  (potential Kernel.id (cycleBranchKernel false)).withDensity (fun _ y => nextMarkWeight y)

noncomputable def initialMarkedBeginning : Kernel EvenState OddCost :=
  rawFirstMarkedBeginning ∘ₖ delayedRegeneration

noncomputable def initialMarkedCostLaw (s : EvenState) : Measure ℝ :=
  (initialMarkedBeginning s).map Prod.snd

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelPotential

noncomputable def initialBeginningReg : Kernel EvenState RegCost :=
  initialMarkedBeginning.comapRight (MeasurableEmbedding.subtype_coe returnSet_measurable)

noncomputable def markedWindowSuccess (v H : ℝ) (z : RegCost) : ℝ≥0∞ :=
  if beginningCost z < v then (potential (beginningWindow 0 v H) (beginningBelow 0 v)) z univ
  else if beginningCost z ≤ v+H then 1 else 0

noncomputable def markedWindowFailure (v H : ℝ) (z : RegCost) : ℝ≥0∞ :=
  if beginningCost z < v then (potential (beginningOver 0 v H) (beginningBelow 0 v)) z univ
  else if beginningCost z ≤ v+H then 0 else 1

noncomputable def initialMarkedWindowSuccess (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, markedWindowSuccess v H z ∂initialBeginningReg s

noncomputable def initialMarkedWindowFailure (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, markedWindowFailure v H z ∂initialBeginningReg s

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrdinaryMarkedWindow
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

noncomputable def markInputWeightKernel : Kernel OddCost OddCost :=
  Kernel.id.withDensity (fun _ z => nextMarkWeight z)

noncomputable def ordinaryWindowCapture (v H : ℝ) : Kernel OddCost OddCost :=
  markInputWeightKernel.restrict (ordinaryCostWindow_measurable v H)

noncomputable def ordinaryWindowContinue (v H : ℝ) : Kernel OddCost OddCost :=
  cycleBranchKernel false+cycleBranchKernel true ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl

instance ordinaryWindowContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (ordinaryWindowContinue v H) := by
  unfold ordinaryWindowContinue
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def ordinaryMarkedHit (v H : ℝ) : Kernel OddCost OddCost :=
  potential (ordinaryWindowCapture v H) (ordinaryWindowContinue v H)

noncomputable def unmarkedStar : Kernel OddCost OddCost := potential Kernel.id (cycleBranchKernel false)

instance unmarkedStar_isSFiniteKernel : IsSFiniteKernel unmarkedStar := by unfold unmarkedStar; infer_instance

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostHitReduction
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

noncomputable def costMarkedLoop (v H : ℝ) : Kernel ℝ ℝ := markedClockKernel ∘ₖ costOutsideFilter v H

noncomputable def costCurrentHit (v H : ℝ) : Kernel ℝ ℝ :=
  potential (costWindowFilter v H) (costMarkedLoop v H)

noncomputable def ordinaryMarkedLoop (v H : ℝ) : Kernel OddCost OddCost :=
  rawBeginningKernel ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl
instance ordinaryMarkedLoop_isSFiniteKernel (v H : ℝ) : IsSFiniteKernel (ordinaryMarkedLoop v H) := by
  unfold ordinaryMarkedLoop
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential

noncomputable def ordinaryInitialHitMass (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ordinaryMarkedHit v H z univ ∂delayedRegeneration s

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationInputPotential
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.KernelPotential

noncomputable def regenerationInput : Kernel OddCost OddCost := stateFilter returnSet_measurable
noncomputable def nonregenerationInput : Kernel OddCost OddCost := stateFilter returnSet_measurable.compl

instance regenerationInput_isFiniteKernel : IsFiniteKernel regenerationInput := by unfold regenerationInput; infer_instance
instance nonregenerationInput_isFiniteKernel : IsFiniteKernel nonregenerationInput := by unfold nonregenerationInput; infer_instance

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
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.KernelPotential

noncomputable def oddConsecutiveCapture (v H : ℝ) : Kernel OddCost OddCost :=
  ordinaryWindowCapture v H ∘ₖ regenerationInput

noncomputable def oddConsecutiveContinue (v H : ℝ) : Kernel OddCost OddCost :=
  pairedCostKernel ∘ₖ nonregenerationInput+pairWindowContinue v H ∘ₖ regenerationInput

instance oddConsecutiveContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (oddConsecutiveContinue v H) := by
  unfold oddConsecutiveContinue
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def oddConsecutiveHit (v H : ℝ) : Kernel OddCost OddCost :=
  potential (oddConsecutiveCapture v H) (oddConsecutiveContinue v H)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualOddPairLink
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CostReturnLaw

noncomputable def oddGoodInput (v H : ℝ) : Set OddCost := returnSet ∩ ordinaryCostWindow v H

end Erdos970Dependency.MarkedVisits

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

open _root_.Set _root_.Finset
namespace ErdosContinuousAnomaly
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.UniformExponentialOccupation NumberTheoryLean.ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def continuousBoundaryCorrection (w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*((-1:ℝ)^ps.length*
    continuousAnomaly (terminal w start ps).side (terminal w start ps).gap)

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CompactCorrectionLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosCorrectionOccupation
attribute [local instance] Classical.propDecidable
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail

noncomputable def compactCorrection (K w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
    compactAnomalyTest K (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio)

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PaperContinuousCorrection
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
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale
open Erdos970Dependency.InvariantCostBound

noncomputable def paperStart (a : ℝ) (e : ℝ → ℝ) (closed : Bool) (L : ℝ) : Node where
  side := .even
  gap := paperGap a e L
  ratio := paperGap a e L/sourceB L
  cutoff := sourceB L
  closed := closed

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCenteredGap
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.PrimeHistories NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def sourceRootNode (a z : ℝ) : Node where
  side := .even
  gap := sourceRootGap a z
  ratio := sourceRootGap a z/ErdosInverseBoxHeight.sourceB z
  cutoff := ErdosInverseBoxHeight.sourceB z
  closed := true

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualPrefixClearance
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualPrefixClearance
open FinitePathGeometry PrimeHistories SourceStopPredicate RepresentativeAdmission RepresentativeStopGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


def actualClearance (w : ℝ) (z : Node) (Delta : ℝ) (ps : List ℕ) : Prop :=
  ∀ qs ∈ ps.inits,qs ≠ [] → (terminal w z qs).side=.even →
    sourceHeight (terminal w z qs).cutoff+10*Delta < (terminal w z qs).gap

end NumberTheoryLean.ActualPrefixClearance


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
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualPrimeHigh ActualProcessCoupling
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open ActualCoupledHistories
open ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels


def compactAdjacentWord {n : ℕ} (w : ℝ) (lab : ℕ → Fin n) (L : ℝ) (start : Node) (ps : List ℕ) : Prop :=
  ∃ pre p q tail,ps=pre++p::q::tail ∧ lab p=lab q ∧ (terminal w start (pre++[p])).gap ≤ L

end NumberTheoryLean.RepeatedWordEvents


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
open ErdosSubsetWord ErdosCofactorChoices ActualSourceTags
open ErdosPrimeInputs.PrimePrefixMass
attribute [local instance] Classical.propDecidable

noncomputable def regularWords {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B K : ℝ) (z : Node) : Finset (List ℕ) :=
  (decreasingPrefixes (sourcePrimeSet w top)).filter (fun ps =>
    (ps.length:ℝ) ≤ Clen*Real.log B ∧ actualClearance w z (2*Clen*xi) ps ∧
    (terminal w z ps).gap ≤ K ∧ ∀ b,searchBin w (lower w top xi b) →
      (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b ≤ 1)

end NumberTheoryLean.ActualRegularBoxes



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



namespace NumberTheoryLean.GeometricRegularWords
open FinitePathGeometry PrimeHistories ActualRegularBoxes RepeatedWordEvents NonisolatedWordOccurrence
open IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def geometricWords {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B R L alpha beta : ℝ) (z : Node) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B R z).filter (fun ps =>
    ¬compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps ∧
    ¬noIsolatedWord hw htop hxi B alpha beta ps)

end NumberTheoryLean.GeometricRegularWords


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceRawBoxFactory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosVarianceEligible
open NumberTheoryLean PrimeHistories GeometricRegularWords ActualCountErrorEdges ErdosCofactorChoices ErdosSubsetWord
  LogarithmicBinScale

def unwitnessedSelection {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs C B K L alpha beta eps : ℝ) (residue : ℕ → ℕ) (z : Node) (Q : Finset ℚ)
    (f : Fin (binCount w top xi) → Finset ℕ) : Prop :=
  descendingWord f ∈ geometricWords hw htop hxi C B K L alpha beta z ∧
    eps < |wordCountError Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue (SmallSieveFinite.smallEuler ⌊w⌋₊) (descendingWord f)| ∧
    ¬eligibleWordWitness Y w Cs residue Q (descendingWord f)

end ErdosVarianceEligible



open _root_.Filter


end Erdos970

end OAI
end



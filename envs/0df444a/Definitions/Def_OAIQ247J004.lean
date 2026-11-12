-- Prove2me | Definitions.Def_OAIQ247J004
-- name    : OAIQ247J004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:42:40.854754+00:00
-- url     : https://prove2.me/theorems/a260c08e-ce03-4cf8-bd0c-ce9654908122
-- title:
--   Definitions bundle OAIQ247J004 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 271 declarations of OpenAI's Lean: 142 definitions, 2 instances and 127 theorems. The definitions and types are `OAI.Erdos970.NumberTheoryLean.ParentTailPartition.aboveIndexSet`, `OAI.Erdos970.NumberTheoryLean.PartitionedSelections.joinSelection`, `OAI.Erdos970.NumberTheoryLean.PartitionedSelections.restrictMultiplicity`, `OAI.Erdos970.NumberTheoryLean.PartitionedSelections.restrictSelection`, `OAI.Erdos970.NumberTheoryLean.PrimeBinAlignmentMass.mass`, `OAI.Erdos970.NumberTheoryLean.PrimeDensityBlocks.dyadicPrimes`, `OAI.Erdos970.NumberTheoryLean.ProgressionSieve.deletionBudget`, `OAI.Erdos970.NumberTheoryLean.ProgressionSieve.progressionLength`, `OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors`, `OAI.Erdos970.NumberTheoryLean.ReciprocalGapExposure.potential`, `OAI.Erdos970.NumberTheoryLean.ReferenceCutoffRecurrence.Above`, `OAI.Erdos970.NumberTheoryLean.ReferenceProductErrorBounds.primeError`, `OAI.Erdos970.NumberTheoryLean.ReferencePruning.suffixPrimes`, `OAI.Erdos970.NumberTheoryLean.RegularityDefectPartition.lengthFailure`, `OAI.Erdos970.NumberTheoryLean.SelbergOptimization.diagonalTarget`, `OAI.Erdos970.NumberTheoryLean.SelbergOptimization.inverseMultiples`, `OAI.Erdos970.NumberTheoryLean.SelbergOptimization.lowerMobius`, `OAI.Erdos970.NumberTheoryLean.SelbergOptimization.normalization`, `OAI.Erdos970.NumberTheoryLean.SelbergOptimization.optimizedWeight`, `OAI.Erdos970.NumberTheoryLean.SievePartition.childCell`, `OAI.Erdos970.NumberTheoryLean.SingletonBinSelection.eraseMultiplicity`, `OAI.Erdos970.NumberTheoryLean.SingletonBinSelection.fillSelection`, `OAI.Erdos970.NumberTheoryLean.SingletonSubsetMass.subsetWeight`, `OAI.Erdos970.NumberTheoryLean.SourceTailBudget.failureBudget`, `OAI.Erdos970.NumberTheoryLean.SourceThresholdCoupling.thresholdPerturbation`, `OAI.Erdos970.NumberTheoryLean.SquarefreeHarmonic.squarefreeHarmonic`, `OAI.Erdos970.NumberTheoryLean.SquarefreeHarmonic.squarefreeUpTo`, `OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.goodKernel`, `OAI.Erdos970.NumberTheoryLean.SurvivorResidueShift.successorResidues`, `OAI.Erdos970.NumberTheoryLean.TwoSingletonBins.eraseTwo`, `OAI.Erdos970.NumberTheoryLean.TwoSingletonBins.fillTwo`, `OAI.Erdos970.NumberTheoryLean.UniformExponentialOccupation.positiveGapEnvelope`, `OAI.Erdos970.NumberTheoryLean.UniformFailureBudget.upperDisplacement`, `OAI.Erdos970.NumberTheoryLean.WeightedGapTail.binCoefficient`, `OAI.Erdos970.NumberTheoryLean.WeightedGapTail.tailBudget`, `OAI.Erdos970.NumberTheoryLean.WeightedGapTail.tailSeries`, `OAI.Erdos970.NumberTheoryLean.WordIntervalGeometry.wordIntervalExponent`, `OAI.Erdos970.WeightedTorusJets.Deformation.genericFiberLocalBaseEquiv`, `OAI.Erdos970.WeightedTorusJets.Deformation.localFractionAlgebra`, `OAI.Erdos970.WeightedTorusJets.Deformation.localQuotientAlgEquiv` and 102 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Jacobsthal_Estimates_EvenInverseBands`, `Jacobsthal_Estimates_MovingLocalReference`, `Jacobsthal_Estimates_ReferenceCutoffRecurrence`, `Jacobsthal_Estimates_ScaledOriginalTail`, `Jacobsthal_Estimates_SingletonSubsetMass`, `Jacobsthal_Estimates_SquarefreeHarmonic`, `Jacobsthal_Estimates_UniformFailureBudget`, `Jacobsthal_Partitions_ActualBoxFourSum`, `Jacobsthal_Partitions_RegularityDefectPartition`, `Jacobsthal_Partitions_TwoSingletonBins`, `Jacobsthal_Paths_FiniteHistorySupport`, `Jacobsthal_Paths_PrefixCompletions`, `Jacobsthal_Paths_WordIntervalGeometry`, `Jacobsthal_Primes_PrimeChoiceCoordinateMass`, `Jacobsthal_Primes_PrimeDensityBlocks`, `Jacobsthal_Probability_SourceThresholdCoupling`, `Jacobsthal_Probability_SubMarkovFlagPowers`, `Jacobsthal_Siegel_CoeffPolynomialEvalMul`, `Jacobsthal_Siegel_CoefficientSubspaceEquiv`, `Jacobsthal_Siegel_ConductorCompletedL`, `Jacobsthal_Siegel_ConeMap`, `Jacobsthal_Siegel_ConeMapEval`, `Jacobsthal_Siegel_CoordinateLocalizedPrime`, `Jacobsthal_Siegel_DegreeMap`, `Jacobsthal_Siegel_DerivationJet`, `Jacobsthal_Siegel_DominantFunctionFieldHom`, `Jacobsthal_Siegel_FiniteTypeFieldModelEquiv`, `Jacobsthal_Siegel_FinrankDerivationCardTranscendenceBasis`, `Jacobsthal_Siegel_GenericNormalization`, `Jacobsthal_Siegel_GradedIdealQuotient`, `Jacobsthal_Siegel_HilbertSeries`, `Jacobsthal_Siegel_HomogeneousDeformation`, `Jacobsthal_Siegel_Homogenize`, `Jacobsthal_Siegel_IdealPowLayer`, `Jacobsthal_Siegel_InvariantDerivation`, `Jacobsthal_Siegel_InvariantJetLinearMap`, `Jacobsthal_Siegel_LaurentEvalOne`, `Jacobsthal_Siegel_LinearVariableBasis`, `Jacobsthal_Siegel_LocalFractionAlgebra`, `Jacobsthal_Siegel_LocalQuotientEquiv`, `Jacobsthal_Siegel_LogarithmicForm`, `Jacobsthal_Siegel_NormalizationPresentationLocalEquiv`, `Jacobsthal_Siegel_ParameterIdeal`, `Jacobsthal_Siegel_PolynomialBox`, `Jacobsthal_Siegel_PolynomialLaurent`, `Jacobsthal_Siegel_PolynomialLinearCoefficients`, `Jacobsthal_Siegel_RectangleThreshold`, `Jacobsthal_Siegel_ResidueTensorQuotientAlgEquiv`, `Jacobsthal_Siegel_TorusDerivationOverRat`, `Jacobsthal_Siegel_TorusEvalOne`, `Jacobsthal_Sieve_AlignedPrimeCongruence`, `Jacobsthal_Sieve_EulerProductRatio`, `Jacobsthal_Sieve_ResidueCountDifference`, `Jacobsthal_Sieve_SurvivorResidueShift`, `Jacobsthal_Sieve_UniformExponentialOccupation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ247J007`; the statements `OAI_Erdos970_ErdosRandomVariance_stable_source_chebyshev_jb247`, `OAI_Erdos970_ErdosRichLine_integer_polynomial_rich_line_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_moving_weighted_pair_lower_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_interval_slack_jb247`, `OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247`, `OAI_Erdos970_ErdosVarianceUniformMoments_uniform_density_inverse_jb247`, `OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247`, `OAI_Erdos970_EulerWeightedLower_weightedSmallSum_eventually_uniform_jb247`, `OAI_Erdos970_NumberTheoryLean_RealFundamentalSieve_fundamental_lemma_jb247`, `OAI_Erdos970_WeightedTorusJets_Geometry_DegreeBezout_coefficient_localization_finrank_le_pow_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.derivativeStageIdeal_graded_length_lower_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247` and `OAI_Erdos970_WeightedTorusJets_Geometry_uniform_rectangular_multiplicity_jb247`; the proofs of `OAI_Erdos970_ErdosRandomVariance_stable_source_chebyshev_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_moving_subbin_prime_lower_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_interval_slack_jb247`, `OAI_Erdos970_EulerWeightedLower_weightedSmallSum_eventually_uniform_jb247` and `OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247`.
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

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace NumberTheoryLean.ReciprocalGapExposure
attribute [local instance] Classical.propDecidable

noncomputable def potential (a r : ℝ) : ℝ := min (1/r) (1/a)

end NumberTheoryLean.ReciprocalGapExposure



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EvenInverseBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightedGapTail

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable def tailSeries (c : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 3 * Real.exp (-c * ((n : ℝ) + 1))

noncomputable def tailBudget (C : ℝ≥0∞) (c : ℝ) (N : ℕ) : ℝ≥0∞ :=
  C * ∑' k : ℕ, ENNReal.ofReal (tailSeries c (k + N))

noncomputable def binCoefficient (c : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 2 * Real.exp (-c * ((n : ℝ) + 1))

end NumberTheoryLean.WeightedGapTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PrefixCompletions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable

noncomputable def suffixPrimes (P : Finset ℕ) (pre : List ℕ) : Finset ℕ :=
  P.filter (fun q => ∀ p ∈ pre,q < p)

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceCutoffRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ReferenceCutoffRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open ReferencePruning

def Above (P Q : Finset ℕ) : Prop := ∀ p ∈ P,∀ q ∈ Q,q<p

end NumberTheoryLean.ReferenceCutoffRecurrence

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

noncomputable def childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) (p : ι) : Finset α := by
  classical
  exact C.filter fun x => bad p x ∧ ∀ q ∈ P, q < p → ¬ bad q x

omit [DecidableEq α] in
@[simp] theorem mem_childCell {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {p : ι} {x : α} :
    x ∈ childCell C P bad p ↔
      x ∈ C ∧ bad p x ∧ ∀ q ∈ P, q < p → ¬ bad q x := by
  classical
  simp [childCell]

end NumberTheoryLean.SievePartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformFailureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.UniformFailureBudget

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def upperDisplacement (S mesh : ℝ) (N : ℕ) : ℝ :=
  (S+1)*(Real.exp (4*(N:ℝ)*mesh)-1)

end NumberTheoryLean.UniformFailureBudget

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SourceTailBudget

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable def failureBudget (A c κ w : ℝ) : ℝ := (A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))

end NumberTheoryLean.SourceTailBudget

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

variable {α : Type*} [MeasurableSpace α]

noncomputable def goodKernel (K : Kernel α α) {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : Kernel α α := K.restrict hBad.compl

instance goodKernel_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) : IsSFiniteKernel (goodKernel K hBad) := by
  unfold goodKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.SubMarkovFlagPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceThresholdCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SourceThresholdCoupling
open _root_.Set _root_.MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

variable {w ell S : ℝ}

noncomputable def thresholdPerturbation (mesh : ℝ) (N : ℕ) : ℝ :=
  3*mesh+3*(Real.exp (4*((N:ℝ)+1)*mesh)-1)

end NumberTheoryLean.SourceThresholdCoupling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_UniformExponentialOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.UniformExponentialOccupation

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset

noncomputable def positiveGapEnvelope (c r : ℝ) : ℝ := if 2 ≤ r then Real.exp (-c*r) else 0

end NumberTheoryLean.UniformExponentialOccupation

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



namespace NumberTheoryLean.ReferenceProductErrorBounds

open _root_.Finset

noncomputable def primeError (c w t : ℝ) : ℝ := Real.exp (-c*Real.sqrt (t*Real.log w))

end NumberTheoryLean.ReferenceProductErrorBounds



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeChoiceCoordinateMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.PrimeBinAlignmentMass


noncomputable def mass (P : Finset ℕ) : ℝ := ∑ p ∈ P,(p:ℝ)⁻¹

end NumberTheoryLean.PrimeBinAlignmentMass



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SingletonSubsetMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.SingletonSubsetMass
open PrimeBinAlignmentMass

attribute [local instance] Classical.propDecidable

noncomputable def subsetWeight (s : Finset ℕ) : ℝ := ∏ p ∈ s,(p:ℝ)⁻¹

end NumberTheoryLean.SingletonSubsetMass


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SquarefreeHarmonic
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeDensityBlocks
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

end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_EulerProductRatio
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueCountDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.ProgressionSieve

open scoped BigOperators

def progressionLength (Y z : ℕ) : ℕ := Y / (z + 1) + 1

noncomputable def deletionBudget (Y z : ℕ) : ℝ :=
  255 * (1 + (progressionLength Y z : ℝ) / Real.log (progressionLength Y z))

end NumberTheoryLean.ProgressionSieve



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



namespace NumberTheoryLean.SingletonBinSelection

attribute [local instance] Classical.propDecidable

noncomputable def eraseMultiplicity {n : ℕ} (m : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  fun k => if k=i then 0 else m k
noncomputable def fillSelection {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) : Fin n → Finset ℕ :=
  Function.update f i {p}

end NumberTheoryLean.SingletonBinSelection



namespace NumberTheoryLean.PartitionedSelections

attribute [local instance] Classical.propDecidable

noncomputable def restrictMultiplicity {n : ℕ} (m : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun k => if k∈S then m k else 0
noncomputable def restrictSelection {n : ℕ} (f : Fin n → Finset ℕ) (S : Finset (Fin n)) : Fin n → Finset ℕ :=
  fun k => if k∈S then f k else ∅
noncomputable def joinSelection {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → Finset ℕ) : Fin n → Finset ℕ :=
  fun k => if k∈S then f k else g k

end NumberTheoryLean.PartitionedSelections



namespace NumberTheoryLean.TwoSingletonBins
open SingletonBinSelection

attribute [local instance] Classical.propDecidable

noncomputable def eraseTwo {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  eraseMultiplicity (eraseMultiplicity m i) j
noncomputable def fillTwo {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) (p u : ℕ) : Fin n → Finset ℕ :=
  fillSelection (fillSelection f j u) i p

end NumberTheoryLean.TwoSingletonBins


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConductorCompletedL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section
open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology
open _root_.Filter _root_.Set _root_.Asymptotics

namespace RealCharacterAnalysis

open _root_.Complex

theorem toNat_divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (z : ℂ) :
    Int.toNat (MeromorphicOn.divisor f Set.univ z) = analyticOrderNatAt f z := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ z)]
  unfold analyticOrderNatAt
  cases h : analyticOrderAt f z <;> simp

end RealCharacterAnalysis

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConeMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

noncomputable def coneMap (p : Ideal (MvPolynomial σ K)) :
    MvPolynomial (Option σ) K →ₐ[K] Polynomial (MvPolynomial σ K ⧸ p) :=
  MvPolynomial.aeval (fun o : Option σ => o.elim Polynomial.X
    (fun i => Polynomial.C (Ideal.Quotient.mk p (X i)) * Polynomial.X))

noncomputable def coneIdeal (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (Option σ) K) := RingHom.ker (coneMap p)

@[simp] theorem coneMap_X_none (p : Ideal (MvPolynomial σ K)) :
    coneMap p (X none) = Polynomial.X := by
  simp [coneMap]

@[simp] theorem coneMap_X_some (p : Ideal (MvPolynomial σ K)) (i : σ) :
    coneMap p (X (some i)) =
      Polynomial.C (Ideal.Quotient.mk p (X i)) * Polynomial.X := by
  simp [coneMap]

theorem coneIdeal_isPrime (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (coneIdeal p).IsPrime := RingHom.ker_isPrime (coneMap p)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

open _root_.Polynomial IsLocalRing

theorem polynomial_local_coefficient_prime_map
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (Polynomial.C : A →+* Polynomial A)).map
      (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) =
    (maximalIdeal (Localization.AtPrime p)).map Polynomial.C := by
  rw [← (show p.map (algebraMap A (Localization.AtPrime p)) =
      maximalIdeal (Localization.AtPrime p) from Localization.AtPrime.map_eq_maximalIdeal),
    Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  simp

theorem polynomial_coefficient_denominators_disjoint
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Disjoint ((p.primeCompl.map Polynomial.C : Submonoid (Polynomial A)) : Set (Polynomial A))
      ((p.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha (by simpa using (Ideal.mem_map_C_iff.mp h) 0)

noncomputable def polynomialLocalCoefficientPolyEquiv
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime (p.map (Polynomial.C : A →+* Polynomial A)) ≃ₐ[Polynomial A]
      Localization.AtPrime ((maximalIdeal (Localization.AtPrime p)).map Polynomial.C) := by
  let M : Submonoid (Polynomial A) := p.primeCompl.map Polynomial.C
  let q : Ideal (Polynomial (Localization.AtPrime p)) :=
    (maximalIdeal (Localization.AtPrime p)).map Polynomial.C
  have ht := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M := M) (Localization.AtPrime q) q
  have hq : q = (p.map Polynomial.C).map
      (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) :=
    (polynomial_local_coefficient_prime_map p).symm
  have he := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial (Localization.AtPrime p))
    (show (p.map Polynomial.C).IsPrime from inferInstance)
    (polynomial_coefficient_denominators_disjoint p)
  rw [← hq] at he
  change q.comap (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) =
    p.map Polynomial.C at he
  simp_rw [he] at ht
  exact IsLocalization.algEquiv (p.map Polynomial.C).primeCompl _ _

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

noncomputable def conePolynomialMap :
    MvPolynomial (Option σ) K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  MvPolynomial.aeval (fun o : Option σ => o.elim Polynomial.X
    (fun i => Polynomial.C (X i) * Polynomial.X))

@[simp] theorem conePolynomialMap_X_none :
    conePolynomialMap (X (none : Option σ) : MvPolynomial (Option σ) K) = Polynomial.X := by
  simp [conePolynomialMap]

@[simp] theorem conePolynomialMap_X_some (i : σ) :
    conePolynomialMap (X (some i) : MvPolynomial (Option σ) K) =
      Polynomial.C (X i) * Polynomial.X := by
  simp [conePolynomialMap]

local notation "𝒜" => MvPolynomial σ K
local notation "𝒮" => MvPolynomial (Option σ) K
local notation "𝒰" => Localization.Away (X (none : Option σ) : 𝒮)
local notation "𝒱" => Localization.Away (Polynomial.X : Polynomial 𝒜)

noncomputable def coneAwayForward : 𝒰 →ₐ[K] 𝒱 :=
  IsLocalization.Away.liftAlgHom (X none)
    (f := (IsScalarTower.toAlgHom K (Polynomial 𝒜) 𝒱).comp conePolynomialMap) (by
      change IsUnit (algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap (X none)))
      rw [conePolynomialMap_X_none]
      exact IsLocalization.Away.algebraMap_isUnit (S := 𝒱) (Polynomial.X : Polynomial 𝒜))

noncomputable def coneAwayInverseCoefficients : 𝒜 →ₐ[K] 𝒰 :=
  MvPolynomial.aeval (fun i => algebraMap 𝒮 𝒰 (X (some i)) *
    IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮))

noncomputable def coneAwayBackward : 𝒱 →ₐ[K] 𝒰 :=
  IsLocalization.Away.liftAlgHom Polynomial.X
    (f := Polynomial.aevalTower coneAwayInverseCoefficients (algebraMap 𝒮 𝒰 (X none))) (by
      rw [Polynomial.aevalTower_X]
      exact IsLocalization.Away.algebraMap_isUnit (S := 𝒰) (X (none : Option σ) : 𝒮))

theorem coneAwayForward_algebraMap (a : 𝒮) :
    coneAwayForward (algebraMap 𝒮 𝒰 a) = algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap a) :=
  by simp [coneAwayForward]

theorem coneAwayBackward_algebraMap (a : Polynomial 𝒜) :
    coneAwayBackward (algebraMap (Polynomial 𝒜) 𝒱 a) =
      Polynomial.aevalTower coneAwayInverseCoefficients (algebraMap 𝒮 𝒰 (X none)) a :=
  by simp [coneAwayBackward]

theorem coneAwayForward_invSelf :
    coneAwayForward (IsLocalization.Away.invSelf (X (none : Option σ) : 𝒮) : 𝒰) =
      (IsLocalization.Away.invSelf (Polynomial.X : Polynomial 𝒜) : 𝒱) := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := 𝒱)
    (Polynomial.X : Polynomial 𝒜)).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf]
  have h := congrArg (coneAwayForward : 𝒰 →ₐ[K] 𝒱)
    (IsLocalization.Away.mul_invSelf (S := 𝒰) (X (none : Option σ) : 𝒮))
  rw [map_mul, map_one, coneAwayForward_algebraMap, conePolynomialMap_X_none] at h
  exact h

theorem coneAwayForward_comp_backward :
    (coneAwayForward : 𝒰 →ₐ[K] 𝒱).comp coneAwayBackward = AlgHom.id K 𝒱 := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X : Polynomial 𝒜))
  apply Polynomial.algHom_ext'
  · ext i
    change coneAwayForward (coneAwayBackward
      (algebraMap (Polynomial 𝒜) 𝒱 (Polynomial.C (X i)))) =
        algebraMap (Polynomial 𝒜) 𝒱 (Polynomial.C (X i))
    rw [coneAwayBackward_algebraMap, Polynomial.aevalTower_C]
    rw [show coneAwayInverseCoefficients (X i) = algebraMap 𝒮 𝒰 (X (some i)) *
      IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮) from
        MvPolynomial.aeval_X _ _]
    rw [map_mul, coneAwayForward_algebraMap, coneAwayForward_invSelf,
      conePolynomialMap_X_some, map_mul, mul_assoc,
      IsLocalization.Away.mul_invSelf, mul_one]
  · change coneAwayForward (coneAwayBackward (algebraMap (Polynomial 𝒜) 𝒱 Polynomial.X)) =
      algebraMap (Polynomial 𝒜) 𝒱 Polynomial.X
    rw [coneAwayBackward_algebraMap, Polynomial.aevalTower_X,
      coneAwayForward_algebraMap, conePolynomialMap_X_none]

theorem coneAwayBackward_comp_forward :
    (coneAwayBackward : 𝒱 →ₐ[K] 𝒰).comp coneAwayForward = AlgHom.id K 𝒰 := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X (none : Option σ) : 𝒮))
  ext i
  change coneAwayBackward (coneAwayForward (algebraMap 𝒮 𝒰 (X i))) = algebraMap 𝒮 𝒰 (X i)
  rw [coneAwayForward_algebraMap]
  cases i with
  | none =>
    rw [conePolynomialMap_X_none, coneAwayBackward_algebraMap, Polynomial.aevalTower_X]
  | some i =>
    rw [conePolynomialMap_X_some, coneAwayBackward_algebraMap, map_mul,
      Polynomial.aevalTower_C, Polynomial.aevalTower_X]
    rw [show coneAwayInverseCoefficients (X i) = algebraMap 𝒮 𝒰 (X (some i)) *
      IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮) from
        MvPolynomial.aeval_X _ _]
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮)),
      IsLocalization.Away.mul_invSelf, mul_one]

noncomputable def coneAwayEquiv : 𝒰 ≃ₐ[K] 𝒱 :=
  AlgEquiv.ofAlgHom coneAwayForward coneAwayBackward
    coneAwayForward_comp_backward coneAwayBackward_comp_forward

@[simp] theorem coneAwayEquiv_algebraMap (a : 𝒮) :
    coneAwayEquiv (algebraMap 𝒮 𝒰 a) = algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap a) :=
  coneAwayForward_algebraMap a

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem coneIdeal_eq_comap_polynomial (p : Ideal (MvPolynomial σ K)) :
    coneIdeal p = (p.map Polynomial.C).comap conePolynomialMap := by
  have h : (Polynomial.mapRingHom (Ideal.Quotient.mk p)).comp
      conePolynomialMap.toRingHom = (coneMap p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap, conePolynomialMap]
      rfl
    · intro i
      cases i <;> simp [coneMap, conePolynomialMap]
  calc
    coneIdeal p = RingHom.ker ((Polynomial.mapRingHom (Ideal.Quotient.mk p)).comp
        conePolynomialMap.toRingHom) := by rw [h]; rfl
    _ = (RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk p))).comap
        conePolynomialMap := rfl
    _ = _ := by rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]

theorem polynomial_X_powers_disjoint (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Disjoint ((Submonoid.powers (Polynomial.X : Polynomial (MvPolynomial σ K))) :
      Set (Polynomial (MvPolynomial σ K)))
      ((p.map Polynomial.C : Ideal (Polynomial (MvPolynomial σ K))) :
        Set (Polynomial (MvPolynomial σ K))) := by
  apply (Ideal.disjoint_powers_iff_notMem_of_isPrime Polynomial.X).mpr
  intro h
  have h1 : (1 : MvPolynomial σ K) ∈ p := by simpa using (Ideal.mem_map_C_iff.mp h) 1
  exact (show p.IsPrime from inferInstance).ne_top (p.eq_top_of_isUnit_mem h1 isUnit_one)

theorem polynomialAwayPrime_isPrime (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ((p.map Polynomial.C).map (algebraMap (Polynomial (MvPolynomial σ K))
      (Localization.Away (Polynomial.X : Polynomial (MvPolynomial σ K))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers Polynomial.X) _ _
    inferInstance (polynomial_X_powers_disjoint p)

attribute [local instance] coneIdeal_isPrime polynomialAwayPrime_isPrime

noncomputable def conePolynomialLocalEquiv (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime (coneIdeal p) ≃ₐ[K] Localization.AtPrime (p.map Polynomial.C) := by
  let A := MvPolynomial σ K
  let S := MvPolynomial (Option σ) K
  let U := Localization.Away (X (none : Option σ) : S)
  let V := Localization.Away (Polynomial.X : Polynomial A)
  let q : Ideal (Polynomial A) := p.map Polynomial.C
  have hd := polynomial_X_powers_disjoint p
  let q' := q.map (algebraMap (Polynomial A) V)
  have hq' : q'.comap (algebraMap (Polynomial A) V) = q :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers (Polynomial.X : Polynomial A)) V inferInstance hd
  let e : U ≃ₐ[K] V := coneAwayEquiv
  let p' := q'.comap e.toRingHom
  have hp' : p'.comap (algebraMap S U) = coneIdeal p := by
    change q'.comap (e.toRingHom.comp (algebraMap S U)) = _
    have he : e.toRingHom.comp (algebraMap S U) =
        (algebraMap (Polynomial A) V).comp conePolynomialMap.toRingHom := by
      apply RingHom.ext
      intro f
      exact coneAwayEquiv_algebraMap f
    rw [he, ← Ideal.comap_comap, hq']
    exact (coneIdeal_eq_comap_polynomial p).symm
  let eS : Localization.AtPrime (coneIdeal p) ≃ₐ[S] Localization.AtPrime p' := by
    let : IsLocalization (coneIdeal p).primeCompl (Localization.AtPrime p') := by
      have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers (X (none : Option σ) : S)) (Localization.AtPrime p') p'
      change IsLocalization (p'.comap (algebraMap S U)).primeCompl (Localization.AtPrime p') at h
      simpa only [hp'] using h
    exact IsLocalization.algEquiv (coneIdeal p).primeCompl _ _
  let eB : Localization.AtPrime q ≃ₐ[Polynomial A] Localization.AtPrime q' := by
    let : IsLocalization q.primeCompl (Localization.AtPrime q') := by
      have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers (Polynomial.X : Polynomial A)) (Localization.AtPrime q') q'
      simpa only [hq'] using h
    exact IsLocalization.algEquiv q.primeCompl _ _
  exact ((eS.restrictScalars K).trans
    (Localization.localAlgEquiv p' q' e rfl)).trans (eB.restrictScalars K).symm

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] coneIdeal_isPrime Polynomial.algebra Polynomial.isLocalization

noncomputable def coneLocalEquiv (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime (coneIdeal p) ≃ₐ[K]
      Localization.AtPrime
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C) :=
  (conePolynomialLocalEquiv p).trans
    ((DegreeBezout.polynomialLocalCoefficientPolyEquiv p).restrictScalars K)

end WeightedTorusJets.Geometry

end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_Homogenize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section

section

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

noncomputable def homogenize (f : MvPolynomial σ K) : MvPolynomial (Option σ) K :=
  ∑ i ∈ Finset.range (f.totalDegree + 1),
    X none ^ (f.totalDegree - i) * rename some (homogeneousComponent i f)

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_eval₂_mul
    {R S τ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial τ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (c : R →+* S) (x : τ → S) (t : S) :
    p.eval₂ c (fun i => x i * t) = p.eval₂ c x * t ^ n := by
  classical
  simp only [eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hn : n = ∑ i ∈ d.support, d i := hp.degree_eq_sum_deg_support hd
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hn, mul_assoc]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry



open MvPolynomial

noncomputable def paddedHomogenizedIdeal {ι K σ : Type*} [CommRing K]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ) : Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span (Set.range fun i => (X (none : Option σ)) ^ n i * homogenize (f i))

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

end

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoeffPolynomialEvalMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coeff_polynomial_eval₂_mul
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) (n : ℕ) :
    ((p.eval₂ (Polynomial.C.comp c)
      (fun i => Polynomial.C (x i) * Polynomial.X)).coeff n) =
        (homogeneousComponent n p).eval₂ c x := by
  classical
  have hh (i : ℕ) : (homogeneousComponent i p).eval₂ (Polynomial.C.comp c)
      (fun j => Polynomial.C (x j) * Polynomial.X) =
        Polynomial.C ((homogeneousComponent i p).eval₂ c x) * Polynomial.X ^ i := by
    rw [homogeneous_eval₂_mul (homogeneousComponent_isHomogeneous i p),
      ← MvPolynomial.hom_eval₂]
  conv_lhs => rw [← sum_homogeneousComponent p]
  simp only [eval₂_sum, Polynomial.finsetSum_coeff, hh, Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < p.totalDegree + 1
  · simp [hn]
  · have hdegree : p.totalDegree < n := by omega
    simp [hn, homogeneousComponent_eq_zero n p hdegree]

theorem polynomial_eval₂_homogeneousComponent
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) (n : ℕ) :
    (homogeneousComponent n p).eval₂ (Polynomial.C.comp c)
      (fun i => Polynomial.C (x i) * Polynomial.X) =
        Polynomial.C ((p.eval₂ (Polynomial.C.comp c)
          (fun i => Polynomial.C (x i) * Polynomial.X)).coeff n) * Polynomial.X ^ n := by
  rw [homogeneous_eval₂_mul (homogeneousComponent_isHomogeneous n p),
    ← MvPolynomial.hom_eval₂, coeff_polynomial_eval₂_mul]

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConeMapEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem coneMap_eq_eval₂ (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) :
    coneMap p f = f.eval₂ (Polynomial.C.comp (algebraMap K (MvPolynomial σ K ⧸ p)))
      (fun o : Option σ => Polynomial.C (o.elim 1 (fun i => Ideal.Quotient.mk p (X i))) *
        Polynomial.X) := by
  rw [coneMap, aeval_def]
  have halg : algebraMap K (Polynomial (MvPolynomial σ K ⧸ p)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K ⧸ p)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K ⧸ p) r
  rw [halg]
  congr 1
  funext o
  cases o <;> simp

theorem coneMap_homogeneousComponent (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) (n : ℕ) :
    coneMap p (homogeneousComponent n f) =
      Polynomial.C ((coneMap p f).coeff n) * Polynomial.X ^ n := by
  simp only [coneMap_eq_eval₂, polynomial_eval₂_homogeneousComponent]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coneIdeal_isHomogeneous (p : Ideal (MvPolynomial σ K)) :
    (coneIdeal p).IsHomogeneous (homogeneousSubmodule (Option σ) K) := by
  apply (Ideal.isHomogeneous_iff_forall_subset _ _).mpr
  intro n f hf
  change GradedRing.proj (homogeneousSubmodule (Option σ) K) n f ∈ coneIdeal p
  rw [GradedRing.proj_apply]
  change (MvPolynomial.decomposition.decompose' f n : MvPolynomial (Option σ) K) ∈ coneIdeal p
  rw [MvPolynomial.decomposition.decompose'_apply]
  change coneMap p (homogeneousComponent n f) = 0
  rw [coneMap_homogeneousComponent, show coneMap p f = 0 from hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalQuotientEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open _root_.Polynomial
open Ideal RingTheory.Sequence IsLocalRing
open Ideal RingTheory.Sequence
open scoped Pointwise
open Ideal RingTheory.Sequence
open CategoryTheory Abelian
universe u
open scoped BigOperators

namespace WeightedTorusJets.Deformation

theorem localRingHom_surjective_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    Function.Surjective (Localization.localRingHom (p.comap f) p f rfl) := by
  have : IsLocalization ((p.comap f).primeCompl.map f) (Localization.AtPrime p) := by
    rw [p.map_primeCompl_comap_of_surjective f hf]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (p.comap f).primeCompl
    (Localization.AtPrime (p.comap f)) (Localization.AtPrime p) (g := f) hf

theorem ker_localRingHom_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    RingHom.ker (Localization.localRingHom (p.comap f) p f rfl) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (p.comap f))) := by
  exact IsLocalization.ker_map (Localization.AtPrime p) f
    (p.map_primeCompl_comap_of_surjective f hf)

noncomputable def localQuotientEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    (Localization.AtPrime (p.comap f) ⧸
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (p.comap f)))) ≃+*
        Localization.AtPrime p :=
  (Ideal.quotEquivOfEq (ker_localRingHom_of_surjective f hf p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (localRingHom_surjective_of_surjective f hf p))

theorem localQuotientEquiv_apply_mk_algebraMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] (x : R) :
    localQuotientEquiv f hf p (Ideal.Quotient.mk _
      (algebraMap R (Localization.AtPrime (p.comap f)) x)) =
        algebraMap S (Localization.AtPrime p) (f x) := by
  simp only [localQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, Localization.localRingHom_to_map]

noncomputable def localQuotientAlgEquiv
    {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    (Localization.AtPrime (p.comap f.toRingHom) ⧸
      (RingHom.ker f.toRingHom).map
        (algebraMap R (Localization.AtPrime (p.comap f.toRingHom)))) ≃ₐ[K]
          Localization.AtPrime p :=
  (Ideal.quotientEquivAlgOfEq K (ker_localRingHom_of_surjective f.toRingHom hf p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Localization.localAlgHom (p.comap f.toRingHom) p f rfl)
      (localRingHom_surjective_of_surjective f.toRingHom hf p))

theorem localQuotientAlgEquiv_apply_mk_algebraMap
    {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] (x : R) :
    localQuotientAlgEquiv f hf p (Ideal.Quotient.mk _
      (algebraMap R (Localization.AtPrime (p.comap f.toRingHom)) x)) =
        algebraMap S (Localization.AtPrime p) (f x) := by
  exact localQuotientEquiv_apply_mk_algebraMap f.toRingHom hf p x

open _root_.Polynomial

theorem ker_mvPolynomial_evaluation
    {R σ : Type*} [CommRing R] (a : R) :
    RingHom.ker (MvPolynomial.map (σ := σ) (evalRingHom a) :
      MvPolynomial σ R[X] →+* MvPolynomial σ R) =
        Ideal.span {MvPolynomial.C (σ := σ) (X - C a)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (MvPolynomial.C_dvd_iff_map_hom_eq_zero (evalRingHom a) (X - C a)
    (fun _ => dvd_iff_isRoot.symm) f).symm

noncomputable def mvPolynomialLocalQuotientAlgEquiv
    {R σ : Type*} [CommRing R] (p : Ideal (MvPolynomial σ R)) [p.IsPrime] (a : R) :
    letI : CommRing (Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := inferInstance
    (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))) ⧸
      (Ideal.span {algebraMap (MvPolynomial σ R[X])
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
          (MvPolynomial.C (σ := σ) (X - C a))} :
        Ideal (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))))
          ≃ₐ[R] Localization.AtPrime p := by
  letI : CommRing (Localization.AtPrime
    (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := inferInstance
  have h : (Ideal.span {algebraMap (MvPolynomial σ R[X])
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (MvPolynomial.C (σ := σ) (X - C a))} :
          Ideal (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))) =
      (RingHom.ker (MvPolynomial.map (σ := σ) (evalRingHom a))).map
        (algebraMap (MvPolynomial σ R[X])
          (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))) := by
    rw [ker_mvPolynomial_evaluation, Ideal.map_span]
    simp
  exact (Ideal.quotientEquivAlgOfEq R h).trans
    (localQuotientAlgEquiv (MvPolynomial.mapAlgHom (aeval a))
      (MvPolynomial.map_surjective _ (fun r => ⟨C r, eval_C⟩)) p)

theorem mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap
    {R σ : Type*} [CommRing R] (p : Ideal (MvPolynomial σ R)) [p.IsPrime] (a : R)
    (f : MvPolynomial σ R[X]) :
    mvPolynomialLocalQuotientAlgEquiv p a (Ideal.Quotient.mk _
      (algebraMap (MvPolynomial σ R[X])
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) f)) =
      algebraMap (MvPolynomial σ R) (Localization.AtPrime p) (MvPolynomial.map (evalRingHom a) f) := by
  exact localQuotientAlgEquiv_apply_mk_algebraMap (MvPolynomial.mapAlgHom (aeval a))
    (MvPolynomial.map_surjective _ (fun r => ⟨C r, eval_C⟩)) p f

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

noncomputable def quotientFamilySpecializationAlgEquiv
    {K S R ι : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (J : Ideal S) (e : (S ⧸ J) ≃ₐ[K] R)
    (f : ι → S) (g : ι → R)
    (hfg : ∀ i, e (Ideal.Quotient.mk J (f i)) = g i) :
    ((S ⧸ Ideal.span (Set.range f)) ⧸
      J.map (Ideal.Quotient.mk (Ideal.span (Set.range f)))) ≃ₐ[K]
      R ⧸ Ideal.span (Set.range g) := by
  refine (DoubleQuot.quotQuotEquivCommₐ K (Ideal.span (Set.range f)) J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span (Set.range g) =
    ((Ideal.span (Set.range f)).map (Ideal.Quotient.mk J)).map e.toRingEquiv.toRingHom
  rw [Ideal.map_map, Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, RingHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, hfg i⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, (hfg i).symm.trans h⟩



open _root_.Polynomial

end WeightedTorusJets.Deformation

namespace WeightedTorusJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

noncomputable def polynomialDeformation (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial σ (Polynomial R) :=
  MvPolynomial.C (1 - Polynomial.X) * MvPolynomial.map Polynomial.C (f i) +
    MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ d

theorem polynomialDeformation_at_zero (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (polynomialDeformation f d i) = f i := by
  have hcomp : (Polynomial.evalRingHom (0 : R)).comp Polynomial.C = RingHom.id R := by
    ext r
    simp
  simp [polynomialDeformation, MvPolynomial.map_map, hcomp, MvPolynomial.map_id]

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

open _root_.Polynomial

noncomputable def residueFieldAtLinearAlgEquiv
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) : I.ResidueField ≃ₐ[K] K := by
  have : I.IsMaximal := by
    rw [hI]
    exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
  exact (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (K[X] ⧸ I) I.ResidueField)
    I.bijective_algebraMap_quotient_residueField).symm.trans
      ((Ideal.quotientEquivAlgOfEq K hI).trans (quotientSpanXSubCAlgEquiv a))

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open _root_.Polynomial

theorem specialFiber_prime_comap_C
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K) :
    (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))).comap MvPolynomial.C =
      Ideal.span {X - C a} := by
  ext f
  rw [← ker_evalRingHom a]
  change MvPolynomial.map (evalRingHom a) (MvPolynomial.C f) ∈ p ↔ f.eval a = 0
  rw [MvPolynomial.map_C, ← Ideal.Quotient.eq_zero_iff_mem]
  let g : K →+* MvPolynomial σ K ⧸ p := (Ideal.Quotient.mk p).comp MvPolynomial.C
  change g (f.eval a) = 0 ↔ f.eval a = 0
  exact map_eq_zero_iff g g.injective

@[instance_reducible] noncomputable def parameterLocalAlgebra
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    Algebra (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) :=
  (Localization.localRingHom I (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
    MvPolynomial.C (hI.trans (specialFiber_prime_comap_C p a).symm)).toAlgebra

end WeightedTorusJets.Deformation

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section

open scoped BigOperators

open Module

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

variable {K σ : Type*} [Field K]

def degreePiece (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap

def degreePresentation (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    homogeneousSubmodule σ K n →ₗ[K] degreePiece I n :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.submoduleMap (homogeneousSubmodule σ K n)

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
variable {K σ : Type*} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
theorem homogeneousComponent_mul_of_le {f g : MvPolynomial σ K} {d n : ℕ}
    (hf : f.IsHomogeneous d) (hdn : d ≤ n) :
    homogeneousComponent n (f * g) = f * homogeneousComponent (n - d) g := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_le
    (homogeneousSubmodule σ K) (b := g) hf hdn
  change (decomposition.decompose' (f * g) n : MvPolynomial σ K) =
    f * (decomposition.decompose' g (n - d) : MvPolynomial σ K) at h
  simpa only [decomposition.decompose'_apply] using h

theorem homogeneousComponent_mul_of_lt {f g : MvPolynomial σ K} {d n : ℕ}
    (hf : f.IsHomogeneous d) (hnd : n < d) :
    homogeneousComponent n (f * g) = 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    (homogeneousSubmodule σ K) (b := g) hf (Nat.not_le.mpr hnd)
  change (decomposition.decompose' (f * g) n : MvPolynomial σ K) = 0 at h
  simpa only [decomposition.decompose'_apply] using h

end WeightedTorusJets.Geometry.GradedQuotient

noncomputable section

open scoped BigOperators DirectSum
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial
open scoped DirectSum

variable {K σ : Type*} [Field K] [Finite σ]

open MvPolynomial

def rectangularIdeal {σ : Type u_1} {K : Type u_2}
    [CommRing K] (k : σ → ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i)

theorem mem_rectangularIdeal {σ K : Type*} [CommRing K] (k : σ → ℕ)
    (p : MvPolynomial σ K) :
    p ∈ rectangularIdeal k ↔ ∀ d ∈ p.support, ∃ i, k i ≤ d i := by
  classical
  have h : Set.range (fun i => (X i : MvPolynomial σ K) ^ k i) =
      (fun d => monomial d (1 : K)) '' Set.range (fun i => Finsupp.single i (k i)) := by
    simpa only [X_pow_eq_monomial] using
      Set.range_comp' (fun d => monomial d (1 : K)) (fun i => Finsupp.single i (k i))
  simp only [rectangularIdeal, h, mem_ideal_span_monomial_image, Set.mem_range,
    exists_exists_eq_and, Finsupp.single_le_iff]

theorem rectangularIdeal_restrictScalars {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (rectangularIdeal k : Ideal (MvPolynomial σ K)).restrictScalars K =
      restrictSupport K {d | ∃ i, k i ≤ d i} := by
  ext p
  rw [Submodule.restrictScalars_mem, mem_rectangularIdeal, mem_restrictSupport_iff]
  rfl

theorem isCompl_restrictSupport_compl {σ K : Type*} [CommRing K]
    (s : Set (σ →₀ ℕ)) : IsCompl (restrictSupport K s) (restrictSupport K sᶜ) := by
  have h : IsCompl (Finsupp.supported K K s) (Finsupp.supported K K sᶜ) :=
    ⟨Finsupp.disjoint_supported_supported disjoint_compl_right,
      Finsupp.codisjoint_supported_supported (codisjoint_iff.mpr sup_compl_eq_top)⟩
  have h' := (Submodule.orderIsoMapComap (AddMonoidAlgebra.coeffLinearEquiv K).symm).isCompl h
  simp only [restrictSupport, AddMonoidAlgebra.supported_eq_map]
  exact h'

def rectangularQuotientEquiv {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (MvPolynomial σ K ⧸ rectangularIdeal k) ≃ₗ[K]
      restrictSupport K {d | ∀ i, d i < k i} := by
  have h : {d : σ →₀ ℕ | ∃ i, k i ≤ d i}ᶜ = {d | ∀ i, d i < k i} := by
    ext d
    simp
  exact (Submodule.Quotient.restrictScalarsEquiv K (rectangularIdeal k)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (rectangularIdeal_restrictScalars k)).trans
      ((restrictSupport K {d | ∃ i, k i ≤ d i}).quotientEquivOfIsCompl _
        (h ▸ isCompl_restrictSupport_compl {d | ∃ i, k i ≤ d i})))

def rectangularExponentEquiv {σ : Type*} [Fintype σ] (k : σ → ℕ) :
    {d : σ →₀ ℕ // ∀ i, d i < k i} ≃ (∀ i, Fin (k i)) where
  toFun d i := ⟨d.1 i, d.2 i⟩
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i => (d i).val), fun i => (d i).isLt⟩
  left_inv d := by apply Subtype.ext; ext i; rfl
  right_inv d := by funext i; apply Fin.ext; rfl

def rectangularQuotientBasis {σ K : Type*} [Fintype σ] [CommRing K] (k : σ → ℕ) :
    Module.Basis (∀ i, Fin (k i)) K (MvPolynomial σ K ⧸ rectangularIdeal k) :=
  ((basisRestrictSupport K {d | ∀ i, d i < k i}).reindex
    (rectangularExponentEquiv k)).map (rectangularQuotientEquiv k).symm

open MvPolynomial

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DegreeMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

section
section

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

def degreeMap {I J : Ideal (MvPolynomial σ K)} (hIJ : I ≤ J) (n : ℕ) :
    degreePiece I n →ₗ[K] degreePiece J n where
  toFun x := ⟨Ideal.Quotient.factorₐ K hIJ x, by
    rcases x.property with ⟨p, hp, hpx⟩
    exact ⟨p, hp, by rw [← hpx]; rfl⟩⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)

theorem degreeMap_surjective {I J : Ideal (MvPolynomial σ K)} (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (degreeMap hIJ n) := by
  rintro ⟨x, p, hp, rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I p, p, hp, rfl⟩, rfl⟩

def degreeMul (I : Ideal (MvPolynomial σ K)) {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (n : ℕ) : degreePiece I n →ₗ[K] degreePiece I (d + n) where
  toFun x := ⟨Ideal.Quotient.mk I f * x, by
    rcases x.property with ⟨p, hp, hpx⟩
    refine ⟨f * p, hf.mul hp, ?_⟩
    change Ideal.Quotient.mk I (f * p) = _
    change Ideal.Quotient.mk I p = _ at hpx
    rw [map_mul, hpx]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (mul_smul_comm _ _ _)

theorem homogeneous_mem_sup_span_iff
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f p : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d)
    (hp : p.IsHomogeneous n) (hdn : d ≤ n) :
    p ∈ I ⊔ Ideal.span {f} ↔
      ∃ g : MvPolynomial σ K, g.IsHomogeneous (n - d) ∧ p - f * g ∈ I := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp (by
      simpa only [sup_comm] using h)
    rw [mul_comm a f] at hab
    refine ⟨homogeneousComponent (n - d) a, homogeneousComponent_isHomogeneous _ _, ?_⟩
    have heq : p - f * homogeneousComponent (n - d) a = homogeneousComponent n b := by
      conv_lhs => lhs; rw [← homogeneousComponent_eq_self hp, ← hab]
      rw [map_add, homogeneousComponent_mul_of_le hf hdn]
      simp
    rw [heq]
    exact homogeneousComponent_mem_of_mem hI hb n
  · rintro ⟨g, _, hpg⟩
    rw [← sub_add_cancel p (f * g)]
    exact Ideal.add_mem _ ((le_sup_left : I ≤ I ⊔ Ideal.span {f}) hpg)
      ((le_sup_right : Ideal.span {f} ≤ I ⊔ Ideal.span {f})
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton f))))

theorem homogeneous_mem_sup_span_iff_of_lt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f p : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d)
    (hp : p.IsHomogeneous n) (hnd : n < d) :
    p ∈ I ⊔ Ideal.span {f} ↔ p ∈ I := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp (by
      simpa only [sup_comm] using h)
    rw [mul_comm a f] at hab
    have heq : p = homogeneousComponent n b := by
      rw [← homogeneousComponent_eq_self hp, ← hab, map_add,
        homogeneousComponent_mul_of_lt hf hnd, zero_add]
    rw [heq]
    exact homogeneousComponent_mem_of_mem hI hb n
  · exact fun hpI => (le_sup_left : I ≤ I ⊔ Ideal.span {f}) hpI

theorem ker_degreeMap_eq_range_degreeMul
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) (d + n)) =
      LinearMap.range (degreeMul I hf n) := by
  ext x
  rcases x with ⟨x, p, hp, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have hpJ : p ∈ I ⊔ Ideal.span {f} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h)
    obtain ⟨g, hg, hpg⟩ := (homogeneous_mem_sup_span_iff hI hf hp (Nat.le_add_right d n)).mp hpJ
    have hgn : g.IsHomogeneous n := by simpa using hg
    refine ⟨⟨Ideal.Quotient.mk I g, g, hgn, rfl⟩, Subtype.ext ?_⟩
    change Ideal.Quotient.mk I f * Ideal.Quotient.mk I g = Ideal.Quotient.mk I p
    rw [← map_mul]
    exact (Ideal.Quotient.eq.mpr hpg).symm
  · rintro ⟨y, hy⟩
    rw [← hy]
    apply Subtype.ext
    change Ideal.Quotient.factorₐ K _ (Ideal.Quotient.mk I f * (y : MvPolynomial σ K ⧸ I)) = 0
    rw [map_mul]
    have hfJ : Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_right : Ideal.span {f} ≤ I ⊔ Ideal.span {f}) (Ideal.subset_span (Set.mem_singleton f)))
    change Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f * _ = 0
    rw [hfJ, zero_mul]

def degreeCokernelEquiv
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    (degreePiece I (d + n) ⧸ LinearMap.range (degreeMul I hf n)) ≃ₗ[K]
      degreePiece (I ⊔ Ideal.span {f}) (d + n) :=
  (Submodule.quotEquivOfEq _ _ (ker_degreeMap_eq_range_degreeMul hI hf n).symm).trans
    ((degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) (d + n)).quotKerEquivOfSurjective
      (degreeMap_surjective _ _))

instance degreePiece_finite [Finite σ] (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.Finite K (degreePiece I n) :=
  Module.Finite.of_fg ((homogeneousSubmodule_fg σ K n).map _)

theorem degreeMap_injective_of_lt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d) (hnd : n < d) :
    Function.Injective (degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) n) := by
  apply LinearMap.ker_eq_bot.mp
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hx
    rcases x with ⟨x, p, hp, rfl⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I p = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (homogeneous_mem_sup_span_iff_of_lt hI hf hp hnd).mp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hx)
  · rintro rfl
    exact map_zero _

def degreeEquivOfLt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d) (hnd : n < d) :
    degreePiece I n ≃ₗ[K] degreePiece (I ⊔ Ideal.span {f}) n :=
  LinearEquiv.ofBijective (degreeMap le_sup_left n)
    ⟨degreeMap_injective_of_lt hI hf hnd, degreeMap_surjective _ _⟩

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def quotientMulColon (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    (MvPolynomial σ K ⧸ I.colon {f}) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
  ((I.colon {f}).restrictScalars K).mapQ (I.restrictScalars K)
    (LinearMap.mul K (MvPolynomial σ K) f) (by
      intro p hp
      change f * p ∈ I
      change p ∈ I.colon {f} at hp
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hp)

theorem quotientMulColon_mk (I : Ideal (MvPolynomial σ K)) (f p : MvPolynomial σ K) :
    quotientMulColon I f (Ideal.Quotient.mk (I.colon {f}) p) =
      Ideal.Quotient.mk I (f * p) := rfl

theorem quotientMulColon_injective (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    Function.Injective (quotientMulColon I f) := by
  apply LinearMap.ker_eq_bot.mp
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientMulColon_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx
  · rintro rfl
    exact map_zero _

noncomputable def degreeMulColon (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    degreePiece (I.colon {f}) n →ₗ[K] degreePiece I (d + n) where
  toFun x := ⟨quotientMulColon I f x, by
    rcases x.property with ⟨p, hp, hpx⟩
    refine ⟨f * p, hf.mul hp, ?_⟩
    rw [← hpx]
    rfl⟩
  map_add' x y := Subtype.ext (map_add (quotientMulColon I f)
    (x : MvPolynomial σ K ⧸ I.colon {f}) (y : MvPolynomial σ K ⧸ I.colon {f}))
  map_smul' a x := Subtype.ext (map_smul (quotientMulColon I f) a
    (x : MvPolynomial σ K ⧸ I.colon {f}))

theorem degreeMulColon_injective (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    Function.Injective (degreeMulColon I hf n) := by
  intro x y hxy
  apply Subtype.ext
  exact quotientMulColon_injective I f (congrArg Subtype.val hxy)

theorem degreeMulColon_comp_degreeMap (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    (degreeMulColon I hf n).comp (degreeMap (Ideal.le_colon : I ≤ I.colon {f}) n) =
      degreeMul I hf n := by
  ext x
  rcases x with ⟨x, p, hp, rfl⟩
  exact map_mul (Ideal.Quotient.mk I) f p

theorem range_degreeMulColon (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.range (degreeMulColon I hf n) = LinearMap.range (degreeMul I hf n) := by
  rw [← degreeMulColon_comp_degreeMap I hf n, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (degreeMap_surjective _ _), Submodule.map_top]

theorem colon_isHomogeneous {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (homogeneousSubmodule σ K) := by
  intro n p hp
  change (decomposition.decompose' p n : MvPolynomial σ K) ∈ I.colon {f}
  rw [decomposition.decompose'_apply, Submodule.mem_colon_singleton]
  change homogeneousComponent n p * f ∈ I
  have hfp : f * p ∈ I := by
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hp
  have h := homogeneousComponent_mem_of_mem hI hfp (d + n)
  rw [homogeneousComponent_mul_of_le hf (Nat.le_add_right d n), Nat.add_sub_cancel_left] at h
  simpa only [mul_comm] using h

theorem finrank_degreePiece_sup_span_add_colon [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank K (degreePiece (I ⊔ Ideal.span {f}) n) +
        (if d ≤ n then Module.finrank K (degreePiece (I.colon {f}) (n - d)) else 0) =
      Module.finrank K (degreePiece I n) := by
  split_ifs with hdn
  · have h := (LinearMap.range (degreeMul I hf (n - d))).finrank_quotient_add_finrank
    rw [(degreeCokernelEquiv hI hf (n - d)).finrank_eq,
      ← range_degreeMulColon I hf (n - d),
      LinearMap.finrank_range_of_inj (degreeMulColon_injective I hf (n - d))] at h
    have hindex : d + (n - d) = n := by omega
    rw [hindex] at h
    exact h
  · simpa using (degreeEquivOfLt hI hf (Nat.lt_of_not_ge hdn)).finrank_eq.symm

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

theorem degreePiece_eq_bot_of_variables_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ i : σ, X i ∈ I)
    {n : ℕ} (hn : 0 < n) : degreePiece I n = ⊥ := by
  have hvars : idealOfVars σ K ≤ I := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hI i)
  apply le_antisymm _ bot_le
  rintro x ⟨p, hp, rfl⟩
  change Ideal.Quotient.mk I p = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hvars
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  intro a ha
  exact hp.coeff_eq_zero (by omega)

theorem finrank_degreePiece_eq_zero_of_variables_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ i : σ, X i ∈ I)
    {n : ℕ} (hn : 0 < n) : Module.finrank K (degreePiece I n) = 0 := by
  rw [degreePiece_eq_bot_of_variables_mem I hI hn, finrank_bot]

end WeightedTorusJets.Geometry.GradedQuotient

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R]

local notation "HR" => fun S : PowerSeries R ↦
  ∃ d : ℕ, ∃ p : Polynomial R,
    ((1 : PowerSeries R) - PowerSeries.X) ^ d * S = (p : PowerSeries R)

theorem HilbertRational.polynomial (p : Polynomial R) :
    HR (p : PowerSeries R) := ⟨0, p, by simp⟩

theorem HilbertRational.add {S T : PowerSeries R}
    (hS : HR S) (hT : HR T) : HR (S + T) := by
  obtain ⟨d, p, hp⟩ := hS
  obtain ⟨e, q, hq⟩ := hT
  refine ⟨d + e, (1 - Polynomial.X) ^ e * p + (1 - Polynomial.X) ^ d * q, ?_⟩
  push_cast
  rw [pow_add, mul_add]
  calc
    _ = (1 - PowerSeries.X) ^ e * ((1 - PowerSeries.X) ^ d * S) +
        (1 - PowerSeries.X) ^ d * ((1 - PowerSeries.X) ^ e * T) := by ring
    _ = _ := by rw [hp, hq]

theorem HilbertRational.X_mul {S : PowerSeries R} (hS : HR S) :
    HR (PowerSeries.X * S) := by
  obtain ⟨d, p, hp⟩ := hS
  refine ⟨d, Polynomial.X * p, ?_⟩
  push_cast
  calc
    _ = PowerSeries.X * ((1 - PowerSeries.X) ^ d * S) := by ring
    _ = _ := by rw [hp]

theorem HilbertRational.of_eq_add_X_mul_self {S T : PowerSeries R}
    (hT : HR T) (hST : S = T + PowerSeries.X * S) : HR S := by
  obtain ⟨d, p, hp⟩ := hT
  have hclear : (1 - PowerSeries.X) * S = T := by
    rw [sub_mul, one_mul]
    exact sub_eq_iff_eq_add.mpr hST
  refine ⟨d + 1, p, ?_⟩
  rw [pow_succ, mul_assoc, hclear, hp]

theorem HilbertRational.exists_mul_invOneSubPow {S : PowerSeries R}
    (hS : HR S) :
    ∃ p : Polynomial R, ∃ d : ℕ, S = p * PowerSeries.invOneSubPow R d := by
  obtain ⟨d, p, hp⟩ := hS
  refine ⟨p, d, ?_⟩
  calc
    S = ((PowerSeries.invOneSubPow R d).val * (1 - PowerSeries.X) ^ d) * S := by
      rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.val_inv, one_mul]
    _ = (PowerSeries.invOneSubPow R d).val * p := by rw [mul_assoc, hp]
    _ = _ := mul_comm _ _

theorem hilbertRational_of_noetherian_recurrence
    {A : Type*} [PartialOrder A] [WellFoundedGT A]
    (H : A → PowerSeries R) (P : A → Prop)
    (hstep : ∀ I, P I → HR (H I) ∨
      ∃ J K, I < J ∧ I ≤ K ∧ P J ∧ P K ∧
        H I = H J + PowerSeries.X * H K) :
    ∀ I, P I → HR (H I) := by
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hI
    rcases hstep I hI with h | ⟨J, K, hIJ, hIK, hJ, hK, hrec⟩
    · exact h
    have hJrat := ih J hIJ hJ
    rcases hIK.eq_or_lt with hKeq | hKlt
    · subst K
      exact HilbertRational.of_eq_add_X_mul_self hJrat hrec
    · rw [hrec]
      exact HilbertRational.add hJrat (HilbertRational.X_mul (ih K hKlt hK))

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace Polynomial

open _root_.Polynomial

variable {F : Type*} [Field F] [CharZero F]

theorem coeff_hilbertPoly_succ_top (p : F[X]) (d : ℕ) :
    (hilbertPoly p (d + 1)).coeff d = p.eval 1 / (d.factorial : F) := by
  rw [hilbertPoly_succ]
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_preHilbertPoly_self,
    ← Finset.sum_mul, div_eq_mul_inv]
  congr 1
  simp only [eval_eq_sum, one_pow, mul_one, sum_def]

theorem natDegree_hilbertPoly_succ_le (p : F[X]) (d : ℕ) :
    (hilbertPoly p (d + 1)).natDegree ≤ d := by
  rw [hilbertPoly_succ]
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_smul_le _ _).trans (natDegree_preHilbertPoly F d i).le

theorem natDegree_hilbertPoly_succ_of_eval_one_ne_zero {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) : (hilbertPoly p (d + 1)).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_hilbertPoly_succ_le p d)
  rw [coeff_hilbertPoly_succ_top]
  exact div_ne_zero hp (by exact_mod_cast Nat.factorial_ne_zero d)

theorem leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) :
    (hilbertPoly p (d + 1)).leadingCoeff = p.eval 1 / (d.factorial : F) := by
  rw [leadingCoeff, natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp,
    coeff_hilbertPoly_succ_top]

theorem factorial_mul_leadingCoeff_hilbertPoly_succ {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) :
    (d.factorial : F) * (hilbertPoly p (d + 1)).leadingCoeff = p.eval 1 := by
  rw [leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero hp]
  have hd : (d.factorial : F) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  field_simp

end Polynomial

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HilbertSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators
namespace PowerSeries

open _root_.PowerSeries

variable {F : Type*} [Field F]

theorem exists_reduced_mul_invOneSubPow (p : Polynomial F) (d : ℕ) :
    ∃ q : Polynomial F, ∃ e : ℕ,
      (p * invOneSubPow F d : PowerSeries F) = q * invOneSubPow F e ∧
        (e = 0 ∨ q.eval 1 ≠ 0) := by
  induction d generalizing p with
  | zero => exact ⟨p, 0, rfl, Or.inl rfl⟩
  | succ d ih =>
    by_cases hp : p.eval 1 = 0
    · obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hp
      have hfactor : p = (1 - Polynomial.X) * (-q) := by
        rw [hq]
        simp only [Polynomial.C_1]
        ring
      have hcancel : (p * invOneSubPow F (d + 1) : PowerSeries F) =
          (-q : Polynomial F) * invOneSubPow F d := by
        rw [hfactor, Polynomial.coe_mul, Polynomial.coe_sub,
          Polynomial.coe_one, Polynomial.coe_X]
        calc
          _ = ((-q : Polynomial F) : PowerSeries F) *
              ((1 - _root_.PowerSeries.X) ^ 1 * (invOneSubPow F (d + 1)).val) := by ring
          _ = _ := by rw [one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
      obtain ⟨r, e, hre, he⟩ := ih (-q)
      exact ⟨r, e, hcancel.trans hre, he⟩
    · exact ⟨p, d + 1, rfl, Or.inr hp⟩

end PowerSeries

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def hilbertSeries (I : Ideal (MvPolynomial σ K)) : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ (Module.finrank K (degreePiece I n) : ℚ)

end WeightedTorusJets.Geometry.GradedQuotient

open _root_.Filter

namespace WeightedTorusJets.Geometry

theorem leadingCoeff_pos_of_eventually_nat_eval_nonneg (P : Polynomial ℚ) (hP : P ≠ 0)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 < P.leadingCoeff := by
  by_contra h
  have hneg : P.leadingCoeff < 0 :=
    lt_of_le_of_ne (le_of_not_gt h) (Polynomial.leadingCoeff_ne_zero.mpr hP)
  by_cases hdeg : 0 < P.degree
  · have hlim : Tendsto (fun n : ℕ => P.eval (n : ℚ)) atTop atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hn'⟩ := (hpos.and (hlim.eventually_lt_atBot 0)).exists
    exact hn'.not_ge hn
  · obtain ⟨n, hn⟩ := hpos.exists
    have hconst : P.eval (n : ℚ) = P.leadingCoeff := by
      rw [Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hdeg)]
      simp
    exact hneg.not_ge (hconst ▸ hn)

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem numerator_eval_one_is_integer (S : PowerSeries ℚ)
    (hS : ∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = S.coeff n)
    (q : Polynomial ℚ) (d : ℕ)
    (hclear : (1 - PowerSeries.X) ^ d * S = (q : PowerSeries ℚ)) :
    ∃ z : ℤ, (z : ℚ) = q.eval 1 := by
  classical
  choose a ha using hS
  let T : PowerSeries ℤ := PowerSeries.mk a
  have hT : PowerSeries.map (Int.castRingHom ℚ) T = S := by
    ext n
    simpa only [T, PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom] using ha n
  let U : PowerSeries ℤ := (1 - PowerSeries.X) ^ d * T
  have hU : PowerSeries.map (Int.castRingHom ℚ) U = (q : PowerSeries ℚ) := by
    simpa only [U, map_mul, map_pow, map_sub, map_one, PowerSeries.map_X, hT] using hclear
  refine ⟨∑ n ∈ q.support, U.coeff n, ?_⟩
  rw [Int.cast_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [one_pow, mul_one, PowerSeries.coeff_map, Int.coe_castRingHom,
    Polynomial.coeff_coe] using congrArg (fun P : PowerSeries ℚ => P.coeff n) hU

end WeightedTorusJets.Geometry

end
end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalFractionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section

section

namespace WeightedTorusJets.Deformation

@[instance_reducible] noncomputable def localFractionAlgebra
    {R F : Type*} [CommRing R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) F :=
  (IsLocalization.lift (S := Localization.AtPrime p) (g := algebraMap R F)
    (fun s : p.primeCompl => isUnit_iff_ne_zero.mpr (by
      apply (map_ne_zero_iff (algebraMap R F) (IsFractionRing.injective R F)).mpr
      intro hs
      exact s.property (hs ▸ p.zero_mem)))).toAlgebra

end WeightedTorusJets.Deformation

end

section

open TensorProduct

namespace WeightedTorusJets.Deformation

noncomputable def genericFiberLocalBaseEquiv
    {R A F B : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    [Field F] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    (F ⊗[A] B) ≃ₐ[F] (F ⊗[R] B) := by
  have := IsLocalization.tensorProduct_compatibleSMul M A F B
  exact Algebra.TensorProduct.equivOfCompatibleSMul R A F F B

end WeightedTorusJets.Deformation

open TensorProduct

namespace WeightedTorusJets.Deformation

variable {R A σ ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

noncomputable def mvPolynomialQuotientBaseChange (I : Ideal (MvPolynomial σ R)) :
    A ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[A]
      MvPolynomial σ A ⧸ I.map (MvPolynomial.map (algebraMap R A)) := by
  refine (Algebra.TensorProduct.tensorQuotientEquiv A (MvPolynomial σ R) A I).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R A) ?_)
  change I.map (MvPolynomial.map (algebraMap R A)) =
    (I.map (Algebra.TensorProduct.includeRight (R := R) (A := A)
      (B := MvPolynomial σ R)).toRingHom).map
        (MvPolynomial.algebraTensorAlgEquiv R A).toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp

@[simp]
theorem mvPolynomialQuotientBaseChange_tmul_mk
    (I : Ideal (MvPolynomial σ R)) (a : A) (p : MvPolynomial σ R) :
    mvPolynomialQuotientBaseChange (A := A) I (a ⊗ₜ[R] Ideal.Quotient.mk I p) =
      a • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p) := by
  simp only [mvPolynomialQuotientBaseChange, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ A _).toLinearMap.map_smul a _

noncomputable def mvPolynomialSpanQuotientBaseChange (f : ι → MvPolynomial σ R) :
    A ⊗[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range f)) ≃ₐ[A]
      MvPolynomial σ A ⧸ Ideal.span
        (Set.range (fun i => MvPolynomial.map (algebraMap R A) (f i))) :=
  (mvPolynomialQuotientBaseChange (A := A) (Ideal.span (Set.range f))).trans
    (Ideal.quotientEquivAlgOfEq A (by rw [Ideal.map_span, ← Set.range_comp']))

@[simp]
theorem mvPolynomialSpanQuotientBaseChange_tmul_mk
    (f : ι → MvPolynomial σ R) (a : A) (p : MvPolynomial σ R) :
    mvPolynomialSpanQuotientBaseChange (A := A) f
        (a ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p) =
      a • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p) := by
  simp [mvPolynomialSpanQuotientBaseChange]

@[simp]
theorem mvPolynomialSpanQuotientBaseChange_symm_mk_map
    (f : ι → MvPolynomial σ R) (p : MvPolynomial σ R) :
    (mvPolynomialSpanQuotientBaseChange (A := A) f).symm
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p)) =
      1 ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p := by
  apply (mvPolynomialSpanQuotientBaseChange (A := A) f).injective
  simp

end WeightedTorusJets.Deformation

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantDerivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section


open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

noncomputable def invariantDerivation (c : ι → R) :
    Derivation R (MvPolynomial ι R) (MvPolynomial ι R) :=
  ∑ i, c i • ((MvPolynomial.X i : MvPolynomial ι R) • MvPolynomial.pderiv i)

theorem derivation_sum_apply' {R A M ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (s : Finset ι)
    (D : ι → Derivation R A M) (a : A) : (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Derivation.add_apply, ih]

theorem invariantDerivation_monomial (c : ι → R) (m : ι →₀ ℕ) (r : R) :
    invariantDerivation c (MvPolynomial.monomial m r) =
      (∑ i, c i * (m i : R)) • MvPolynomial.monomial m r := by
  simp only [invariantDerivation, derivation_sum_apply', Derivation.smul_apply, smul_eq_mul,
    MvPolynomial.X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    Finset.sum_smul]

theorem coeff_invariantDerivation (c : ι → R) (f : MvPolynomial ι R) (m : ι →₀ ℕ) :
    (invariantDerivation c f).coeff m = (∑ i, c i * (m i : R)) * f.coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n r =>
      simp only [invariantDerivation_monomial, MvPolynomial.coeff_smul, smul_eq_mul,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst n
        rfl
      · simp
  | add f g hf hg =>
      simp only [Derivation.add_apply, map_add, MvPolynomial.coeff_add, hf, hg, mul_add]

noncomputable def invariantJet (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : MvPolynomial ι R :=
  (invariantDerivation (c 0))^[a 0]
    ((invariantDerivation (c 1))^[a 1]
      ((invariantDerivation (c 2))^[a 2] f))

theorem coeff_iterate_invariantDerivation (c : ι → R) (f : MvPolynomial ι R)
    (m : ι →₀ ℕ) (k : ℕ) :
    ((invariantDerivation c)^[k] f).coeff m =
      (∑ i, c i * (m i : R)) ^ k * f.coeff m := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Function.iterate_succ_apply', coeff_invariantDerivation, hk, pow_succ']
    exact (mul_assoc _ _ _).symm

theorem coeff_invariantJet (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) (m : ι →₀ ℕ) :
    (invariantJet c a f).coeff m =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) * f.coeff m := by
  simp only [invariantJet, coeff_iterate_invariantDerivation, mul_assoc]

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
namespace WeightedTorusJets.Geometry

noncomputable def polynomialBox (K : Type*) [Field K] (N : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  Submodule.span K (Set.range fun n : Fin 4 → Fin N =>
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (n i : ℕ)) 1)



def rectangleJetIdeal {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (b : ℕ) : Ideal R :=
  Ideal.span (jet '' {a | ∀ j, a j ≤ b * t j})


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry



attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_nonZeroDivisors_disjoint
    {B σ : Type*} [CommRing B] [IsDomain B]
    (p : Ideal (MvPolynomial σ B))
    (hp : p.comap MvPolynomial.C = ⊥) :
    Disjoint (((nonZeroDivisors B).map MvPolynomial.C :
      Submonoid (MvPolynomial σ B)) : Set (MvPolynomial σ B)) (p : Set _) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨b, hb, rfl⟩ hbp
  have hz : b = 0 := by
    have hmem : b ∈ p.comap MvPolynomial.C := hbp
    simpa [hp] using hmem
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hz

noncomputable def coefficientLocalizationLocalEquiv
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [((p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Localization.AtPrime p ≃ₐ[MvPolynomial σ B]
      Localization.AtPrime (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))) := by
  let M : Submonoid (MvPolynomial σ B) :=
    (nonZeroDivisors B).map MvPolynomial.C
  let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
  have hM := coefficient_nonZeroDivisors_disjoint p hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M := M) (Localization.AtPrime q) q
  simp_rw [q, IsLocalization.under_map_of_isPrime_disjoint M (MvPolynomial σ F)
      (show p.IsPrime from inferInstance) hM]
    at this
  exact IsLocalization.algEquiv p.primeCompl _ _

theorem kernel_isMaximal_of_algebraic_field
    {F L A : Type*} [Field F] [Field L] [CommRing A]
    [Algebra F L] [Algebra F A] [Algebra.IsAlgebraic F L]
    (f : A →ₐ[F] L) : (RingHom.ker f).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact (Ideal.quotientKerEquivRange f).toMulEquiv.isField
    (Subalgebra.isField_of_algebraic f.range)

theorem coefficient_localization_isMaximal
    {B F L σ : Type*} [CommRing B] [Field F] [Field L]
    [Algebra B F] [IsFractionRing B F] [Algebra F L] [Algebra.IsAlgebraic F L]
    (p : Ideal (MvPolynomial σ B)) (f : MvPolynomial σ F →ₐ[F] L)
    (hp : (RingHom.ker f).comap
      (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal := by
  rw [← hp, IsLocalization.map_under ((nonZeroDivisors B).map MvPolynomial.C)
    (MvPolynomial σ F)]
  exact kernel_isMaximal_of_algebraic_field f

@[instance_reducible] noncomputable def coordinateFractionAlgebra
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) :
    Algebra (FractionRing (MvPolynomial σ K)) L :=
  (IsFractionRing.liftAlgHom (K := FractionRing (MvPolynomial σ K))
    (algebraicIndependent_iff_injective_aeval.2 hx)).toRingHom.toAlgebra

end WeightedTorusJets.Geometry

open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry

def coordinateSplit {K σ : Type*} [CommSemiring K] (s : Set σ) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) := by
  classical
  exact (renameEquiv K ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumComm _ _))).trans
    (sumAlgEquiv K (sᶜ : Set σ) s)

@[simp] theorem coordinateSplit_C {K σ : Type*} [CommSemiring K]
    (s : Set σ) (c : K) : coordinateSplit s (C c) = C (C c) := by
  classical
  simp [coordinateSplit]

@[simp] theorem coordinateSplit_X_mem {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : s) : coordinateSplit (K := K) s (X i) = C (X i) := by
  classical
  simp [coordinateSplit]

@[simp] theorem coordinateSplit_X_compl {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : (sᶜ : Set σ)) : coordinateSplit (K := K) s (X i) = X i := by
  classical
  simp [coordinateSplit]

theorem coordinateSplit_symm_C {K σ : Type*} [CommSemiring K]
    (s : Set σ) (p : MvPolynomial s K) :
    (coordinateSplit s).symm (C p) = rename (Subtype.val : s → σ) p := by
  have he : (coordinateSplit (K := K) s).toAlgHom.comp
      (rename (Subtype.val : s → σ)) =
      IsScalarTower.toAlgHom K (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) := by
    ext i
    simp
  apply (coordinateSplit s).injective
  simpa using congrArg (fun f : MvPolynomial s K →ₐ[K]
    MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) => f p) he.symm

@[simp] theorem coordinateSplit_symm_X_compl {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : (sᶜ : Set σ)) :
    (coordinateSplit (K := K) s).symm (X i) = X (i : σ) := by
  apply (coordinateSplit s).injective
  simp only [AlgEquiv.apply_symm_apply, coordinateSplit_X_compl]

theorem coordinateSplit_comap_coefficients_eq_bot
    {K σ : Type*} [Field K] (s : Set σ) (p : Ideal (MvPolynomial σ K))
    (hs : AlgebraicIndependent K (fun i : s => Ideal.Quotient.mk p (X i))) :
    (p.comap (coordinateSplit s).symm.toRingHom).comap
      (algebraMap (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))) = ⊥ := by
  apply bot_unique
  intro q hq
  change (coordinateSplit s).symm (C q) ∈ p at hq
  rw [coordinateSplit_symm_C] at hq
  apply hs.eq_zero_of_aeval_eq_zero q
  have he : aeval (fun i : s => Ideal.Quotient.mk p (X i)) =
      (Ideal.Quotient.mkₐ K p).comp (rename (Subtype.val : s → σ)) := by
    ext i
    simp
  rw [he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

theorem coordinateSplit_comap_coefficients_eq_bot_of_fractionField
    {K σ : Type*} [Field K] (s : Set σ) (p : Ideal (MvPolynomial σ K))
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (X i)))) :
    (p.comap (coordinateSplit s).symm.toRingHom).comap
      (algebraMap (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))) = ⊥ := by
  apply coordinateSplit_comap_coefficients_eq_bot s p
  exact hs.of_comp (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p)
    (FractionRing (MvPolynomial σ K ⧸ p)))

def coordinateSplitLocalEquiv
    {K σ : Type*} [CommRing K] (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime p ≃ₐ[K]
      Localization.AtPrime (p.comap (coordinateSplit s).symm.toRingHom) :=
  (Localization.localAlgEquiv (p.comap (coordinateSplit s).symm.toRingHom) p
    (coordinateSplit s).symm rfl).symm




def componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (i : σ) :
    FractionRing (MvPolynomial σ K ⧸ p) :=
  algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
    (Ideal.Quotient.mk p (MvPolynomial.X i))

attribute [local instance] MvPolynomial.algebraMvPolynomial

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoordinateLocalizedPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace WeightedTorusJets.Geometry

open scoped AlgebraMonoidAlgebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coordinateLocalizedPrime {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))) :=
  (p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
    (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))

noncomputable def coordinateFractionLocalEquiv {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    Localization.AtPrime p ≃ₐ[K] Localization.AtPrime (coordinateLocalizedPrime s p) := by
  have : ((p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsPrime :=
    ‹(coordinateLocalizedPrime s p).IsPrime›
  letI : IsScalarTower K (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (Localization.AtPrime (coordinateLocalizedPrime s p)) :=
    IsScalarTower.to₁₂₄ K (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)))
      (Localization.AtPrime (coordinateLocalizedPrime s p))
  exact (coordinateSplitLocalEquiv s p).trans
    ((coefficientLocalizationLocalEquiv (F := FractionRing (MvPolynomial s K))
      (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
      (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs)).restrictScalars K)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_residue_injective
    {B σ : Type*} [CommRing B]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Function.Injective (algebraMap B p.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq B (MvPolynomial σ B) p.ResidueField,
    ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
  exact hp

@[instance_reducible] noncomputable def componentCoefficientFractionAlgebra
    {B F σ : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) : Algebra F p.ResidueField :=
  (IsFractionRing.lift (K := F) (coefficient_residue_injective p hp)).toAlgebra

theorem componentCoefficientFractionAlgebra_tower
    {B F σ : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    letI := componentCoefficientFractionAlgebra (F := F) p hp
    IsScalarTower B F p.ResidueField := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (IsFractionRing.lift_algebraMap (K := F) (coefficient_residue_injective p hp) b).symm

theorem component_functionField_finite
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) :
    letI := componentCoefficientFractionAlgebra (F := F) p hp
    Module.Finite F p.ResidueField := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  have hb : Function.Injective (algebraMap B (MvPolynomial σ B ⧸ p)) := by
    intro x y hxy
    apply coefficient_residue_injective p hp
    rw [IsScalarTower.algebraMap_apply B (MvPolynomial σ B ⧸ p) p.ResidueField,
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B ⧸ p) p.ResidueField, hxy]
  let : FaithfulSMul B (MvPolynomial σ B ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective B (MvPolynomial σ B ⧸ p)).mpr hb
  apply Module.finite_of_finrank_pos
  rw [IsFractionRing.finrank_eq B F (MvPolynomial σ B ⧸ p) p.ResidueField]
  exact Module.finrank_pos

theorem coefficient_localization_isMaximal_of_finite
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  let := component_functionField_finite (F := F) p hp
  let M : Submonoid (MvPolynomial σ B) := (nonZeroDivisors B).map MvPolynomial.C
  let g := IsScalarTower.toAlgHom B (MvPolynomial σ B) p.ResidueField
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hyp : (y : MvPolynomial σ B) ∈ p :=
      Ideal.algebraMap_residueField_eq_zero.mp hy
    exact Set.disjoint_left.mp (coefficient_nonZeroDivisors_disjoint p hp) y.property hyp
  let fB : MvPolynomial σ F →ₐ[B] p.ResidueField := IsLocalization.liftAlgHom hu
  let f := fB.extendScalarsOfIsLocalization F (nonZeroDivisors B)
  have he : f.toRingHom.comp (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) =
      algebraMap (MvPolynomial σ B) p.ResidueField := by
    exact IsLocalization.lift_comp hu
  apply coefficient_localization_isMaximal p f
  change (RingHom.ker f.toRingHom).comap
    (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p
  rw [RingHom.comap_ker, he, Ideal.ker_algebraMap_residueField]

end WeightedTorusJets.Geometry.DegreeBezout

noncomputable section

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

def normalizationPresentation
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial τ (MvPolynomial ι K) :=
  e.symm.trans ((renameEquiv K (Equiv.sumComm ι τ)).trans (sumAlgEquiv K τ ι))

@[simp] theorem normalizationPresentation_symm_C_X
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) (i : ι) :
    (normalizationPresentation e).symm (C (X i)) = e (X (Sum.inl i)) := by
  simp [normalizationPresentation]

@[simp] theorem normalizationPresentation_symm_X
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) (j : τ) :
    (normalizationPresentation e).symm (X j) = e (X (Sum.inr j)) := by
  simp [normalizationPresentation]

theorem normalizationPresentation_coefficient_map
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i))))
    (b : MvPolynomial ι K) :
    Ideal.Quotient.mk P ((normalizationPresentation e).symm (C b)) = g b := by
  have h : (Ideal.Quotient.mkₐ K P).comp
      ((normalizationPresentation e).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom K (MvPolynomial ι K)
          (MvPolynomial τ (MvPolynomial ι K)))) = g := by
    ext i
    change Ideal.Quotient.mk P ((normalizationPresentation e).symm (C (X i))) = g (X i)
    rw [normalizationPresentation_symm_C_X]
    exact (hg i).symm
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P) => f b) h

def normalizationPresentationQuotientEquiv
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) :
    let := g.toAlgebra
    (MvPolynomial τ (MvPolynomial ι K) ⧸
      P.comap (normalizationPresentation e).symm.toRingHom) ≃ₐ[MvPolynomial ι K]
      (MvPolynomial σ K ⧸ P) := by
  let := g.toAlgebra
  let q := P.comap (normalizationPresentation e).symm.toRingHom
  let eQ : (MvPolynomial τ (MvPolynomial ι K) ⧸ q) ≃ₐ[K]
      (MvPolynomial σ K ⧸ P) :=
    Ideal.quotientEquivAlg q P (normalizationPresentation e).symm
      (Ideal.map_comap_of_surjective (normalizationPresentation e).symm.toRingHom
        (normalizationPresentation e).symm.surjective P).symm
  refine { eQ.toRingEquiv with commutes' := ?_ }
  intro b
  change eQ (Ideal.Quotient.mk q (C b)) = g b
  change Ideal.Quotient.mk P ((normalizationPresentation e).symm (C b)) = g b
  exact normalizationPresentation_coefficient_map e P g hg b

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ResidueTensorQuotientAlgEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section

section

open TensorProduct

namespace WeightedTorusJets.Deformation

noncomputable def residueTensorQuotientAlgEquiv
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t}) :
    (IsLocalRing.ResidueField A ⊗[A] B) ≃ₐ[K]
      B ⧸ Ideal.span {algebraMap A B t} := by
  refine (((Algebra.TensorProduct.comm A (IsLocalRing.ResidueField A) B).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (IsLocalRing.maximalIdeal A)).symm.restrictScalars A)).restrictScalars K).trans ?_
  apply Ideal.quotientEquivAlgOfEq K
  rw [ht, Ideal.map_span]
  simp

end WeightedTorusJets.Deformation

end

section
namespace WeightedTorusJets.Deformation

open _root_.Polynomial

noncomputable def polynomialDeformationSpecialFiberAlgEquiv
    {K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : σ → MvPolynomial σ K) (d : ℕ) :
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (evalRingHom (0 : K))))
    letI : CommRing S := inferInstance
    let fs := fun i => algebraMap (MvPolynomial σ K[X]) S (polynomialDeformation f d i)
    let I := Ideal.span (Set.range fs)
    let t := algebraMap (MvPolynomial σ K[X]) S (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))
    ((S ⧸ I) ⧸ (Ideal.span {t}).map (Ideal.Quotient.mk I)) ≃ₐ[K]
      (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))) := by
  intro S
  letI : CommRing S := inferInstance
  have he := quotientFamilySpecializationAlgEquiv
    (Ideal.span {algebraMap (MvPolynomial σ K[X]) S
      (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))} : Ideal S)
    (mvPolynomialLocalQuotientAlgEquiv p (0 : K))
    (fun i => algebraMap (MvPolynomial σ K[X]) S (polynomialDeformation f d i))
    (fun i => algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i))
    (fun i => by
      rw [mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap,
        polynomialDeformation_at_zero])
  exact he

end WeightedTorusJets.Deformation
end

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormalizationPresentationLocalEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

noncomputable def normalizationPresentationLocalEquiv
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Localization.AtPrime P ≃ₐ[K]
      Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom) :=
  (Localization.localAlgEquiv (P.comap (normalizationPresentation e).symm.toRingHom) P
    (normalizationPresentation e).symm rfl).symm

end WeightedTorusJets.Geometry.DegreeBezout

open Module TensorProduct

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coefficientLocalizationResidueAlgEquiv
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    [Algebra F p.ResidueField] [IsScalarTower B F p.ResidueField]
    (hp : p.comap MvPolynomial.C = ⊥) :
    p.ResidueField ≃ₐ[F]
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField :=
  (IsLocalRing.ResidueField.mapAlgEquiv
    ((coefficientLocalizationLocalEquiv p hp).restrictScalars B)).extendScalarsOfIsLocalization
      F (nonZeroDivisors B)

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FinrankDerivationCardTranscendenceBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

section
open Module
open scoped RatFunc

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem coordinateSplit_localized_mem_minimalPrimes
    {K σ : Type*} [Field K] (s : Set σ) (I p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes)
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (X i)))) :
    ((p.comap (coordinateSplit s).symm.toRingHom).map
      (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K))))) ∈
    ((I.comap (coordinateSplit s).symm.toRingHom).map
      (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K))))).minimalPrimes := by
  let B := MvPolynomial s K
  let F := FractionRing B
  let A := MvPolynomial (sᶜ : Set σ) B
  let A' := MvPolynomial (sᶜ : Set σ) F
  let p' : Ideal A := p.comap (coordinateSplit s).symm.toRingHom
  let I' : Ideal A := I.comap (coordinateSplit s).symm.toRingHom
  let M : Submonoid A := (nonZeroDivisors B).map MvPolynomial.C
  have hp' : p' ∈ I'.minimalPrimes :=
    Ideal.minimalPrimes_comap_of_surjective (coordinateSplit (K := K) s).symm.surjective hp
  have hcoeff : p'.comap MvPolynomial.C = ⊥ :=
    coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs
  have hdisj : Disjoint (M : Set A) (p' : Set A) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨b, hb, rfl⟩ hbp
    have hz : b = 0 := by
      have hmem : b ∈ p'.comap MvPolynomial.C := hbp
      simpa [hcoeff] using hmem
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hz
  change p'.map (algebraMap A A') ∈ (I'.map (algebraMap A A')).minimalPrimes
  rw [IsLocalization.minimalPrimes_map M]
  change (p'.map (algebraMap A A')).under A ∈ I'.minimalPrimes
  rw [IsLocalization.under_map_of_isPrime_disjoint M A' (show p'.IsPrime from inferInstance) hdisj]
  exact hp'

end WeightedTorusJets.Geometry

end
end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DominantFunctionFieldHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section OriginalSourceGeometryOverlay

noncomputable section

local instance WeightedTorusJets.Geometry.polynomialGradedAlgebra
    (R σ : Type*) [CommSemiring R] :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra

open Module

open CategoryTheory _root_.AlgebraicGeometry

open CategoryTheory _root_.AlgebraicGeometry

open IsLocalRing

open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory

open AlgebraicGeometry TopologicalSpace CategoryTheory

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GenericNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory

open CategoryTheory _root_.AlgebraicGeometry

open MvPolynomial HomogeneousLocalization

namespace WeightedTorusJets.Geometry

def affineProjEval {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : MvPolynomial (Option ι) k →ₐ[k] A :=
  aeval (Option.elim' 1 x)

abbrev affineProjChart (k ι : Type*) [CommRing k] :=
  Away (homogeneousSubmodule (Option ι) k) (X (none : Option ι))

def affineProjChartMap {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : affineProjChart k ι →+* A :=
  (IsLocalization.Away.lift (X (none : Option ι))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval])).comp
    (algebraMap (affineProjChart k ι) (Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k)))

end WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable (k ι : Type u) [CommRing k]

attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra in
noncomputable def polynomialProjToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0)))

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [-instance] polynomialGradedAlgebra in
attribute [local instance] MvPolynomial.gradedAlgebra in

def affineIntoProj {k A ι : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) : Spec (CommRingCat.of A) ⟶ Proj (homogeneousSubmodule (Option ι) k) :=
  Spec.map (CommRingCat.ofHom (affineProjChartMap (k := k) x)) ≫
    Proj.awayι (homogeneousSubmodule (Option ι) k) (X (none : Option ι))
      (show (X (none : Option ι) : MvPolynomial (Option ι) k) ∈
        homogeneousSubmodule (Option ι) k 1 from isHomogeneous_X k (none : Option ι)) (by decide)

end WeightedTorusJets.Geometry

open _root_.Polynomial IsLocalRing TensorProduct

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ParameterIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct

open TensorProduct IsLocalRing

open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def conormalDifferential (I : Ideal A) :
    I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] Ω[A⁄K] :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)).comp
      (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap A (A ⧸ I)))
        Ideal.mk_ker.symm).toLinearMap)

@[simp]
theorem conormalDifferential_toCotangent (I : Ideal A) (x : I) :
    conormalDifferential (K := K) I (I.toCotangent x) =
      1 ⊗ₜ[A] KaehlerDifferential.D K A x.val := by
  simp only [conormalDifferential, LinearMap.extendScalarsOfSurjective_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Ideal.Cotangent.equivOfEq_toCotangent,
    KaehlerDifferential.kerCotangentToTensor_toCotangent]
  rfl

theorem conormalDifferential_injective (I : Ideal A)
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)] :
    Function.Injective (conormalDifferential (K := K) I) := by
  have hi : Function.Injective (KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      (R := K) Ideal.Quotient.mk_surjective).mpr inferInstance
  exact hi.comp (Ideal.Cotangent.equivOfEq I
    (RingHom.ker (algebraMap A (A ⧸ I))) Ideal.mk_ker.symm).injective

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry



variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

noncomputable def localizeDerivation (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) : Derivation R T T :=
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  let d := (Algebra.ofId S T).toLinearMap.compDer D
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

end WeightedTorusJets.Geometry

open scoped BigOperators

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LogarithmicForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct
open TensorProduct IsLocalRing
open scoped TensorProduct
open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {k F ι : Type*} [Field k] [Field F] [Algebra k F] [Fintype ι]

noncomputable def logarithmicForm (c : ι → k) (f : ι → F) :
    KaehlerDifferential k F :=
  ∑ i, (algebraMap k F (c i) * (f i)⁻¹) • KaehlerDifferential.D k F (f i)

noncomputable def logarithmicTangentMap (f : ι → F) :
    Derivation k F F →ₗ[F] (ι → F) where
  toFun D i := (f i)⁻¹ * D (f i)
  map_add' D E := by ext i; simp [mul_add]
  map_smul' a D := by ext i; simp [mul_left_comm]

noncomputable def logarithmicLinearForm (c : ι → k) : (ι → F) →ₗ[F] F :=
  ∑ i, algebraMap k F (c i) • LinearMap.proj i

end WeightedTorusJets.Geometry


end

open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FiniteTypeFieldModelEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section OriginalSourceGeometryOverlay
open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct
noncomputable section
noncomputable section
namespace WeightedTorusJets.Geometry

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

def derivationOnIdeal (D : Derivation K R R) (I : Ideal R) : I →ₗ[R] R ⧸ I where
  toFun x := Ideal.Quotient.mk I (D x)
  map_add' x y := by simp
  map_smul' r x := by
    change Ideal.Quotient.mk I (D (r * x.val)) = r • Ideal.Quotient.mk I (D x.val)
    rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul, add_zero]
    rfl

def derivationCotangent (D : Derivation K R R) (I : Ideal R) :
    I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (derivationOnIdeal D I) (by
    intro x y
    change Ideal.Quotient.mk I (D (x.val * y.val)) = 0
    rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property,
      Ideal.Quotient.eq_zero_iff_mem.mpr y.property]
    simp)

def derivationCotangentResidue (D : Derivation K R R) (I : Ideal R) :
    I.Cotangent →ₗ[R ⧸ I] R ⧸ I where
  toFun := derivationCotangent D I
  map_add' := (derivationCotangent D I).map_add
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    change derivationCotangent D I (r • x) =
      (algebraMap R (R ⧸ I)) r • derivationCotangent D I x
    rw [algebraMap_smul, map_smul]

end WeightedTorusJets.Geometry

open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def derivationAmbientCovector (I : Ideal A) (D : Derivation K A A) :
    (A ⧸ I) ⊗[A] Ω[A⁄K] →ₗ[A ⧸ I] A ⧸ I :=
  ((Algebra.linearMap A (A ⧸ I)).comp D.liftKaehlerDifferential).liftBaseChange (A ⧸ I)

@[simp]
theorem derivationAmbientCovector_tmul_D (I : Ideal A) (D : Derivation K A A) (x : A) :
    derivationAmbientCovector I D (1 ⊗ₜ[A] KaehlerDifferential.D K A x) =
      Ideal.Quotient.mk I (D x) := by
  simp [derivationAmbientCovector, Derivation.liftKaehlerDifferential_comp_D]

theorem range_conormalDifferential (I : Ideal A) :
    LinearMap.range (conormalDifferential (K := K) I) =
      LinearMap.ker (KaehlerDifferential.mapBaseChange K A (A ⧸ I)) := by
  apply Submodule.restrictScalars_injective A (A ⧸ I) _
  change LinearMap.range ((KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)).comp
    (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap A (A ⧸ I)))
      Ideal.mk_ker.symm).toLinearMap) = _
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  exact KaehlerDifferential.range_kerCotangentToTensor K A (A ⧸ I)
    Ideal.Quotient.mk_surjective

noncomputable def residueTangentMap (I : Ideal A) :
    Derivation K (A ⧸ I) (A ⧸ I) →ₗ[A ⧸ I]
      Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K]) :=
  (KaehlerDifferential.mapBaseChange K A (A ⧸ I)).dualMap.comp
    (KaehlerDifferential.linearMapEquivDerivation K (A ⧸ I)).symm.toLinearMap

@[simp]
theorem residueTangentMap_tmul_D (I : Ideal A)
    (D : Derivation K (A ⧸ I) (A ⧸ I)) (x : A) :
    residueTangentMap I D (1 ⊗ₜ[A] KaehlerDifferential.D K A x) =
      D (Ideal.Quotient.mk I x) := by
  change D.liftKaehlerDifferential
    (KaehlerDifferential.mapBaseChange K A (A ⧸ I)
      (1 ⊗ₜ[A] KaehlerDifferential.D K A x)) = _
  simp [Derivation.liftKaehlerDifferential_comp_D]

theorem ker_conormalDual_eq_range_residueTangent (I : Ideal A) [I.IsMaximal] :
    LinearMap.ker (conormalDifferential (K := K) I).dualMap =
      LinearMap.range (residueTangentMap (K := K) I) := by
  let := Ideal.Quotient.field I
  rw [residueTangentMap, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, range_conormalDifferential]

noncomputable def normalQuotientEquivCotangentDual (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)] :
    (Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K]) ⧸
      LinearMap.range (residueTangentMap (K := K) I)) ≃ₗ[A ⧸ I]
        Module.Dual (A ⧸ I) I.Cotangent := by
  letI := Ideal.Quotient.field I
  exact (Submodule.quotEquivOfEq _ _
    (ker_conormalDual_eq_range_residueTangent (K := K) I).symm).trans
      ((conormalDifferential (K := K) I).dualMap.quotKerEquivOfSurjective
        (LinearMap.dualMap_surjective_of_injective (conormalDifferential_injective I)))

@[simp]
theorem normalQuotientEquivCotangentDual_mk (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)]
    (φ : Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K])) :
    normalQuotientEquivCotangentDual (K := K) I (Submodule.Quotient.mk φ) =
      (conormalDifferential (K := K) I).dualMap φ := by
  simp [normalQuotientEquivCotangentDual]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K S ι : Type*} [CommRing K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S]
    [Algebra.FormallyEtale (MvPolynomial ι K) S]

noncomputable def localizedPolynomialKaehlerBasis : Module.Basis ι S Ω[S⁄K] :=
  ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) S)

@[simp]
theorem localizedPolynomialKaehlerBasis_apply (i : ι) :
    localizedPolynomialKaehlerBasis (K := K) (S := S) i =
      KaehlerDifferential.D K S (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) := by
  simp [localizedPolynomialKaehlerBasis, KaehlerDifferential.mvPolynomialBasis_apply]

noncomputable def logarithmicKaehlerBasis
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    Module.Basis ι S Ω[S⁄K] :=
  localizedPolynomialKaehlerBasis.unitsSMul (fun i => (hx i).unit⁻¹)

@[simp]
theorem logarithmicKaehlerBasis_apply
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) (i : ι) :
    logarithmicKaehlerBasis hx i = ((hx i).unit⁻¹ : Sˣ) •
      KaehlerDifferential.D K S (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) := by
  rw [logarithmicKaehlerBasis, Module.Basis.unitsSMul_apply,
    localizedPolynomialKaehlerBasis_apply]

variable {L : Type*} [Field L] [Algebra S L] [Fintype ι]

noncomputable def logarithmicAmbientEquiv
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    Module.Dual L (L ⊗[S] Ω[S⁄K]) ≃ₗ[L] (ι → L) := by
  classical
  exact ((logarithmicKaehlerBasis hx).baseChange L).dualBasis.equivFun

theorem logarithmicAmbientEquiv_apply
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (φ : Module.Dual L (L ⊗[S] Ω[S⁄K])) (i : ι) :
    logarithmicAmbientEquiv hx φ i =
      (algebraMap S L (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))⁻¹ *
        φ (1 ⊗ₜ[S] KaehlerDifferential.D K S
          (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) := by
  simp only [logarithmicAmbientEquiv, Module.Basis.dualBasis_equivFun,
    Module.Basis.baseChange_apply, logarithmicKaehlerBasis_apply]
  rw [Units.smul_def, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
    Algebra.smul_def]
  congr 1
  rw [map_units_inv, (hx i).unit_spec]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field
variable {K S ι : Type*} [Field K] [CommRing S] [Fintype ι]
    [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S]
    [Algebra.FormallyEtale (MvPolynomial ι K) S]

theorem logarithmicAmbientEquiv_residueTangentMap (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K (S ⧸ I) (S ⧸ I)) :
    logarithmicAmbientEquiv hx (residueTangentMap I D) =
      logarithmicTangentMap (fun i => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) D := by
  ext i
  rw [logarithmicAmbientEquiv_apply, residueTangentMap_tmul_D]
  rfl

theorem map_range_residueTangent_logarithmic (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    (LinearMap.range (residueTangentMap (K := K) I)).map
      (logarithmicAmbientEquiv hx).toLinearMap =
      LinearMap.range (logarithmicTangentMap (k := K) (fun i => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext D i
  exact congrFun (logarithmicAmbientEquiv_residueTangentMap I hx D) i

noncomputable def coordinateNormalEquivCotangentDual [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    ((ι → S ⧸ I) ⧸ LinearMap.range (logarithmicTangentMap (k := K)
      (fun i => Ideal.Quotient.mk I (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))))
      ≃ₗ[S ⧸ I] Module.Dual (S ⧸ I) I.Cotangent := by
  have : Algebra.FormallySmooth K S := Algebra.FormallySmooth.comp K (MvPolynomial ι K) S
  have : Algebra.FormallySmooth K (S ⧸ I) := inferInstance
  exact (Submodule.Quotient.equiv _ _ (logarithmicAmbientEquiv hx)
    (map_range_residueTangent_logarithmic I hx)).symm.trans
      (normalQuotientEquivCotangentDual I)

end WeightedTorusJets.Geometry

open Module

end
end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusEvalOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

section

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem isIrreducible_subtype_preimage {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hS : IsIrreducible S) (hSZ : S ⊆ Z) :
    IsIrreducible ((Subtype.val : Z → X) ⁻¹' S) := by
  let := Subtype.irreducibleSpace hS
  let f : S → Z := fun s ↦ ⟨s, hSZ s.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hi := (IrreducibleSpace.isIrreducible_univ S).image f hf.continuousOn
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, Set.mem_univ _, Subtype.ext rfl⟩
  · rintro ⟨y, _, rfl⟩
    exact y.2

def irreducibleClosedSubtypeEmbedding {X : Type*} [TopologicalSpace X] (Z : Set X) :
    {V : TopologicalSpace.IrreducibleCloseds X // (V : Set X) ⊆ Z} ↪o
      TopologicalSpace.IrreducibleCloseds Z :=
  OrderEmbedding.ofMapLEIff
    (fun V ↦ ⟨Subtype.val ⁻¹' (V.1 : Set X),
      isIrreducible_subtype_preimage V.1.isIrreducible V.2,
      V.1.isClosed.preimage continuous_subtype_val⟩)
    fun A _ ↦ ⟨fun h x hx ↦ h (show (⟨x, A.2 hx⟩ : Z) ∈
      Subtype.val ⁻¹' (A.1 : Set X) from hx), fun h _ hx ↦ h hx⟩

end WeightedTorusJets.Geometry

open scoped BigOperators

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RectangleThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets.Geometry

noncomputable def rectangleThreshold (H N : ℝ) (j : Fin 3) : ℝ :=
  32 * H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def coefficientDerivationLinear (σ : Type*) (D : Derivation ℚ A A) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ A :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap D.toLinearMap ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem coefficientDerivationLinear_monomial (σ : Type*) (D : Derivation ℚ A A)
    (d : σ →₀ ℕ) (a : A) :
    coefficientDerivationLinear σ D (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (D a) := by
  classical
  ext e
  change D ((MvPolynomial.monomial d a).coeff e) =
    (MvPolynomial.monomial d (D a)).coeff e
  simp [MvPolynomial.coeff_monomial, apply_ite D]

def quotientDerivation (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) : Derivation ℚ (A ⧸ I) (A ⧸ I) :=
  Derivation.liftOfSurjective (f := Ideal.Quotient.mkₐ ℚ I)
    (Ideal.Quotient.mkₐ_surjective ℚ I)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (hI a (Ideal.Quotient.eq_zero_iff_mem.mp ha)))

end



end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DerivationJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry



noncomputable section

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

def derivationJet (D : Fin 3 → Derivation ℚ A A) (β : Fin 3 → ℕ) (a : A) : A :=
  ((D 0).toLinearMap ^ β 0) (((D 1).toLinearMap ^ β 1) (((D 2).toLinearMap ^ β 2) a))

def derivativeStageIdeal (D : Fin 3 → Derivation ℚ A A) (t : Fin 3 → ℕ)
    (b : ℕ) (F : A) : Ideal A :=
  Ideal.span ((fun β => derivationJet D β F) '' {β | ∀ j, β j ≤ b * t j})

@[simp] theorem derivationJet_zero (D : Fin 3 → Derivation ℚ A A) (a : A) :
    derivationJet D 0 a = a := by
  simp [derivationJet]

end

end WeightedTorusJets.Geometry

noncomputable section

namespace WeightedTorusJets.Geometry

open MvPolynomial

open MvPolynomial

theorem ker_constantCoeff_eq_idealOfVars {σ K : Type*} [CommRing K] :
    RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) = idealOfVars σ K := by
  classical
  ext p
  rw [RingHom.mem_ker, idealOfVars, ← Set.image_univ,
    mem_ideal_span_X_image]
  constructor
  · intro hp d hd
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      exact (mem_support_iff.mp hd) hp
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd0
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro hp
    by_contra h
    obtain ⟨i, _, hi⟩ := hp 0 (mem_support_iff.mpr h)
    exact hi rfl

def quotientAugmentation {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K)) :
    (MvPolynomial σ K ⧸ J) →ₐ[K] K :=
  Ideal.Quotient.liftₐ J (aeval (0 : σ → K)) fun p hp => by
    simpa using hJ hp

@[simp] theorem quotientAugmentation_mk {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K))
    (p : MvPolynomial σ K) :
    quotientAugmentation J hJ (Ideal.Quotient.mk J p) = constantCoeff p := by
  simp [quotientAugmentation]

theorem ker_quotientAugmentation {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K)) :
    RingHom.ker (quotientAugmentation J hJ).toRingHom =
      (idealOfVars σ K).map (Ideal.Quotient.mk J) := by
  rw [← ker_constantCoeff_eq_idealOfVars]
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker]
  change quotientAugmentation J hJ (Ideal.Quotient.mk J p) = 0 ↔ _
  rw [quotientAugmentation_mk, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨q, hq, hpq⟩
    change constantCoeff q = 0 at hq
    have hmem := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hpq
    have hh := hJ hmem
    change constantCoeff (q - p) = 0 at hh
    simpa only [map_sub, hq, zero_sub, neg_eq_zero] using hh

end WeightedTorusJets.Geometry

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusDerivationOverRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section

namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [CharZero K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

noncomputable def torusDerivationOverRat (c : Fin 3 → Fin 4 → K) (j : Fin 3) :
    Derivation ℚ TorusCoordRing TorusCoordRing :=
  (localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
    (invariantDerivation (c j))).restrictScalars ℚ

noncomputable def localTorusDerivationOverRat (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (j : Fin 3) :
    Derivation ℚ (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
  localizeDerivation q.asIdeal.primeCompl (torusDerivationOverRat c j)


end WeightedTorusJets.Geometry

open scoped TensorProduct


open scoped TensorProduct







open Module




open scoped BigOperators







end
end




open scoped BigOperators


open Module


open MvPolynomial


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoefficientSubspaceEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section

section

open scoped BigOperators DirectSum

namespace WeightedTorusJets.Geometry

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    (N : Submodule K M)

theorem graded_quotient_coeLinearMap_injective (hN : N.IsHomogeneous 𝓜) :
    Function.Injective
      (DirectSum.coeLinearMap (fun n => (𝓜 n).map N.mkQ)) := by
  classical
  let 𝓠 := fun n => (𝓜 n).map N.mkQ
  change Function.Injective (DirectSum.coeLinearMap 𝓠)
  suffices hk : ∀ x : ⨁ i, 𝓠 i, DirectSum.coeLinearMap 𝓠 x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hk (x - y) (by simp only [map_sub, hxy, sub_self]))
  intro x hx
  have hxsum : (∑ i ∈ x.support, (x i : M ⧸ N)) = 0 := by
    simpa only [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] using hx
  have hlift (i : ℕ) : ∃ m : M, m ∈ 𝓜 i ∧ N.mkQ m = (x i : M ⧸ N) :=
    (x i).property
  choose m hm hmx using hlift
  have hsum : (∑ i ∈ x.support, m i) ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (∑ i ∈ x.support, m i) = 0
    rw [map_sum]
    simpa only [hmx] using hxsum
  apply DFinsupp.ext
  intro i
  by_cases hi : i ∈ x.support
  · apply Subtype.ext
    change (x i : M ⧸ N) = 0
    rw [← hmx i]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    have hmem := hN i hsum
    have heq : (DirectSum.decompose 𝓜 (∑ j ∈ x.support, m j) i : M) = m i := by
      rw [DirectSum.decompose_sum]
      rw [DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
      rw [Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same 𝓜 (hm i)
      · intro j _ hji
        exact DirectSum.decompose_of_mem_ne 𝓜 (hm j) hji
      · exact fun hnot => (hnot hi).elim
    rwa [heq] at hmem
  · simpa only [DFinsupp.zero_apply] using DFinsupp.notMem_support_iff.mp hi

theorem graded_quotient_coeLinearMap_surjective :
    Function.Surjective
      (DirectSum.coeLinearMap (fun n => (𝓜 n).map N.mkQ)) := by
  classical
  rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
  apply top_unique
  intro x _
  obtain ⟨m, rfl⟩ := N.mkQ_surjective x
  rw [← DirectSum.sum_support_decompose 𝓜 m, map_sum]
  apply Submodule.sum_mem
  intro n _
  apply le_iSup (fun n => (𝓜 n).map N.mkQ) n
  exact Submodule.mem_map_of_mem (DirectSum.decompose 𝓜 m n).property

@[instance_reducible]
noncomputable def gradedQuotientDecomposition (hN : N.IsHomogeneous 𝓜) :
    DirectSum.Decomposition (fun n => (𝓜 n).map N.mkQ) :=
  (show DirectSum.IsInternal (fun n => (𝓜 n).map N.mkQ) from
    ⟨graded_quotient_coeLinearMap_injective 𝓜 N hN,
      graded_quotient_coeLinearMap_surjective 𝓜 N⟩).chooseDecomposition

end WeightedTorusJets.Geometry

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GradedIdealQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open scoped BigOperators DirectSum
namespace WeightedTorusJets.Geometry

@[instance_reducible]
noncomputable def gradedIdealQuotient
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (I : Ideal A) (hI : I.IsHomogeneous 𝓐) :
    GradedAlgebra (fun n => (𝓐 n).map (Ideal.Quotient.mkₐ K I).toLinearMap) where
  __ := gradedQuotientDecomposition 𝓐 (I.restrictScalars K) hI
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨x * y, SetLike.GradedMul.mul_mem hx hy, by simp⟩

end WeightedTorusJets.Geometry

end

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearVariableBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open Module TensorProduct

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial Module

noncomputable section

def linearVariableBasis (K σ : Type*) [Field K] :
    Basis σ K (homogeneousSubmodule σ K 1) :=
  (Basis.span (linearIndependent_X σ K)).map
    (LinearEquiv.ofEq _ _ homogeneousSubmodule_one_eq_span_X.symm)

@[simp] theorem linearVariableBasis_apply {K σ : Type*} [Field K] (i : σ) :
    (linearVariableBasis K σ i : MvPolynomial σ K) = X i := by
  simp [linearVariableBasis]

def polynomialCoordinatesOfLinearBasis
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial σ K :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.trans
    (SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ))

end

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLinearCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section
noncomputable section
namespace WeightedTorusJets.Geometry
open MvPolynomial
theorem mem_vars_square_iff {σ K : Type*} [CommRing K] (p : MvPolynomial σ K) :
    p ∈ idealOfVars σ K ^ 2 ↔ p.coeff 0 = 0 ∧ ∀ i, p.coeff (Finsupp.single i 1) = 0 := by
  rw [mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun i => h (Finsupp.single i 1) (by simp)⟩
  · rintro ⟨h₀, h₁⟩ d hd
    have h : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases h with h | h
    · exact (Finsupp.degree_eq_zero_iff d).mp h ▸ h₀
    · obtain ⟨i, rfl⟩ := (Finsupp.range_single_one (σ := σ) ▸ h :
        d ∈ Set.range (fun i : σ => Finsupp.single i 1))
      exact h₁ i

def polynomialLinearCoefficients {σ K : Type*} [CommRing K] :
    MvPolynomial σ K →ₗ[K] (σ → K) :=
  LinearMap.pi fun i => lcoeff K (Finsupp.single i 1)

@[simp] theorem polynomialLinearCoefficients_apply {σ K : Type*} [CommRing K]
    (p : MvPolynomial σ K) (i : σ) :
    polynomialLinearCoefficients p i = p.coeff (Finsupp.single i 1) := rfl

def varsCotangentCoefficients {σ K : Type*} [CommRing K] :
    (idealOfVars σ K).Cotangent →ₗ[K] (σ → K) :=
  Ideal.Cotangent.lift
    (polynomialLinearCoefficients.comp ((idealOfVars σ K).subtype.restrictScalars K))
    fun x y => by
      ext i
      exact (mem_vars_square_iff (x * y)).mp
        (by rw [pow_two]; exact Ideal.mul_mem_mul x.property y.property) |>.2 i

@[simp] theorem varsCotangentCoefficients_toCotangent {σ K : Type*} [CommRing K]
    (p : idealOfVars σ K) (i : σ) :
    varsCotangentCoefficients ((idealOfVars σ K).toCotangent p) i =
      (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := rfl

def quotientVarsCotangentMap {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) :
    (idealOfVars σ K).Cotangent →ₗ[K]
      ((idealOfVars σ K).map (Ideal.Quotient.mk J)).Cotangent :=
  Ideal.mapCotangent _ _ (Ideal.Quotient.mkₐ K J)
    (fun _ hp => Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hp)

theorem quotientVarsCotangentMap_injective {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2) :
    Function.Injective (quotientVarsCotangentMap J) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := (idealOfVars σ K).toCotangent_surjective x
  change ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent
    ⟨Ideal.Quotient.mk J p, _⟩ = 0 at hx
  have hp₂ := (((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent_eq_zero _).mp hx
  rw [← Ideal.map_pow] at hp₂
  obtain ⟨q, hq, hqp⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective).mp hp₂
  have hd : q - p ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hqp
  apply ((idealOfVars σ K).toCotangent_eq_zero p).mpr
  simpa using (idealOfVars σ K ^ 2).sub_mem hq (hJ hd)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

noncomputable def cotangentEquivOfEqOver (R : Type*) {A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (I J : Ideal A) (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst J
  exact LinearEquiv.refl R _

@[simp] theorem cotangentEquivOfEqOver_toCotangent (R : Type*) {A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (I J : Ideal A) (h : I = J) (p : I) :
    cotangentEquivOfEqOver R I J h (I.toCotangent p) =
      J.toCotangent ⟨p, h ▸ p.property⟩ := by
  subst J
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
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_IdealPowLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

namespace WeightedTorusJets.Geometry



abbrev idealPowLayer {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :=
  ↥(I ^ n) ⧸ (I • ⊤ : Submodule A ↥(I ^ n))


def mapIdealPowLayer {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (I : Ideal A) (J : Ideal B) (hf : I ≤ J.comap f) (n : ℕ) :
    idealPowLayer I n →ₗ[R] idealPowLayer J n := by
  have hpow : I ^ n ≤ (J ^ n).comap f :=
    (pow_le_pow_left' hf n).trans (Ideal.le_comap_pow f n)
  refine Submodule.mapQ ((I • ⊤ : Submodule A ↥(I ^ n)).restrictScalars R)
    ((J • ⊤ : Submodule B ↥(J ^ n)).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := (I ^ n).restrictScalars R)
      (q := (J ^ n).restrictScalars R) hpow
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ (fun _ _ ↦ add_mem)
    rintro a ha ⟨b, hb⟩ _
    change (⟨f (a * b), hpow ((I ^ n).mul_mem_left a hb)⟩ : ↥(J ^ n)) ∈
      J • (⊤ : Submodule B ↥(J ^ n))
    convert!
      (Submodule.smul_mem_smul (M := ↥(J ^ n)) (r := f a) (n := ⟨f b, hpow hb⟩)
        (hf ha) Submodule.mem_top) using 1
    all_goals try with_reducible_and_instances rfl
    ext
    exact map_mul f a b

def mapIdealPowLayerSemilinear {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (hf : I ≤ J.comap f) (n : ℕ) :
    idealPowLayer I n →ₛₗ[Ideal.quotientMap J f hf] idealPowLayer J n := by
  let : Algebra A B := f.toAlgebra
  let g := mapIdealPowLayer (Algebra.ofId A B) I J hf n
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        change g (a • x) = f a • g x
        exact g.map_smul a x }



noncomputable def mapIdealPowLayerQuotientAugmentation {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (n : ℕ) :
    let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
    letI := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) e.symm.toRingHom
    idealPowLayer (m.map (Ideal.Quotient.mk J)) n →ₗ[R ⧸ m]
      idealPowLayer (RingHom.ker q) n := by
  let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
  letI := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) e.symm.toRingHom
  have hf : m.map (Ideal.Quotient.mk J) ≤ (RingHom.ker q).comap f := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).mp ha
    change q (f (Ideal.Quotient.mk J r)) = 0
    exact (RingHom.congr_fun hcomp r).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hq : Function.Surjective q := fun c => ⟨algebraMap (R ⧸ m) B c, q.commutes c⟩
  have hscalar (c : R ⧸ m) :
      Ideal.quotientMap (RingHom.ker q) f hf (e.symm c) =
        algebraMap (R ⧸ m) (B ⧸ RingHom.ker q) c := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    change Ideal.quotientMap (RingHom.ker q) f hf
      ((DoubleQuot.quotQuotEquivQuotOfLE hJm).symm (Ideal.Quotient.mk m r)) = _
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
    apply (q.toRingHom.quotientKerEquivOfSurjective hq).injective
    change q (f (Ideal.Quotient.mk J r)) =
      q (algebraMap (R ⧸ m) B (Ideal.Quotient.mk m r))
    rw [q.commutes]
    exact RingHom.congr_fun hcomp r
  let g := mapIdealPowLayerSemilinear f (m.map (Ideal.Quotient.mk J)) (RingHom.ker q) hf n
  refine { toFun := g, map_add' := g.map_add, map_smul' := ?_ }
  intro c x
  change g (e.symm c • x) = c • g x
  rw [g.map_smulₛₗ, hscalar, algebraMap_smul]

theorem quotientAugmentation_comap_ker_eq {R B : Type*} [CommRing R] [CommRing B]
    (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m) :
    (RingHom.ker q).comap f = m.map (Ideal.Quotient.mk J) := by
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJm]
  change RingHom.ker ((q.toRingHom.comp f).comp (Ideal.Quotient.mk J)) = m
  rw [hcomp, Ideal.mk_ker]

@[simp]
theorem mapIdealPowLayerQuotientAugmentation_mk {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (n : ℕ) (x : ↥((m.map (Ideal.Quotient.mk J)) ^ n)) :
    mapIdealPowLayerQuotientAugmentation J m hJm f q hcomp n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x, (Ideal.le_comap_pow f n)
          ((pow_le_pow_left' (quotientAugmentation_comap_ker_eq J m hJm f q hcomp).ge n)
            x.property)⟩ : ↥((RingHom.ker q) ^ n)) := rfl

end WeightedTorusJets.Geometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLaurent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section

namespace WeightedTorusJets.Geometry
open scoped BigOperators
variable (K ι : Type*) [CommRing K]
local notation "P" => MvPolynomial ι K
local notation "G" => ι →₀ ℤ
local notation "A" => AddMonoidAlgebra K G
local notation "L" => Localization.Away (∏ i : ι, (MvPolynomial.X i : P))

noncomputable def polynomialToLaurent : P →ₐ[K] A :=
  MvPolynomial.aeval fun i => AddMonoidAlgebra.single (Finsupp.single i 1) 1

@[simp] theorem polynomialToLaurent_X (i : ι) :
    polynomialToLaurent K ι (MvPolynomial.X i) =
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 :=
  MvPolynomial.aeval_X _ _

variable [Fintype ι]

noncomputable def localizationToLaurent : L →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (∏ i : ι, (MvPolynomial.X i : P))
    (f := polynomialToLaurent K ι) (by
    simpa [map_prod] using
      (Group.isUnit (Multiplicative.ofAdd (∑ i : ι, Finsupp.single i (1 : ℤ)))).map
        (AddMonoidAlgebra.of K G))

noncomputable def localizedCoordinateUnit (i : ι) : Lˣ :=
  (IsLocalization.Away.isUnit_of_dvd _
    (Finset.dvd_prod_of_mem (fun j : ι => (MvPolynomial.X j : P)) (Finset.mem_univ i))).unit

@[simp] theorem localizedCoordinateUnit_val (i : ι) :
    (localizedCoordinateUnit K ι i : L) = algebraMap P L (MvPolynomial.X i) := by
  rfl

noncomputable def localizedExponentHom : Multiplicative G →* Lˣ :=
  AddMonoidHom.toMultiplicativeLeft
    (Finsupp.liftAddHom fun i =>
      zmultiplesHom (Additive Lˣ) (Additive.ofMul (localizedCoordinateUnit K ι i)))

@[simp] theorem localizedExponentHom_single (i : ι) (n : ℤ) :
    localizedExponentHom K ι (Multiplicative.ofAdd (Finsupp.single i n)) =
      localizedCoordinateUnit K ι i ^ n := by
  simp [localizedExponentHom]

noncomputable def laurentToLocalization : A →ₐ[K] L :=
  AddMonoidAlgebra.lift K L G
    ((Units.coeHom L).comp (localizedExponentHom K ι))

noncomputable def laurentEquivLocalization : A ≃ₐ[K] L :=
  AlgEquiv.ofAlgHom (laurentToLocalization K ι) (localizationToLaurent K ι)
    (by
      ext i
      simp [Algebra.algHom, localizationToLaurent, laurentToLocalization])
    (by
      apply (AddMonoidAlgebra.lift K A G).symm.injective
      ext i
      simp [localizationToLaurent, laurentToLocalization])

@[simp] theorem laurentEquivLocalization_coordinate (i : ι) :
    laurentEquivLocalization K ι (AddMonoidAlgebra.single (Finsupp.single i 1) 1) =
      algebraMap P L (MvPolynomial.X i) := by
  simp [laurentEquivLocalization, laurentToLocalization]

end WeightedTorusJets.Geometry

end

section

namespace WeightedTorusJets.Geometry

noncomputable def localizationResidueAlgEquiv {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    p.ResidueField ≃ₐ[R] IsLocalRing.ResidueField A :=
  IsLocalRing.ResidueField.mapAlgEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A)

@[instance_reducible]
noncomputable def localizationResidueQuotientAlgebra {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
  ((localizationResidueAlgEquiv (A := A) p).toRingHom.comp
    (algebraMap (R ⧸ p) p.ResidueField)).toAlgebra

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantJetLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

noncomputable def invariantJetLinearMap (c : Fin 3 → ι → R) (a : Fin 3 → ℕ) :
    Module.End R (MvPolynomial ι R) where
  toFun := invariantJet c a
  map_add' f g := by
    ext m
    simp only [coeff_invariantJet, MvPolynomial.coeff_add, mul_add]
  map_smul' r f := by
    ext m
    simp only [coeff_invariantJet, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LaurentEvalOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace WeightedTorusJets.Geometry

open scoped BigOperators

variable (K ι : Type*) [CommRing K]

local notation "P" => MvPolynomial ι K
local notation "L" => Localization.Away (∏ i : ι, (MvPolynomial.X i : P))

variable [Fintype ι]

@[simp] theorem laurentEquivLocalization_symm_algebraMap (p : P) :
    (laurentEquivLocalization K ι).symm (algebraMap P L p) =
      polynomialToLaurent K ι p := by
  simp [laurentEquivLocalization, localizationToLaurent]

@[simp] theorem laurentEquivLocalization_polynomial (p : P) :
    laurentEquivLocalization K ι (polynomialToLaurent K ι p) = algebraMap P L p := by
  rw [← laurentEquivLocalization_symm_algebraMap, AlgEquiv.apply_symm_apply]

end WeightedTorusJets.Geometry

end



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



namespace NumberTheoryLean.RegularityDefectPartition
attribute [local instance] Classical.propDecidable

noncomputable def lengthFailure (C B : ℝ) (ps : List ℕ) : Prop := C*Real.log B < (ps.length:ℝ)
end NumberTheoryLean.RegularityDefectPartition


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
open SingletonBinSelection TwoSingletonBins
open PartitionedSelections

attribute [local instance] Classical.propDecidable

noncomputable def aboveIndexSet {n : ℕ} (j : Fin n) : Finset (Fin n) := Finset.univ.filter (fun k => j<k)

end NumberTheoryLean.ParentTailPartition



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_WordIntervalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.WordIntervalGeometry

noncomputable def wordIntervalExponent (w : ℝ) (Y : ℕ) (ps : List ℕ) : ℝ :=
  Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log w

end NumberTheoryLean.WordIntervalGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_SurvivorResidueShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.SurvivorResidueShift
open SievePartition

attribute [local instance] Classical.propDecidable

def successorResidues (a : ℕ → ℕ) (p : ℕ) : ℕ := a p+1

end NumberTheoryLean.SurvivorResidueShift


end Erdos970

end OAI
end



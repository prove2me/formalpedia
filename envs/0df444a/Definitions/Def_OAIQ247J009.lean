-- Prove2me | Definitions.Def_OAIQ247J009
-- name    : OAIQ247J009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:53:16.090706+00:00
-- url     : https://prove2.me/theorems/d9e86f6d-d3d6-4ab2-89f4-dacb60223944
-- title:
--   Definitions bundle OAIQ247J009 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 5 definitions and 1 instance. The definitions and types are `OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.coordinates`, `OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.flagUpdate`, `OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel`, `OAI.Erdos970.WeightedTorusJets.Geometry.rectangularAugmentationCotangentEquiv`, `OAI.Erdos970.WeightedTorusJets.Geometry.rectangularTaylorThree`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: [`Jacobsthal_Paths_FlaggedHarmonicPaths`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/FlaggedHarmonicPaths.lean), [`Jacobsthal_Siegel_PolynomialLinearCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/PolynomialLinearCoefficients.lean), [`Jacobsthal_Siegel_RectangleThreshold`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/RectangleThreshold.lean).
--
--   **Imports.** It imports the bundles `OAIQ247J006` and `OAIQ247J007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ247J010` and `OAIQ247J012`; the statements `OAI_Erdos970_Erdos970Final_source_root_survivor_lower_jb247`, `OAI_Erdos970_ErdosCorrectionLimit_full_limiting_integral_fubini_jb247`, `OAI_Erdos970_ErdosInverseSampleCost_source_expected_cost_small_jb247`, `OAI_Erdos970_ErdosInverseStructured_uniform_no_rich_nonstructured_set_jb247`, `OAI_Erdos970_ErdosInverseTail_sieve_tail_upper_jb247`, `OAI_Erdos970_ErdosLargePatternLaw_uniform_pattern_chebyshev_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_loss_le_scalarTailMass_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_primeHypothetical_uniform_upper_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_intersection_prime_error_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_count_errors_jb247`, `OAI_Erdos970_ErdosVarianceLargeScale_source_large_pair_bound_jb247`, `OAI_Erdos970_ErdosVarianceWeighted_source_raw_hard_prime_mass_jb247`, `OAI_Erdos970_NumberTheoryLean_IteratedLogBudget_separation_jb247`, `OAI_Erdos970_NumberTheoryLean_ReferenceProductLower_reference_product_lower_jb247` and `OAI_Erdos970_WeightedTorusJets_Geometry_local_length_mul_projectiveClosure_degree_le_jb247`; the proofs of `OAI_Erdos970_Erdos970Dependency_MarkedVisits_moving_marked_window_capture_jb247`, `OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_primitive_zero_free_region_jb247`, `OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_sharp_character_exponential_jb247`, `OAI_Erdos970_ErdosInverseTail_sieve_tail_upper_jb247`, `OAI_Erdos970_ErdosLargePatternLaw_uniform_pattern_chebyshev_jb247`, `OAI_Erdos970_ErdosOmissionBindings_actual_third_loss_eq_L3_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_loss_le_scalarTailMass_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_omission_tail_lt_jb247`, `OAI_Erdos970_ErdosRichLine_integer_polynomial_rich_line_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_moving_weighted_pair_lower_jb247`, `OAI_Erdos970_ErdosStoppedArithmetic_primeHypothetical_uniform_upper_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_intersection_prime_error_jb247`, `OAI_Erdos970_ErdosVarianceCommon_source_common_count_errors_jb247`, `OAI_Erdos970_ErdosVarianceSmallPrime_source_small_H_bad_prime_fraction_jb247`, `OAI_Erdos970_ErdosVarianceUniformMoments_uniform_density_inverse_jb247`, `OAI_Erdos970_NumberTheoryLean_IteratedLogBudget_separation_jb247`, `OAI_Erdos970_NumberTheoryLean_RealFundamentalSieve_fundamental_lemma_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.derivativeStageIdeal_graded_length_lower_jb247` and `OAI_Erdos970_WeightedTorusJets_Geometry_local_length_mul_projectiveClosure_degree_le_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
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
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J006
import Definitions.Def_OAIQ247J007

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicPaths
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

noncomputable def flagUpdate (S : ℝ) (b : Bool) (y : CostState) : FlagState :=
  (y, if b = true ∨ S < stateRatio y.1 then true else false)

noncomputable def kernel (v ell S : ℝ) : Kernel FlagState FlagState :=
  ((Kernel.id : Kernel FlagState FlagState).prod
    ((admittedHarmonic v ell).comap (fun z : FlagState => z.1) measurable_fst)).map
      (fun p => flagUpdate S p.1.2 p.2)

instance kernel_isSFinite (v ell S : ℝ) : IsSFiniteKernel (kernel v ell S) := by
  unfold kernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def coordinates (v : ℝ) (z : FlagState) : ExponentState :=
  (currentExponent v z.1, gapValue v z.1, z.2)

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RectangleThreshold
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
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

def rectangularTaylorThree {B : Type*} [CommRing B] (σ : Type*) (k : σ → ℕ)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ) (f : A →+* B) :
    A →+* (MvPolynomial σ B ⧸ rectangularIdeal k) :=
  (rectangularMap k f).comp
    ((rectangularTaylorAlong σ k D₁ i₁).toRingHom.comp
      ((rectangularTaylorAlong σ k D₂ i₂).toRingHom.comp
        ((rectangularTaylorAlong σ k D₃ i₃).toRingHom.comp
          ((Ideal.Quotient.mk (rectangularIdeal k)).comp MvPolynomial.C))))

end

end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLinearCoefficients
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
noncomputable section

namespace WeightedTorusJets.Geometry

open MvPolynomial

noncomputable def rectangularAugmentationCotangentEquiv
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (RingHom.ker (rectangularAugmentation (K := K) k
      (fun i => by have := hk i; omega)).toRingHom).Cotangent ≃ₗ[K] (σ → K) :=
  (cotangentEquivOfEqOver K _ _ (ker_quotientAugmentation _ _)).trans
    (polynomialQuotientCotangentEquiv _ (rectangularIdeal_le_vars_square k hk))



end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end



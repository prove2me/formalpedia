-- Prove2me | Definitions.Def_Q234IR000
-- name    : Q234IR000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:21:23.073762+00:00
-- url     : https://prove2.me/theorems/6dc4e825-4077-44db-b494-ec2f87ec824e
-- title:
--   Definitions bundle Q234IR000 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 482 declarations of OpenAI's Lean: 234 definitions, 6 inductive types or structures, 8 instances and 234 theorems. The definitions and types are `OAI.Invariant233.AffiliatedTransport.closedImageOn`, `OAI.Invariant233.AffiliatedTransport.imageOn`, `OAI.Invariant233.BVDiscrepancy.coefficient`, `OAI.Invariant233.BVDiscrepancy.step`, `OAI.Invariant233.BVDiscrepancy.tail`, `OAI.Invariant233.BVDiscrepancy.unitMeasure`, `OAI.Invariant233.BackgroundBumpData`, `OAI.Invariant233.BlockedProductCoupling.Coordinate`, `OAI.Invariant233.BlockedProductCoupling.ProjectionField`, `OAI.Invariant233.BlockedProductCoupling.Sample`, `OAI.Invariant233.BlockedProductCoupling.blockLaw`, `OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint`, `OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint`, `OAI.Invariant233.BlockedProductCoupling.currentEvent`, `OAI.Invariant233.BlockedProductCoupling.flatSourceEvent`, `OAI.Invariant233.BlockedProductCoupling.flatten`, `OAI.Invariant233.BlockedProductCoupling.futureBad`, `OAI.Invariant233.BlockedProductCoupling.law`, `OAI.Invariant233.BlockedProductCoupling.leftEndpoint`, `OAI.Invariant233.BlockedProductCoupling.parameters`, `OAI.Invariant233.BlockedProductCoupling.projectionDiagonal`, `OAI.Invariant233.BlockedProductCoupling.retainedEvent`, `OAI.Invariant233.BlockedProductCoupling.rightEndpoint`, `OAI.Invariant233.BlockedProductCoupling.sourceBasisZero`, `OAI.Invariant233.BlockedProductCoupling.sourceCoefficientA`, `OAI.Invariant233.BlockedProductCoupling.sourceCoefficientB`, `OAI.Invariant233.BlockedProductCoupling.sourceEvent`, `OAI.Invariant233.BlockedProductCoupling.sourceLaw`, `OAI.Invariant233.BlockedProductCoupling.sourceRetainedEvent`, `OAI.Invariant233.BlockedProductCoupling.toCircle`, `OAI.Invariant233.BlockedProductCoupling.unflatten`, `OAI.Invariant233.CFCLogSeries.term`, `OAI.Invariant233.CharacterLaws.characterMap`, `OAI.Invariant233.CharacterLaws.characterPhaseLaw`, `OAI.Invariant233.CharacterLaws.circleHaar`, `OAI.Invariant233.CharacterLaws.haarPhaseLaw`, `OAI.Invariant233.CharacterLaws.torusHaar`, `OAI.Invariant233.CharacterWeakConvergence.pullbackIntegral`, `OAI.Invariant233.CircleCoupling.DigitMarginalLaws`, `OAI.Invariant233.CircleCoupling.OrderedCouplingIdentities` and 200 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `IrrationalRotation_Analysis_BVDiscrepancy`, `IrrationalRotation_Analysis_BackgroundBumps`, `IrrationalRotation_Analysis_BackgroundCost`, `IrrationalRotation_Analysis_BlockedSourceTransport`, `IrrationalRotation_Analysis_ConcretePredualComplete`, `IrrationalRotation_Analysis_ConcretePredualCore`, `IrrationalRotation_Analysis_ConcretePredualEvaluation`, `IrrationalRotation_Analysis_ConcretePredualRepresentation`, `IrrationalRotation_Analysis_ContinuityCoboundary`, `IrrationalRotation_Analysis_NonnegativeCostIntegral`, `IrrationalRotation_Analysis_ParameterOrbitIdentity`, `IrrationalRotation_Analysis_ParameterSmoothing`, `IrrationalRotation_Analysis_ParameterTails`, `IrrationalRotation_Analysis_RationalGraphTrimming`, `IrrationalRotation_Analysis_SawtoothSmoothing`, `IrrationalRotation_Analysis_UniformQuantization`, `IrrationalRotation_Couplings_CircleCouplingConditioning`, `IrrationalRotation_Couplings_CircleCouplingLaw`, `IrrationalRotation_Couplings_CircleCouplingParameters`, `IrrationalRotation_Couplings_CircleDigitCoupling`, `IrrationalRotation_Couplings_CouplingMarginalBounds`, `IrrationalRotation_Couplings_CouplingMixture`, `IrrationalRotation_Couplings_OneCoordinateCoupling`, `IrrationalRotation_Model_BackgroundData`, `IrrationalRotation_Model_BlockedProductCoupling`, `IrrationalRotation_Model_BlockedSourceEvent`, `IrrationalRotation_Model_CharacterLaw`, `IrrationalRotation_Model_CircleCoupling`, `IrrationalRotation_Model_CircleDigitCoupling`, `IrrationalRotation_Model_CircleDigitMarginals`, `IrrationalRotation_Model_CircleOrderedCoupling`, `IrrationalRotation_Model_CircleParameters`, `IrrationalRotation_Model_CircleRationalGraphs`, `IrrationalRotation_Model_CircleSamplingGraph`, `IrrationalRotation_Model_CircleSamplingStage`, `IrrationalRotation_Model_CircleSmoothing`, `IrrationalRotation_Model_CircleTailAttenuation`, `IrrationalRotation_Model_CircleTruncationEvent`, `IrrationalRotation_Model_CircleWeights`, `IrrationalRotation_Model_CompactTransfer`, `IrrationalRotation_Model_ContinuityCoboundary`, `IrrationalRotation_Model_ContinuousConstruction`, `IrrationalRotation_Model_CouplingMarginalBounds`, `IrrationalRotation_Model_CouplingMixture`, `IrrationalRotation_Model_Diagonal`, `IrrationalRotation_Model_DiagonalGauge`, `IrrationalRotation_Model_Fejer`, `IrrationalRotation_Model_FiniteKernelMixture`, `IrrationalRotation_Model_MixedRadix`, `IrrationalRotation_Model_MixedRadixCircle`, `IrrationalRotation_Model_OneCoordinateCoupling`, `IrrationalRotation_Model_ParameterCircleOperator`, `IrrationalRotation_Model_ParameterCircleWeights`, `IrrationalRotation_Model_ParameterSmoothing`, `IrrationalRotation_Model_ProductCocycle`, `IrrationalRotation_Model_ProductCoupling`, `IrrationalRotation_Model_ProductCouplingCircle`, `IrrationalRotation_Model_ProductScales`, `IrrationalRotation_Model_RationalGraphTrimming`, `IrrationalRotation_Model_RotationMeasurable`, `IrrationalRotation_Model_SawtoothSmoothing`, `IrrationalRotation_Model_StrictPhase`, `IrrationalRotation_Model_TrialSampling`, `IrrationalRotation_Model_TrimmedCircleSamplingGraph`, `IrrationalRotation_Model_UniformQuantization`, `IrrationalRotation_Model_UnrestrictedDiagonal`, `IrrationalRotation_Model_VectorTraceState`, `IrrationalRotation_Operators_AffiliatedTransportSupplement`, `IrrationalRotation_Operators_OperatorCompactTransfer`, `IrrationalRotation_Product_CoordinateSwap`, `IrrationalRotation_Rotation_AnalyticWeightBridge`, `IrrationalRotation_Rotation_CircleBackgroundBumps`, `IrrationalRotation_Rotation_CircleBackgroundCost`, `IrrationalRotation_Rotation_CircleCocycle`, `IrrationalRotation_Rotation_CircleCurrentBlockEvent`, `IrrationalRotation_Rotation_CircleFutureEndpointLoss`, `IrrationalRotation_Rotation_CircleKernelConvolution`, `IrrationalRotation_Rotation_CircleOrderedTransfer`, `IrrationalRotation_Rotation_CircleParameterBlocks`, `IrrationalRotation_Rotation_CircleQuantizedMarginals`, `IrrationalRotation_Rotation_CircleRationalGraphApproximants`, `IrrationalRotation_Rotation_CircleRepresentative`, `IrrationalRotation_Rotation_CircleSmoothing`, `IrrationalRotation_Rotation_CircleTruncationMass`, `IrrationalRotation_Rotation_CircleWeightSupport`, `IrrationalRotation_Rotation_ContinuousWeightAssembly`, `IrrationalRotation_Rotation_ContinuousWeightOperatorBridge`, `IrrationalRotation_Rotation_DiagonalContinuity`, `IrrationalRotation_Rotation_ExponentialWeight`, `IrrationalRotation_Rotation_FieldDiagonal`, `IrrationalRotation_Rotation_FiniteSupportWeights`, `IrrationalRotation_Rotation_ParameterCircleCocycle`, `IrrationalRotation_Rotation_Rotation`, `IrrationalRotation_Rotation_WeightedGraphMarginals`, `IrrationalRotation_Rotation_WeightedShiftAlgebra`, `IrrationalRotation_Rotation_WeightedShiftPowers`, `IrrationalRotation_Sampling_CharacterWeakConvergence`, `IrrationalRotation_Sampling_CircleCharacterDynamics`, `IrrationalRotation_Sampling_CircleRationalSamplingIndex`, `IrrationalRotation_Sampling_CircleSamplingGraph`, `IrrationalRotation_Sampling_CircleSamplingGraphLimits`, `IrrationalRotation_Sampling_CircleSamplingKernelBridge`, `IrrationalRotation_Sampling_CircleSamplingLp`, `IrrationalRotation_Sampling_MixedRadix`, `IrrationalRotation_Sampling_MixedRadixCircle`, `IrrationalRotation_Sampling_MixedRadixTransport`, `IrrationalRotation_Spectral_CFCLogSeries`.
--
--   **Imports.** It imports the published bundle `Def_IrrationalRotation`.
--
--   **Imported by** (directly, in this split): the bundle `Q234IR003`; the statements `OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order`, `OAI.Invariant233.CircleCoupling.ae_endpointPairLaw_ratio_cap`, `OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap`, `OAI.Invariant233.CircleCoupling.ae_hybridPairLaw_ratio_cap`, `OAI.Invariant233.CircleCoupling.endpoint_absolutelyContinuous`, `OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset`, `OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass`, `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field`, `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass`, `OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections`, `OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation` and `OAI.Invariant233.exists_circle_parameters`; the proofs of `OAI.Invariant233.CircleCoupling.ae_endpointPairLaw_ratio_cap` and `OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation

section
-- module Solutions.Q234_IR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BVDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Invariant233.BVDiscrepancy

def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance instIsProbabilityMeasureRealUnitMeasure : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure]

def tail (a x : ℝ) : ℂ := (Icc a 1).indicator (fun _ => 1) x

def coefficient (f : ℝ → ℂ) (N k : ℕ) : ℂ :=
  if k = 0 then f 0 else f ((k : ℝ) / N) - f (((k - 1 : ℕ) : ℝ) / N)

def step (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), coefficient f N k * tail ((k : ℝ) / N) x

@[simp] lemma coefficient_zero (f : ℝ → ℂ) (N : ℕ) : coefficient f N 0 = f 0 := by
  simp [coefficient]

@[simp] lemma coefficient_succ (f : ℝ → ℂ) (N k : ℕ) :
    coefficient f N (k + 1) = f (((k : ℝ) + 1) / N) - f ((k : ℝ) / N) := by
  simp [coefficient]

end Invariant233.BVDiscrepancy

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BackgroundBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.BackgroundCost

theorem disjoint_support_comp_symm {ι X : Type*} (T : ι → X ≃ X)
    (v : X → ℝ) (s : Set X) (hs : Function.support v ⊆ s)
    (hd : Pairwise (fun i j => Disjoint (T i '' s) (T j '' s))) :
    Pairwise (fun i j => Disjoint
      (Function.support (fun x => v ((T i).symm x)))
      (Function.support (fun x => v ((T j).symm x)))) := by
  have hsub : ∀ i, Function.support (fun x => v ((T i).symm x)) ⊆ T i '' s := by
    intro i x hx
    exact ⟨(T i).symm x, hs hx, (T i).apply_symm_apply x⟩
  intro i j hij
  exact (hd hij).mono (hsub i) (hsub j)

end Invariant233.BackgroundCost

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BackgroundCost
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace Invariant233.BackgroundCost

theorem sum_le_one_of_disjoint_support {ι X : Type*} (s : Finset ι)
    (v : ι → X → ℝ) (hv : ∀ i x, v i x ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (Function.support (v i))
      (Function.support (v j)))) (x : X) :
    (∑ i ∈ s, v i x) ≤ 1 := by
  classical
  by_cases h : ∃ i ∈ s, v i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := h
    have hz : ∀ j ∈ s, j ≠ i → v j x = 0 := by
      intro j _ hji
      by_contra hjx
      exact Set.disjoint_left.mp (hd hji) hjx hix
    rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji)
      (fun hni => False.elim (hni hi))]
    exact hv i x
  · have hz : ∀ i ∈ s, v i x = 0 := by
      intro i hi
      by_contra hix
      exact h ⟨i, hi, hix⟩
    simp only [Finset.sum_eq_zero hz]
    norm_num

theorem average_bounds_of_disjoint_support {ι X : Type*} (s : Finset ι)
    (v : ι → X → ℝ) (hv0 : ∀ i x, 0 ≤ v i x) (hv1 : ∀ i x, v i x ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (Function.support (v i))
      (Function.support (v j)))) {W : ℝ} (hW : 0 < W) (x : X) :
    0 ≤ (∑ i ∈ s, v i x) / W ∧ (∑ i ∈ s, v i x) / W ≤ 1 / W := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hv0 i x) hW.le
  · exact div_le_div_of_nonneg_right
      (sum_le_one_of_disjoint_support s v hv1 hd x) hW.le

theorem continuous_negative_cost {X : Type*} [TopologicalSpace X]
    (w : ℕ → X → ℝ) (c : ℕ → ℝ) (hw : ∀ n, Continuous (w n))
    (hc : Summable c) (hbound : ∀ n x, ‖w n x‖ ≤ c n) :
    Continuous (fun x => ∑' n, w n x) :=
  continuous_tsum hw hc hbound

theorem continuousOn_tsum_of_locally_finite {X : Type*} [TopologicalSpace X]
    (v : ℕ → X → ℝ) (s : Set X) (hv : ∀ n, Continuous (v n))
    (hlocal : ∀ x ∈ s, ∃ t : Finset ℕ,
      ∀ᶠ y in 𝓝 x, ∀ n ∉ t, v n y = 0) :
    ContinuousOn (fun x => ∑' n, v n x) s := by
  intro x hx
  obtain ⟨t, ht⟩ := hlocal x hx
  have hfinite : Continuous (fun y => ∑ n ∈ t, v n y) :=
    continuous_finsetSum t (fun n _ => hv n)
  apply ContinuousAt.continuousWithinAt
  apply hfinite.continuousAt.congr_of_eventuallyEq
  exact ht.mono fun y hy => tsum_eq_sum hy

theorem locally_finite_of_support_shrinks {X : Type*} [MetricSpace X]
    (a : X) (v : ℕ → X → ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n) :
    ∀ x ≠ a, ∃ t : Finset ℕ,
      ∀ᶠ y in 𝓝 x, ∀ n ∉ t, v n y = 0 := by
  intro x hxa
  have hd : 0 < dist x a := dist_pos.mpr hxa
  have he : ∀ᶠ n in atTop, r n < dist x a / 2 :=
    hr.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨Finset.range N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (show 0 < dist x a / 2 by linarith)]
    with y hy
  intro n hn
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  by_contra hv
  have hya := hsupp n y hv
  have hnsmall := hN n hn'
  have htri := dist_triangle x y a
  have hxy : dist x y < dist x a / 2 := by
    simpa [Metric.mem_ball, dist_comm] using hy
  linarith

theorem summable_of_support_shrinks {X : Type*} [MetricSpace X]
    (a : X) (v : ℕ → X → ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n)
    {x : X} (hx : x ≠ a) : Summable (fun n => v n x) := by
  obtain ⟨t, ht⟩ := locally_finite_of_support_shrinks a v r hr hsupp x hx
  exact summable_of_ne_finset_zero (mem_of_mem_nhds ht)

theorem hasSum_background_majorant :
    HasSum (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 2)) (1 / 2) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 4 : ℝ)
  have heq : (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 2)) =
      (fun n : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ n) := by
    funext n
    simp only [pow_add, div_pow, one_pow]
    norm_num
  rw [heq]
  simpa only [show (1 / 4 : ℝ) * (1 - 1 / 2)⁻¹ = 1 / 2 by norm_num] using h

theorem negative_cost_le {X : Type*} (w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) (x : X) :
    (∑' n, w n x) ≤ ∑' n, c n := by
  have hw : Summable (fun n => w n x) :=
    Summable.of_nonneg_of_le (fun n => hw0 n x) (fun n => hwc n x) hc
  exact hw.tsum_le_tsum (fun n => hwc n x) hc

theorem background_cost_ge_half {X : Type*} (v w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hc : Summable c) (hcsum : (∑' n, c n) ≤ 1 / 2)
    (hv0 : ∀ n x, 0 ≤ v n x) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) (x : X) :
    1 / 2 ≤ 1 + (∑' n, v n x) - (∑' n, w n x) := by
  have hp : 0 ≤ ∑' n, v n x := tsum_nonneg (fun n => hv0 n x)
  have hn := (negative_cost_le w c hc hw0 hwc x).trans hcsum
  linarith

theorem background_cost_continuousOn {X : Type*} [MetricSpace X]
    (a : X) (v w : ℕ → X → ℝ) (r c : ℕ → ℝ)
    (hv : ∀ n, Continuous (v n)) (hw : ∀ n, Continuous (w n))
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n)
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) :
    ContinuousOn (fun x => 1 + (∑' n, v n x) - (∑' n, w n x)) {a}ᶜ := by
  have hp : ContinuousOn (fun x => ∑' n, v n x) {a}ᶜ :=
    continuousOn_tsum_of_locally_finite v _ hv
      (fun x hx => locally_finite_of_support_shrinks a v r hr hsupp x hx)
  have hn : Continuous (fun x => ∑' n, w n x) :=
    continuous_negative_cost w c hw hc (fun n x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 n x)] using hwc n x)
  exact (continuousOn_const.add hp).sub hn.continuousOn

theorem tendsto_background_atTop {X : Type*} [TopologicalSpace X]
    (a : X) (v w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hv : ∀ n, Continuous (v n)) (hva : ∀ n, v n a = 1)
    (hv0 : ∀ n x, 0 ≤ v n x)
    (hvs : ∀ x, x ≠ a → Summable (fun n => v n x))
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) :
    Tendsto (fun x => 1 + (∑' n, v n x) - (∑' n, w n x))
      (𝓝[≠] a) atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b + ∑' n, c n)
  have hpartial : Continuous (fun x => ∑ n ∈ Finset.range N, v n x) :=
    continuous_finsetSum _ (fun n _ => hv n)
  have hcenter : (∑ n ∈ Finset.range N, v n a) = (N : ℝ) := by
    simp [hva]
  have he : ∀ᶠ x in 𝓝 a,
      b + (∑' n, c n) ≤ ∑ n ∈ Finset.range N, v n x := by
    apply hpartial.continuousAt.eventually
    exact eventually_ge_nhds (by simpa [hcenter] using hN)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hxa
  have hxa' : x ≠ a := hxa
  have hp : (∑ n ∈ Finset.range N, v n x) ≤ ∑' n, v n x :=
    (hvs x hxa').sum_le_tsum _ (fun n _ => hv0 n x)
  have hn := negative_cost_le w c hc hw0 hwc x
  linarith

end Invariant233.BackgroundCost

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CouplingMarginalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CouplingMarginalBounds

open MeasureTheory

noncomputable def rho (κ m w : ℝ) : ℝ := κ * Real.sqrt (w / m)

noncomputable def diagonalMass (κ m a b t : ℝ) : ℝ :=
  1 - 2 * rho κ m a - 2 * rho κ m b - t / m

noncomputable def uniformDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) : Ω → ℝ :=
  s.indicator (fun _ => (μ.real s)⁻¹)

noncomputable def componentProbabilities (κ m a b t : ℝ) : Fin 5 → ℝ :=
  ![rho κ m a, rho κ m a, rho κ m b, rho κ m b, t / m]

noncomputable def componentVarianceBounds (m a b : ℝ) : Fin 5 → ℝ :=
  ![2 / a, 2 / a, 2 / b, 2 / b, m]

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_nonneg {κ m w : ℝ} (hκ : 0 ≤ κ) : 0 ≤ rho κ m w :=
  mul_nonneg hκ (Real.sqrt_nonneg _)

lemma width_pos {m w : ℝ} (hm : 0 < m) (hw : 1 / m ≤ w) : 0 < w :=
  lt_of_lt_of_le (one_div_pos.mpr hm) hw

lemma sqrt_width_div_le {m w : ℝ} (hm : 0 < m) (hw : 1 / m ≤ w) :
    Real.sqrt (w / m) ≤ w := by
  have hw0 := width_pos hm hw
  apply (Real.sqrt_le_iff).2
  refine ⟨hw0.le, ?_⟩
  apply (div_le_iff₀ hm).2
  have hmw : 1 ≤ w * m := (div_le_iff₀ hm).1 hw
  nlinarith [mul_le_mul_of_nonneg_left hmw hw0.le]

lemma rho_le_mul_width {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w ≤ κ * w :=
  mul_le_mul_of_nonneg_left (sqrt_width_div_le hm hw) hκ

lemma diagonalMass_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    49 / 50 ≤ diagonalMass κ m a b t ∧ diagonalMass κ m a b t ≤ 1 := by
  have hm0 : 0 < m := by linarith
  have hra := rho_le_mul_width hκ0 hm0 ha
  have hrb := rho_le_mul_width hκ0 hm0 hb
  have hra' : rho κ m a ≤ κ / 4 := by nlinarith
  have hrb' : rho κ m b ≤ κ / 4 := by nlinarith
  have htm : t / m ≤ 1 / 100 := by
    apply (div_le_iff₀ hm0).2
    nlinarith
  have htm0 : 0 ≤ t / m := div_nonneg ht0 hm0.le
  have hra0 := rho_nonneg (m := m) (w := a) hκ0
  have hrb0 := rho_nonneg (m := m) (w := b) hκ0
  unfold diagonalMass
  constructor <;> linarith

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CouplingMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

noncomputable def diagonal (μ : Measure X) : Measure (X × X) :=
  μ.map (fun x => (x, x))

noncomputable def mixture (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) : Measure (X × X) :=
  q • diagonal μ + ∑ i, p i • (u i).prod (v i)

noncomputable def intervalLaw (a b : ℝ) : Measure ℝ :=
  volume[|Ico a b]

noncomputable def labelledMixture [MeasurableSpace (Option I)] (μ : Measure X)
    (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X) :
    Measure (Option I × (X × X)) :=
  q • (diagonal μ).map (fun z => (none, z)) +
    ∑ i, p i • ((u i).prod (v i)).map (fun z => (some i, z))

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

instance diagonal_isProbabilityMeasure (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diagonal μ) := by
  unfold diagonal
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma mixture_isProbabilityMeasure (μ : Measure X) [IsProbabilityMeasure μ]
    (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X)
    [∀ i, IsProbabilityMeasure (u i)] [∀ i, IsProbabilityMeasure (v i)]
    (htotal : q + ∑ i, p i = 1) : IsProbabilityMeasure (mixture μ q p u v) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one, Measure.finsetSum_apply]
  simpa using htotal

lemma intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top

lemma map_finsetSum {A B J : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (s : Finset J) (μ : J → Measure A) {f : A → B} (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

omit [Fintype I] in
lemma map_snd_label [MeasurableSpace (Option I)] (ν : Measure (X × X))
    (l : Option I) : (ν.map (fun z => (l, z))).map Prod.snd = ν := by
  rw [Measure.map_map measurable_snd (show Measurable (fun z : X × X => (l, z)) from
    measurable_const.prodMk measurable_id)]
  exact Measure.map_id

lemma labelledMixture_map_snd [MeasurableSpace (Option I)]
    (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X) :
    (labelledMixture μ q p u v).map Prod.snd = mixture μ q p u v := by
  unfold labelledMixture mixture
  rw [Measure.map_add _ _ measurable_snd, map_finsetSum _ _ measurable_snd]
  simp only [Measure.map_smul, map_snd_label]

lemma labelledMixture_isProbabilityMeasure [MeasurableSpace (Option I)]
    (μ : Measure X) [IsProbabilityMeasure μ] (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] (htotal : q + ∑ i, p i = 1) :
    IsProbabilityMeasure (labelledMixture μ q p u v) := by
  constructor
  have := mixture_isProbabilityMeasure μ q p u v htotal
  have h := congrArg (fun ν : Measure (X × X) => ν Set.univ)
    (labelledMixture_map_snd μ q p u v)
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using h

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_OneCoordinateCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

noncomputable def baseLaw : Measure ℝ := intervalLaw 0 1

noncomputable def leftLaw (m a b : ℝ) : Fin 5 → Measure ℝ :=
  ![intervalLaw 0 (1 - a / 2), intervalLaw 0 (a / 2),
    intervalLaw 0 (1 - b / 2), intervalLaw 0 (b / 2), intervalLaw 0 (1 / m)]

noncomputable def rightLaw (m a b : ℝ) : Fin 5 → Measure ℝ :=
  ![intervalLaw (1 - a / 2) 1, intervalLaw (a / 2) 1,
    intervalLaw (1 - b / 2) 1, intervalLaw (b / 2) 1, intervalLaw (1 - 1 / m) 1]

instance labelMeasurableSpace : MeasurableSpace (Option (Fin 5)) := ⊤

noncomputable def labelledLaw (κ m a b t : ℝ) :
    Measure (Option (Fin 5) × (ℝ × ℝ)) :=
  labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw m a b) (rightLaw m a b)

noncomputable def intervalDensity (a b : ℝ) : ℝ → ℝ :=
  uniformDensity baseLaw (Set.Ico a b)

noncomputable def leftDensity (m a b : ℝ) : Fin 5 → ℝ → ℝ :=
  ![intervalDensity 0 (1 - a / 2), intervalDensity 0 (a / 2),
    intervalDensity 0 (1 - b / 2), intervalDensity 0 (b / 2), intervalDensity 0 (1 / m)]

noncomputable def rightDensity (m a b : ℝ) : Fin 5 → ℝ → ℝ :=
  ![intervalDensity (1 - a / 2) 1, intervalDensity (a / 2) 1,
    intervalDensity (1 - b / 2) 1, intervalDensity (b / 2) 1,
    intervalDensity (1 - 1 / m) 1]

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

instance baseLaw_isProbabilityMeasure : IsProbabilityMeasure baseLaw :=
  intervalLaw_isProbabilityMeasure (by norm_num)

lemma leftLaw_isProbabilityMeasure {m a b : ℝ}
    (hm : 0 < m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) (i : Fin 5) :
    IsProbabilityMeasure (leftLaw m a b i) := by
  have hinv : 0 < 1 / m := one_div_pos.mpr hm
  fin_cases i <;> simp only [leftLaw] <;>
    apply intervalLaw_isProbabilityMeasure <;> linarith

lemma rightLaw_isProbabilityMeasure {m a b : ℝ}
    (hm : 2 ≤ m) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) (i : Fin 5) :
    IsProbabilityMeasure (rightLaw m a b i) := by
  have hm0 : 0 < m := by linarith
  have hinv : 0 < 1 / m := one_div_pos.mpr hm0
  fin_cases i <;> simp only [rightLaw] <;>
    apply intervalLaw_isProbabilityMeasure <;> linarith

lemma componentProbabilities_nonneg {κ m a b t : ℝ}
    (hκ : 0 ≤ κ) (hm : 0 < m) (ht : 0 ≤ t) (i : Fin 5) :
    0 ≤ componentProbabilities κ m a b t i := by
  fin_cases i <;>
    simp only [componentProbabilities]
  all_goals first | exact rho_nonneg hκ | exact div_nonneg ht hm.le

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

structure Parameters where
  κ : ℕ → ℝ
  m : ℕ → ℝ
  a : ℕ → ℝ
  b : ℕ → ℝ
  t : ℕ → ℝ
  κ_nonneg : ∀ i, 0 ≤ κ i
  κ_le : ∀ i, κ i ≤ 1 / 100
  m_ge : ∀ i, 100 ≤ m i
  a_lower : ∀ i, 1 / m i ≤ a i
  a_upper : ∀ i, a i ≤ 1 / 4
  b_lower : ∀ i, 1 / m i ≤ b i
  b_upper : ∀ i, b i ≤ 1 / 4
  t_nonneg : ∀ i, 0 ≤ t i
  t_le : ∀ i, t i ≤ 1

abbrev CoordinateSample := Option (Fin 5) × (ℝ × ℝ)
abbrev Sample := ℕ → CoordinateSample
abbrev Endpoint := ℕ → ℝ

def leftEndpoint (ω : Sample) (i : ℕ) : ℝ := (ω i).2.1

def rightEndpoint (ω : Sample) (i : ℕ) : ℝ := (ω i).2.2

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_BlockedProductCoupling
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.BlockedProductCoupling

abbrev Coordinate := Option (Fin 5) × (ℝ × ℝ)

abbrev Sample (m : ℕ → ℕ) := (s : ℕ) → Fin (m s) → Coordinate

def flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) (z : Sample m) :
    OrderedProductCoupling.Sample := fun i => z (e i).1 (e i).2

def leftEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (z : Sample m) : OrderedProductCoupling.Endpoint :=
  OrderedProductCoupling.leftEndpoint (flatten e z)

def rightEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (z : Sample m) : OrderedProductCoupling.Endpoint :=
  OrderedProductCoupling.rightEndpoint (flatten e z)

def toCircle (x : OrderedProductCoupling.Endpoint) : ProductModel.Base :=
  fun i => (x i : Circle)

def circleLeftEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Sample m → ProductModel.Base := toCircle ∘ leftEndpoint e

def circleRightEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Sample m → ProductModel.Base := toCircle ∘ rightEndpoint e

def parameters {m : ℕ → ℕ} {κ : ℕ → ℝ}
    {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) : OrderedProductCoupling.Parameters where
  κ i := κ (e i).1
  m i := m (e i).1
  a i := a (e i).1 (e i).2
  b i := b (e i).1 (e i).2
  t i := if (e i).1 = j then 1 else 0
  κ_nonneg i := hκ0 _
  κ_le i := hκ _
  m_ge i := Nat.cast_le.mpr (hm _)
  a_lower i := ha _ _
  a_upper i := ha' _ _
  b_lower i := hb _ _
  b_upper i := hb' _ _
  t_nonneg i := by split_ifs <;> norm_num
  t_le i := by split_ifs <;> norm_num

noncomputable def blockLaw (m : ℕ → ℕ) (κ : ℕ → ℝ)
    (a b : (s : ℕ) → Fin (m s) → ℝ) (j s : ℕ) :
    Measure (Fin (m s) → Coordinate) :=
  Measure.pi (fun i => OneCoordinateCoupling.labelledLaw (κ s) (m s)
    (a s i) (b s i) (if s = j then 1 else 0))

noncomputable def law (m : ℕ → ℕ) (κ : ℕ → ℝ)
    (a b : (s : ℕ) → Fin (m s) → ℝ) (j : ℕ) : Measure (Sample m) :=
  Measure.infinitePi (blockLaw m κ a b j)

def currentEvent (m : ℕ → ℕ) (j : ℕ) : Set (Sample m) :=
  {z | (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
    ∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
      2 / (m j : ℝ) < (z j i).2.2}

def futureBad (m : ℕ → ℕ) (K : ℕ → ℝ) (j : ℕ) : Set (Sample m) :=
  ⋃ n : ℕ, ⋃ i : Fin (m (j + 1 + n)),
    {z | 1 - 2 * K j / ((m (j + 1 + n) : ℝ) * K (j + 1 + n)) ≤
        (z (j + 1 + n) i).2.1 ∨
      (z (j + 1 + n) i).2.2 ≤
        2 * K j / ((m (j + 1 + n) : ℝ) * K (j + 1 + n))}

def retainedEvent {X : Type*} (m : ℕ → ℕ) (K : ℕ → ℝ)
    (r : X → ℝ) (x y : Sample m → X) (j : ℕ) : Set (Sample m) :=
  currentEvent m j \ (futureBad m K j ∪
    ({z | r (x z) < 1 / (j : ℝ)} ∪ {z | 1 - r (y z) < 1 / (j : ℝ)}))

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Invariant233.ProductCocycle

abbrev Space (I : Type*) := I → UnitAddCircle

def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def cocycleVersion {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) : ℝ :=
  Real.exp (-(∑' i, c i * (⌊representative (x i) + (k : ℝ) * θ i⌋ : ℝ)))

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductScales
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233

structure ProductScaleData where
  m : ℕ → ℕ
  K : ℕ → ℕ
  G : ℕ → ℕ
  L : ℕ → ℝ
  C : ℕ → ℝ
  ε : ℕ → ℝ

namespace ProductScaleData

def kappa (n : ℕ) : ℝ := 1 / (100 * ((n + 1 : ℕ) : ℝ))

def a (p : ProductScaleData) (n : ℕ) : ℝ := (p.G n : ℝ) / p.m n

def b (p : ProductScaleData) (n : ℕ) : ℝ := (p.m n : ℝ) ^ (-(19 / 20 : ℝ))

end ProductScaleData

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FiniteKernelMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def weightedKernel (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) : Kernel X Y where
  toFun x := ∑ i, w i x • κ i x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun i _ => (hw i).mul (Kernel.measurable_coe (κ i) hs))

noncomputable def normalizedKernel (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) : Kernel X Y :=
  weightedKernel κ (fun i x => w i x / ∑ j, w j x)
    (fun i => (hw i).div (Finset.measurable_sum _ (fun j _ => hw j)))

end Invariant233.FiniteKernelMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCouplingCircle
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

def circleEndpoint (x : Endpoint) : ProductModel.Base := fun i => (x i : Circle)

def circleLeftEndpoint : Sample → ProductModel.Base := circleEndpoint ∘ leftEndpoint

def circleRightEndpoint : Sample → ProductModel.Base := circleEndpoint ∘ rightEndpoint

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_BlockedSourceEvent
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

namespace Invariant233.BlockedProductCoupling

def sourceBasisZero : ProductModel.Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

abbrev ProjectionField := ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber

def projectionDiagonal (P : ProjectionField) (x : ProductModel.Base) : ℝ :=
  ((P x sourceBasisZero) 0).re

def sourceRetainedEvent {X : Type*} (m : ℕ → ℕ) (K : ℕ → ℝ)
    (r : X → ℝ) (x y : Sample m → X) (j : ℕ) : Set (Sample m) :=
  currentEvent m j \ (futureBad m K j ∪
    ({z | r (x z) < 1 / ((j + 1 : ℕ) : ℝ)} ∪
      {z | 1 - r (y z) < 1 / ((j + 1 : ℕ) : ℝ)}))

noncomputable def sourceLaw (p : ProductScaleData) (j : ℕ) : MeasureTheory.Measure (Sample p.m) :=
  law p.m ProductScaleData.kappa (fun s _ => p.a s) (fun s _ => p.b s) j

def sourceEvent (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (r : ProductModel.Base → ℝ) (j : ℕ) : Set (Sample p.m) :=
  sourceRetainedEvent p.m (fun s => (p.K s : ℝ)) r
    (circleLeftEndpoint e) (circleRightEndpoint e) j

def unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (ω : OrderedProductCoupling.Sample) : Sample m :=
  fun s i => ω (e.symm ⟨s, i⟩)

def flatSourceEvent (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (r : ProductModel.Base → ℝ) (j : ℕ) : Set OrderedProductCoupling.Sample :=
  unflatten e ⁻¹' sourceEvent p e r j

def sourceCoefficientA (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (P : ProjectionField) (z : Sample p.m) (v : ℤ) : ℂ :=
  (P (circleLeftEndpoint e z) sourceBasisZero) v /
    (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) v
      (circleLeftEndpoint e z) : ℂ)

def sourceCoefficientB (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (P : ProjectionField) (z : Sample p.m) (v : ℤ) : ℂ :=
  (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) (-v)
    (circleRightEndpoint e z) : ℂ) *
      conj (((1 - P (circleRightEndpoint e z)) sourceBasisZero) (-v))

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterTails
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ParameterTails

theorem half_decay_iterate {a : ℕ → ℝ}
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j n : ℕ) :
    a (j + n) ≤ a j * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a (j + (n + 1)) ≤ a (j + n) / 2 := by
          simpa only [Nat.add_assoc] using hstep (j + n)
        _ ≤ (a j * (1 / 2 : ℝ) ^ n) / 2 := by linarith
        _ = a j * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem summable_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) : Summable a := by
  apply Summable.of_nonneg_of_le ha
    (fun n => by simpa using half_decay_iterate hstep 0 n)
  simpa using summable_geometric_two.mul_left (a 0)

theorem reciprocal_half_decay {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (n : ℕ) :
    1 / K (n + 1) ≤ (1 / K n) / 2 := by
  calc
    1 / K (n + 1) ≤ 1 / (2 * K n) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) (hK n)) (hdouble n)
    _ = (1 / K n) / 2 := by ring

theorem summable_reciprocal {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) :
    Summable (fun n => 1 / K n) :=
  summable_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
    (reciprocal_half_decay hK hdouble)

end Invariant233.ParameterTails

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_circleRepresentative :
    MeasurePreserving
      (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 x) : ℝ))
      volume (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hmk : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ico 0 (0 + 1))) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact AddCircle.measurePreserving_mk 1 0
  have hs := hmk.comp (measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Ico 0 (0 + 1)) measurableSet_Ico)
  have he : MeasurePreserving (AddCircle.measurableEquivIco (1 : ℝ) 0).symm
      (Measure.comap Subtype.val (volume : Measure ℝ)) volume := hs
  have hi := MeasurePreserving.symm (AddCircle.measurableEquivIco (1 : ℝ) 0).symm he
  have h2 := (measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Ico 0 (0 + 1)) measurableSet_Ico).comp hi
  convert h2 using 2 <;> first | rfl | (rw [zero_add]) | (funext x; rfl) | simp

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.MixedRadix

def denominator (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, r i

abbrev Digits (r : ℕ → ℕ) := (n : ℕ) → Fin (r n)

noncomputable def term {r : ℕ → ℕ} (d : Digits r) (n : ℕ) : ℝ :=
  (d n : ℝ) / (denominator r (n + 1) : ℝ)

noncomputable def ofDigits {r : ℕ → ℕ} (d : Digits r) : ℝ :=
  ∑' n, term d n

def prefixRank {r : ℕ → ℕ} (d : Digits r) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixRank d n * r n + (d n : ℕ)

def radices (q : ℕ → ℕ) (n : ℕ) : ℕ := q (n + 1) / q n

def hybrid {r : ℕ → ℕ} (d e : Digits r) (N : ℕ) : Digits r :=
  fun n => if n < N then e n else d n

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.MixedRadix

noncomputable def circleValue {r : ℕ → ℕ} (d : Digits r) : AddCircle (1 : ℝ) :=
  (ofDigits d : AddCircle (1 : ℝ))

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleParameters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233

structure CircleParameterData where
  m : ℕ → ℕ
  K : ℕ → ℕ
  G : ℕ → ℕ
  q : ℕ → ℕ
  L : ℕ → ℝ
  C : ℕ → ℝ
  ε : ℕ → ℝ
  height : ℕ → ℕ
  partition : ℕ → ℕ → C(Circle, ℝ)
  samples : ℕ → ℕ → Finset ℕ

namespace CircleParameterData

def rep (x : Circle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def delta (z : ℝ) : ℝ := min (Int.fract z) (1 - Int.fract z)

def kernelWidth (m : ℕ) : ℝ := (m : ℝ) ^ (-(3 / 5 : ℝ))

def kernel (m : ℕ) (z v : ℝ) : ℝ :=
  if (1 / (m : ℝ) ^ 2 ≤ delta z) ∧ 0 < v ∧ v < kernelWidth m * delta z
  then 1 / (kernelWidth m * delta z) else 0

def orientedKernel (endpoint : Bool) (m : ℕ) (z v : ℝ) : ℝ :=
  if endpoint then kernel m (z - v) v else kernel m z v

def blockEnd (p : CircleParameterData) (j : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 j, p.m s

def blockIndex (p : CircleParameterData) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, i ≤ p.blockEnd j then Nat.find h else 0

def flattenedFrequency (p : CircleParameterData) (n : ℕ) : ℤ := p.q (n + 1)

def flattenedCost (p : CircleParameterData) (n : ℕ) : ℝ :=
  p.C (p.blockIndex (n + 1))

def block (p : CircleParameterData) (j : ℕ) : Finset ℕ :=
  Finset.Icc (p.blockEnd (j - 1) + 1) (p.blockEnd j)

def N (p : CircleParameterData) (j : ℕ) : ℝ := (p.m j : ℝ) * p.K j

def a (p : CircleParameterData) (j : ℕ) : ℝ := (p.G j : ℝ) / p.m j

def b (p : CircleParameterData) (j : ℕ) : ℝ := (p.m j : ℝ) ^ (-(19 / 20 : ℝ))

def Q (p : CircleParameterData) (j : ℕ) : ℝ :=
  (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)

def kappa (j : ℕ) : ℝ := 1 / (100 * (j : ℝ))

def alpha (p : CircleParameterData) (θ : ℝ) (i : ℕ) : ℝ :=
  Int.fract ((p.q i : ℝ) * θ)

def coordinate (p : CircleParameterData) (i : ℕ) (x : Circle) : ℝ :=
  rep (p.q i • x)

def ell (p : CircleParameterData) (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (p.blockEnd (j - 1) : ℝ)) *
    (p.q (p.blockEnd (j - 1)) : ℝ))

def shift (p : CircleParameterData) (j r : ℕ) : ℝ :=
  (r : ℝ) / p.q (p.blockEnd (j - 1))

def coefficientBound (p : CircleParameterData) (j : ℕ) : ℝ :=
  Real.exp (((p.K j : ℝ) + 1) *
    ∑ s ∈ Finset.Icc 1 (j - 1), p.C s * p.m s)

def convolutionCoefficient (K : ℕ) (A B : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), A t * B (n - t)

def samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (x : Circle) : ℝ :=
  (1 / ((p.samples j r).card : ℝ)) *
    ∑ n ∈ p.samples j r, ∏ i ∈ p.block j,
      orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i))

end CircleParameterData

open CircleParameterData

structure CircleParameterLaws (θ : ℝ) (p : CircleParameterData) : Prop where
  m_pos : ∀ j, 1 ≤ j → 0 < p.m j
  K_pos : ∀ j, 1 ≤ j → 0 < p.K j
  G_pos : ∀ j, 1 ≤ j → 0 < p.G j
  q_pos : ∀ i, 0 < p.q i
  L_pos : ∀ j, 1 ≤ j → 0 < p.L j
  C_pos : ∀ j, 1 ≤ j → 0 < p.C j
  epsilon_pos : ∀ j, 1 ≤ j → 0 < p.ε j
  partition_nonneg : ∀ j, 1 ≤ j → ∀ n, n ≤ p.height j →
    ∀ x, 0 ≤ p.partition j n x
  partition_sum : ∀ j, 1 ≤ j → ∀ x,
    (∑ n ∈ Finset.range (p.height j + 1), p.partition j n x) = 1
  partition_support : ∀ j, 1 ≤ j → ∀ n, n ≤ p.height j →
    ∀ x ∈ tsupport (p.partition j n),
      dist (x + (((n : ℝ) * θ : ℝ) : Circle)) 0 < 1 / (10 * (j : ℝ))
  frequency_zero : p.q 0 = 1
  frequency_increasing : StrictMono p.q
  frequency_divisible : ∀ i, p.q i ∣ p.q (i + 1)
  phase_bounds : ∀ j, 1 ≤ j → ∀ i ∈ p.block j,
    1 / p.N j < p.alpha θ i ∧ p.alpha θ i < 2 / p.N j
  frequency_ratios : ∀ j, 1 ≤ j → ∀ i ∈ p.block j,
    p.N j ≤ (p.q (i + 1) : ℝ) / p.q i
  spread_high : ∀ j, 1 ≤ j → ∀ k : ℤ,
    p.N j / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (p.m j : ℝ) ^ ((4 / 5 : ℝ) * p.m j) →
    (p.m j : ℝ) / 20 ≤
      ((p.block j).filter (fun i =>
        1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.b j) (1 - p.b j))).card
  spread_low : ∀ j, 1 ≤ j → ∀ k : ℤ,
    (p.G j : ℝ) * p.K j ≤ |(k : ℝ)| → |(k : ℝ)| ≤ p.N j / 4 →
    ∀ i ∈ p.block j,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.a j) (1 - p.a j)
  initial_K : p.K 1 = 100
  initial_G : p.G 1 = 1
  L_ge_one : ∀ j, 1 ≤ j → 1 ≤ p.L j
  L_monotone : ∀ j k, 1 ≤ j → j ≤ k → p.L j ≤ p.L k
  C_eq : ∀ j, 1 ≤ j → p.C j = max (p.L j) ((p.K j : ℝ) ^ 2)
  m_ge_K : ∀ j, 1 ≤ j → p.K j ≤ p.m j
  m_ge_pow : ∀ j, 1 ≤ j → 2 ^ j ≤ p.m j
  m_ge_G : ∀ j, 1 ≤ j → 4 * p.G j ≤ p.m j
  m_ge_200 : ∀ j, 1 ≤ j → 200 ≤ p.m j
  next_K : ∀ j, 1 ≤ j →
    p.K (j + 1) = ⌈(p.m j : ℝ) ^ ((3 / 4 : ℝ) * p.m j)⌉₊
  K_double : ∀ j, 1 ≤ j → 2 * p.K j < p.K (j + 1)
  next_G_gap : ∀ j, 1 ≤ j →
    (p.G (j + 1) : ℝ) * p.K (j + 1) <
      (p.m j : ℝ) ^ ((4 / 5 : ℝ) * p.m j)
  attenuation_m : ∀ j, 1 ≤ j →
    p.L j ≤ kappa j * (p.m j : ℝ) ^ (1 / 40 : ℝ)
  attenuation_G : ∀ j, 1 ≤ j →
    p.L j ≤ kappa (j + 1) * Real.sqrt (p.G (j + 1) : ℝ)
  continuity_height : ∀ j, 1 ≤ j →
    (p.height (j + 1) : ℝ) / p.K (j + 1) ≤ (1 / 2 : ℝ) ^ j
  polynomial_lower : ∀ j, 1 ≤ j → ∀ A B : ℤ → ℂ,
    Function.support A ⊆ Set.Icc (-(p.K j : ℤ)) (p.K j : ℤ) →
    Function.support B ⊆ Set.Icc (-(p.K j : ℤ)) (p.K j : ℤ) →
    (∀ n, ‖A n‖ ≤ p.coefficientBound j) →
    (∀ n, ‖B n‖ ≤ p.coefficientBound j) →
    1 / (j : ℝ) ≤ ‖A 0‖ → 1 / (j : ℝ) ≤ ‖B 0‖ →
    ∃ n ∈ Finset.Icc 0 (2 * p.K j),
      p.ε j ≤ ‖convolutionCoefficient (p.K j) A B (-(n : ℤ))‖
  polynomial_attenuation : ∀ j, 1 ≤ j →
    ((2 * p.K j + 1 : ℕ) : ℝ) * 3 * Real.exp (-p.L j / 10000) ≤ p.ε j / j
  samples_nonempty : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → (p.samples j r).Nonempty
  samples_positive : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r, 0 < n
  samples_range : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r,
      p.Q j / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ p.Q j
  samples_phase : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r,
      Int.fract ((n : ℝ) * θ - p.shift j r) ∈ Set.Ioo 0 (p.ell j)
  sampling_L2 : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ endpoint : Bool,
      eLpNorm (fun x => p.samplingAverage θ j r endpoint x - 1) 2 circleMeasure <
        ENNReal.ofReal (1 / (j : ℝ))

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CircleParameterData

@[simp] theorem blockEnd_zero (p : CircleParameterData) : p.blockEnd 0 = 0 := by
  simp [blockEnd]

theorem blockEnd_succ (p : CircleParameterData) (j : ℕ) :
    p.blockEnd (j + 1) = p.blockEnd j + p.m (j + 1) := by
  exact Finset.sum_Icc_succ_top (by omega) p.m

theorem card_block (p : CircleParameterData) (j : ℕ) (hj : 1 ≤ j) :
    (p.block j).card = p.m j := by
  have hd := p.blockEnd_succ (j - 1)
  have he : j - 1 + 1 = j := by omega
  rw [he] at hd
  simp only [block, Nat.card_Icc]
  omega

theorem mem_block_iff (p : CircleParameterData) (j i : ℕ) :
    i ∈ p.block j ↔ p.blockEnd (j - 1) < i ∧ i ≤ p.blockEnd j := by
  simp only [block, Finset.mem_Icc, Nat.add_one_le_iff]

theorem blockEnd_ge_index (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j : ℕ) : j ≤ p.blockEnd j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [blockEnd_succ]
    have h := hm (j + 1) (by omega)
    omega

theorem blockEnd_strictMono (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) : StrictMono p.blockEnd := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [blockEnd_succ]
  exact Nat.lt_add_of_pos_right (hm (j + 1) (by omega))

theorem exists_mem_block (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (i : ℕ) (hi : 1 ≤ i) :
    ∃ j, 1 ≤ j ∧ i ∈ p.block j := by
  have hex : ∃ j, i ≤ p.blockEnd j := ⟨i, p.blockEnd_ge_index hm i⟩
  let j := Nat.find hex
  have hj : i ≤ p.blockEnd j := Nat.find_spec hex
  have hjpos : 1 ≤ j := by
    by_contra h
    have he : j = 0 := by omega
    rw [he, blockEnd_zero] at hj
    omega
  refine ⟨j, hjpos, (p.mem_block_iff j i).mpr ⟨?_, hj⟩⟩
  have hprev : ¬ i ≤ p.blockEnd (j - 1) :=
    Nat.find_min hex (show j - 1 < j by omega)
  omega

theorem blockIndex_eq_of_mem (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j i : ℕ} (hi : i ∈ p.block j) :
    p.blockIndex i = j := by
  classical
  have hij := (p.mem_block_iff j i).mp hi
  have hex : ∃ k, i ≤ p.blockEnd k := ⟨j, hij.2⟩
  rw [blockIndex, dite_eq_left hex]
  apply le_antisymm
  · exact Nat.find_min' hex hij.2
  · by_contra h
    have hle : Nat.find hex ≤ j - 1 := by omega
    have hd := (p.blockEnd_strictMono hm).monotone hle
    have hf := Nat.find_spec hex
    omega

theorem blockIndex_pos (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {i : ℕ} (hi : 1 ≤ i) :
    1 ≤ p.blockIndex i := by
  obtain ⟨j, hj, hij⟩ := p.exists_mem_block hm i hi
  rwa [p.blockIndex_eq_of_mem hm hij]

end Invariant233.CircleParameterData

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleCharacterDynamics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace CircleCharacterDynamics

local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem representative_coe (x : ℝ) : rep (x : Circle) = Int.fract x := by
  simp [AddCircle.coe_equivIco_mk_apply]

end CircleCharacterDynamics
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem denominator_zero (r : ℕ → ℕ) : denominator r 0 = 1 := by
  simp [denominator]

@[simp] theorem denominator_succ (r : ℕ → ℕ) (n : ℕ) :
    denominator r (n + 1) = denominator r n * r n := by
  simp [denominator, Finset.prod_range_succ]

theorem denominator_pos {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < denominator r n := by
  exact Finset.prod_pos (fun i _ => hr i)

theorem term_nonneg {r : ℕ → ℕ} (d : Digits r) (n : ℕ) :
    0 ≤ term d n := by unfold term; positivity

theorem term_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (n : ℕ) :
    term d n ≤ 1 / (denominator r n : ℝ) - 1 / (denominator r (n + 1) : ℝ) := by
  have hq : (0 : ℝ) < denominator r n := by exact_mod_cast denominator_pos hr n
  have hrr : (0 : ℝ) < r n := by exact_mod_cast hr n
  have hd : (d n : ℝ) ≤ (r n : ℝ) - 1 := by
    have hh : (d n : ℝ) + 1 ≤ (r n : ℝ) := by exact_mod_cast (d n).isLt
    linarith
  rw [term, denominator_succ, Nat.cast_mul]
  calc
    (d n : ℝ) / ((denominator r n : ℝ) * (r n : ℝ)) ≤
        ((r n : ℝ) - 1) / ((denominator r n : ℝ) * (r n : ℝ)) :=
      div_le_div_of_nonneg_right hd (mul_pos hq hrr).le
    _ = _ := by field_simp

theorem denominator_double {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) (n : ℕ) :
    2 * (denominator r n : ℝ) ≤ (denominator r (n + 1) : ℝ) := by
  rw [denominator_succ, Nat.cast_mul]
  have hh : (2 : ℝ) ≤ r n := by exact_mod_cast hr n
  nlinarith [Nat.cast_nonneg (α := ℝ) (denominator r n)]

theorem summable_reciprocal_denominator {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Summable (fun n => 1 / (denominator r n : ℝ)) := by
  apply ParameterTails.summable_reciprocal
  · intro n
    exact_mod_cast denominator_pos (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) n
  · exact denominator_double hr

theorem continuous_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Continuous (@ofDigits r) := by
  apply continuous_tsum (u := fun n => 1 / (denominator r n : ℝ))
  · intro n
    have hd : Continuous (fun a : Fin (r n) => (a : ℝ)) := continuous_of_discreteTopology
    exact (hd.comp (continuous_apply n)).div_const _
  · exact summable_reciprocal_denominator hr
  · intro n d
    rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg d n)]
    have h := term_le_reciprocal_gap
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) d n
    have hnn : (0 : ℝ) ≤ 1 / (denominator r (n + 1) : ℝ) := by positivity
    linarith

@[simp] theorem prefixRank_zero {r : ℕ → ℕ} (d : Digits r) : prefixRank d 0 = 0 := rfl

@[simp] theorem prefixRank_succ {r : ℕ → ℕ} (d : Digits r) (N : ℕ) :
    prefixRank d (N + 1) = prefixRank d N * r N + (d N : ℕ) := rfl

theorem measurable_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Measurable (@ofDigits r) := (continuous_ofDigits hr).measurable

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem radices_ge_two {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    2 ≤ radices q n := by
  have heq : q n * radices q n = q (n + 1) := Nat.mul_div_cancel' (hdiv n)
  have hi := hstrict (Nat.lt_succ_self n)
  have hp := hq n
  by_contra hnot
  have hle : radices q n ≤ 1 := by omega
  nlinarith

@[simp] theorem hybrid_apply_ge {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : N ≤ n) :
    hybrid d e N n = d n := ite_eq_right (not_lt.mpr hn)

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceTransport
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.BlockedProductCoupling

@[simp] theorem unflatten_flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) (z : Sample m) :
    unflatten e (flatten e z) = z := by
  funext s i
  change (fun q : Σ t, Fin (m t) => z q.1 q.2) (e (e.symm ⟨s, i⟩)) = z s i
  rw [e.apply_symm_apply]

@[simp] theorem flatten_unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (ω : OrderedProductCoupling.Sample) : flatten e (unflatten e ω) = ω := by
  funext i
  simp [unflatten, flatten]

@[simp] theorem circleLeftEndpoint_unflatten {m : ℕ → ℕ}
    (e : ℕ ≃ Σ s, Fin (m s)) (ω : OrderedProductCoupling.Sample) :
    circleLeftEndpoint e (unflatten e ω) = OrderedProductCoupling.circleLeftEndpoint ω := by
  change toCircle (OrderedProductCoupling.leftEndpoint (flatten e (unflatten e ω))) = _
  rw [flatten_unflatten]
  rfl

@[simp] theorem circleRightEndpoint_unflatten {m : ℕ → ℕ}
    (e : ℕ ≃ Σ s, Fin (m s)) (ω : OrderedProductCoupling.Sample) :
    circleRightEndpoint e (unflatten e ω) = OrderedProductCoupling.circleRightEndpoint ω := by
  change toCircle (OrderedProductCoupling.rightEndpoint (flatten e (unflatten e ω))) = _
  rw [flatten_unflatten]
  rfl

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_VectorTraceState
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannSMulMemClass :
    SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c {_} ha := s.toSubalgebra.smul_mem ha c

instance vonNeumannNormClosed (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualCore
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (M : VonNeumannAlgebra H) (x y : H) : StrongDual ℂ M :=
  ((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H) y)).comp
    M.toSubalgebra.toSubmodule.subtypeL

@[simp] theorem vectorFunctional_apply (M : VonNeumannAlgebra H) (x y : H) (A : M) :
    vectorFunctional M x y A = inner ℂ x ((A : H →L[ℂ] H) y) := rfl

def predual (M : VonNeumannAlgebra H) : Submodule ℂ (StrongDual ℂ M) :=
  (Submodule.span ℂ (Set.range (fun xy : H × H => vectorFunctional M xy.1 xy.2))).topologicalClosure

theorem vectorFunctional_mem (M : VonNeumannAlgebra H) (x y : H) :
    vectorFunctional M x y ∈ predual M :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x, y), rfl⟩)

def vector (M : VonNeumannAlgebra H) (x y : H) : predual M :=
  ⟨vectorFunctional M x y, vectorFunctional_mem M x y⟩

@[simp] theorem vector_coe (M : VonNeumannAlgebra H) (x y : H) :
    (vector M x y : StrongDual ℂ M) = vectorFunctional M x y := rfl

def evaluation (M : VonNeumannAlgebra H) (A : M) : StrongDual ℂ (predual M) :=
  ((ContinuousLinearMap.apply ℂ ℂ) A).comp (predual M).subtypeL

@[simp] theorem evaluation_apply (M : VonNeumannAlgebra H) (A : M) (f : predual M) :
    evaluation M A f = (f : StrongDual ℂ M) A := rfl

@[simp] theorem evaluation_vector (M : VonNeumannAlgebra H) (A : M) (x y : H) :
    evaluation M A (vector M x y) = inner ℂ x ((A : H →L[ℂ] H) y) := rfl

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualEvaluation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance evaluationPredualNormedAddCommGroup (M : VonNeumannAlgebra H) : NormedAddCommGroup (predual M) :=
  (predual M).normedAddCommGroup
local instance evaluationPredualNormedSpace (M : VonNeumannAlgebra H) : NormedSpace ℂ (predual M) :=
  (predual M).normedSpace

theorem vector_norm_bound (M : VonNeumannAlgebra H) (x y : H) :
    ‖vector M x y‖ ≤ ‖x‖ * ‖y‖ := by
  change ‖vectorFunctional M x y‖ ≤ ‖x‖ * ‖y‖
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  change ‖inner ℂ x ((A : H →L[ℂ] H) y)‖ ≤ (‖x‖ * ‖y‖) * ‖A‖
  calc
    ‖inner ℂ x ((A : H →L[ℂ] H) y)‖ ≤ ‖x‖ * ‖(A : H →L[ℂ] H) y‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖(A : H →L[ℂ] H)‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((A : H →L[ℂ] H).le_opNorm y) (norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖A‖ := by change _ = (‖x‖ * ‖y‖) * ‖(A : H →L[ℂ] H)‖; ring

theorem norm_evaluation_le (M : VonNeumannAlgebra H) (A : M) :
    ‖evaluation M A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  calc
    ‖evaluation M A f‖ ≤ ‖(f : StrongDual ℂ M)‖ * ‖A‖ :=
      (f : StrongDual ℂ M).le_opNorm A
    _ = ‖A‖ * ‖f‖ := mul_comm _ _

theorem norm_le_evaluation (M : VonNeumannAlgebra H) (A : M) :
    ‖A‖ ≤ ‖evaluation M A‖ := by
  change ‖(A : H →L[ℂ] H)‖ ≤ ‖evaluation M A‖
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg _)
  intro x y hx hy
  calc
    (inner ℂ ((A : H →L[ℂ] H) x) y).re =
        (inner ℂ y ((A : H →L[ℂ] H) x)).re := inner_re_symm (𝕜 := ℂ) _ _
    _ ≤ ‖inner ℂ y ((A : H →L[ℂ] H) x)‖ := Complex.re_le_norm _
    _ = ‖evaluation M A (vector M y x)‖ := rfl
    _ ≤ ‖evaluation M A‖ * ‖vector M y x‖ :=
      (evaluation M A).le_opNorm _
    _ ≤ ‖evaluation M A‖ * (‖y‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (vector_norm_bound M y x) (norm_nonneg _)
    _ = ‖evaluation M A‖ := by rw [hy, hx]; ring

@[simp] theorem norm_evaluation (M : VonNeumannAlgebra H) (A : M) :
    ‖evaluation M A‖ = ‖A‖ :=
  le_antisymm (norm_evaluation_le M A) (norm_le_evaluation M A)

def evaluationLinearIsometry (M : VonNeumannAlgebra H) :
    M →ₗᵢ[ℂ] StrongDual ℂ (predual M) where
  toFun := evaluation M
  map_add' A B := by
    ext f
    exact (f : StrongDual ℂ M).map_add A B
  map_smul' c A := by
    ext f
    exact (f : StrongDual ℂ M).map_smul c A
  norm_map' := norm_evaluation M

@[simp] theorem evaluationLinearIsometry_apply (M : VonNeumannAlgebra H) (A : M) :
    evaluationLinearIsometry M A = evaluation M A := rfl

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualRepresentation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
attribute [-simp] _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometry_apply _root_.OAI.Invariant233.ConcretePredual.norm_evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem vectorFunctional_add_left (M : VonNeumannAlgebra H) (x z y : H) :
    vectorFunctional M (x + z) y = vectorFunctional M x y + vectorFunctional M z y := by
  ext A
  simp

@[simp] theorem vectorFunctional_add_right (M : VonNeumannAlgebra H) (x y z : H) :
    vectorFunctional M x (y + z) = vectorFunctional M x y + vectorFunctional M x z := by
  ext A
  simp

@[simp] theorem vectorFunctional_smul_left (M : VonNeumannAlgebra H) (c : ℂ) (x y : H) :
    vectorFunctional M (c • x) y = star c • vectorFunctional M x y := by
  ext A
  simp [mul_comm]

@[simp] theorem vectorFunctional_smul_right (M : VonNeumannAlgebra H) (c : ℂ) (x y : H) :
    vectorFunctional M x (c • y) = c • vectorFunctional M x y := by
  ext A
  simp

theorem norm_vectorFunctional_le (M : VonNeumannAlgebra H) (x y : H) :
    ‖vectorFunctional M x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  calc
    ‖vectorFunctional M x y A‖ ≤ ‖x‖ * ‖(A : H →L[ℂ] H) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((A : H →L[ℂ] H).le_opNorm y) (norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖A‖ := by ring

def representingForm (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun x =>
        { toFun := fun y => Φ (vectorFunctional M x y)
          map_add' := by intro y z; simp
          map_smul' := by intro c y; simp }
      map_add' := by intro x z; ext y; simp
      map_smul' := by intro c x; ext y; simp } ‖Φ‖
    (by
      intro x y
      exact (Φ.le_opNorm _).trans (by
        calc
          ‖Φ‖ * ‖vectorFunctional M x y‖ ≤ ‖Φ‖ * (‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left (norm_vectorFunctional_le M x y) (norm_nonneg Φ)
          _ = ‖Φ‖ * ‖x‖ * ‖y‖ := by ring))

def representingOperator (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (representingForm M Φ)).adjoint

@[simp] theorem inner_representingOperator (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) (x y : H) :
    inner ℂ x (representingOperator M Φ y) = Φ (vectorFunctional M x y) := by
  rw [representingOperator, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualComplete
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance completedPredualNormedAddCommGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (predual M) := (predual M).normedAddCommGroup

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ContinuityCoboundary
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

variable {X : Type*}

def backwardSum (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ r ∈ Finset.range n, v ((σ.symm : X → X)^[r + 1] x)

def relocated (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (x : X) : ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    h ((σ.symm : X → X)^[n] x) * φ n ((σ.symm : X → X)^[n] x)

def relocationTransfer (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (x : X) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), backwardSum σ (fun y => h y * φ n y) n x

def backwardAverage (σ : X ≃ X) (v : X → ℝ) (W : ℕ) (x : X) : ℝ :=
  (W : ℝ)⁻¹ * backwardSum σ v W x

def backgroundTransfer (σ : X ≃ X) (v : X → ℝ) (W : ℕ) (x : X) : ℝ :=
  (W : ℝ)⁻¹ * ∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x

end InvariantProjection.Continuity

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ContinuityCoboundary
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*}

theorem relocated_nonneg (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (hh : ∀ x, 0 ≤ h x) (hφ : ∀ n ≤ H, ∀ x, 0 ≤ φ n x) (x : X) :
    0 ≤ relocated σ h φ H x := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (hh _) (hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) _)

theorem support_relocated_subset (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (O : Set X)
    (hφ : ∀ n ≤ H, (σ : X → X)^[n] '' support (φ n) ⊆ O) :
    support (relocated σ h φ H) ⊆ O := by
  intro x hx
  by_contra hxO
  apply hx
  apply Finset.sum_eq_zero
  intro n hn
  have hz : φ n ((σ.symm : X → X)^[n] x) = 0 := by
    by_contra hne
    apply hxO
    apply hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    refine ⟨(σ.symm : X → X)^[n] x, hne, ?_⟩
    exact (Function.LeftInverse.iterate σ.apply_symm_apply n) x
  rw [hz, mul_zero]

theorem continuous_relocated [TopologicalSpace X] (σ : X ≃ₜ X)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (hh : Continuous h)
    (hφ : ∀ n ≤ H, Continuous (φ n)) :
    Continuous (relocated σ.toEquiv h φ H) := by
  apply continuous_finsetSum
  intro n hn
  exact (hh.comp (σ.symm.continuous.iterate n)).mul
    ((hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).comp
      (σ.symm.continuous.iterate n))

end InvariantProjection.Continuity

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurableEmbedding_iterate (σ : X ≃ᵐ X) (n : ℕ) :
    MeasurableEmbedding (σ : X → X)^[n] := by
  induction n with
  | zero => exact MeasurableEmbedding.id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp σ.measurableEmbedding

theorem integral_relocated (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ)
    (hint : ∀ n ≤ H, Integrable (fun x => h x * φ n x) μ)
    (hpartition : ∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) :
    ∫ x, relocated σ.toEquiv h φ H x ∂μ = ∫ x, h x ∂μ := by
  have hb := hσ.symm σ
  have hp (n : ℕ) : MeasurePreserving (σ.symm : X → X)^[n] μ μ := hb.iterate n
  unfold relocated
  rw [integral_finsetSum]
  · calc
      (∑ n ∈ Finset.range (H + 1),
          ∫ x, h ((σ.symm : X → X)^[n] x) *
            φ n ((σ.symm : X → X)^[n] x) ∂μ) =
          ∑ n ∈ Finset.range (H + 1), ∫ x, h x * φ n x ∂μ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hp n).integral_comp (measurableEmbedding_iterate σ.symm n)
          (fun x : X => h x * φ n x)
      _ = ∫ x, ∑ n ∈ Finset.range (H + 1), h x * φ n x ∂μ := by
        symm
        apply integral_finsetSum
        intro n hn
        exact hint n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
      _ = ∫ x, h x ∂μ := by
        congr 1
        funext x
        rw [← Finset.mul_sum, hpartition x, mul_one]
  · intro n hn
    exact (hp n).integrable_comp_of_integrable
      (hint n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_NonnegativeCostIntegral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_cost_add_background_eq_top (g b : X → ℝ)
    (hg : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞)
    (hb : ∀ᵐ x ∂μ, 0 ≤ b x) :
    (∫⁻ x, ENNReal.ofReal (b x + g x) ∂μ) = ∞ := by
  apply top_unique
  rw [← hg]
  apply lintegral_mono_ae
  filter_upwards [hb] with x hx
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hx)

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_Diagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal lp

namespace Invariant233

abbrev SequenceHilbert (I : Type*) := lp (fun _ : I => ℂ) 2

namespace SequenceHilbert
variable {I : Type*}

def diagonalLinear (a : I → ℂ) (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert I →ₗ[ℂ] SequenceHilbert I where
  toFun x := ⟨fun i => a i * x i, by
    apply Memℓp.mono ((lp.memℓp x).norm.const_mul C)
    intro i
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)⟩
  map_add' x y := by
    apply lp.ext
    funext i
    exact mul_add _ _ _
  map_smul' c x := by
    apply lp.ext
    funext i
    change a i * (c * x i) = c * (a i * x i)
    ring

def diagonal (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert I →L[ℂ] SequenceHilbert I :=
  (diagonalLinear a C ha).mkContinuous C (by
    intro x
    calc
      ‖diagonalLinear a C ha x‖ ≤ ‖C • x‖ := by
        apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        intro i
        change ‖a i * x i‖ ≤ ‖C • x i‖
        rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
      _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC])

end SequenceHilbert
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_UnrestrictedDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.SequenceHilbert

variable {I : Type*}

def boundedDiagonal (a : I → ℂ) : SequenceHilbert I →L[ℂ] SequenceHilbert I := by
  classical
  exact if h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C then
    diagonal a h.choose h.choose_spec.1 h.choose_spec.2
  else 0

end Invariant233.SequenceHilbert

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped NNReal
noncomputable section

namespace Invariant233

noncomputable def ratioDiagonal {X : Type*} (F : ℤ → X → ℝ) (t : X × X) :
    SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ :=
  SequenceHilbert.boundedDiagonal (fun i => ((F i t.2 / F i t.1 : ℝ) : ℂ))

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CircleWeights

def representative (x : UnitAddCircle) : ℝ :=
  AddCircle.equivIco (1 : ℝ) 0 x

def coordinate {ι : Type*} (q : ι → ℤ) (i : ι) (x : UnitAddCircle) : ℝ :=
  representative (q i • x)

def phase {ι : Type*} (θ : ℝ) (q : ι → ℤ) (i : ι) : ℝ :=
  Int.fract ((q i : ℝ) * θ)

def rotate (θ : ℝ) (k : ℤ) (x : UnitAddCircle) : UnitAddCircle :=
  x + k • (θ : UnitAddCircle)

def floorCost {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : ℝ :=
  ∑' i, c i * (Int.floor (coordinate q i x + (k : ℝ) * phase θ q i) : ℝ)

def cocycle {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : ℝ :=
  Real.exp (-floorCost θ q c k x)

def weight {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) : UnitAddCircle → ℝ :=
  cocycle θ q c 1

end Invariant233.CircleWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ParameterCircleWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

abbrev Coord (p : CircleParameterData) :=
  Σ j : ℕ, {i : ℕ // i ∈ p.block (j + 1)}

def coordFrequency (p : CircleParameterData) (i : p.Coord) : ℤ := p.q i.2

def coordCost (p : CircleParameterData) (i : p.Coord) : ℝ := p.C (i.1 + 1)

def floorCocycle (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) : ℝ :=
  CircleWeights.cocycle θ p.coordFrequency p.coordCost k x

def measurableWeight (p : CircleParameterData) (θ : ℝ) : Circle → ℝ :=
  CircleWeights.weight θ p.coordFrequency p.coordCost

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_RotationMeasurable
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

def measurableOrbitWeight (θ : ℝ) (g : Circle → ℂ) (C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ C) (x : Circle) : WeightedShift.Weight :=
  ⟨fun k => g (action θ k x), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    exact hb _⟩

def measurableRepresentation (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (measurableOrbitWeight θ g C hb) C hC
    (fun _ => lp.norm_le_of_forall_le hC (fun _ => hb _))
    (fun _k => (hg.comp (continuous_id.add continuous_const).measurable).aestronglyMeasurable)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ParameterCircleOperator
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.CircleParameterData.blockEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleParameterData

theorem measurableWeight_borel (p : CircleParameterData) (θ : ℝ) :
    Measurable (p.measurableWeight θ) := by
  unfold measurableWeight CircleWeights.weight CircleWeights.cocycle CircleWeights.floorCost
  apply Measurable.exp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  apply Measurable.mul measurable_const
  apply (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
  apply Measurable.floor
  apply Measurable.add _ measurable_const
  change Measurable (fun x : Circle =>
    ((AddCircle.equivIco (1 : ℝ) 0 (p.coordFrequency i • x)) : ℝ))
  exact (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable).comp
      (continuous_const_smul (p.coordFrequency i)).measurable

theorem measurableWeight_operator_bound (p : CircleParameterData) (θ : ℝ)
    (hp : CircleParameterLaws θ p) (x : Circle) :
    ‖(p.measurableWeight θ x : ℂ)‖ ≤ 1 := by
  have hpos : 0 < p.measurableWeight θ x := Real.exp_pos _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hp.C_pos (i.1 + 1) (Nat.succ_le_iff.mpr (Nat.zero_lt_succ _))).le
  apply Int.cast_nonneg
  apply Int.floor_nonneg.mpr
  apply add_nonneg
  · exact (AddCircle.equivIco (1 : ℝ) 0 (p.coordFrequency i • x)).property.1
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)

def measurableOperator (p : CircleParameterData) (θ : ℝ)
    (hp : CircleParameterLaws θ p) : Rotation.Hilbert →L[ℂ] Rotation.Hilbert :=
  Rotation.U * Rotation.measurableRepresentation θ
    (fun x => (p.measurableWeight θ x : ℂ)) 1 (by norm_num)
    (Complex.measurable_ofReal.comp (p.measurableWeight_borel θ))
    (p.measurableWeight_operator_bound θ hp)

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem exp_neg_tsum_mem_Ioc (c a : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i) :
    Real.exp (-(∑' i, c i * a i)) ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (tsum_nonneg fun i => mul_nonneg (hc i) (ha i))

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem measurePreserving_characterRepresentative (q : ℤ) (hq : q ≠ 0) :
    MeasurePreserving
      (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (q • x)) : ℝ))
      volume (volume.restrict (Ico (0 : ℝ) 1)) := by
  exact CocycleSupport.measurePreserving_circleRepresentative.comp
    (Measure.measurePreserving_zsmul volume hq)

theorem measurable_exp_weight {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (α c : ι → ℝ) :
    Measurable (fun x : UnitAddCircle => Real.exp (-(∑' i,
      c i * (Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i) : ℝ)))) := by
  apply Measurable.exp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  apply Measurable.mul measurable_const
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (((measurePreserving_characterRepresentative (q i) (hq i)).measurable.add_const _).floor)

theorem exp_weight_mem_Ioc {ι : Type*} (q : ι → ℤ) (α c : ι → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle) :
    Real.exp (-(∑' i,
      c i * (Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i) : ℝ)))
       ∈ Set.Ioc (0 : ℝ) 1 := by
  apply FiniteSupportWeights.exp_neg_tsum_mem_Ioc c _ hc
  intro i
  apply Int.cast_nonneg
  apply Int.floor_nonneg.mpr
  exact add_nonneg (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property.1 (hα0 i)

end Invariant233.CircleWeightSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem phase_nonneg (θ : ℝ) (q : ι → ℤ) (i : ι) : 0 ≤ phase θ q i :=
  Int.fract_nonneg _

theorem measurable_cocycle [Countable ι] (θ : ℝ) (q : ι → ℤ)
    (hq : ∀ i, q i ≠ 0) (c : ι → ℝ) (k : ℤ) :
    Measurable (cocycle θ q c k) := by
  exact CircleWeightSupport.measurable_exp_weight q hq
    (fun i => (k : ℝ) * phase θ q i) c

theorem weight_mem_Ioc (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle) : weight θ q c x ∈ Ioc (0 : ℝ) 1 := by
  simpa only [weight, cocycle, floorCost, Int.cast_one, one_mul, coordinate, representative] using
    CircleWeightSupport.exp_weight_mem_Ioc q (phase θ q) c (phase_nonneg θ q) hc x

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordFrequency_ne_zero (i : p.Coord) : p.coordFrequency i ≠ 0 := by
  change (p.q i.2 : ℤ) ≠ 0
  exact_mod_cast (hp.q_pos i.2).ne'

theorem coordCost_pos (i : p.Coord) : 0 < p.coordCost i :=
  hp.C_pos (i.1 + 1) (by omega)

theorem measurable_parameter_weight : Measurable (p.measurableWeight θ) := by
  exact CircleWeights.measurable_cocycle θ p.coordFrequency hp.coordFrequency_ne_zero
    p.coordCost 1

theorem parameter_weight_mem_Ioc (x : Circle) :
    p.measurableWeight θ x ∈ Ioc (0 : ℝ) 1 :=
  CircleWeights.weight_mem_Ioc θ p.coordFrequency p.coordCost
    (fun i => (hp.coordCost_pos i).le) x

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

@[simp] theorem reindex_apply (e : Equiv.Perm ℤ) (ξ : Hilbert) (k : ℤ) :
    reindex e ξ k = ξ (e k) := rfl

@[simp] theorem shift_apply (m : ℤ) (ξ : Hilbert) (k : ℤ) :
    shift m ξ k = ξ (k - m) := rfl

@[simp] theorem diagonal_apply (w : Weight) (ξ : Hilbert) (k : ℤ) :
    diagonal w ξ k = w k * ξ k := rfl

@[simp] theorem operator_apply (w : Weight) (ξ : Hilbert) (k : ℤ) :
    operator w ξ k = w (k - 1) * ξ (k - 1) := rfl

@[simp] theorem orbitProduct_apply (w : Weight) (n : ℕ) (k : ℤ) :
    orbitProduct w n k = ∏ j ∈ Finset.range n, w (k + j) := rfl

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftAlgebra
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal ComplexConjugate
namespace Invariant233.WeightedShift

@[simp] theorem diagonalAlgHom_apply (w : Weight) : diagonalAlgHom w = diagonal w := rfl

@[simp] theorem diagonal_one : diagonal (1 : Weight) = 1 := diagonalAlgHom.map_one
@[simp] theorem diagonal_zero : diagonal (0 : Weight) = 0 := diagonalAlgHom.map_zero
@[simp] theorem diagonal_add (w v : Weight) : diagonal (w + v) = diagonal w + diagonal v :=
  diagonalAlgHom.map_add w v
@[simp] theorem diagonal_mul (w v : Weight) : diagonal (w * v) = diagonal w * diagonal v :=
  diagonalAlgHom.map_mul w v
@[simp] theorem diagonal_smul (c : ℂ) (w : Weight) : diagonal (c • w) = c • diagonal w :=
  diagonalAlgHom.toLinearMap.map_smul c w

@[simp] theorem diagonal_star (w : Weight) : diagonal (star w) = star (diagonal w) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro ξ η
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [diagonal_apply, lp.coeFn_star, Pi.star_apply, RCLike.inner_apply,
    map_mul, starRingEnd_apply, star_star]
  ring

@[simp] theorem translate_apply (w : Weight) (m k : ℤ) : translate w m k = w (k + m) := rfl

@[simp] theorem translate_zero (w : Weight) : translate w 0 = w := by
  ext k
  simp

@[simp] theorem translate_add (w : Weight) (m n : ℤ) :
    translate w (m + n) = translate (translate w n) m := by
  ext k
  simp [add_assoc]

@[simp] theorem shift_zero : (shift 0).toLinearIsometry.toContinuousLinearMap = 1 := by
  ext ξ k
  change ξ (k - 0) = ξ k
  simp

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

theorem fieldDiagonal_ae (f : Lp Hilbert 2 μ) :
    fieldDiagonal a C hC ha hm f =ᵐ[μ] fun x => diagonal (a x) (f x) :=
  fieldDiagonalVec_ae a C hC ha hm f

variable {a C hC ha hm}

theorem fieldDiagonal_star_of_eq
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    (heq : b =ᵐ[μ] fun x => star (a x)) :
    fieldDiagonal b D hD hb hn = star (fieldDiagonal a C hC ha hm) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldDiagonal_ae b D hD hb hn f,
    fieldDiagonal_ae a C hC ha hm g, heq] with x hx hy he
  rw [hx, hy, he, diagonal_star, ContinuousLinearMap.star_eq_adjoint]
  exact (diagonal (a x)).adjoint_inner_left (g x) (f x)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_Rotation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

@[simp] theorem action_zero (θ : ℝ) (x : Circle) : action θ 0 x = x := by
  simp [action]

@[simp] theorem action_add (θ : ℝ) (m n : ℤ) (x : Circle) :
    action θ m (action θ n x) = action θ (m + n) x := by
  simp only [action, add_zsmul]
  abel

@[simp] theorem orbitWeight_apply (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) (k : ℤ) :
    orbitWeight θ a x k = a (action θ k x) := rfl

theorem representation_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    representation θ a ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (ξ x) :=
  WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun _ => lp.norm_le_of_forall_le (norm_nonneg a) (fun _ => a.norm_coe_le_norm _))
    (fun _ => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable) ξ

theorem representation_coordinates_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      representation θ a ξ x k = a (action θ k x) * ξ x k := by
  filter_upwards [representation_ae θ a ξ] with x hx
  intro k
  rw [hx]
  rfl

@[simp] theorem character_norm (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem operator_ext_of_coordinates {A B : Hilbert →L[ℂ] Hilbert}
    (h : ∀ ξ : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, A ξ x k = B ξ x k) : A = B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [h ξ] with x hx
  exact lp.ext (funext hx)

@[simp] theorem representation_one (θ : ℝ) : representation θ 1 = 1 := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ 1 ξ] with x hx
  intro k
  simpa only [ContinuousMap.one_apply, one_mul, one_apply_eq_self] using hx k

@[simp] theorem representation_mul (θ : ℝ) (a b : C(Circle, ℂ)) :
    representation θ (a * b) = representation θ a * representation θ b := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (a * b) ξ,
    representation_coordinates_ae θ a (representation θ b ξ),
    representation_coordinates_ae θ b ξ] with x hab ha hb
  intro k
  change representation θ (a * b) ξ x k =
    representation θ a (representation θ b ξ) x k
  rw [hab k, ha k, hb k, ContinuousMap.mul_apply]
  ring

@[simp] theorem representation_add (θ : ℝ) (a b : C(Circle, ℂ)) :
    representation θ (a + b) = representation θ a + representation θ b := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (a + b) ξ,
    representation_coordinates_ae θ a ξ, representation_coordinates_ae θ b ξ,
    Lp.coeFn_add (representation θ a ξ) (representation θ b ξ)] with x hab ha hb hs
  intro k
  change representation θ (a + b) ξ x k =
    ((representation θ a ξ + representation θ b ξ) x) k
  rw [hs]
  change representation θ (a + b) ξ x k =
    representation θ a ξ x k + representation θ b ξ x k
  rw [hab k, ha k, hb k, ContinuousMap.add_apply]
  ring

@[simp] theorem representation_smul (θ : ℝ) (c : ℂ) (a : C(Circle, ℂ)) :
    representation θ (c • a) = c • representation θ a := by
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ (c • a) ξ,
    representation_coordinates_ae θ a ξ, Lp.coeFn_smul c (representation θ a ξ)] with x hca ha hs
  intro k
  change representation θ (c • a) ξ x k = ((c • representation θ a ξ) x) k
  rw [hs]
  change representation θ (c • a) ξ x k = c * representation θ a ξ x k
  rw [hca k, ha k]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

@[simp] theorem representation_star (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ (star a) = star (representation θ a) := by
  unfold representation
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Filter.Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

@[simp] theorem representation_zero (θ : ℝ) : representation θ 0 = 0 := by
  have hzero : (0 : ℂ) • (1 : C(Circle, ℂ)) = 0 := by
    ext x
    simp
  calc
    representation θ 0 = representation θ ((0 : ℂ) • (1 : C(Circle, ℂ))) :=
      congrArg (representation θ) hzero.symm
    _ = (0 : ℂ) • representation θ (1 : C(Circle, ℂ)) := representation_smul θ 0 1
    _ = 0 := by
      ext vector
      simp

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

@[simp]
theorem diagonal_apply (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    diagonal a C hC ha v i = a i * v i := rfl

@[simp]
theorem diagonal_single [DecidableEq I]
    (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (i : I) (z : ℂ) :
    diagonal a C hC ha (lp.single 2 i z) = lp.single 2 i (a i * z) := by
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

end Invariant233.SequenceHilbert

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterOrbitIdentity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Invariant233

namespace CircleParameterLaws
open CircleParameterData Rotation WeightedShift
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

abbrev parameterOrbitWeight (x : Circle) : Weight :=
  Rotation.measurableOrbitWeight θ (fun z => (p.measurableWeight θ z : ℂ)) 1
    (p.measurableWeight_operator_bound θ hp) x

end CircleParameterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SawtoothSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

def smoothSawtooth (δ u : ℝ) : ℝ :=
  (2 * δ)⁻¹ * ∫ t in -δ..δ, Int.fract (u + t)

def smoothedDrop (C α δ u : ℝ) : ℝ :=
  C * (α + smoothSawtooth δ u - smoothSawtooth δ (u + α))

end InvariantProjection.Continuity

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

def circleSmoothSawtooth (δ : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  AddCircle.liftIco 1 0 (smoothSawtooth δ)

def circleSmoothedDrop (C a δ : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  C * (a + circleSmoothSawtooth δ x - circleSmoothSawtooth δ (x + (a : AddCircle (1 : ℝ))))

def circleSmoothingTransfer (C δ : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  C * (circleSmoothSawtooth δ x - (AddCircle.equivIco 1 0 x : ℝ))

end InvariantProjection.Continuity

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ParameterSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

open InvariantProjection.Continuity

def smoothBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4)
    ((p.q i : ℤ) • x)

def rawBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, p.C j * (⌊p.coordinate i x + p.alpha θ i⌋ : ℝ)

def smoothBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, circleSmoothingTransfer (p.C j) (p.alpha θ i / 4)
    ((p.q i : ℤ) • x)

def relocatedBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) : Circle → ℝ :=
  relocated (Equiv.addRight (θ : Circle)) (p.smoothBlock θ j)
    (fun n x => p.partition j n x) (p.height j)

def relocatedBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) : Circle → ℝ :=
  relocationTransfer (Equiv.addRight (θ : Circle)) (p.smoothBlock θ j)
    (fun n x => p.partition j n x) (p.height j)

def relocatedCost (p : CircleParameterData) (θ : ℝ) (x : Circle) : ℝ :=
  ∑' n : ℕ, p.relocatedBlock θ (n + 1) x

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SawtoothSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set

theorem intervalIntegrable_fract (a b : ℝ) :
    IntervalIntegrable Int.fract volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
  · exact measurable_fract.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      change ‖Int.fract x‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      exact (Int.fract_lt_one x).le)

theorem fract_fract_add (u a : ℝ) :
    Int.fract (Int.fract u + a) = Int.fract (u + a) := by
  have hu : u + a = (Int.fract u + a) + (⌊u⌋ : ℝ) := by
    have := Int.fract_add_floor u
    linarith
  rw [hu, Int.fract_add_intCast]

theorem floor_drop_eq_sawtooth_difference (u a : ℝ) :
    (⌊Int.fract u + a⌋ : ℝ) = a + Int.fract u - Int.fract (u + a) := by
  have ha := Int.floor_add_fract (Int.fract u + a)
  rw [fract_fract_add] at ha
  linarith

theorem smoothSawtooth_periodic (δ : ℝ) :
    Function.Periodic (smoothSawtooth δ) 1 := by
  intro u
  unfold smoothSawtooth
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have h : u + 1 + t = (u + t) + 1 := by ring
  change Int.fract (u + 1 + t) = Int.fract (u + t)
  rw [h, Int.fract_add_one]

theorem continuous_smoothSawtooth (δ : ℝ) : Continuous (smoothSawtooth δ) := by
  have hc := intervalIntegral.continuous_primitive intervalIntegrable_fract 0
  have heq (u : ℝ) : smoothSawtooth δ u =
      (2 * δ)⁻¹ * ((∫ t in 0..u + δ, Int.fract t) -
        ∫ t in 0..u - δ, Int.fract t) := by
    unfold smoothSawtooth
    rw [intervalIntegral.integral_comp_add_left]
    have ht := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fract 0 (u - δ))
      (intervalIntegrable_fract (u - δ) (u + δ))
    congr 1
    change (∫ t in u - δ..u + δ, Int.fract t) = _
    linarith
  have hf : smoothSawtooth δ = fun u =>
      (2 * δ)⁻¹ * ((∫ t in 0..u + δ, Int.fract t) -
        ∫ t in 0..u - δ, Int.fract t) := funext heq
  rw [hf]
  exact continuous_const.mul ((hc.comp (continuous_id.add_const δ)).sub
    (hc.comp (continuous_id.sub continuous_const)))

theorem intervalIntegrable_fract_add (u a b : ℝ) :
    IntervalIntegrable (fun t => Int.fract (u + t)) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
  · exact (measurable_const.add measurable_id).fract.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      change ‖Int.fract (u + t)‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le)

theorem smoothedDrop_eq_average (C a δ u : ℝ) (hδ : δ ≠ 0) :
    smoothedDrop C a δ u = C * (2 * δ)⁻¹ *
      ∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ) := by
  have hiu := intervalIntegrable_fract_add u (-δ) δ
  have hiua := intervalIntegrable_fract_add (u + a) (-δ) δ
  have hi : (∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ)) =
      (2 * δ) * a + (∫ t in -δ..δ, Int.fract (u + t)) -
        (∫ t in -δ..δ, Int.fract (u + a + t)) := by
    calc
      _ = ∫ t in -δ..δ, a + Int.fract (u + t) - Int.fract (u + a + t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change (⌊Int.fract (u + t) + a⌋ : ℝ) = _
        rw [floor_drop_eq_sawtooth_difference]
        congr 2
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hiu) hiua,
          intervalIntegral.integral_add intervalIntegrable_const hiu,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  rw [hi]
  unfold smoothedDrop smoothSawtooth
  field_simp

theorem smoothedDrop_nonneg {C a δ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hδ : 0 < δ) (u : ℝ) : 0 ≤ smoothedDrop C a δ u := by
  rw [smoothedDrop_eq_average C a δ u hδ.ne']
  apply mul_nonneg
  · positivity
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg (Int.fract_nonneg _) ha)

theorem integral_smoothedDrop (C a δ : ℝ) :
    (∫ u in (0 : ℝ)..1, smoothedDrop C a δ u) = C * a := by
  have hs := continuous_smoothSawtooth δ
  have hshift : (∫ u in (0 : ℝ)..1, smoothSawtooth δ (u + a)) =
      ∫ u in (0 : ℝ)..1, smoothSawtooth δ u := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm (1 : ℝ) a] using
      (smoothSawtooth_periodic δ).intervalIntegral_add_eq a 0
  unfold smoothedDrop
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (f := fun u : ℝ => a + smoothSawtooth δ u)
      (g := fun u : ℝ => smoothSawtooth δ (u + a))
      (intervalIntegrable_const.add (hs.intervalIntegrable 0 1))
      ((hs.comp (continuous_id.add_const a)).intervalIntegrable 0 1),
    intervalIntegral.integral_add
      (f := fun _ : ℝ => a) (g := smoothSawtooth δ)
      intervalIntegrable_const (hs.intervalIntegrable 0 1),
    intervalIntegral.integral_const, hshift]
  simp

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set
local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem periodic_apply_fract {f : ℝ → ℝ} (hf : Function.Periodic f 1) (u : ℝ) :
    f (Int.fract u) = f u := by
  simpa only [Int.fract, zsmul_eq_mul, mul_one] using hf.sub_zsmul_eq (x := u) ⌊u⌋

@[simp] theorem circleSmoothSawtooth_coe (δ u : ℝ) :
    circleSmoothSawtooth δ (u : Circle) = smoothSawtooth δ u := by
  change smoothSawtooth δ (rep (u : Circle)) = smoothSawtooth δ u
  rw [Invariant233.CircleCharacterDynamics.representative_coe]
  exact periodic_apply_fract (smoothSawtooth_periodic δ) u

theorem continuous_circleSmoothSawtooth (δ : ℝ) :
    Continuous (circleSmoothSawtooth δ) := by
  apply AddCircle.liftIco_zero_continuous
  · simpa only [zero_add] using (smoothSawtooth_periodic δ 0).symm
  · exact (continuous_smoothSawtooth δ).continuousOn

@[simp] theorem circleSmoothedDrop_coe (C a δ u : ℝ) :
    circleSmoothedDrop C a δ (u : Circle) = smoothedDrop C a δ u := by
  unfold circleSmoothedDrop smoothedDrop
  simp only [← AddCircle.coe_add, circleSmoothSawtooth_coe]

theorem circleSmoothedDrop_eq_representative (C a δ : ℝ) (x : Circle) :
    circleSmoothedDrop C a δ x = smoothedDrop C a δ (rep x) := by
  rw [← circleSmoothedDrop_coe]
  exact congrArg (circleSmoothedDrop C a δ) AddCircle.coe_equivIco.symm

theorem continuous_circleSmoothedDrop (C a δ : ℝ) :
    Continuous (circleSmoothedDrop C a δ) := by
  unfold circleSmoothedDrop
  exact continuous_const.mul
    ((continuous_const.add (continuous_circleSmoothSawtooth δ)).sub
      ((continuous_circleSmoothSawtooth δ).comp (continuous_id.add_const (a : Circle))))

theorem circleSmoothedDrop_nonneg {C a δ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hδ : 0 < δ) (x : Circle) : 0 ≤ circleSmoothedDrop C a δ x := by
  rw [circleSmoothedDrop_eq_representative]
  exact smoothedDrop_nonneg hC ha hδ _

theorem integral_circleSmoothedDrop (C a δ : ℝ) :
    (∫ x : Circle, circleSmoothedDrop C a δ x) = C * a := by
  rw [← UnitAddCircle.intervalIntegral_preimage 0]
  simp only [circleSmoothedDrop_coe]
  simpa only [zero_add] using integral_smoothedDrop C a δ

theorem continuous_characterSmoothedDrop (C a δ : ℝ) (q : ℤ) :
    Continuous (fun x : Circle => circleSmoothedDrop C a δ (q • x)) :=
  (continuous_circleSmoothedDrop C a δ).comp (continuous_id.zsmul q)

theorem integral_characterSmoothedDrop (C a δ : ℝ) {q : ℤ} (hq : q ≠ 0) :
    (∫ x : Circle, circleSmoothedDrop C a δ (q • x)) = C * a := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hm : AEStronglyMeasurable (circleSmoothedDrop C a δ)
      (Measure.map (fun x : Circle => q • x) volume) := by
    rw [hp.map_eq]
    exact (continuous_circleSmoothedDrop C a δ).aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at he
  exact he.symm.trans (integral_circleSmoothedDrop C a δ)

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open MeasureTheory Set InvariantProjection.Continuity
open scoped ENNReal

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_pos (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i ∈ p.block j) :
    0 < p.alpha θ i := by
  have hN : 0 < p.N j := by
    unfold CircleParameterData.N
    exact mul_pos (Nat.cast_pos.mpr (hp.m_pos j hj)) (Nat.cast_pos.mpr (hp.K_pos j hj))
  exact (one_div_pos.mpr hN).trans (hp.phase_bounds j hj i hi).1

omit hp in

theorem continuous_smoothBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) :
    Continuous (p.smoothBlock θ j) := by
  unfold CircleParameterData.smoothBlock
  exact continuous_finsetSum _ (fun i _ => continuous_characterSmoothedDrop _ _ _ _)

theorem smoothBlock_nonneg (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    0 ≤ p.smoothBlock θ j x := by
  apply Finset.sum_nonneg
  intro i hi
  apply circleSmoothedDrop_nonneg (hp.C_pos j hj).le
    (hp.block_phase_pos j hj i hi).le
  exact div_pos (hp.block_phase_pos j hj i hi) (by norm_num)

theorem integral_smoothBlock (j : ℕ) :
    (∫ x, p.smoothBlock θ j x) = p.C j * ∑ i ∈ p.block j, p.alpha θ i := by
  unfold CircleParameterData.smoothBlock
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_characterSmoothedDrop _ _ _ (by exact_mod_cast (hp.q_pos i).ne')
  · intro i hi
    exact (continuous_characterSmoothedDrop _ _ _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit hp in

theorem continuous_relocatedBlock (j : ℕ) : Continuous (p.relocatedBlock θ j) := by
  exact continuous_relocated (Homeomorph.addRight (θ : Circle)) _ _ _
    (continuous_smoothBlock p θ j) (fun n _ => (p.partition j n).continuous)

theorem relocatedBlock_nonneg (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    0 ≤ p.relocatedBlock θ j x := by
  exact relocated_nonneg _ _ _ _ (hp.smoothBlock_nonneg j hj)
    (hp.partition_nonneg j hj) x

theorem support_relocatedBlock_subset (j : ℕ) (hj : 1 ≤ j) :
    Function.support (p.relocatedBlock θ j) ⊆
      Metric.ball (0 : Circle) (1 / (10 * (j : ℝ))) := by
  apply support_relocated_subset
  intro n hn
  rintro y ⟨x, hx, rfl⟩
  change dist (((fun z : Circle => z + (θ : Circle))^[n]) x) 0 < _
  rw [add_right_iterate]
  have hs := hp.partition_support j hj n hn x (subset_tsupport _ hx)
  simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using hs

theorem integral_relocatedBlock (j : ℕ) (hj : 1 ≤ j) :
    (∫ x, p.relocatedBlock θ j x) = p.C j * ∑ i ∈ p.block j, p.alpha θ i := by
  have ht : (∫ x, p.relocatedBlock θ j x) = ∫ x, p.smoothBlock θ j x := by
    apply integral_relocated (MeasurableEquiv.addRight (θ : Circle))
      (measurePreserving_add_right volume _)
    · intro n hn
      exact ((continuous_smoothBlock p θ j).mul (p.partition j n).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact hp.partition_sum j hj
  exact ht.trans (hp.integral_smoothBlock j)

theorem block_phase_sum_ge (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.K j : ℝ) ≤ ∑ i ∈ p.block j, p.alpha θ i := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    _ = ∑ _i ∈ p.block j, 1 / p.N j := by
      simp only [Finset.sum_const, nsmul_eq_mul, p.card_block j hj, CircleParameterData.N]
      field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i hi => (hp.phase_bounds j hj i hi).1.le)

theorem integral_relocatedBlock_ge_K (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) ≤ ∫ x, p.relocatedBlock θ j x := by
  have hK : 0 < (p.K j : ℝ) := Nat.cast_pos.mpr (hp.K_pos j hj)
  have hC : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j hj]
    exact le_max_right _ _
  rw [hp.integral_relocatedBlock j hj]
  calc
    (p.K j : ℝ) ≤ p.C j * (1 / (p.K j : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hK]
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.block_phase_sum_ge j hj) (hp.C_pos j hj).le

omit hp in
theorem shrinking_radius_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => 1 / (10 * ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 10
  convert ht using 1
  · funext n
    push_cast
    field_simp
  · norm_num

theorem relocatedBlock_locally_finite :
    ∀ x : Circle, x ≠ 0 → ∃ s : Finset ℕ,
      ∀ᶠ y in nhds x, ∀ n ∉ s, p.relocatedBlock θ (n + 1) y = 0 := by
  apply BackgroundCost.locally_finite_of_support_shrinks 0 _ _ shrinking_radius_tendsto_zero
  intro n x hx
  exact (hp.support_relocatedBlock_subset (n + 1) (by omega) hx).le

theorem summable_relocatedBlock_of_ne_zero {x : Circle} (hx : x ≠ 0) :
    Summable (fun n : ℕ => p.relocatedBlock θ (n + 1) x) := by
  obtain ⟨s, hs⟩ := hp.relocatedBlock_locally_finite x hx
  exact summable_of_ne_finset_zero (mem_of_mem_nhds hs)

theorem continuousOn_relocatedCost : ContinuousOn (p.relocatedCost θ) ({0}ᶜ : Set Circle) := by
  exact BackgroundCost.continuousOn_tsum_of_locally_finite _ _
    (fun n => continuous_relocatedBlock (p := p) (θ := θ) (n + 1))
    (fun x hx => hp.relocatedBlock_locally_finite x hx)

theorem relocatedCost_nonneg (x : Circle) : 0 ≤ p.relocatedCost θ x :=
  tsum_nonneg (fun n => hp.relocatedBlock_nonneg (n + 1) (by omega) x)

theorem ae_summable_relocatedBlock :
    ∀ᵐ x : Circle, Summable (fun n : ℕ => p.relocatedBlock θ (n + 1) x) := by
  have hzero : volume ({0} : Set Circle) = 0 := by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num
  have hne : ∀ᵐ x : Circle, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using hzero
  exact hne.mono (fun x hx => hp.summable_relocatedBlock_of_ne_zero hx)

theorem lintegral_relocatedCost_eq_top :
    (∫⁻ x : Circle, ENNReal.ofReal (p.relocatedCost θ x)) = ⊤ := by
  have hsum : (∫⁻ x : Circle, ENNReal.ofReal (p.relocatedCost θ x)) =
      ∑' n : ℕ, ∫⁻ x : Circle, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
    calc
      _ = ∫⁻ x : Circle, ∑' n : ℕ, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
        apply lintegral_congr_ae
        exact hp.ae_summable_relocatedBlock.mono (fun x hx =>
          ENNReal.ofReal_tsum_of_nonneg
            (fun n => hp.relocatedBlock_nonneg (n + 1) (by omega) x) hx)
      _ = _ := lintegral_tsum (fun n =>
        (continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).measurable.ennreal_ofReal.aemeasurable)
  rw [hsum]
  apply top_unique
  calc
    ⊤ = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' n : ℕ, ∫⁻ x : Circle, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (Filter.Eventually.of_forall (hp.relocatedBlock_nonneg (n + 1) (by omega)))]
      apply ENNReal.one_le_ofReal.mpr
      have hK : (1 : ℝ) ≤ p.K (n + 1) := by
        exact_mod_cast hp.K_pos (n + 1) (by omega)
      exact hK.trans (hp.integral_relocatedBlock_ge_K (n + 1) (by omega))

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_RationalGraphTrimming
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.CircleParameterData

def orbitGraphDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (x : Circle) : ℝ :=
  ∏ i ∈ p.block j, kernel (p.m j) (p.coordinate i x)
    (Int.fract ((n : ℝ) * p.alpha θ i))

def rationalGraphGood (p : CircleParameterData) (A j : ℕ) : Set Circle :=
  {x | (∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
      p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) ∧
    ∀ s, j < s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * p.Q j / p.N s}

def rationalGraphPrefixCost (p : CircleParameterData) (A : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (A - 1), p.flattenedCost k

def rationalGraphBad (p : CircleParameterData) (A j : ℕ) : Set Circle :=
  (p.rationalGraphGood A j)ᶜ

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingKernelBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
namespace Invariant233.CircleParameterData

theorem measurable_rep : Measurable rep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable

theorem measurable_coordinate (p : CircleParameterData) (i : ℕ) :
    Measurable (p.coordinate i) := by
  exact measurable_rep.comp (continuous_nsmul (p.q i)).measurable

theorem measurable_kernel (m : ℕ) (v : ℝ) : Measurable (fun z => kernel m z v) := by
  have hd : Measurable delta := measurable_fract.min (measurable_const.sub measurable_fract)
  unfold kernel
  apply Measurable.ite
  · exact (measurableSet_le measurable_const hd).inter
      ((MeasurableSet.const (0 < v)).inter
        (measurableSet_lt measurable_const (measurable_const.mul hd)))
  · exact measurable_const.div (measurable_const.mul hd)
  · exact measurable_const

theorem measurable_orientedKernel (endpoint : Bool) (m : ℕ) (v : ℝ) :
    Measurable (fun z => orientedKernel endpoint m z v) := by
  cases endpoint
  · exact measurable_kernel m v
  · exact (measurable_kernel m v).comp (measurable_id.sub_const v)

theorem measurable_samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) : Measurable (p.samplingAverage θ j r endpoint) := by
  unfold samplingAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_orientedKernel endpoint (p.m j)
    (Int.fract ((n : ℝ) * p.alpha θ i))).comp (p.measurable_coordinate i)

end Invariant233.CircleParameterData

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingLp
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.CircleParameterData.blockEnd_zero _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem kernel_bounds {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ kernel m z v ∧ kernel m z v ≤ (m : ℝ)^2 / kernelWidth m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : (0 : ℝ) < (m : ℝ)^2 := sq_pos_of_pos hmR
  have hw : 0 < kernelWidth m := Real.rpow_pos_of_pos hmR _
  unfold kernel
  split_ifs with h
  · have hd : 0 < delta z := (one_div_pos.mpr hsq).trans_le h.1
    refine ⟨by positivity, ?_⟩
    calc
      1 / (kernelWidth m * delta z) ≤
          1 / (kernelWidth m * (1 / (m : ℝ)^2)) :=
        one_div_le_one_div_of_le (mul_pos hw (one_div_pos.mpr hsq))
          (mul_le_mul_of_nonneg_left h.1 hw.le)
      _ = (m : ℝ)^2 / kernelWidth m := by field_simp
  · exact ⟨le_rfl, by positivity⟩

theorem orientedKernel_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ orientedKernel endpoint m z v ∧
      orientedKernel endpoint m z v ≤ (m : ℝ)^2 / kernelWidth m := by
  cases endpoint
  · exact kernel_bounds hm z v
  · exact kernel_bounds hm (z - v) v

theorem samplingAverage_bounds (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (x : Circle) :
    0 ≤ p.samplingAverage θ j r endpoint x ∧
      p.samplingAverage θ j r endpoint x ≤
        ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
  classical
  have hb : 0 ≤ (p.m j : ℝ)^2 / kernelWidth (p.m j) := by
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hprod (n : ℕ) :
      0 ≤ ∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i)) := by
    exact Finset.prod_nonneg fun i _ => (orientedKernel_bounds endpoint hm _ _).1
  have hprod_le (n : ℕ) :
      (∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i))) ≤
        ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
    calc
      _ ≤ ∏ _i ∈ p.block j, (p.m j : ℝ)^2 / kernelWidth (p.m j) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact (orientedKernel_bounds endpoint hm _ _).1
        · intro i hi
          exact (orientedKernel_bounds endpoint hm _ _).2
      _ = _ := by simp [div_pow]
  unfold samplingAverage
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hprod n), ?_⟩
  by_cases hs : (p.samples j r).card = 0
  · simp only [hs, Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg hb _
  · have hsR : ((p.samples j r).card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      _ ≤ (1 / ((p.samples j r).card : ℝ)) *
          ∑ _n ∈ p.samples j r,
            ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hprod_le n)
        positivity
      _ = _ := by simp [hsR]

theorem memLp_samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (s : ENNReal) :
    MemLp (p.samplingAverage θ j r endpoint) s circleMeasure := by
  let : IsFiniteMeasure circleMeasure := by
    unfold circleMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply MemLp.of_bound (p.measurable_samplingAverage θ j r endpoint).aestronglyMeasurable
    (((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card)
  apply Filter.Eventually.of_forall
  intro x
  have h := p.samplingAverage_bounds θ j r endpoint hm x
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphTrimming
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimming_frequency_dvd_of_le {a b : ℕ} (hab : a ≤ b) : p.q a ∣ p.q b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b _ ih => exact ih.trans (hp.frequency_divisible b)

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_UniformQuantization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.UniformQuantization

def quantize (q : ℕ) [NeZero q] (x : ℝ) : Fin q :=
  ⟨⌊(q : ℝ) * x⌋₊ % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩

def binAverage (q : ℕ) [NeZero q] (h : ℝ → ℝ) (a : Fin q) : ℝ :=
  (q : ℝ) * ∫ x in {x | quantize q x = a}, h x ∂volume.restrict (Ico (0 : ℝ) 1)

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformQuantization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformQuantization

theorem measurable_quantize (q : ℕ) [NeZero q] : Measurable (quantize q) := by
  exact (measurable_of_countable (fun n : ℕ =>
    (⟨n % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩ : Fin q))).comp
    ((measurable_const.mul measurable_id).nat_floor)

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingParameters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma coupling_kappa_bounds (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ kappa j ∧ kappa j ≤ 1 / 100 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold kappa
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by norm_num)
    nlinarith

lemma coupling_a_bounds (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.m j : ℝ) ≤ p.a j ∧ p.a j ≤ 1 / 4 := by
  have hm : (0 : ℝ) < p.m j := by exact_mod_cast hp.m_pos j hj
  have hG : (1 : ℝ) ≤ p.G j := by exact_mod_cast hp.G_pos j hj
  have hGm : 4 * (p.G j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_G j hj
  unfold a
  exact ⟨div_le_div_of_nonneg_right hG hm.le, (div_le_iff₀ hm).mpr (by linarith)⟩

lemma coupling_b_bounds (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.m j : ℝ) ≤ p.b j ∧ p.b j ≤ 1 / 4 := by
  have hm : (200 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_200 j hj
  have hm1 : (1 : ℝ) ≤ p.m j := by linarith
  have hm0 : (0 : ℝ) < p.m j := by linarith
  constructor
  · simpa only [b, one_div, Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hm1 (show (-1 : ℝ) ≤ -(19 / 20 : ℝ) by norm_num))
  · have hs : (4 : ℝ) ≤ Real.sqrt (p.m j) := by
      apply (Real.le_sqrt (by norm_num) hm0.le).mpr
      nlinarith
    have hpw : (4 : ℝ) ≤ (p.m j : ℝ) ^ (19 / 20 : ℝ) := by
      calc
        _ ≤ Real.sqrt (p.m j) := hs
        _ = (p.m j : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
    rw [b, Real.rpow_neg hm0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hpw

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

abbrev Label := Option (Fin 5)
abbrev CoordinateSample := Label × (ℝ × ℝ)

def endpointLaw (side : Bool) (m a b : ℝ) : Label → Measure ℝ
  | none => baseLaw
  | some i => if side then rightLaw (2 * m) a b i else leftLaw (2 * m) a b i

def endpointDensity (side : Bool) (m a b : ℝ) : Label → ℝ → ℝ
  | none => fun _ => 1
  | some i => if side then rightDensity (2 * m) a b i else leftDensity (2 * m) a b i

def marginalDensity (side : Bool) (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * endpointDensity side m a b (some i) x

def labelMass (κ m a b t : ℝ) : Label → ℝ≥0∞
  | none => ENNReal.ofReal (diagonalMass κ m a b t)
  | some i => ENNReal.ofReal (componentProbabilities κ m a b t i)

def rawLaw (κ m a b t : ℝ) : Measure CoordinateSample :=
  labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)

def endpoint (side : Bool) (z : CoordinateSample) : ℝ :=
  if side then z.2.2 else z.2.1

def bin (r : ℕ) (d : Fin r) : Set ℝ :=
  Set.Ico ((d : ℝ) / r) (((d : ℝ) + 1) / r)

def digitJoint (side : Bool) (r : ℕ) [NeZero r] (κ m a b t : ℝ) :
    Measure (Fin r × Label) :=
  (rawLaw κ m a b t).map (fun z =>
    (UniformQuantization.quantize r (endpoint side z), z.1))

def digitWeight (side : Bool) (r : ℕ) (κ m a b t : ℝ)
    (l : Label) (d : Fin r) : ℝ≥0∞ :=
  labelMass κ m a b t l * endpointLaw side m a b l (bin r d)

def labelsGivenDigit (side : Bool) (r : ℕ) (κ m a b t : ℝ) : Kernel (Fin r) Label :=
  FiniteKernelMixture.normalizedKernel
    (fun l => Kernel.const (Fin r) (Measure.dirac l))
    (digitWeight side r κ m a b t)
    (fun _ => measurable_of_countable _)

def width (a b : ℝ) (which : Bool) : ℝ := if which then b else a

def topLabel (which : Bool) : Label := some (if which then 2 else 0)
def bottomLabel (which : Bool) : Label := some (if which then 3 else 1)

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleCoupling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

abbrev Sample := ℕ → CoordinateSample

def initialLaw : Measure CoordinateSample :=
  baseLaw.map (fun x => (none, (x, x)))

def tag (j s : ℕ) : ℝ := if s = j then 1 else 0

def coordinateLaw (p : CircleParameterData) (j i : ℕ) : Measure CoordinateSample :=
  if i = 0 then initialLaw else
    rawLaw (kappa (p.blockIndex i)) (p.m (p.blockIndex i))
      (p.a (p.blockIndex i)) (p.b (p.blockIndex i)) (tag j (p.blockIndex i))

def law (p : CircleParameterData) (j : ℕ) : Measure Sample :=
  Measure.infinitePi (coordinateLaw p j)

def observedDigit (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (i : ℕ) (z : CoordinateSample) : Fin (MixedRadix.radices p.q i) := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact UniformQuantization.quantize (MixedRadix.radices p.q i) (endpoint side z)

def digits (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) : MixedRadix.Digits (MixedRadix.radices p.q) :=
  fun i => observedDigit p hr side i (ω i)

def point (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) : Circle := MixedRadix.circleValue (digits p hr side ω)

def label (i : ℕ) (ω : Sample) : Label := (ω i).1

def posterior (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) :
    Kernel (Fin (MixedRadix.radices p.q i)) Label :=
  if i = 0 then Kernel.const _ (Measure.dirac none) else
    labelsGivenDigit side (MixedRadix.radices p.q i) (kappa (p.blockIndex i))
      (p.m (p.blockIndex i)) (p.a (p.blockIndex i)) (p.b (p.blockIndex i))
      (tag j (p.blockIndex i))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma labelMass_sum : (∑ l, labelMass κ m a b t l) = 1 := by
  have hm0 : 0 < m := by linarith
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  rw [Fintype.sum_option]
  change ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i),
    ← ENNReal.ofReal_add hq0 (Finset.sum_nonneg (fun i _ => hp0 i))]
  have heq : diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i = 1 := by
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    unfold diagonalMass
    ring
  rw [heq]
  norm_num

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma rawLaw_isProbabilityMeasure : IsProbabilityMeasure (rawLaw κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  apply labelledMixture_isProbabilityMeasure
  have h := labelMass_sum hκ0 hκ hm ha ha' hb hb' ht0 ht
  simpa only [Fintype.sum_option, labelMass] using h

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingLaw
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma tag_bounds (j s : ℕ) : 0 ≤ tag j s ∧ tag j s ≤ 1 := by
  unfold tag
  split_ifs <;> norm_num

lemma initialLaw_isProbabilityMeasure : IsProbabilityMeasure initialLaw := by
  have := baseLaw_isProbabilityMeasure
  unfold initialLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinateLaw_isProbabilityMeasure (j i : ℕ) :
    IsProbabilityMeasure (coordinateLaw p j i) := by
  by_cases hi : i = 0
  · simpa [coordinateLaw, hi] using initialLaw_isProbabilityMeasure
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  simpa only [coordinateLaw, ite_eq_right hi] using rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (tag_bounds j _).1 (tag_bounds j _).2

lemma law_isProbabilityMeasure (j : ℕ) : IsProbabilityMeasure (law p j) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit hp in
lemma measurable_observedDigit (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (i : ℕ) : Measurable (observedDigit p hr side i) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  change Measurable (UniformQuantization.quantize _ ∘ endpoint side)
  apply (UniformQuantization.measurable_quantize _).comp
  cases side
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

omit hp in
lemma measurable_digits (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    Measurable (digits p hr side) := by
  exact Measurable.of_eval (fun i =>
    (measurable_observedDigit hr side i).comp (measurable_pi_apply i))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem measurable_circleValue {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Measurable (@circleValue r) :=
  AddCircle.measurable_mk'.comp (measurable_ofDigits hr)

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingConditioning
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma measurable_point (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    Measurable (point p hr side) :=
  (MixedRadix.measurable_circleValue
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)).comp
    (measurable_digits hr side)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_BackgroundData
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233

structure BackgroundBumpData (θ : ℝ) where
  radius : ℕ → ℝ
  bump : ℕ → Circle → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_lt : ∀ n, radius n < 1 / ((n : ℝ) + 1)
  continuous_bump : ∀ n, Continuous (bump n)
  bump_zero : ∀ n, bump n 0 = 1
  bump_bounds : ∀ n x, 0 ≤ bump n x ∧ bump n x ≤ 1
  bump_support : ∀ n, Function.support (bump n) ⊆ Metric.closedBall 0 (radius n)
  disjoint_translates : ∀ n, Pairwise (fun i j : Fin (2 ^ (n + 2)) =>
    Disjoint
      ((fun x : Circle => x + ((i : ℕ) + 1) • (θ : Circle)) ''
        Metric.closedBall 0 (radius n))
      ((fun x : Circle => x + ((j : ℕ) + 1) • (θ : Circle)) ''
        Metric.closedBall 0 (radius n)))
  weighted_support_bound :
    (∑' n, (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (radius n))) ≤ 1 / 2

def backgroundNegative {θ : ℝ} (d : BackgroundBumpData θ) (n : ℕ) (x : Circle) : ℝ :=
  InvariantProjection.Continuity.backwardAverage (Equiv.addRight (θ : Circle))
    (d.bump n) (2 ^ (n + 2)) x

def backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) : ℝ :=
  1 + (∑' n, d.bump n x) - (∑' n, backgroundNegative d n x)

def backgroundTransferSum {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) : ℝ :=
  ∑' n, InvariantProjection.Continuity.backgroundTransfer (Equiv.addRight (θ : Circle))
    (d.bump n) (2 ^ (n + 2)) x

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CharacterLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CharacterLaws

open MeasureTheory

def circleHaar : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨volume, ⟨by simp [AddCircle.measure_univ]⟩⟩

def torusHaar (m : ℕ) : ProbabilityMeasure (UnitAddTorus (Fin m)) := by
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    circleHaar.property
  exact ⟨volume, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def characterMap {m : ℕ} (q : Fin m → ℕ) :
    C(AddCircle (1 : ℝ), UnitAddTorus (Fin m)) :=
  ⟨fun x i => (q i : ℤ) • x, by fun_prop⟩

def characterPhaseLaw {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] {m : ℕ} (q : Fin m → ℕ) (a : Z) :
    ProbabilityMeasure (Z × UnitAddTorus (Fin m)) :=
  circleHaar.map (f := fun x => (a, characterMap q x)) (measurable_const.prodMk (characterMap q).continuous.measurable).aemeasurable

def haarPhaseLaw {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (m : ℕ) (a : Z) : ProbabilityMeasure (Z × UnitAddTorus (Fin m)) :=
  (torusHaar m).map (f := fun y => (a, y)) (measurable_const.prodMk measurable_id).aemeasurable

end Invariant233.CharacterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleDigitMarginals
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData

def hybridDigits (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) (ω : Sample) :
    MixedRadix.Digits (MixedRadix.radices p.q) :=
  fun i => observedDigit p hr (ε i) i (ω i)

def hybridPoint (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) (ω : Sample) : Circle :=
  MixedRadix.circleValue (hybridDigits p hr ε ω)

def rawDensity (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ => 1 else
    marginalDensity side (kappa (p.blockIndex i)) (p.m (p.blockIndex i))
      (p.a (p.blockIndex i)) (p.b (p.blockIndex i)) (tag j (p.blockIndex i))

def digitDensity (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (j : ℕ) (side : Bool) (i : ℕ) : Fin (MixedRadix.radices p.q i) → ℝ := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact UniformQuantization.binAverage (MixedRadix.radices p.q i) (rawDensity p j side i)

def digitReference (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (i : ℕ) : Measure (Fin (MixedRadix.radices p.q i)) := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact (PMF.uniformOfFintype (Fin (MixedRadix.radices p.q i))).toMeasure

def marginalBound : ℝ := Real.exp (25 * ((∑' s : ℕ, kappa s ^ 2) + 1))

def DigitMarginalLaws (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : Prop :=
  0 < marginalBound ∧ ∀ (j : ℕ) (ε : ℕ → Bool),
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal marginalBound ∧
      (law p j).map (hybridPoint p hr ε) =
        volume.withDensity (fun x => ENNReal.ofReal (H x))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleRationalGraphs
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

namespace CircleParameterData

def rationalTranslation (p : CircleParameterData) (A : ℕ) (r : ℤ) : Circle :=
  (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)

def rationalRatioBound (p : CircleParameterData) (A : ℕ) : ℝ :=
  Real.exp (∑ i ∈ Finset.range (A - 1), p.flattenedCost i)

def RationalGraphIdentities (p : CircleParameterData) (θ : ℝ)
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ) : Prop :=
  ∀ᵐ x ∂circleMeasure, ∀ A : ℕ, 1 ≤ A → ∀ r : ℤ,
    (1 - P (x + p.rationalTranslation A r)) *
      ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0

end CircleParameterData
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleOrderedCoupling
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleCoupling

def finiteHybridChoice (N i : ℕ) : Bool := decide (i < N + 1)

def finiteHybridPoint (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) : Sample → Circle :=
  hybridPoint p hr (finiteHybridChoice N)

def OrderedCouplingIdentities (p : CircleParameterData) (θ : ℝ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) : Prop :=
  ∀ j : ℕ, ∀ᵐ ω ∂law p j,
    (1 - F (point p hr true ω)) *
      ratioDiagonal (p.floorCocycle θ) (point p hr false ω, point p hr true ω) *
      F (point p hr false ω) = 0 ∧
    ∀ k : ℤ, 0 < p.floorCocycle θ k (point p hr true ω) /
      p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (point p hr true ω) /
      p.floorCocycle θ k (point p hr false ω) ≤ 1

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleSamplingGraph
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

def samplingDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) (x : Circle) : ℝ :=
  ∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
    (Int.fract ((n : ℝ) * p.alpha θ i))

def samplingTranslation (θ : ℝ) (n : ℕ) (x : Circle) : Circle :=
  x + (((n : ℝ) * θ : ℝ) : Circle)

def samplingGraph (p : CircleParameterData) (θ : ℝ) (j n : ℕ) :
    Measure (Circle × Circle) :=
  (circleMeasure.withDensity
    (fun x => ENNReal.ofReal (p.samplingDensity θ j n false x))).map
      (fun x => (x, samplingTranslation θ n x))

def samplingGraphAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ) :
    Measure (Circle × Circle) :=
  ENNReal.ofReal (1 / ((p.samples j r).card : ℝ)) •
    ∑ n ∈ p.samples j r, p.samplingGraph θ j n

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_StrictPhase
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

noncomputable def strictPhaseGoodCount {ι : Type*} (J : Finset ι) (b : ℝ)
    (k : ℤ) (θ : ι → ℝ) : ℕ := by
  classical
  exact (J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈
    Set.Ioo b (1 - b))).card

def strictLargePhaseCondition {ι : Type*} (J : Finset ι) (N : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, N / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card) →
    (J.card : ℝ) / 20 ≤
      (strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_TrialSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.TrialSampling

def average (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) (z : Fin m → Circle) : ℝ :=
  (samples.card : ℝ)⁻¹ * ∑ n ∈ samples, ∏ i : Fin m,
    CircleParameterData.orientedKernel endpoint m
      (CircleParameterData.rep (z i)) (Int.fract ((n : ℝ) * phase i))

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleSamplingStage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233

structure CircleSamplingStage (θ : ℝ) (j K d q₀ m : ℕ) (R : ℝ) where
  q : ℕ → ℕ
  samples : Fin q₀ → Finset ℕ
  q_zero : q 0 = q₀
  q_pos : ∀ i, 0 < q i
  q_strict : StrictMono q
  q_div : ∀ i, q i ∣ q (i + 1)
  q_ratio : ∀ i < m, R ≤ (q (i + 1) : ℝ) / q i
  phases : ∀ i : Fin m,
    Int.fract ((q (i.val + 1) : ℝ) * θ) ∈
      Ioo (1 / ((m : ℝ) * K)) (2 / ((m : ℝ) * K))
  spread : ProductPhases.strictLargePhaseCondition Finset.univ ((m : ℝ) * K)
    (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
  samples_nonempty : ∀ r, (samples r).Nonempty
  samples_positive : ∀ r, ∀ n ∈ samples r, 0 < n
  samples_range : ∀ r, ∀ n ∈ samples r,
    (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
      (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  samples_phase : ∀ r, ∀ n ∈ samples r,
    Int.fract ((n : ℝ) * θ - (r.val : ℝ) / q₀) ∈
      Ioo 0 (1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (d : ℝ)) * q₀))
  sampling_L2 : ∀ r endpoint,
    eLpNorm (fun x : Circle => TrialSampling.average m (samples r) endpoint
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
      (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
        ENNReal.ofReal (1 / (j : ℝ))

end Invariant233

namespace Invariant233

def CircleStageSupply (θ : ℝ) : Prop :=
  ∀ j K d q₀ : ℕ, 0 < j → 0 < K → 0 < q₀ →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ R : ℝ,
      Nonempty (CircleSamplingStage θ j K d q₀ m R)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleTailAttenuation
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.CircleCoupling

def tagEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  {ω | ∃ i ∈ p.block j, label i ω = some 4}

abbrev endpointSigma (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) : MeasurableSpace Sample :=
  MeasurableSpace.comap (point p hr side) inferInstance

def TailAttenuation (θ : ℝ) (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : Prop :=
  ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₁.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr false]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j,
        ((law p j)[H₂.indicator (fun _ => (1 : ℝ)) | endpointSigma p hr true]) ω ≤
          Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂law p j, ω ∈ tagEvent p j →
        p.floorCocycle θ k (point p hr true ω) /
          p.floorCocycle θ k (point p hr false ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleTruncationEvent
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

def truncationEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) : Set Sample :=
  {ω | (∀ i ∈ p.block j,
      (ω i).2.1 < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < (ω i).2.2) ∧
    ω ∈ tagEvent p j ∧
    (∀ s, j < s → ∀ i ∈ p.block s,
      (ω i).2.1 < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < (ω i).2.2) ∧
    1 / (j : ℝ) ≤ r (point p hr false ω) ∧
    1 / (j : ℝ) ≤ 1 - r (point p hr true ω)}

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ContinuousConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

def rawCost (p : CircleParameterData) (θ : ℝ) (x : Circle) : ℝ :=
  ∑' n : ℕ, p.rawBlock θ (n + 1) x

def continuousCost (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ)
    (x : Circle) : ℝ :=
  backgroundCost d x + ∑' n : ℕ, p.relocatedBlock θ (n + 1) x

def continuousTransfer (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ)
    (x : Circle) : ℝ :=
  backgroundTransferSum d x - ∑' n : ℕ,
    (p.smoothBlockTransfer θ (n + 1) x + p.relocatedBlockTransfer θ (n + 1) x)

def continuousWeight (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ) :
    Circle → ℝ :=
  Function.update (fun x => Real.exp (-p.continuousCost θ d x)) 0 0

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_DiagonalGauge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.DiagonalGauge

abbrev Circle := AddCircle (1 : ℝ)
abbrev Fiber := WeightedShift.Hilbert

def weight (t : Circle) : WeightedShift.Weight :=
  ⟨fun k => fourier k t, memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    exact (Circle.norm_coe _).le⟩

def fiberOperator (t : Circle) : Fiber →L[ℂ] Fiber :=
  WeightedShift.diagonal (weight t)

end Invariant233.DiagonalGauge

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_Fejer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.Fejer

abbrev Circle := AddCircle (1 : ℝ)

def frequencies (H : ℕ) : Finset ℤ := Finset.Ioo (-(H : ℤ)) (H : ℤ)

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_TrimmedCircleSamplingGraph
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleParameterData

def trimmedSamplingGraphAverage (p : CircleParameterData) (θ : ℝ)
    (A j r : ℕ) : Measure (Circle × Circle) :=
  (p.samplingGraphAverage θ j r).restrict (Prod.fst ⁻¹' p.rationalGraphGood A j)

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_AffiliatedTransportSupplement
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.AffiliatedTransport

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def imageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) : Submodule ℂ E :=
  (p.comap H.domain.subtype).map H.toFun

def closedImageOn (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) : Submodule ℂ E :=
  (imageOn H p).topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn [CompleteSpace E] (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E) :
    CompleteSpace (closedImageOn H p) := by
  unfold closedImageOn
  infer_instance

@[simp] theorem mem_imageOn {H : E →ₗ.[ℂ] E} {p : Submodule ℂ E} {y : E} :
    y ∈ imageOn H p ↔ ∃ x : H.domain, (x : E) ∈ p ∧ H x = y := by
  rfl

end Invariant233.AffiliatedTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_OperatorCompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal lp

noncomputable section
namespace Invariant233.CompactTransfer

local instance operatorCompactTransferSecondCountableTopology_rf379d0_1 :
    SecondCountableTopology (SequenceHilbert ℤ) := by
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ) |>.closure
  have : TopologicalSpace.SeparableSpace (SequenceHilbert ℤ) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      simpa only [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] using hs)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
def cappedDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X) :
    SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ :=
  SequenceHilbert.diagonal (fun i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B hB (by
    intro i
    have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
      le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
      (min_le_left B (F i t.2 / F i t.1)))

end Invariant233.CompactTransfer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_CoordinateSwap
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.CoordinateSwap

variable {X : Type*} [MeasurableSpace X]

def flatten : ((ℕ → X) × (ℕ → X)) ≃ᵐ (Fin 2 × ℕ → X) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.curry (Fin 2) ℕ X).symm

def swapIndex (I : Finset ℕ) : Fin 2 × ℕ ≃ Fin 2 × ℕ where
  toFun p := (if p.2 ∈ I then Equiv.swap 0 1 p.1 else p.1, p.2)
  invFun p := (if p.2 ∈ I then Equiv.swap 0 1 p.1 else p.1, p.2)
  left_inv p := by rcases p with ⟨a,n⟩; by_cases hn : n ∈ I <;> simp [hn]
  right_inv p := by rcases p with ⟨a,n⟩; by_cases hn : n ∈ I <;> simp [hn]

def swapEquiv (I : Finset ℕ) : ((ℕ → X) × (ℕ → X)) ≃ᵐ ((ℕ → X) × (ℕ → X)) :=
  (flatten.trans (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × ℕ => X) (swapIndex I))).trans
    flatten.symm

end Invariant233.CoordinateSwap

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ExponentialWeight
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Invariant233

section ExponentialExtension

variable {X : Type*} [TopologicalSpace X] [T1Space X] [DecidableEq X]
variable (a : X) (g : X → ℝ)

theorem continuous_exp_neg_update
    (hc : ContinuousOn g ({a}ᶜ))
    (hlim : Tendsto g (𝓝[≠] a) atTop) :
    Continuous (Function.update (fun x => Real.exp (-g x)) a 0) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = a
  · subst x
    rw [continuousAt_update_same]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim
  · rw [continuousAt_update_of_ne hx]
    have hgc : ContinuousAt g x :=
      (hc x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)
    exact Real.continuous_exp.continuousAt.comp hgc.neg

omit [TopologicalSpace X] [T1Space X] in

theorem exp_neg_update_mem_Icc (hg : ∀ x ≠ a, 0 ≤ g x) (x : X) :
    Function.update (fun y => Real.exp (-g y)) a 0 x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x = a
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg x hx))⟩

omit [TopologicalSpace X] [T1Space X] in

theorem exp_neg_update_eq_zero_iff (x : X) :
    Function.update (fun y => Real.exp (-g y)) a 0 x = 0 ↔ x = a := by
  classical
  by_cases hx : x = a
  · simp [hx]
  · simp [Real.exp_ne_zero, hx]

end ExponentialExtension

section Integral

variable {X : Type*} [MeasurableSpace X] [DecidableEq X]
variable (μ : Measure X) (a : X) (g : X → ℝ)

theorem lintegral_neg_log_exp_neg_update (ha : μ {a} = 0) :
    (∫⁻ x, ENNReal.ofReal (-Real.log
      (Function.update (fun y => Real.exp (-g y)) a 0 x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  classical
  apply lintegral_congr_ae
  have hne : ∀ᵐ x ∂μ, x ≠ a := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using ha
  filter_upwards [hne] with x hx
  simp [Function.update_of_ne hx, Real.log_exp]

end Integral


end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_AnalyticWeightBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

@[simp] theorem negLogCost_zero : negLogCost 0 = ∞ := by
  simp [negLogCost]

theorem negLogCost_of_pos {t : ℝ} (ht : 0 < t) :
    negLogCost t = ENNReal.ofReal (-Real.log t) := by
  simp [negLogCost, ht.ne', abs_of_pos ht]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_negLogCost_eq_of_ae_pos (f : X → ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    (∫⁻ x, negLogCost (f x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hpos] with x hx
  exact negLogCost_of_pos hx

theorem hasNegInfiniteLogIntegral_iff_of_ae_pos (f : X → ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    HasNegInfiniteLogIntegral μ f ↔
      (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞ := by
  unfold HasNegInfiniteLogIntegral
  rw [lintegral_negLogCost_eq_of_ae_pos f hpos]

theorem ae_pos_of_nonneg_singleton_zero (f : X → ℝ) (a : X)
    (ha : μ {a} = 0) (hf : ∀ x, 0 ≤ f x)
    (hz : ∀ x, f x = 0 ↔ x = a) : ∀ᵐ x ∂μ, 0 < f x := by
  have hne : ∀ᵐ x ∂μ, x ≠ a := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using ha
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (hf x) (Ne.symm (fun h => hx ((hz x).mp h)))

@[simp] theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  change volume {x} = 0
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleBackgroundBumps
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233.BackgroundCost

theorem BackgroundBumpData.radius_tendsto_zero {θ : ℝ} (d : BackgroundBumpData θ) :
    Tendsto d.radius atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (d.radius_pos n).le) (fun n => (d.radius_lt n).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Invariant233.BackgroundCost

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleBackgroundCost
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open InvariantProjection.Continuity

namespace Invariant233.BackgroundCost

local instance instFactLtRealOfNat_solutions_rf379d0_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance instIsFiniteMeasureCircleCircleMeasure_rf379d0_1 : IsFiniteMeasure circleMeasure := by
  change IsFiniteMeasure (volume : Measure (AddCircle (1 : ℝ)))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem backgroundNegative_eq_finiteAverage {θ : ℝ} (d : BackgroundBumpData θ)
    (n : ℕ) (x : Circle) :
    backgroundNegative d n x =
      (∑ i : Fin (2 ^ (n + 2)),
        d.bump n (x - ((i : ℕ) + 1) • (θ : Circle))) / (2 : ℝ) ^ (n + 2) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => d.bump n (x - (i + 1) • (θ : Circle))) (2 ^ (n + 2))]
  unfold backgroundNegative backwardAverage backwardSum
  simp only [Equiv.addRight_symm, Equiv.coe_addRight, add_right_iterate,
    smul_neg, Nat.cast_pow, Nat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

theorem backgroundNegative_bounds {θ : ℝ} (d : BackgroundBumpData θ)
    (n : ℕ) (x : Circle) :
    0 ≤ backgroundNegative d n x ∧
      backgroundNegative d n x ≤ 1 / (2 : ℝ) ^ (n + 2) := by
  let T : Fin (2 ^ (n + 2)) → Circle ≃ Circle :=
    fun i => Equiv.addRight (((i : ℕ) + 1) • (θ : Circle))
  have hd := disjoint_support_comp_symm T (d.bump n)
    (Metric.closedBall 0 (d.radius n)) (d.bump_support n) (d.disjoint_translates n)
  have h := average_bounds_of_disjoint_support Finset.univ
    (fun i x => d.bump n ((T i).symm x))
    (fun i x => (d.bump_bounds n _).1) (fun i x => (d.bump_bounds n _).2)
    hd (W := (2 : ℝ) ^ (n + 2)) (by positivity) x
  rw [backgroundNegative_eq_finiteAverage]
  simpa only [T, Equiv.addRight_symm, Equiv.coe_addRight, sub_eq_add_neg] using h

theorem continuous_backgroundNegative {θ : ℝ} (d : BackgroundBumpData θ) (n : ℕ) :
    Continuous (backgroundNegative d n) := by
  have heq : backgroundNegative d n = fun x =>
      (∑ i : Fin (2 ^ (n + 2)),
        d.bump n (x - ((i : ℕ) + 1) • (θ : Circle))) / (2 : ℝ) ^ (n + 2) :=
    funext (backgroundNegative_eq_finiteAverage d n)
  rw [heq]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact (d.continuous_bump n).comp (continuous_id.sub continuous_const)

theorem backgroundCost_ge_half {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) :
    1 / 2 ≤ backgroundCost d x := by
  apply background_cost_ge_half (d.bump) (backgroundNegative d)
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) hasSum_background_majorant.summable
    hasSum_background_majorant.tsum_eq.le
    (fun n x => (d.bump_bounds n x).1)
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

theorem continuousOn_backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) :
    ContinuousOn (backgroundCost d) ({0}ᶜ : Set Circle) := by
  exact background_cost_continuousOn 0 d.bump (backgroundNegative d) d.radius
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) d.continuous_bump
    (continuous_backgroundNegative d) (BackgroundBumpData.radius_tendsto_zero d)
    (fun n x hx => d.bump_support n hx) hasSum_background_majorant.summable
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

theorem tendsto_backgroundCost_atTop {θ : ℝ} (d : BackgroundBumpData θ) :
    Tendsto (backgroundCost d) (𝓝[≠] (0 : Circle)) atTop := by
  exact tendsto_background_atTop 0 d.bump (backgroundNegative d)
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) d.continuous_bump d.bump_zero
    (fun n x => (d.bump_bounds n x).1)
    (fun x hx => summable_of_support_shrinks 0 d.bump d.radius
      (BackgroundBumpData.radius_tendsto_zero d) (fun n y hy => d.bump_support n hy) hx)
    hasSum_background_majorant.summable
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

end Invariant233.BackgroundCost

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCurrentBlockEvent
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

def rawCurrentBlockEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  {ω | (∃ i ∈ p.block j, label i ω = some (4 : Fin 5)) ∧
    ∀ i ∈ p.block j, (ω i).2.1 < 1 - 3 / (p.m j : ℝ) ∧
      3 / (p.m j : ℝ) < (ω i).2.2}

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleFutureEndpointLoss
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

def futureBadEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  ⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
    {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ (ω i).2.1 ∨
      (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)}

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleKernelConvolution
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.CircleKernelConvolution

def convolution (k : C(UnitAddCircle, ℝ)) (f : UnitAddCircle → ℝ)
    (x : UnitAddCircle) : ℝ := ∫ y, k (x - y) * f y

def testCoefficient (f : UnitAddCircle → ℝ) (v : ℤ) : ℂ :=
  ∫ y, fourier (-v) y * (f y : ℂ)

@[simp] theorem testCoefficient_zero (f : UnitAddCircle → ℝ) :
    testCoefficient f 0 = (∫ y, f y : ℝ) := by
  simp [testCoefficient, integral_complex_ofReal]

def translationError (f : UnitAddCircle → ℝ) (t : UnitAddCircle) : ℝ :=
  ∫ x, |f (x - t) - f x|

end Invariant233.CircleKernelConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleRationalSamplingIndex
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

theorem exists_nat_rational_representative (d : ℕ) (hd : 0 < d) (z : ℤ) :
    ∃ r : ℕ, r < d ∧
      (((z : ℝ) / (d : ℝ) : ℝ) : Circle) =
        (((r : ℝ) / (d : ℝ) : ℝ) : Circle) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hn : 0 ≤ z % (d : ℤ) := Int.emod_nonneg z hdZ.ne'
  refine ⟨(z % (d : ℤ)).toNat, (Int.toNat_lt hn).mpr (Int.emod_lt_of_pos z hdZ), ?_⟩
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z / (d : ℤ), ?_⟩
  have hcast : (((z % (d : ℤ)).toNat : ℕ) : ℝ) = (z % (d : ℤ) : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hdiv := congrArg (fun n : ℤ => (n : ℝ))
    (Int.emod_add_mul_ediv z (d : ℤ))
  push_cast at hdiv
  rw [hcast, zsmul_eq_mul, mul_one]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  nlinarith

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rational_shift_later_denominator {A a : ℕ} (hAa : A ≤ a) (r : ℤ) :
    ∃ s : ℕ, s < p.q a ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) =
        (((s : ℝ) / (p.q a : ℝ) : ℝ) : Circle) := by
  obtain ⟨d, hd⟩ := hp.trimming_frequency_dvd_of_le hAa
  have hqa : (p.q A : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos A).ne'
  have hqb : (p.q a : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos a).ne'
  have he : ((r * (d : ℤ) : ℤ) : ℝ) / (p.q a : ℝ) =
      (r : ℝ) / (p.q A : ℝ) := by
    have hdR : (p.q a : ℝ) = (p.q A : ℝ) * d := by exact_mod_cast hd
    push_cast
    field_simp
    rw [hdR]
    ring
  obtain ⟨s, hs, heq⟩ := exists_nat_rational_representative (p.q a) (hp.q_pos a)
    (r * (d : ℤ))
  refine ⟨s, hs, ?_⟩
  rwa [he] at heq

theorem exists_rational_sampling_index {A j : ℕ}
    (hAj : A ≤ p.blockEnd (j - 1)) (r : ℤ) :
    ∃ s : ℕ, s < p.q (p.blockEnd (j - 1)) ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) = (p.shift j s : Circle) := by
  exact hp.rational_shift_later_denominator hAj r

theorem exists_rational_sampling_index_of_late {A j : ℕ}
    (hAj : A + 1 ≤ j) (r : ℤ) :
    ∃ s : ℕ, s < p.q (p.blockEnd (j - 1)) ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) = (p.shift j s : Circle) := by
  apply hp.exists_rational_sampling_index
  exact (show A ≤ j - 1 by omega).trans (p.blockEnd_ge_index hp.m_pos (j - 1))

end CircleParameterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedGraphMarginals
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.WeightedGraphMarginals

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_fst_graph (μ : Measure X) {T : X → Y} (hT : Measurable T) :
    (μ.map (fun x => (x, T x))).map Prod.fst = μ := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map measurable_fst hg]
  change μ.map id = μ
  exact Measure.map_id

theorem withDensity_finset_sum {ι : Type*} (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Measurable (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert ha]
      rw [show (fun x => f a x + ∑ i ∈ s, f i x) =
        f a + (fun x => ∑ i ∈ s, f i x) from rfl,
        withDensity_add_left hfa, ih hfs]

theorem map_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure X)
    {T : X → Y} (hT : Measurable T) :
    (∑ i ∈ s, μ i).map T = ∑ i ∈ s, (μ i).map T := by
  simp only [← Measure.mapₗ_apply_of_measurable hT, map_sum]

theorem withDensity_real_finset_sum {ι : Type*} (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, Measurable (f i))
    (hfnonneg : ∀ i ∈ s, ∀ x, 0 ≤ f i x) {c : ℝ} (hc : 0 ≤ c) :
    μ.withDensity (fun x => ENNReal.ofReal (c * ∑ i ∈ s, f i x)) =
      ENNReal.ofReal c • ∑ i ∈ s, μ.withDensity (fun x => ENNReal.ofReal (f i x)) := by
  have he : (fun x => ENNReal.ofReal (c * ∑ i ∈ s, f i x)) =
      ENNReal.ofReal c • (fun x => ∑ i ∈ s, ENNReal.ofReal (f i x)) := by
    funext x
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg
      (fun i hi => hfnonneg i hi x)]
    rfl
  rw [he, withDensity_smul]
  · rw [withDensity_finset_sum μ s _ (fun i hi => (hf i hi).ennreal_ofReal)]
  · exact Finset.measurable_sum s (fun i hi => (hf i hi).ennreal_ofReal)

end Invariant233.WeightedGraphMarginals

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingGraph
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem measurable_samplingDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) : Measurable (p.samplingDensity θ j n endpoint) := by
  unfold samplingDensity
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_orientedKernel endpoint (p.m j)
    (Int.fract ((n : ℝ) * p.alpha θ i))).comp (p.measurable_coordinate i)

theorem samplingDensity_nonneg (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (x : Circle) :
    0 ≤ p.samplingDensity θ j n endpoint x := by
  exact Finset.prod_nonneg fun i _ => (orientedKernel_bounds endpoint hm _ _).1

theorem samplingTranslation_measurable (θ : ℝ) (n : ℕ) :
    Measurable (samplingTranslation θ n) :=
  (continuous_id.add continuous_const).measurable

theorem samplingGraph_first_marginal (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    (p.samplingGraph θ j n).map Prod.fst =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingDensity θ j n false x)) := by
  exact WeightedGraphMarginals.map_fst_graph _ (samplingTranslation_measurable θ n)

theorem samplingGraphAverage_first_marginal (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) :
    (p.samplingGraphAverage θ j r).map Prod.fst =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ j r false x)) := by
  rw [samplingGraphAverage, Measure.map_smul,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_fst]
  simp_rw [p.samplingGraph_first_marginal]
  exact (WeightedGraphMarginals.withDensity_real_finset_sum circleMeasure
    (p.samples j r) (fun n => p.samplingDensity θ j n false)
    (fun n _ => p.measurable_samplingDensity θ j n false)
    (fun n _ x => p.samplingDensity_nonneg θ j n false hm x)
    (by positivity : 0 ≤ 1 / ((p.samples j r).card : ℝ))).symm

theorem samplingGraphAverage_finite (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) : IsFiniteMeasure (p.samplingGraphAverage θ j r) := by
  let : IsFiniteMeasure circleMeasure := by unfold circleMeasure; infer_instance
  have hi : Integrable (p.samplingAverage θ j r false) circleMeasure :=
    (p.memLp_samplingAverage θ j r false hm 1).integrable le_rfl
  have hn : 0 ≤ᵐ[circleMeasure] p.samplingAverage θ j r false :=
    Filter.Eventually.of_forall fun x => (p.samplingAverage_bounds θ j r false hm x).1
  have ht := (lintegral_ofReal_ne_top_iff_integrable
    hi.aestronglyMeasurable hn).2 hi
  have : IsFiniteMeasure ((p.samplingGraphAverage θ j r).map Prod.fst) := by
    rw [p.samplingGraphAverage_first_marginal θ j r hm]
    exact isFiniteMeasure_withDensity ht
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingGraphLimits
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Invariant233.CircleParameterData

def circleFiniteBase : FiniteMeasure Circle :=
  ⟨circleMeasure, by unfold circleMeasure; infer_instance⟩

instance circleFiniteBase_probability : IsProbabilityMeasure (circleFiniteBase : Measure Circle) := by
  constructor
  change volume (Set.univ : Set Circle) = 1
  exact UnitAddCircle.measure_univ

def samplingGraphFinite (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (hm : 0 < p.m j) : FiniteMeasure (Circle × Circle) :=
  ⟨p.samplingGraphAverage θ j r, p.samplingGraphAverage_finite θ j r hm⟩

end Invariant233.CircleParameterData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRationalGraphApproximants
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

def rationalSamplingStage (A n : ℕ) : ℕ := n + A + 1

def rationalSamplingLabel (A : ℕ) (r : ℤ) (n : ℕ) : ℕ :=
  Classical.choose (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)

theorem rationalSamplingStage_pos (A n : ℕ) : 1 ≤ rationalSamplingStage A n := by
  unfold rationalSamplingStage
  omega

def rationalGraphApproximant (A : ℕ) (r : ℤ) (n : ℕ) : FiniteMeasure (Circle × Circle) :=
  (p.samplingGraphFinite θ (rationalSamplingStage A n) (hp.rationalSamplingLabel A r n)
    (hp.m_pos _ (rationalSamplingStage_pos A n))).restrict
      (Prod.fst ⁻¹' p.rationalGraphGood A (rationalSamplingStage A n))

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleQuantizedMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
@[simp] lemma hybridPoint_const (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    hybridPoint p hr (fun _ => side) = point p hr side := rfl

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleOrderedTransfer
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

def sampleFiniteLaw (j : ℕ) : FiniteMeasure Sample := by
  letI := law_isProbabilityMeasure hp j
  exact ⟨law p j, inferInstance⟩

def hybridPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) : FiniteMeasure (Circle × Circle) :=
  (sampleFiniteLaw hp j).map (fun ω => (point p hr false ω, finiteHybridPoint p hr N ω))

def endpointPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    FiniteMeasure (Circle × Circle) :=
  (sampleFiniteLaw hp j).map (fun ω => (point p hr false ω, point p hr true ω))

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTruncationMass
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Invariant233.CircleCoupling

def centralBadEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) : Set Sample :=
  {ω | r (point p hr false ω) < 1 / (j : ℝ)} ∪
    {ω | 1 - r (point p hr true ω) < 1 / (j : ℝ)}

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousWeightAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Function Set
open scoped ENNReal Topology

namespace Invariant233.CircleParameterLaws

open InvariantProjection.Continuity

variable {θ : ℝ} {p : CircleParameterData}

variable (hp : CircleParameterLaws θ p)
include hp

theorem continuousOn_continuousCost (d : BackgroundBumpData θ) :
    ContinuousOn (p.continuousCost θ d) ({0}ᶜ : Set Circle) :=
  (BackgroundCost.continuousOn_backgroundCost d).add hp.continuousOn_relocatedCost

theorem continuousCost_ge_half (d : BackgroundBumpData θ) (x : Circle) :
    1 / 2 ≤ p.continuousCost θ d x :=
  (BackgroundCost.backgroundCost_ge_half d x).trans
    (le_add_of_nonneg_right (hp.relocatedCost_nonneg x))

theorem tendsto_continuousCost_atTop (d : BackgroundBumpData θ) :
    Tendsto (p.continuousCost θ d) (𝓝[≠] (0 : Circle)) atTop := by
  apply tendsto_atTop_mono (fun x => le_add_of_nonneg_right (hp.relocatedCost_nonneg x))
  exact BackgroundCost.tendsto_backgroundCost_atTop d

theorem lintegral_continuousCost_eq_top (d : BackgroundBumpData θ) :
    (∫⁻ x, ENNReal.ofReal (p.continuousCost θ d x) ∂circleMeasure) = ∞ := by
  apply lintegral_cost_add_background_eq_top (p.relocatedCost θ) (backgroundCost d)
    hp.lintegral_relocatedCost_eq_top
  exact Eventually.of_forall (fun x => (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans
    (BackgroundCost.backgroundCost_ge_half d x))

theorem isContinuousCircleWeight_continuousWeight (d : BackgroundBumpData θ) :
    IsContinuousCircleWeight (p.continuousWeight θ d) := by
  classical
  have hnonneg (x : Circle) (hx : x ≠ 0) : 0 ≤ p.continuousCost θ d x :=
    (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (hp.continuousCost_ge_half d x)
  have hcont : Continuous (p.continuousWeight θ d) :=
    continuous_exp_neg_update 0 (p.continuousCost θ d)
      (hp.continuousOn_continuousCost d) (hp.tendsto_continuousCost_atTop d)
  have hrange : ∀ x, 0 ≤ p.continuousWeight θ d x ∧ p.continuousWeight θ d x ≤ 1 :=
    exp_neg_update_mem_Icc 0 (p.continuousCost θ d) hnonneg
  have hzero : ∀ x, p.continuousWeight θ d x = 0 ↔ x = 0 :=
    exp_neg_update_eq_zero_iff 0 (p.continuousCost θ d)
  refine ⟨hcont, hrange, hzero, ?_⟩
  have hpos := ae_pos_of_nonneg_singleton_zero (p.continuousWeight θ d) 0
    (circleMeasure_singleton 0) (fun x => (hrange x).1) hzero
  apply (hasNegInfiniteLogIntegral_iff_of_ae_pos _ hpos).mpr
  exact (lintegral_neg_log_exp_neg_update circleMeasure 0 (p.continuousCost θ d)
    (circleMeasure_singleton 0)).trans (hp.lintegral_continuousCost_eq_top d)

end Invariant233.CircleParameterLaws

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousWeightOperatorBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurable_complexParameterWeight :
    Measurable (fun x => (p.measurableWeight θ x : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp hp.measurable_parameter_weight

theorem norm_complexParameterWeight_le_one (x : Circle) :
    ‖(p.measurableWeight θ x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hp.parameter_weight_mem_Ioc x).1] using (hp.parameter_weight_mem_Ioc x).2

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterWeakConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233
namespace CharacterWeakConvergence

open MeasureTheory Filter Set
open scoped Topology NNReal

section Integral
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def pullbackIntegral (φ : C(X, Y)) : C(Y, ℂ) →L[ℂ] ℂ :=
  let L : C(Y, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f (φ x) ∂μ
      map_add' := by
        intro f g
        exact integral_add
          (f.continuous.comp φ.continuous |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          (g.continuous.comp φ.continuous |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, integral_smul, RingHom.id_apply] }
  L.mkContinuous 1 (fun f => by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (φ x)))
    change ‖∫ x, f (φ x) ∂μ‖ ≤ 1 * ‖f‖
    simpa using h)

@[simp] theorem pullbackIntegral_apply (φ : C(X, Y)) (f : C(Y, ℂ)) :
    pullbackIntegral μ φ f = ∫ x, f (φ x) ∂μ := rfl

end Integral

end CharacterWeakConvergence
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_CFCLogSeries
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped CStarAlgebra
namespace Invariant233
namespace CFCLogSeries

section Normed
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def term (a : A) (n : ℕ) : A := ((n + 1 : ℝ)⁻¹) • a ^ (n + 1)

end Normed

end CFCLogSeries
end Invariant233

end

end OAI
end



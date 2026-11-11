-- Prove2me | Definitions.Def_Q234IR001
-- name    : Q234IR001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:22:04.622133+00:00
-- url     : https://prove2.me/theorems/1fcdfff4-3d4e-44c6-9032-f9e19f7b01d0
-- title:
--   Definitions bundle Q234IR001 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 454 declarations of OpenAI's Lean: 192 definitions, 5 inductive types or structures, 10 instances and 247 theorems. The definitions and types are `OAI.Invariant233.DirectIntegral.fieldOperator`, `OAI.Invariant233.DirectIntegral.fieldOperatorLinear`, `OAI.Invariant233.DirectIntegral.fieldOperatorVec`, `OAI.Invariant233.DirectIntegral.shiftedPullback`, `OAI.Invariant233.FieldKoopman.equivalence`, `OAI.Invariant233.Fields.columnOperator`, `OAI.Invariant233.Fields.indicatorConstLpCLM`, `OAI.Invariant233.Fields.rationalComplex`, `OAI.Invariant233.FiniteSupportWeights.integerCore`, `OAI.Invariant233.FiniteWindow.convolution`, `OAI.Invariant233.FiniteWindow.laurent`, `OAI.Invariant233.FourierSampling.polynomial`, `OAI.Invariant233.HilbertModelSize.constL2Isometry`, `OAI.Invariant233.KernelProduct.independent`, `OAI.Invariant233.KernelProduct.pairCoordinates`, `OAI.Invariant233.L2Multiplication.multiplier`, `OAI.Invariant233.OrderedProductCoupling.PrefixIndex`, `OAI.Invariant233.OrderedProductCoupling.PrefixPairs`, `OAI.Invariant233.OrderedProductCoupling.TailIndex`, `OAI.Invariant233.OrderedProductCoupling.TailValues`, `OAI.Invariant233.OrderedProductCoupling.blockDensityBound`, `OAI.Invariant233.OrderedProductCoupling.collapsePrefixPattern`, `OAI.Invariant233.OrderedProductCoupling.prefixPatternEvent`, `OAI.Invariant233.OrderedProductCoupling.selectedPrefixPattern`, `OAI.Invariant233.OrderedProductCoupling.sourceKappa`, `OAI.Invariant233.PositiveDiagonalModel.Fiber`, `OAI.Invariant233.PositiveDiagonalModel.Space`, `OAI.Invariant233.PositiveDiagonalModel.diagonalState`, `OAI.Invariant233.PositiveDiagonalModel.e0`, `OAI.Invariant233.PositiveDiagonalModel.fiberShift`, `OAI.Invariant233.PositiveDiagonalModel.fiberShiftUnit`, `OAI.Invariant233.PositiveDiagonalModel.realDiagonal`, `OAI.Invariant233.PositiveDiagonalModel.realWeight`, `OAI.Invariant233.PositiveDiagonalModel.realWeightedShift`, `OAI.Invariant233.PrescribedPhaseRealization.spliceFrequency`, `OAI.Invariant233.ProductDensity.partialDensityLp`, `OAI.Invariant233.ProductModel.GlobalPolarSupport.productPolarModulusComplexRealModule`, `OAI.Invariant233.ProductModel.IdealSampling.coordinateKernel`, `OAI.Invariant233.ProductModel.IdealSampling.cutoffEvent`, `OAI.Invariant233.ProductModel.IdealSampling.endpoint` and 157 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `IrrationalRotation_Analysis_ClosedRangeTransport`, `IrrationalRotation_Analysis_ExtendedExponential`, `IrrationalRotation_Analysis_FieldCovariance`, `IrrationalRotation_Analysis_FieldKoopman`, `IrrationalRotation_Analysis_FieldKoopmanGenerated`, `IrrationalRotation_Analysis_FieldMultiplierCutoff`, `IrrationalRotation_Analysis_FieldPositivity`, `IrrationalRotation_Analysis_FieldUnboundedMultiplier`, `IrrationalRotation_Analysis_FieldVectorState`, `IrrationalRotation_Analysis_FieldsNorm`, `IrrationalRotation_Analysis_FiniteConvolution`, `IrrationalRotation_Analysis_FrequencySplice`, `IrrationalRotation_Analysis_FrequencyTower`, `IrrationalRotation_Analysis_GeneratedVonNeumann`, `IrrationalRotation_Analysis_LaurentNoncancellation`, `IrrationalRotation_Analysis_LaurentWindow`, `IrrationalRotation_Analysis_OmittedEvents`, `IrrationalRotation_Analysis_ScalarMultiplier`, `IrrationalRotation_Analysis_ScalarMultiplierFields`, `IrrationalRotation_Analysis_ScalarRectangleDiscrepancy`, `IrrationalRotation_Analysis_StrongFieldContinuity`, `IrrationalRotation_Analysis_StrongFieldMeasurability`, `IrrationalRotation_Analysis_TaggedEventBounds`, `IrrationalRotation_Analysis_TailScaleCover`, `IrrationalRotation_Analysis_TestedTriangularMoments`, `IrrationalRotation_Couplings_BlockProductCoupling`, `IrrationalRotation_Couplings_ConditionalConvolution`, `IrrationalRotation_Couplings_ProductConditionalData`, `IrrationalRotation_Couplings_ProductDensity`, `IrrationalRotation_Couplings_ProductDensityLimit`, `IrrationalRotation_Model_AffiliatedTransport`, `IrrationalRotation_Model_BlockProductCoupling`, `IrrationalRotation_Model_CircleRationalGraphs`, `IrrationalRotation_Model_ColumnOperator`, `IrrationalRotation_Model_CompactTransfer`, `IrrationalRotation_Model_ConditionalConvolution`, `IrrationalRotation_Model_FieldOperator`, `IrrationalRotation_Model_FieldUnboundedMultiplier`, `IrrationalRotation_Model_FieldWeightedShift`, `IrrationalRotation_Model_FiniteConvolution`, `IrrationalRotation_Model_IndependentKernelProduct`, `IrrationalRotation_Model_JointEigenspace`, `IrrationalRotation_Model_LaurentConvolution`, `IrrationalRotation_Model_OrbitMeasurable`, `IrrationalRotation_Model_PhaseBlocks`, `IrrationalRotation_Model_PhaseFailure`, `IrrationalRotation_Model_PositiveDiagonalModel`, `IrrationalRotation_Model_PrefixHybrid`, `IrrationalRotation_Model_ProductCharacters`, `IrrationalRotation_Model_ProductIdealSampling`, `IrrationalRotation_Model_ProductPrefixDomination`, `IrrationalRotation_Model_ProductTailTrimming`, `IrrationalRotation_Model_RotationTransfer`, `IrrationalRotation_Model_ScalarEndpointDensity`, `IrrationalRotation_Model_ScalarKernelEstimates`, `IrrationalRotation_Model_ScalarMultiplier`, `IrrationalRotation_Model_ScalarSampling`, `IrrationalRotation_Model_ScalarSamplingEstimates`, `IrrationalRotation_Model_ShiftedPullback`, `IrrationalRotation_Model_SpectralCutoff`, `IrrationalRotation_Model_TrialSampling`, `IrrationalRotation_Model_UniformIntervalPhase`, `IrrationalRotation_Model_VectorTraceState`, `IrrationalRotation_Operators_AffiliatedTransport`, `IrrationalRotation_Operators_ColumnOperator`, `IrrationalRotation_Operators_CovariantTracialVector`, `IrrationalRotation_Operators_FieldTraceCyclic`, `IrrationalRotation_Operators_FieldTraceFaithfulness`, `IrrationalRotation_Operators_FiniteConvolutionAlgebra`, `IrrationalRotation_Operators_HilbertModelSize`, `IrrationalRotation_Operators_JointEigenprojection`, `IrrationalRotation_Operators_LpOperatorExt`, `IrrationalRotation_Operators_ProjectionMeetTrace`, `IrrationalRotation_Operators_ScalarMultiplierCommutation`, `IrrationalRotation_Operators_StrongOperatorConvergence`, `IrrationalRotation_Operators_StrongOperatorIntegral`, `IrrationalRotation_Operators_TracialProjectionTransport`, `IrrationalRotation_Operators_VectorTraceState`, `IrrationalRotation_Product_IndependentKernelProduct`, `IrrationalRotation_Product_ProductOrbitTests`, `IrrationalRotation_Product_ProductScaleConstruction`, `IrrationalRotation_Product_ProductTestedExpectationSummability`, `IrrationalRotation_Product_ProductTestedKernelMoments`, `IrrationalRotation_Product_ProductWeightBridge`, `IrrationalRotation_Rotation_CircleFiberDecay`, `IrrationalRotation_Rotation_CircleWeightDecay`, `IrrationalRotation_Rotation_FieldDiagonalConvergence`, `IrrationalRotation_Rotation_FiniteSupportWeights`, `IrrationalRotation_Rotation_ProjectionCocycleWindow`, `IrrationalRotation_Rotation_RealWeightedPositiveDiagonal`, `IrrationalRotation_Rotation_RotationDecay`, `IrrationalRotation_Rotation_UniformRotationAverage`, `IrrationalRotation_Sampling_BlockPhaseConstruction`, `IrrationalRotation_Sampling_FourierSampling`, `IrrationalRotation_Sampling_PrefixReferenceCompletion`, `IrrationalRotation_Sampling_ProductCharacters`, `IrrationalRotation_Sampling_ProductIdealSamplingProduct`, `IrrationalRotation_Sampling_ProductSampling`, `IrrationalRotation_Sampling_ProductSamplingCylinderWeights`, `IrrationalRotation_Sampling_ProductSamplingIdealBounds`, `IrrationalRotation_Sampling_ProductSamplingPhaseMoments`, `IrrationalRotation_Sampling_ProductSamplingTestIntegrability`, `IrrationalRotation_Sampling_ProductSamplingTrimming`, `IrrationalRotation_Sampling_ProductSamplingWeightAssembly`, `IrrationalRotation_Sampling_ProductSamplingWeightTests`, `IrrationalRotation_Sampling_ProductSamplingWeights`, `IrrationalRotation_Sampling_SamplingAsymptotics`, `IrrationalRotation_Sampling_SamplingCylinderWeak`, `IrrationalRotation_Sampling_SamplingHorizon`, `IrrationalRotation_Sampling_SamplingOrbitWeak`, `IrrationalRotation_Sampling_ScalarSamplingEndpointVariation`, `IrrationalRotation_Sampling_ScalarSamplingPairMoments`, `IrrationalRotation_Sampling_TestedSamplingMoments`, `IrrationalRotation_Sampling_TrialSamplingSelection`, `IrrationalRotation_Sampling_UniformIntervalPhase`, `IrrationalRotation_Spectral_DeterminantHomogeneity`, `IrrationalRotation_Spectral_FieldResolvent`, `IrrationalRotation_Spectral_ProductDeterminant`, `IrrationalRotation_Spectral_ProductPolarModulusComplex`, `IrrationalRotation_Spectral_ProductQuasinilpotent`, `IrrationalRotation_Spectral_ProductWeightPolar`, `IrrationalRotation_Spectral_QuasinilpotentSeries`.
--
--   **Imports.** It imports the published bundle `Def_IrrationalRotation`.
--
--   **Imported by** (directly, in this split): the bundle `Q234IR003`; the statements `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass` and `OAI.Invariant233.Rotation.exponentialTransfer_projection_transport`; the proof of `OAI.Invariant233.CircleParameterLaws.rational_graphs_of_representation`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ClosedRangeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace InvariantRotation.ClosedRangeTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (p : Submodule 𝕜 E) [CompleteSpace p]
variable (f : p →L[𝕜] E) (hinj : Function.Injective f)
variable (hclosed : IsClosed (Set.range f))

omit [CompleteSpace p] in

theorem range_hasOrthogonalProjection (hclosed : IsClosed (Set.range f)) :
    f.range.HasOrthogonalProjection := by
  let : IsClosed (f.range : Set E) := hclosed
  infer_instance

def partialInverse : E →L[𝕜] E := by
  letI := range_hasOrthogonalProjection p f hclosed
  exact p.subtypeL.comp
    ((f.equivRange hinj hclosed).symm.toContinuousLinearMap.comp
      f.range.orthogonalProjectionOnto)

def forward : E →L[𝕜] E :=
  f.comp p.orthogonalProjectionOnto

@[simp]
theorem partialInverse_apply_image (x : p) :
    partialInverse p f hinj hclosed (f x) = (x : E) := by
  let := range_hasOrthogonalProjection p f hclosed
  change (((f.equivRange hinj hclosed).symm
    (f.range.orthogonalProjectionOnto (f x)) : p) : E) = x
  have hproj : f.range.orthogonalProjectionOnto (f x) = ⟨f x, f.mem_range_self x⟩ :=
    f.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f x, f.mem_range_self x⟩
  rw [hproj, f.equivRange_symm_apply hinj hclosed x]

end InvariantRotation.ClosedRangeTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExtendedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal

namespace Invariant233

theorem extendedExpNeg_eq_exp_toReal (a : ℝ≥0∞) (ha : a ≠ ∞) :
    (EReal.exp (-(a : EReal))).toReal = Real.exp (-a.toReal) := by
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_neg, EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem extendedExpNeg_mem_Icc (a : ℝ≥0∞) :
    (EReal.exp (-(a : EReal))).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ha : a = ∞
  · simp [ha]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    exact ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)⟩

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldTraceCyclic
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.FieldTraceCyclic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hasSum_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    HasSum (fun r : ℤ => inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k)))
      (inner ℂ (b k) (A (B (b k)))) := by
  simpa only [ContinuousLinearMap.adjoint_inner_left] using
    b.hasSum_inner_mul_inner ((ContinuousLinearMap.adjoint A) (b k)) (B (b k))

theorem summable_norm_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    Summable (fun r : ℤ =>
      ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) :=
  summable_norm_iff.mpr (hasSum_matrix_product b A B k).summable

theorem tsum_norm_matrix_product_le (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    (∑' r : ℤ, ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) ≤
      ‖A‖ * ‖B‖ := by
  have hc := lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two)
    (b.repr ((ContinuousLinearMap.adjoint A) (b k))) (b.repr (B (b k)))
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at hc
  calc
    (∑' r : ℤ, ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) =
        ∑' r : ℤ, ‖inner ℂ (b r) ((ContinuousLinearMap.adjoint A) (b k))‖ *
          ‖inner ℂ (b r) (B (b k))‖ := by
      apply tsum_congr
      intro r
      rw [norm_mul, ← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ ≤ ‖(ContinuousLinearMap.adjoint A) (b k)‖ * ‖B (b k)‖ := hc
    _ ≤ (‖ContinuousLinearMap.adjoint A‖ * ‖b k‖) * (‖B‖ * ‖b k‖) :=
      mul_le_mul ((ContinuousLinearMap.adjoint A).le_opNorm (b k))
        (B.le_opNorm (b k)) (norm_nonneg _) (by positivity)
    _ = ‖A‖ * ‖B‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map, b.orthonormal.norm_eq_one]
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem hasSum_integral_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : Ω → E →L[ℂ] E)
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (k : ℤ) :
    HasSum (fun r : ℤ => ∫ x,
      inner ℂ (b k) (A x (b r)) * inner ℂ (b r) (B x (b k)) ∂μ)
      (∫ x, inner ℂ (b k) (A x (B x (b k))) ∂μ) := by
  let F : ℤ → Ω → ℂ := fun r x =>
    inner ℂ (b k) (A x (b r)) * inner ℂ (b r) (B x (b k))
  have hFm : ∀ r, AEStronglyMeasurable (F r) μ := by
    intro r
    exact (aestronglyMeasurable_const.inner (hA r)).mul
      (aestronglyMeasurable_const.inner (hB k))
  have hsumInt : Integrable (fun x => ∑' r, ‖F r x‖) μ := by
    apply (integrable_const (CA * CB)).mono' (AEStronglyMeasurable.tsum (fun r => (hFm r).norm))
    filter_upwards [hAbound, hBbound] with x hxA hxB
    rw [Real.norm_of_nonneg (tsum_nonneg (fun r => norm_nonneg (F r x)))]
    exact (tsum_norm_matrix_product_le b (A x) (B x) k).trans
      (mul_le_mul hxA hxB (norm_nonneg _) hCA)
  exact hasSum_integral_of_dominated_convergence
    (fun r x => ‖F r x‖) hFm (fun _ => ae_of_all _ (fun _ => le_rfl))
    (ae_of_all _ (fun x => summable_norm_matrix_product b (A x) (B x) k))
    hsumInt (ae_of_all _ (fun x => hasSum_matrix_product b (A x) (B x) k))

theorem integral_central_matrix_product_cyclic (b : HilbertBasis ℤ ℂ E)
    (A B : Ω → E →L[ℂ] E)
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcovA : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) = inner ℂ (b (k + r)) (A x (b (l + r))))
    (hcovB : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (B (σ r x) (b l)) = inner ℂ (b (k + r)) (B x (b (l + r)))) :
    (∫ x, inner ℂ (b 0) (A x (B x (b 0))) ∂μ) =
      ∫ x, inner ℂ (b 0) (B x (A x (b 0))) ∂μ := by
  have hterm (r : ℤ) :
      (∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
        ∫ x, inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0)) ∂μ := by
    let f : Ω → ℂ := fun x =>
      inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0))
    have hfm : AEStronglyMeasurable f μ :=
      (aestronglyMeasurable_const.inner (hB (-r))).mul
        (aestronglyMeasurable_const.inner (hA 0))
    have hm : AEStronglyMeasurable f (μ.map (σ r)) := by
      rw [(hσ r).map_eq]
      exact hfm
    calc
      (∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
          ∫ x, f (σ r x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcovA r (-r) 0, hcovB r 0 (-r)] with x hxA hxB
        simp only [neg_add_cancel, zero_add] at hxA hxB
        dsimp [f]
        rw [hxA, hxB]
        exact mul_comm _ _
      _ = ∫ x, f x ∂μ := by
        simpa only [(hσ r).map_eq] using
          (integral_map (hσ r).measurable.aemeasurable hm).symm
  rw [← (hasSum_integral_matrix_product b A B hA hB CA CB hCA hAbound hBbound 0).tsum_eq,
    ← (hasSum_integral_matrix_product b B A hB hA CB CA hCB hBbound hAbound 0).tsum_eq]
  calc
    (∑' r : ℤ, ∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
        ∑' r : ℤ, ∫ x, inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0)) ∂μ :=
      tsum_congr hterm
    _ = ∑' r : ℤ, ∫ x, inner ℂ (b 0) (B x (b r)) * inner ℂ (b r) (A x (b 0)) ∂μ :=
      by
        simpa only [Equiv.neg_apply] using
          (Equiv.neg ℤ).tsum_eq (fun r : ℤ =>
            ∫ x, inner ℂ (b 0) (B x (b r)) * inner ℂ (b r) (A x (b 0)) ∂μ)

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldVectorState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem constant_vector_state_eq_integral
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) (v : E) :
    inner ℂ (Lp.const 2 μ v) (T (Lp.const 2 μ v)) =
      ∫ x, inner ℂ v (A x v) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ v, hT (Lp.const 2 μ v)] with x hx hTx
  rw [hTx, hx]
  rfl

theorem constant_vector_state_mul_eq_integral
    (T S : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hS : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (S ξ) x = B x (ξ x)) (v : E) :
    inner ℂ (Lp.const 2 μ v) ((T * S) (Lp.const 2 μ v)) =
      ∫ x, inner ℂ v (A x (B x v)) ∂μ := by
  change inner ℂ (Lp.const 2 μ v) (T (S (Lp.const 2 μ v))) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ v, hT (S (Lp.const 2 μ v)),
    hS (Lp.const 2 μ v)] with x hx hTx hSx
  rw [hTx, hSx, hx]
  rfl

theorem constant_vector_state_cyclic_of_covariance [CompleteSpace E]
    (b : HilbertBasis ℤ ℂ E) (T S : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A B : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hS : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (S ξ) x = B x (ξ x))
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcovA : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) = inner ℂ (b (k + r)) (A x (b (l + r))))
    (hcovB : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (B (σ r x) (b l)) = inner ℂ (b (k + r)) (B x (b (l + r)))) :
    inner ℂ (Lp.const 2 μ (b 0)) ((T * S) (Lp.const 2 μ (b 0))) =
      inner ℂ (Lp.const 2 μ (b 0)) ((S * T) (Lp.const 2 μ (b 0))) := by
  rw [constant_vector_state_mul_eq_integral T S A B hT hS,
    constant_vector_state_mul_eq_integral S T B A hS hT]
  exact integral_central_matrix_product_cyclic b A B hA hB CA CB hCA hCB
    hAbound hBbound σ hσ hcovA hcovB

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ShiftedPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.DirectIntegral

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure Ω}

def shiftedPullback (S : E →L[ℂ] E) (σ : Ω → Ω)
    (hσ : MeasurePreserving σ μ μ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (S.compLpL 2 μ).comp (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_HilbertModelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.HilbertModelSize

open TopologicalSpace MeasureTheory
open scoped lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem separable_of_countable_hilbertBasis {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ E) : SeparableSpace E := by
  have hs : IsSeparable (Submodule.span ℂ (Set.range b) : Set E) :=
    (Set.countable_range b).isSeparable.span
  have hc := hs.closure
  have heq : closure (Submodule.span ℂ (Set.range b) : Set E) = Set.univ := by
    change ((Submodule.span ℂ (Set.range b)).topologicalClosure : Set E) = Set.univ
    rw [b.dense_span]
    rfl
  rw [heq] at hc
  exact isSeparable_univ_iff.mp hc

section BochnerLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def constL2Isometry : E →ₗᵢ[ℂ] Lp E 2 μ where
  toLinearMap := Lp.constₗ 2 μ ℂ
  norm_map' x := by
    change ‖Lp.const 2 μ x‖ = ‖x‖
    rw [Lp.norm_const' 2 μ x (by norm_num) (by norm_num)]
    simp

end BochnerLp

end Invariant233.HilbertModelSize

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem shiftedPullback_ae (S : E →L[ℂ] E) (σ : Ω → Ω)
    (hσ : MeasurePreserving σ μ μ) (ξ : Lp E 2 μ) :
    ∀ᵐ x ∂μ, (DirectIntegral.shiftedPullback S σ hσ ξ) x = S (ξ (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ ξ),
    Lp.coeFn_compMeasurePreserving ξ hσ] with x hSx hσx
  exact hSx.trans (congrArg S hσx)

theorem ae_covariance_apply_of_commute
    (T J : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (J ξ) x = S (ξ (σ x)))
    (hcomm : Commute T J) (v : E) :
    ∀ᵐ x ∂μ, A x (S v) = S (A (σ x) v) := by
  let c := Lp.const 2 μ v
  have hc : ∀ᵐ x ∂μ, c (σ x) = v :=
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ v)
  have hTc : ∀ᵐ x ∂μ, (T c) (σ x) = A (σ x) (c (σ x)) :=
    hσ.quasiMeasurePreserving.ae (hT c)
  have heq : T (J c) = J (T c) :=
    congrArg (fun R : Lp E 2 μ →L[ℂ] Lp E 2 μ => R c) hcomm.eq
  filter_upwards [hT (J c), hJ c, hJ (T c), hc, hTc] with x hTx hJx hJTx hcx hTcx
  have heqx := congrArg (fun ξ : Lp E 2 μ => ξ x) heq
  rw [hTx, hJx, hJTx, hTcx, hcx] at heqx
  exact heqx

theorem ae_matrix_covariance_of_commute
    (b : HilbertBasis ℤ ℂ E)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (J : ℤ → Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (S : ℤ → E →ₗᵢ[ℂ] E) (σ : ℤ → Ω → Ω)
    (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hS : ∀ r k : ℤ, S r (b k) = b (k + r))
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ r (ξ : Lp E 2 μ), ∀ᵐ x ∂μ, (J r ξ) x = S r (ξ (σ r x)))
    (hcomm : ∀ r, Commute T (J r)) :
    ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) =
        inner ℂ (b (k + r)) (A x (b (l + r))) := by
  intro r k l
  have hv := ae_covariance_apply_of_commute T (J r) A (S r).toContinuousLinearMap
    (σ r) (hσ r) hT (hJ r) (hcomm r) (b l)
  filter_upwards [hv] with x hx
  change A x (S r (b l)) = S r (A (σ r x) (b l)) at hx
  calc
    inner ℂ (b k) (A (σ r x) (b l)) =
        inner ℂ (S r (b k)) (S r (A (σ r x) (b l))) :=
      ((S r).inner_map_map (b k) (A (σ r x) (b l))).symm
    _ = inner ℂ (b (k + r)) (A x (b (l + r))) := by
      rw [hS, ← hx, hS]

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldKoopman
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.FieldKoopman

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X}

open DirectIntegral

theorem operator_ae (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (ξ : Lp E 2 μ) :
    shiftedPullback S σ hσ ξ =ᵐ[μ] fun x => S (ξ (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ ξ),
    Lp.coeFn_compMeasurePreserving ξ hσ] with x hx hy
  exact hx.trans (congrArg S hy)

theorem operator_mul (S R : E →L[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ) :
    shiftedPullback S σ hσ * shiftedPullback R τ hτ =
      shiftedPullback (S * R) (τ ∘ σ) (hτ.comp hσ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [operator_ae S σ hσ (shiftedPullback R τ hτ ξ),
    hσ.quasiMeasurePreserving.ae (operator_ae R τ hτ ξ),
    operator_ae (S * R) (τ ∘ σ) (hτ.comp hσ) ξ] with x hx hy hz
  change shiftedPullback S σ hσ (shiftedPullback R τ hτ ξ) x = _
  rw [hx, hy, hz]
  rfl

theorem operator_one_id :
    shiftedPullback (1 : E →L[ℂ] E) id (MeasurePreserving.id μ) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [operator_ae (1 : E →L[ℂ] E) id (MeasurePreserving.id μ) ξ] with x hx
  exact hx

theorem operator_mul_eq_one (S R : E →L[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hSR : S * R = 1) (hτσ : τ ∘ σ = id) :
    shiftedPullback S σ hσ * shiftedPullback R τ hτ = 1 := by
  rw [operator_mul, hSR]
  simpa only [hτσ] using (operator_one_id (E := E) (μ := μ))

theorem commute_of_represented_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (shiftedPullback S σ hσ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (shiftedPullback S σ hσ ξ), operator_ae S σ hσ ξ,
    operator_ae S σ hσ (T ξ), hσ.quasiMeasurePreserving.ae (hT ξ), hcov]
    with x hTx hJx hJTx hTσx hcovx
  change T (shiftedPullback S σ hσ ξ) x = shiftedPullback S σ hσ (T ξ) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun B : E →L[ℂ] E => B (ξ (σ x))) hcovx

theorem commute_const (R S : E →L[ℂ] E) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hRS : Commute R S) :
    Commute (R.compLpL 2 μ) (shiftedPullback S σ hσ) := by
  apply commute_of_represented_covariance (R.compLpL 2 μ) (fun _ => R)
    (fun ξ => R.coeFn_compLpL ξ) S σ hσ
  exact Filter.Eventually.of_forall (fun _ => hRS.eq)

theorem norm_operator (S : E ≃ₗᵢ[ℂ] E) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) (ξ : Lp E 2 μ) :
    ‖shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ξ‖ = ‖ξ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ξ) 2 μ =
        eLpNorm (fun x => ξ (σ x)) 2 μ := by
      apply eLpNorm_congr_norm_ae
      filter_upwards [operator_ae S.toLinearIsometry.toContinuousLinearMap σ hσ ξ]
        with x hx
      rw [hx]
      exact S.norm_map _
    _ = eLpNorm ξ 2 μ :=
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable ξ) hσ

def equivalence (S : E ≃ₗᵢ[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hτσ : τ ∘ σ = id) (hστ : σ ∘ τ = id) :
    Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ where
  toFun := shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ
  invFun := shiftedPullback S.symm.toLinearIsometry.toContinuousLinearMap τ hτ
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv ξ := by
    have h := operator_mul_eq_one S.symm.toLinearIsometry.toContinuousLinearMap
      S.toLinearIsometry.toContinuousLinearMap τ σ hτ hσ
      (by ext v; exact S.symm_apply_apply v) hστ
    exact congrArg (fun T : Lp E 2 μ →L[ℂ] Lp E 2 μ => T ξ) h
  right_inv ξ := by
    have h := operator_mul_eq_one S.toLinearIsometry.toContinuousLinearMap
      S.symm.toLinearIsometry.toContinuousLinearMap σ τ hσ hτ
      (by ext v; exact S.apply_symm_apply v) hτσ
    exact congrArg (fun T : Lp E 2 μ →L[ℂ] Lp E 2 μ => T ξ) h
  norm_map' := norm_operator S σ hσ

theorem operator_mem_unitary
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : F ≃ₗᵢ[ℂ] F) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hτσ : τ ∘ σ = id) (hστ : σ ∘ τ = id) :
    shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ∈
      unitary (Lp F 2 μ →L[ℂ] Lp F 2 μ) := by
  exact (Unitary.linearIsometryEquiv.symm (equivalence S σ τ hσ hτ hτσ hστ)).property

end Invariant233.FieldKoopman

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_GeneratedVonNeumann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

@[simp]
theorem coe_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    (vonNeumannGenerated s : Set (H →L[ℂ] H)) =
      (s ∪ star s).centralizer.centralizer := by
  exact StarSubalgebra.coe_centralizer_centralizer ℂ s

theorem subset_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    s ⊆ vonNeumannGenerated s := by
  rw [coe_vonNeumannGenerated]
  exact Set.Subset.trans Set.subset_union_left Set.subset_centralizer_centralizer

@[simp]
theorem coe_commutant_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    ((vonNeumannGenerated s).commutant : Set (H →L[ℂ] H)) =
      (s ∪ star s).centralizer := by
  rw [VonNeumannAlgebra.coe_commutant, coe_vonNeumannGenerated,
    Set.centralizer_centralizer_centralizer]

theorem mem_commutant_vonNeumannGenerated_iff (s : Set (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ (vonNeumannGenerated s).commutant ↔
      ∀ A ∈ s, A * T = T * A ∧ star A * T = T * star A := by
  change T ∈ ((vonNeumannGenerated s).commutant : Set (H →L[ℂ] H)) ↔ _
  rw [coe_commutant_vonNeumannGenerated]
  exact StarSubalgebra.mem_centralizer_iff ℂ

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldKoopmanGenerated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.FieldKoopman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_star_left_of_unitary {A J : H →L[ℂ] H}
    (hJ : J ∈ unitary (H →L[ℂ] H)) (h : Commute A J) : Commute (star A) J := by
  apply Commute.symm
  apply (commute_unitary_iff_star_left_conjugate hJ).mpr
  have heq := congrArg star ((commute_unitary_iff_star_left_conjugate hJ).mp h.symm)
  simpa only [star_mul, star_star, mul_assoc] using heq

theorem commute_of_mem_generated_of_unitary
    (s : Set (H →L[ℂ] H)) {J : H →L[ℂ] H}
    (hJ : J ∈ unitary (H →L[ℂ] H))
    (hs : ∀ A ∈ s, Commute A J) {T : H →L[ℂ] H}
    (hT : T ∈ vonNeumannGenerated s) : Commute T J := by
  have hmem : J ∈ (vonNeumannGenerated s).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff s J).mpr
    intro A hA
    exact ⟨(hs A hA).eq, (commute_star_left_of_unitary hJ (hs A hA)).eq⟩
  change T * J = J * T
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hmem) T hT

end Invariant233.FieldKoopman

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FieldUnboundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

abbrev FieldHilbert := Lp Hilbert 2 μ

def fieldMultiplierGraph (h : X → ℤ → ℂ) :
    Submodule ℂ (FieldHilbert μ × FieldHilbert μ) where
  carrier := {p | ∀ᵐ x ∂μ, ∀ k, p.2 x k = h x k * p.1 x k}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero Hilbert 2 μ] with x hx
    intro k
    simp only [Prod.fst_zero, Prod.snd_zero, hx, Pi.zero_apply, lp.coeFn_zero, mul_zero]
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.1 q.1, Lp.coeFn_add p.2 q.2]
      with x hp hq hfst hsnd
    intro k
    change (p.2 + q.2) x k = h x k * (p.1 + q.1) x k
    rw [hsnd, hfst]
    change p.2 x k + q.2 x k = h x k * (p.1 x k + q.1 x k)
    rw [hp, hq, mul_add]
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2]
      with x hp hfst hsnd
    intro k
    change (c • p.2) x k = h x k * (c • p.1) x k
    rw [hsnd, hfst]
    change c * p.2 x k = h x k * (c * p.1 x k)
    rw [hp, mul_left_comm]

def fieldUnboundedMultiplier (h : X → ℤ → ℂ) :
    FieldHilbert μ →ₗ.[ℂ] FieldHilbert μ :=
  (fieldMultiplierGraph μ h).toLinearPMap

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldUnboundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldHilbert_ext {ξ η : FieldHilbert μ}
    (h : ∀ᵐ x ∂μ, ∀ k, ξ x k = η x k) : ξ = η := by
  apply Lp.ext
  filter_upwards [h] with x hx
  exact lp.ext (funext hx)

theorem fieldMultiplierGraph_unique (h : X → ℤ → ℂ)
    {ξ η ζ : FieldHilbert μ}
    (hη : (ξ, η) ∈ fieldMultiplierGraph μ h)
    (hζ : (ξ, ζ) ∈ fieldMultiplierGraph μ h) : η = ζ := by
  apply fieldHilbert_ext
  filter_upwards [hη, hζ] with x hη hζ
  intro k
  exact (hη k).trans (hζ k).symm

theorem fieldMultiplierGraph_zero (h : X → ℤ → ℂ)
    (p : FieldHilbert μ × FieldHilbert μ)
    (hp : p ∈ fieldMultiplierGraph μ h) (hzero : p.1 = 0) : p.2 = 0 := by
  apply fieldHilbert_ext
  filter_upwards [hp, Lp.coeFn_zero Hilbert 2 μ] with x hx hz
  intro k
  rw [hx, hzero, hz]
  simp

theorem mem_fieldUnboundedMultiplier_domain_iff (h : X → ℤ → ℂ)
    (ξ : FieldHilbert μ) :
    ξ ∈ (fieldUnboundedMultiplier μ h).domain ↔
      ∃ η : FieldHilbert μ, ∀ᵐ x ∂μ, ∀ k, η x k = h x k * ξ x k := by
  change ξ ∈ (fieldMultiplierGraph μ h).map (LinearMap.fst ℂ _ _) ↔ _
  constructor
  · rintro ⟨⟨ζ, η⟩, hζη, hζ⟩
    change ζ = ξ at hζ
    subst ζ
    exact ⟨η, hζη⟩
  · rintro ⟨η, hη⟩
    exact ⟨(ξ, η), hη, rfl⟩

theorem fieldUnboundedMultiplier_apply_ae (h : X → ℤ → ℂ)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    ∀ᵐ x ∂μ, ∀ k, fieldUnboundedMultiplier μ h ξ x k = h x k * ξ.val x k :=
  (fieldMultiplierGraph μ h).mem_graph_toLinearPMap (fieldMultiplierGraph_zero h) ξ

theorem fieldUnboundedMultiplier_eq_of_ae (h : X → ℤ → ℂ)
    (ξ : (fieldUnboundedMultiplier μ h).domain) (η : FieldHilbert μ)
    (hη : ∀ᵐ x ∂μ, ∀ k, η x k = h x k * ξ.val x k) :
    fieldUnboundedMultiplier μ h ξ = η :=
  fieldMultiplierGraph_unique h (fieldUnboundedMultiplier_apply_ae h ξ) hη

theorem field_operator_mem_multiplierDomain
    (h f g : X → ℤ → ℂ) (c : ℂ)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    A ξ.val ∈ (fieldUnboundedMultiplier μ h).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff h _).mpr
  refine ⟨c • B (fieldUnboundedMultiplier μ h ξ), ?_⟩
  filter_upwards [hA ξ.val, hB (fieldUnboundedMultiplier μ h ξ),
    fieldUnboundedMultiplier_apply_ae h ξ, hfg,
    Lp.coeFn_smul c (B (fieldUnboundedMultiplier μ h ξ))]
    with x hA hB hH hfg hsmul
  intro k
  rw [hsmul]
  change c * B (fieldUnboundedMultiplier μ h ξ) x k = h x k * A ξ.val x k
  rw [hA, hB, hH]
  have hk := hfg (k - 1)
  simp only [sub_add_cancel] at hk
  rw [← mul_assoc (h x k), hk]
  ring

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SpectralCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.WeightedShift.SpectralCutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def boundedWeight (a : X → ℤ → ℂ) (C : ℝ)
    (ha : ∀ x k, ‖a x k‖ ≤ C) (x : X) : Weight :=
  ⟨a x, memℓp_infty ⟨C, by rintro r ⟨k, rfl⟩; exact ha x k⟩⟩

def boundedOperator (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (boundedWeight a C ha) C hC
    (fun x => lp.norm_le_of_forall_le hC (ha x)) hm

def window (n : ℕ) : Set ℝ := Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1 : ℝ)

def symbol (n : ℕ) (r : ℝ) : ℂ := (window n).indicator (fun _ => 1) r

theorem norm_symbol_le (n : ℕ) (r : ℝ) : ‖symbol n r‖ ≤ 1 := by
  classical
  by_cases hr : r ∈ window n
  · simp [symbol, hr]
  · simp [symbol, hr]

def projection (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => symbol n (h x k)) 1 (by norm_num)
    (fun x k => norm_symbol_le n (h x k))
    (fun k => ((measurable_const.indicator measurableSet_Icc).comp (hm k)).aestronglyMeasurable)

def productSymbol (n : ℕ) (r : ℝ) : ℂ := (r : ℂ) * symbol n r

def inverseSymbol (n : ℕ) (r : ℝ) : ℂ := (r⁻¹ : ℝ) * symbol n r

theorem norm_productSymbol_le (n : ℕ) (r : ℝ) :
    ‖productSymbol n r‖ ≤ n + 1 := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : 0 ≤ r := le_trans (by positivity) hr.1
    simpa [productSymbol, symbol, hr, Complex.norm_real, abs_of_nonneg hr0] using hr.2
  · simp [productSymbol, symbol, hr] <;> positivity

theorem norm_inverseSymbol_le (n : ℕ) (r : ℝ) :
    ‖inverseSymbol n r‖ ≤ n + 1 := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1
    have hbound : r⁻¹ ≤ n + 1 := (inv_le_comm₀ hr0 (by positivity)).mpr hr.1
    simpa [inverseSymbol, symbol, hr, Complex.norm_real, abs_of_pos hr0] using hbound
  · simp [inverseSymbol, symbol, hr] <;> positivity

def productOperator (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => productSymbol n (h x k)) (n + 1) (by positivity)
    (fun x k => norm_productSymbol_le n (h x k))
    (fun k => ((Complex.measurable_ofReal.comp (hm k)).mul
      ((measurable_const.indicator measurableSet_Icc).comp (hm k))).aestronglyMeasurable)

def inverseOperator (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => inverseSymbol n (h x k)) (n + 1) (by positivity)
    (fun x k => norm_inverseSymbol_le n (h x k))
    (fun k => ((Complex.measurable_ofReal.comp (hm k).inv).mul
      ((measurable_const.indicator measurableSet_Icc).comp (hm k))).aestronglyMeasurable)

def cutoffSpace (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    Submodule ℂ (FieldHilbert μ) := (projection h hm n).range.topologicalClosure

instance cutoffSpace_hasOrthogonalProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (cutoffSpace (μ := μ) h hm n).HasOrthogonalProjection := by
  let : IsClosed (cutoffSpace (μ := μ) h hm n : Set (FieldHilbert μ)) :=
    Submodule.isClosed_topologicalClosure _
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldMultiplierCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift.SpectralCutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem real_mul_inverseSymbol (n : ℕ) (r : ℝ) :
    (r : ℂ) * inverseSymbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hr.1)
    simp [inverseSymbol, symbol, hr, hr0]
  · simp [inverseSymbol, symbol, hr]

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldPositivity
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology ComplexOrder

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem indicator_quadratic_eq_setIntegral
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (v : E) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (T (indicatorConstLp 2 hs (measure_ne_top μ s) v))
      (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
        ∫ x in s, inner ℂ (A x v) v ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := v),
    hT (indicatorConstLp 2 hs (measure_ne_top μ s) v)] with x hx hTx
  rw [hTx, hx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
  · simp only [Set.indicator_of_notMem hxs, map_zero, inner_zero_left]

theorem integrable_represented_quadratic
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) (v : E) :
    Integrable (fun x => inner ℂ (A x v) v) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (T (Lp.const 2 μ v))
    (Lp.const 2 μ v)).congr
  filter_upwards [Lp.coeFn_const 2 μ v, hT (Lp.const 2 μ v)] with x hx hTx
  rw [hTx, hx]
  rfl

theorem ae_represented_quadratic_nonneg
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : T.IsPositive) (v : E) :
    ∀ᵐ x ∂μ, 0 ≤ (inner ℂ (A x v) v).re ∧ (inner ℂ (A x v) v).im = 0 := by
  have hi := integrable_represented_quadratic T A hT v
  have hlocal (s : Set Ω) (hs : MeasurableSet s) :
      0 ≤ ∫ x in s, inner ℂ (A x v) v ∂μ := by
    rw [← indicator_quadratic_eq_setIntegral T A hT v s hs]
    exact hpos.inner_nonneg_left _
  have hreal : 0 ≤ᵐ[μ] fun x => (inner ℂ (A x v) v).re := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hi.re
    intro s hs _
    rw [integral_re hi.integrableOn]
    exact (Complex.nonneg_iff.mp (hlocal s hs)).1
  have him : (fun x => (inner ℂ (A x v) v).im) =ᵐ[μ] 0 := by
    apply hi.im.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    rw [integral_im hi.integrableOn]
    exact (Complex.nonneg_iff.mp (hlocal s hs)).2.symm
  filter_upwards [hreal, him] with x hr hm
  exact ⟨hr, hm⟩

theorem ae_isPositive_of_represented_isPositive [TopologicalSpace.SeparableSpace E]
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : T.IsPositive) : ∀ᵐ x ∂μ, (A x).IsPositive := by
  let v := TopologicalSpace.denseSeq E
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq E
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      0 ≤ (inner ℂ (A x (v n)) (v n)).re ∧
        (inner ℂ (A x (v n)) (v n)).im = 0 :=
    ae_all_iff.mpr (fun n => ae_represented_quadratic_nonneg T A hT hpos (v n))
  filter_upwards [hall] with x hx
  apply (ContinuousLinearMap.isPositive_iff_complex (A x)).mpr
  intro w
  have hc : Continuous (fun w => inner ℂ (A x w) w) :=
    (A x).continuous.inner continuous_id
  have hm : 0 ≤ (inner ℂ (A x w) w).re ∧ (inner ℂ (A x w) w).im = 0 :=
    hv.induction_on w
      ((isClosed_le continuous_const (Complex.continuous_re.comp hc)).inter
        (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)) hx
  refine ⟨?_, hm.1⟩
  apply Complex.ext
  · simp
  · simpa using hm.2.symm

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldsNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.Fields

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem ae_norm_le_of_local_square_integral [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {v : Y → E} {C : ℝ}
    (hC : 0 ≤ C) (hv : Integrable (fun y => ‖v y‖ ^ 2) μ)
    (hlocal : ∀ s, MeasurableSet s →
      (∫ y in s, ‖v y‖ ^ 2 ∂μ) ≤ C ^ 2 * μ.real s) :
    ∀ᵐ y ∂μ, ‖v y‖ ≤ C := by
  have hsq : (fun y => ‖v y‖ ^ 2) ≤ᵐ[μ] (fun _ => C ^ 2) := by
    apply ae_le_of_forall_setIntegral_le hv (integrable_const _)
    intro s hs _
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hlocal s hs
  filter_upwards [hsq] with y hy
  nlinarith [norm_nonneg (v y)]


variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Countable ι]

theorem ae_eq_of_countable_columns {A B : Y → E →L[𝕜] F} {v : ι → E}
    (hv : Dense (Submodule.span 𝕜 (Set.range v) : Set E))
    (hcol : ∀ i, ∀ᵐ y ∂μ, A y (v i) = B y (v i)) :
    A =ᵐ[μ] B := by
  have hcols : ∀ᵐ y ∂μ, ∀ i, A y (v i) = B y (v i) :=
    ae_all_iff.mpr hcol
  filter_upwards [hcols] with y hy
  apply ContinuousLinearMap.ext_on hv
  rintro _ ⟨i, rfl⟩
  exact hy i


end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FiniteConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.FiniteConvolution

abbrev Coefficients (K : ℕ) := Fin (2 * K + 1) → ℂ

def center (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩

noncomputable def polynomial {K : ℕ} (a : Coefficients K) : Polynomial ℂ :=
  ∑ i : Fin (2 * K + 1), Polynomial.monomial (i : ℕ) (a i)

noncomputable def lowProduct {K : ℕ} (a b : Coefficients K) : Coefficients K :=
  fun n => (polynomial a * polynomial b).coeff (n : ℕ)

end InvariantProjection.FiniteConvolution

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FiniteConvolutionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open Polynomial

theorem exists_nonzero_product_coeff_le
    {R : Type*} [Semiring R] [NoZeroDivisors R]
    (A B : R[X]) (k l : ℕ)
    (hA : A.coeff k ≠ 0) (hB : B.coeff l ≠ 0) :
    ∃ n ≤ k + l, (A * B).coeff n ≠ 0 := by
  have hA0 : A ≠ 0 := by
    intro h
    simp [h] at hA
  have hB0 : B ≠ 0 := by
    intro h
    simp [h] at hB
  refine ⟨(A * B).natTrailingDegree, ?_, ?_⟩
  · rw [natTrailingDegree_mul hA0 hB0]
    exact Nat.add_le_add
      (natTrailingDegree_le_of_ne_zero hA)
      (natTrailingDegree_le_of_ne_zero hB)
  · exact coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hA0 hB0)

theorem exists_nonzero_product_coeff_le_two_mul
    (A B : ℂ[X]) (K : ℕ)
    (hA : A.coeff K ≠ 0) (hB : B.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (A * B).coeff n ≠ 0 := by
  simpa [two_mul] using exists_nonzero_product_coeff_le A B K K hA hB

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.FiniteConvolution

@[simp] theorem polynomial_coeff {K : ℕ} (a : Coefficients K)
    (i : Fin (2 * K + 1)) : (polynomial a).coeff (i : ℕ) = a i := by
  classical
  simp [polynomial, Polynomial.coeff_monomial,
    Fin.val_inj]

theorem continuous_lowProduct (K : ℕ) :
    Continuous (fun p : Coefficients K × Coefficients K => lowProduct p.1 p.2) := by
  classical
  apply continuous_pi
  intro n
  simp only [lowProduct, polynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.finsetSum_coeff, Polynomial.monomial_mul_monomial]
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  simp only [Polynomial.coeff_monomial]
  split_ifs <;> fun_prop

theorem uniform_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖ := by
  classical
  let S : Set (Coefficients K) :=
    Metric.closedBall 0 D ∩ {a | δ ≤ ‖a (center K)‖}
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : Coefficients K) D).inter_right
      (isClosed_le continuous_const (continuous_apply (center K)).norm)
  have hpositive : ∀ p ∈ S ×ˢ S, 0 < ‖lowProduct p.1 p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    have ha : (polynomial p.1).coeff K ≠ 0 := by
      change (polynomial p.1).coeff ((center K) : ℕ) ≠ 0
      rw [polynomial_coeff]
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ hp.1.2)
    have hb : (polynomial p.2).coeff K ≠ 0 := by
      change (polynomial p.2).coeff ((center K) : ℕ) ≠ 0
      rw [polynomial_coeff]
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ hp.2.2)
    obtain ⟨n, hn, hne⟩ :=
      InvariantProjection.exists_nonzero_product_coeff_le_two_mul
        (polynomial p.1) (polynomial p.2) K ha hb
    intro hz
    apply hne
    have he := congrFun hz (⟨n, by omega⟩ : Fin (2 * K + 1))
    simpa only [lowProduct, Pi.zero_apply] using he
  obtain ⟨ε, hε, hbound⟩ := (hS.prod hS).exists_forall_le'
    (continuous_lowProduct K).norm.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb hca hcb
  have haS : a ∈ S := by
    refine ⟨?_, hca⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (ha (center K)))).mpr ha)
  have hbS : b ∈ S := by
    refine ⟨?_, hcb⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hb (center K)))).mpr hb)
  have hnorm := hbound (a, b) ⟨haS, hbS⟩
  by_contra h
  push Not at h
  exact (not_lt_of_ge hnorm) ((pi_norm_lt_iff hε).mpr h)

end InvariantProjection.FiniteConvolution

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FrequencySplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.PrescribedPhaseRealization

def spliceFrequency (old new : ℕ → ℕ) (p : ℕ) (i : ℕ) : ℕ :=
  if i ≤ p then old i else new (i - p)

theorem spliceFrequency_eq_old (old new : ℕ → ℕ) {p i : ℕ} (hi : i ≤ p) :
    spliceFrequency old new p i = old i := by
  simp [spliceFrequency, hi]

theorem spliceFrequency_eq_new (old new : ℕ → ℕ) {p i : ℕ}
    (hboundary : new 0 = old p) (hi : p ≤ i) :
    spliceFrequency old new p i = new (i - p) := by
  rcases eq_or_lt_of_le hi with rfl | hi
  · simp [spliceFrequency, hboundary]
  · simp [spliceFrequency, Nat.not_le.mpr hi]

@[simp] theorem spliceFrequency_add (old new : ℕ → ℕ) (p i : ℕ)
    (hboundary : new 0 = old p) :
    spliceFrequency old new p (p + i) = new i := by
  simpa using spliceFrequency_eq_new old new hboundary (Nat.le_add_right p i)

theorem spliceFrequency_pos (old new : ℕ → ℕ) (p : ℕ)
    (hold : ∀ i ≤ p, 0 < old i) (hnew : ∀ i, 0 < new i) :
    ∀ i, 0 < spliceFrequency old new p i := by
  intro i
  by_cases hi : i ≤ p
  · simpa [spliceFrequency, hi] using hold i hi
  · simpa [spliceFrequency, hi] using hnew (i - p)

theorem spliceFrequency_strictMono (old new : ℕ → ℕ) (p : ℕ)
    (hboundary : new 0 = old p)
    (hold : ∀ i < p, old i < old (i + 1)) (hnew : StrictMono new) :
    StrictMono (spliceFrequency old new p) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hi : i < p
  · rw [spliceFrequency_eq_old old new (by omega),
      spliceFrequency_eq_old old new (by omega)]
    exact hold i hi
  · rw [spliceFrequency_eq_new old new hboundary (by omega),
      spliceFrequency_eq_new old new hboundary (by omega)]
    apply hnew
    omega

theorem spliceFrequency_divisible (old new : ℕ → ℕ) (p : ℕ)
    (hboundary : new 0 = old p)
    (hold : ∀ i < p, old i ∣ old (i + 1))
    (hnew : ∀ i, new i ∣ new (i + 1)) :
    ∀ i, spliceFrequency old new p i ∣ spliceFrequency old new p (i + 1) := by
  intro i
  by_cases hi : i < p
  · rw [spliceFrequency_eq_old old new (by omega),
      spliceFrequency_eq_old old new (by omega)]
    exact hold i hi
  · rw [spliceFrequency_eq_new old new hboundary (by omega),
      spliceFrequency_eq_new old new hboundary (by omega)]
    have he : i + 1 - p = (i - p) + 1 := by omega
    rw [he]
    exact hnew (i - p)

end Invariant233.PrescribedPhaseRealization

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FrequencyTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.PrescribedPhaseRealization

theorem frequencyTower_stable (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d)
    (hkeep : ∀ j i, i ≤ d j → q (j + 1) i = q j i)
    {j k i : ℕ} (hjk : j ≤ k) (hi : i ≤ d j) : q k i = q j i := by
  induction k with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        rfl
      · have hjk' : j ≤ k := by omega
        calc
          q (k + 1) i = q k i := hkeep k i (hi.trans (hd hjk'))
          _ = q j i := ih hjk'

theorem exists_frequency_of_prefix_tower (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hcover : ∀ j, j ≤ d j)
    (hkeep : ∀ j i, i ≤ d j → q (j + 1) i = q j i)
    (hpos : ∀ j i, i ≤ d j → 0 < q j i)
    (hmono : ∀ j i, i < d j → q j i < q j (i + 1))
    (hdiv : ∀ j i, i < d j → q j i ∣ q j (i + 1)) :
    ∃ Q : ℕ → ℕ, (∀ j i, i ≤ d j → Q i = q j i) ∧
      (∀ i, 0 < Q i) ∧ StrictMono Q ∧ (∀ i, Q i ∣ Q (i + 1)) := by
  let Q : ℕ → ℕ := fun i => q i i
  have hagree : ∀ j i, i ≤ d j → Q i = q j i := by
    intro j i hi
    have ha := frequencyTower_stable d q hd hkeep (le_max_right j i) (hcover i)
    have hb := frequencyTower_stable d q hd hkeep (le_max_left j i) hi
    exact ha.symm.trans hb
  refine ⟨Q, hagree, ?_, ?_, ?_⟩
  · intro i
    exact hpos i i (hcover i)
  · apply strictMono_nat_of_lt_succ
    intro i
    have hi : i < d (i + 1) := (Nat.lt_succ_self i).trans_le (hcover (i + 1))
    rw [hagree (i + 1) i hi.le, hagree (i + 1) (i + 1) (hcover (i + 1))]
    exact hmono (i + 1) i hi
  · intro i
    have hi : i < d (i + 1) := (Nat.lt_succ_self i).trans_le (hcover (i + 1))
    rw [hagree (i + 1) i hi.le, hagree (i + 1) (i + 1) (hcover (i + 1))]
    exact hdiv (i + 1) i hi

end Invariant233.PrescribedPhaseRealization

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LaurentWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.LaurentWindow

open Polynomial LaurentPolynomial

variable {R : Type*} [Semiring R]

@[simp] theorem coeff_trunc (A : LaurentPolynomial R) (n : ℕ) :
    (LaurentPolynomial.trunc A).coeff n = A.coeff (n : ℤ) := by
  rfl

@[simp] theorem coeff_trunc_mul_T (A : LaurentPolynomial R) (k : ℤ) (n : ℕ) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T k)).coeff n =
      A.coeff ((n : ℤ) - k) := by
  rw [coeff_trunc, LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_one, sub_eq_add_neg]

@[simp] theorem coeff_toLaurent_nat (p : Polynomial R) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  change (Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff) n = _
  exact Finsupp.mapDomain_apply Nat.cast_injective _ n

@[simp] theorem coeff_toLaurent_neg (p : Polynomial R) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  change (Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff) n = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, rfl⟩
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

@[simp] theorem coeff_mul_T (A : LaurentPolynomial R) (k n : ℤ) :
    (A * LaurentPolynomial.T k).coeff n = A.coeff (n - k) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_one, sub_eq_add_neg]

theorem toLaurent_trunc_of_nonnegative (A : LaurentPolynomial R)
    (hA : ∀ n : ℤ, n < 0 → A.coeff n = 0) :
    (LaurentPolynomial.trunc A).toLaurent = A := by
  ext n
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [coeff_toLaurent_nat, coeff_trunc]
  · rw [coeff_toLaurent_neg _ n (lt_of_not_ge hn), hA n (lt_of_not_ge hn)]

theorem toLaurent_trunc_shift (K : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ n : ℤ, n < -(K : ℤ) → A.coeff n = 0) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))).toLaurent =
      A * LaurentPolynomial.T (K : ℤ) := by
  apply toLaurent_trunc_of_nonnegative
  intro n hn
  rw [coeff_mul_T]
  apply hA
  omega

theorem coeff_trunc_shift_above (K n : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ i : ℤ, (K : ℤ) < i → A.coeff i = 0) (hn : 2 * K < n) :
    (LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))).coeff n = 0 := by
  rw [coeff_trunc_mul_T]
  apply hA
  omega

theorem coeff_fin_sum_monomial (N : ℕ) (a : Fin N → R) (i : Fin N) :
    (∑ j : Fin N, Polynomial.monomial (j : ℕ) (a j)).coeff (i : ℕ) = a i := by
  classical
  simp [Polynomial.coeff_monomial, Fin.val_inj]

theorem coeff_window_sum (s : Finset ℤ) (a : ℤ → R) (n : ℤ) :
    (∑ i ∈ s, (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)).coeff n =
      if n ∈ s then a n else 0 := by
  classical
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp

theorem coeff_window_product (s t : Finset ℤ) (a b : ℤ → R) (n : ℤ) :
    ((∑ i ∈ s, (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)) *
      (∑ j ∈ t, (AddMonoidAlgebra.single j (b j) : LaurentPolynomial R))).coeff n =
      ∑ i ∈ s, if n - i ∈ t then a i * b (n - i) else 0 := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [show ∀ j : ℤ, i + j = n ↔ j = n - i by intro j; omega]
  simp

theorem coeff_symmetric_window_product (K : ℕ) (a b : ℤ → R) (n : ℤ) :
    ((∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (AddMonoidAlgebra.single i (a i) : LaurentPolynomial R)) *
      (∑ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (AddMonoidAlgebra.single j (b j) : LaurentPolynomial R))).coeff (-n) =
      ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i => |n + i| ≤ (K : ℤ)),
        a i * b (-n - i) := by
  classical
  rw [coeff_window_product, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hiff : -n - i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ↔ |n + i| ≤ (K : ℤ) := by
    simp only [Finset.mem_Icc, abs_le]
    omega
  simp only [hiff]


variable {S : Type*} [CommSemiring S]

theorem coeff_shifted_product (K n : ℕ) (A B : LaurentPolynomial S)
    (hA : ∀ i : ℤ, i < -(K : ℤ) → A.coeff i = 0)
    (hB : ∀ i : ℤ, i < -(K : ℤ) → B.coeff i = 0) :
    ((LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ))) *
      (LaurentPolynomial.trunc (B * LaurentPolynomial.T (K : ℤ)))).coeff n =
      (A * B).coeff ((n : ℤ) - 2 * (K : ℤ)) := by
  rw [← coeff_toLaurent_nat, map_mul,
    toLaurent_trunc_shift K A hA, toLaurent_trunc_shift K B hB]
  rw [mul_mul_mul_comm, ← LaurentPolynomial.T_add, coeff_mul_T]
  congr 1
  omega


end Invariant233.LaurentWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_LaurentConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

def laurent (K : ℕ) (a : ℤ → ℂ) : LaurentPolynomial ℂ :=
  ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), AddMonoidAlgebra.single i (a i)

def convolution (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i => |(n : ℤ) + i| ≤ (K : ℤ)),
    a i * b (-(n : ℤ) - i)

end Invariant233.FiniteWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LaurentNoncancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

open Invariant233.LaurentWindow
open InvariantProjection.FiniteConvolution

@[simp] theorem laurent_coeff (K : ℕ) (a : ℤ → ℂ) (i : ℤ) :
    (laurent K a).coeff i = if |i| ≤ (K : ℤ) then a i else 0 := by
  rw [laurent, coeff_window_sum]
  simp only [Finset.mem_Icc, abs_le]

@[simp] theorem laurent_coeff_zero (K : ℕ) (a : ℤ → ℂ) :
    (laurent K a).coeff 0 = a 0 := by
  simp only [laurent_coeff, abs_zero, Int.natCast_nonneg, ite_true, if_true]

theorem coeff_laurent_product (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) :
    (laurent K a * laurent K b).coeff (-(n : ℤ)) = convolution K a b n :=
  coeff_symmetric_window_product K a b (n : ℤ)

end Invariant233.FiniteWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ConditionalConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal lp ComplexConjugate

noncomputable section

namespace InvariantProjection.ConditionalConvolution

def window (K : ℕ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter fun v => |(n : ℤ) + v| ≤ (K : ℤ)

def selector (K : ℕ) (n : ℕ) (v : ℤ) : ℤ :=
  if (K : ℤ) < |v| then v else (n : ℤ) + v

def omittedEvent {Ω : Type*} (H : ℤ → Set Ω) (K : ℕ) (n : ℕ) (v : ℤ) : Set Ω :=
  if v ∈ window K n then ∅ else H (selector K n v)

def truncated (K : ℕ) (n : ℕ) (A B : ℤ → ℂ) : ℂ :=
  ∑ v ∈ window K n, A v * B (-(n : ℤ) - v)

def coeffA {Ω : Type*} (ξ : Ω → ℓ²(ℤ, ℂ)) (Fx : Ω → ℤ → ℝ)
    (ω : Ω) (v : ℤ) : ℂ := ξ ω v / (Fx ω v : ℂ)

def coeffB {Ω : Type*} (γ : Ω → ℓ²(ℤ, ℂ)) (Fy : Ω → ℤ → ℝ)
    (ω : Ω) (w : ℤ) : ℂ := (Fy ω (-w) : ℂ) * conj (γ ω (-w))

structure Data (Ω : Type*) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (D a c η δ : ℝ) where
  mX : MeasurableSpace Ω
  mY : MeasurableSpace Ω
  mX_le : mX ≤ mΩ
  mY_le : mY ≤ mΩ
  ξ : Ω → ℓ²(ℤ, ℂ)
  γ : Ω → ℓ²(ℤ, ℂ)
  ξ_measurable : StronglyMeasurable[mX] ξ
  γ_measurable : StronglyMeasurable[mY] γ
  ξ_unit : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1
  γ_unit : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1
  Fx : Ω → ℤ → ℝ
  Fy : Ω → ℤ → ℝ
  Fx_measurable : ∀ k, Measurable[mΩ] (fun ω => Fx ω k)
  Fy_measurable : ∀ k, Measurable[mΩ] (fun ω => Fy ω k)
  Fx_pos : ∀ᵐ ω ∂μ, ∀ k, 0 < Fx ω k
  Fy_pos : ∀ᵐ ω ∂μ, ∀ k, 0 < Fy ω k
  Fx_zero : ∀ᵐ ω ∂μ, Fx ω 0 = 1
  Fy_zero : ∀ᵐ ω ∂μ, Fy ω 0 = 1
  zero_convolution : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ,
    (∑' v : ℤ, coeffA ξ Fx ω v * coeffB γ Fy ω (-(n : ℤ) - v)) = 0
  ratio_bounds : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ, ∀ v : ℤ,
    0 < Fy ω ((n : ℤ) + v) / Fx ω v ∧
    Fy ω ((n : ℤ) + v) / Fx ω v ≤
      min (Fy ω v / Fx ω v) (Fy ω ((n : ℤ) + v) / Fx ω ((n : ℤ) + v)) ∧
    min (Fy ω v / Fx ω v) (Fy ω ((n : ℤ) + v) / Fx ω ((n : ℤ) + v)) ≤ 1
  E : Set Ω
  E_measurable : MeasurableSet[mΩ] E
  E_mass : c ≤ μ.real E
  coefficient_bounds : ∀ᵐ ω ∂μ.restrict E,
    (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖coeffA ξ Fx ω v‖ ≤ D) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖coeffB γ Fy ω v‖ ≤ D) ∧
    a ≤ ‖coeffA ξ Fx ω 0‖ ∧ a ≤ ‖coeffB γ Fy ω 0‖
  H₁ : ℤ → Set Ω
  H₂ : ℤ → Set Ω
  H₁_measurable : ∀ k, MeasurableSet[mΩ] (H₁ k)
  H₂_measurable : ∀ k, MeasurableSet[mΩ] (H₂ k)
  attenuation : ∀ᵐ ω ∂μ.restrict E, ∀ k : ℤ, (K : ℤ) < |k| →
    Fy ω k / Fx ω k ≤ η + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
      (H₂ k).indicator (fun _ => (1 : ℝ)) ω
  conditional₁ : ∀ k : ℤ, (K : ℤ) < |k| →
    μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mX] ≤ᵐ[μ] fun _ => δ
  conditional₂ : ∀ k : ℤ, (K : ℤ) < |k| →
    μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | mY] ≤ᵐ[μ] fun _ => δ

end InvariantProjection.ConditionalConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OmittedEvents
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.ConditionalConvolution

open MeasureTheory

@[simp] theorem mem_window_iff (K n : ℕ) (v : ℤ) :
    v ∈ window K n ↔ |v| ≤ (K : ℤ) ∧ |(n : ℤ) + v| ≤ (K : ℤ) := by
  simp only [window, Finset.mem_filter, Finset.mem_Icc, abs_le]

end InvariantProjection.ConditionalConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ScalarMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def multiplier (g : Lp ℂ ∞ μ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2 g

end Invariant233.L2Multiplication

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarMultiplier
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem multiplier_coe (g : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplier g f =ᵐ[μ] fun x => g x • f x := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).coeFn_holder g f

variable [IsFiniteMeasure μ]

theorem multiplier_indicator_coe (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f =ᵐ[μ]
      s.indicator f := by
  filter_upwards [multiplier_coe (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f,
    indicatorConstLp_coeFn (p := ∞) (μ := μ) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℂ))] with x hx hi
  rw [hx, hi]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem multiplier_indicator_const (s : Set X) (hs : MeasurableSet s) (c : E) :
    multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) (Lp.const 2 μ c) =
      indicatorConstLp 2 hs (measure_ne_top μ s) c := by
  apply Lp.ext
  filter_upwards [multiplier_indicator_coe s hs (Lp.const 2 μ c),
    Lp.coeFn_const 2 μ c,
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
      (hμs := measure_ne_top μ s) (c := c)] with x hx hc hi
  rw [hx, hi]
  by_cases hxs : x ∈ s
  · simpa only [Set.indicator_of_mem hxs, Function.const_apply] using hc
  · simp only [Set.indicator_of_notMem hxs]

end Invariant233.L2Multiplication

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FieldOperator
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem apply_simple_aestronglyMeasurable
    (A : X → E →L[ℂ] F)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) (s : SimpleFunc X E) :
    AEStronglyMeasurable (fun x => A x (s x)) μ := by
  classical
  induction s using SimpleFunc.induction' with
  | const v => exact hm v
  | @pcw s t u hu hs ht =>
    convert AEStronglyMeasurable.piecewise hu hs.restrict ht.restrict using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : x ∈ u <;> simp [SimpleFunc.coe_piecewise, hx]

theorem apply_aestronglyMeasurable
    (A : X → E →L[ℂ] F)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    {f : X → E} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => A x (f x)) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => A x (hf.stronglyMeasurable_mk.approx n x))
  · intro n
    exact apply_simple_aestronglyMeasurable A hm _
  · filter_upwards [hf.ae_eq_mk] with x hx
    rw [hx]
    exact ((A x).continuous.tendsto _).comp (hf.stronglyMeasurable_mk.tendsto_approx x)

def fieldOperatorVec (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    (f : Lp E 2 μ) : Lp F 2 μ :=
  ((Lp.memLp f).of_le_mul (apply_aestronglyMeasurable A hm (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => (A x).le_of_opNorm_le (hA x) (f x))).toLp _

theorem fieldOperatorVec_ae (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    (f : Lp E 2 μ) :
    fieldOperatorVec A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  MemLp.coeFn_toLp _

def fieldOperatorLinear (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) :
    Lp E 2 μ →ₗ[ℂ] Lp F 2 μ where
  toFun := fieldOperatorVec A C hA hm
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fieldOperatorVec_ae A C hA hm (f + g),
      fieldOperatorVec_ae A C hA hm f, fieldOperatorVec_ae A C hA hm g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (fieldOperatorVec A C hA hm f) (fieldOperatorVec A C hA hm g)]
      with x hfg hf hg hsum hout
    simp only [Pi.add_apply] at hsum hout
    rw [hfg, hout, hf, hg, hsum, map_add]
  map_smul' c f := by
    change fieldOperatorVec A C hA hm (c • f) = c • fieldOperatorVec A C hA hm f
    apply Lp.ext
    filter_upwards [fieldOperatorVec_ae A C hA hm (c • f),
      fieldOperatorVec_ae A C hA hm f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (fieldOperatorVec A C hA hm f)] with x hcf hf hsmul hout
    simp only [Pi.smul_apply] at hsmul hout
    rw [hcf, hout, hf, hsmul, map_smul]

def fieldOperator (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) :
    Lp E 2 μ →L[ℂ] Lp F 2 μ :=
  (fieldOperatorLinear A C hA hm).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    change ∀ᵐ x ∂μ, ‖fieldOperatorVec A C hA hm f x‖ ≤ C * ‖f x‖
    filter_upwards [fieldOperatorVec_ae A C hA hm f] with x hx
    rw [hx]
    exact (A x).le_of_opNorm_le (hA x) (f x))

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.StrongField

open MeasureTheory Filter
open scoped Topology

variable {X ι H F : Type*} [MeasurableSpace X] [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem stronglyMeasurable_apply_of_columns
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] F)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i))
    {v : X → H} (hv : StronglyMeasurable v) :
    StronglyMeasurable fun x => A x (v x) := by
  classical
  let approximant : Finset ι → X → F := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • A x (b i)
  have hm (s : Finset ι) : StronglyMeasurable (approximant s) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have hc : StronglyMeasurable fun x => b.repr (v x) i := by
      simp only [b.repr_apply_apply]
      exact (innerSL ℂ (b i)).continuous.comp_stronglyMeasurable hv
    exact hc.smul (hA i)
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) hm
  apply tendsto_pi_nhds.mpr
  intro x
  have h := (A x).hasSum (b.hasSum_repr (v x))
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant, map_smul] using h

end Invariant233.StrongField

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ColumnOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.Fields

noncomputable def rationalComplex (q : ℚ × ℚ) : ℂ :=
  Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ))

variable {ι H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

noncomputable def columnOperator (b : HilbertBasis ι ℂ H) (c : ι → F) : H →L[ℂ] F :=
  (Finsupp.linearCombination ℂ c).extendOfNorm (Finsupp.linearCombination ℂ b)

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ColumnOperator
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.Fields

open MeasureTheory

variable {ι H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem denseRange_basis_linearCombination (b : HilbertBasis ι ℂ H) :
    DenseRange (Finsupp.linearCombination ℂ b) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ b) : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Finsupp.range_linearCombination]
  exact b.dense_span

theorem columnOperator_linearCombination (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ}
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (z : ι →₀ ℂ) :
    columnOperator b c (Finsupp.linearCombination ℂ b z) =
      Finsupp.linearCombination ℂ c z := by
  exact LinearMap.extendOfNorm_eq (denseRange_basis_linearCombination b) ⟨C, hbound⟩ z

theorem columnOperator_apply_basis (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ}
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (i : ι) : columnOperator b c (b i) = c i := by
  classical
  simpa using columnOperator_linearCombination b c hbound (Finsupp.single i 1)

theorem norm_columnOperator_le (b : HilbertBasis ι ℂ H) (c : ι → F)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖) :
    ‖columnOperator b c‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_basis_linearCombination b) hC hbound

theorem denseRange_rationalComplex : DenseRange rationalComplex := by
  have hq := Rat.isDenseEmbedding_coe_real.dense
  have hprod := hq.prodMap hq
  have h := Complex.equivRealProdCLM.symm.surjective.denseRange.comp hprod
    Complex.equivRealProdCLM.symm.continuous
  change DenseRange (fun q : ℚ × ℚ =>
    Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ)))
  simpa only [Function.comp_def, Prod.map] using h

omit [CompleteSpace F] in

theorem finite_combination_bound_of_rational
    (b : HilbertBasis ι ℂ H) (c : ι → F) {C : ℝ}
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ,
      ‖∑ i : s, rationalComplex (q i) • c i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖) :
    ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ c z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖ := by
  classical
  intro z
  have hd : DenseRange (fun q : z.support → ℚ × ℚ =>
      fun i : z.support => rationalComplex (q i)) :=
    DenseRange.piMap (fun _ => denseRange_rationalComplex)
  have h : ‖∑ i : z.support, z i • c i‖ ≤ C * ‖∑ i : z.support, z i • b i‖ := by
    exact hd.induction_on
      (p := fun a : z.support → ℂ =>
        ‖∑ i : z.support, a i • c i‖ ≤ C * ‖∑ i : z.support, a i • b i‖)
      (fun i : z.support => z i)
      (isClosed_le (by fun_prop) (by fun_prop)) (hbound z.support)
  rw [z.support.sum_coe_sort (fun i => z i • c i),
    z.support.sum_coe_sort (fun i => z i • b i)] at h
  exact h

variable {X : Type*} [MeasurableSpace X] [Countable ι]

theorem stronglyMeasurable_columnOperator_apply
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ}
    (hbound : ∀ x, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (c x) z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖)
    (hc : ∀ i, StronglyMeasurable fun x => c x i)
    {v : X → H} (hv : StronglyMeasurable v) :
    StronglyMeasurable fun x => columnOperator b (c x) (v x) := by
  apply StrongField.stronglyMeasurable_apply_of_columns b
  · intro i
    simpa only [columnOperator_apply_basis b _ (hbound _)] using hc i
  · exact hv

omit [CompleteSpace F] in

theorem ae_finite_combination_bound_of_rational
    (b : HilbertBasis ι ℂ H) (c : X → ι → F) {C : ℝ} {μ : Measure X}
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖) :
    ∀ᵐ x ∂μ, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (c x) z‖ ≤ C * ‖Finsupp.linearCombination ℂ b z‖ := by
  have hs : ∀ s : Finset ι, ∀ᵐ x ∂μ, ∀ q : s → ℚ × ℚ,
      ‖∑ i : s, rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, rationalComplex (q i) • b i‖ := by
    intro s
    exact ae_all_iff.mpr (hbound s)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact finite_combination_bound_of_rational b (c x) hx

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_LpOperatorExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.Fields

open MeasureTheory
open scoped ENNReal

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_operator_ext_indicator (hp : p ≠ ∞)
    (A B : Lp E p μ →L[ℂ] F)
    (h : ∀ (v : E) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      A (indicatorConstLp p hs hμs v) = B (indicatorConstLp p hs hμs v)) :
    A = B := by
  ext f
  apply Lp.induction hp (fun g => A g = B g) _ _ _ f
  · intro v s hs hμs
    exact h v s hs hμs.ne
  · intro g k hg hk hdis hAg hAk
    simp only [map_add, hAg, hAk]
  · exact isClosed_eq A.continuous B.continuous

noncomputable def indicatorConstLpCLM (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : E →L[ℂ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := indicatorConstLp p hs hμs
      map_add' := fun v w => (indicatorConstLp_add (c := v) (c' := w)).symm
      map_smul' := by
        intro c v
        simp only [indicatorConstLp, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun x => by
          simp only [RingHom.id_apply, Pi.smul_apply, Set.indicator_smul_apply] }
    (μ.real s ^ (1 / p.toReal))
    (fun v => by
      change ‖indicatorConstLp p hs hμs v‖ ≤ μ.real s ^ (1 / p.toReal) * ‖v‖
      simpa only [mul_comm] using
        (norm_indicatorConstLp_le (p := p) (hs := hs) (hμs := hμs) (c := v)))

theorem lp_operator_ext_basis_indicator {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : HilbertBasis ι ℂ H) (hp : p ≠ ∞)
    (A B : Lp H p μ →L[ℂ] F)
    (h : ∀ (i : ι) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      A (indicatorConstLp p hs hμs (e i)) =
        B (indicatorConstLp p hs hμs (e i))) : A = B := by
  apply lp_operator_ext_indicator hp A B
  intro v s hs hμs
  let C : H →L[ℂ] Lp H p μ := indicatorConstLpCLM s hs hμs
  have hAC : A.comp C = B.comp C := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
    rintro _ ⟨i, rfl⟩
    exact h i s hs hμs
  exact DFunLike.congr_fun hAC v

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarMultiplierFields
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sq_eq_integral_hilbert (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def]
  simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]

variable [IsFiniteMeasure μ]

theorem norm_indicator_sq_hilbert (s : Set X) (hs : MeasurableSet s) (v : E) :
    ‖indicatorConstLp 2 hs (measure_ne_top μ s) v‖ ^ 2 = ‖v‖ ^ 2 * μ.real s := by
  rw [norm_sq_eq_integral_hilbert]
  calc
    (∫ x, ‖indicatorConstLp 2 hs (measure_ne_top μ s) v x‖ ^ 2 ∂μ) =
        ∫ x, s.indicator (fun _ => ‖v‖ ^ 2) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
        (hμs := measure_ne_top μ s) (c := v)] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]
    _ = ‖v‖ ^ 2 * μ.real s := by rw [integral_indicator hs]; simp [mul_comm]

theorem norm_multiplier_indicator_sq_hilbert (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    ‖multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f‖ ^ 2 =
      ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_hilbert, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [multiplier_indicator_coe s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem ae_norm_apply_const_le
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) (v : E) :
    ∀ᵐ x ∂μ, ‖A (Lp.const 2 μ v) x‖ ≤ ‖A‖ * ‖v‖ := by
  apply Fields.ae_norm_le_of_local_square_integral (mul_nonneg (norm_nonneg A) (norm_nonneg v))
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
  intro s hs
  have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ => B (Lp.const 2 μ v))
    (hA (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
  have hid : A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
      multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
        (A (Lp.const 2 μ v)) := by
    simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
  rw [← norm_multiplier_indicator_sq_hilbert s hs, ← hid]
  calc
    ‖A (indicatorConstLp 2 hs (measure_ne_top μ s) v)‖ ^ 2 ≤
        (‖A‖ * ‖indicatorConstLp 2 hs (measure_ne_top μ s) v‖) ^ 2 := by
      gcongr
      exact A.le_opNorm _
    _ = (‖A‖ * ‖v‖) ^ 2 * μ.real s := by
      rw [mul_pow, norm_indicator_sq_hilbert]
      ring

theorem apply_const_finsetSum_coe {ι : Type*}
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (s : Finset ι) (z : ι → ℂ) (v : ι → E) :
    A (Lp.const 2 μ (∑ i ∈ s, z i • v i)) =ᵐ[μ]
      fun x => ∑ i ∈ s, z i • A (Lp.const 2 μ (v i)) x := by
  have heq : A (Lp.const 2 μ (∑ i ∈ s, z i • v i)) =
      ∑ i ∈ s, z i • A (Lp.const 2 μ (v i)) := by
    change (A.comp (Lp.constL 2 μ ℂ)) (∑ i ∈ s, z i • v i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_smul _ _ _
  rw [heq]
  have hsmul : ∀ᵐ x ∂μ, ∀ i ∈ s,
      (z i • A (Lp.const 2 μ (v i))) x = z i • A (Lp.const 2 μ (v i)) x := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    exact Lp.coeFn_smul _ _
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => z i • A (Lp.const 2 μ (v i))), hsmul]
    with x hx hxs
  rw [hx]
  exact Finset.sum_congr rfl hxs

theorem apply_indicator_coe_of_commutes
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g))
    (s : Set X) (hs : MeasurableSet s) (v : E) :
    A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =ᵐ[μ]
      s.indicator (A (Lp.const 2 μ v)) := by
  have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ => B (Lp.const 2 μ v))
    (hA (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
  have hid : A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
      multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
        (A (Lp.const 2 μ v)) := by
    simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
  rw [hid]
  exact multiplier_indicator_coe s hs _

variable {ι : Type*} [Countable ι] [CompleteSpace E]

omit [IsFiniteMeasure μ] in

theorem exists_stronglyMeasurable_field_of_rational_tests
    (b : HilbertBasis ι ℂ E) (c : X → ι → E) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, Fields.rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, Fields.rationalComplex (q i) • b i‖)
    (hc : ∀ i, AEStronglyMeasurable (fun x => c x i) μ) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ C) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ᵐ x ∂μ, ∀ i, F x (b i) = c x i) := by
  classical
  let d : X → ι → E := fun x i => (hc i).mk (fun x => c x i) x
  have hd : ∀ i, StronglyMeasurable fun x => d x i :=
    fun i => (hc i).stronglyMeasurable_mk
  have hdc : ∀ᵐ x ∂μ, ∀ i, d x i = c x i :=
    ae_all_iff.mpr (fun i => (hc i).ae_eq_mk.symm)
  have hdtest : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, Fields.rationalComplex (q i) • d x i‖ ≤
        C * ‖∑ i : s, Fields.rationalComplex (q i) • b i‖ := by
    intro s q
    filter_upwards [hbound s q, hdc] with x hx hdx
    simpa only [hdx] using hx
  have hdbound := Fields.ae_finite_combination_bound_of_rational b d hdtest
  obtain ⟨s, hsae, hsm, hsb⟩ := hdbound.exists_measurable_mem
  let e : X → ι → E := fun x i => s.indicator (fun x => d x i) x
  have he : ∀ i, StronglyMeasurable fun x => e x i :=
    fun i => (hd i).indicator hsm
  have hebound : ∀ x, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (e x) z‖ ≤
        C * ‖Finsupp.linearCombination ℂ b z‖ := by
    intro x z
    by_cases hx : x ∈ s
    · simpa only [e, Set.indicator_of_mem hx] using hsb x hx z
    · simp only [e, Set.indicator_of_notMem hx]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_zero, Finset.sum_const_zero,
        norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  refine ⟨fun x => Fields.columnOperator b (e x), ?_, ?_, ?_⟩
  · intro x
    exact Fields.norm_columnOperator_le b (e x) hC (hebound x)
  · intro v
    exact Fields.stronglyMeasurable_columnOperator_apply b e hebound he stronglyMeasurable_const
  · filter_upwards [hsae, hdc] with x hx hdx
    intro i
    rw [Fields.columnOperator_apply_basis b (e x) (hebound x)]
    simpa only [e, Set.indicator_of_mem hx] using hdx i

theorem exists_field_columns_of_commutes
    (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ᵐ x ∂μ, ∀ i, F x (b i) = A (Lp.const 2 μ (b i)) x) := by
  apply exists_stronglyMeasurable_field_of_rational_tests b
    (fun x i => A (Lp.const 2 μ (b i)) x) (norm_nonneg A)
  · intro s q
    filter_upwards [ae_norm_apply_const_le A hA
      (∑ i : s, Fields.rationalComplex (q i) • b i),
      apply_const_finsetSum_coe A Finset.univ
        (fun i : s => Fields.rationalComplex (q i)) (fun i : s => b i)] with x hx hcomb
    rw [hcomb] at hx
    exact hx
  · intro i
    exact Lp.aestronglyMeasurable _

omit [CompleteSpace E] in

theorem field_unique_of_representation (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F G : X → E →L[ℂ] E)
    (hF : ∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x))
    (hG : ∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) : F =ᵐ[μ] G := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  filter_upwards [hF (Lp.const 2 μ (b i)), hG (Lp.const 2 μ (b i)),
    Lp.coeFn_const 2 μ (b i)] with x hx hy hc
  simpa only [hc, Function.const_apply] using hx.symm.trans hy

omit [Countable ι] [CompleteSpace E] in

theorem represented_eq_of_basis_columns (b : HilbertBasis ι ℂ E)
    (A T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F : X → E →L[ℂ] E)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g))
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => F x (f x))
    (hcol : ∀ᵐ x ∂μ, ∀ i, F x (b i) = A (Lp.const 2 μ (b i)) x) : A = T := by
  apply Fields.lp_operator_ext_basis_indicator b (by simp) A T
  intro i s hs hμs
  apply Lp.ext
  filter_upwards [apply_indicator_coe_of_commutes A hA s hs (b i),
    hT (indicatorConstLp 2 hs hμs (b i)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := b i),
    hcol] with x hx ht hi hc
  rw [hx, ht, hi]
  by_cases hxs : x ∈ s
  · simpa only [Set.indicator_of_mem hxs] using (hc i).symm
  · simp only [Set.indicator_of_notMem hxs, map_zero]

theorem exists_field_of_commutes (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) := by
  obtain ⟨F, hnorm, hmeas, hcol⟩ := exists_field_columns_of_commutes b A hA
  let T : Lp E 2 μ →L[ℂ] Lp E 2 μ := DirectIntegral.fieldOperator F ‖A‖ hnorm
    (fun v => (hmeas v).aestronglyMeasurable)
  have hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => F x (f x) := by
    intro f
    exact DirectIntegral.fieldOperatorVec_ae F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) f
  have hAT : A = T := represented_eq_of_basis_columns b A T F hA hT hcol
  refine ⟨F, hnorm, hmeas, ?_⟩
  intro f
  rw [hAT]
  exact hT f

theorem exists_unique_field_of_commutes (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) := by
  obtain ⟨F, hnorm, hmeas, hrep⟩ := exists_field_of_commutes b A hA
  exact ⟨F, hnorm, hmeas, hrep, fun G hG => field_unique_of_representation b A F G hrep hG⟩

end Invariant233.L2Multiplication

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_FourierSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.FourierSampling

noncomputable def polynomial (s : Finset ℤ) (a : ℤ → ℂ)
    (x : UnitAddCircle) : ℂ := ∑ i ∈ s, a i * fourier i x

end Invariant233.FourierSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_UniformIntervalPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

noncomputable def intervalLaw (a L : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / L) • volume.restrict (Ioc a (a + L))

noncomputable def phaseLaw (a L : ℝ) : Measure UnitAddCircle :=
  (intervalLaw a L).map (fun x : ℝ => (x : UnitAddCircle))

noncomputable def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco 1 0 x : ℝ)

noncomputable def lambdaLaw (N₀ : ℝ) : Measure ℝ :=
  ENNReal.ofReal N₀ • volume.restrict (Icc (1 / N₀) (2 / N₀))

noncomputable def fractionLaw (N₀ n : ℝ) : Measure ℝ :=
  (lambdaLaw N₀).map (fun x => Int.fract (n * x))

noncomputable def fractionDensity (N₀ n x : ℝ) : ℝ :=
  ((fractionLaw N₀ n).rnDeriv (volume.restrict (Ico 0 1)) x).toReal

end Invariant233.UniformIntervalPhase

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_UniformIntervalPhase
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

@[simp] theorem representative_coe (x : ℝ) :
    representative (x : UnitAddCircle) = Int.fract x := by
  simp [representative]

end Invariant233.UniformIntervalPhase

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarRectangleDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.ScalarRectangles

def intervalTest (a b : ℝ) (x : UnitAddCircle) : ℝ :=
  (Icc a b).indicator (fun _ => 1) (UniformIntervalPhase.representative x)

end Invariant233.ScalarRectangles

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldContinuity
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open Filter Topology

variable {𝕜 E F G ι X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem tendsto_apply_of_strong_tendsto_of_bounded
    {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {v : ι → E} {v₀ : E} {C : ℝ}
    (hA : ∀ w, Tendsto (fun i => A i w) l (𝓝 (A₀ w)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C)
    (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hnorm : Tendsto (fun i => C * ‖v i - v₀‖) l (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => C) l (𝓝 C)).mul
      (hv.sub_const v₀).norm
  have hzero : Tendsto (fun i => A i (v i - v₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hnorm
    filter_upwards [hC] with i hi
    exact ((A i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hsum := hzero.add (hA v₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using hsum

variable [TopologicalSpace X]

theorem continuous_apply_of_strong_continuous_of_bounded
    {A : X → E →L[𝕜] F} {v : X → E} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (hv : Continuous v) :
    Continuous (fun x => A x (v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact tendsto_apply_of_strong_tendsto_of_bounded
    (fun w => (hA w).continuousAt) (Eventually.of_forall hC) hv.continuousAt

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TaggedEventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantRotation.TaggedEventBounds

open MeasureTheory

section ProductEvent

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def tagRectangle (T G : ι → Set Ω) (i : ι) : Set (ι → Ω) :=
  Set.pi Set.univ (fun j => if j = i then T j else G j)

def oneTagEvent (T G : ι → Set Ω) : Set (ι → Ω) :=
  ⋃ i, tagRectangle T G i

end ProductEvent


variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def currentBlockEvent (T B₁ B₂ : ι → Set Ω) : Set (ι → Ω) :=
  {x | (∃ i, x i ∈ T i) ∧ ∀ i, x i ∉ B₁ i ∧ x i ∉ B₂ i}


end InvariantRotation.TaggedEventBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TailScaleCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

noncomputable section
open Set
open scoped BigOperators

namespace Invariant233.TailScaleCover

def upperHorizon (m : ℕ) : ℝ := (m : ℝ) ^ ((4 / 5 : ℝ) * m)

end Invariant233.TailScaleCover

end
end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ScalarSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.ScalarSampling

def delta (s : ℝ) : ℝ := min s (1 - s)

def rawKernel (h α s t : ℝ) : ℝ :=
  if α ≤ delta s then
    (Set.Ioo 0 (h * delta s)).indicator (fun _ => (h * delta s)⁻¹) t
  else 0

def circleKernel (h α z v : ℝ) : ℝ :=
  rawKernel h α (Int.fract z) (Int.fract v)

def manuscriptKernel (m : ℕ) (z v : ℝ) : ℝ :=
  circleKernel ((m : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) z v

def manuscriptEndpointKernel (m : ℕ) (z v : ℝ) : ℝ :=
  manuscriptKernel m (z - v) v

def triangularKernel (s t : ℝ) : ℝ :=
  (Set.Ioo 0 (1 - s)).indicator (fun _ => 1) t

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingEndpointVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.ScalarSampling

structure VariationControl (f : ℝ → ℝ) (C V : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  le_height : ∀ x, f x ≤ C
  variation : eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal V

noncomputable def leftEndpointPiece (h α s v : ℝ) : ℝ :=
  if 0 < v then if v < h * (s - v) then if α ≤ s - v then
    if s - v ≤ 1 / 2 then (h * max α (s - v))⁻¹ else 0 else 0 else 0 else 0

noncomputable def rightEndpointPiece (h α s v : ℝ) : ℝ :=
  if 0 < v then if v < h * (1 - s + v) then if α ≤ 1 - s + v then
    if 1 / 2 < s - v then (h * max α (1 - s + v))⁻¹ else 0 else 0 else 0 else 0

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TestedTriangularMoments
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedTriangular

def firstKernel (E F : Set ℝ) (s t : ℝ) : ℝ :=
  triangularKernel s t * E.indicator (fun _ => 1) s *
    F.indicator (fun _ => 1) (Int.fract (s + t))

def secondKernel (E F : Set ℝ) (s t : ℝ) : ℝ :=
  triangularKernel (Int.fract (s - t)) t *
    E.indicator (fun _ => 1) (Int.fract (s - t)) * F.indicator (fun _ => 1) s

@[simp] theorem firstKernel_univ_univ (s t : ℝ) :
    firstKernel univ univ s t = triangularKernel s t := by
  simp [firstKernel]

@[simp] theorem secondKernel_univ_univ (s t : ℝ) :
    secondKernel univ univ s t = triangularKernel (Int.fract (s - t)) t := by
  simp [secondKernel]

end Invariant233.ScalarSampling.TestedTriangular

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem memLp_finite_product
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i)) :
    MemLp (fun x => ∏ i, h i (x i)) 2 (Measure.pi μ) := by
  have hi : Integrable (fun x => ∏ i, h i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep fun i => (hh i).integrable (by norm_num)
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2
  simpa only [Finset.prod_pow] using
    (Integrable.fintype_prod_dep fun i => (hh i).integrable_sq)

theorem measurePreserving_restrict_infinitePi
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (s : Finset ι) :
    MeasurePreserving s.restrict (Measure.infinitePi μ)
      (Measure.pi fun i : s => μ i) :=
  ⟨Finset.measurable_restrict s, Measure.infinitePi_map_restrict μ⟩

theorem partial_product_eq_restrict
    {ι : Type*} {Ω : ι → Type*} (h : (i : ι) → Ω i → ℝ) (s : Finset ι) :
    (fun x => ∏ i ∈ s, h i (x i)) =
      (fun x : (i : s) → Ω i => ∏ i : s, h i (x i)) ∘ s.restrict := by
  funext x
  exact (Finset.prod_coe_sort s (fun i => h i (x i))).symm

theorem memLp_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i)) :
    MemLp (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) := by
  rw [partial_product_eq_restrict h s]
  exact (memLp_finite_product (fun i : s => hh i)).comp_measurePreserving
    (measurePreserving_restrict_infinitePi μ s)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductDensity

noncomputable def partialDensityLp
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (n : ℕ) : Lp ℝ 2 (Measure.infinitePi μ) :=
  (memLp_partial_product (Finset.range n) hh).toLp
    (fun x => ∏ i ∈ Finset.range n, h i (x i))

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_BlockProductCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrderedProductCoupling

def sourceKappa (s : ℕ) : ℝ := 1 / (100 * ((s : ℝ) + 1))

def blockDensityBound (κ : ℕ → ℝ) : ℝ :=
  Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1))

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockProductCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling

lemma sourceKappa_nonneg (s : ℕ) : 0 ≤ sourceKappa s := by
  unfold sourceKappa
  positivity

lemma sourceKappa_le (s : ℕ) : sourceKappa s ≤ 1 / 100 := by
  unfold sourceKappa
  apply (div_le_iff₀ (by positivity : 0 < 100 * ((s : ℝ) + 1))).2
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal lp ComplexConjugate

noncomputable section

namespace InvariantProjection.ConditionalConvolution

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {K : ℕ} {D a c η δ : ℝ}

def exceptionalTail (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) : ℝ :=
  ∑' v : ℤ, (omittedEvent H K n v).indicator
    (fun ω => ‖ξ ω v‖ * ‖γ ω ((n : ℤ) + v)‖) ω

end InvariantProjection.ConditionalConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldTraceFaithfulness
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceFaithfulness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem apply_eq_zero_of_re_inner_eq_zero {T : E →L[ℂ] E}
    (hT : T.IsPositive) {x : E} (hx : (inner ℂ (T x) x).re = 0) : T x = 0 := by
  let R := CFC.sqrt T
  have hR : R.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)
  have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)
  have hnorm : ‖R x‖ ^ 2 = 0 := by
    rw [R.apply_norm_sq_eq_inner_adjoint_left, (ContinuousLinearMap.isSelfAdjoint_iff'.mp hR.isSelfAdjoint)]
    change (inner ℂ ((R * R) x) x).re = 0
    rw [hRR]
    exact hx
  have hRx : R x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [← hRR]
  change R (R x) = 0
  simp [hRx]

theorem eq_zero_of_re_diagonal_eq_zero {ι : Type*} (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive)
    (hdiag : ∀ i, (inner ℂ (T (b i)) (b i)).re = 0) : T = 0 := by
  have hb : ∀ i, T (b i) = 0 := fun i =>
    apply_eq_zero_of_re_inner_eq_zero hT (hdiag i)
  ext x
  have hsum := T.hasSum (b.hasSum_repr x)
  simp only [map_smul, hb, smul_zero] at hsum
  exact hsum.unique hasSum_zero

theorem ae_eq_zero_of_integral_diagonal_eq_zero
    {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (b : HilbertBasis ι ℂ E) (i₀ : ι)
    (H : X → E →L[ℂ] E) (σ : ι → X → X)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hpos : ∀ᵐ x ∂μ, (H x).IsPositive)
    (hcov : ∀ i, ∀ᵐ x ∂μ,
      (inner ℂ (H x (b i)) (b i)).re =
        (inner ℂ (H (σ i x) (b i₀)) (b i₀)).re)
    (hint : Integrable (fun x => (inner ℂ (H x (b i₀)) (b i₀)).re) μ)
    (htrace : ∫ x, (inner ℂ (H x (b i₀)) (b i₀)).re ∂μ = 0) :
    H =ᵐ[μ] 0 := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => (inner ℂ (H x (b i₀)) (b i₀)).re := by
    filter_upwards [hpos] with x hx
    exact hx.re_inner_nonneg_left _
  have hzero : ∀ᵐ x ∂μ, (inner ℂ (H x (b i₀)) (b i₀)).re = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp htrace
  have hall : ∀ i, ∀ᵐ x ∂μ, (inner ℂ (H x (b i)) (b i)).re = 0 := by
    intro i
    filter_upwards [hcov i, (hσ i).quasiMeasurePreserving.ae hzero] with x hcovx hzerox
    exact hcovx.trans hzerox
  filter_upwards [hpos, ae_all_iff.mpr hall] with x hposx hdiagx
  exact eq_zero_of_re_diagonal_eq_zero b hposx hdiagx

end Invariant233.FieldTraceFaithfulness

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_CovariantTracialVector
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω}

theorem represented_eq_zero_of_field_ae_zero
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hA : A =ᵐ[μ] 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT ξ, hA, Lp.coeFn_zero E 2 μ] with x hx hxA hx0
  simpa only [hxA, Pi.zero_apply, zero_apply, hx0] using hx

variable [CompleteSpace E] [IsFiniteMeasure μ]

theorem represented_eq_zero_of_vector_state_zero
    (b : HilbertBasis ℤ ℂ E) (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : ∀ᵐ x ∂μ, (A x).IsPositive)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcov : ∀ r : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b 0) (A (σ r x) (b 0)) = inner ℂ (b r) (A x (b r)))
    (hzero : inner ℂ (Lp.const 2 μ (b 0)) (T (Lp.const 2 μ (b 0))) = 0) :
    T = 0 := by
  have hi : Integrable (fun x => inner ℂ (b 0) (A x (b 0))) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (Lp.const 2 μ (b 0))
      (T (Lp.const 2 μ (b 0)))).congr
    filter_upwards [Lp.coeFn_const 2 μ (b 0), hT (Lp.const 2 μ (b 0))]
      with x hx hTx
    rw [hTx, hx]
    rfl
  have heq : (fun x => (inner ℂ (A x (b 0)) (b 0)).re) =
      fun x => (inner ℂ (b 0) (A x (b 0))).re := by
    funext x
    exact inner_re_symm (𝕜 := ℂ) (A x (b 0)) (b 0)
  have hcov' : ∀ r : ℤ, ∀ᵐ x ∂μ,
      (inner ℂ (A x (b r)) (b r)).re =
        (inner ℂ (A (σ r x) (b 0)) (b 0)).re := by
    intro r
    filter_upwards [hcov r] with x hx
    calc
      (inner ℂ (A x (b r)) (b r)).re = (inner ℂ (b r) (A x (b r))).re :=
        inner_re_symm (𝕜 := ℂ) (A x (b r)) (b r)
      _ = (inner ℂ (b 0) (A (σ r x) (b 0))).re := congrArg Complex.re hx.symm
      _ = (inner ℂ (A (σ r x) (b 0)) (b 0)).re :=
        inner_re_symm (𝕜 := ℂ) (b 0) (A (σ r x) (b 0))
  have hint : Integrable (fun x => (inner ℂ (A x (b 0)) (b 0)).re) μ := by
    rw [heq]
    exact hi.re
  have htr : (∫ x, (inner ℂ (A x (b 0)) (b 0)).re ∂μ) = 0 := by
    rw [heq]
    change (∫ x, RCLike.re (inner ℂ (b 0) (A x (b 0))) ∂μ) = 0
    rw [integral_re hi,
      ← constant_vector_state_eq_integral T A hT (b 0), hzero]
    rfl
  exact represented_eq_zero_of_field_ae_zero T A hT
    (FieldTraceFaithfulness.ae_eq_zero_of_integral_diagonal_eq_zero
      μ b 0 A σ hσ hpos hcov' hint htr)

theorem faithfulTracialVector_of_covariant_fields [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖) ∧
        (∀ r k l : ℤ, ∀ᵐ x ∂μ,
          inner ℂ (b k) (A (σ r x) (b l)) =
            inner ℂ (b (k + r)) (A x (b (l + r)))) ∧
        (T.IsPositive → ∀ᵐ x ∂μ, (A x).IsPositive)) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Lp.norm_const' 2 μ (b 0) (by norm_num) (by norm_num)]
    simp [b.orthonormal.norm_eq_one]
  · intro T S hTM hSM
    obtain ⟨A, hT, hA, hAbound, hcovA, _⟩ := hfields T hTM
    obtain ⟨B, hS, hB, hBbound, hcovB, _⟩ := hfields S hSM
    exact constant_vector_state_cyclic_of_covariance b T S A B hT hS hA hB
      ‖T‖ ‖S‖ (norm_nonneg _) (norm_nonneg _) hAbound hBbound σ hσ hcovA hcovB
  · intro T hTM hpos hzero
    obtain ⟨A, hT, _, _, hcov, hApos⟩ := hfields T hTM
    apply represented_eq_zero_of_vector_state_zero b T A hT (hApos hpos) σ hσ
    · intro r
      simpa only [zero_add] using hcov r 0 0
    · exact hzero

theorem faithfulTracialVector_of_represented_covariant_fields
    [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖) ∧
        (∀ r k l : ℤ, ∀ᵐ x ∂μ,
          inner ℂ (b k) (A (σ r x) (b l)) =
            inner ℂ (b (k + r)) (A x (b (l + r))))) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  let := HilbertModelSize.separable_of_countable_hilbertBasis b
  apply faithfulTracialVector_of_covariant_fields b M σ hσ
  intro T hTM
  obtain ⟨A, hT, hA, hAbound, hcov⟩ := hfields T hTM
  exact ⟨A, hT, hA, hAbound, hcov,
    ae_isPositive_of_represented_isPositive T A hT⟩

theorem faithfulTracialVector_of_commuting_shiftedPullbacks [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (S : ℤ → E →ₗᵢ[ℂ] E) (hS : ∀ r k : ℤ, S r (b k) = b (k + r))
    (hcomm : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M → ∀ r,
      Commute T (DirectIntegral.shiftedPullback (S r).toContinuousLinearMap (σ r) (hσ r)))
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖)) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  apply faithfulTracialVector_of_represented_covariant_fields b M σ hσ
  intro T hTM
  obtain ⟨A, hT, hA, hAbound⟩ := hfields T hTM
  refine ⟨A, hT, hA, hAbound, ?_⟩
  exact ae_matrix_covariance_of_commute b T A
    (fun r => DirectIntegral.shiftedPullback (S r).toContinuousLinearMap (σ r) (hσ r))
    S σ hσ hS hT
    (fun r => shiftedPullback_ae (S r).toContinuousLinearMap (σ r) (hσ r)) (hcomm T hTM)

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ScalarMultiplierCommutation
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem commute_multiplier_of_represented
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => A x (ξ x))
    (g : Lp ℂ ∞ μ) : Commute T (multiplier g) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (multiplier g ξ), multiplier_coe g ξ,
    multiplier_coe g (T ξ), hT ξ] with x hTM hM hMT hTx
  change T (multiplier g ξ) x = multiplier g (T ξ) x
  rw [hTM, hM, hMT, hTx, map_smul]

theorem multiplier_star (g : Lp ℂ ∞ μ) :
    (multiplier (star g) : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
      star (multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro ξ η
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_coe (star g) ξ, multiplier_coe g η,
    Lp.coeFn_star g] with x hx hy hg
  rw [hx, hy, hg]
  simp only [Pi.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

theorem star_commutes_multiplier
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ g : Lp ℂ ∞ μ, Commute T (multiplier g))
    (g : Lp ℂ ∞ μ) : Commute (star T) (multiplier g) := by
  change star T * multiplier g = multiplier g * star T
  have h := congrArg star (hT (star g)).eq
  simpa only [star_mul, ← multiplier_star, star_star] using h.symm

end Invariant233.L2Multiplication

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSampling
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

@[fun_prop]
theorem representative_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CompactTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped NNReal
noncomputable section

namespace Invariant233

def UniformlyAbsolutelyContinuous {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : ι → Measure X) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i, ν i A < ε

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weight_mem_Icc (θ c : ℕ → ℝ) (x : Base) :
    weight θ c x ∈ Icc (0 : ℝ) 1 :=
  extendedExpNeg_mem_Icc _

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FieldWeightedShift
attribute [-instance] _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def fieldOperator (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ :=
  (shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
    fieldDiagonal a C hC ha hm

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weightedOperator_mem_factor (θ c : ℕ → ℝ) :
    weightedOperator θ c ∈ factor θ := by
  unfold weightedOperator
  apply (factor θ).mul_mem
  · exact subset_vonNeumannGenerated _ (Set.mem_union_left _ (by simp))
  · apply subset_vonNeumannGenerated _
    apply Set.mem_union_right
    exact ⟨_, _, _, _, _, rfl⟩

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductTailTrimming
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

def coordinateOrderFailure (θ : ℕ → ℝ) (n : ℕ) (i : ℕ) : Set Base :=
  {x | circleRepresentative (rotationIterate θ (n : ℤ) x i) <
    circleRepresentative (x i)}

def tailOrderFailure (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) : Set Base :=
  ⋃ i : {i : ℕ // i ∉ I}, coordinateOrderFailure θ n i

namespace TailTrimming

def orbitPairMap (θ : ℕ → ℝ) (n : ℕ) (x : Base) : Base × Base :=
  (x, rotationIterate θ (n : ℤ) x)

def orbitPairMeasure (θ : ℕ → ℝ) (n : ℕ) (w : Base → ℝ≥0∞) : Measure (Base × Base) :=
  (baseMeasure.withDensity w).map (orbitPairMap θ n)

def orbitAverageMeasure (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) : Measure (Base × Base) :=
  (N.card : ℝ≥0∞)⁻¹ • ∑ n ∈ N, orbitPairMeasure θ n (w n)

def orderedPairEvent : Set (Base × Base) := {xy | Ordered xy.1 xy.2}

end TailTrimming

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTrimming
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel

local instance productSamplingTrimmingOpensMeasurableSpace :
    OpensMeasurableSpace EndpointPair := inferInstance

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingHorizon
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SamplingHorizon

open Filter
open scoped Topology

theorem decay_le_inv {m : ℝ} (hm : 20 ≤ m) :
    m ^ (-m / 20) ≤ m⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem ceiling_ratio_le_decay {m : ℝ} (hm : 20 ≤ m) :
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
      2 * m ^ (-m / 20) := by
  have hmone : 1 ≤ m := by linarith
  have hmpos : 0 < m := by linarith
  have hpowone : 1 ≤ m ^ ((3 / 4 : ℝ) * m) :=
    Real.one_le_rpow hmone (by positivity)
  have hceil : (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤
      2 * m ^ ((3 / 4 : ℝ) * m) := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hmpos.le ((3 / 4 : ℝ) * m))
    linarith
  calc
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
        (2 * m ^ ((3 / 4 : ℝ) * m)) / m ^ ((4 / 5 : ℝ) * m) :=
      div_le_div_of_nonneg_right hceil (Real.rpow_nonneg hmpos.le _)
    _ = 2 * m ^ (((3 / 4 : ℝ) * m) - ((4 / 5 : ℝ) * m)) := by
      rw [Real.rpow_sub hmpos]
      ring
    _ = 2 * m ^ (-m / 20) := by congr 2; ring

theorem ceiling_ratio_le_inv {m : ℝ} (hm : 20 ≤ m) :
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
      2 * m⁻¹ :=
  (ceiling_ratio_le_decay hm).trans (mul_le_mul_of_nonneg_left (decay_le_inv hm) (by norm_num))

theorem tendsto_ceiling_ratio {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) /
      m n ^ ((4 / 5 : ℝ) * m n)) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n in atTop, 20 ≤ m n := hm.eventually_ge_atTop 20
  have hi : Tendsto (fun n => 2 * (m n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hm).const_mul 2
  apply squeeze_zero' _ _ hi
  · filter_upwards [hlarge] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [hlarge] with n hn
    exact ceiling_ratio_le_inv hn

theorem eventually_scale_gap {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) (G : ℝ) :
    ∀ᶠ n in atTop, G * (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) <
      m n ^ ((4 / 5 : ℝ) * m n) := by
  have hlim : Tendsto (fun n => G * ((⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) /
      m n ^ ((4 / 5 : ℝ) * m n))) atTop (𝓝 0) := by
    simpa using (tendsto_ceiling_ratio hm).const_mul G
  have hlt := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hlt, hm.eventually_ge_atTop 20] with n hn hm20
  have hpow : 0 < m n ^ ((4 / 5 : ℝ) * m n) :=
    Real.rpow_pos_of_pos (by linarith) _
  apply (div_lt_one hpow).mp
  simpa only [mul_div_assoc] using hn

theorem twice_lt_ceiling_cutoff {m : ℝ} (hm : 20 ≤ m) :
    2 * m < (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hsq : m ^ 2 ≤ m ^ ((3 / 4 : ℝ) * m) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ m by linarith) (show (2 : ℝ) ≤ (3 / 4 : ℝ) * m by linarith)
    simpa only [Real.rpow_two] using h
  have hceil := Nat.le_ceil (m ^ ((3 / 4 : ℝ) * m))
  have hstrict : 2 * m < m ^ 2 := by nlinarith
  exact hstrict.trans_le (hsq.trans hceil)

theorem tendsto_ceiling_cutoff {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hm
  filter_upwards [hm.eventually_ge_atTop 20] with n hn
  have h := twice_lt_ceiling_cutoff hn
  linarith

theorem eventually_block_size (B G L H κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, B ≤ (m : ℝ) ∧ 200 ≤ m ∧
      L ≤ κ * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      G * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ ε ∧
      2 * (m : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun m : ℕ => κ * (m : ℝ) ^ (1 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hm |>.const_mul_atTop hκ
  have hheight : Tendsto (fun m : ℕ => H /
      (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_ceiling_cutoff hm)).const_mul H
  have hall : ∀ᶠ m : ℕ in atTop, B ≤ (m : ℝ) ∧ 200 ≤ m ∧
      L ≤ κ * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      G * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ ε ∧
      2 * (m : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
    filter_upwards [hm.eventually_ge_atTop B, eventually_ge_atTop 200,
      hpow.eventually_ge_atTop L, eventually_scale_gap hm G,
      hheight.eventually (gt_mem_nhds hε)] with m hB hm200 hL hG hH
    refine ⟨hB, hm200, hL, hG, hH.le, twice_lt_ceiling_cutoff ?_⟩
    exact_mod_cast le_trans (by norm_num : 20 ≤ 200) hm200
  exact hall

theorem eventually_stage_size (j : ℕ) (hj : 0 < j) (K G Gnext L H d : ℝ) :
    ∀ᶠ m : ℕ in atTop, K ≤ (m : ℝ) ∧ (2 : ℝ) ^ j ≤ m ∧ 4 * G ≤ m ∧ 200 ≤ m ∧
      d ≤ (m : ℝ) / 100 ∧
      L ≤ (1 / (100 * (j : ℝ))) * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      Gnext * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j ∧
      2 * K < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hall :=
    eventually_block_size (max K (max ((2 : ℝ) ^ j) (max (4 * G) (100 * d))))
      Gnext L H (1 / (100 * (j : ℝ))) ((1 / 2 : ℝ) ^ j) (by positivity) (by positivity)
  filter_upwards [hall] with m hm
  obtain ⟨hB, hm200, hL, hgap, hH, hdouble⟩ := hm
  simp only [max_le_iff] at hB
  refine ⟨hB.1, hB.2.1, hB.2.2.1, hm200, ?_, hL, hgap, hH, ?_⟩
  · linarith [hB.2.2.2]
  · linarith [hB.1]

theorem exists_stage_size (j : ℕ) (hj : 0 < j) (K G Gnext L H d : ℝ) :
    ∃ m : ℕ, K ≤ (m : ℝ) ∧ (2 : ℝ) ^ j ≤ m ∧ 4 * G ≤ m ∧ 200 ≤ m ∧
      d ≤ (m : ℝ) / 100 ∧
      L ≤ (1 / (100 * (j : ℝ))) * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      Gnext * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j ∧
      2 * K < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) :=
  (eventually_stage_size j hj K G Gnext L H d).exists

theorem exists_attenuation (A lower ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ lower ≤ L ∧ A * Real.exp (-L / 10000) ≤ ε := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) / 10000) atTop atTop :=
    hm.atTop_div_const (by norm_num)
  have hexp : Tendsto (fun n : ℕ => A * Real.exp (-(n : ℝ) / 10000))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_div, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv).const_mul A
  have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n ∧ lower ≤ n ∧
      A * Real.exp (-(n : ℝ) / 10000) ≤ ε := by
    filter_upwards [hm.eventually_ge_atTop 1, hm.eventually_ge_atTop lower,
      hexp.eventually (gt_mem_nhds hε)] with n h1 hlo he
    exact ⟨h1, hlo, he.le⟩
  obtain ⟨n, h1, hlo, he⟩ := hall.exists
  exact ⟨n, h1, hlo, he⟩

theorem exists_next_gain (κ L : ℝ) (hκ : 0 < κ) :
    ∃ G : ℕ, 1 ≤ G ∧ L ≤ κ * Real.sqrt (G : ℝ) := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hm).const_mul_atTop hκ
  have hall : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ L ≤ κ * Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hs.eventually_ge_atTop L] with n hn hL
    exact ⟨hn, hL⟩
  exact hall.exists

end Invariant233.SamplingHorizon

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_PhaseBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

open scoped BigOperators

def consecutiveBlock (m : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  Finset.Ico (∑ r ∈ Finset.range j, m r)
    ((∑ r ∈ Finset.range j, m r) + m j)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.ProductScaleConstruction

open SamplingHorizon FiniteWindow

structure State where
  K : ℕ
  G : ℕ
  count : ℕ
  cost : ℝ
  previousL : ℝ

end Invariant233.ProductScaleConstruction

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_PhaseFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

noncomputable def failureBound (m : ℝ) : ℝ :=
  2 * m ^ ((4 / 5 : ℝ) * m) * (2 : ℝ) ^ m *
    (10 * m ^ (-19 / 20 : ℝ)) ^ ((19 / 20 : ℝ) * m)

noncomputable def nonzeroIntegerWindow (R : ℝ) : Finset ℤ :=
  (Finset.Icc (-Int.floor R) (Int.floor R)).erase 0

noncomputable def largePhaseTimes (N R : ℝ) : Finset ℤ :=
  (nonzeroIntegerWindow R).filter (fun k => N / 4 ≤ |(k : ℝ)|)

noncomputable def phaseGoodCount {ι : Type*} (J : Finset ι) (b : ℝ)
    (k : ℤ) (θ : ι → ℝ) : ℕ := by
  classical
  exact (J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈
    Set.Icc b (1 - b))).card

noncomputable def largePhaseFailure {ι : Type*} (J : Finset ι) (N : ℝ) :
    Set (ι → ℝ) :=
  {θ | ∃ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
    (phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ) <
      (J.card : ℝ) / 20}

def largePhaseCondition {ι : Type*} (J : Finset ι) (N : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, N / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card) →
    (J.card : ℝ) / 20 ≤
      (phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ)

def smallPhaseCondition {ι : Type*} (J : Finset ι) (K G : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, G * K ≤ |(k : ℝ)| → |(k : ℝ)| ≤ (J.card : ℝ) * K / 4 →
    ∀ i ∈ J, 1 - Int.fract ((k : ℝ) * θ i) ∈
      Set.Icc (G / J.card) (1 - G / J.card)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_BlockPhaseConstruction
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

@[simp] theorem card_consecutiveBlock (m : ℕ → ℕ) (j : ℕ) :
    (consecutiveBlock m j).card = m j := by
  simp [consecutiveBlock]

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_IndependentKernelProduct
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.KernelProduct

variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def independent (κ : ∀ i, Kernel (A i) (B i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (∀ i, A i) (∀ i, B i) where
  toFun x := Measure.infinitePi (fun i => κ i (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders
        (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp))
    rintro _ ⟨s, t, ht, rfl⟩
    simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
    simp_rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.measurable_fun_prod s (fun i _ =>
      (Kernel.measurable_coe (κ i) (ht i)).comp (measurable_pi_apply i))

end Invariant233.KernelProduct

namespace Invariant233.KernelProduct
variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def pairCoordinates : ((∀ i, A i) × (∀ i, B i)) ≃ᵐ (∀ i, A i × B i) where
  toFun p i := (p.1 i, p.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv p := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ∀ i, A i × B i => (fun i => (z i).1, fun i => (z i).2))
    fun_prop

end Invariant233.KernelProduct

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentKernelProduct
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Invariant233.KernelProduct

variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

instance independent_isMarkov (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (independent κ) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))⟩

@[simp] theorem independent_apply (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] (x : ∀ i, A i) :
    independent κ x = Measure.infinitePi (fun i => κ i (x i)) := rfl

end Invariant233.KernelProduct

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

abbrev sourceUnitVector : Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_AffiliatedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantRotation.AffiliatedTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def domainImage (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) : Submodule 𝕜 E :=
  (p.comap H.domain.subtype).map H.toFun

def transported (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) : Submodule 𝕜 E :=
  (domainImage H p).topologicalClosure

variable [CompleteSpace E]

instance transported_hasOrthogonalProjection
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) :
    (transported H p).HasOrthogonalProjection := by
  let : IsClosed (transported H p : Set E) :=
    Submodule.isClosed_topologicalClosure _
  infer_instance

end InvariantRotation.AffiliatedTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CircleRationalGraphs
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

def circleTranslationGraph (t : Circle) : FiniteMeasure (Circle × Circle) :=
  ⟨circleMeasure.map (fun x => (x, x + t)), by
    change IsFiniteMeasure ((volume : Measure Circle).map (fun x => (x, x + t)))
    infer_instance⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_JointEigenspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def jointEigenspace (D : ι → H →L[ℂ] H) (ev : ι → ℂ) : Submodule ℂ H :=
  ⨅ i, Module.End.eigenspace (D i).toLinearMap (ev i)

instance isClosed_jointEigenspace (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    IsClosed (jointEigenspace D ev : Set H) := by
  unfold jointEigenspace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i => ContinuousLinearMap.isClosed_eigenspace (D i) (ev i)

def jointEigenprojection (D : ι → H →L[ℂ] H) (ev : ι → ℂ) : H →L[ℂ] H :=
  (jointEigenspace D ev).starProjection

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_OrbitMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

variable {X Y : Type*} [MeasurableSpace Y]

@[reducible] def orbitMeasurableSpace (σ : Equiv.Perm X) (f : X → Y) : MeasurableSpace X :=
  ⨆ n : ℤ, MeasurableSpace.comap (fun x => f ((σ ^ n) x)) ‹MeasurableSpace Y›

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_PositiveDiagonalModel
attribute [-instance] _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.PositiveDiagonalModel

abbrev Fiber := WeightedShift.Hilbert
abbrev Space {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) := Lp Fiber 2 μ

def e0 : Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

def fiberShift : Fiber →L[ℂ] Fiber :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap

def fiberShiftUnit : (Fiber →L[ℂ] Fiber)ˣ :=
  (ContinuousLinearEquiv.unitsEquiv ℂ Fiber).symm
    (WeightedShift.shift 1).toContinuousLinearEquiv

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

def realWeight (a : Y → ℤ → ℝ) (C : ℝ)
    (hbound : ∀ y k, |a y k| ≤ C) (y : Y) : WeightedShift.Weight :=
  ⟨fun k => (a y k : ℂ), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound y k⟩

def realDiagonal (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ) :
    Space μ →L[ℂ] Space μ :=
  WeightedShift.fieldDiagonal (realWeight a C hbound) C hC
    (fun y => lp.norm_le_of_forall_le hC (fun k => by
      simpa only [realWeight, Complex.norm_real, Real.norm_eq_abs] using hbound y k))
    (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k))

def realWeightedShift (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ) :
    Space μ →L[ℂ] Space μ :=
  (fiberShift.compLpL 2 μ) * realDiagonal a C hC hbound hm

def diagonalState [IsFiniteMeasure μ] (P : Space μ →L[ℂ] Space μ) : ℝ :=
  (inner ℂ (Lp.const 2 μ e0) (P (Lp.const 2 μ e0))).re

end Invariant233.PositiveDiagonalModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_PrefixHybrid
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

def prefixEndpoint (D : ℕ) (x y : Base) : Base :=
  selectedEndpoint (Finset.range D) x y

def prefixPair (D : ℕ) (xy : EndpointPair) : EndpointPair :=
  (xy.1, prefixEndpoint D xy.1 xy.2)

def prefixPairLaw (ν : Measure EndpointPair) (D : ℕ) : Measure EndpointPair :=
  ν.map (prefixPair D)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators

noncomputable def characterPhase {ι : Type*} (v : ι →₀ ℤ)
    (x : ι → UnitAddCircle) : UnitAddCircle :=
  v.sum (fun i n => n • x i)

noncomputable def productCharacter {ι : Type*} (v : ι →₀ ℤ) :
    C((ι → UnitAddCircle), ℂ) where
  toFun x := (AddCircle.toCircle (characterPhase v x) : ℂ)
  continuous_toFun := by
    apply continuous_subtype_val.comp
    apply AddCircle.continuous_toCircle.comp
    unfold characterPhase Finsupp.sum
    fun_prop

noncomputable def productFourierAlgebra (ι : Type*) :
    StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range (productCharacter (ι := ι)))

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductIdealSampling
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel.IdealSampling

def endpoint (I D : Finset ℕ) (h : ℝ) (x z : Base) : Base :=
  fun i => if i ∈ I then z i else if i ∈ D then
    x i + ((h * ScalarSampling.delta (circleRepresentative (x i)) *
      circleRepresentative (z i) : ℝ) : Circle) else x i

def endpointMap (I D : Finset ℕ) (h : ℝ) (xz : EndpointPair) : EndpointPair :=
  (xz.1, endpoint I D h xz.1 xz.2)

def cutoffEvent (I D : Finset ℕ) (α : ℝ) : Set EndpointPair :=
  {xz | ∀ i ∈ D \ I, α ≤ ScalarSampling.delta (circleRepresentative (xz.1 i))}

def sourceMeasure (I : Finset ℕ) : Measure EndpointPair :=
  (baseMeasure.prod baseMeasure).restrict (triangularEvent I)

def law (I D : Finset ℕ) (h α : ℝ) : Measure EndpointPair :=
  ((sourceMeasure I).restrict (cutoffEvent I D α)).map (endpointMap I D h)

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductPrefixDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

abbrev PrefixIndex (D : ℕ) := ↥(Finset.range D)
abbrev TailIndex (D : ℕ) := {i : ℕ // i ∉ Finset.range D}
abbrev PrefixPairs (D : ℕ) := PrefixIndex D → ℝ × ℝ
abbrev TailValues (D : ℕ) := TailIndex D → ℝ

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_RotationTransfer
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.Rotation

def exponentialTransfer (θ : ℝ) (b : Circle → ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  WeightedShift.fieldUnboundedMultiplier circleMeasure
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ScalarEndpointDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ScalarEndpointDensity
noncomputable section

def cutDistance (z : ℝ) : ℝ := min z (1 - z)

def endpointMap (t z : ℝ) : ℝ := z + t * cutDistance z

def midpoint (t : ℝ) : ℝ := (1 + t) / 2

def slopeDensity (t s : ℝ) : ℝ :=
  if s ≤ midpoint t then (1 + t)⁻¹ else (1 - t)⁻¹

def averagedDensity (h s : ℝ) : ℝ :=
  h⁻¹ * ∫ t in (0 : ℝ)..h, slopeDensity t s

end

end Invariant233.ScalarEndpointDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ScalarKernelEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

structure KernelEstimates (m : ℕ) (u : ℝ → ℝ → ℝ) : Prop where
  boundedVariation : ∀ s, BoundedVariationOn (u s) (Icc (0 : ℝ) 1)
  variation_sharp : ∀ s,
    sSup (Set.range (fun v : ℝ => |u s v|)) +
      (eVariationOn (u s) (Icc (0 : ℝ) 1)).toReal ≤ 11 * (m : ℝ)^(13 / 5 : ℝ)
  variation_coarse : ∀ s,
    sSup (Set.range (fun v : ℝ => |u s v|)) +
      (eVariationOn (u s) (Icc (0 : ℝ) 1)).toReal ≤ 11 * (m : ℝ)^10
  average_bounds : ∀ s, 0 ≤ (∫ v in (0 : ℝ)..1, u s v) ∧
    (∫ v in (0 : ℝ)..1, u s v) ≤ 2
  mass : (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v) = 1 - 2 / (m : ℝ)^2
  average_square_lower : (1 - 2 / (m : ℝ)^2)^2 ≤
    ∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2
  average_square_upper : (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
    1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2
  square_mass : (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v^2) =
    (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ScalarSamplingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

def samplingHorizon (m : ℕ) : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)

def bvSize (f : ℝ → ℂ) : ℝ :=
  sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
    (eVariationOn f (Icc (0 : ℝ) 1)).toReal

def SeparatedPowers (m : ℕ) (N : ℝ) (n n' : ℕ) : Prop :=
  ∀ v v' : ℤ, |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
    (v ≠ 0 ∨ v' ≠ 0) →
      N * (m : ℝ) ^ 1000 < |(v : ℝ) * n + (v' : ℝ) * n'|

structure SamplingPair (m : ℕ) (N₀ N : ℝ) (n n' : ℕ) : Prop where
  N₀_pos : 0 < N₀
  N₀_le : N₀ ≤ N
  N_le : N ≤ (m : ℝ)^2
  n_pos : 0 < n
  n'_pos : 0 < n'
  distinct : n ≠ n'
  first_range : samplingHorizon m / 2 ≤ n ∧ (n : ℝ) ≤ samplingHorizon m
  second_range : samplingHorizon m / 2 ≤ n' ∧ (n' : ℝ) ≤ samplingHorizon m
  separated : SeparatedPowers m N n n'

def BVEstimate (m : ℕ) (N₀ : ℝ) (n n' : ℕ) (C : ℝ) : Prop :=
  ∀ f g : ℝ → ℂ,
    BoundedVariationOn f (Icc (0 : ℝ) 1) →
    BoundedVariationOn g (Icc (0 : ℝ) 1) →
      ‖(∫ x, f (Int.fract ((n : ℝ) * x)) * g (Int.fract ((n' : ℝ) * x))
          ∂UniformIntervalPhase.lambdaLaw N₀) -
        (∫ x in (0 : ℝ)..1, f x) * (∫ x in (0 : ℝ)..1, g x)‖ ≤
          C * (m : ℝ)^(-(80 : ℝ)) * bvSize f * bvSize g

def AllKernelEstimates : Prop :=
  ∀ m : ℕ, 200 ≤ m →
    KernelEstimates m (manuscriptKernel m) ∧
      KernelEstimates m (manuscriptEndpointKernel m)

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_TrialSampling
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.TrialSampling

def phaseLaw (m : ℕ) (N : ℝ) : Measure (Fin m → ℝ) :=
  Measure.infinitePi (fun _ : Fin m =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N)))

def spatialLaw (m : ℕ) : Measure (Fin m → Circle) :=
  Measure.pi (fun _ : Fin m => circleMeasure)

def pairLaw (N : ℝ) : Measure (ℝ × Circle) :=
  (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod circleMeasure

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_VectorTraceState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorTraceCLM (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ H) ξ)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_AffiliatedTransport
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantRotation.AffiliatedTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
theorem mem_domainImage {H : E →ₗ.[𝕜] E} {p : Submodule 𝕜 E} {y : E} :
    y ∈ domainImage H p ↔ ∃ x : H.domain, (x : E) ∈ p ∧ H x = y := by
  simp [domainImage, Submodule.mem_map]


end InvariantRotation.AffiliatedTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_JointEigenprojection
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]
theorem mem_jointEigenspace {D : ι → H →L[ℂ] H} {ev : ι → ℂ} {x : H} :
    x ∈ jointEigenspace D ev ↔ ∀ i, D i x = ev i • x := by
  simp [jointEigenspace]

@[simp]
theorem isStarProjection_jointEigenprojection (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    IsStarProjection (jointEigenprojection D ev) :=
  isStarProjection_starProjection

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialProjectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal

namespace Invariant233.TracialProjectionTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


variable [CompleteSpace H]

def cutoffMap (T : H →ₗ.[ℂ] H) (r : Submodule ℂ H) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖) : r →L[ℂ] H :=
  (T.toFun.comp (Submodule.inclusion hrD)).mkContinuous K hupper


end Invariant233.TracialProjectionTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ProjectionMeetTrace
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Invariant233.ProjectionMeetTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

omit [CompleteSpace H] in
@[simp] theorem vectorFunctional_apply (ξ : H) (A : H →L[ℂ] H) :
    vectorFunctional ξ A = vectorTrace ξ A := rfl

def meanOperator (A : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, A ^ k

end Invariant233.ProjectionMeetTrace

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_StrongOperatorConvergence
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology
namespace Invariant233

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem strong_tendsto_of_dense_of_bounded
    {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {s : Set E} {C : ℝ} (hs : Dense s)
    (hA : ∀ w ∈ s, Tendsto (fun i => A i w) l (𝓝 (A₀ w)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : E) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := max C 0 + ‖A₀‖ + 1
  have hM : 0 < M := by dsimp [M] <;> positivity
  have hCM : C ≤ M := by dsimp [M]; have := le_max_left C 0; have := norm_nonneg A₀; linarith
  have hAM : ‖A₀‖ ≤ M := by dsimp [M]; have := le_max_right C 0; linarith
  obtain ⟨w, hws, hvw⟩ := hs.exists_dist_lt v (div_pos (show 0 < ε / 3 by positivity) hM)
  have hMw : M * dist v w < ε / 3 := by
    simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw
  have hw := Metric.tendsto_nhds.mp (hA w hws) (ε / 3) (by positivity)
  filter_upwards [hC, hw] with i hi hwi
  have hfirst : dist (A i v) (A i w) < ε / 3 :=
    ((A i).dist_le_opNorm v w).trans_lt
      ((mul_le_mul_of_nonneg_right (hi.trans hCM) dist_nonneg).trans_lt hMw)
  have hlast : dist (A₀ w) (A₀ v) < ε / 3 := by
    rw [dist_comm]
    exact (A₀.dist_le_opNorm v w).trans_lt
      ((mul_le_mul_of_nonneg_right hAM dist_nonneg).trans_lt hMw)
  have htri := dist_triangle (A i v) (A i w) (A₀ v)
  have htri' := dist_triangle (A i w) (A₀ w) (A₀ v)
  linarith

theorem strong_tendsto_of_dense_span_of_bounded
    {κ : Type*} {l : Filter ι} {A : ι → E →L[𝕜] F} {A₀ : E →L[𝕜] F}
    {b : κ → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ k, Tendsto (fun i => A i (b k)) l (𝓝 (A₀ (b k))))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : E) :
    Tendsto (fun i => A i v) l (𝓝 (A₀ v)) := by
  apply strong_tendsto_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨k, rfl⟩ := hw; exact hA k
  | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : F)) l (𝓝 0))
  | add w z hw hz ihw ihz => simpa only [map_add] using ihw.add ihz
  | smul c w hw ih => simpa only [map_smul] using ih.const_smul c

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_StrongOperatorIntegral
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.StrongOperatorIntegral

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure X} [IsProbabilityMeasure μ]

def linearMap (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ) : E →ₗ[ℂ] F where
  toFun v := ∫ x, A x v ∂μ
  map_add' v w := by
    simp only [map_add]
    exact integral_add (hint v) (hint w)
  map_smul' c v := by
    simp only [map_smul]
    exact integral_smul c (fun x => A x v)

omit [CompleteSpace F] in

theorem norm_linearMap_le (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (v : E) :
    ‖linearMap A hint v‖ ≤ C * ‖v‖ := by
  change ‖∫ x, A x v ∂μ‖ ≤ C * ‖v‖
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (C := C * ‖v‖) (f := fun x => A x v) (by
      filter_upwards [hbound] with x hx
      exact ((A x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg v)))
  simpa using h

def operator (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : E →L[ℂ] F :=
  (linearMap A hint).mkContinuous C (norm_linearMap_le A hint hbound)

omit [CompleteSpace F] in
@[simp] theorem operator_apply (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (v : E) :
    operator A hint C hbound v = ∫ x, A x v ∂μ := rfl

end Invariant233.StrongOperatorIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_VectorTraceState
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]
theorem vectorTraceCLM_apply (ξ : H) (A : H →L[ℂ] H) :
    vectorTraceCLM ξ A = vectorTrace ξ A := rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitTests
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

def orbitTestWeight (θ : ℕ → ℝ) (A : Set EndpointPair)
    (w : ℕ → Base → ℝ) (n : ℕ) : Base → ℝ :=
  (orbitPairMap θ n ⁻¹' A).indicator (w n)

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TestedSamplingMoments
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedSampling

def firstKernel (m : ℕ) (E F : Set ℝ) (s t : ℝ) : ℝ :=
  manuscriptKernel m s t * E.indicator (fun _ => 1) s *
    F.indicator (fun _ => 1) (Int.fract (s + t))

def secondKernel (m : ℕ) (E F : Set ℝ) (s t : ℝ) : ℝ :=
  manuscriptEndpointKernel m s t *
    E.indicator (fun _ => 1) (Int.fract (s - t)) * F.indicator (fun _ => 1) s

def MomentBounds (m : ℕ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
  Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
  (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧ (∫ t in (0 : ℝ)..1, u s t) ≤ 2) ∧
  (0 ≤ (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t)^2) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2) ∧
  (0 ≤ (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, u s t^2) ∧
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, u s t^2) ≤
      (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2))

@[simp] theorem firstKernel_univ_univ (m : ℕ) (s t : ℝ) :
    firstKernel m univ univ s t = manuscriptKernel m s t := by simp [firstKernel]

@[simp] theorem secondKernel_univ_univ (m : ℕ) (s t : ℝ) :
    secondKernel m univ univ s t = manuscriptEndpointKernel m s t := by simp [secondKernel]

end Invariant233.ScalarSampling.TestedSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingPhaseMoments
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSamplingPhaseMoments

def unitInterval : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

instance unitInterval_probability : IsProbabilityMeasure unitInterval := by
  constructor
  simp [unitInterval]

def mean (u : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ t, u s t ∂unitInterval

def sample (u : ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  u p.2 (Int.fract ((n : ℝ) * p.1))

def realBVSize (f : ℝ → ℝ) : ℝ :=
  sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) +
    (eVariationOn f (Icc (0 : ℝ) 1)).toReal

@[fun_prop] theorem measurable_sample {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) (n : ℕ) : Measurable (sample u n) := by
  exact hu.comp (measurable_snd.prodMk ((measurable_const_mul (n : ℝ)).comp measurable_fst).fract)

@[fun_prop] theorem measurable_mean {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) : Measurable (mean u) :=
  hu.stronglyMeasurable.integral_prod_right.measurable

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTestedKernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments
open Invariant233.ScalarSampling

def testedKernel (m : ℕ) (selected endpoint : Bool) (a b c d : ℝ) : ℝ → ℝ → ℝ :=
  if endpoint then
    if selected then TestedTriangular.secondKernel (Ico a b) (Ico c d)
    else TestedSampling.secondKernel m (Ico a b) (Ico c d)
  else
    if selected then TestedTriangular.firstKernel (Ico a b) (Ico c d)
    else TestedSampling.firstKernel m (Ico a b) (Ico c d)

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTestedExpectationSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.ProductSamplingPhaseMoments

def testedExpectedError {κ : Type*} [Fintype κ] (m : ℕ)
    (N₀ : κ → ℝ) (powers : Finset ℕ) (selected : κ → Bool)
    (endpoint : Bool) (a b c d : κ → ℝ) : ℝ :=
  let u := fun i => testedKernel m (selected i) endpoint (a i) (b i) (c i) (d i)
  ∫ θ, ∫ x, ((powers.card : ℝ)⁻¹ *
      (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * θ i))) -
      ∏ i, mean (u i) (x i))^2
    ∂Measure.pi (fun _ : κ => unitInterval)
    ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter Finset

namespace InvariantProjection.RotationDecay

variable {X : Type*}

def truncatedLog (f : X → ℝ) (M : ℝ) (x : X) : ℝ :=
  Real.log (max (f x) (Real.exp (-M)))

def orbitProduct (σ : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∏ k ∈ range n, f (σ^[k] x)

end InvariantProjection.RotationDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UniformRotationAverage
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace InvariantProjection.UniformRotationAverage

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)
abbrev CSpace := C(Circle, ℂ)

def translate (a : Circle) : C(Circle, Circle) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

def translateL (a : Circle) : CSpace →L[ℂ] CSpace :=
  ContinuousMap.compCLM ℂ ℂ (translate a)

def averageL (a : Circle) (n : ℕ) : CSpace →L[ℂ] CSpace :=
  (n : ℂ)⁻¹ • ∑ k ∈ range n, translateL (k • a)

@[simp] lemma averageL_apply (a : Circle) (n : ℕ) (f : CSpace) (x : Circle) :
    averageL a n f x = (n : ℂ)⁻¹ * ∑ k ∈ range n, f (x + k • a) := by
  simp [averageL, translateL, translate]

def meanL : CSpace →L[ℂ] CSpace :=
  (ContinuousLinearMap.const ℂ Circle).comp
    ((MeasureTheory.L1.integralCLM' ℂ).comp
      (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ))

@[simp] lemma meanL_apply (f : CSpace) :
    meanL f = ContinuousMap.const Circle (∫ x, f x ∂AddCircle.haarAddCircle) := by
  apply ContinuousMap.ext
  intro x
  change (MeasureTheory.L1.integralCLM' ℂ)
    (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ f) = _
  rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle f)

def convergentSubmodule (a : Circle) : Submodule ℂ CSpace where
  carrier := {f | Tendsto (fun n => averageL a n f) atTop (𝓝 (meanL f))}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun n => averageL a n (f + g)) atTop (𝓝 (meanL (f + g)))
    simpa only [map_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun n => averageL a n (c • f)) atTop (𝓝 (meanL (c • f)))
    simpa only [map_smul] using hf.const_smul c

end InvariantProjection.UniformRotationAverage

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightDecay
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleWeightDecay

local instance circleWeightDecayPeriodPos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)

end InvariantProjection.CircleWeightDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleFiberDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleFiberDecay

abbrev Circle := AddCircle (1 : ℝ)

end InvariantProjection.CircleFiberDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonalConvergence
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem lp_tendsto_of_ae_of_dominated
    {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → Lp E 2 μ} {g : Lp E 2 μ} {bound : X → ℝ}
    (hbound : MemLp bound 2 μ)
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => Lp.aestronglyMeasurable (f n)) (Lp.memLp g) ?_ hfg
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hbound.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  apply le_trans ?_ (hsmall s hs hμs)
  apply eLpNorm_mono_ae_real
  filter_upwards [hf n] with x hx
  by_cases hxs : x ∈ s
  · simpa [hxs] using hx
  · simp [hxs]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

def integerCore (σ : ℤ → X → X) (s : Set X) : Set X :=
  {x | ∀ n : ℤ, σ n x ∈ s}

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ProjectionCocycleWindow
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped lp ComplexConjugate InnerProductSpace

namespace Invariant233.ProjectionCocycleWindow

def basisZero : ℓ²(ℤ, ℂ) := lp.single 2 (0 : ℤ) (1 : ℂ)

@[simp] theorem norm_basisZero : ‖basisZero‖ = 1 := by
  simp [basisZero, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

@[simp] theorem basisZero_zero : basisZero 0 = 1 := by
  simp [basisZero]

end Invariant233.ProjectionCocycleWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RealWeightedPositiveDiagonal
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.PositiveDiagonalModel

@[simp] theorem coe_fiberShiftUnit :
    (fiberShiftUnit : Fiber →L[ℂ] Fiber) = fiberShift := rfl

@[simp] theorem norm_e0 : ‖e0‖ = 1 := by
  simp [e0, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

end Invariant233.PositiveDiagonalModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixReferenceCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

def collapsePrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool)
    (z : PrefixPairs D) : PrefixPairs D :=
  fun i => if pattern i then z i else ((z i).1, (z i).1)

def prefixPatternEvent (D : ℕ) (pattern : PrefixIndex D → Bool) : Set (PrefixPairs D) :=
  {z | ∀ i, pattern i = true → (z i).1 < (z i).2}

def selectedPrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i => pattern i = true)).image Subtype.val

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductCharacters
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators ComplexConjugate
open Set Algebra Submodule

variable {ι : Type*}

@[simp] theorem characterPhase_zero (x : ι → UnitAddCircle) :
    characterPhase (0 : ι →₀ ℤ) x = 0 := by
  simp [characterPhase]

@[simp] theorem characterPhase_single (i : ι) (n : ℤ) (x : ι → UnitAddCircle) :
    characterPhase (Finsupp.single i n) x = n • x i := by
  simp [characterPhase]

@[simp] theorem productCharacter_zero : productCharacter (0 : ι →₀ ℤ) = 1 := by
  ext x
  simp [productCharacter]

@[simp] theorem productCharacter_single_one (i : ι) (x : ι → UnitAddCircle) :
    productCharacter (Finsupp.single i 1) x = (AddCircle.toCircle (x i) : ℂ) := by
  simp [productCharacter]

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.IdealSampling

def coordinateKernel (I : Finset ℕ) (h α : ℝ) (i : ℕ) (s t : ℝ) : ℝ :=
  if i ∈ I then ScalarSampling.triangularKernel s t else ScalarSampling.rawKernel h α s t

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeights
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

open ScalarSampling

def coordinateWeight (I : Finset ℕ) (h α : ℝ) (i : ℕ) (s t : ℝ) : ℝ :=
  if i ∈ I then triangularKernel s t else rawKernel h α s t

def orbitWeight (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (x : Base) : ℝ :=
  ∏ i ∈ D, coordinateWeight I h α i (circleRepresentative (x i))
    (Int.fract ((n : ℝ) * θ i))

def prefixWeight (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (x : D → Circle) : ℝ :=
  ∏ i : D, coordinateWeight I h α i (circleRepresentative (x i))
    (Int.fract ((n : ℝ) * θ i))

def height (h α : ℝ) : ℝ := max 1 (h * α)⁻¹

@[simp] theorem prefixWeight_restrict (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    prefixWeight D I h α θ n (fun i : D => x i) = orbitWeight D I h α θ n x := by
  unfold prefixWeight orbitWeight
  rw [Finset.prod_coe_sort_eq_attach]
  exact Finset.prod_attach D (fun i => coordinateWeight I h α i
    (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)))

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightTests
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

namespace Invariant233.ProductModel.SamplingWeights

def testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ) (h α : ℝ) (i : ℕ)
    (E F : Set ℝ) (s t : ℝ) : ℝ :=
  let a := if endpoint then Int.fract (s - t) else s
  let b := if endpoint then s else Int.fract (s + t)
  coordinateWeight I h α i a t * E.indicator (fun _ => 1) a *
    F.indicator (fun _ => 1) b

def rectangle (D : Finset ℕ) (E F : ℕ → Set ℝ) : Set (Base × Base) :=
  {xy | ∀ i ∈ D, circleRepresentative (xy.1 i) ∈ E i ∧
    circleRepresentative (xy.2 i) ∈ F i}

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingCylinderWeak
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

namespace Invariant233.SamplingCylinderWeak

abbrev CylinderTest (ι : Type*) := Finset (ι × ℚ × ℚ)

def cylinder {ι : Type*} (t : CylinderTest ι) : Set (ι → ℝ) :=
  {x | ∀ v ∈ t, (v.2.1 : ℝ) < x v.1 ∧ x v.1 < (v.2.2 : ℝ)}

@[simp] theorem cylinder_empty {ι : Type*} :
    cylinder (∅ : CylinderTest ι) = univ := by
  ext x
  simp [cylinder]

@[simp] theorem cylinder_union {ι : Type*} [DecidableEq ι] (s t : CylinderTest ι) :
    cylinder (s ∪ t) = cylinder s ∩ cylinder t := by
  classical
  ext x
  change (∀ v ∈ s ∪ t, _) ↔ ((∀ v ∈ s, _) ∧ (∀ v ∈ t, _))
  constructor
  · intro h
    exact ⟨fun v hv => h v (Finset.mem_union_left t hv),
      fun v hv => h v (Finset.mem_union_right s hv)⟩
  · rintro ⟨hs, ht⟩ v hv
    exact (Finset.mem_union.mp hv).elim (hs v) (ht v)

open ProductModel

local instance instOpensMeasurableSpaceEndpointPair : OpensMeasurableSpace EndpointPair := inferInstance

def cutCoordinates (xy : EndpointPair) : Bool × ℕ → ℝ :=
  fun i => circleRepresentative (if i.1 then xy.2 i.2 else xy.1 i.2)

def quotientCoordinates (x : Bool × ℕ → ℝ) : EndpointPair :=
  (fun i => (x (false, i) : Circle), fun i => (x (true, i) : Circle))

@[simp] theorem quotient_cutCoordinates (xy : EndpointPair) :
    quotientCoordinates (cutCoordinates xy) = xy := by
  ext i <;> exact AddCircle.coe_equivIco

def endpointCylinder (t : CylinderTest (Bool × ℕ)) : Set EndpointPair :=
  cutCoordinates ⁻¹' cylinder t

end Invariant233.SamplingCylinderWeak

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingOrbitWeak
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductModel.TailTrimming
open SamplingCylinderWeak

def cylinderTestAverage (θ : ℕ → ℝ) (N : Finset ℕ) (w : ℕ → Base → ℝ)
    (t : CylinderTest (Bool × ℕ)) (x : Base) : ℝ :=
  (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitTestWeight θ (endpointCylinder t) w n x

@[simp] theorem cylinderTestAverage_empty (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (x : Base) :
    cylinderTestAverage θ N w ∅ x = (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x := by
  simp [cylinderTestAverage, orbitTestWeight, endpointCylinder]

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingCylinderWeights
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Filter

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

def cylinderSupport (t : CylinderTest (Bool × ℕ)) : Finset ℕ :=
  t.image (fun v => v.1.2)

def cylinderCoordinateSet (t : CylinderTest (Bool × ℕ)) (b : Bool) (i : ℕ) : Set ℝ :=
  {s | ∀ v ∈ t, v.1 = (b, i) → (v.2.1 : ℝ) < s ∧ s < (v.2.2 : ℝ)}

@[simp] theorem cylinderCoordinateSet_empty (b : Bool) (i : ℕ) :
    cylinderCoordinateSet ∅ b i = univ := by
  ext s
  simp [cylinderCoordinateSet]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingIdealBounds
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

def idealCoordinate (endpoint : Bool) (I : Finset ℕ) (h α : ℝ) (i : ℕ)
    (E F : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, testedCoordinateWeight endpoint I h α i E F s t

def idealProduct (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (x : Base) : ℝ :=
  ∏ i ∈ D, idealCoordinate endpoint I h α i (E i) (F i) (circleRepresentative (x i))

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTestIntegrability
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

def testedProduct (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) : ℝ :=
  ∏ i ∈ D, testedCoordinateWeight endpoint I h α i (E i) (F i)
    (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))

def testedIdeal (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (x : Base) : ℝ :=
  ∏ i ∈ D, ∫ t in (0 : ℝ)..1,
    testedCoordinateWeight endpoint I h α i (E i) (F i)
      (circleRepresentative (x i)) t

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightAssembly
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

def orientedAverage (endpoint : Bool) (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (x : Base) : ℝ :=
  (N.card : ℝ)⁻¹ * ∑ n ∈ N, ∏ i ∈ D,
    testedCoordinateWeight endpoint I h α i univ univ
      (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))

@[simp] theorem rectangle_univ (D : Finset ℕ) :
    rectangle D (fun _ => univ) (fun _ => univ) = univ := by
  ext x
  simp only [rectangle, mem_ofPred_eq, mem_univ, and_self, implies_true]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.SamplingAsymptotics

def momentBase (n : ℕ) : ℝ := 1 + 4 * (n : ℝ) ^ (-(6 / 5 : ℝ))

def kernelMass (n : ℕ) : ℝ := 1 - 2 * (n : ℝ) ^ (-(2 : ℝ))

def productError (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))) *
    (momentBase n + C * (n : ℝ) ^ (-(50 : ℝ))) ^ (n - 1)

def diagonalError (n : ℕ) : ℝ :=
  (8 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n) ^ n /
    (n : ℝ) ^ ((69 / 100 : ℝ) * n)

def idealError (n : ℕ) : ℝ := (momentBase n) ^ n - 2 * (kernelMass n) ^ n + 1

def meanSquareBound (C : ℝ) (n : ℕ) : ℝ :=
  2 * (diagonalError n + 3 * productError C n) + 2 * idealError n

end Invariant233.SamplingAsymptotics

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingPairMoments
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

def scalarUnitLaw : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

def scalarPairLaw (N : ℝ) : Measure (ℝ × ℝ) :=
  (UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw

instance scalarUnitLaw_probability : IsProbabilityMeasure scalarUnitLaw := by
  constructor
  simp [scalarUnitLaw]

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingSelection
attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

instance spatialLaw_probability (m : ℕ) : IsProbabilityMeasure (spatialLaw m) := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  dsimp [spatialLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_DeterminantHomogeneity
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal CStarAlgebra
namespace Invariant233

def positiveRegularizerScale (r : ℝ) (hr : 0 < r) :
    {ε : ℝ // 0 < ε} ≃ {ε : ℝ // 0 < ε} where
  toFun ε := ⟨r * ε.val, mul_pos hr ε.property⟩
  invFun ε := ⟨ε.val / r, div_pos ε.property hr⟩
  left_inv ε := by apply Subtype.ext; dsimp; field_simp [ne_of_gt hr]
  right_inv ε := by apply Subtype.ext; dsimp; field_simp [ne_of_gt hr]

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldResolvent
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem resolventCoefficient_bound (t : ℝ) (ht : 0 ≤ t) :
    ‖((1 + t)⁻¹ : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).mpr (by linarith)

theorem resolvent_scalar_identity (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    z - (((1 + t)⁻¹ : ℝ) : ℂ) * z =
      (t : ℂ) * ((((1 + t)⁻¹ : ℝ) : ℂ) * z) := by
  have hne : (1 + (t : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + t : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp
  ring

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

def intervalCoordinate : C(Set.Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun t => (t.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductPolarModulusComplex
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder
namespace Invariant233.ProductModel.GlobalPolarSupport

local instance productPolarModulusComplexRealModule : Module ℝ (Hilbert →L[ℂ] Hilbert) :=
  Module.complexToReal (Hilbert →L[ℂ] Hilbert)

end Invariant233.ProductModel.GlobalPolarSupport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductWeightPolar
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem weight_complex_norm_le_one (θ c : ℕ → ℝ) (x : Base) :
    ‖(weight θ c x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weight_mem_Icc θ c x).1] using (weight_mem_Icc θ c x).2

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_QuasinilpotentSeries
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {A : Type*} [NormedRing A]

variable [NormedAlgebra ℂ A]

variable [CompleteSpace A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def vectorTraceContinuousLinearMap (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

@[simp] theorem vectorTraceContinuousLinearMap_apply (ξ : H) (T : H →L[ℂ] H) :
    vectorTraceContinuousLinearMap ξ T = vectorTrace ξ T := rfl

end Invariant233

end

end OAI
end


